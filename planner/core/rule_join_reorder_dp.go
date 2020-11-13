// Copyright 2018 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"math/bits"

	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	nodeIDs    []int
	nodeIDMask uint
	expr       expression.Expression
}

func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	// TODO: You need to implement the join reorder algo based on DP.

	// The pseudo code can be found in README.
	// And there's some common struct and method like `baseNodeCumCost`, `calcJoinCumCost` you can use in `rule_join_reorder.go`.
	// Also, you can take a look at `rule_join_reorder_greedy.go`, this file implement the join reorder algo based on greedy algorithm.
	// You'll see some common usages in the greedy version.

	// Note that the join tree may be disconnected. i.e. You need to consider the case `select * from t, t1, t2`.

	// we simply just use DPsize to search the join order having minimum cost
	// the implementation in TiDB 4.7 use DPsub for searching
	// ref: http://www.vldb.org/conf/2006/p930-moerkotte.pdf
	// init the s.curJoinGroup
	for _, node := range joinGroup {
		_, err := node.recursiveDeriveStats()
		if err != nil {
			return nil, err
		}
		s.curJoinGroup = append(s.curJoinGroup, &jrNode{
			p:       node,
			cumCost: s.baseNodeCumCost(node),
		})
	}
	// construct the matrix, later we use this matrix to check connections
	adjacent := make([][]int, len(s.curJoinGroup))
	totalEqEdges := make([]joinGroupEqEdge, 0, len(eqConds))
	addEqEdge := func(node1, node2 int, edgeContent *expression.ScalarFunction) {
		totalEqEdges = append(totalEqEdges, joinGroupEqEdge{
			nodeIDs: []int{node1, node2},
			edge:    edgeContent,
		})
		adjacent[node1] = append(adjacent[node1], node2)
		adjacent[node2] = append(adjacent[node2], node1)
	}

	for _, cond := range eqConds {
		sf := cond.(*expression.ScalarFunction)
		lCol := sf.GetArgs()[0].(*expression.Column)
		rCol := sf.GetArgs()[1].(*expression.Column)
		lIdx, err := findNodeIndexInGroup(joinGroup, lCol)
		if err != nil {
			return nil, err
		}
		rIdx, err := findNodeIndexInGroup(joinGroup, rCol)
		if err != nil {
			return nil, err
		}
		addEqEdge(lIdx, rIdx, sf)
	}

	totalNonEqEdges := make([]joinGroupNonEqEdge, 0, len(s.otherConds))
	for _, cond := range s.otherConds {
		cols := expression.ExtractColumns(cond)
		mask := uint(0)
		ids := make([]int, 0, len(cols))
		for _, col := range cols {
			idx, err := findNodeIndexInGroup(joinGroup, col)
			if err != nil {
				return nil, err
			}
			ids = append(ids, idx)
			mask |= 1 << uint(idx)
		}
		totalNonEqEdges = append(totalNonEqEdges, joinGroupNonEqEdge{
			nodeIDs:    ids,
			nodeIDMask: mask,
			expr:       cond,
		})
	}
	// construct subnets
	subnets := adjacent2Subnet(adjacent)
	joins := make([]LogicalPlan, 0)
	for _, subnet := range subnets {
		join, err := s.dpSearch(subnet, totalEqEdges, totalNonEqEdges)
		if err != nil {
			return nil, err
		}
		joins = append(joins, join)
	}
	// //  TODO: what is the remainedOtherConds used for????
	remainedOtherConds := make([]expression.Expression, 0, len(totalNonEqEdges))
	for _, edge := range totalNonEqEdges {
		remainedOtherConds = append(remainedOtherConds, edge.expr)
	}
	return s.makeBushyJoin(joins, remainedOtherConds), nil
}

func (s *joinReorderDPSolver) dpSearch(subnet []int,
	totalEqEdges []joinGroupEqEdge, totalNonEqEdges []joinGroupNonEqEdge) (LogicalPlan, error) {
	nodeCnt := uint(len(subnet))
	bestPlan := make([]*jrNode, 1<<len(s.curJoinGroup)) // memory array
	totalBitmap := 0
	// bestPlan[s] is nil can be treated as bestCost[s] = +inf.
	for i := uint(0); i < nodeCnt; i++ {
		bestPlan[1<<subnet[i]] = s.curJoinGroup[subnet[i]]
		totalBitmap |= 1 << subnet[i]
	}

	for size := uint(2); size <= nodeCnt; size++ {
		for lSize := uint(1); lSize < size; lSize++ {
			visited := make([]int, len(bestPlan))
			rSize := size - lSize
			for i, lSubJoin := range bestPlan {
				lBitmap := uint(i)
				if uint(bits.OnesCount(lBitmap)) != lSize || lSubJoin == nil {
					continue
				}
				for j, rSubJoin := range bestPlan {
					rBitmap := uint(j)
					if i == j || visited[j] == 1 || uint(bits.OnesCount(uint(j))) != rSize ||
						isOverlap(lBitmap, rBitmap) || rSubJoin == nil {
						continue
					}
					usedEdges, otherConds := s.nodesAreConnected(lBitmap, rBitmap, totalEqEdges, totalNonEqEdges)
					if len(usedEdges) == 0 {
						continue
					}
					join, err := s.newJoinWithEdge(lSubJoin.p, rSubJoin.p, usedEdges, otherConds)
					if err != nil {
						return nil, err
					}
					curCost := s.calcJoinCumCost(join, lSubJoin, rSubJoin)

					visited[j] = 1
					nodeBitmap := lBitmap | rBitmap
					if bestPlan[nodeBitmap] == nil {
						bestPlan[nodeBitmap] = &jrNode{
							p:       join,
							cumCost: curCost,
						}
					} else if bestPlan[nodeBitmap].cumCost > curCost {
						bestPlan[nodeBitmap].p = join
						bestPlan[nodeBitmap].cumCost = curCost
					}
				}
			}
		}
	}
	return bestPlan[totalBitmap].p, nil
}

func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

func (s *joinReorderDPSolver) nodesAreConnected(leftMask, rightMask uint,
	totalEqEdges []joinGroupEqEdge, totalNonEqEdges []joinGroupNonEqEdge) ([]joinGroupEqEdge, []expression.Expression) {
	var (
		usedEqEdges []joinGroupEqEdge
		otherConds  []expression.Expression
	)
	for _, edge := range totalEqEdges {
		lIdx := edge.nodeIDs[0]
		rIdx := edge.nodeIDs[1]
		if ((leftMask&(1<<lIdx)) > 0 && (rightMask&(1<<rIdx)) > 0) || ((leftMask&(1<<rIdx)) > 0 && (rightMask&(1<<lIdx)) > 0) {
			usedEqEdges = append(usedEqEdges, edge)
		}
	}
	for _, edge := range totalNonEqEdges {
		// If the result is false, means that the current group hasn't covered the columns involved in the expression.
		if edge.nodeIDMask&(leftMask|rightMask) != edge.nodeIDMask {
			continue
		}
		// Check whether this expression is only built from one side of the join.
		if edge.nodeIDMask&leftMask == 0 || edge.nodeIDMask&rightMask == 0 {
			continue
		}
		otherConds = append(otherConds, edge.expr)
	}
	return usedEqEdges, otherConds
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}

func isOverlap(lBitmap, rBitmap uint) bool {
	return lBitmap&rBitmap > 0
}

func adjacent2Subnet(adjacent [][]int) [][]int {
	visited := make([]bool, len(adjacent))
	subnets := make([][]int, 0)
	for nodeID := range adjacent {
		if visited[nodeID] {
			continue
		}
		queue := []int{nodeID}
		visited[nodeID] = true
		subnet := make([]int, 0)
		var mask uint64
		var head int
		for len(queue) > 0 {
			head, queue = queue[0], queue[1:]
			subnet, mask = append(subnet, head), mask|1<<head
			connects := adjacent[head]
			for _, target := range connects {
				if visited[target] {
					continue
				}
				queue = append(queue, target)
				visited[target] = true
			}
		}
		subnets = append(subnets, subnet)
	}
	return subnets
}

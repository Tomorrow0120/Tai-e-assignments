/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.Edge;

import java.util.ArrayDeque;
import java.util.Deque;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Deque<Node> worklist = new ArrayDeque<>();

        for (Node node : cfg) {
            worklist.add(node);
        }

        while (!worklist.isEmpty()) {
            Node node = worklist.removeFirst();


            Fact in;
            if (node.equals(cfg.getEntry())) {
                in = result.getInFact(node);
            } else {
                in = analysis.newInitialFact();
                for (Node pred : cfg.getPredsOf(node)) {
                    analysis.meetInto(result.getOutFact(pred), in);
                }
                result.setInFact(node, in);
            }

            // 2. 计算 OUT = transfer(IN)
            Fact out = result.getOutFact(node);
            if (analysis.transferNode(node, in, out)) {
                // 3. 如果 OUT 变了，把后继加入 worklist
                for (Node succ : cfg.getSuccsOf(node)) {
                    if (!worklist.contains(succ)) {
                        worklist.add(succ);
                    }
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Deque<Node> worklist = new ArrayDeque<>();

        // 把所有节点加入 worklist
        for (Node node : cfg) {
            worklist.add(node);
        }

        while (!worklist.isEmpty()) {
            Node node = worklist.removeFirst();

            Fact out = result.getOutFact(node);
            if(!cfg.isExit(node)) {
                out = analysis.newInitialFact();
                for (Node succ : cfg.getSuccsOf(node)) {
                    analysis.meetInto(result.getInFact(succ), out);
                }
                result.setOutFact(node, out);
            }

            // 2. 计算 IN = transfer(OUT)
            Fact in = result.getInFact(node);
            if (analysis.transferNode(node, in, out)) {
                // 3. 如果 IN 变了，把前驱加入 worklist
                for (Node pred : cfg.getPredsOf(node)) {
                    if (!worklist.contains(pred)) {
                        worklist.add(pred);
                    }
                }
            }
        }

    }
}

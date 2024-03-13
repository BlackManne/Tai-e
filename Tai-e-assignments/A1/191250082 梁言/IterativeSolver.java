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
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.ir.exp.Var;

import java.util.Set;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        boolean changeOrNot = true;
        while(changeOrNot){
            System.out.println(changeOrNot);
            changeOrNot = false;
            Set<Node> nodes = cfg.getNodes();
            for(Node node: nodes){
                //找到node的全部后继
                Set<Node> successors = cfg.getSuccsOf(node);
                Fact out = result.getOutFact(node);
                //全部后继meet在一起成一个union
                for(Node succ: successors){
                    analysis.meetInto(result.getInFact(succ),out);
                }
                Fact in = result.getInFact(node);
                //做transfer,如果有一个transfer是true，就代表整个IN中发生了变化，继续进行while循环
                boolean change = analysis.transferNode(node, in, out);
//                result.setInFact(node,in);
//                result.setOutFact(node,out);
                //false的时候赋值，如果赋值是false没影响，如果是true的话，之后也就不用再管了
                if(!changeOrNot)
                    changeOrNot = change;
            }
        }
    }
}

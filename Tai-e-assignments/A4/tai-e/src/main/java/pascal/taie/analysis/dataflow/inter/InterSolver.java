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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
//        List<Method> entries= this.icfg.entryMethods().toList();
//        //先处理所有entry方法的entry结点
//        for(Method method: entries){
//            Node entry = this.icfg.getEntryOf(method);
//            result.setInFact(entry, analysis.newInitialFact());
//            result.setOutFact(entry, analysis.newBoundaryFact(entry));
//        }
//        //再处理之外的节点
        for(Node node: this.icfg.getNodes()){
//            if(entries.contains(node))   //如果是entry节点就不处理
//                continue;
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
    }

    private void doSolve() {
//        LinkedList<Node> worklist = new LinkedList<>();
        //把所有节点加入worklist
        workList = new LinkedList<>();
        for(Node node:this.icfg){
            workList.add(node);
        }
        while(!workList.isEmpty()){
//            if(worklist.size() > 6)
//                System.out.println("11111");
            Node node = workList.remove();
            //找到该节点全部前驱
            Set<ICFGEdge<Node>> list = this.icfg.getInEdgesOf(node);
            Fact in = result.getInFact(node);
            for(ICFGEdge<Node> pre: list){
                analysis.meetInto(analysis.transferEdge(pre, result.getOutFact(pre.getSource())), in);
            }
            boolean changeornot = analysis.transferNode(node, in, result.getOutFact(node));
            //如果改了就把所有后继加进去
            if(changeornot){
                Set<Node> succs = this.icfg.getSuccsOf(node);
                workList.addAll(succs);
            }
        }
    }
}

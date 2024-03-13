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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.Assignment;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;
import soot.jimple.IfStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        if(cfg.getNodes().size() > 4){
            System.out.println("1111");
        }

        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        //要找的就是1.无用赋值，2.if和switch因为条件语句值是常量因此不能到达的分支
        //还有3.控制流不可达？

        //遍历CFG图,具体做法是从entry节点开始，维护一个队列，队列为空时不继续
        LinkedList<Stmt> queue = new LinkedList<>();
        Set<Stmt> set = new HashSet<>();
        queue.add(cfg.getEntry());
        while(!queue.isEmpty()){
            Stmt node = queue.remove();
            boolean deadAssignOrNot = false;
            //使用set可以取消重复，避免重复加入
            if(node instanceof If){
                ConditionExp conditionExp = ((If) node).getCondition();
                //如果是true，false的分支就是dead的
                //if语句的判断值，如果是true那么false失效，如果是false那么true失效；如果不是常量就不管
                if(ConstantPropagation.evaluate(conditionExp, constants.getInFact(node)).isConstant()){
                    //所以如果是true就把true能到达的全部加进去，否则把false能到达的全部加进去
                    boolean conditionValue = ConstantPropagation.evaluate(conditionExp, constants.getInFact(node)).getConstant() == 1;
                    Set<Edge<Stmt>> edges = cfg.getOutEdgesOf(node);
                    for(Edge<Stmt> edge: edges) {
                        if ((conditionValue && edge.getKind() == Edge.Kind.IF_TRUE)
                                || (!conditionValue && edge.getKind() == Edge.Kind.IF_FALSE)) {
                            Stmt target = edge.getTarget();
                            //为了处理循环，不能多次加入set
                            if(!set.contains(target)){
                                queue.add(target);
                                set.add(node);
                            }
                            break;
//                        //通过fallthrough判断把整个分支的代码块找到
//                        while(target.canFallThrough() || target instanceof Goto){
//                            deadCode.add(target);
//                            target = ((Edge<Stmt>) cfg.getOutEdgesOf(target).toArray()[0]).getTarget();
//
                        }
                    }
                    //如果是常量就进行完了，否则继续进行后面的，全部加入进去
                    continue;
                }
            }
            if(node instanceof SwitchStmt){
                Var var = ((SwitchStmt) node).getVar();
                //通过constants数组获得switch-case的数值
                if(ConstantPropagation.evaluate(var, constants.getInFact(node)).isConstant()){
                    Stmt target = null;
                    boolean defaultOrNot = true;
                    Value switchValue = ConstantPropagation.evaluate(var, constants.getInFact(node));
                    //如果是某个case就进去
                    List<Pair<Integer, Stmt>> caseAndTargets = ((SwitchStmt) node).getCaseTargets();
                    for(Pair<Integer, Stmt> pair : caseAndTargets){
                        if(pair.first().equals(switchValue.getConstant())){
                            target = pair.second();
                            defaultOrNot = false;
                            break;
                        }
                    }
                    //如果没有对应的case就default
                    if(defaultOrNot)
                        target = ((SwitchStmt) node).getDefaultTarget();
                    assert target != null;
                    if(!set.contains(target)){
                        queue.add(target);
                        set.add(node);
                    }
                    continue;
                }
            }
            if(node instanceof AssignStmt){
                //1.如果左侧是普通变量，那么可以根据活跃变量得到
                if(((AssignStmt<?, ?>) node).getLValue() instanceof Var var){
                    //判断左侧的赋值是否是无用的
                    //如果左侧的变量不在这一点的活跃变量表中，说明这一点这个变量不活跃
                    if(!liveVars.getOutFact(node).contains(var) && DeadCodeDetection.hasNoSideEffect(((AssignStmt<?, ?>) node).getRValue())){
//                    deadCode.add(node);
                        deadAssignOrNot = true;
                    }
                }
                //2.如果是一个赋值语句，但是左侧不是变量（如o.m=xxx)，判断右侧是否有用（用函数）

            }

            if(!deadAssignOrNot)
                set.add(node);
            //为了避免某个语句在循环里面，要在这边进行去重，类似if的情况
            Set<Stmt> succs = cfg.getSuccsOf(node);
            for(Stmt stmt: succs){
                if(!set.contains(stmt))
                    queue.add(stmt);
            }
        }
        for(Stmt stmt: cfg.getNodes()){
            //因为存在exit结点没进来的情况（无限循环，所以要排除这个）
            if(cfg.isExit(stmt))
                continue;
            if(!set.contains(stmt))
                deadCode.add(stmt);
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}

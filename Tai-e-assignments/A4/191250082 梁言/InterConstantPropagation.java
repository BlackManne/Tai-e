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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.ReferenceType;

import java.util.Collection;
import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
//        CPFact oldOut = out.copy();
//        cp.transferNode(stmt, in, out);
//        if(stmt instanceof Invoke){
//            Var kill = ((Invoke) stmt).getLValue();
//            out.remove(kill);
//        }
        CPFact oldOut = out.copy();
//        if(out != null)
//            oldOut = out.copy();
        //2.然后合并in和out，把in merge进out
        meetInto(in, out);
        return !out.equals(oldOut);
//        return cp.transferNode(stmt, in, out);
    }

    //不是方法调用，直接用常量传播的代码
    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Stmt source = edge.getSource();
        if(source instanceof Invoke){
            //等号左侧没有变量，不修改act
            Var kill = ((Invoke) source).getResult();
            if(kill == null)
                return out;
            //左侧有变量
            CPFact copy = out.copy();
            copy.remove(kill);
            return copy;
        }
        //到这里其实就有问题了
        return null;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        //source是调用语句
        Stmt source = edge.getSource();
        //方法声明语句
        JMethod callee = edge.getCallee();
        if(source instanceof Invoke){
            CPFact callFact = new CPFact();
            //实参列表
            List<Var> actualParams = ((Invoke) source).getInvokeExp().getArgs();
            //形参列表
            List<Var> funcParams = callee.getIR().getParams();
            for(int i = 0; i < actualParams.size(); i ++){
                Var var = actualParams.get(i);
                //只考虑int型
                if(var.getType() instanceof ReferenceType || ConstantPropagation.canHoldInt(var)){
                    Value value = callSiteOut.get(var);
                    //考虑形参是否是int型
                    Var funcVar = funcParams.get(i);
                    if(funcVar.getType() instanceof ReferenceType || ConstantPropagation.canHoldInt(funcVar)){
                        callFact.update(funcVar,value);
                    }
                }
            }
            return callFact;
        }
        return null;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        Stmt source = edge.getSource();
        if(source instanceof Invoke){
            Var kill = ((Invoke) source).getLValue();
            returnOut.remove(kill);
        }
        Collection<Var> returnVars = edge.getReturnVars();
//        if(returnVars.size() > 0)
//            System.out.println(returnVars.size());
        Stmt callSite =  edge.getCallSite();
        CPFact returnFact = new CPFact();
        if(callSite instanceof Invoke){
            //如果该callsite没有左值，可以返回一个空的fact
            //这个lvalue是调用者的返回值
            Var lValue = ((Invoke) callSite).getLValue();
            if(lValue == null)
                return returnFact;
            //
//            if(ConstantPropagation.canHoldInt(lValue)){
//                Stmt target = edge.getTarget();
                //获取该条return边return的Var是什么
//                if(target.getDef().isPresent() && target.getDef().get() instanceof Var returnVar){
//                    Value returnValue = returnOut.get(returnVar);
//                    returnFact.update(lValue, returnValue);
//                    return returnFact;
//                }
            if(lValue.getType() instanceof ReferenceType || ConstantPropagation.canHoldInt(lValue)){
                Var[] varList = returnVars.toArray(new Var[0]);
                Value returnValue = returnOut.get(varList[0]);
                if(returnVars.size() == 1){
                    returnFact.update(lValue,returnValue);
                }else{
                    for(int i = 1; i < varList.length; i ++){
                        returnValue = cp.meetValue(returnValue, returnOut.get(varList[i]));
                    }
                    returnFact.update(lValue,returnValue);
                }
                return returnFact;
            }

        }
        return null;
    }
}

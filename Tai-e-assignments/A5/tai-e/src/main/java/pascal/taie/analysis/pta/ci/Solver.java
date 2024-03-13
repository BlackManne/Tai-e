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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if(!callGraph.contains(method)){
            callGraph.addReachableMethod(method);
            List<Stmt> statements = method.getIR().getStmts();
            for(Stmt statement: statements){
                //处理所有x = new T()语句
                if (statement instanceof New allocSite){
                    Var var = allocSite.getLValue();
                    Obj obj = heapModel.getObj(allocSite);
                    VarPtr varPtr = pointerFlowGraph.getVarPtr(var);
//                    varPtr.getPointsToSet().addObject(obj);
                    workList.addEntry(varPtr, new PointsToSet(obj));
                }
                //处理所有非静态x = y的copy语句
                if (statement instanceof Copy copySite){
                    Var target = copySite.getLValue();
                    Var source = copySite.getRValue();
                    VarPtr targetPtr = pointerFlowGraph.getVarPtr(target);
                    VarPtr sourcePtr = pointerFlowGraph.getVarPtr(source);
                    addPFGEdge(sourcePtr,targetPtr);
                }
                //处理静态的load方法 y = T.f
                if(statement instanceof LoadField loadField && loadField.isStatic()){
                    VarPtr target = pointerFlowGraph.getVarPtr(loadField.getLValue());
                    StaticField staticField = pointerFlowGraph.getStaticField(loadField.getFieldRef().resolve());
                    addPFGEdge(staticField, target);
                }
                //处理静态的store方法 T.f = y
                if(statement instanceof StoreField storeField && storeField.isStatic()){
                    VarPtr source = pointerFlowGraph.getVarPtr(storeField.getRValue());
                    StaticField staticField= pointerFlowGraph.getStaticField(storeField.getFieldRef().resolve());
                    addPFGEdge(source,staticField);
                }
                //处理静态的方法调用
                if(statement instanceof Invoke invoke && invoke.isStatic()){
                    JMethod jmethod = resolveCallee(null,invoke);
                    if(!callGraph.getCallersOf(jmethod).contains(invoke)){
                        callGraph.addEdge(new Edge<>(CallKind.STATIC, invoke, jmethod));
                        addReachable(jmethod);
                        List<Var> actualParams = invoke.getInvokeExp().getArgs();
                        List<Var> funcParams = jmethod.getIR().getParams();
                        List<Var> returnVar = jmethod.getIR().getReturnVars();
                        for(int i = 0; i < actualParams.size(); i ++){
                            addPFGEdge(pointerFlowGraph.getVarPtr(actualParams.get(i)), pointerFlowGraph.getVarPtr(funcParams.get(i)));
                        }
                        //如果有返回值
                        Var mret = invoke.getLValue();
                        if(mret != null){
                            for (Var value : returnVar) {
                                addPFGEdge(pointerFlowGraph.getVarPtr(value), pointerFlowGraph.getVarPtr(mret));
                            }
                        }

                    }
                }
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        //说明没有s->t的这条边
        if(!pointerFlowGraph.getSuccsOf(source).contains(target)){
            pointerFlowGraph.addEdge(source,target);
            PointsToSet pointsToSet = source.getPointsToSet();
            if(!pointsToSet.isEmpty()){
                workList.addEntry(target,pointsToSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet pts = entry.pointsToSet();
            Pointer n = entry.pointer();
            PointsToSet delta = propagate(n,pts);
            if(n instanceof VarPtr){
                Var var = ((VarPtr) n).getVar();
                Set<Obj> objects = delta.getObjects();
                for(Obj obj: objects){
                    List<StoreField> storeFields = var.getStoreFields();
                    for(StoreField storeField: storeFields){
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()), pointerFlowGraph.getInstanceField(obj,storeField.getFieldRef().resolve()));
                    }
                    List<LoadField> loadFields = var.getLoadFields();
                    for(LoadField loadField: loadFields){
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj,loadField.getFieldRef().resolve()),pointerFlowGraph.getVarPtr(loadField.getLValue()));
                    }
                    List<StoreArray> storeArrays = var.getStoreArrays();
                    for(StoreArray storeArray: storeArrays){
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()), pointerFlowGraph.getArrayIndex(obj));
                    }
                    List<LoadArray> loadArrays = var.getLoadArrays();
                    for(LoadArray loadArray: loadArrays){
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        //delta = pts - ptn
        PointsToSet ptn = pointer.getPointsToSet();
        PointsToSet delta = new PointsToSet();
        Set<Obj> pts = pointsToSet.getObjects();
        // ptn U= pts
        for(Obj obj: pts) {
            //A里面有B里面没有
            if (!ptn.contains(obj)) {
                delta.addObject(obj);
                ptn.addObject(obj);
            }
        }
        if(!delta.isEmpty()){
            //foreach n → s ∈ PFG
            Set<Pointer> succsOfN = pointerFlowGraph.getSuccsOf(pointer);
            for(Pointer p: succsOfN){
                //add <s, pts> to WL
                workList.addEntry(p,delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        List<Invoke> invokes = var.getInvokes();
        for(Invoke invoke: invokes){
            JMethod jMethod = resolveCallee(recv,invoke);
            VarPtr mthis = pointerFlowGraph.getVarPtr(jMethod.getIR().getThis());
//            mthis.getPointsToSet().addObject(recv);
//            workList.addEntry(mthis, mthis.getPointsToSet());
            workList.addEntry(mthis, new PointsToSet(recv));
            if(!callGraph.getCallersOf(jMethod).contains(invoke)){
                Edge<Invoke, JMethod> edge = null;
                if(invoke.isSpecial())
                    edge = new Edge<>(CallKind.SPECIAL, invoke, jMethod);
                else if(invoke.isInterface())
                    edge = new Edge<>(CallKind.INTERFACE, invoke, jMethod);
                else if(invoke.isVirtual())
                    edge = new Edge<>(CallKind.VIRTUAL, invoke, jMethod);
                else if(invoke.isDynamic())
                    edge = new Edge<>(CallKind.DYNAMIC, invoke, jMethod);
                callGraph.addEdge(edge);
                addReachable(jMethod);
                List<Var> actualParams = invoke.getInvokeExp().getArgs();
                List<Var> funcParams = jMethod.getIR().getParams();
                List<Var> returnVar = jMethod.getIR().getReturnVars();
                for(int i = 0; i < actualParams.size(); i ++){
                    addPFGEdge(pointerFlowGraph.getVarPtr(actualParams.get(i)), pointerFlowGraph.getVarPtr(funcParams.get(i)));
                }
                Var mret = invoke.getLValue();
                if(mret != null){
                    for (Var value : returnVar) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(value), pointerFlowGraph.getVarPtr(mret));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}

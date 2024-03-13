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

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        //IN[exit]为空
        return new SetFact<>();
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        //IN[B]为空
        return new SetFact<>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me
        //1先保存原来的数值，然后处理out
        //2然后-def
        //3然后和use做∪
        //1先保存一下原来的数值
        SetFact<Var> beforeIn = new SetFact<>();
        if(!(in == null || in.size() == 0))
            beforeIn = in.copy();
        //处理out
        assert(in != null);
        if(out != null && out.size() != 0)
            in.union(out);
        //2处理def
        Optional<LValue> def = stmt.getDef();
        List<RValue> use = stmt.getUses();
        //判断Def是否为空，不为空的话从OUT集合里删除
        if(def.isPresent()){
            //判断是不是Var
            LValue definition = def.get();
            if(definition instanceof Var){
                if(in.size()!= 0 && in.contains((Var) definition)){
                    in.remove((Var) definition);
                }
            }
        }
        SetFact<Var> uses = new SetFact<>();
        for(RValue rValue: use){
            if(rValue instanceof Var){
                //集合里面没有数值的时候才要加入集合
                if(!uses.contains((Var)rValue))
                    uses.add((Var)rValue);
            }
        }
        in.union(uses);
        //相等的话说明没有变化，不相等有变化，应该返回true
        return !in.equals(beforeIn);
    }
}

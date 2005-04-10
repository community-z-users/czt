/*
 * FlatSetCompNew.java
 *
 * Created on 07 April 2005, 12:32
 */

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.EnvirUtils;
import net.sourceforge.czt.animation.eval.EvalException;
import net.sourceforge.czt.animation.eval.Flatten;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RefName;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.util.Factory;

/**
 *
 * @author leo
 */
public class FlatSetCompNew extends FlatSetComp {
    
    protected Envir declsEnv_;
    protected Flatten flatten_;
    protected Factory factory_;
    protected FlatPredList predsF_;
    protected FlatPredList predsDecls_;
    
    protected Mode bodyMode_;
    
    /** Creates a new instance of FlatSetCompNew */
    public FlatSetCompNew(/*@non_null@*/ZLive zlive,
            /*@non_null@*/List/*<Decl>*/ decls,
            Pred pred,
            /*@non_null@*/Expr result,
            /*@non_null@*/RefName set) {
        super(zlive, decls, pred, result, set);
        flatten_ = zlive.getFlatten();
        factory_ = zlive.getFactory();
        declsEnv_ = new Envir();
        predsDecls_ = new FlatPredList(zlive);
        for (Iterator i = decls.iterator(); i.hasNext(); ) {
            Decl decl = (Decl)i.next();
            predsDecls_.addDecl(decl);
            addDeclEnvInfo(decl);
        }
        
        predsF_ = new FlatPredList(zlive);        
        if (pred != null) {
            predsF_.addPred(pred);            
        }
        // Now add 'resultName = result'.
        RefExpr resultExpr = zlive.getFactory().createRefExpr(resultName_);
        Pred eq = zlive.getFactory().createEquality(resultExpr, result);
        predsF_.addPred(eq);        
    }
    
    protected void addDeclEnvInfo(Decl decl) {
        //try {
        if (decl instanceof VarDecl) {
            VarDecl vdecl = (VarDecl) decl;
            Expr type = vdecl.getExpr();
            // Or lets just assume simple (RefName) types at the moment?
            //RefName typeName = flatten_.flattenExpr(type, predsDecls_.predlist_);
            //declsEnv_ = declsEnv_.add(typeName, null);
            //RefExpr typeExpr = factory_.createRefExpr(typeName);
            //declsEnv_ = declsEnv_.add(typeName, typeExpr);
            Iterator i = vdecl.getDeclName().iterator();
            while (i.hasNext()) {
                DeclName var = (DeclName) i.next();
                RefName varref = factory_.createRefName(var);
                //unflattened expresion type?
                declsEnv_ = declsEnv_.add(varref, type);
            }
        } //        else if (decl instanceof ConstDecl) {
        //            ConstDecl cdecl = (ConstDecl) decl;
        //            DeclName var = cdecl.getDeclName();
        //            boundVars_.add(var);
        //            Expr expr = cdecl.getExpr();
        //            RefName varref = factory_.createRefName(var);
        //            boundVars_.add(varref);
        //            flatten_.flattenPred(factory_.createMemPred(varref, expr), predlist_);
        //        }
        else {
            throw new EvalException("Unknown kind of Decl: " + decl);
        }
        //} catch (CommandException exception) {
        //    throw new EvalException(exception);
        //}
    }
    
    private Envir freeVarsEnvir() {
        Envir env = new Envir();
        for(Object o : freeVars()) {
            RefName free = (RefName)o;
            env = env.add(free, null);
        }
        return env;
    }
    
    public Mode chooseMode(Envir env) {
        Mode m = super.chooseMode(env);
        if (m == null) {
            
            // Create the Env I = freeVars() + env
            ArrayList inputs = new ArrayList(args.size());
            int varsDefined = setInputs(env, inputs);
            for(int i=0;i<inputs.size();i++) {
                if (((Boolean)inputs.get(i)).booleanValue() == false)
                    env = env.add((RefName)args.get(i),null);
            }
            bodyMode_ = null; // reset bodyMode
            Envir D = EnvirUtils.copy(declsEnv_);
            if (EnvirUtils.disjoint(D, env)) { // D \cap I = \emptyset
                env = EnvirUtils.merge(env, declsEnv_);
                // Execute F in {D|F} = s in an env, where the freeVars() are ok?
                bodyMode_ = predsF_.chooseMode(env);
                predsF_.startEvaluation(bodyMode_, env);
                Envir O = predsF_.getOutputEnvir();
                if (EnvirUtils.subset(D, O)) { // D.sameAs(O); D = O
                    m = new Mode(env, inputs, bodyMode_.getSolutions());
                } else {
                    bodyMode_ = null;
                }
            }
        }
        // bind (set |-> this), so that size estimates work better.
        if (m != null)
            m.getEnvir().setValue((RefName)args.get(args.size()-1), this);
        return m;
    }
}

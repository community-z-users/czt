/*
 * FlatSetCompNew.java
 *
 * Created on 07 April 2005, 12:32
 */

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.BitSet;
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
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.ZRefName;
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
            /*@non_null@*/List<Decl> decls,
            Pred pred,
            /*@non_null@*/Expr result,
            /*@non_null@*/ZRefName set) {
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
            // Or lets just assume simple (ZRefName) types at the moment?
            //ZRefName typeName = flatten_.flattenExpr(type, predsDecls_.predlist_);
            //declsEnv_ = declsEnv_.add(typeName, null);
            //RefExpr typeExpr = factory_.createRefExpr(typeName);
            //declsEnv_ = declsEnv_.add(typeName, typeExpr);
            for (DeclName d : vdecl.getDeclName()) {
                ZDeclName dvar = (ZDeclName) d;
                ZRefName varref = factory_.createZRefName(dvar);
                //unflattened expresion type?
                declsEnv_ = declsEnv_.add(varref, type);
            }
        } //        else if (decl instanceof ConstDecl) {
        //            ConstDecl cdecl = (ConstDecl) decl;
        //            ZDeclName var = cdecl.getDeclName();
        //            boundVars_.add(var);
        //            Expr expr = cdecl.getExpr();
        //            ZRefName varref = factory_.createZRefName(var);
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
        for(ZRefName free : freeVars()) {
            env = env.add(free, null);
        }
        return env;
    }
    
    public Mode chooseMode(Envir env) {
        Mode m = super.chooseMode(env);
        if (m == null) {
            
            // Create the Env I = freeVars() + env
            BitSet inputs = getInputs(env);
            for(int i=0;i<args.size();i++) {
                if ( ! (inputs.get(i)) == false)
                    env = env.add(args.get(i),null);
            }
            bodyMode_ = null; // reset bodyMode
            Envir D = EnvirUtils.copy(declsEnv_);
            if (EnvirUtils.disjoint(D, env)) { // D \cap I = \emptyset
                env = EnvirUtils.merge(env, declsEnv_);
                // Execute F in {D|F} = s in an env, where the freeVars() are ok?
                bodyMode_ = predsF_.chooseMode(env);
                predsF_.setMode(bodyMode_);
                predsF_.startEvaluation();
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
            m.getEnvir().setValue(args.get(args.size()-1), this);
        return m;
    }
}

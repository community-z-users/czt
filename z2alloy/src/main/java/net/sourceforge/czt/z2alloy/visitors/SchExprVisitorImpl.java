package net.sourceforge.czt.z2alloy.visitors;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z2alloy.Z2Alloy;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.ExprVar;
import net.sourceforge.czt.z2alloy.ast.Field;
import net.sourceforge.czt.z2alloy.ast.Func;
import net.sourceforge.czt.z2alloy.ast.Module;
import net.sourceforge.czt.z2alloy.ast.PrimSig;
import net.sourceforge.czt.z2alloy.ast.Sig;

public class SchExprVisitorImpl extends ExprVisitorAbs implements SchExprVisitor<AlloyExpr> {

  private String name;
  
  public SchExprVisitorImpl(String name, PredVisitorImpl pred) {
    super(pred);
    this.name = name;
  }

  //	
  // /**
  // * creates a new signiture to represent the schema <br>
  // * includes all the fields of the schema <br>
  // * if the schema contains an InclDecl, it includes all the fields of this
  // * schema <br>
  // * the predicate for this schema is included in the new signiture <br>
  // * eg
  // *
  // * <pre>
  // * given sig A {a : univ}{pred_A[a]} pred pred_A[a] {...}
  // *
  // * \begin{schema}{B}
  // * A
  // * c : C
  // * \where
  // * ...
  // * \end{schema}
  // *</pre>
  // *
  // * translates to:
  // *
  // * <pre>
  // * sig B {a : univ, c : C} {pred_B[a,c]} pred pred_B {... and pred_A[a]}
  // * </pre>
  // *
  // */
  public AlloyExpr visitSchExpr(SchExpr schExpr) {
    Sig sig = new PrimSig(name);
    AlloyExpr fieldPred = null;
    for (Decl d : schExpr.getZSchText().getZDeclList()) {
      if (d instanceof VarDecl) {
        VarDecl vardecl = (VarDecl) d;
        ZNameList nameList = vardecl.getName();
        for (Name name : nameList) {
          sig.addField(new Field(Z2Alloy.getInstance().print(name), visit(vardecl.getExpr())));
        }
      } else if (d instanceof InclDecl) {
        InclDecl incldecl = (InclDecl) d;
        AlloyExpr newPred = addInclSig((Sig) visit(
            incldecl.getExpr()), sig);
        if (newPred != null && fieldPred != null)
          fieldPred = newPred.and(fieldPred);
        else if (newPred != null)
          fieldPred = newPred;
      } else {
        System.err.println(d.getClass() + " not yet implemented");
        return null;
      }
    }
    Z2Alloy.getInstance().addSig(sig);
    AlloyExpr pred = visit(schExpr.getZSchText().getPred());
    if (fieldPred != null) {
      Z2Alloy.getInstance().addSigPred(sig, fieldPred);
    }

    if (pred != null) {
      Z2Alloy.getInstance().addSigPred(sig, pred);
    }
    return null;
  }

  /*
   * note that the expr returned is the new predicate the fields and stuff are
   * added within this method
   */
  private AlloyExpr addInclSig(Sig inclSig, Sig sig) {
    // so we can easily see if a field is already present
    Map<String, Field> sigfieldnames = new HashMap<String, Field>();
    // the fields needed for calling the predicate of the included sig at the
    // end
    List<AlloyExpr> args = new ArrayList<AlloyExpr>();
    // collect all the fields already included in the signature
    for (Field sigfield : sig.fields()) {
      sigfieldnames.put(sigfield.label(), sigfield);
    }
    // collect all the fields in the included signature
    for (Field subfield : inclSig.fields()) {
      if (!sigfieldnames.containsKey(subfield.label())) { // ie they aren't
                                                          // already present
        // make a new field, and add it to the signature
        Field newfield = new Field(subfield.label(), subfield.expr());
        sig.addField(newfield);
        sigfieldnames.put(newfield.label(), newfield);
      }
      // put the field in args - doesn't matter if it comes from the old or new
      // location
      Field field = sigfieldnames.get(subfield.label());
      args.add(new ExprVar(field.label(), field.expr()));
    }
    Func f;
    Module module = Z2Alloy.getInstance().module();
    // this is to put the included sig predicate in the predicate
    if (module.containsFunc("pred_" + inclSig.label())) {
      f = module.getFunc("pred_" + inclSig.label());
    }
    // this case is if it is a primed - the correct pred to find is the unprimed
    // version
    // TODO clare could be made more general
    else if (module.containsFunc("pred_" + inclSig.label().replaceAll("'", ""))) {
      f = module.getFunc("pred_" + inclSig.label().replace("'", ""));
    }
    // if there isn't a predicate for some reason - nothing to add.
    else {
      return null;
    }
    return f.call(args.toArray(new AlloyExpr[0]));
  }

}

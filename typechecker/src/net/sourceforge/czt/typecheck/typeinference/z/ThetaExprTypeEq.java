package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.9
public class ThetaExprTypeEq
  implements TypeInferenceRule
{
  private Sequent sequent_;

  private TypeChecker checker_;

  private ZFactory factory_;
  private TypeEnvInt typeEnv_;

  public ThetaExprTypeEq(TypeEnvInt env, ThetaExpr term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    factory_ = checker_.getFactory();
  }

  public Object solve() throws TypeException
  {
    ThetaExpr term = (ThetaExpr) sequent_.getTerm();
    Expr expr = (Expr) term.getExpr().accept(checker_);
    List strokes = term.getStroke();
    boolean gotStrokes = true ? false : (strokes.size() == 0);
    Type type = checker_.getTypeFromAnns(expr);
    if (! (type instanceof PowerType)) {
      throw new TypeException(ErrorKind.POWERTYPE_NEEDED, type);
    }
    Type innerType = ((PowerType) type).getType();
    if (! (innerType instanceof SchemaType)) {
      throw new TypeException(ErrorKind.SCHEMATYPE_NEEDED, innerType);
    }
    List sig = ((SchemaType) innerType).getSignature().getNameTypePair();
    DeclName tmpDn = null;
    Type type1 = null;
    NameTypePair ntp = null;
    List tmpStrokes = null;
    for (int i = 0; i < sig.size(); i++) {
      ntp = (NameTypePair) sig.get(i);
      type1 = ntp.getType();
      tmpDn = (DeclName) ntp.getName().accept(checker_);
      tmpStrokes = tmpDn.getStroke();
      Vector nv = new Vector(tmpStrokes);
      nv.addAll(strokes);
      DeclName dn =
        factory_.createDeclName(tmpDn.getWord(), nv, tmpDn.getId());
      NameTypePair ntp1 = typeEnv_.search(dn);
      // actually should delay the throw of these exceptions...
      if (ntp1 == null) {
        throw new TypeException(ErrorKind.UNDECLAREDNAME, tmpDn);
      }
      Type tmpType = ntp1.getType();
      if ((tmpType instanceof GenType) || (tmpType instanceof VariableType)) {
        throw new TypeException(ErrorKind.GENTYPE_FOUND, tmpType);
      }
      if (! TypeChecker.unify(type1, tmpType)) {
        throw new TypeException(ErrorKind.NAMETYPEPAIR_NOT_FOUND, ntp);
      }
    }
    term = (ThetaExpr) checker_.addAnns(term, innerType);
    return term;
  }
}

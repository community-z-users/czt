package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.10
public class BindSelExprTypeEq implements TypeInferenceRule
{
  private Sequent sequent_;

  private TypeChecker checker_;

  private ZFactory factory_;
  private TypeEnvInt typeEnv;

  public BindSelExprTypeEq(TypeEnvInt env, BindSelExpr term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    factory_ = checker_.getFactory();
  }

  public Object solve() throws TypeException
  {
    BindSelExpr term = (BindSelExpr) sequent_.getTerm();
    Expr expr = (Expr) term.getExpr().accept(checker_);
    // haven't done yet
    RefName refName = (RefName) term.getName().accept(checker_);
    DeclName dn = (DeclName) refName.getDecl().accept(checker_);
    Type type = checker_.getTypeFromAnns(expr);
    if (! (type instanceof SchemaType)) {
      throw new TypeException(ErrorKind.SCHEMATYPE_NEEDED, type);
    }
    List ntps = ((SchemaType) type).getSignature().getNameTypePair();
    NameTypePair ntp = TypeChecker.findDeclNameInSignature(dn, ntps);
    if (ntp == null) {
      throw new TypeException(ErrorKind.DECLNAME_NOT_FOUND_IN_SCHEMA,
                              dn,
                              type);
    }
    Type resultType = ntp.getType();
    term = (BindSelExpr) checker_.addAnns(term, resultType);
    return term;
  }
}

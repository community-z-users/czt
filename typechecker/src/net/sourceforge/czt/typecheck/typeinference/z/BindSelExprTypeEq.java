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
public class BindSelExprTypeEq extends TypeInferenceRule
{
  public BindSelExprTypeEq(SectTypeEnv sectTypeEnv,
			   BindSelExpr bindSelExpr,
			   TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, bindSelExpr);
    typechecker_ = typechecker;
  }

  public Object solve() throws TypeException
  {
    BindSelExpr term = (BindSelExpr) sequent_.getTerm();
    Expr expr = (Expr) term.getExpr().accept(typechecker_);
    // haven't done yet
    RefName refName = (RefName) term.getName().accept(typechecker_);
    DeclName dn = (DeclName) refName.getDecl().accept(typechecker_);
    Type type = typechecker_.getTypeFromAnns(expr);
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
    term = (BindSelExpr) typechecker_.addAnns(term, resultType);
    return term;
  }
}

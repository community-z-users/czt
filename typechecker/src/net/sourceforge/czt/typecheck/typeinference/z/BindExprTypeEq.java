package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.9
public class BindExprTypeEq extends TypeInferenceRule
{
  public BindExprTypeEq(SectTypeEnv sectTypeEnv,
			BindExpr bindExpr,
			TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, bindExpr);
    typechecker_ = typechecker;
  }

  public Object solve() throws TypeException
  {
    BindExpr term = (BindExpr) sequent_.getTerm();
    List pairs = term.getNameExprPair();
    Vector tmpNameList = new Vector();
    Vector tmpNTList = new Vector();
    Signature sig = factory_.createSignature(tmpNTList);
    // type of the term
    SchemaType st = factory_.createSchemaType(sig);
    NameExprPair nep = null;
    DeclName dn = null;
    Expr expr = null;
    Type type = null;
    for (int i = 0; i < pairs.size(); i++)
    {
      nep = (NameExprPair) pairs.get(i);
      dn = (DeclName) ((DeclName) nep.getName()).accept(typechecker_);
      // exception happened
      if (dn == null) continue;
      if (tmpNameList.contains(dn.getWord())) {
        // actually should delay this exception
        throw new TypeException(ErrorKind.REDECLARATION, dn);
      }
      tmpNameList.add(dn.getWord());
      expr = (Expr) ((Expr) nep.getExpr()).accept(typechecker_);
      type = typechecker_.getTypeFromAnns(expr);
      NameTypePair ntp = factory_.createNameTypePair(dn, type);
      tmpNTList.add(ntp);
    }
    term = (BindExpr) typechecker_.addAnns(term, st);
    return term;
  }
}

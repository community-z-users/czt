package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

// rule: whenever there's a SchText, enterScope & exitScope
// from the parent node
//13.2.6.14
public class SchTextTypeEq extends TypeInferenceRule
{
  public SchTextTypeEq(SectTypeEnv sectTypeEnv,
		       SchText schText, TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, schText);
    typechecker_ = typechecker;
  }

  public Object solve() throws TypeException
  {
    SchText schText = (SchText) sequent_.getTerm();

    //visit each declaration
    List decls = schText.getDecl();
    for (Iterator iter = decls.iterator(); iter.hasNext(); ) {
      Decl decl = (Decl) iter.next();
      decl.accept(typechecker_);
    }

    //visit the predicate
    Pred pred = schText.getPred();
    if (pred != null) {
      pred.accept(typechecker_);
    }

    return null;
  }
}

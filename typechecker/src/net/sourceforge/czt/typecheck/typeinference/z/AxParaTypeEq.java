package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

public class AxParaTypeEq implements TypeInferenceRule
{
  private Sequent subsequent_;
  private Sequent sequent_;

  private TypeChecker checker_;

  private boolean isGeneric_;

  private ZFactory factory_;
  private TypeEnvInt typeEnv_;

  public AxParaTypeEq(TypeEnvInt env, AxPara term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    if (term.getDeclName().size() == 0) isGeneric_ = false;
    else isGeneric_ = true;
    factory_ = checker_.getFactory();
  }

  public Object solve () throws TypeException
  {
    AxPara term = (AxPara) sequent_.getTerm();
    typeEnv_ = sequent_.getTypeEnv();
    // temp vector to store all decl names
    Vector tmpList = new Vector();
    List forParas = term.getDeclName();
    // check for duplicate in gen paras and add type annotations to DeclNames
    for (int i = 0; isGeneric_ && i < forParas.size(); i++) {
      DeclName tmpDn =
        (DeclName) ((DeclName) forParas.get(i)).accept(checker_);
      // exception happened
      if (tmpDn == null) continue;
      if (tmpList.contains(tmpDn.getWord())) {
        throw new TypeException (ErrorKind.REDECLARATION, tmpDn);
      }
      tmpList.add(tmpDn.getWord());
      // add annotation to DeclName
      GenType gt = factory_.createGenType(tmpDn);
      PowerType pt = factory_.createPowerType(gt);
      tmpDn = (DeclName) checker_.addAnns(tmpDn, pt);
      // add NameTypePair into env
      NameTypePair ntp = factory_.createNameTypePair(tmpDn, pt);
      typeEnv_.addNameTypePair(ntp);
    }
    // now form the subsequent_ of the eq
    SchText schtxt = term.getSchText();
    subsequent_ = new Sequent(typeEnv_, schtxt);

    // now take care of the schema text
    schtxt = (SchText) schtxt.accept(checker_);

    PowerType pt = (PowerType) checker_.getTypeFromAnns(schtxt);
    // is a SchemaType
    Type type = pt.getType();

    // add type annotation to the AxPara
    TypeAnn ta = factory_.createTypeAnn(type);
    term = (AxPara) checker_.addAnns(term, ta);

    return term;
  }
}

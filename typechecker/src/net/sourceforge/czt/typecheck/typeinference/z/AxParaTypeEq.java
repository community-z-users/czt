package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

public class AxParaTypeEq extends TypeInferenceRule
{
  private Sequent subsequent_;

  public AxParaTypeEq(SectTypeEnv sectTypeEnv, 
		      AxPara axPara, 
		      TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, axPara);
    typechecker_ = typechecker;
  }

  public Object solve () throws TypeException
  {
    AxPara axPara = (AxPara) sequent_.getTerm();
    TypeEnvInt typeEnv = sequent_.getTypeEnv();
    // temp vector to store all decl names
    Vector tmpList = new Vector();
    List forParas = axPara.getDeclName();
    // check for duplicate in gen paras and add type annotations to DeclNames
    for (int i = 0; i < forParas.size(); i++) {
      DeclName tmpDn =
        (DeclName) ((DeclName) forParas.get(i)).accept(typechecker_);
      // exception happened
      if (tmpDn == null) continue;
      if (tmpList.contains(tmpDn.getWord())) {
        throw new TypeException (ErrorKind.REDECLARATION, tmpDn);
      }
      tmpList.add(tmpDn.getWord());
      // add annotation to DeclName
      GenType gt = factory_.createGenType(tmpDn);
      PowerType pt = factory_.createPowerType(gt);
      tmpDn = (DeclName) typechecker_.addAnns(tmpDn, pt);
      // add NameTypePair into env
      NameTypePair ntp = factory_.createNameTypePair(tmpDn, pt);
      typeEnv.addNameTypePair(ntp);
    }
    // now form the subsequent_ of the eq
    SchText schtxt = axPara.getSchText();
    subsequent_ = new Sequent(sequent_.getSectTypeEnv(), schtxt);

    // now take care of the schema text
    schtxt = (SchText) schtxt.accept(typechecker_);

    PowerType pt = (PowerType) typechecker_.getTypeFromAnns(schtxt);
    // is a SchemaType
    Type type = pt.getType();

    // add type annotation to the AxPara
    TypeAnn ta = factory_.createTypeAnn(type);
    axPara = (AxPara) typechecker_.addAnns(axPara, ta);

    return axPara;
  }
}

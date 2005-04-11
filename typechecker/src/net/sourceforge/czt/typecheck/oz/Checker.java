/*
  Copyright (C) 2004, 2005 Tim Miller
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.typecheck.oz;

import java.util.List;
import java.lang.RuntimeException;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.typecheck.oz.impl.*;

/**
 * A super class for the *Checker classes in the typechecker.
 */
abstract public class Checker
  extends net.sourceforge.czt.typecheck.z.Checker
{
  //the information required for the typechecker classes.
  protected TypeChecker typeChecker_;

  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
    typeChecker_ = typeChecker;
  }

  //non-safe typecast
  protected static ClassType classType(Object o)
  {
    return (ClassType) o;
  }

  //non-safe typecast
  protected static VariableClassSig variableClassSig(Object o)
  {
    return (VariableClassSig) o;
  }

  //the operation expr checker
  protected Checker opExprChecker()
  {
    return typeChecker_.opExprChecker_;
  }

  //the current class name
  protected DeclName className()
  {
    return typeChecker_.className_;
  }

  //set the name of the current class
  protected void setClassName(DeclName declName)
  {
    typeChecker_.className_ = declName;
  }

  //the last of primary state variables in the current class
  protected List<DeclName> primary()
  {
    return typeChecker_.primary_;
  }

  //reset the list of primary variables in the current class to empty
  protected void resetPrimary()
  {
    typeChecker_.primary_.clear();
  }

  //typecheck a file using an instance of this typechecker
  protected List typecheck(TermA termA, SectionInfo sectInfo)
  {
    return TypeCheckUtils.typecheck(termA, sectInfo);
  }

  protected void error(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = errorAnn(termA, error, params);
    error(termA, errorAnn);
  }

  protected ErrorAnn errorAnn(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
                                     sectName(), nearestLocAnn(termA));
    return errorAnn;
  }


  //check if a name is in a signature's visibility list
  protected boolean isVisible(RefName refName, ClassRefType classRefType)
  {
    return classRefType.getVisibilityList() == null ||
      classRefType.getVisibilityList().getRefName().contains(refName);
  }

  //get the type of "self"
  protected ClassRefType getSelfType()
  {
    RefName refName = factory().createRefName(OzString.SELF, list(), null);
    RefExpr refExpr = factory().createRefExpr(refName, list(), Boolean.FALSE);
    Type2 selfType = (Type2) refExpr.accept(exprChecker());

    assert selfType instanceof ClassRefType;
    return (ClassRefType) selfType;
  }

  //check the class signature for duplicate declaration names
  protected void checkForDuplicates(ClassSig cSig)
  {
    List<DeclName> decls = list(className());

    //collect the names
    List<NameTypePair> attrDecls = cSig.getAttribute();
    for (NameTypePair pair : attrDecls) {
      decls.add(pair.getName());
    }
    Signature stateSig = cSig.getState();
    List<NameTypePair> stateDecls = stateSig.getNameTypePair();
    for (NameTypePair pair : stateDecls) {
      decls.add(pair.getName());
    }
    List<NameSignaturePair> opDecls = cSig.getOperation();
    for (NameSignaturePair pair : opDecls) {
      decls.add(pair.getName());
    }

    //check for duplicate names
    for (int i = 0; i < decls.size(); i++) {
      DeclName first = decls.get(i);
      for (int j = i + 1; j < decls.size(); j++) {
        DeclName second = decls.get(j);
        if (first.equals(second)) {
          Object [] params = {first, className()};
          error(first, ErrorMessage.REDECLARED_NAME_IN_CLASSPARA, params);
        }
      }
    }
  }

  protected Type2 instantiate(Type2 type)
  {
    Type2 result = factory().createUnknownType();

    //if this is a class type, instantiate it
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      ClassSig cSig = classType.getClassSig();

      if (!(cSig instanceof VariableClassSig)) {
        //instantiate the state
        Signature state = cSig.getState();
        if (state != null) {
          instantiate(state);
        }

        //instantiate the attributes
        List<NameSignaturePair> attrs = cSig.getAttribute();
        for (NameSignaturePair pair : attrs) {
          Signature signature = pair.getSignature();
          instantiate(signature);
        }

        //instantiate the operations
        List<NameSignaturePair> ops = cSig.getOperation();
        for (NameSignaturePair pair : ops) {
          Signature signature = pair.getSignature();
          instantiate(signature);
        }
      }

      result = classType;
    }
    //if not a class type, use the Z typechecker's instantiate method
    else {
      result = super.instantiate(type);
    }

    return result;
  }

  protected Type getType(RefName name)
  {
    Type type = super.getType(name);

    //if the name we are looking up is this class name, then we clone
    //the type because for a generic class, the parameters must be
    //instantiated even when referenced from within itself
    if (className() != null &&
        className().getWord().equals(name.getWord()) &&
        className().getStroke().equals(name.getStroke())) {
      type = (Type2) factory().cloneTerm(type);
    }

    return type;
  }

  protected List<ClassRef> getClasses(Type2 type)
  {
    List<ClassRef> classes = list();
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      classes = getClasses(classType.getClassSig());
    }
    return classes;
  }

  //get the classes that make up the parents of the class name.
  protected List<ClassRef> getClasses(ClassSig cSig)
  {
    List<ClassRef> classes = cSig.getClasses();
    return classes;
  }

  protected boolean isClassExpr(Type2 type)
  {
    boolean result = false;
    if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      if (powerType.getType() instanceof ClassType) {
        result = true;
      }
    }
    return result;
  }

  protected Signature findOperation(RefName refName, ClassSig cSig)
  {
    Signature result = null;

    //find the operation that has this name
    DeclName declName = factory().createDeclName(refName);
    List<NameSignaturePair> pairs = cSig.getOperation();
    for(NameSignaturePair pair : pairs) {
      if (declName.equals(pair.getName())) {
        result = pair.getSignature();
        break;
      }
    }
    return result;
  }
}

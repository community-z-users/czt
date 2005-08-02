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

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.util.OzString;

import net.sourceforge.czt.typecheck.oz.util.ClassNamesAnn;

/**
 */
public class SpecChecker
  extends Checker
  implements ParentVisitor
{
  //the name of the Object-Z toolkit
  public final static String OZ_TOOLKIT = "oz_toolkit";

  //a Z spec checker
  protected net.sourceforge.czt.typecheck.z.SpecChecker zSpecChecker_;

  public SpecChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zSpecChecker_ =
      new net.sourceforge.czt.typecheck.z.SpecChecker(typeChecker);

    //add the type for \oid
    DeclName oidName = factory().createDeclName(OzString.OID, list());
    ClassUnionType cuType = factory().createClassUnionType();
    PowerType oidType = factory().createPowerType(cuType);
    NameSectTypeTriple triple =
      factory().createNameSectTypeTriple(oidName, OZ_TOOLKIT, oidType);
    sectTypeEnv().add(triple);
  }

  public Object visitTerm(Term term)
  {
    return term.accept(zSpecChecker_);
  }

  public Object visitParent(Parent parent)
  {
    //first do the usual things that the Z typechecker does
    Object result = parent.accept(zSpecChecker_);

    String parentName = parent.getWord();
    TermA termA = null;
    try {
      termA = (TermA) sectInfo().get(new Key(parentName, ZSect.class));
    }
    catch (CommandException e) {
      assert false;
    }

    //if we find the sectino, get the class names annotation, and copy
    //the names over
    if (termA != null) {
      ClassNamesAnn ann = (ClassNamesAnn) termA.getAnn(ClassNamesAnn.class);
      if (ann != null) {
	List<DeclName> classNames = ann.getClassNames();
	for (DeclName className : classNames) {
	  classNames().add(className);
	}
      }
    }
    return result;
  }
}

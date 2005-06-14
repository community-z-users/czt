/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.oz.util;

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * Calculates the carrier set of Object-Z types.
 */
public class CarrierSet
  extends net.sourceforge.czt.typecheck.z.util.CarrierSet
  implements
    ClassRefTypeVisitor,
    ClassUnionTypeVisitor,
    ClassPolyTypeVisitor,
    ClassRefVisitor
    //VariableClassTypeVisitor
{
  protected OzFactory ozFactory_;

  public CarrierSet()
  {
    super();
    ozFactory_ = new net.sourceforge.czt.oz.impl.OzFactoryImpl();
  }

  public CarrierSet(boolean allowVariableTypes)
  {
    this();
    allowVariableTypes_ = allowVariableTypes;
  }

  public CarrierSet(ZFactory zFactory, OzFactory ozFactory)
  {
    super(zFactory);
    ozFactory_ = ozFactory;
  }

  public Object visitClassRefType(ClassRefType classRefType)
  {
    ClassRef classRef = classRefType.getThisClass();
    Expr result = (Expr) classRef.accept(this);
    return result;
  }

  public Object visitClassPolyType(ClassPolyType classPolyType)
  {
    ClassRef classRef = classPolyType.getRootClass();
    Expr expr = (Expr) classRef.accept(this);
    PolyExpr result = ozFactory_.createPolyExpr(expr);
    return result;
  }

  public Object visitClassUnionType(ClassUnionType classUnionType)
  {
    ClassSig classSig = classUnionType.getClassSig();
    List<ClassRef> classRefs = classSig.getClasses();

    assert classRefs.size() > 1;
    ClassUnionExpr result = null;
    for (ClassRef classRef : classRefs) {
      Expr expr = (Expr) classRef.accept(this);
      if (result == null) {
        result = ozFactory_.createClassUnionExpr();
        result.setLeftExpr(expr);
      }
      else if (result.getRightExpr() == null) {
	result.setRightExpr(expr);
      }
      else {
        ClassUnionExpr next = ozFactory_.createClassUnionExpr(result, expr);
	result = next;
      }
    }

    return result;
  }

  public Object visitClassRef(ClassRef classRef)
  {
    List<Expr> exprs = new java.util.ArrayList();
    List<Type2> types = classRef.getType2();
    for (Type2 type : types) {
      Expr expr = (Expr) type.accept(this);
      exprs.add(expr);
    }
    Expr result =
      zFactory_.createRefExpr(classRef.getRefName(), exprs, Boolean.FALSE);
    if (classRef.getNameNamePair().size() > 0) {
      result = zFactory_.createRenameExpr(result, classRef.getNameNamePair());
    }
    return result;
  }
}

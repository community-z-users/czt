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
package net.sourceforge.czt.typecheck.z;

import java.util.List;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A <code>CharTuple</code> instance visits a ZSchText instances in an
 * AST, and returns the type of the characteristic tuple in the
 * ZSchText.
 */
public class CharTupleChecker
  extends Checker<List<Type2>>
  implements 
    ZSchTextVisitor<List<Type2>>,
    VarDeclVisitor<List<Type2>>,
    ConstDeclVisitor<List<Type2>>,
    InclDeclVisitor<List<Type2>>,
    ZDeclListVisitor<List<Type2>>
{
  public CharTupleChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public List<Type2> visitZSchText(ZSchText zSchText)
  {
    DeclList declList = zSchText.getDeclList();
    List<Type2> result = declList.accept(charTupleChecker());

    return result;
  }

  public List<Type2> visitVarDecl(VarDecl varDecl)
  {
    //get the type of the name from the expression
    List<Type2> result = factory().list();
    ZNameList zNameList = varDecl.getName();
    for (Name name : zNameList) {
      Type2 type = getType2FromAnns(varDecl.getExpr());

      //if the type is a PowerType, take the inner type
      if (type instanceof PowerType) {
	PowerType powerType = (PowerType) type;
	result.add(powerType.getType());
      }
      //otherwise, the type must not be resolved yet,
      //so use a fresh unknown type
      else {
	result.add(factory().createUnknownType());
      }
    }
    return result;
  }

  public List<Type2> visitConstDecl(ConstDecl constDecl)
  {
    Type2 type = getType2FromAnns(constDecl.getExpr());
    List<Type2> result = factory().list(type);
    return result;
  }

  public List<Type2> visitInclDecl(InclDecl inclDecl)
  {
    List<Type2> result = factory().list();

    //get the type of the inner expression
    Type2 type = getType2FromAnns(inclDecl.getExpr());

    //if the type is a PowerType, take the inner type
    if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      result.add(powerType.getType());
    }
    //otherwise, the type must not be resolved yet,
    //so use a fresh unknown type
    else {
      result.add(factory().createUnknownType());
    }
    return result;
  }

  public List<Type2> visitZDeclList(ZDeclList zDeclList)
  {
    List<Type2> result = factory().list();

    //for each declaration in the list, get the types from that
    for (Decl decl : zDeclList.getDecl()) {
      List<Type2> nextTypes = decl.accept(charTupleChecker());
      result.addAll(nextTypes);
    }

    //if the size is 0, then the type is an empty schema type
    if (result.size() == 0) {
      Signature signature = factory().createSignature();
      SchemaType schemaType = factory().createSchemaType(signature);
      result.add(schemaType);
    }
    return result;
  }
}

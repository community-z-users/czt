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
package net.sourceforge.czt.typecheck.z.util;

import java.io.*;
import java.util.Stack;
import java.util.List;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A <code>TypeEnv</code> maintains a mapping from non-global
 * variables to their type/signature .
 */
public class TypeEnv
{
  /** A Factory. */
  protected Factory factory_;

  /** The names and their types. */
  protected Stack<List<NameTypePair>> typeInfo_;

  /**
   * The list of current generic parameters. Used for tracking the
   * order of generic parameters for type unification.
   */
  protected Stack<List<ZDeclName>> parameters_;

  public TypeEnv()
  {
    this(new ZFactoryImpl());
  }

  public TypeEnv(ZFactory zFactory)
  {
    factory_ = new Factory(zFactory);
    typeInfo_ = new Stack<List<NameTypePair>>();
    parameters_ = new Stack<List<ZDeclName>>();
  }

  public void enterScope()
  {
    List<NameTypePair> info = list();
    typeInfo_.push(info);
    List<ZDeclName> parameters = list();
    parameters_.push(parameters);
  }

  public void exitScope()
  {
    typeInfo_.pop();
    parameters_.pop();
  }

  public TypeEnvAnn getTypeEnvAnn()
  {
    List<NameTypePair> pairs = getNameTypePairs();
    return factory_.createTypeEnvAnn(pairs);
  }

  public void addParameters(List<DeclName> paramNames)
  {
    for (DeclName paramName : paramNames) {
      ZDeclName zParamName = assertZDeclName(paramName);
      parameters_.peek().add(zParamName);
    }
  }

  public List<ZDeclName> getParameters()
  {
    List<ZDeclName> result = list();
    result.addAll(parameters_.peek());
    return result;
  }

  public void add(ZDeclName zDeclName, Type type)
  {
    NameTypePair pair = factory_.createNameTypePair(zDeclName, type);
    add(pair);
  }


  /**
   * Add a name into the environment, overriding an existing name in
   * the inner-most variable scope.
   */
  public void override(ZDeclName zDeclName, Type type)
  {
    //override if this is in the top scope
    for (NameTypePair pair : typeInfo_.peek()) {
      if (namesEqual(zDeclName, pair.getZDeclName())) {
        pair.setType(type);
        return;
      }
    }

    //otherwise, add it to the environment
    add(zDeclName, type);
  }

  public void add(NameTypePair pair)
  {
    typeInfo_.peek().add(pair);
  }

  /**
   * Add a list of NameTypePair objects to this environment.
   */
  public void add(List<NameTypePair> pairs)
  {
    for (NameTypePair pair : pairs) {
      add(pair);
    }
  }

  public Type getType(ZRefName zRefName)
  {
    Type result = factory_.createUnknownType();

    //get the info for this name
    NameTypePair pair = getPair(zRefName);
    if (pair != null) {
      result = pair.getType();
      zRefName.setDecl(pair.getDeclName());
    }

    return result;
  }

  public List<NameTypePair> getNameTypePair()
  {
    return typeInfo_.peek();
  }

  public Type getTypeFromAnns(TermA termA)
  {
    Type result = factory_.createUnknownType();

    List anns = termA.getAnns();
    for (Object next : anns) {
      if (next instanceof TypeAnn) {
        result = ((TypeAnn) next).getType();
        break;
      }
    }

    return result;
  }

  protected List<NameTypePair> getNameTypePairs()
  {
    List<NameTypePair> result = list();
    for (List<NameTypePair> list : typeInfo_) {
      for (NameTypePair pair : list) {
        NameTypePair existing = findNameTypePair(pair.getZDeclName(), result);
        if (existing == null) {
          result.add(pair);
        }
      }
    }
    return result;
  }

  protected NameTypePair findNameTypePair(ZDeclName zDeclName,
                                          List<NameTypePair> pairs)
  {
    NameTypePair result = null;
    for (NameTypePair pair : pairs) {
      if (namesEqual(pair.getZDeclName(), zDeclName)) {
        result = pair;
        break;
      }
    }
    return result;
  }

  //gets the pair with the corresponding name
  protected NameTypePair getPair(ZRefName zRefName)
  {
    NameTypePair result = null;
    for (List<NameTypePair> list : typeInfo_) {
      for (NameTypePair pair : list) {
        if (namesEqual(pair.getZDeclName(), zRefName)) {
          result = pair;
        }
      }
    }
    return result;
  }
}

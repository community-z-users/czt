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
import java.util.Map;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;
import static net.sourceforge.czt.z.util.ZUtils.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A <code>TypeEnv</code> maintains a mapping from non-global
 * variables to their type/signature .
 */
public class TypeEnv
  extends AbstractTypeEnv
{
  /** A Factory. */
  protected Factory factory_;

  /** The names and their types. */
  protected Stack<Map<ZName, NameTypePair>> typeInfo_;

  /**
   * The list of current generic parameters. Used for tracking the
   * order of generic parameters for type unification.
   */
  protected Stack<List<ZName>> parameters_;

  public TypeEnv(Factory factory)
  {
    factory_ = factory;
    typeInfo_ = new Stack<Map<ZName, NameTypePair>>();
    parameters_ = new Stack<List<ZName>>();
  }
/*  
  protected TypeEnv(Factory factory, TypeEnv copyFrom)
  {
    this(factory);
    for(Map<ZName, NameTypePair> ti : copyFrom.typeInfo_)
    {
      
    }
    typeInfo_ = (Stack<Map<ZName, NameTypePair>>)copyFrom.typeInfo_.clone();
    parameters_ = (Stack<List<ZName>>)copyFrom.parameters_.clone();
  }
*/
  public Factory getFactory()
  {
    return factory_;
  }

  public void enterScope()
  {
    Map<ZName, NameTypePair> info = map();
    typeInfo_.push(info);
    List<ZName> parameters = getFactory().list();
    parameters_.push(parameters);
  }

  public void exitScope()
  {
    typeInfo_.pop();
    parameters_.pop();
  }

  public void addParameters(List<Name> paramNames)
  {
    for (Name paramName : paramNames) {
      ZName zParamName = assertZName(paramName);
      parameters_.peek().add(zParamName);
    }
  }

  public List<ZName> getParameters()
  {
    List<ZName> result = getFactory().list();
    result.addAll(parameters_.peek());
    return result;
  }

  public void add(ZName zName, Type type)
  {
    NameTypePair pair = getFactory().createNameTypePair(zName, type);
    add(pair);
  }


  /**
   * Add a name into the environment, overriding an existing name in
   * the inner-most variable scope.
   */
  public void override(ZName zName, Type type)
  {
    //override if this is in the top scope
    Map<ZName, NameTypePair> map = typeInfo_.peek();
    NameTypePair pair = getX(zName, map);
    if (pair != null) {
      pair.setType(type);
      return;
    }

    //otherwise, add it to the environment
    add(zName, type);
  }

  public void add(NameTypePair pair)
  {
    typeInfo_.peek().put(pair.getZName(), pair);
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

  public Type getType(ZName zName)
  {
    return getTypeFromStack(zName, typeInfo_);
  }

  //gets the pair with the corresponding name
  protected NameTypePair getPair(ZName zName)
  {    
    return getPairFromStack(zName, typeInfo_);
  }
  
  /**
   * General method that retrieves NameTypePair for the given name from the given type information stack
   * for Z typechecking that means
   */
  protected NameTypePair getPairFromStack(ZName zName, Stack<Map<ZName, NameTypePair>> ti)
  {
    NameTypePair result = null;
    for (Map<ZName, NameTypePair> map : ti) {
      NameTypePair pair = getX(zName, map);
      if (pair != null) {
        result = pair;
      }
    }
    return result;
  }
  
  public Type getTypeFromStack(ZName zName, Stack<Map<ZName, NameTypePair>> ti)
  {
    Type result = getFactory().createUnknownType();

    //get the info for this name
    NameTypePair pair = getPairFromStack(zName, ti);
    if (pair != null) {
      result = pair.getType();
      getFactory().merge(zName, pair.getZName());
    }

    //if the type is unknown, try looking up the Delta or Xi reference
    //of it
    if (pair == null) {
      result = getDeltaXiType(zName, result);
    }
    return result;
  }
}

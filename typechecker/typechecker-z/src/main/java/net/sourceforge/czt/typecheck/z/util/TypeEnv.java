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

import java.util.Stack;
import java.util.List;
import java.util.Map;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;
import static net.sourceforge.czt.z.util.ZUtils.*;

import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A <code>TypeEnv</code> maintains a mapping from non-global
 * variables to their type/signature .
 */
public class TypeEnv
  extends AbstractTypeEnv<NameTypePair>
{
  /** A Factory. */
  //protected Factory factory_; already defined in AbstractTypeEnv!

  /** The names and their types. */
  protected Stack<Map<ZName, NameTypePair>> typeInfo_;

  /**
   * The list of current generic parameters. Used for tracking the
   * order of generic parameters for type unification.
   */
  protected Stack<List<ZName>> parameters_;

  /**
   * Creates a type environment with the given factory. 
   * It is used within the environment (and its descendents)
   * to create terms, usually lists and Type terms.
   */
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

  /**
   * Enters a typing scope, which involves pushing a type information map
   * and a list of generic parameters in the corresponding environment stacks.
   */
  public void enterScope()
  {
    Map<ZName, NameTypePair> info = map();
    typeInfo_.push(info);
    List<ZName> parameters = getFactory().list();
    parameters_.push(parameters);
  }

  /**
   * Exits a typing scope by popping the environment stacks.
   */
  public void exitScope()
  {
    typeInfo_.pop();
    parameters_.pop();
  }

  /**
   * Add the list of the name to the top of the stack of generic parameters.
   */
  public void addParameters(List<Name> paramNames)
  {
    for (Name paramName : paramNames) {
      ZName zParamName = assertZName(paramName);
      parameters_.peek().add(zParamName);
    }
  }

  /**
   * Gets the list of names from the the top of the stack of generic parameters.
   * This creates a new list of names (i.e., changes to the result do not affect
   * the underlying stack).
   */
  public List<ZName> getParameters()
  {
    List<ZName> result = getFactory().list();
    result.addAll(parameters_.peek());
    return result;
  }

  /**
   * Adds a name and type pair to the type information map at the current scope.
   */
  public void add(ZName zName, Type type)
  {
    NameTypePair pair = getFactory().createNameTypePair(zName, type);
    add(pair);  
  }  
  
  /**
   * Adds a name and type pair to the type information map at the current scope.
   */
  public void add(NameTypePair pair)
  {    
    typeInfo_.peek().put(pair.getZName(), pair);
  }
  
  /**
   * Adds a list of name and type pairs to the type information map at the current scope.
   */
  public void add(List<NameTypePair> pairs)
  {
    for (NameTypePair pair : pairs) {
      add(pair);
    }
  }
  
  //private static int count = 1;  
  protected NameTypePair getX(ZName zName, Map<ZName, NameTypePair> map)
  {
    NameTypePair result = super.getX(zName, map);
    //System.out.println(count++); //36016, current test set
    assert (result == null || namesEqual(result.getZName(), zName)) :
      "getX invariant broken at TypeEnv: requested name " + zName + 
      " differs from name found (" + result.getZName() + ").";
    return result;
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
  
  /**
   * <p>
   * Returns the type of the given name in the type environment stack, or UnknownType
   * if it does not exist at any scope. Thus, the result is never null. 
   * See getTypeFromStack for details.
   * </p>
   *
   *@param name the name to lookup the type
   *@result the type for the given name or UnknownType 
   */
  public Type getType(ZName zName)
  {
    Type result = getTypeFromStack(zName, typeInfo_);
    assert result != null : "Invalid type for name " + zName;
    return result;
  }

  /**
   * Gets the pair for the corresponding name in the type environment, or null 
   * if none exists.
   */
  protected NameTypePair getPair(ZName zName)
  {    
    return getPairFromStack(zName, typeInfo_);
  }
  
  /**
   * <p>
   * General method that retrieves NameTypePair for the given name from the given type 
   * information stack. For Z typechecking, that means retrieving type information for
   * global scope. Other extensions may have different stacks to be looked at, depending
   * on the context where the information is needed. 
   * </p>
   * <p>
   * The method looksup from the bottom to the top of the stack (i.e., outermost to
   * innermost scopes) for the given name, which is looked up within the the map elements
   * of the stack. Thus, innermost pairs are always returned. 
   * </p>
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
  
   /**
   * <p>
   * Returns the type of the given name in the environment (stack) given, or UnknownType
   * if it does not exist at any scope. Thus, the result is never null.
   * </p>
   * <p>
   * That is, it performs a lookup over each map of the type environment stack, where
   * the innermost associated type is returned. Also, the IDs within the names
   * given are updated to make sure references are properly linked with their
   * declaring name. Finally, if no result has been found yet, it tries to see
   * if this is a Delta or Xi name where the base type exists, otherwise, UnknownType 
   * is returned.
   * </p>
   *
   *@param name the name to lookup the type
   *@param ti the type environment stack to search
   *@result the type for the given name or UnknownType 
   */
  protected Type getTypeFromStack(ZName zName, Stack<Map<ZName, NameTypePair>> ti)
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

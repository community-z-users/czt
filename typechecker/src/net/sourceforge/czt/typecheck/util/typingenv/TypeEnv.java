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
package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 * A <code>TypeEnv</code> maintains a mapping from non-global
 * variables to their type.
 */
public class TypeEnv
{
  /** A Factory. */
  protected Factory factory_ = null;

  /** The names and their types. */
  protected Stack typeInfo_ = null;

  /**
   * The list of current generic parameters. Used for tracking the
   * order of generic parameters for type unification.
   */
  protected List parameters_ = list();

  public TypeEnv()
  {
    this(new ZFactoryImpl());
  }

  public TypeEnv(ZFactory zFactory)
  {
    factory_ = new Factory(zFactory);
    typeInfo_ = new Stack();
  }

  public void enterScope()
  {
    List info = list();
    typeInfo_.push(info);
  }

  public void exitScope()
  {
    pop();
    if (typeInfo_.size() == 0) {
      parameters_ = list();
    }
  }

  public void setParameters(List parameters)
  {
    parameters_ = parameters;
  }

  public List getParameters()
  {
    return parameters_;
  }

  public void add(DeclName declName, Type2 type)
  {
    NameTypePair nameTypePair = factory_.createNameTypePair(declName, type);
    add(nameTypePair);
  }

  public void add(NameTypePair nameTypePair)
  {
    peek().add(nameTypePair);
  }

  /**
   * Add a list of NameTypePair objects to this environment.
   */
  public void add(List nameTypePairs)
  {
    for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();
      add(nameTypePair);
    }
  }

  public Type2 getType(RefName name)
  {
    DeclName unknownName = factory_.createDeclName(name);

    Type2 result = factory_.createUnknownType(unknownName);

    //get the info for this name
    NameTypePair pair = getPair(name);
    if (pair != null) {
      result = (Type2) pair.getType();
    }

    return result;
  }

  public List getNameTypePair()
  {
    return peek();
  }

  public Type getTypeFromAnns(TermA termA)
  {
    Type result = factory_.createUnknownType();

    List anns = termA.getAnns();
    for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next instanceof TypeAnn) {
        result = ((TypeAnn) next).getType();
        break;
      }
    }

    return result;
  }

  //peeks at the top of the stack
  private List peek()
  {
    List result = list();

    if (typeInfo_.size() != 0) {
      result = (List) typeInfo_.peek();
    }

    return result;
  }

  //pops the top of the stack
  private List pop()
  {
    List result = list();

    if (typeInfo_.size() != 0) {
      result = (List) typeInfo_.pop();
    }

    return result;
  }

  //gets the pair with the corresponding name
  private NameTypePair getPair(Name name)
  {
    NameTypePair result = null;

    for (Iterator stackIter = typeInfo_.iterator(); stackIter.hasNext(); ) {
      List list = (List) stackIter.next();
      for (Iterator iter = list.iterator(); iter.hasNext(); ) {
        NameTypePair pair = (NameTypePair) iter.next();
        if (pair.getName().getWord().equals(name.getWord()) &&
            pair.getName().getStroke().equals(name.getStroke())) {
          result = pair;
        }
      }
    }

    return result;
  }

  private DeclName getName(Name name)
  {
    DeclName result = null;

    for (Iterator stackIter = typeInfo_.iterator(); stackIter.hasNext(); ) {
      List list = (List) stackIter.next();

      for (Iterator iter = list.iterator(); iter.hasNext(); ) {
        DeclName declName = (DeclName) iter.next();

        if (declName.getWord().equals(name.getWord()) &&
            declName.getStroke().equals(name.getStroke())) {
          result = declName;
        }
      }
    }

    return result;
  }

  protected static List list()
  {
    return new ArrayList();
  }
}

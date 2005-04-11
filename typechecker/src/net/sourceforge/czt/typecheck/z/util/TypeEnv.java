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
import java.util.ArrayList;

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
  protected List<DeclName> parameters_;

  public TypeEnv()
  {
    this(new ZFactoryImpl());
  }

  public TypeEnv(ZFactory zFactory)
  {
    factory_ = new Factory(zFactory);
    typeInfo_ = new Stack<List<NameTypePair>>();
    parameters_ = new ArrayList<DeclName>();
  }

  public void enterScope()
  {
    List<NameTypePair> info = new ArrayList<NameTypePair>();
    typeInfo_.push(info);
  }

  public void exitScope()
  {
    pop();
    if (typeInfo_.size() == 0) {
      parameters_ = new ArrayList<DeclName>();
    }
  }

  public void setParameters(List<DeclName> parameters)
  {
    parameters_ = parameters;
  }

  public List<DeclName> getParameters()
  {
    return parameters_;
  }

  public void add(DeclName declName, Type type)
  {
    NameTypePair pair = factory_.createNameTypePair(declName, type);
    add(pair);
  }

  public void add(NameTypePair pair)
  {
    peek().add(pair);
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

  public Type getType(RefName name)
  {
    DeclName unknownName = factory_.createDeclName(name);

    Type result = factory_.createUnknownType(unknownName);

    //get the info for this name
    NameTypePair pair = getPair(name);
    if (pair != null) {
      result = pair.getType();
      name.setDecl(pair.getName());
    }

    return result;
  }

  public List<NameTypePair> getNameTypePair()
  {
    return peek();
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

  //peeks at the top of the stack
  private List<NameTypePair> peek()
  {
    List<NameTypePair> result = new ArrayList<NameTypePair>();
    if (typeInfo_.size() != 0) {
      result = typeInfo_.peek();
    }
    return result;
  }

  //pops the top of the stack
  private List<NameTypePair> pop()
  {
    List<NameTypePair> result = new ArrayList<NameTypePair>();
    if (typeInfo_.size() != 0) {
      result = typeInfo_.pop();
    }
    return result;
  }

  //gets the pair with the corresponding name
  private NameTypePair getPair(Name name)
  {
    NameTypePair result = null;

    for (List<NameTypePair> list : typeInfo_) {
      for (NameTypePair pair : list) {
        if (pair.getName().getWord().equals(name.getWord()) &&
            pair.getName().getStroke().equals(name.getStroke())) {
          result = pair;
        }
      }
    }

    return result;
  }
}

package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.z.*;

/**
 * A <code>TypeEnv</code> maintains a mapping from non-global
 * variables to their type.
 */
public class TypeEnv
{
  /** A ZFactory. */
  protected ZFactory factory_ = null;

  /** The names and their types. */
  protected Stack typeInfo_ = null;

  /**
   * The list of current generic parameters. Used for tracking the
   * order of generic parameters for type unification.
   */
  protected List parameters_ = new ArrayList();

  public TypeEnv ()
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    typeInfo_ = new Stack();
  }

  public void enterScope()
  {
    List info = new ArrayList();
    typeInfo_.push(info);
  }

  public void exitScope()
  {
    pop();
    if (typeInfo_.size() == 0) {
      parameters_ = new ArrayList();
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

  public void add(DeclName declName, Type type)
  {
    NameTypePair nameTypePair = factory_.createNameTypePair(declName, type);
    peek().add(nameTypePair);
  }

  /**
   * Add a list of NameTypePair objects to this environment.
   */
  public void add(List nameTypePairs)
  {
    for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();
      add(nameTypePair.getName(), nameTypePair.getType());
    }
  }

  public Type getType(Name name)
  {
    DeclName unknownName =
      factory_.createDeclName(name.getWord(), name.getStroke(), null);

    Type result = UnknownTypeImpl.create(unknownName, true);

    //get the info for this name
    NameTypePair pair = getPair(name);
    if (pair != null) {
      result = pair.getType();
    }

    return result;
  }

  public List getNameTypePair()
  {
    return peek();
  }

  public static Type getTypeFromAnns(TermA termA)
  {
    Type result = UnknownTypeImpl.create();

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
    List result = new ArrayList();

    if (typeInfo_.size() != 0) {
      result = (List) typeInfo_.peek();
    }

    return result;
  }

  //pops the top of the stack
  private List pop()
  {
    List result = new ArrayList();

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
}

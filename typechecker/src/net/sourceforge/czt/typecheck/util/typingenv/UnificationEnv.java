package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.*;

/**
 * Unifies a generic or variable type with an actual type.
 */
public class UnificationEnv
{
  /** A ZFactory. */
  protected ZFactory factory_ = null;

  /** The list of names and their unified types. */
  protected Stack unificationInfo_ = null;

  public UnificationEnv()
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    unificationInfo_ = new Stack();
  }

  public void enterScope()
  {
    List info = new ArrayList();
    unificationInfo_.push(info);
  }

  public void exitScope()
  {
    unificationInfo_.pop();
  }

  /**
   * Add the name and type this unificiation environment. Return true
   * iff this name is not in the environment, or its type unifies with
   * the existing type
   */
  public boolean add(DeclName name, Type type)
  {
    boolean result = false;

    if (unifies(name, type)) {
      NameTypePair nameTypePair =
        factory_.createNameTypePair(name, type);
      peek().add(nameTypePair);
      result = true;
    }

    return result;
  }

  public Type getType(Name name)
  {
    Type result = UnknownTypeImpl.create();

    for (Iterator iter = peek().iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();

      if (pair.getName().getWord().equals(name.getWord()) &&
          pair.getName().getStroke().equals(name.getStroke())) {
        result = pair.getType();
        break;
      }
    }

    return result;
  }

  /**
   * Returns true if and only if the name unifies with the existing
   * type in this environment (if one exists).
   */
  protected boolean unifies(Name name, Type type)
  {
    boolean result = true;
    Type storedType = getType(name);

    if (!(storedType instanceof UnknownType)) {
      if (storedType instanceof PowerType && type instanceof PowerType) {
        PowerType powerType1 = (PowerType) storedType;
        PowerType powerType2 = (PowerType) type;
        if (powerType1.getType() != null && powerType2.getType() != null) {
          result = storedType.equals(type);
        }
      }
      else if (!storedType.equals(type)) {
        result = false;
      }
    }

    return result;
  }

  private List peek()
  {
    List result = new ArrayList();
    if (unificationInfo_.size() > 0) {
      result = (List) unificationInfo_.peek();
    }
    return result;
  }
}

package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.*;

import net.sourceforge.czt.z.ast.*;

/**
 * Unifies a generic type with an actual type
 */
public class UnificationEnv
{
  /** a ZFactory */
  protected ZFactory factory_ = null;

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

  public Type getType(Name genName)
  {
    Type result = UnknownTypeImpl.create();

    for (Iterator iter = peek().iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();

      if (pair.getName().getWord().equals(genName.getWord()) &&
	  pair.getName().getStroke().equals(genName.getStroke())) {
	result = pair.getType();
	break;
      }
    }

    return result;
  }

  /**
   * Returns true if and only if the name unifies with the existing
   * type in this environment (if one exists)
   */
  public boolean unifies(Name name, Type type)
  {
    boolean result = true;
    Type storedType = getType(name);

    if (!(storedType instanceof UnknownType)) {
      if (storedType instanceof PowerType && type instanceof PowerType) {
	PowerType powerType1 = (PowerType) storedType;
	PowerType powerType2 = (PowerType) type;
	result = (powerType1.getType() == null || powerType2.getType() == null);
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

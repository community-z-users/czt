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

  public void add(DeclName name, Type type)
  {
    Type lookupType = getType(name);
    if ((!(lookupType instanceof UnknownType)) && !lookupType.equals(type)) {
      String message = "Attempt to instantiate generic type " + 
	name.getWord() + " more than once with different types";
      throw new TypeException(ErrorKind.UNIFICATION_FAILED, name, type, message);
    }
    else {
      NameTypePair nameTypePair =
	factory_.createNameTypePair(name, type);
      peek().add(nameTypePair);
    }
  }

  public Type getType(Name genName)
  {
    Type result = UnknownTypeImpl.create();

    for (Iterator iter = peek().iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();

      if (pair.getName().getWord().equals(genName.getWord())) {
	result = pair.getType();
	break;
      }
    }

    return result;
  }

  private List peek()
  {
    return (List) unificationInfo_.peek();
  }
}

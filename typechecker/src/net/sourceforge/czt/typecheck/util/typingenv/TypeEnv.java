package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.*;

import net.sourceforge.czt.z.ast.*;

public class TypeEnv
{
  /** a ZFactory */
  protected ZFactory factory_ = null;

  protected Stack typeInfo_ = null;

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

  public TypeEnvAnn exitScope()
  {
    return factory_.createTypeEnvAnn(pop());
  }

  public void add(DeclName declName, Type type)
    throws TypeException
  {
    NameTypePair pair = getPair(declName);
    if (pair != null) {
      String message = "Redeclared name: " + SectTypeEnv.toString(declName);
      throw new TypeException(ErrorKind.REDECLARATION, declName);
    }

    NameTypePair nameTypePair = factory_.createNameTypePair(declName, type);
    peek().add(nameTypePair);
  }

  /**
   * Add a NameTypePair to this environment
   */
  public void add(NameTypePair nameTypePair)
  {
    peek().add(nameTypePair);
  }

  /**
   * Add a list of NameTypePair objects to this environment
   */
  public void add(List nameTypePairs)
  {
    for (Iterator iter = nameTypePairs.iterator(); iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();
      peek().add(nameTypePair);
    }
  }

  public Type getType(Name name)
  {
    Type result = UnknownTypeImpl.create();

    //get the info for this name
    NameTypePair pair = getPair(name);
    if (pair != null) {
      result = pair.getType();
    }

    return result;
  }

  //peeks at the top of the stack
  private List peek()
  {
    return (List) typeInfo_.peek();
  }

  //pops the top of the stack
  private List pop()
  {
    return (List) typeInfo_.pop();
  }

  //gets the pair with the corresponding name. At the moment, I have
  //assumed that a duplicate name in a nested expression is prohibited,
  //but I think the standard allows it
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
}

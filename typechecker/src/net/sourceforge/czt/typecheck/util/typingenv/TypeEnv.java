package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
//import java.util.Stack;
import java.util.Vector;
import java.util.List;

import net.sourceforge.czt.typecheck.util.typeerror.*;
//import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.z.*;

import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.TypeEnvAnn;
import net.sourceforge.czt.z.ast.ZFactory;

public class TypeEnv implements TypeEnvInt
{
  private ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  private Vector typeEnvAnns_;
  private int curDepth_;

  public TypeEnv ()
  {
    curDepth_ = 2;
    typeEnvAnns_ = new Vector(curDepth_);
    for (int i = 0; i < curDepth_; i++) {
      typeEnvAnns_.add(i, factory_.createTypeEnvAnn());
    }
  }

  public void enterScope()
  {
    typeEnvAnns_.add(curDepth_++, factory_.createTypeEnvAnn());
  }

  public TypeEnvAnn  exitScope()
  {
    return (TypeEnvAnn) typeEnvAnns_.remove(--curDepth_);
  }

  public NameTypePair addNameTypePair(NameTypePair ntPair)
    throws TypeException
  {
    NameTypePair result = null;
    DeclName dn = ntPair.getName();
    String name = dn.getWord();
    NameTypePair pair1 = search(dn);
    if (pair1 == null) {
      add(ntPair);
      result = ntPair;
    }
    else {
      Type ntType = ntPair.getType();
      Type type1 = pair1.getType();
      if (! TypeChecker.unify(ntType, type1)) {
        result = pair1;
        throw new TypeException(ErrorKind.REDECLARATION, ntPair);
      }
      else {
        result = ntPair;
      }
    }
    return result;
  }

  private void add(NameTypePair ntPair)
  {
    TypeEnvAnn env = top();
    List nameTypePairs = env.getNameTypePair();
    nameTypePairs.add(ntPair);
  }

  public NameTypePair search(DeclName dn)
  {
    NameTypePair result = null;
    for (int i = curDepth_ - 1; i >= 0; i--) {
      TypeEnvAnn env = (TypeEnvAnn) typeEnvAnns_.get(i);
      NameTypePair temp = searchLocal(env, dn);
      if (temp != null) {
        result = temp;
        break;
      }
    }
    return result;
  }

  // changed this method and now it search for NameTypePair
  // not only by the name string,
  // but also by the strokes & Ids
  private NameTypePair searchLocal(TypeEnvAnn env, DeclName dn)
  {
    NameTypePair result = null;
    NameTypePair temp = null;
    List list = env.getNameTypePair();
    String name = dn.getWord();
    DeclName dn1 = null;
    for (int i = 0; i < list.size(); i++) {
      temp = (NameTypePair) list.get(i);
      dn1 = temp.getName();
      String name1 = dn1.getWord();
      if (name.equals(name1)) {
        boolean strokesAgree =
          TypeChecker.strokesAgree(dn.getStroke(), dn1.getStroke());
        boolean idsAgree = TypeChecker.IdsAgree(dn, dn1);
        if (strokesAgree && idsAgree) {
          result = temp;
          break;
        }
      }
    }
    return result;
  }

  private TypeEnvAnn top()
  {
    TypeEnvAnn env = (TypeEnvAnn) typeEnvAnns_.get(curDepth_ - 1);
    return env;
  }

  public int getCount()
  {
    int result = 0;
    for (int i = 0; i < curDepth_; i++) {
      TypeEnvAnn env = (TypeEnvAnn) typeEnvAnns_.get(i);
      result += env.getNameTypePair().size();
    }
    return result;
  }
}

package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.Vector;
import java.util.List;

import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.*;

import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.ZFactory;

public class SectTypeEnv
{
  ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  Vector typeEnv_;

  public SectTypeEnv ()
  {
    typeEnv_ = new Vector(10, 5);
  }

  public NameSectTypeTriple addNameSectTypePair(NameSectTypeTriple ntPair)
    throws TypeException
  {
    NameSectTypeTriple result = null;
    DeclName dn = ntPair.getName();
    String name = dn.getWord();
    System.out.println("sect = " + ntPair.getSect());
    System.out.println("name = " + name);
    NameSectTypeTriple pair1 = search(name);
    //System.out.println("pair1 = " + pair1 + " " + (pair1 != null));
    if (pair1 == null) {
      add(ntPair);
      result = ntPair;
    }
    else {
      String sn = ntPair.getSect();
      String sect1 = pair1.getSect();
      if (! sn.equals(sect1)) {
        result = pair1;
        throw new TypeException(ErrorKind.SECT_REDECLARATION, pair1);
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
    }
    return result;
  }

  private void add(NameSectTypeTriple ntPair)
  {
    typeEnv_.add(ntPair);
  }

  public NameSectTypeTriple search(String name)
  {
    NameSectTypeTriple result = null;
    NameSectTypeTriple temp = null;
    for (int i = typeEnv_.size() - 1; i >= 0; i--) {
      temp = (NameSectTypeTriple) typeEnv_.get(i);
      String name1 = temp.getName().getWord();
      if (name.equals(name1)) {
        result = temp;
        break;
      }
    }
    return result;
  }

  public void checkAndAdd(SectTypeEnvAnn ann)
  {
    List list = ann.getNameSectTypeTriple();
    NameSectTypeTriple cur = null;
    //System.out.println("list size = " + list.size());
    for (int i = 0; i < list.size(); i++) {
      cur = (NameSectTypeTriple) list.get(i);
      try {
        addNameSectTypePair(cur);
      }
      catch (TypeException e) {
        System.out.println(e.toString() + "\n" + "Source: "
                           + cur.getName().getWord());
      }
    }
  }
}

package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.z.ast.*;

/**
 * An implementation for NameSectTypeTriple that hides VariableType instances
 * if they have a value.
 */
public class NameSectTypeTripleImpl
  extends TermImpl
  implements NameSectTypeTriple
{
  protected NameSectTypeTripleImpl(NameSectTypeTriple triple)
  {
    super(triple);
  }

  public void setSect(String section)
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    triple.setSect(section);
  }

  public void setName(DeclName declName)
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    triple.setName(declName);
  }

  public void setType(Type type)
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    triple.setType(type);
  }

  public String getSect()
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    return triple.getSect();
  }

  public DeclName getName()
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    return triple.getName();
  }

  public Type getType()
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    Type result = triple.getType();
    if (result instanceof VariableType) {
      VariableType vType = (VariableType) result;
      if (vType.getValue() != null) {
        result = vType.getValue();
      }
    }
    return result;
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof NameSectTypeTriple) {
      NameSectTypeTriple triple = (NameSectTypeTriple) obj;
      if (!getSect().equals(triple.getSect()) ||
          !getName().equals(triple.getName()) ||
          !getType().equals(triple.getType())) {
        return false;
      }
      return true;
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "NameSectTypeTripleImpl".hashCode();
    if (getName() != null) {
      hashCode += constant * getName().hashCode();
    }
    if (getSect() != null) {
      hashCode += constant * getSect().hashCode();
    }
    if (getType() != null) {
      hashCode += constant * getType().hashCode();
    }
    return hashCode;
  }
}

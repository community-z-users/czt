
/*
THIS FILE WAS GENERATED BY GNAST.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

************************************************************

Copyright 2003 Mark Utting
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

package net.sourceforge.czt.core.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.core.ast.*;
import net.sourceforge.czt.core.util.*;

/**
 * An implementation of the interface
 * {@link NameSectTypeTriple}.
 *
 * @author Gnast version 0.1
 */
public class NameSectTypeTripleImpl
extends TermImpl implements NameSectTypeTriple
{
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.core.impl.NameSectTypeTripleImpl");

  /**
   * The constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link CoreFactory object factory}.
   */
  protected NameSectTypeTripleImpl(DeclName name)
  {
    super();
    mName = name;
  }
 
  /**
   * Compares the specified object with this NameSectTypeTripleImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) NameSectTypeTripleImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      NameSectTypeTripleImpl object = (NameSectTypeTripleImpl) obj;
      if(mName !=null &&
         ! mName.equals(object.mName)) return false;
      if(mName == null && object.mName != null)
        return false;
      if(mSect !=null &&
         ! mSect.equals(object.mSect)) return false;
      if(mSect == null && object.mSect != null)
        return false;
      if(mType !=null &&
         ! mType.equals(object.mType)) return false;
      if(mType == null && object.mType != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this NameSectTypeTripleImpl.
   * The hash code of a NameSectTypeTripleImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "NameSectTypeTripleImpl".hashCode();
    if(mName != null) {
      hashCode += 31*mName.hashCode();
    }
    if(mSect != null) {
      hashCode += 31*mSect.hashCode();
    }
    if(mType != null) {
      hashCode += 31*mType.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(AstVisitor v) {
    return v.visitNameSectTypeTriple(this);
  }

  /**
   * Returns a new object of this class.
   */
  public Term create(Object[] args) {
    sLogger.entering("NameSectTypeTripleImpl", "create", args);
    NameSectTypeTriple zedObject = null;
    try {
      DeclName name = (DeclName) args[0];
      String sect = (String) args[1];
      Type type = (Type) args[2];
      zedObject = new NameSectTypeTripleImpl(name);
      zedObject.setSect(sect);
      zedObject.setType(type);
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    sLogger.entering("NameSectTypeTripleImpl", "create", zedObject);
    return zedObject;
  }

  public Object[] getChildren()
  {
    sLogger.entering("NameSectTypeTripleImpl", "getChildren");
    Object[] erg = { getName(), getSect(), getType() };
    sLogger.exiting("NameSectTypeTripleImpl", "getChildren", erg);
    return erg;
  }

  private DeclName mName;

  public DeclName getName()
  {
    return mName;
  }

  private String mSect;

  public String getSect()
  {
    return mSect;
  }

  public void setSect(String sect)
  {
    mSect = sect;
  }

  private Type mType;

  public Type getType()
  {
    return mType;
  }

  public void setType(Type type)
  {
    mType = type;
  }
}

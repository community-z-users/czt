
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
 * {@link ZSect}.
 *
 * @author Gnast version 0.1
 */
public class ZSectImpl
extends SectImpl implements ZSect
{
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.core.impl.ZSectImpl");

  /**
   * The constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link CoreFactory object factory}.
   */
  protected ZSectImpl(String name)
  {
    super();
    mName = name;
  }
 
  /**
   * Compares the specified object with this ZSectImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ZSectImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      ZSectImpl object = (ZSectImpl) obj;
      if(mName !=null &&
         ! mName.equals(object.mName)) return false;
      if(mName == null && object.mName != null)
        return false;
      if(mParent !=null &&
         ! mParent.equals(object.mParent)) return false;
      if(mParent == null && object.mParent != null)
        return false;
      if(mPara !=null &&
         ! mPara.equals(object.mPara)) return false;
      if(mPara == null && object.mPara != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this ZSectImpl.
   * The hash code of a ZSectImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "ZSectImpl".hashCode();
    if(mName != null) {
      hashCode += 31*mName.hashCode();
    }
    if(mParent != null) {
      hashCode += 31*mParent.hashCode();
    }
    if(mPara != null) {
      hashCode += 31*mPara.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(AstVisitor v) {
    return v.visitZSect(this);
  }

  /**
   * Returns a new object of this class.
   */
  public Term create(Object[] args) {
    sLogger.entering("ZSectImpl", "create", args);
    ZSect zedObject = null;
    try {
      String name = (String) args[0];
      java.util.List parent = (java.util.List) args[1];
      java.util.List para = (java.util.List) args[2];
      zedObject = new ZSectImpl(name);
      if(parent != null) {
        zedObject.getParent().addAll(parent);
      }
      if(para != null) {
        zedObject.getPara().addAll(para);
      }
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    sLogger.entering("ZSectImpl", "create", zedObject);
    return zedObject;
  }

  public Object[] getChildren()
  {
    sLogger.entering("ZSectImpl", "getChildren");
    Object[] erg = { getName(), getParent(), getPara() };
    sLogger.exiting("ZSectImpl", "getChildren", erg);
    return erg;
  }

  private String mName;

  public String getName()
  {
    return mName;
  }

  private java.util.List mParent = new java.util.Vector();

  public java.util.List getParent()
  {
    return mParent;
  }

  private java.util.List mPara = new java.util.Vector();

  public java.util.List getPara()
  {
    return mPara;
  }
}

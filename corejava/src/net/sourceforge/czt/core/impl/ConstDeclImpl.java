
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
 * {@link ConstDecl}.
 *
 * @author Gnast version 0.1
 */
public class ConstDeclImpl
extends DeclImpl implements ConstDecl
{
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.core.impl.ConstDeclImpl");

  /**
   * The constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link CoreFactory object factory}.
   */
  protected ConstDeclImpl(DeclName declName)
  {
    super();
    mDeclName = declName;
  }
 
  /**
   * Compares the specified object with this ConstDeclImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ConstDeclImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      ConstDeclImpl object = (ConstDeclImpl) obj;
      if(mDeclName !=null &&
         ! mDeclName.equals(object.mDeclName)) return false;
      if(mDeclName == null && object.mDeclName != null)
        return false;
      if(mExpr !=null &&
         ! mExpr.equals(object.mExpr)) return false;
      if(mExpr == null && object.mExpr != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this ConstDeclImpl.
   * The hash code of a ConstDeclImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "ConstDeclImpl".hashCode();
    if(mDeclName != null) {
      hashCode += 31*mDeclName.hashCode();
    }
    if(mExpr != null) {
      hashCode += 31*mExpr.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(AstVisitor v) {
    return v.visitConstDecl(this);
  }

  /**
   * Returns a new object of this class.
   */
  public Term create(Object[] args) {
    sLogger.entering("ConstDeclImpl", "create", args);
    ConstDecl zedObject = null;
    try {
      DeclName declName = (DeclName) args[0];
      Expr expr = (Expr) args[1];
      zedObject = new ConstDeclImpl(declName);
      zedObject.setExpr(expr);
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    sLogger.entering("ConstDeclImpl", "create", zedObject);
    return zedObject;
  }

  public Object[] getChildren()
  {
    sLogger.entering("ConstDeclImpl", "getChildren");
    Object[] erg = { getDeclName(), getExpr() };
    sLogger.exiting("ConstDeclImpl", "getChildren", erg);
    return erg;
  }

  private DeclName mDeclName;

  public DeclName getDeclName()
  {
    return mDeclName;
  }

  private Expr mExpr;

  public Expr getExpr()
  {
    return mExpr;
  }

  public void setExpr(Expr expr)
  {
    mExpr = expr;
  }
}

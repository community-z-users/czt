
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
 * {@link Spec}.
 *
 * @author Gnast version 0.1
 */
public class SpecImpl
extends TermAImpl implements Spec
{
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.core.impl.SpecImpl");

  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link CoreFactory object factory}.
   */
  protected SpecImpl() { }
 
  /**
   * Compares the specified object with this SpecImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) SpecImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      SpecImpl object = (SpecImpl) obj;
      if((mSect == null && object.mSect != null) ||
         (mSect != null &&
         ! mSect.equals(object.mSect))) return false;
      if(mSect == null && object.mSect != null)
        return false;
      if((mVersion == null && object.mVersion != null) ||
         (mVersion != null &&
         ! mVersion.equals(object.mVersion))) return false;
      if(mVersion == null && object.mVersion != null)
        return false;
      if((mAuthor == null && object.mAuthor != null) ||
         (mAuthor != null &&
         ! mAuthor.equals(object.mAuthor))) return false;
      if(mAuthor == null && object.mAuthor != null)
        return false;
      if((mModified == null && object.mModified != null) ||
         (mModified != null &&
         ! mModified.equals(object.mModified))) return false;
      if(mModified == null && object.mModified != null)
        return false;
      if((mSource == null && object.mSource != null) ||
         (mSource != null &&
         ! mSource.equals(object.mSource))) return false;
      if(mSource == null && object.mSource != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this SpecImpl.
   * The hash code of a SpecImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "SpecImpl".hashCode();
    if(mSect != null) {
      hashCode += 31*mSect.hashCode();
    }
    if(mVersion != null) {
      hashCode += 31*mVersion.hashCode();
    }
    if(mAuthor != null) {
      hashCode += 31*mAuthor.hashCode();
    }
    if(mModified != null) {
      hashCode += 31*mModified.hashCode();
    }
    if(mSource != null) {
      hashCode += 31*mSource.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(AstVisitor v) {
    return v.visitSpec(this);
  }

  /**
   * Returns a new object of this class.
   */
  public Term create(Object[] args) {
    sLogger.entering("SpecImpl", "create", args);
    Spec zedObject = null;
    try {
      java.util.List sect = (java.util.List) args[0];
      String version = (String) args[1];
      String author = (String) args[2];
      java.util.Calendar modified = (java.util.Calendar) args[3];
      String source = (String) args[4];
      zedObject = new SpecImpl();
      if(sect != null) {
        zedObject.getSect().addAll(sect);
      }
      zedObject.setVersion(version);
      zedObject.setAuthor(author);
      zedObject.setModified(modified);
      zedObject.setSource(source);
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    sLogger.exiting("SpecImpl", "create", zedObject);
    return zedObject;
  }

  public Object[] getChildren()
  {
    sLogger.entering("SpecImpl", "getChildren");
    Object[] erg = { getSect(), getVersion(), getAuthor(), getModified(), getSource() };
    sLogger.exiting("SpecImpl", "getChildren", erg);
    return erg;
  }

  private java.util.List mSect = new java.util.Vector();

  public java.util.List getSect()
  {
    return mSect;
  }

  private String mVersion;

  public String getVersion()
  {
    return mVersion;
  }

  public void setVersion(String version)
  {
    mVersion = version;
  }

  private String mAuthor;

  public String getAuthor()
  {
    return mAuthor;
  }

  public void setAuthor(String author)
  {
    mAuthor = author;
  }

  private java.util.Calendar mModified;

  public java.util.Calendar getModified()
  {
    return mModified;
  }

  public void setModified(java.util.Calendar modified)
  {
    mModified = modified;
  }

  private String mSource;

  public String getSource()
  {
    return mSource;
  }

  public void setSource(String source)
  {
    mSource = source;
  }
}

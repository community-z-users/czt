
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstClass.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004 Mark Utting
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
******************************************************************************/

package net.sourceforge.czt.z.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.z.visitor.SpecVisitor;

/**
 * An implementation of the interface
 * {@link Spec}.
 *
 * @author Gnast version 0.1
 */
public class SpecImpl
  extends TermAImpl   implements Spec
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.z.ast.ZFactory object factory}.
   */
  protected SpecImpl()
  {
  }

  /**
   * Compares the specified object with this SpecImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) SpecImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        SpecImpl object = (SpecImpl) obj;
        if (sect_ != null) {
          if (!sect_.equals(object.sect_)) {
            return false;
          }
        }
        else {
          if (object.sect_ != null) {
            return false;
          }
        }
        if (version_ != null) {
          if (!version_.equals(object.version_)) {
            return false;
          }
        }
        else {
          if (object.version_ != null) {
            return false;
          }
        }
        if (author_ != null) {
          if (!author_.equals(object.author_)) {
            return false;
          }
        }
        else {
          if (object.author_ != null) {
            return false;
          }
        }
        if (modified_ != null) {
          if (!modified_.equals(object.modified_)) {
            return false;
          }
        }
        else {
          if (object.modified_ != null) {
            return false;
          }
        }
        if (source_ != null) {
          if (!source_.equals(object.source_)) {
            return false;
          }
        }
        else {
          if (object.source_ != null) {
            return false;
          }
        }
        return true;
      }
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
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "SpecImpl".hashCode();
    if (sect_ != null) {
      hashCode += constant * sect_.hashCode();
    }
    if (version_ != null) {
      hashCode += constant * version_.hashCode();
    }
    if (author_ != null) {
      hashCode += constant * author_.hashCode();
    }
    if (modified_ != null) {
      hashCode += constant * modified_.hashCode();
    }
    if (source_ != null) {
      hashCode += constant * source_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof SpecVisitor) {
      SpecVisitor visitor = (SpecVisitor) v;
      return visitor.visitSpec(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    Spec zedObject = null;
    try {
      java.util.List sect = (java.util.List) args[0];
      String version = (String) args[1];
      String author = (String) args[2];
      java.util.Calendar modified = (java.util.Calendar) args[3];
      String source = (String) args[4];
      zedObject = new SpecImpl();
      if (sect != null) {
        zedObject.getSect().addAll(sect);
      }
      zedObject.setVersion(version);
      zedObject.setAuthor(author);
      zedObject.setModified(modified);
      zedObject.setSource(source);
    }
    catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    }
    catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getSect(), getVersion(), getAuthor(), getModified(), getSource() };
    return erg;
  }


  private java.util.List sect_ =
    new TypesafeList(Sect.class);

  public java.util.List getSect()
  {
    return sect_;
  }

  private String version_;

  public String getVersion()
  {
    return version_;
  }

  public void setVersion(String version)
  {
    version_ = version;
  }

  private String author_;

  public String getAuthor()
  {
    return author_;
  }

  public void setAuthor(String author)
  {
    author_ = author;
  }

  private java.util.Calendar modified_;

  public java.util.Calendar getModified()
  {
    return modified_;
  }

  public void setModified(java.util.Calendar modified)
  {
    modified_ = modified;
  }

  private String source_;

  public String getSource()
  {
    return source_;
  }

  public void setSource(String source)
  {
    source_ = source;
  }
}

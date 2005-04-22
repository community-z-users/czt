
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstClass.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004, 2005 Mark Utting
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

package net.sourceforge.czt.circus.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.*;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.visitor.*;

import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;

/**
 * An implementation of the interface
 * {@link ProcessPara}.
 *
 * @author Gnast version 0.1
 */
public class ProcessParaImpl
  extends ParaImpl   implements ProcessPara
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.circus.ast.CircusFactory object factory}.
   */
  protected ProcessParaImpl()
  {
  }

  /**
   * Compares the specified object with this ProcessParaImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ProcessParaImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        ProcessParaImpl object = (ProcessParaImpl) obj;
        if (declName_ != null) {
          if (!declName_.equals(object.declName_)) {
            return false;
          }
        }
        else {
          if (object.declName_ != null) {
            return false;
          }
        }
        if (genericTypes_ != null) {
          if (!genericTypes_.equals(object.genericTypes_)) {
            return false;
          }
        }
        else {
          if (object.genericTypes_ != null) {
            return false;
          }
        }
        if (processDesc_ != null) {
          if (!processDesc_.equals(object.processDesc_)) {
            return false;
          }
        }
        else {
          if (object.processDesc_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this ProcessParaImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ProcessParaImpl".hashCode();
    if (declName_ != null) {
      hashCode += constant * declName_.hashCode();
    }
    if (genericTypes_ != null) {
      hashCode += constant * genericTypes_.hashCode();
    }
    if (processDesc_ != null) {
      hashCode += constant * processDesc_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof ProcessParaVisitor) {
      ProcessParaVisitor visitor = (ProcessParaVisitor) v;
      return visitor.visitProcessPara(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    ProcessPara zedObject = null;
    try {
      net.sourceforge.czt.z.ast.DeclName declName = (net.sourceforge.czt.z.ast.DeclName) args[0];
      java.util.List genericTypes = (java.util.List) args[1];
      ProcessDesc processDesc = (ProcessDesc) args[2];
      zedObject = new ProcessParaImpl();
      zedObject.setDeclName(declName);
      if (genericTypes != null) {
        zedObject.getGenericTypes().addAll(genericTypes);
      }
      zedObject.setProcessDesc(processDesc);
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
    Object[] erg = { getDeclName(), getGenericTypes(), getProcessDesc() };
    return erg;
  }

  private net.sourceforge.czt.z.ast.DeclName declName_;

  public net.sourceforge.czt.z.ast.DeclName getDeclName()
  {
    return declName_;
  }

  public void setDeclName(net.sourceforge.czt.z.ast.DeclName declName)
  {
    declName_ = declName;
  }


  private net.sourceforge.czt.base.ast.ListTerm genericTypes_ =
    new net.sourceforge.czt.base.impl.ListTermImpl(net.sourceforge.czt.z.ast.DeclName.class);

  public net.sourceforge.czt.base.ast.ListTerm getGenericTypes()
  {
    return genericTypes_;
  }

  private ProcessDesc processDesc_;

  public ProcessDesc getProcessDesc()
  {
    return processDesc_;
  }

  public void setProcessDesc(ProcessDesc processDesc)
  {
    processDesc_ = processDesc;
  }
}

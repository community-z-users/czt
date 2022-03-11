/*
  Copyright (C) 2008 Leo freitas
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
package net.sourceforge.czt.typecheck.circus.impl;

import java.util.List;
import net.sourceforge.czt.circus.ast.CommunicationType;
import net.sourceforge.czt.circus.visitor.CommunicationTypeVisitor;
import net.sourceforge.czt.typecheck.z.impl.Type2Impl;
import net.sourceforge.czt.typecheck.z.impl.VariableSignature;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.ZName;

/**
 * An implementation for ChannelType that hides VariableType instances
 * if they have a value.
 *
 *@author Leo
 */
public class CommunicationTypeImpl extends Type2Impl implements CommunicationType
{
  
  /** Creates a new instance of CommunicationTypeImpl */
  public CommunicationTypeImpl(CommunicationType commType)
  {
    super(commType);     
  }  
  
  public void setSignature(Signature signature)
  {
    CommunicationType commType = (CommunicationType) term_;
    commType.setSignature(signature);
  }
 
  public Signature getSignature()
  {
    CommunicationType schemaType = (CommunicationType) term_;
    Signature result = schemaType.getSignature();
    if (result instanceof VariableSignature) {
      VariableSignature vSig = (VariableSignature) result;
      if (vSig.getValue() != vSig) {
        result = vSig.getValue();
      }
    }
    return result;
  }

  public CommunicationTypeImpl create(Object [] args)
  {
    CommunicationType commType = (CommunicationType) term_.create(args);
    CommunicationTypeImpl result = new CommunicationTypeImpl(commType);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof CommunicationTypeVisitor) {
      CommunicationTypeVisitor<R> visitor = (CommunicationTypeVisitor<R>) v;
      return visitor.visitCommunicationType(this);
    }
    return super.accept(v);
  }

  public String toString()
  {
    CommunicationType commType = (CommunicationType) term_;
    return "comm " + commType.toString();
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof CommunicationType) {
      CommunicationType commType = (CommunicationType) obj;
      return getSignature().equals(commType.getSignature());
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "CommunicationTypeImpl".hashCode();
    if (getSignature() != null) {
      hashCode += constant * getSignature().hashCode();
    }
    return hashCode;
  }

  @Override
  public Name getChannelName()
  {
    CommunicationType commType = (CommunicationType) term_;
    return commType.getChannelName();
  }

  @Override
  public ZName getChannelZName()
  {
    CommunicationType commType = (CommunicationType) term_;
    return commType.getChannelZName();
  }

  @Override
  public Type getChannelType()
  {
    CommunicationType commType = (CommunicationType) term_;
    return commType.getChannelType();
  }

  @Override
  public List<NameTypePair> getCommunicationPattern()
  {
    CommunicationType commType = (CommunicationType) term_;
    return commType.getCommunicationPattern();
  }

  @Override
  public boolean isSynchronisation()
  {
    CommunicationType commType = (CommunicationType) term_;
    return commType.isSynchronisation();
  }
} 
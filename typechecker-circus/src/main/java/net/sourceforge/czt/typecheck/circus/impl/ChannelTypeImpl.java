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

import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.visitor.ChannelTypeVisitor;
import net.sourceforge.czt.typecheck.z.impl.Type2Impl;
import net.sourceforge.czt.typecheck.z.impl.VariableType;
import net.sourceforge.czt.z.ast.Type2;

/**
 * An implementation for ChannelType that hides VariableType instances
 * if they have a value.
 *
 *@author Leo
 */
public class ChannelTypeImpl extends Type2Impl implements ChannelType
{
  
  /** Creates a new instance of ChannelTypeImpl */
  public ChannelTypeImpl(ChannelType channelType)
  {
    super(channelType);
  }  
  
  public void setType(Type2 type)
  {
    ChannelType channelType = (ChannelType) term_;
    channelType.setType(type);
  }

  public Type2 getType()
  {
    //assert false : "TODO: do I need VariableChannelType ? maybe not";
    ChannelType channelType = (ChannelType) term_;
    Type2 result = channelType.getType();
    if (result instanceof VariableType) {
      VariableType vType = (VariableType) result;
      if (vType.getValue() != null) {
        result = vType.getValue();
      }
    }
    return result;
  }

  public ChannelTypeImpl create(Object [] args)
  {
    ChannelType channelType = (ChannelType) term_.create(args);
    ChannelTypeImpl result = new ChannelTypeImpl(channelType);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof ChannelTypeVisitor) {
      ChannelTypeVisitor<R> visitor = (ChannelTypeVisitor<R>) v;
      return visitor.visitChannelType(this);
    }
    return super.accept(v);
  }

  public String toString()
  {
    ChannelType channelType = (ChannelType) term_;
    return "channel " + channelType.toString();
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof ChannelType) {
      ChannelType channelType = (ChannelType) obj;
      return getType().equals(channelType.getType());
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ChannelTypeImpl".hashCode();
    if (getType() != null) {
      hashCode += constant * getType().hashCode();
    }
    return hashCode;
  }
} 
/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.tcoz.impl;

import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.oz.ast.OzFactory;
import net.sourceforge.czt.tcoz.ast.*;

/**
 * A factory for creating types that hide VariableTypes.
 */
public class Factory
  extends net.sourceforge.czt.typecheck.oz.impl.Factory
{
  /** The TcozFactory that is used to create wrapped types. */
  protected TcozFactory tcozFactory_;

  public Factory()
  {
    zFactory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    ozFactory_ = new net.sourceforge.czt.oz.impl.OzFactoryImpl();
    tcozFactory_ = new net.sourceforge.czt.tcoz.impl.TcozFactoryImpl();
  }

  public Factory(ZFactory zFactory, OzFactory ozFactory, TcozFactory tcozFactory)
  {
    zFactory_ = zFactory;
    ozFactory_ = ozFactory;
    tcozFactory_ = tcozFactory;
  }

  public OzFactory getOzFactory()
  {
    return ozFactory_;
  }

  public TcozFactory getTcozFactory()
  {
    return tcozFactory_;
  }

  public ChannelType createChannelType()
  {
    ChannelType result = tcozFactory_.createChannelType();
    return result;
  }
}

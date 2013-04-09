/*
Copyright (C) 2007 Leo Freitas
This file is part of the CZT project.
The CZT project contains free software;
you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.
The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.typecheck.circustime.impl;

import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circustime.ast.CircusTimeFactory;
import net.sourceforge.czt.z.ast.ZFactory;

public class Factory 
  extends net.sourceforge.czt.typecheck.circus.impl.Factory
{
  /** The CircusToolsFactory that is used to create wrapped types. */
  protected CircusTimeFactory circustimeFactory_;
  
  public Factory()
  {
    zFactory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    circusFactory_ = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();
    circustimeFactory_ = new net.sourceforge.czt.circustime.impl.CircusTimeFactoryImpl();
  }
  
  public Factory(ZFactory zFactory, CircusFactory circusFactory, CircusTimeFactory circustimeFactory)
  {
    zFactory_ = zFactory;
    circusFactory_ = circusFactory;
    circustimeFactory_ = circustimeFactory;
  }
  

  public CircusTimeFactory getCircusTimeFactory()
  {
    return circustimeFactory_;
  }
 
}

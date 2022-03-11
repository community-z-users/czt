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

package net.sourceforge.czt.typecheck.circusconf.impl;

import net.sourceforge.czt.circusconf.ast.CircusConfFactory;
import net.sourceforge.czt.z.ast.ZFactory;

/**
 *
 * @author Leo Freitas
 */
public class Factory 
  extends net.sourceforge.czt.typecheck.circus.impl.Factory
{
  
  /** The CircusToolsFactory that is used to create wrapped types. */
  protected CircusConfFactory circusConfFactory_;
  
  public Factory(ZFactory zFactory, net.sourceforge.czt.circus.ast.CircusFactory circusFactory, CircusConfFactory ccFactory)
  {
    super(zFactory, new net.sourceforge.czt.circus.util.Factory(circusFactory));
    circusConfFactory_ = new net.sourceforge.czt.circusconf.util.Factory(ccFactory);
  }
  
  public CircusConfFactory getCircusConfFactory()
  {
	 return circusConfFactory_;
  }
}

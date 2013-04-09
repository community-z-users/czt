/*
  Copyright (C) 2007 Leo Freitas
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
package net.sourceforge.czt.typecheck.circustime;

import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.circustime.ProcessChecker;
import net.sourceforge.czt.typecheck.circustime.ActionChecker;
import net.sourceforge.czt.typecheck.circus.WarningManager;

public class TypeChecker 
  extends net.sourceforge.czt.typecheck.circus.TypeChecker
  implements net.sourceforge.czt.typecheck.circus.TypecheckPropertiesKeys
{
	  public TypeChecker(net.sourceforge.czt.typecheck.circustime.impl.Factory factory,
              SectionManager sectInfo)
	  {
		  this(factory, sectInfo, true, false);
	  }

	  public TypeChecker(net.sourceforge.czt.typecheck.circustime.impl.Factory factory,
		      SectionManager sectInfo,
		      boolean recursiveTypes,
		      boolean sortDeclNames)
	  {
		  super(factory, sectInfo, recursiveTypes, sortDeclNames);
		  processChecker_ = new ProcessChecker(this);
		  actionChecker_ = new ActionChecker(this);	  
		  warningManager_ = new WarningManager(TypeChecker.class, sectInfo);		  
	  }
	  
	  public net.sourceforge.czt.typecheck.circustime.impl.Factory getFactory()
	  {
	    return (net.sourceforge.czt.typecheck.circustime.impl.Factory) super.getFactory();
	  }
	  protected void setPreamble(String sectName, SectionManager sectInfo)
	  {
	    super.setPreamble(sectName, sectInfo);
	  }   
}

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
package net.sourceforge.czt.typecheck.circusconf;

import net.sourceforge.czt.session.SectionManager;


/**
 *
 * @author Leo Freitas
 */
public class TypeChecker 
  extends net.sourceforge.czt.typecheck.circus.TypeChecker
  implements TypecheckPropertiesKeys
{
  
  public TypeChecker(net.sourceforge.czt.typecheck.circus.impl.Factory factory,
                     SectionManager sectInfo)
  {
    this(factory, sectInfo, PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT,
        PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT);
  }

  public TypeChecker(net.sourceforge.czt.typecheck.circus.impl.Factory factory,
                     SectionManager sectInfo,
                     boolean recursiveTypes,
                     boolean sortDeclNames)
  {
    // create all the checkers as default - for Z
    super(factory, sectInfo, recursiveTypes, sortDeclNames);     
  }  

  @Override
  public net.sourceforge.czt.typecheck.circus.impl.Factory getFactory()
  {
    return super.getFactory();
  }

  @Override
  protected void setPreamble(String sectName, SectionManager sectInfo)
  {
    super.setPreamble(sectName, sectInfo);
  }    

}

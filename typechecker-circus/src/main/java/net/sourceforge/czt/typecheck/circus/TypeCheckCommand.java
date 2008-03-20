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

package net.sourceforge.czt.typecheck.circus;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.ErrorAnn;

/**
 * A command to compute the SectTypeInfo of a Z section.
 */
public class TypeCheckCommand
  extends net.sourceforge.czt.typecheck.z.TypeCheckCommand
  implements TypecheckPropertiesKeys
{
  @Override
  protected List<? extends ErrorAnn> typecheck(Term term,
                                               SectionManager manager) {
    boolean useBeforeDecl = false && // don't accept this for now
      getBooleanProperty(manager, PROP_TYPECHECK_USE_BEFORE_DECL);
    boolean useNameIds = false && // don't accept this for now
      getBooleanProperty(manager, PROP_TYPECHECK_USE_NAMEIDS);
    boolean sortDeclNames = false && // don't accept this for now
      getBooleanProperty(manager, PROP_TYPECHECK_SORT_DECL_NAMES);
    boolean raiseWarnings =
      getBooleanProperty(manager, PROP_TYPECHECK_RAISE_WARNINGS);    
    return TypeCheckUtils.typecheck(term, manager, useBeforeDecl, 
      sortDeclNames, useNameIds, raiseWarnings, null);
  }
}

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

package net.sourceforge.czt.typecheck.zeves;

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
    return TypeCheckUtils.typecheck(term, manager, recursiveTypes_, sortDeclNames_,
      useNameIds_, warningOutput_, null);
  }

  @Override
  protected net.sourceforge.czt.typecheck.z.impl.SectSummaryAnn createSectSummaryEnv(String sectName)
  {
    return new net.sourceforge.czt.typecheck.zeves.impl.SectSummaryAnn(sectName);
  }

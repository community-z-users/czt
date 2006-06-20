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
package net.sourceforge.czt.typecheck.z.util;

import java.util.List;

import net.sourceforge.czt.z.ast.Type2;

/**
 * An annotation for recording a list of annotations associated with
 * an expression.
 */
public class ParameterAnn
{
  /** The parameters. */
  protected List<Type2> parameters_;

  public ParameterAnn(List<Type2> anns)
  {
    parameters_ = anns;
  }

  public List<Type2> getParameters()
  {
    return parameters_;
  }
}

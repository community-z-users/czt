/*
  Copyright (C) 2006 Mark Utting
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

package net.sourceforge.czt.z.util;

import java.util.ListResourceBundle;

/** This resource bundle translates {@link ConcreteSyntaxSymbol}
 *  elements into short descriptions.
 *  Currently, the resulting string (typically 4-14 characters long)
 *  is simply the name of the ConcreteSyntaxSymbol itself.
 *  This can be used as a very short summary of the AST node,
 *  for example, in an outline editor in JEdit or Eclipse.
 *
 * @author Petra Malik
 */
public class ShortDescriptionResourceBundle
  extends ListResourceBundle
{
  private static final Object[][] CONTENTS = computeContents();

  private static Object[][] computeContents()
  {
    Object[][] result = new Object[ConcreteSyntaxSymbol.values().length][2];
    int i = 0;
    for (ConcreteSyntaxSymbol sym : ConcreteSyntaxSymbol.values()) {
      result[i][0] = sym.toString();
      result[i][1] = sym.toString();
      i++;
    }
    return result;
  }

  public Object[][] getContents()
  {
    return CONTENTS.clone();//don't expose contents
  }
}

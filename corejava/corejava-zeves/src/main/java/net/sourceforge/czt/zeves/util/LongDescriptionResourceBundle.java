/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.zeves.util;

import java.util.ListResourceBundle;

/** This resource bundle translates ConcreteSyntaxSymbol
 *  elements into long human-readable descriptions.
 *  The resulting strings (typically 20-40 characters long)
 *  can be displayed as a summary of the meaning of each Z construct.
 *
 * @author Petra Malik
 */
public class LongDescriptionResourceBundle
  extends ListResourceBundle
{
  private static final Object[][] CONTENTS = computeContents();

  private static Object[][] computeContents()
  {
    Object[][] result = new Object[ZEvesConcreteSyntaxSymbol.values().length][2];
    int i = 0;
    for (ZEvesConcreteSyntaxSymbol sym : ZEvesConcreteSyntaxSymbol.values()) {
      result[i][0] = sym.toString();
      result[i][1] = ZEvesUtils.getConcreteSyntaxSymbolLongDesc(sym);
      i++;
    }
    return result;
  }

  @Override
  public Object[][] getContents()
  {
    return CONTENTS;
  }
}

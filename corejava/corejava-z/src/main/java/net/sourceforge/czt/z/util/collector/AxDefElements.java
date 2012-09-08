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
package net.sourceforge.czt.z.util.collector;

import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Jul 25, 2011
 */
public class AxDefElements extends GenericElements<AxPara>
{

  private ZSchText fZSchText;
  private ZSchTextCollector<AxPara> fZSchTextCollector;

  AxDefElements()
  {
    super();
    fZSchText = null;
    fZSchTextCollector = new ZSchTextCollector<AxPara>();
  }

  public ZSchText getZSchText()
  {
    return fZSchText;
  }

  @Override
  public void collect(AxPara term)
  {
    assert term.getBox().equals(Box.AxBox) || term.getBox().equals(Box.OmitBox);
    //TODO: add some labelling/tagging here for AxBox?
    setName(ZUtils.isAbbreviation(term) ?
        ZUtils.assertZName(ZUtils.getAbbreviationName(term)).getWord() : "");
    collectGenerics(ZUtils.getAxParaZGenFormals(term));
    fZSchText = term.getZSchText();
    fZSchText.accept(fZSchTextCollector);
  }
  /* TODO: Include the ZSchTextCollector information here */
}

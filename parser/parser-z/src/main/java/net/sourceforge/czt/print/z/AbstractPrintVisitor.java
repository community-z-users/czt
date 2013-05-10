/*
  Copyright 2004, 2005, 2006, 2007 Petra Malik
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

package net.sourceforge.czt.print.z;

import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.parser.util.AbstractVisitor;
import net.sourceforge.czt.parser.util.Token;

/**
 * A Z visitor used for printing.
 *
 * @author Petra Malik
 */
public abstract class AbstractPrintVisitor<R>
  extends AbstractVisitor<R>
{
  private ZPrinter printer_;

  public AbstractPrintVisitor(SectionInfo sectInfo)
  {
	super(sectInfo);  
  }
  
  public AbstractPrintVisitor(SectionInfo sectInfo, ZPrinter printer)
  {
	super(sectInfo);
    printer_ = printer;
  }

  public ZPrinter getPrinter()
  {
    return printer_;
  }

  public void setPrinter(ZPrinter printer)
  {
    printer_ = printer;
  }

  protected void print(Token token)
  {
    printer_.printToken(token);
  }
}

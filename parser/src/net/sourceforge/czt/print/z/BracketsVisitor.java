/**
Copyright 2004 Petra Malik
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

import java.util.Iterator;
import java.util.List;

import java_cup.runtime.Symbol;

import net.sourceforge.czt.util.Visitor;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;

import net.sourceforge.czt.util.CztException;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * A Z visitor used for printing.
 *
 * @author Petra Malik
 */
public class BracketsVisitor
  extends AbstractPrintVisitor
  implements TermAVisitor
{
  public BracketsVisitor(ZPrinter printer)
  {
    super(printer);
  }

  public Object visitTermA(TermA termA)
  {
    List anns = termA.getAnns();
    for (Iterator iter = anns.iterator(); iter.hasNext(); )
    {
      if (iter.next() instanceof ParenAnn) {
        print(Sym.LPAREN);
      }
    }
    termA.accept(getVisitor());
    for (Iterator iter = anns.iterator(); iter.hasNext(); )
    {
      if (iter.next() instanceof ParenAnn) {
        print(Sym.RPAREN);
      }
    }
    return null;
  }
}

/**
Copyright (C) 2004 Petra Malik
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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.ast.TermA;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.TermAVisitor;
import net.sourceforge.czt.z.ast.ParenAnn;

/**
 * This class is a helper class for the ZPrintVisitor.  It is usually
 * not used alone but together with another visitor.  It visits all
 * terms, prints a left parenthesis when the visited term is an
 * annotated term and has a ParenAnn annotation, then calls the other
 * visitor to do its work and finally prints the right paranthesis if
 * a left parenthesis has been printed as well.
 *
 * @author Petra Malik
 */
public class BracketsVisitor
  extends AbstractPrintVisitor
  implements TermVisitor, TermAVisitor
{

  /**
   * Creates a new BracketsVisitor that uses the given printer to
   * print the brackets.
   */
  public BracketsVisitor(ZPrinter printer)
  {
    super(printer);
  }

  /**
   * Just call the provided visitor to do its work.
   *
   * @param term the term to be visited.
   * @return <code>null</code>.
   */
  public Object visitTerm(Term term)
  {
    term.accept(getVisitor());
    return null;
  }

  /**
   * Prints left parenthesis, calls the provided visitor,
   * and prints right parenthesis.  The number of parenthesis
   * printed is equal to the number of ParenAnn found in
   * the annotation list.  If an annotated term doesn't have
   * ParenAnn, no parenthesis are printed.
   *
   * @param termA the annotated term to be visited.
   * @return <code>null</code>.
   */
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

/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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

package net.sourceforge.czt.print.ast;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Assoc;
import net.sourceforge.czt.z.impl.ParaImpl;

/**
 * A printable paragraph.
 *
 * @author Petra Malik
 */
public class PrintParagraph
  extends ParaImpl
{
  List<?> something_;

  protected PrintParagraph(PrintFactory factory, List<?> something)
  {
    super(factory);
    something_ = something;
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof PrintParagraphVisitor) {
      PrintParagraphVisitor<R> v = (PrintParagraphVisitor<R>) visitor;
      return v.visitPrintParagraph(this);
    }
    return super.accept(visitor);
  }

  public Object[] getChildren()
  {
    return something_.toArray();
  }

  public PrintParagraph create(Object[] children)
  {
    throw new UnsupportedOperationException();
  }
}

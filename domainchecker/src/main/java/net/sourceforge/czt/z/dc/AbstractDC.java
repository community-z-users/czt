/**
Copyright 2007, Leo Freitas
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.z.dc;

import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.util.Factory;

/**
 *
 * @author leo
 */
public abstract class AbstractDC<R> implements Visitor<R>, TermVisitor<R>
{  
  protected static final Factory factory_ = new Factory();
  
  /** Creates a new instance of AbstractDC */
  public AbstractDC()
  {
  }
  
  /** Creates a TruePred (i.e. true) */
  protected Pred truePred()
  {
    return factory_.createTruePred();
  }
}

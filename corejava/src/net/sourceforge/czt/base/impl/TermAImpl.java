/*
  Copyright 2003, 2005 Mark Utting
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

package net.sourceforge.czt.base.impl;

import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;

import net.sourceforge.czt.base.visitor.TermAVisitor;
import net.sourceforge.czt.util.Visitor;

/**
 * An abstract implementation of the interface {@link TermA}.
 *
 * @author Petra Malik
 */
public abstract class TermAImpl extends TermImpl implements TermA
{
  /**
   * A list of annotations.
   */
  private ListTerm anns_ = new ListTermImpl(Object.class);

  /**
   * Returns a list of annotiations.
   */
  public ListTerm getAnns()
  {
    return anns_;
  }

  public Object getAnn(Class aClass)
  {
    for (Iterator iter = anns_.iterator(); iter.hasNext(); ) {
      Object annotation = iter.next();
      if (aClass.isInstance(annotation)) {
        return annotation;
      }
    }
    return null;
  }

  public <R> R accept(Visitor<R> v)
  {
    if (v instanceof TermAVisitor) {
      TermAVisitor<R> visitor = (TermAVisitor<R>) v;
      return visitor.visitTermA(this);
    }
    return super.accept(v);
  }

  public boolean equals(Object obj)
  {
    if (obj != null && this.getClass().equals(obj.getClass())) {
      return super.equals(obj);
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;
    int erg = super.hashCode();
    String s = "TermA";
    erg += constant * s.hashCode();
    return erg;
  }
}

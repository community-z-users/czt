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
package net.sourceforge.czt.typecheck.z.impl;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * An implementation for Term that hides VariableType instances
 * if they have a value.
 */
public abstract class TermAImpl
  extends TermImpl
  implements TermA
{
  protected TermAImpl(TermA termA)
  {
    super(termA);
  }

  public ListTerm<Object> getAnns()
  {
    ListTerm<Object> result = new ListTermImpl<Object>();
    if (term_ != null) {
      result = ((TermA) term_).getAnns();
    }
    return result;
  }

  public Object getAnn(Class aClass)
  {
    Object result = null;
    if (term_ != null) {
      result = ((TermA) term_).getAnn(aClass);
    }
    return result;
  }
}

/*
 * GetChildrenVisitor.java
 * Copyright (C) 2006 Petra Malik
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package net.sourceforge.czt.jedit.zsidekick;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

public class GetChildrenVisitor
  implements TermVisitor<Term[]>,
             ZParaListVisitor<Term[]>,
             ZSectVisitor<Term[]>
{
  public Term[] visitTerm(Term term)
  {
    return new Term[0];
  }

  public Term[] visitZSect(ZSect zSect)
  {
    return zSect.getParaList().accept(this);
  }

  public Term[] visitZParaList(ZParaList list)
  {
    List<Para> result = new ArrayList<Para>();
    for (Para para : list) {
      if (! (para instanceof LatexMarkupPara) &&
          ! (para instanceof NarrPara)) {
        result.add(para);
      }
    }
    return result.toArray(new Term[0]);
  }
}

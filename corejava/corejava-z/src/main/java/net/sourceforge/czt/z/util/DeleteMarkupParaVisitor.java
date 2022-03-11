/*
  Copyright 2004, 2006 Mark Utting
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

package net.sourceforge.czt.z.util;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

public class DeleteMarkupParaVisitor
  implements TermVisitor<Term>,
             LatexMarkupParaVisitor<Term>,
             SpecVisitor<Term>,
             ZParaListVisitor<Term>,
             ZSectVisitor<Term>
{
  /**
   * Returns the given term.  No iteration is needed since
   * MarkupPara are only possible in specifications or sections.
   */
  public Term visitTerm(Term term)
  {
    return term;
  }

  /**
   * Visit all sections contained in the section list.  The
   * specification is returned unchanged iff visiting all sections
   * returned the same section as provided.  Otherwise, a new
   * specification is created containing the sections returned by the
   * visit calls.
   */
  public Term visitSpec(Spec spec)
  {
    List<Sect> newSects = new ArrayList<Sect>(spec.getSect().size());
    for (Sect sect : spec.getSect()) {
      newSects.add((Sect) sect.accept(this));
    }
    if (spec.getSect().equals(newSects)) {
      return spec;
    }
    Object[] children = spec.getChildren();
    children[0] = newSects;
    return spec.create(children);
  }

  public Term visitLatexMarkupPara(LatexMarkupPara term)
  {
    return null;
  }

  /**
   * Visits all the paragraphs and returns a new paragraph list if a
   * call to the visit method has changed a child.  It also removes
   * empty paragraphs.
   */
  public Term visitZParaList(ZParaList list)
  {
    ZParaList newList = (ZParaList) list.create(new Object[0]);
    for (Para para : list) {
      Para p = (Para) para.accept(this);
      if (p != null) newList.add(para);
    }
    if (newList.equals(list)) return list;
    return newList;
  }

  /**
   * The Z section is returned unchanged iff it did not contain
   * markup paragraphs.  Otherwise, a new Z section is created
   * containing all paragraphs contained by <code>zSect</code>
   * but markup paragraphs.
   */
  public Term visitZSect(ZSect zSect)
  {
    ParaList paraList = (ParaList) zSect.getParaList().accept(this);
    if (paraList.equals(zSect.getParaList())) return zSect;
    Object[] children = { zSect.getName(), zSect.getParent(), paraList };
    return zSect.create(children);
  }
}

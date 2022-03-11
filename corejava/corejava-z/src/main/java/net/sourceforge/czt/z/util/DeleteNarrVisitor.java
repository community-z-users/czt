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

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * A visitor that removes all narrative paragraphs and sections from a
 * specification.
 *
 * @author Petra Malik
 */
public class DeleteNarrVisitor
  implements TermVisitor<Term>,
             NarrParaVisitor<Term>,
             NarrSectVisitor<Term>,
             SpecVisitor<Term>,
             ZParaListVisitor<Term>,
             ZSectVisitor<Term>
{
  /**
   * @return the given term unchanged.  No iteration is needed since
   *         narratives are only possible in specifications or sections.
   */
  public Term visitTerm(Term term)
  {
    return term;
  }

  /**
   * @return {@code null}
   */
  public Term visitNarrPara(NarrPara narrPara)
  {
    return null;
  }

  /**
   * @return {@code null}
   */
  public Term visitNarrSect(NarrSect narrSect)
  {
    return null;
  }

  /**
   * Visit all sections contained in the section list and removes
   * all narrative sections.
   * The specification is returned unchanged iff visiting all sections
   * returned the same section as provided and no narrative section
   * was found.  Otherwise, a new specification is created containing
   * non-narrative sections returned by the visit calls.
   */
  public Term visitSpec(Spec spec)
  {
    Spec newSpec = (Spec) spec.create(spec.getChildren());
    List<Sect> newSects = newSpec.getSect();
    newSects.clear();
    for (Sect sect : spec.getSect()) {
      sect = (Sect) sect.accept(this);
      if (sect != null) newSects.add(sect);
    }
    if (spec.getSect().equals(newSects)) {
      return spec;
    }
    return newSpec;
  }

  /**
   * Removes all narrative paragraphs from the paragraph list.
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
   * narrative paragraphs.  Otherwise, a new Z section is returned,
   * containing all paragraphs contained in {@code zSect} except for
   * narrative paragraphs.
   */
  public Term visitZSect(ZSect zSect)
  {
    ParaList paraList = (ParaList) zSect.getParaList().accept(this);
    if (paraList.equals(zSect.getParaList())) return zSect;
    Object[] children = { zSect.getName(), zSect.getParent(), paraList };
    return zSect.create(children);
  }
}

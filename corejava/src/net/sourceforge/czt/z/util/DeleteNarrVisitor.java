/*
Copyright 2004 Mark Utting
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
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

public class DeleteNarrVisitor
  implements TermVisitor, SpecVisitor, ZSectVisitor
{
  /**
   * Returns the given term.  No iteration is needed since
   * Narrative are only possible in specifications or sections.
   */
  public Object visitTerm(Term term)
  {
    return term;
  }

  /**
   * Visit all sections contained in the section list and removes
   * all narrative sections.
   * The specification is returned unchanged iff visiting all sections
   * returned the same section as provided and no narrative section
   * was found.  Otherwise, a new specification is created containing
   * non-narrative sections returned by the visit calls.
   */
  public Object visitSpec(Spec spec)
  {
    List sects = spec.getSect();
    List newSects = new ArrayList();
    for (Iterator iter = sects.iterator(); iter.hasNext();) {
      Sect sect = (Sect) ((Sect) iter.next()).accept(this);
      if (! (sect instanceof NarrSect)) newSects.add(sect);
    }
    if (sects.equals(newSects)) {
      return spec;
    }
    Spec result = (Spec) spec.create(spec.getChildren());
    sects = result.getSect();
    sects.clear();
    sects.addAll(newSects);
    return result;
  }

  /**
   * Removes all narrative paragraphs from the paragraph list.
   * The Z section is returned unchanged iff it did not contain
   * narrative paragraphs.  Otherwise, a new Z section is created
   * containing all paragraphs contained by <code>zSect</code>
   * but narrative paragraphs.
   */
  public Object visitZSect(ZSect zSect)
  {
    List paras = zSect.getPara();
    List newParas = new ArrayList();
    for (Iterator iter = paras.iterator(); iter.hasNext();) {
      Para para = (Para) iter.next();
      if (! (para instanceof NarrPara)) newParas.add(para);
    }
    if (paras.equals(newParas)) {
      return zSect;
    }
    ZSect result = (ZSect) zSect.create(zSect.getChildren());
    paras = result.getPara();
    paras.clear();
    paras.addAll(newParas);
    return result;
  }
}

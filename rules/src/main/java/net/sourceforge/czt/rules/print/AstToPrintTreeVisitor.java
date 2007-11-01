/*
  Copyright (C) 2006 Petra Malik
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

package net.sourceforge.czt.rules.print;

import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.base.ast.*;
import  net.sourceforge.czt.rules.Joker;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.*;
import net.sourceforge.czt.zpatt.visitor.*;

public class AstToPrintTreeVisitor
  extends net.sourceforge.czt.print.z.AstToPrintTreeVisitor
  implements HeadDeclListVisitor<Term>
{
  Factory factory_ = new Factory();

  public AstToPrintTreeVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
  }

  public Term visitTerm(Term term)
  {
    if (term instanceof Joker && ((Joker) term).boundTo() != null) {
      return visit(((Joker) term).boundTo());
    }
    return super.visitTerm(term);
  }

  public Term visitHeadDeclList(HeadDeclList hdl)
  {
    JokerDeclList jdl = hdl.getJokerDeclList();
    if (jdl instanceof Joker && ((Joker) jdl).boundTo() != null) {
      ZDeclList zdl = (ZDeclList) visit(hdl.getZDeclList());
      if (zdl == hdl.getZDeclList()) {
        zdl = factory_.createZDeclList();
        zdl.addAll(hdl.getZDeclList());
      }
      Object obj = visit(((Joker) jdl).boundTo());
      if (obj instanceof ZDeclList) {
        zdl.addAll((ZDeclList) obj);
      }
      else {
        HeadDeclList hdl2 = (HeadDeclList) obj;
        zdl.addAll(hdl2.getZDeclList());
        return factory_.createHeadDeclList(zdl, hdl2.getJokerDeclList());
      }
      return zdl;
    }
    return super.visitTerm(hdl);
  }
}

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

package net.sourceforge.czt.print.oz;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;

/**
 */
public class AstToPrintTreeVisitor
  extends net.sourceforge.czt.print.z.AstToPrintTreeVisitor
  implements ClassParaVisitor<Term>

{
  /**
   * Creates a new ast to print tree visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public AstToPrintTreeVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
  }

  public Term visitClassPara(ClassPara classPara)
  {
    //don't visit inner AxPara paragraphs
    List<Para> paras = classPara.getLocalDef();
    for (int i = 0; i < paras.size(); i++) {
      Para para = paras.get(i);
      if (para instanceof AxPara) {
        AxPara axPara = (AxPara) para;
        if (Box.OmitBox.equals(axPara.getBox())) {
          axPara.setBox(Box.AxBox);
        }
      }
      Para newPara = (Para) visit(para);
      paras.set(i, newPara);
    }

    State state = classPara.getState();
    if (state != null) {
      classPara.setState((State) visit(state));
    }

    InitialState initialState = classPara.getInitialState();
    if (initialState != null) {
      classPara.setInitialState((InitialState) visit(initialState));
    }

    List<Operation> ops = classPara.getOperation();
    for (int i = 0; i < ops.size(); i++) {
      ops.set(i, (Operation) visit(ops.get(i)));
    }

    return classPara;
  }
}

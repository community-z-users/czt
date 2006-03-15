/*
 * LongStringVisitor.java
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
package zsidekick;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

public class LongStringVisitor
  implements TermVisitor<String>,
             AxParaVisitor<String>,
             ConjParaVisitor<String>,
             FreeParaVisitor<String>,
             GivenParaVisitor<String>,
             NarrParaVisitor<String>,
             NarrSectVisitor<String>,
             OptempParaVisitor<String>,
             UnparsedParaVisitor<String>,
             ZSectVisitor<String>
{
  public String visitTerm(Term term)
  {
    return term.getClass().getName();
  }

  public String visitAxPara(AxPara axPara)
  {
    String result = "Axiomatic description paragraph";
    final Box box = axPara.getBox();
    try {
      if (Box.OmitBox.equals(box)) {
        result = "Definition paragraph";
      }
      else if (Box.SchBox.equals(box)) {
        ConstDecl constDecl =
          (ConstDecl) axPara.getZSchText().getZDeclList().get(0);
        result = "Schema paragraph for \"" +
          constDecl.getZDeclName().getWord() + "\"";
      }
    }
    catch (Exception e) {}
    return result;
  }

  public String visitConjPara(ConjPara conjPara)
  {
    return "Conjecture paragraph";
  }

  public String visitFreePara(FreePara freePara)
  {
    return "Free types paragraph";
  }

  public String visitGivenPara(GivenPara givenPara)
  {
    return "Given types paragraph";
  }

  public String visitNarrPara(NarrPara narrPara)
  {
    return "Narrative paragraph";
  }

  public String visitNarrSect(NarrSect narrSect)
  {
    return "Narrative section";
  }

  public String visitOptempPara(OptempPara optempPara)
  {
    return "Operator template parargraph";
  }

  public String visitUnparsedPara(UnparsedPara unparsedPara)
  {
    return "Unparsed paragraph";
  }

  public String visitZSect(ZSect zSect)
  {
    return "Z section '" + zSect.getName() + "'";
  }
}

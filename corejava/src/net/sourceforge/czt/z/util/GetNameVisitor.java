/*
  Copyright (C) 2006 Mark Utting
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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * @author Petra Malik
 */
public class GetNameVisitor
  implements AxParaVisitor<String>,
             ConstDeclVisitor<String>,
             FreeParaVisitor<String>,
             FreetypeVisitor<String>,
             GivenParaVisitor<String>,
             ListTermVisitor<String>,
             VarDeclVisitor<String>,
             ZDeclListVisitor<String>,
             ZDeclNameVisitor<String>,
             ZRefNameVisitor<String>,
             ZSchTextVisitor<String>,
             ZSectVisitor<String>
{
  private final String LIST_SEPARATOR = ", ";

  public String visitAxPara(AxPara axPara)
  {
    return visit(axPara.getSchText());
  }

  public String visitConstDecl(ConstDecl constDecl)
  {
    return visit(constDecl.getDeclName());
  }

  public String visitFreePara(FreePara freePara)
  {
    return visit(freePara.getFreetype());
  }

  public String visitFreetype(Freetype freetype)
  {
    return visit(freetype.getDeclName());
  }

  public String visitGivenPara(GivenPara givenPara)
  {
    return visit(givenPara.getDeclName());
  }

  public String visitListTerm(ListTerm listTerm)
  {
    return visitList(listTerm);
  }

  public String visitVarDecl(VarDecl varDecl)
  {
    return visit(varDecl.getDeclName());
  }

  public String visitZDeclList(ZDeclList zDeclList)
  {
    return visitList(zDeclList);
  }

  public String visitZDeclName(ZDeclName zDeclName)
  {
    return zDeclName.getWord();
  }

  public String visitZRefName(ZRefName zRefName)
  {
    return zRefName.getWord();
  }

  public String visitZSchText(ZSchText zSchText)
  {
    return visit(zSchText.getDeclList());
  }

  public String visitZSect(ZSect zSect)
  {
    return zSect.getName();
  }

  protected String visit(Term term)
  {
    return term.accept(this);
  }

  protected String visitList(List<? extends Term> list)
  {
    final StringBuffer result = new StringBuffer();
    String separator = "";
    for (Term term : list) {
      final String next = term.accept(this);
      if (next != null && ! "".equals(next)) {
        result.append(separator + next);
        separator = LIST_SEPARATOR;
      }
    }
    return result.toString();
  }
}

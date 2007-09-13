/*
  Copyright (C) 2006, 2007 Mark Utting
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

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.ListTermVisitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * @author Petra Malik
 */
public class GetNameVisitor
  extends PrintVisitor
  implements TermVisitor<String>,
	     AxParaVisitor<String>,
             ConstDeclVisitor<String>,
             FreeParaVisitor<String>,
             FreetypeVisitor<String>,
             GivenParaVisitor<String>,
             ListTermVisitor<String>,
             VarDeclVisitor<String>,
             ZDeclListVisitor<String>,
             ZNameListVisitor<String>,
             ZFreetypeListVisitor<String>,
             ZSchTextVisitor<String>,
             ZSectVisitor<String>
{
  private static final String LIST_SEPARATOR = ", ";

  public String visitTerm(Term term)
  {
    return null;
  }

  public String visitAxPara(AxPara axPara)
  {
    return visit(axPara.getSchText());
  }

  public String visitConstDecl(ConstDecl constDecl)
  {
    return visit(constDecl.getName());
  }

  public String visitFreePara(FreePara freePara)
  {
    return visit(freePara.getFreetypeList());
  }

  public String visitFreetype(Freetype freetype)
  {
    return visit(freetype.getName());
  }

  public String visitGivenPara(GivenPara givenPara)
  {
    return visit(givenPara.getNameList());
  }

  public String visitListTerm(ListTerm listTerm)
  {
    final StringBuilder result = new StringBuilder();
    String sep = LIST_SEPARATOR;
    boolean first = true;
    for (Object obj : listTerm) {
      String string;
      if (obj instanceof Term) string = visit((Term) obj);
      else string = obj.toString();
      if (string != null) {
        if (! first) result.append(sep);
        result.append(string);
        first = false;
      }
    }
    return result.toString();
  }

  public String visitVarDecl(VarDecl varDecl)
  {
    return visit(varDecl.getNameList());
  }

  public String visitZDeclList(ZDeclList zDeclList)
  {
    return visitList(zDeclList, LIST_SEPARATOR);
  }

  public String visitZNameList(ZNameList zdnl)
  {
    return visitList(zdnl, LIST_SEPARATOR);
  }

  public String visitZFreetypeList(ZFreetypeList list)
  {
    return visitList(list, LIST_SEPARATOR);
  }

  public String visitZSchText(ZSchText zSchText)
  {
    return visit(zSchText.getDeclList());
  }

  public String visitZSect(ZSect zSect)
  {
    return zSect.getName();
  }
}

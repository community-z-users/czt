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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * @author Petra Malik
 */
public class GetNameVisitor
  implements ZSectVisitor<String>,
             AxParaVisitor<String>,
             ConstDeclVisitor<String>,
             FreeParaVisitor<String>,
             FreetypeVisitor<String>,
             ListTermVisitor<String>,
             VarDeclVisitor<String>,
             ZDeclListVisitor<String>,
             ZDeclNameVisitor<String>,
             ZSchTextVisitor<String>
{
  public String visitAxPara(AxPara axPara)
  {
    return axPara.getSchText().accept(this);
  }

  public String visitConstDecl(ConstDecl constDecl)
  {
    return constDecl.getDeclName().accept(this);
  }

  public String visitFreePara(FreePara freePara)
  {
    return freePara.getFreetype().accept(this);
  }

  public String visitFreetype(Freetype freetype)
  {
    return freetype.getDeclName().accept(this);
  }

  public String visitListTerm(ListTerm listTerm)
  {
    if (listTerm.size() > 0) {
      Object obj = listTerm.get(0);
      if (obj instanceof Term) {
        return ((Term) obj).accept(this);
      }
    }
    return null;
  }

  public String visitVarDecl(VarDecl varDecl)
  {
    return varDecl.getDeclName().accept(this);
  }

  public String visitZDeclList(ZDeclList zDeclList)
  {
    if (zDeclList.size() > 0) return zDeclList.get(0).accept(this);
    return null;
  }

  public String visitZDeclName(ZDeclName zDeclName)
  {
    return zDeclName.getWord();
  }

  public String visitZSect(ZSect zSect)
  {
    return zSect.getName();
  }

  public String visitZSchText(ZSchText zSchText)
  {
    return zSchText.getDeclList().accept(this);
  }
}

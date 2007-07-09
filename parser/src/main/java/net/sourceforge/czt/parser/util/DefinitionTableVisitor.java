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

package net.sourceforge.czt.parser.util;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.visitor.*;

/**
 * A visitor that computes a {@link DefinitionTable} from a given
 * Z Section.
 *
 * @author Petra Malik
 */
public class DefinitionTableVisitor
  extends AbstractVisitor
  implements TermVisitor,
             AxParaVisitor,
             ParaVisitor,
             ZParaListVisitor,
             ZSectVisitor
{
  private DefinitionTable table_;

  /**
   * Creates a new definition table visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.DefinitionTable.class</code>.
   */
  public DefinitionTableVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
  }

  public Object run(Term term)
    throws CommandException
  {
    super.run(term);
    return getDefinitionTable();
  }

  protected DefinitionTable getDefinitionTable()
  {
    return table_;
  }

  public Object visitTerm(Term term)
  {
    final String message = "DefinitionTables can only be build for ZSects; " +
      "was tried for " + term.getClass();
    throw new UnsupportedOperationException(message);
  }

  public Object visitZParaList(ZParaList list)
  {
    for (Para p : list) visit(p);
    return null;
  }
  
  public Object visitAxPara(AxPara axPara)
  { 
    // gets the generic names
    ZNameList genFormals = axPara.getZNameList();
    
    // gets the declarations 
    ZSchText schText = axPara.getZSchText();
    List<Decl> decls = schText.getZDeclList();
    
    for (Iterator<Decl> iter = decls.iterator(); iter.hasNext(); ) {
      Decl decl = iter.next();
      // 
      if (decl instanceof ConstDecl) 
      {        
        ConstDecl constDecl = (ConstDecl) decl;        
        addDefinition(genFormals, constDecl.getName(), constDecl.getExpr(), DefinitionType.CONSTDECL);
      } 
      else if (decl instanceof VarDecl)
      {
        VarDecl varDecl = (VarDecl) decl;
        Expr defExpr = varDecl.getExpr();
        for(Name name : varDecl.getZNameList())
        {
          addDefinition(genFormals, name, defExpr, DefinitionType.VARDECL);
        }
      }
      else if (decl instanceof InclDecl)
      {
        // TODO: What to do when finding inclusions on Ax boxes?
      }
    }
    return null;
  }

  public Object visitPara(Para para)
  {
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    List parentTables = new ArrayList();
    for (Iterator iter = zSect.getParent().iterator(); iter.hasNext(); ) {
      Parent parent = (Parent) iter.next();
      DefinitionTable parentTable =
        (DefinitionTable) get(parent.getWord(), DefinitionTable.class);
      parentTables.add(parentTable);
    }
    try {
      table_ = new DefinitionTable(name, parentTables);
    }
    catch (DefinitionTable.DefinitionException exception)
    {
      throw new CztException(exception);
    }
    visit(zSect.getParaList());
    return null;
  }

  protected void visit(Term term)
  {
    term.accept(this);
  }
  
  protected void addDefinition(ZNameList genFormals, Name declName, Expr defExpr, DefinitionType type)
  {
    String name = declName.accept(new PrintVisitor());
    DefinitionTable.Definition def =
      new DefinitionTable.Definition(genFormals, defExpr, type);
    try {
      table_.add(name, def);
    }
    catch (DefinitionTable.DefinitionException e) {
      throw new CztException(e);
    }
  }
}

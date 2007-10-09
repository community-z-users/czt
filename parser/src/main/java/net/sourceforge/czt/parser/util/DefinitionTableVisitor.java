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
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.*;

/**
 * A visitor that computes a {@link DefinitionTable} from a given
 * Z Section.
 *
 * @author Petra Malik
 */
public class DefinitionTableVisitor
  extends AbstractVisitor<Object>
  implements TermVisitor<Object>,
             AxParaVisitor<Object>,
             ParaVisitor<Object>,
             ZParaListVisitor<Object>,
             ZSectVisitor<Object>
{
  private DefinitionTable table_;
  private final PrintVisitor printVisitor_;
  
  private static final Logger logger_ = Logger.getLogger(DefinitionTableVisitor.class.getName());
          
  /**
   * Creates a new definition table visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.DefinitionTable.class</code>.
   */
  public DefinitionTableVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
    printVisitor_ = new PrintVisitor();
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
    
    // processes all declarations from axPara
    processDeclList(genFormals, decls);
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
    String name = declName.accept(printVisitor_);
    DefinitionTable.Definition def =
      new DefinitionTable.Definition(genFormals, defExpr, type);
    try {
      table_.add(name, def);
    }
    catch (DefinitionTable.DefinitionException e) {
      throw new CztException(e);
    }
  }
  
//  private static int complexInclDeclSeed = 0;
//  public static final String COMPLEX_INCLDECL_NAME_PATTERN = "complexInclDecl$$";
//  
//  protected static String createNewInclDeclDefName()
//  {
//    complexInclDeclSeed++;
//    return COMPLEX_INCLDECL_NAME_PATTERN + complexInclDeclSeed;
//  }
//  
//  protected void addComplexInclDeclDefinition(ZNameList genFormals, Expr expr)
//  {
//    String name = createNewInclDeclDefName();    
//    addDefinition(genFormals, ZUtils.FACTORY.createZName(name), DefinitionType.INCLDECL);    
//  }
//  
  protected void processDeclList(ZNameList genFormals, List<Decl> decls) 
  {
    for (Iterator<Decl> iter = decls.iterator(); iter.hasNext(); ) 
    {
      Decl decl = iter.next();
      // 
      if (decl instanceof ConstDecl) 
      {        
        ConstDecl constDecl = (ConstDecl) decl;        
        addDefinition(genFormals, constDecl.getName(), constDecl.getExpr(),
            DefinitionType.CONSTDECL);
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
        // TODO: What to do when finding inclusions in Ax boxes?
        // For now, we just ignore them, which means that our definition
        // tables are incomplete.  This is not a disaster, since we currently
        // use these definition tables to get *extra* information.
        //
        // A general solution is difficult, since
        // the inclusion expression could be a schema expression that uses
        // fancy schema operators like composition and renaming, which
        // obfuscates the set of names that it declares.  A possible 
        // solution might be to handle just the easy case here
        // (where the schema inclusion is just a name, or perhaps a
        // decorated name), and ignore the complex cases, or use the
        // typechecker to map every declared name to its carrier set.        

// THIS GOES SOMEWHERE ELSE        
//        InclDecl inclDecl = (InclDecl) decl;
//        Name name;
//        Expr expr = inclDecl.getExpr();
//
//        // if it is a reference inclusion, then it is easy
//        if (expr instanceof RefExpr)
//        {
//          RefExpr refExpr = (RefExpr) expr;
//          name = refExpr.getName();
//          String strName = name.accept(printVisitor_);
//          DefinitionTable.Definition def = table_.lookup(strName);
//          if (def != null &&
//              def.getDefinitionType().equals(DefinitionType.CONSTDECL) &&
//              def.getExpr() instanceof SchExpr)
//          {
//            SchExpr schExpr = (SchExpr)def.getExpr();
//            schExpr.getZSchText().getZDeclList()
//            def.getExpr().accept(this);
//          }
//          else 
//          {
//            logger_.warning("Reference to a complex (schema) expression. " +
//              "Added as INCLDECL. Other tools might try to process it further.");
//            addDefinition(genFormals, name, refExpr, DefinitionType.INCLDECL);            
//          }
//        }
//        else 
//        {          
//          // otherwise, we would need a dual-phase visiting.
//          // e.g., (S \land T), go through S and T ?
//          logger_.warning("Could not calculate definition table for schema " +
//            "inclusion that is not a reference name. Adding it with name " + name 
//            + " as INCLDECL. Other tools might try to process it further.");
//          addComplexInclDeclDefinition(genFormals, expr);
//        }        
      }
    }
  }
}

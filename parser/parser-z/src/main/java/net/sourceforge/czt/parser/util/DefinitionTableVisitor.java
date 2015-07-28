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

import java.util.ArrayList;
import java.util.List;

import java.util.Stack;
import java.util.logging.Level;
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
  
  /** The name of the section whose paragraphs are being processed. */
  private String sectName_;

  /**
   * Creates a new definition table visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.DefinitionTable.class</code>.
   * @param sectInfo
   */
  public DefinitionTableVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
    printVisitor_ = new PrintVisitor();
  }

  @Override
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

  @Override
  public Object visitTerm(Term term)
  {
    final String message = "DefinitionTables can only be build for ZSects; " +
      "was tried for " + term.getClass();
    throw new UnsupportedOperationException(message);
  }

  @Override
  public Object visitZParaList(ZParaList list)
  {
    for (Para p : list) visit(p);
    return null;
  }

  @Override
  public Object visitAxPara(AxPara axPara)
  {
    // gets the generic names
    ZNameList genFormals = axPara.getZNameList();

    // gets the declarations
    ZSchText schText = axPara.getZSchText();
    List<Decl> decls = schText.getZDeclList();

    // processes all declarations from axPara with an empty stroke stack.
    // stroke stacks are used to process DecorExpr within InclDecls
    processDeclList(genFormals, decls, new Stack<Stroke>());
    return null;
  }

  @Override
  public Object visitPara(Para para)
  {
    return null;
  }

  @Override
  public Object visitZSect(ZSect zSect)
  {
	sectName_ = zSect.getName();
    List<DefinitionTable> parentTables =
      new ArrayList<DefinitionTable>(zSect.getParent().size());
    for (Parent parent : zSect.getParent()) {
      DefinitionTable parentTable =
        get(parent.getWord(), DefinitionTable.class);
      parentTables.add(parentTable);
    }
    try {
      table_ = new DefinitionTable(getSectionInfo().getDialect(), sectName_, parentTables);
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

  protected void addDefinition(ZNameList genFormals, Name declName,
		  Expr defExpr, DefinitionType type)
  {
	if (table_ == null) {
		throw new CztException(new DefinitionTable.DefinitionException(getSectionInfo().getDialect(), "Invalid table; not yet loaded through visitZSect"));
	}
    String name = declName.accept(printVisitor_);
    DefinitionTable.Definition def =
      new DefinitionTable.Definition(sectName_, genFormals, defExpr, type);
    try {
      table_.add(name, def);
    }
    catch (DefinitionTable.DefinitionException e) {
      throw new CztException(e);
    }
  }

  private static int complexInclDeclSeed = 0;
  public static final String COMPLEX_INCLDECL_NAME_PATTERN = "complexInclDecl";

  public static final Logger logger_ = Logger.getLogger(SectionManager.class.getName());

  protected static String createNewInclDeclDefName()
  {
    complexInclDeclSeed++;
    return COMPLEX_INCLDECL_NAME_PATTERN + complexInclDeclSeed;
  }

  private Name buildName(Name name, List<Stroke> strokes)
  {
    Name result = name;
    if (strokes != null && !strokes.isEmpty())
    {
      ZName zname = ZUtils.assertZName(name);
      result = ZUtils.FACTORY.createZName(zname.getWord(),
        ZUtils.FACTORY.createZStrokeList(zname.getZStrokeList()));
      ((ZName)result).getZStrokeList().addAll(strokes);
    }
    return result;
  }

  private void addComplexRefExprInfo(ZNameList genFormals, Expr expr, List<Stroke> strokes)
  {
    Name complexName = ZUtils.FACTORY.createZName(createNewInclDeclDefName());
    Name bcomplexName = buildName(complexName, strokes);
    //logger_.warning("Found a complex (schema) inclusion expression and could not calculate " +
    //  "definition table for inner element names. Adding it as schema " +
    //  "inclusion that is not a reference name. Adding it with name " + bcomplexName
    //  + " as INCLDECL. Other tools might want to try and process it further.");
    logger_.log(Level.WARNING, "DEFTBL-VISITOR-COMPLEX-SCHEMA-INCL = {0}", bcomplexName);
    addDefinition(genFormals, bcomplexName, expr, DefinitionType.INCLDECL);
  }

  protected void processRefExpr(ZNameList genFormals, RefExpr refExpr, List<Stroke> strokes)
  {
	if (table_ == null) {
		throw new CztException(new DefinitionTable.DefinitionException(getSectionInfo().getDialect(), "Invalid table; not yet loaded through visitZSect"));
	}
    // this name may contain strokes already
    Name name = refExpr.getName();
    String strName = name.accept(printVisitor_);
    DefinitionTable.Definition def = table_.lookup(strName);

    // if we know about this name's definition information and it
    // has the right "shape" (i.e., CONSTDECL schema expression name)
    if (def != null &&
        def.getDefinitionType().equals(DefinitionType.CONSTDECL) &&
        def.getExpr() instanceof SchExpr)
    {
      SchExpr schExpr = (SchExpr)def.getExpr();

      // with the same generic formals, add each declaration within this trivial INCLDECL
      processDeclList(genFormals, schExpr.getZSchText().getZDeclList(), strokes);
    }
    else
    {
      Name bname = buildName(name, strokes);
      //logger_.info("Found a reference to a complex (schema) expression inclusion found while building definition table. " +
      //  "These are usually Delta, Xi, or simple decorated schema inclusion expressions. Added " + bname +
      //  " as INCLDECL. Other tools might want to try and process it further.");
      logger_.log(Level.WARNING, "DEFTBL-VISITOR-DELTAXI-SCHEMA-INCL = {0}", bname);
      addDefinition(genFormals, bname, refExpr, DefinitionType.INCLDECL);
    }
  }

  protected void processDeclList(ZNameList genFormals, List<Decl> decls, List<Stroke> strokes)
  {
    for (Decl decl : decls)
    {
      if (decl instanceof ConstDecl)
      {
        ConstDecl constDecl = (ConstDecl) decl;
        Name name = buildName(constDecl.getName(), strokes);
        addDefinition(genFormals, name, constDecl.getExpr(), DefinitionType.CONSTDECL);

        // for schema expression definitions, add internal elements from declarations
        // these could be either direct VarDecls on top-level schemas, or inclusions.
        if (constDecl.getExpr() instanceof SchExpr)
        {
          SchExpr schExpr = (SchExpr)constDecl.getExpr();
          // no strokes to be added
          processDeclList(genFormals, schExpr.getZSchText().getZDeclList(), strokes);
        }
      }
      else if (decl instanceof VarDecl)
      {
        VarDecl varDecl = (VarDecl) decl;
        Expr defExpr = varDecl.getExpr();
        for(Name name : varDecl.getZNameList())
        {
          Name bname = buildName(name, strokes);
          addDefinition(genFormals, bname, defExpr, DefinitionType.VARDECL);
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

        // THIS GOES SOMEWHERE ELSE??
        InclDecl inclDecl = (InclDecl) decl;
        Expr expr = inclDecl.getExpr();

        // if it is a reference inclusion, then it is easy
        if (expr instanceof RefExpr)
        {
          RefExpr refExpr = (RefExpr) expr;
          processRefExpr(genFormals, refExpr, strokes);
        }
        // for decorated inclusions, add the stroked version of possible names
        else if (expr instanceof DecorExpr)
        {
          // get any previous strokes to consider
          DecorExpr dexpr = (DecorExpr)expr;
          boolean added = strokes.add(dexpr.getStroke());
          // for simple decorated expressions (i.e., S~'?, but not (S \land T)~')
          if (dexpr.getExpr() instanceof RefExpr)
          {
            RefExpr refExpr = (RefExpr)dexpr.getExpr();
            processRefExpr(genFormals, refExpr, strokes);
            if (added)
            {
              // remove last one if added
              strokes.remove(strokes.size()-1);
            }
          }
          else
          {
            addComplexRefExprInfo(genFormals, dexpr.getExpr(), strokes);
          }
        }
        // otherwise, we would need a dual-phase visiting.
        // e.g., (S \land T), go through S and T ?
        else
        {
          addComplexRefExprInfo(genFormals, expr, strokes);
        }
      }
    }
  }
}

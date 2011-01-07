/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 *
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.util;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Stack;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.parser.util.AbstractVisitor;
import net.sourceforge.czt.parser.util.CztErrorList;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.UnknownCommandException;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.CondExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LambdaExpr;
import net.sourceforge.czt.z.ast.LetExpr;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.MuExpr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.PreExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZBranchList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.ParaVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.z.visitor.BranchVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.ZBranchListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;
import net.sourceforge.czt.z.util.ZString;

/**
 * A visitor that computes a {@link DefinitionTable} from a given
 * Z Section.
 *
 * @author Leo Freitas
 */
public class DefinitionTableVisitor
  extends AbstractVisitor<DefinitionTable>
  implements TermVisitor<DefinitionTable>,
             GivenParaVisitor<DefinitionTable>,
             FreeParaVisitor<DefinitionTable>,
             ZFreetypeListVisitor<DefinitionTable>,
             FreetypeVisitor<DefinitionTable>,
             ZBranchListVisitor<DefinitionTable>,
             BranchVisitor<DefinitionTable>,
             AxParaVisitor<DefinitionTable>,
             ParaVisitor<DefinitionTable>,
             ZParaListVisitor<DefinitionTable>,
             ZSectVisitor<DefinitionTable>
{
  private DefinitionTable table_;
  private final ZName freeTypeCtorOpName_;

  private SectTypeEnvAnn types_;
  
  /** The name of the section whose paragraphs are being processed. */
  private String sectName_;

  /** Current name being processed for nested definitions, like FreeTypes and schemas */
  private Stack<ZName> currentName_;

  private Definition currentGlobalDef_;

  private final Factory factory_;
  private final UnificationEnv typeUniEnv_;

  public DefinitionTableVisitor(SectionInfo sectInfo)
  {
    this(sectInfo, ZUtils.FACTORY);
  }

  /**
   * Creates a new definition table visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.DefinitionTable.class</code>.
   * @param sectInfo
   * @param factory
   */
  public DefinitionTableVisitor(SectionInfo sectInfo, Factory factory)
  {
    super(sectInfo);
    sectName_ = null;
    currentGlobalDef_ = null;
    types_ = null;
    factory_ = factory;
    typeUniEnv_ = new UnificationEnv();
    freeTypeCtorOpName_ = factory_.createZName(ZString.ARG_TOK+ZString.INJ+ZString.ARG_TOK);
    currentName_ = new Stack<ZName>();
  }

  @Override
  public DefinitionTable run(Term term)
    throws CommandException
  {
    super.run(term);
    if (errors_.isEmpty())
      return getDefinitionTable();
    else
      throw new DefinitionException(
              "Exceptions raise whilst calculating DefTable for " + sectName_, errors_);
  }

  protected DefinitionTable getDefinitionTable()
  {
    return table_;
  }

  protected SectTypeEnvAnn getTypes()
  {
    return types_;
  }

  @Override
  public DefinitionTable visitTerm(Term term)
  {
    final String message = "DefinitionTables can only be build for ZSects; " +
      "was tried for " + term.getClass();
    throw new CztException(new DefinitionException(message,
            new UnsupportedOperationException()));
  }

  @Override
  public DefinitionTable visitZParaList(ZParaList list)
  {
    for (Para p : list) visit(p);
    return null;
  }


  /** Schema or generic schema definition (vertical).
   *      AxPara.Box          = SchBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = ConstDecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = SchemaName
   *      ConstDecl.expr      = SchExpr
   *
   * Axiomatic or generic definitions
   *      AxPara.Box          = AxBox
   *      AxPara.decl         = generics
   *
   *      AxPara.SchText.decl = declared variables
   *      AxPara.SchText.pred = axiomatic predicate
   *
   * Horizontal definition
   *      AxPara.Box          = OmitBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = Constdecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = HorizDefName (either SchName or AbbrvName)
   *      ConstDecl.expr      = HorizDefExpr (either SchExpr or Other)
   * @param axPara
   */

  @Override
  public DefinitionTable visitAxPara(AxPara axPara)
  {
    // gets the generic names
    ZNameList genFormals = axPara.getZNameList();

    // gets the declarations
    ZSchText schText = axPara.getZSchText();
    List<Decl> decls = schText.getZDeclList();

    Stack<DefinitionKind> defKinds = new Stack<DefinitionKind>();
    Stack<Stroke> strokes = new Stack<Stroke>();
    DefinitionKind currentDefKind;

    switch (axPara.getBox())
    {
      // usual axiomatic boxes: 
      //    \begin{axdef}
      //    \begin{gendef}
      case AxBox:
        // usual case: VARDECL => x, y: T0; z: T1
        // possible  : CONDECL => C == T0 \cross T1 (= C: \power~(T0 \cross T1)
        // wierd     : INCDECL => S  (e.g., schema inclusion in AxDef!) [AVOID?]
        // oddities  : type-unifiable redeclarations (e.g., x: \nat; x: \num) in same axdef [AVOID?]
        currentDefKind = defKinds.push(DefinitionKind.AXIOM);
        break;
 
      // usual schema boxes:
      //    \begin{schema}{S}
      //    \begin{schema}{S}[X]
      case SchBox:
        // only possible case: CONDECL => SN == [ D | P ]
        // needs a stroke stack in case of inner declarations (IncDecl)
        currentDefKind = defKinds.push(DefinitionKind.SCHEMADECL);

        currentGlobalDef_ = null;

        break;
        
      // omit box is complicated. try to guess easy ones
      case OmitBox:
        assert ZUtils.isAxParaSchemaOrHorizDefValid(axPara);
        
        Name name = ((ConstDecl)decls.get(0)).getName();
        Expr expr = ((ConstDecl)decls.get(0)).getExpr();

        currentGlobalDef_ = null;

        currentDefKind = figureOutDefKindForOmitBoxExpr(expr);
        defKinds.push(currentDefKind);
        break;
        
      // unknown box
      default:
        currentDefKind = defKinds.push(DefinitionKind.UNKNOWN);
        break;
    }
    assert !defKinds.empty();

    if (currentDefKind.equals(DefinitionKind.UNKNOWN))
    {
      raiseUnsupportedCase("unknown kind of AxPara", currentDefKind, axPara);
    }


    // (possibly recursively) process declarations accordingly
    processDeclList(genFormals, decls, defKinds, strokes);

    assert !defKinds.empty() : "empty definition stack";
    DefinitionKind old = defKinds.pop();
    assert old.equals(currentDefKind) : "definition stack consistency: expected " + currentDefKind + " found " + old; // or .value() euqlas for SCHBINDING?

    // cannot foresee this case, but deal with it anyway
    if (!defKinds.empty())
    {
      raiseUnsupportedCase("decl processing (stack) error", defKinds.peek(), axPara);
    }

    currentGlobalDef_ = null;
    return null;
  }

  @Override
  public DefinitionTable visitPara(Para para)
  {
    return null;
  }

  @Override
  public DefinitionTable visitGivenPara(GivenPara para)
  {
    // doesn't work for name jokers!
    for(Name given : para.getZNameList())
    {
      // for all names, create a definition as:
      // ZN("N") -> Def({}, Power(Ref("N")), GIVENSET)
      if (given instanceof ZName)
      {
        ZName givenName = (ZName)given;
        addGlobalDefinition(factory_.createZNameList(),
                      givenName,
                      factory_.createPowerExpr(
                        factory_.createRefExpr(givenName)),
                      DefinitionKind.GIVENSET);
      }
    }
    return null;
  }

  @Override
  public DefinitionTable visitFreePara(FreePara para)
  {
    visit(para.getFreetypeList());
    return null;
  }

  @Override
  public DefinitionTable visitZFreetypeList(ZFreetypeList term)
  {
    for(Freetype ft : term) visit(ft);
    return null;
  }
  
  @Override
  public DefinitionTable visitFreetype(Freetype term)
  {
    ZName ftName = term.getZName();
    currentName_.push(ftName);

    currentGlobalDef_ = addGlobalDefinition(factory_.createZNameList(),
       ftName, factory_.createPowerExpr(factory_.createRefExpr(ftName)),
       DefinitionKind.GIVENSET);

    visit(term.getBranchList());

    

    assert !currentName_.empty();
    ZName old = currentName_.pop();
    assert old.equals(ftName);

    currentGlobalDef_ = null;
    return null;
  }

  @Override
  public DefinitionTable visitZBranchList(ZBranchList term)
  {
    for(Branch ftb : term) visit(ftb);
    return null;
  }

  @Override
  public DefinitionTable visitBranch(Branch term)
  {
    assert !currentName_.empty() : "Unknown free type name for branch " + term;
    assert currentGlobalDef_ != null : "Unknown free type global def";

    ZName ftName = currentName_.peek();
    ZName ftElem = term.getZName();
    Expr ftExpr = null;
    RefExpr freeType = factory_.createRefExpr(ftName); // currentName_="FT"
    
    // free type constant
    // FT ::= a | b definition as:
    // ZN("a") --> Def({}, Power(Given(FT)), FREETYPE)
    if (term.getExpr() == null)
    {
      ftExpr = factory_.createPowerExpr(freeType); // Power(Ref(FT))
    }
    // free type constructor
    // FT ::= c < E > | ... definition as:
    // ZN("c") --> Def({}, E >-> FT, FREETYPE)
    //
    else
    {
      // E \inj FT
      ftExpr = factory_.createGenOpApp(freeTypeCtorOpName_,
              factory_.list(term.getExpr(), freeType));
    }
    addLocalDefinition(factory_.createZNameList(), ftElem, ftExpr, DefinitionKind.FREETYPE);
    return null;
  }

  @Override
  public DefinitionTable visitZSect(ZSect zSect)
  {
	  sectName_ = zSect.getName();
    // collect information from parents - accumulate errors rather than raise then
    List<DefinitionTable> parentTables =
      new ArrayList<DefinitionTable>();
    for (Parent parent : zSect.getParent()) 
    {
      try
      {
        DefinitionTable parentTable = get(parent.getWord(), DefinitionTable.class);
        parentTables.add(parentTable);
      }
      catch(CztException ex)
      {
        Throwable cause = ex.getCause();
        if (cause instanceof DefinitionException)
        {
          raiseUnsupportedCase("parent raised errors", null, parent);
          errors_.addAll(((DefinitionException)cause).getExceptions());

          // Should we add erroneous parent? NO?
          //parentTable = get(parent.getWord(), DefinitionTable.class); // try again. NO.
          //parentTables.add(parentTable);
        }
      }
    }
    // attempt to create a table for this section
    // throws exception in case of duplicates from parents
    try {
      table_ = new DefinitionTable(sectName_, parentTables);
    }
    catch (DefinitionException exception)
    {
      throw new CztException(exception);
    }

    // attempt to get type information from parents and this section
    // (E.g., only ask for DefTable of well typed terms).
    // this is important to be able to calculate inclusions properly
    try
    {
      types_ = get(sectName_, SectTypeEnvAnn.class);
    }
    catch (CztException e)
    {
      // get above is a CztE wrapping a cmd expt
      Throwable cause = e.getCause();

      // if we fail, raise a warning about ill-typed section if a cmd expt
      if (cause instanceof CommandException)
      {
        // if cause is cmd exception and its cause a CztErrorList, then it's a type/parse error
        if (cause.getCause() instanceof CztErrorList/*TypeErrorException*/)
        {
          types_ = null;
          SectionManager.traceWarning("Type errors in " + sectName_ + " when calculating DefTable");
        }
        else if (cause instanceof UnknownCommandException)
        {
          types_ = null;
          SectionManager.traceLog("There is no known type checker for " + sectName_);
        }
      }
      else
      // throw it otherwise
        throw e;
    }

    // visit this section to update table_
    visit(zSect.getParaList());
    sectName_ = null;
    return null;
  }

  protected void visit(Term term)
  {
    if (term != null) // ? Add this ? Yes (Leo)?
      term.accept(this);
  }

  /**
   * Test whether a list contains a reference to an object.
   * @param list the list to search.
   * @param o the reference to search for.
   * @return true if and only if the reference is in the list.
   */
  private boolean containsObject(List<?> list, Object o)
  {
    boolean result = false;
    for (Iterator<?> iter = list.iterator(); iter.hasNext(); )
    {
      Object next = iter.next();
      if (next == o)
      {
        result = true;
        break;
      }
    }
    return result;
  }

  private <T extends Term> T cloneTerm(T term)
  {
    List<Term> listTerm = new ArrayList<Term>();
    listTerm.add(term);
    return cloneTerm(term, listTerm);
  }

  private <T extends Term> T cloneTerm(T term, List<Term> listTerm)
  {
    Object[] children = term.getChildren();
    for (int i = 0; i < children.length; i++) {
      Object child = children[i];
      if (child instanceof Term &&
          ! containsObject(listTerm, child)) {
        children[i] = cloneTerm((Term) child, listTerm);
      }
    }
    @SuppressWarnings("unchecked")
    T result = (T)term.create(children);
    assert result.equals(term);
    cloneAnns(term, result);
    return result;
  }

  //copy the LocAnn and UndeclaredAnn from term1 to term2
  private void cloneAnns(Term term1, Term term2)
  {
    if (term1.getAnns() != null)
    {
      for(Object obj : term1.getAnns())
      {
        if (obj instanceof Term)
        {
          Term ann = (Term)obj;
          Term cann = cloneTerm(ann);
          term2.getAnns().add(cann);
        }
        else
        {
          term2.getAnns().add(obj);
        }
      }
    }
  }

  protected Type2 getType(Name declName)
  {
    Type2 result = null;
    if (types_ != null)
    {
      for(NameSectTypeTriple nstt : types_.getNameSectTypeTriple())
      {
        if (ZUtils.namesEqual(declName, nstt.getName()))
        {
          // unwrap generic types, if necessary
          result = typeUniEnv_.unwrapType(nstt.getType());
        }
      }
    }
    return result;
  }

  protected Definition addDefinition(ZNameList genFormals, ZName declName,
		  Expr defExpr, DefinitionKind defKind)
  {
    assert defKind != null;
    if (defKind.isGlobal())
    {
      return addGlobalDefinition(genFormals, declName, defExpr, defKind);
    }
    else
    {
      return addLocalDefinition(genFormals, declName, defExpr, defKind);
    }
  }

  protected Expr tryResolvingGenerics(ZNameList genFormals, Type2 carrierType, Expr expr)
  {
    Expr resolvedExpr = expr;
    if (carrierType != null)
    {
      // returns defExpr if it can't handle instantiation
      resolvedExpr = expr;
    }
    return resolvedExpr;
  }

  /**
   * Enforce the definition type structure for various kinds of definitions
   * @param genFormals
   * @param declName
   * @param defExpr
   * @param defKind
   * @return
   */
  protected Definition addGlobalDefinition(ZNameList genFormals, ZName declName,
		  Expr defExpr, DefinitionKind defKind)
  {
    assert sectName_ != null;
    assert defKind.isGlobal();
    Type2 unifType = getType(declName); //TODO: should this be here (on possibly built names) or at addDef calls?
    Expr resolvedExpr = defExpr;
    Definition result = new Definition(sectName_, declName, genFormals, resolvedExpr, unifType, defKind);
    try
    {
      table_.addGlobalDecl(sectName_, result);
    }
    catch (DefinitionException e)
    {
      raiseUnsupportedCase("while adding global def: " + e.getMessage(), defKind, resolvedExpr);
    }
    return result;
  }

  protected Definition addLocalDefinition(/*Definition parent,*/ ZNameList genFormals,
          ZName declName, Expr defExpr, DefinitionKind defKind)
  {
    assert currentGlobalDef_ != null;
    assert !defKind.isGlobal() : "cannot add global definition as a local def of " + currentGlobalDef_;
    Definition result = null;
    Type2 unifType = getType(declName); //TODO: should this be here (on possibly built names) or at addDef calls?
    Expr resolvedExpr = defExpr;
    try
    {
      result = currentGlobalDef_.addLocalDecl(declName, genFormals, resolvedExpr, unifType, defKind);
    }
    catch (DefinitionException e)
    {
      //raiseUnsupportedCase(e.getMessage(), defKind, resolvedExpr);
      //throw new CztException(e);
      raiseUnsupportedCase("while adding local def: " + e.getMessage(), defKind, resolvedExpr);
    }
    return result;
  }

  protected void addLocalReference(Definition local)
  {
    if (local == null)
    {
      throw new CztException(new DefinitionException("Cannot add global definition reference for null"));
    }
    assert currentGlobalDef_ != null;
    assert local != null && local.getDefinitionKind().isReference() : "cannot add global definition reference for " + local;
    // get (deep) copies of carrier type and expr
    Type2 carrierType = local.getCarrierType();
    if (carrierType != null)
    {
      carrierType = cloneTerm(carrierType);
    }
    Expr localRef = cloneTerm(local.getExpr());

    // try resolving generics
    localRef = tryResolvingGenerics(currentGlobalDef_.getGenericParams(), carrierType, localRef);
    Definition localDef = new Definition(local.getSectionName(), local.getDefName(), local.getGenericParams(), localRef, carrierType, local.getDefinitionKind());
//    Definition localDef = local;
    try
    {
      currentGlobalDef_.addLocalDecl(localDef);
    }
    catch (DefinitionException e)
    {
      //throw new CztException(e);
      raiseUnsupportedCase("while adding (cloned+gen-instantiated) local ref: " + e.getMessage(), localDef.getDefinitionKind(), localDef.getExpr());
    }
  }

  /**
   * Append to the given name the given list of strokes, if the list is not empty
   * @param name
   * @param strokes
   * @return
   */
  private ZName buildName(Name name, List<Stroke> strokes)
  {
    ZName result = ZUtils.assertZName(name);
    if (strokes != null && !strokes.isEmpty())
    {
      result = factory_.createZName(result.getWord(),
        factory_.createZStrokeList(result.getZStrokeList()));
      result.getZStrokeList().addAll(strokes);
    }
    return result;
  }

  List<DefinitionException> errors_ = new ArrayList<DefinitionException>();

  private void raiseUnsupportedCase(String message, DefinitionKind defKind, Term term)
  {
    LocAnn loc = term.getAnn(LocAnn.class);
    errors_.add(new DefinitionException(
            "DefTable could not handle Decl in " + sectName_
            + "\n\t Kind  : " + String.valueOf(defKind)
            + "\n\t Reason: " + message
            + "\n\t Loc   : " + (loc != null ? loc.toString() : "unknown")
            + "\n\t Term  : " + term.toString()));
  }

  protected DefinitionKind figureOutDefKindForOmitBoxExpr(Expr expr)
  {
    DefinitionKind result;
    ZUtils.ZExprKind exprKind = ZUtils.whatKindOfZExpr(expr);
    switch (exprKind)
    {
      case PURE:
        result = DefinitionKind.AXIOM;
        break;
      case SCHEMA:
        result = DefinitionKind.SCHEMADECL;
        break;
      case MIXED:
        if (expr instanceof CondExpr)
        {
          // IF Pred THEN E1 ELSE E2 => see if they agree
          DefinitionKind left = figureOutDefKindForOmitBoxExpr(((CondExpr)expr).getLeftExpr());
          DefinitionKind right = figureOutDefKindForOmitBoxExpr(((CondExpr)expr).getRightExpr());

          // either they agree or choose the easiest (e.g., lowest DefKind value
          if (left.equals(right) || (left.value() < right.value()))
            result = left;
          else
            result = right;
        }
        // Lambda Decl @ Expr => see Expr for adding this as AXIOM or SCHDECL
        else if (expr instanceof LambdaExpr)
          result = figureOutDefKindForOmitBoxExpr(((LambdaExpr)expr).getExpr());
        // Let X == E @ E2 => see E2
        else if (expr instanceof LetExpr)
          result = figureOutDefKindForOmitBoxExpr(((LetExpr)expr).getExpr());
        // Mu Decl @ E => see E
        else if (expr instanceof MuExpr)
          result = figureOutDefKindForOmitBoxExpr(((MuExpr)expr).getExpr());
        // A(x) => see Ref for A (recursively if A is ApplExpr itself)
        else if (expr instanceof ApplExpr)
          result = figureOutDefKindForOmitBoxExpr(ZUtils.getApplExprRef((ApplExpr)expr));
        // R => lookup table for it and find its definition, if availabe.
        else if (expr instanceof RefExpr)
        {
          RefExpr rExpr = (RefExpr)expr;
          Definition def = table_.lookupName(rExpr.getZName());
          if (def != null)
            result = figureOutDefKindForOmitBoxExpr(def.getExpr());
          else
            result = DefinitionKind.UNKNOWN;
        }
        else
          result = DefinitionKind.UNKNOWN;
        break;
      case UNKNOWN:
      default:
        // assume the worst, most complicated case.
        result = DefinitionKind.UNKNOWN;
        break;
    }
    return result;
  }

  /**
   * Add a Definition for all names within a given VarDecl. It uses any
   * generic formal parameters given and names are built taking a list of
   * Strokes into account (e.g., [delta-]schema inclusions may add them).
   * In these cases, definition names are built from the underlying VarDecl
   * names with given strokes appended. 
   *
   * @param genFormals
   * @param decl
   * @param strokes
   * @param defKind
   */
  protected void processVarDecl(VarDecl decl, ZNameList genFormals,
          List<Stroke> strokes, DefinitionKind defKind)
  {
    Expr defExpr = decl.getExpr();
    for(Name name : decl.getZNameList())
    {
      ZName bname = buildName(name, strokes);
      addDefinition(genFormals, bname, defExpr, defKind);
    }
  }

  /**
   * Add definition for the <code>decl</code> given with its underlying (power) type.
   * Unless it is a schema declaration, the type power(decl.getExpr()), otherwise it
   * would not be possible to distinguish C: P(E) and C == E in an axiom or schema Declpart
   * @param decl
   * @param genFormals
   * @param strokes
   * @param defKind
   */
  protected void processConstDecl(ConstDecl decl, ZNameList genFormals,
          List<Stroke> strokes, DefinitionKind defKind)
  {
    Expr defExpr = decl.getExpr();
    switch (defKind.value())
    {
      // odd case where ConstDecl appears in AxDef: C == E
      //    use C: Power(E). otherwise, it would not be possible to
      //    distinguish from C: E (as VarDecl)
      case DefinitionKind.AXIOM_VALUE:
      //  defExpr = factory_.createPowerExpr(decl.getExpr());
      //  break;

      // odd case where ConstDecl appears in SchDef: S == [ C == T | P ] => C: \power(T)
      case DefinitionKind.SCHEMABINDING_VALUE:
        defExpr = factory_.createPowerExpr(decl.getExpr());
        //defExpr = factory_.createPowerExpr(decl.getExpr());
        break;

      // usual case for all SchExpr: S == [ D | P ] or \begin{schema}{S} D | P \end{schema}
      //    use decl.getExpr() or PowerExpr(decl.getExpr())? LATTER
      case DefinitionKind.SCHEMADECL_VALUE:
        defExpr = decl.getExpr();
        break;

      // ConstDecl cannot appear in Schema calculus, given set, or free type
      // e.g., S == T \land R, [G], FT ::= c | f <E>
      case DefinitionKind.SCHEMAEXPR_VALUE:
      case DefinitionKind.GIVENSET_VALUE:
      case DefinitionKind.FREETYPE_VALUE:
      default:
        raiseUnsupportedCase("ill-formed ConstDecl", defKind, decl);
    }
    //defExpr = decl.getExpr();


    ZName bname = buildName(decl.getName(), strokes);
    addDefinition(genFormals, bname, defExpr, defKind);
  }

  /**
   * Processes given RefExpr as a SchExpr, if found. It also adds
   * dashed components for Delta and Xi schemas.
   *
   * @param genFormals
   * @param refExpr
   * @param strokes
   * @param defKinds
   */
  protected void processRefExpr(ZNameList genFormals, RefExpr refExpr,
          Stack<Stroke> strokes, Stack<DefinitionKind> defKinds)
  {
    assert !currentName_.empty();
    assert currentGlobalDef_ != null;

    // this name may contain strokes already - keep then.
    ZName origName = refExpr.getZName();
    
    // if it is a Delta or Xi to a (schema) name, then add dashed 
    // versions of DeclList from the base name
    ZName refName;
    boolean isSpecialRefName = ZUtils.isDeltaXi(origName);
    if (isSpecialRefName)
    {
      refName = ZUtils.getSpecialSchemaBaseName(factory_, origName);
      strokes.push(factory_.createNextStroke());
    }
    else
    {
      refName = origName;
    }

    // if (is Delta/Xi S) then refNae = (S + next stroke in stack) else (S, which may contain strokes)
    // that is: S' may be added globally for \Delta Xi case
    processRefName(genFormals, refName, strokes, defKinds);

    // we need to add the reference name as an inclusion, if needed.
    // strokes to be considered only for DecorExpr not Delta/Xi
    // e.g., if isSpecial then \Delta S else (S + strokes, if any)
    ZName strokedName = buildName(refName, strokes);
    ZName includedName = isSpecialRefName ? origName : strokedName;
    Definition includedDef = table_.lookupDeclName(includedName);
    if (isSpecialRefName && includedDef == null)
    {
      Definition state     = table_.lookupDeclName(refName);
      Definition stateDash = table_.lookupDeclName(strokedName);
      assert state != null && stateDash != null;

      // DON'T REUSE TERMS
      //
      // Delta = true
      // Xi    = \theta S = \theta S'
      Pred specialPred = ZUtils.isXi(includedName) ?
        factory_.createEquality(
          factory_.createThetaExpr(factory_.createRefExpr(refName),
              factory_.createZStrokeList()),
          factory_.createThetaExpr(factory_.createRefExpr(refName),
              factory_.createZStrokeList(factory_.list(factory_.createNextStroke())))) :
        factory_.createTruePred();
      // Delta = [ S; S' | true ]
      // Xi    = [ S; S' | \theta S = \theta S' ]
      SchExpr specialExpr = factory_.createSchExpr(
        factory_.createZSchText(factory_.createZDeclList(factory_.list(
           factory_.createInclDecl(factory_.createRefExpr(refName)),
           factory_.createInclDecl(factory_.createDecorExpr(
                  factory_.createRefExpr(refName), factory_.createNextStroke())))),
           specialPred));
      LocAnn loc = refExpr.getAnn(LocAnn.class);
      if (loc != null)
      {
        specialExpr.getAnns().add(loc);
      }
      // add it as a schema decl, so global
      includedDef = addDefinition(genFormals, includedName, specialExpr, DefinitionKind.SCHEMADECL);

      // also process its inner definitions, which should already be available as
      //processSchExpr(genFormals, includedName, specialExpr, defKinds, strokes);
      Definition topLevelDef = currentGlobalDef_;
      currentGlobalDef_ = includedDef;
      addLocalReference(state);
      addLocalReference(stateDash);
      currentGlobalDef_ = topLevelDef;
    }
    assert includedDef != null;

    // if null, there is a problem: includedDef wasn't found and isn't special! - it is raised
    // otherwise, add a reference for includedDef for current global def
    addLocalReference(includedDef);

    // pop the stroke stack accordingly, if needed
    if (isSpecialRefName)
    {
      assert !strokes.empty() : "empty stroke stack";
      Stroke old = strokes.pop();
      assert old instanceof NextStroke : "stroke stack consistency: not NextStroke";
    }
  }

  /**
   * Look the reference name to see if already properly processed, raising
   * various errors in case it has not. If the reference has a definition
   * of the right shape (e.g., SchExpr) and there are extra strokes to consider
   * (e.g., DecorExpr or \Delta S), then add those stroked version of the reference.
   * The refName ought always to be a base name (e.g., not include Delta / Xi on it).
   * @param genFormals
   * @param refName
   * @param strokes
   * @param defKinds
   */
  protected void processRefName(ZNameList genFormals, ZName refName,
          Stack<Stroke> strokes, Stack<DefinitionKind> defKinds)
  {
    assert !ZUtils.isDeltaXi(refName) : "Delta/Xi refNames are processed as InclDecl!";

    // look the name up: make sure it has been properly processed
    Definition def = table_.lookupName(refName);

    // if we find the name as a Schema declaration
    if (def != null)
    {
      Expr defExpr = def.getExpr();
      if (def.getDefinitionKind().isReference())
      {
        // process the elements for the schema expression
        if (defExpr instanceof SchExpr)
        {
          SchExpr schExpr = (SchExpr)defExpr;

          // only have work to do if the name's changed (e.g., dashed / decorated)
          // only DecorExpr or Delta/Xi inclusion push strokes.
          if (!strokes.empty())
          {
            // get the stroked definition
            ZName strokedName = buildName(refName, strokes);
            Definition strokedDef = table_.lookupName(strokedName);
            boolean needsLocalReference = strokedDef == null;
            // if already in the table, no need to process it
            // otherwise, add the stroked version of refName on top-level
            if (strokedDef == null)
            {
              // save top-level def where DecorExpr is being included from
              Definition topLevelDef = currentGlobalDef_;
              // add+process the DecorExpr as a top-level decl (e.g., add S' == [ x', y': T ] globally)
              strokedDef = addDefinition(def.getGenericParams()/*genFormals*/, strokedName, schExpr, DefinitionKind.SCHEMADECL);
              currentGlobalDef_ = strokedDef;
              processSchExpr(strokedDef.getGenericParams(), refName, schExpr, defKinds, strokes);

              // restore top-level definition
              currentGlobalDef_ = topLevelDef;
            }
            assert strokedDef != null;

            // add a reference to stroked definition
            if (needsLocalReference /*&& strokedDef != null*/)
              addLocalReference(strokedDef);
          }
          // otherwise, we are done
          //    this is the case where an RefExpr has already been properly processed

        }
        // complex reference for schema expression (e.g., should not have been added as SCHEMADECL, but SCHEMAEXPR)
        else
        {
          raiseUnsupportedCase("complex definition for schema reference", def.getDefinitionKind(), defExpr);
        }
      }
      // this method should not be called for references that are not schema declarations
      else
      {
        raiseUnsupportedCase("not a schema reference", def.getDefinitionKind(), defExpr);
      }
    }
    // couldn't find the declaration where this reference came from
    else
    {
      raiseUnsupportedCase("unknown reference", def.getDefinitionKind(), refName);
    }
  }

  protected void processInclDecl(InclDecl decl, ZNameList genFormals,
          Stack<Stroke> strokes, Stack<DefinitionKind> defKinds)
  {
    Expr inclDeclExpr = decl.getExpr();

    // usual case of reference inclusion: S == [ T; \Delta R | P ]
    if (inclDeclExpr instanceof RefExpr)
    {
      RefExpr refExpr = (RefExpr) inclDeclExpr;
      processRefExpr(genFormals, refExpr, strokes, defKinds);
    }
    // usual case of decorated inclusions: S == [ St; St~'; T_0? | P ]
    else if (inclDeclExpr instanceof DecorExpr)
    {
      DecorExpr dexpr = (DecorExpr)inclDeclExpr;
      Expr expr = dexpr.getExpr();

      // simple decorated inclusion: S == [ St~' ]
      if (expr instanceof RefExpr)
      {
        RefExpr refExpr = (RefExpr)expr;

        // get any previous strokes to consider, in case one DecorExpr
        Stroke stroke = strokes.push(dexpr.getStroke());

        // process the reference expr to see whether decorated version is needed.
        // NOTE: this means RefName+Stroke will be added as a binding for the
        //       schema this DecorExpr is being included by
        processRefName(genFormals, refExpr.getZName(), strokes, defKinds);
        
        // remove the decoration from stroke stack
        assert !strokes.empty() : "empty stroke stack";
        Stroke old = strokes.pop();
        assert stroke.equals(old) : "stack stroke consistency: wrong decor expr stroke";
      }
      else
      {
        // SchExpr = on-the-fly constructions as decorated inclusion  S == [ [ x: T ]~'    ]
        // Expr    = complex schema calculus as decoared inclusion    S == [ (T \land R)~' ]
        raiseUnsupportedCase("complex decorated inclusion", DefinitionKind.SCHEMAEXPR, decl);
      }
    }
    // somewhat unusual case: S == [ [ x: T | P ] | Q ]
    else if (inclDeclExpr instanceof SchExpr)
    {
      processDeclList(genFormals, ((SchExpr)inclDeclExpr).getZSchText().getZDeclList(), defKinds, strokes);
    }
    // somewhat usual case: S == [ St[x/y] | P ]
    else if (inclDeclExpr instanceof RenameExpr)
    {
      RenameExpr rexpr = (RenameExpr)inclDeclExpr;
      raiseUnsupportedCase("not handling rename expr in inclusion", DefinitionKind.SCHEMAEXPR, rexpr);
    }
    else
    {
      // S == [ (T \land R) | P ] => will need to use type information?
      raiseUnsupportedCase("complex schema expression inclusion", DefinitionKind.SCHEMAEXPR, decl);
    }
  }

  /**
   * Declares all the declared elements within a schema as its bindings, providing
   * expr is a SchExpr --- not yet handling complex schema expr. These are the schemas
   * defined either via boxed or horizontal environments.
   * @param genFormals
   * @param refName
   * @param expr
   * @param defKinds
   * @param strokes
   */
  protected void processSchExpr(ZNameList genFormals, ZName refName, Expr expr,
          Stack<DefinitionKind> defKinds, Stack<Stroke> strokes)
  {
    // current schema being processed considering strokes
    // keep a local reference in case recursion changes currentName_
    ZName schName = ZUtils.assertZName(buildName(refName, strokes));
    currentName_.push(schName);

    DefinitionKind currentDefKind = defKinds.peek();

    // we can process SchExpr only when handling their declaraitons
    // or their inclusions as bindings. Otherwise there is a problem?
    // NO! Could appear in AxBox... this is wierd Z (!) should be ruled out.
    //if (currentDefKind.isSchemaBinding() ||
    //    currentDefKind.equals(DefinitionKind.SCHEMADECL))

    // add the schema bindings first
    if (expr instanceof SchExpr)
    {
      SchExpr schExpr = (SchExpr)expr;

      // push inclusion kind onto the stack => these are local to the bindings
      DefinitionKind schKind = defKinds.push(DefinitionKind.getSchBinding(schName, schExpr));

      processDeclList(genFormals, schExpr.getZSchText().getZDeclList(), defKinds, strokes);

      // pop it from the stack
      assert !defKinds.empty() : "empty definition stack";
      DefinitionKind old = defKinds.pop();
      assert old.equals(schKind) : "definition stack consistency: not SCHBINDING"; // ??? or just .value() equals?
    }
    else if (expr instanceof PreExpr)
    {
      Expr prExpr = ((PreExpr)expr).getExpr();
      if (prExpr instanceof RefExpr)
      {
        processRefExpr(genFormals, (RefExpr)prExpr, strokes, defKinds);
      }
      else
      {
        raiseUnsupportedCase("complex definition for schema precondition", currentDefKind, expr);
      }
    }
//    else if (expr instanceof HideExpr)
//    {
//
//    }
//    else if (expr instanceof NegExpr)
//    {
//      ((NegExpr)expr).getExpr()
//    }
//             (term instanceof HideExpr) ||
//             (term instanceof NegExpr) ||
//             (term instanceof RenameExpr) ||
//             // Pipe, Proj, And, Or, Implies, Iff, Comp
//             (term instanceof SchExpr2) ||
//             (term instanceof ExistsExpr) ||
//             (term instanceof Exists1Expr) ||
//             (term instanceof ForallExpr))

    // complex reference for schema expression (e.g., should not have been added as SCHEMADECL, but SCHEMAEXPR)
    else
    {
      raiseUnsupportedCase("complex definition for schema reference", currentDefKind, expr);
    }

    // clear current name
    assert !currentName_.empty();
    ZName old = currentName_.pop();
    assert old.equals(schName);
  }

  /**
   * Processes the expressions within the given declaration lists, where
   * a stack of strokes is carried along in order to enable processing DecorExpr.
   * @param genFormals
   * @param decls
   * @param defKinds
   * @param strokes
   */
  protected void processDeclList(ZNameList genFormals, List<Decl> decls,
          Stack<DefinitionKind> defKinds, Stack<Stroke> strokes)
  {
    for (Decl decl : decls)
    {
      DefinitionKind currentDefKind = defKinds.peek();
      
      switch (currentDefKind.value())
      {
        // Declarations coming from an Axiomatic box (AxBox only)
        case DefinitionKind.AXIOM_VALUE:
          assert currentDefKind.equals(DefinitionKind.AXIOM);
          
          // usual: x, y: T; z: T2
          if (decl instanceof VarDecl)
          {
            processVarDecl((VarDecl)decl, genFormals, strokes, currentDefKind);
          }
          // odd Ax case: C == E  in an axiomatic box [I find it wierd / unnecessary]
          else if (decl instanceof ConstDecl)
          {
            processConstDecl((ConstDecl)decl, genFormals, strokes, currentDefKind);
          }
          // odd Ax case: inclusion in axiomatic box (!)
          else if (decl instanceof InclDecl)
          {
            // inclusions are taken as global
            //processInclDecl((InclDecl)decl, genFormals, strokes, defKinds);
            raiseUnsupportedCase("TODO: schema inclusion in axiomatic definition", currentDefKind, decl);
          }
          break;

        // Declarations coming from a Schema box (SchBox only)
        case DefinitionKind.SCHEMADECL_VALUE:
          assert currentDefKind.equals(DefinitionKind.SCHEMADECL);

          // MUST BE ConstDecl = Z Std conformance
          if (decl instanceof ConstDecl)
          {
            ConstDecl cDecl = (ConstDecl)decl;

            // add the schema definition itself after processing its bindings
            currentGlobalDef_ = addGlobalDefinition(genFormals, cDecl.getZName(), cDecl.getExpr(), currentDefKind);

            // process the SchExpr - don't add it as INCLUSION within processSchExpr,  but below
            processSchExpr(genFormals, cDecl.getZName(), cDecl.getExpr(), defKinds, strokes);

            currentGlobalDef_ = null;
          }
          else
          {
            // non-std schema
            raiseUnsupportedCase("unknown schema declaration", currentDefKind, decl);
          }
          break;

        // Declarations coming from within schemas
        case DefinitionKind.SCHEMABINDING_VALUE:
          assert DefinitionKind.SCHEMABINDING_VALUE == currentDefKind.value();

          // usual VarDecl within Schemas  : S == [ x, y: T1; z: T0 | P ]
          if (decl instanceof VarDecl)
          {
            processVarDecl((VarDecl)decl, genFormals, strokes, currentDefKind);
          }
          // wierd ConstDecl within Schemas: S == [ C == T;      x, y: T | P ]
          // (e.g., it is just the same as   S == [ C: \power~T; x, y: T | P ] )
          else if (decl instanceof ConstDecl)
          {
            processConstDecl((ConstDecl)decl, genFormals, strokes, currentDefKind);
          }
          // usual (yet complex) case : S == [ \Delta St | P ] or something more complicated for Decl
          else if (decl instanceof InclDecl)
          {
            processInclDecl((InclDecl)decl, genFormals, strokes, defKinds);
          }
          break;

        case DefinitionKind.SCHEMAEXPR_VALUE:
          raiseUnsupportedCase("complex schema expression", currentDefKind, decl);
          break;
          
        // cannot handle given sets of free type decl from an AxBox DeclList
        case DefinitionKind.GIVENSET_VALUE:
        case DefinitionKind.FREETYPE_VALUE:
        default:
          raiseUnsupportedCase("invalid AxPara decl list", currentDefKind, decl);
      }
    }
  }
}

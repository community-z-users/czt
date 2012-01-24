/*
  Copyright (C) 2004, 2005, 2006, 2007 Petra Malik
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

package net.sourceforge.czt.print.z;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.util.TokenImpl;
import net.sourceforge.czt.z.util.WarningManager;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.Fixity;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * <p>This visitor transforms an AST into a print tree, that is an AST
 * prepared for printing.</p>
 *
 * <p>In order to print, precedences and associativity of operators
 * needs to be known.  This information is provided by an SectInfo
 * object.</p>
 *
 * <p>Note that fixed precedences and associativities are defined
 * in the Z standard in Table 31; user defined precedences and
 * associativities are obtained from an operator table.  This
 * implies that this visitor cannot be used for an arbitrary term,
 * like an expression, without providing the operator table as well.</p>
 *
 * <p>The recommended way to use this visitor is via the #run(ZSect)
 * or #run(Spec) methods.  In this case, the operator table is
 * obtained from the SectInfo object (provided in the constructor of
 * this class) as soon as the name of the current section to be
 * visited becomes available (which happens when visiting a
 * ZSect).</p>
 *
 * <p>It is also possible to provide an operator table explicitly via
 * the #run(Term, OpTable) method.  This method enables the handling
 * of arbitrary terms where the name of the section is not apparent.
 * Note that this explicity provided operator table is discarded when
 * a ZSect is visited.  As soon as a ZSect is visited, the SectInfo
 * object is consulted to provide an operator table for the given
 * section and this operator table is used instead of the explicitly
 * provided one (even if the new one is <code>null</code>).</p>
 *
 * <p>It is not recommended to call the accept method of a term to use
 * this visitor since it is not guaranteed that the correct operator
 * table is used.</p>
 *
 * @author Petra Malik
 */
public class AstToPrintTreeVisitor
  implements TermVisitor<Term>,
             AndPredVisitor<Term>,
             ApplExprVisitor<Term>,
             AxParaVisitor<Term>,
             MemPredVisitor<Term>,
             RefExprVisitor<Term>,
             ZSectVisitor<Term>
{
  private ZFactory factory_ = new ZFactoryImpl();
  private PrintFactory printFactory_ = new PrintFactory();
  
  protected ZFactory getZFactory() {
      return factory_;
  }
  
  protected PrintFactory getZPrintFactory() {
      return printFactory_;
  }  
  
  private boolean oldZ_ = false;

  /**
   * The operator table of the current section.  It is
   * used to lookup precedence and associativity of user
   * defined operators.
   */
  private OpTable opTable_;

  private PrecedenceVisitor prec_;

  /**
   * Provides the operator table for sections.
   */
  private SectionInfo sectInfo_;
  
  protected final WarningManager warningManager_;

  protected boolean withinAxPara_ = false;

  public AstToPrintTreeVisitor(SectionInfo sectInfo) {
      this(sectInfo, new WarningManager(AstToPrintTreeVisitor.class));
  }
  
  /**
   * Creates a new ast to print tree visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   * @param sectInfo
   * @param wm
   */
  public AstToPrintTreeVisitor(SectionInfo sectInfo, WarningManager wm)
  {
    sectInfo_ = sectInfo;
    warningManager_ = wm;
  }

  public Term run(String sectionName)
    throws CommandException
  {
    warningManager_.setCurrentSectName(sectionName);
    ZSect zSect = sectInfo_.get(new Key<ZSect>(sectionName, ZSect.class));
    return zSect.accept(this);
  }

  /**
   * <p>Visits a term and transforms it into a printable tree.  The given
   * operator table is used to lookup precedence and associativity
   * of user defined operators, but only if the name of the section
   * is not apparent from the term.</p>
   * <p>For instance, the given operator table is used if the given
   * term is an expression, predicate, or paragraph, but not if the
   * given term is a Z section or specification.</p>
   * @param term
   * @param opTable
   * @return
   */
  public Term run(Term term, OpTable opTable)
  {
    if (opTable != null) {
      warningManager_.setCurrentSectName(opTable.getSectionName());
      opTable_ = opTable;
      prec_ = new PrecedenceVisitor(opTable_);
    }
    return term.accept(this);
  }

  /**
   * <p>Visits a term and transforms it into a printable tree.  The given
   * section name is used to lookup precedence and associativity
   * of user defined operators, but only if the name of the section
   * is not apparent from the term itself.</p>
   * <p>For instance, the given section name is used if the given
   * term is an expression, predicate, or paragraph, but not if the
   * given term is a Z section or specification.</p>
   * @param term
   * @param sectionName
   * @return
   * @throws CommandException
   */
  public Term run(Term term, String sectionName)
    throws CommandException
  {
    if (sectionName != null) {
      warningManager_.setCurrentSectName(sectionName);
      opTable_ = sectInfo_.get(new Key<OpTable>(sectionName, OpTable.class));
      prec_ = new PrecedenceVisitor(opTable_);
    }
    return term.accept(this);
  }

  public void setOldZ(boolean value)
  {
    oldZ_ = value;
  }

  /**
   * Visits all children of a term.  If at least one of the children
   * has changed during that visit, a new term of the same class is
   * created that contains the new children.  A child that has not
   * changed is shared between the new and the old AST.
   * @param term
   */
  @Override
  public Term visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  @Override
  public Term visitAndPred(AndPred andPred)
  {
    List<Object> list = new LinkedList<Object>();
    visitAndPred(andPred, list);
    final Precedence prec = getPrec(andPred);
    PrintPredicate result =
      printFactory_.createPrintPredicate(list, prec, null);
    if (andPred.getAnn(ParenAnn.class) != null) {
      result.getAnns().add(factory_.createParenAnn());
    }
    return result;
  }

  private void visitAndPredChild(Pred pred, boolean wedge, List<Object> list)
  {
    if (wedge &&
        pred instanceof AndPred &&
        And.Wedge.equals(((AndPred) pred).getAnd()) &&
        pred.getAnn(ParenAnn.class) == null) {
      visitAndPred((AndPred) pred, list);
    }
    else if (! wedge &&
             pred instanceof AndPred &&
             (And.NL.equals(((AndPred) pred).getAnd()) ||
              And.Semi.equals(((AndPred) pred).getAnd())) &&
             pred.getAnn(ParenAnn.class) == null) {
      visitAndPred((AndPred) pred, list);
    }
    else {
      preprocessTerm(pred, list);
      list.add(visit(pred));
    }
  }

  private void visitAndPred(AndPred andPred, List<Object> list)
  {
    if (And.Wedge.equals(andPred.getAnd())) {
      visitAndPredChild(andPred.getLeftPred(), true, list);
      list.add(ZKeyword.AND);
      visitAndPredChild(andPred.getRightPred(), true, list);
    }
    else if (And.Chain.equals(andPred.getAnd())) {
      PrintPredicate pred1 = (PrintPredicate) visit(andPred.getLeftPred());
      PrintPredicate pred2 = (PrintPredicate) visit(andPred.getRightPred());
      Object[] array1 = pred1.getChildren();
      Object[] array2 = pred2.getChildren();
      if (! array1[array1.length - 1].equals(array2[0])) {
        String message = "Unexpected Op == 'Chain' within AndPred.";
        throw new CannotPrintAstException(message);
      }
      for (int i = 0; i < array1.length; i++) {
        list.add(array1[i]);
      }
      for (int i = 1; i < array2.length; i++) {
        list.add(array2[i]);
      }
      array1 = null;
      array2 = null;
    }
    else if (And.NL.equals(andPred.getAnd())) {
      visitAndPredChild(andPred.getLeftPred(), false, list);
      list.add(ZToken.NL);
      visitAndPredChild(andPred.getRightPred(), false, list);
    }
    else if (And.Semi.equals(andPred.getAnd())) {
      visitAndPredChild(andPred.getLeftPred(), false, list);
      list.add(ZKeyword.SEMICOLON);
      visitAndPredChild(andPred.getRightPred(), false, list);
    }
    else {
      throw new CztException("Unexpected Op");
    }
  }

  /**
   * Transforms each function application (an application expression
   * with Mixfix set to <code>true</code>) into an
   * OperatorApplication, and each application (an application
   * expression with Mixfix set to <code>false</code>) into an
   * Application.
   */
  @Override
  public Term visitApplExpr(ApplExpr applExpr)
  {
    final boolean isFunctionApplication =
      applExpr.getMixfix().booleanValue();
    if (isFunctionApplication && applExpr.getLeftExpr() instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
      OperatorName opName = refExpr.getZName().getOperatorName();
      Expr args = (Expr) visit(applExpr.getRightExpr());
      List argList = new LinkedList();
      if (opName.isUnary()) {
        argList.add(args);
      }
      else {
        TupleExpr tuple = (TupleExpr) args;
        argList.addAll(tuple.getZExprList());
      }
      final Precedence precedence = getPrec(applExpr);
      OperatorApplication result =
        createOperatorApplication(opName, argList, precedence);
      result.getAnns().addAll(applExpr.getAnns());
      return result;
    }
    final Expr leftExpr = (Expr) visit(applExpr.getLeftExpr());
    final Expr rightExpr = (Expr) visit(applExpr.getRightExpr());
    Application appl = printFactory_.createApplication();
    appl.setLeftExpr(leftExpr);
    appl.setRightExpr(rightExpr);
    appl.getAnns().addAll(applExpr.getAnns());
    return appl;
  }

  protected PrintParagraph handleOldZ(List<Object> anns, PrintParagraph pp)
  {
    List newAnns = pp.getAnns();
    if (oldZ_) {
      for (Object o : anns) {
        if (o instanceof AxPara) {
          System.err.println("Add annotation to " + pp);
          newAnns.add(visitAxPara((AxPara) o));
        }
      }
    }
    return pp;
  }

  /**
   * Called for schema boxes right after the schema tagging. That is
   * after "SCH NAME NL" or with generic parameters. That is just before
   * the ZDeclList. This is where Z state and refinement information live.
   * @param term
   * @param list
   */
  protected void preprocessSchema(AxPara term, List<Object> list)
  {
    if (!term.getBox().equals(Box.SchBox))
      throw new PrintException("preprocessing ability for SchBox AxPara only; " + term.getClass().getName());

    // Object: actually Token or Term
    if (term.hasAnn(ZStateAnn.class))
    {
      ZStateAnn sti = term.getAnn(ZStateAnn.class);
      //if (!sti.equals(ZStateInfo.NONE))
      //  list.add(0, ZToken.NL);
      switch (sti.getInfo())
      {
        case STATE:
          list.add(ZToken.ZSTATE);
          break;
        case STINIT:
          list.add(ZToken.ZSTINIT);
          break;
        case STFIN:
          list.add(ZToken.ZSTFIN);
          break;
        case ASTINIT:
          list.add(ZToken.ZASTINIT);
          break;
        case ASTATE:
          list.add(ZToken.ZASTATE);
          break;
        case ASTFIN:
          list.add(ZToken.ZASTFIN);
          break;
        case CSTINIT:
          list.add(ZToken.ZCSTINIT);
          break;
        case CSTATE:
          list.add(ZToken.ZCSTATE);
          break;
        case CSTFIN:
          list.add(ZToken.ZCSTFIN);
          break;
        case RETRIEVE:
          list.add(ZToken.ZRETRIEVE);
          break;
        case RETRIEVEIN:
          list.add(ZToken.ZRETRIEVEIN);
          break;
        case RETRIEVEOUT:
          list.add(ZToken.ZRETRIEVEOUT);
          break;
        case AINITIN:
          list.add(ZToken.ZAINITIN);
          break;
        case AFINOUT:
          list.add(ZToken.ZAFINOUT);
          break;
        case CINITIN:
          list.add(ZToken.ZCINITIN);
          break;
        case CFINOUT:
          list.add(ZToken.ZCFINOUT);
          break;
      }
      // add a NL after then
      list.add(ZToken.NL);
    }
    if (term.hasAnn(ZRefinesAnn.class))
    {
      ZRefinesAnn zr = term.getAnn(ZRefinesAnn.class);
      switch (zr.getRefKind())
      {
        case FORWARD:
          list.add(ZToken.ZFSREFINES);
          break;
        case BACKWARD:
          list.add(ZToken.ZBSREFINES);
          break;
        default:
          throw new AssertionError();
      }
      list.add(visit(zr.getAbstractName()));
      list.add(ZToken.NL);
    }
  }

  /**
   * Called right after the main Z token found. For instance, for Para, that is
   * either ZED, SCH, or GENSCH. If it is a Pred, then this is the first (left-most)
   * in a chain of reasoning, like in an "AndPred"
   * @param term
   * @param list
   */
  protected void preprocessTerm(Term term, List<Object> list)
  {
    //assert term instanceof AxPara || term instanceof Pred;
    if (!(term instanceof AxPara) && !(term instanceof Pred))
      throw new PrintException("preprocessing ability for AxPara and Pred only; " + term.getClass().getName());
  }

  @SuppressWarnings("unchecked")
  @Override
  public Term visitAxPara(AxPara axPara)
  {
    List<Object> list = new LinkedList<Object>();
    withinAxPara_ = true;
    PrintParagraph result = null;
    Box box = axPara.getBox();
    if (box == null || Box.AxBox.equals(box)) {
      if (! isGeneric(axPara)) {
        list.add(ZToken.AX);
      }
      else {
        list.add(ZToken.GENAX);
        list.add(ZToken.LSQUARE);
        boolean first = true;
        for (Name declName : axPara.getName()) {
          if (first) first = false;
          else list.add(ZKeyword.COMMA);
          list.add(visit(declName));
        }
        list.add(ZToken.RSQUARE);
        list.add(ZToken.NL);
      }
      ZSchText schText = axPara.getZSchText();
      for (Iterator<Decl> iter = schText.getZDeclList().iterator();
           iter.hasNext();) {
        list.add(visit(iter.next()));
        if (iter.hasNext()) list.add(ZToken.NL);
      }
      if (schText.getPred() != null) {
        list.add(new TokenImpl(ZToken.DECORWORD, new WhereWord()));
        list.add(visit(schText.getPred()));
      }
      list.add(ZToken.END);
    }
    else if (Box.OmitBox.equals(box)) {
      list.add(ZToken.ZED);
      preprocessTerm(axPara, list);
      final List<Name> declNameList = axPara.getName();
      final SchText schText = axPara.getSchText();
      final List<Decl> decls = axPara.getZSchText().getZDeclList();
      for (Decl decl : decls) {
        final ConstDecl constDecl = (ConstDecl) decl;
        final ZName declName = constDecl.getZName();
        final OperatorName operatorName = declName.getOperatorName();
        final OpTable.OpInfo opInfo = operatorName == null ? null :
          opTable_.lookup(operatorName);
        if (opInfo != null && Cat.Generic.equals(opInfo.getCat())) {
          // generic operator definition
          list.addAll(printOperator(operatorName, declNameList));
          list.add(ZKeyword.DEFEQUAL);
          list.add(visit(constDecl.getExpr()));
        }
        else { // (generic) horizontal definition
          list.add(visit(declName));
          if (declNameList.size() > 0) {
            list.add(ZToken.LSQUARE);
            for (Iterator<Name> iter = declNameList.iterator();
                 iter.hasNext();) {
              list.add(visit(iter.next()));
              if (iter.hasNext()) list.add(ZKeyword.COMMA);
            }
            list.add(ZToken.RSQUARE);
          }
          final Expr expr = constDecl.getExpr();
          final TypeAnn typeAnn = expr.getAnn(TypeAnn.class);
          Token token = ZKeyword.DEFEQUAL;
          if (typeAnn != null) {
            Type type = typeAnn.getType();
            if (type instanceof PowerType) {
              PowerType powerType = (PowerType) type;
              if (powerType.getType() instanceof SchemaType) {
                token = new TokenImpl(ZToken.DECORWORD, new DefsWord());
              }
            }
          }
          list.add(token);
          list.add(visit(expr));
        }
      }
      list.add(ZToken.END);
    }
    else if (Box.SchBox.equals(box)) {
      result = handleOldZ(axPara.getAnns(), handleSchemaDefinition(axPara));
    }
    else {
      withinAxPara_ = false;
      throw new CztException("Unexpected Box " + box);
    }
    withinAxPara_ = false;
    if (result == null)
      result = printFactory_.createPrintParagraph(list);
    return handleOldZ(axPara.getAnns(), result);
  }

  private PrintParagraph handleSchemaDefinition(AxPara axPara)
  {
    List list = new LinkedList();
    assert Box.SchBox.equals(axPara.getBox());
    if (isGeneric(axPara)) {
      list.add(ZToken.GENSCH);
    }
    else {
      list.add(ZToken.SCH);
    }
    preprocessTerm(axPara, list);
    List<Decl> decls = axPara.getZSchText().getZDeclList();
    ConstDecl cdecl = (ConstDecl) decls.get(0);
    String declName = cdecl.getZName().getWord();
    if (declName == null) throw new CztException();
    list.add(declName);
    if (isGeneric(axPara)) {
      list.add(ZToken.LSQUARE);
      for (Iterator<Name> iter = axPara.getName().iterator();
           iter.hasNext();) {
        list.add(visit(iter.next()));
        if (iter.hasNext()) list.add(ZKeyword.COMMA);
      }
      list.add(ZToken.RSQUARE);
    }
    list.add(ZToken.NL);
    preprocessSchema(axPara, list);
    SchExpr schExpr = (SchExpr) cdecl.getExpr();
    ZSchText schText = schExpr.getZSchText();
    for (Iterator<Decl> iter = schText.getZDeclList().iterator();
         iter.hasNext();) {
      list.add(visit(iter.next()));
      if (iter.hasNext()) list.add(ZToken.NL);
    }
    if (schText.getPred() != null) {
      list.add(new TokenImpl(ZToken.DECORWORD, new WhereWord()));
      list.add(visit(schText.getPred()));
    }
    list.add(ZToken.END);
    return printFactory_.createPrintParagraph(list);
  }

  /**
   * Returns whether an axiomatic paragraph is generic, i.e.
   * whether it contains formal parameters.
   */
  private boolean isGeneric(AxPara axPara)
  {
    return ! axPara.getName().isEmpty();
  }

  @Override
  public Term visitMemPred(MemPred memPred)
  {
    final Precedence precedence = getPrec(memPred);
    Expr firstExpr = (Expr) visit(memPred.getLeftExpr());
    Expr secondExpr = (Expr) visit(memPred.getRightExpr());
    boolean mixfix = memPred.getMixfix().booleanValue();
    boolean isEquality = mixfix && secondExpr instanceof SetExpr;
    if (isEquality) {
      SetExpr setExpr = (SetExpr) secondExpr;
      if (setExpr.getZExprList().size() != 1) {
        String message = "Unexpected Mixfix == true.";
        throw new CannotPrintAstException(message);
      }
      List list = new LinkedList();
      list.add(firstExpr);
      list.add(ZKeyword.EQUALS);
      list.add(setExpr.getZExprList().get(0));
      PrintPredicate result =
        printFactory_.createPrintPredicate(list, precedence, null);
      if (memPred.getAnn(ParenAnn.class) != null) {
        result.getAnns().add(factory_.createParenAnn());
      }
      return result;
    }
    if (mixfix) {
      try {
        Expr operand = memPred.getLeftExpr();
        RefExpr operator = (RefExpr) memPred.getRightExpr();
        OperatorName op = new OperatorName(operator.getZName());
        return printFactory_.createPrintPredicate(printOperator(op, operand),
                                                  precedence,
                                                  null);
      }
      catch (Exception e) {
        throw new CannotPrintAstException(e.getMessage());
      }
    }
    List list = new LinkedList();
    list.add(visit(memPred.getLeftExpr()));
    list.add(ZKeyword.MEM);
    list.add(visit(memPred.getRightExpr()));
    PrintPredicate result =
      printFactory_.createPrintPredicate(list, precedence, null);
    if (memPred.getAnn(ParenAnn.class) != null) {
      result.getAnns().add(factory_.createParenAnn());
    }
    return result;
  }

  /**
   * Transforms each generic operator application, that is each
   * reference expression with Mixfix set to <code>true</code> into an
   * OperatorApplication.
   */
  @Override
  public Term visitRefExpr(RefExpr refExpr)
  {
    final boolean isGenericOperatorApplication =
      refExpr.getMixfix().booleanValue();
    if (isGenericOperatorApplication) {
      final OperatorName opName = refExpr.getZName().getOperatorName();
      final ZExprList argList = (ZExprList) visit(refExpr.getZExprList());
      final Precedence precedence = getPrec(refExpr);
      OperatorApplication result =
        createOperatorApplication(opName, argList, precedence);
      result.getAnns().addAll(refExpr.getAnns());
      return result;
    }
    return VisitorUtils.visitTerm(this, refExpr, true);
  }

  /**
   * Sets up the operator table for this Z section.
   */
  @Override
  public Term visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    warningManager_.setCurrentSectName(name);
    try {
      opTable_ = (OpTable) sectInfo_.get(new Key(name, OpTable.class));
    }
    catch (CommandException exception) {      
      warningManager_.warn("Cannot get operator table for {0}; try to print anyway ... ", name);
    }
    if (opTable_ == null) {
      List parentOpTables = new LinkedList();
      for (Parent parent : zSect.getParent()) {
        OpTable parentOpTable = getOpTable(parent.getWord());
        if (parentOpTable != null) {
          parentOpTables.add(parentOpTable);
        }
      }
      if (parentOpTables.size() > 0) {
        try {
          opTable_ = new OpTable(zSect.getName(), parentOpTables);
        }
        catch (InfoTable.InfoTableException e) {
          throw new CannotPrintAstException(e);
        }
      }
    }
    prec_ = new PrecedenceVisitor(opTable_);
    return visitTerm(zSect);
  }

  protected boolean isInfix(OperatorName opName)
  {
    if (opName == null) return false;
    return Fixity.INFIX.equals(opName.getFixity());
  }

  /**
   * Retrieves the operator table of the given section.
   */
  private OpTable getOpTable(String name)
  {
    try {
      return sectInfo_.get(new Key<OpTable>(name, OpTable.class));
    }
    catch (CommandException exception) {      
      warningManager_.warn("Cannot get operator table for {0}; try to print anyway ... ", name);      
    }
    return null;
  }
  
  /**
   * @throws NullPointerException if <code>opName</code> is <code>null</code>.
   */
  private OperatorApplication createOperatorApplication(OperatorName opName,
                                                        List argList,
                                                        Precedence precedence)
  {
    Assoc assoc = null;
    if (isInfix(opName)) {
      if (opTable_ != null) {
        OpTable.OpInfo opInfo = opTable_.lookup(opName);
        if (opInfo != null) {
          assoc = opInfo.getAssoc();
        }
        else {
          String message =
            "Cannot find precedence and associativity for '" + opName + "'.";
          throw new CannotPrintAstException(message);
        }
      }
      else {
        String message =
          "Cannot find precedence and associativity for '" + opName +
          "'; no operator table available";
        throw new CannotPrintAstException(message);
      }
    }
    return printFactory_.createOperatorApplication(opName,
                                                   argList,
                                                   precedence,
                                                   assoc);
  }

  protected Term visit(Term term)
  {
    return term.accept(this);
  }

  protected Precedence getPrec(Term term)
  {
    return term.accept(prec_);
  }

  public static class CannotPrintAstException
    extends net.sourceforge.czt.util.CztException
  {
    public CannotPrintAstException(String message)
    {
      super(message);
    }

    public CannotPrintAstException(Exception cause)
    {
      super(cause);
    }
  }

  private List printOperator(OperatorName op, Object arguments)
  {
    List result = new LinkedList();
    List args = new LinkedList();
    if (arguments instanceof List) {
      args = (List) arguments;
    }
    else {
      if (op.isUnary()) {
        args.add(arguments);
      }
      else {
        if (! (arguments instanceof TupleExpr)) {
          String message = arguments.toString() + " not instance of TupleExpr";
          throw new CannotPrintAstException(message);
        }
        TupleExpr tuple = (TupleExpr) arguments;
        args = tuple.getZExprList();
      }
    }
    int pos = 0;
    for (String opPart : op.getWords()) {
      if (opPart.equals(ZString.ARG)) {
        result.add(visit((Term) args.get(pos)));
        pos++;
      }
      else if (opPart.equals(ZString.LISTARG)) {
        Object arg = args.get(pos);
        if (! (arg instanceof SetExpr)) {
          String message = "Expected SetExpr but got " + arg;
          throw new CannotPrintAstException(message);
        }
        SetExpr setExpr = (SetExpr) arg;
        List<Expr> sequence = setExpr.getZExprList();
        for (Iterator<Expr> i = sequence.iterator(); i.hasNext();) {
          Expr o = i.next();
          if (! (o instanceof TupleExpr)) {
            String message = "Expected TupleExpr but got " + o;
            throw new CannotPrintAstException(message);
          }
          TupleExpr tuple = (TupleExpr) o;
          List<Expr> tupleContents = tuple.getZExprList();
          if (tupleContents.size() != 2) {
            String message =
              "Expected tuple of size 2 but was " + tupleContents.size();
            throw new CannotPrintAstException(message);
          }
          result.add(visit(tupleContents.get(1)));
          if (i.hasNext()) result.add(ZKeyword.COMMA);
        }
        pos++;
      }
      else {
	Decorword decorword =
	  new Decorword(opPart, (ZStrokeList) op.getStrokes());
        result.add(decorword.toString());
      }
    }
    return result;
  }
}

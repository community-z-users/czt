/**
Copyright 2004 Petra Malik
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
import java.util.List;

import java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;

import net.sourceforge.czt.scanner.Sym;

import net.sourceforge.czt.util.CztException;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * A Z visitor used for printing.
 *
 * @author Petra Malik
 */
public class ZPrintVisitor
  implements TermVisitor,
             AndPredVisitor,
             AxParaVisitor,
             ConstDeclVisitor,
             DeclNameVisitor,
             Exists1ExprVisitor,
             ExistsExprVisitor,
             GivenParaVisitor,
             IffPredVisitor,
             ImpliesPredVisitor,
             InStrokeVisitor,
             LambdaExprVisitor,
             LetExprVisitor,
             MemPredVisitor,
             NameVisitor,
             NumExprVisitor,
             NextStrokeVisitor,
             OrPredVisitor,
             OutStrokeVisitor,
             PowerExprVisitor,
             SchTextVisitor,
             SetExprVisitor,
             TupleExprVisitor,
             UnparsedParaVisitor,
             VarDeclVisitor,
             ZSectVisitor
{
  private ZPrinter printer_;

  public ZPrintVisitor(ZPrinter printer)
  {
    printer_ = printer;
  }

  /**
   * Visit all children of a term.
   */
  public Object visitTerm(Term term)
  {
    VisitorUtils.visitArray(this, term.getChildren());
    return null;
  }

  public Object visitAndPred(AndPred andPred)
  {
    andPred.getLeftPred().accept(this);
    if (Op.And.equals(andPred.getOp())) {
      print(Sym.AND);
    }
    else if (Op.Chain.equals(andPred.getOp())) {
      // TODO
    }
    else if (Op.NL.equals(andPred.getOp())) {
      print(Sym.NL);
    }
    else if (Op.Semi.equals(andPred.getOp())) {
      print(Sym.SEMICOLON);
    }
    else {
      throw new CztException("Unexpected Op");
    }
    andPred.getRightPred().accept(this);
    return null;
  }
  public Object visitAxPara(AxPara axPara)
  {
    Box box = axPara.getBox();
    if (box.equals(Box.AxBox)) {
      print(Sym.AX);
      axPara.getSchText().accept(this);
      print(Sym.END);
    }
    else if (box.equals(Box.OmitBox)) {
      print(Sym.ZED);
      axPara.getSchText().accept(this);
      print(Sym.END);
    }
    else if (box.equals(Box.SchBox)) {
      print(Sym.SCH);
      List decls = axPara.getSchText().getDecl();
      ConstDecl cdecl = (ConstDecl) decls.get(0);
      String declName = cdecl.getDeclName().getWord();
      print(Sym.DECORWORD, declName);
      cdecl.getExpr().accept(this);
      print(Sym.END);
    }
    else {
      // TODO
      print(Sym.SCH);
      VisitorUtils.visitList(this, axPara.getDeclName());
      axPara.getSchText().accept(this);
      print(Sym.END);
    }
    return null;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    constDecl.getDeclName().accept(this);
    print(Sym.DEFEQUAL);
    constDecl.getExpr().accept(this);
    return null;
  }

  public Object visitDeclName(DeclName declName)
  {
    print(Sym.DECORWORD, declName.getWord());
    return null;
  }

  public Object visitExists1Expr(Exists1Expr exists1Expr)
  {
    print(Sym.EXI);
    exists1Expr.getSchText().accept(this);
    print(Sym.DOT);
    exists1Expr.getExpr().accept(this);
    return null;
  }

  public Object visitExistsExpr(ExistsExpr existsExpr)
  {
    print(Sym.EXIONE);
    existsExpr.getSchText().accept(this);
    print(Sym.DOT);
    existsExpr.getExpr().accept(this);
    return null;
  }

  public Object visitForallExpr(ForallExpr forallExpr)
  {
    print(Sym.ALL);
    forallExpr.getSchText().accept(this);
    print(Sym.DOT);
    forallExpr.getExpr().accept(this);
    return null;
  }

  public Object visitGivenPara(GivenPara givenPara)
  {
    print(Sym.ZED);
    print(Sym.LSQUARE);
    printTermList(givenPara.getDeclName());
    print(Sym.RSQUARE);
    print(Sym.END);
    return null;
  }

  public Object visitIffPred(IffPred iffPred)
  {
    iffPred.getLeftPred().accept(this);
    print(Sym.IFF);
    iffPred.getRightPred().accept(this);
    return null;
  }

  public Object visitImpliesPred(ImpliesPred impliesPred)
  {
    impliesPred.getLeftPred().accept(this);
    print(Sym.IMP);
    impliesPred.getRightPred().accept(this);
    return null;
  }

  public Object visitInStroke(InStroke inStroke)
  {
    print(Sym.INSTROKE);
    return null;
  }

  public Object visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    print(Sym.LAMBDA);
    lambdaExpr.getSchText().accept(this);
    print(Sym.DOT);
    lambdaExpr.getExpr().accept(this);
    return null;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    print(Sym.LET);
    letExpr.getSchText().accept(this);
    print(Sym.DOT);
    letExpr.getExpr().accept(this);
    return null;
  }

  public Object visitMemPred(MemPred memPred)
  {
    if (memPred.getMixfix().booleanValue()) {
      Expr operand = memPred.getLeftExpr();
      Expr operator = memPred.getRightExpr();
      operand.accept(this);
      operator.accept(this);
    }
    else {
      memPred.getLeftExpr().accept(this);
      print(Sym.MEM);
      memPred.getRightExpr().accept(this);
    }
    return null;
  }

  public Object visitNumExpr(NumExpr numExpr)
  {
    print(Sym.NUMERAL, Integer.valueOf(numExpr.getValue().toString()));
    return null;
  }

  public Object visitName(Name name)
  {
    print(Sym.DECORWORD, name.getWord());
    VisitorUtils.visitList(this, name.getStroke());
    return null;
  }

  public Object visitNextStroke(NextStroke nextStroke)
  {
    print(Sym.NEXTSTROKE);
    return null;
  }

  public Object visitOrPred(OrPred orPred)
  {
    orPred.getLeftPred().accept(this);
    print(Sym.OR);
    orPred.getRightPred().accept(this);
    return null;
  }

  public Object visitOutStroke(OutStroke outStroke)
  {
    print(Sym.OUTSTROKE);
    return null;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    print(Sym.POWER);
    powerExpr.getExpr().accept(this);
    return null;
  }

  public Object visitSchText(SchText schText)
  {
    printTermList(schText.getDecl(), Sym.NL);
    if (schText.getPred() != null) {
      print(Sym.BAR);
      schText.getPred().accept(this);
    }
    return null;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    print(Sym.LBRACE);
    printTermList(setExpr.getExpr());
    print(Sym.RBRACE);
    return null;
  }

  public Object visitTupleExpr(TupleExpr tupleExpr)
  {
    print(Sym.LPAREN);
    printTermList(tupleExpr.getExpr());
    print(Sym.RPAREN);
    return null;
  }

  public Object visitUnparsedPara(UnparsedPara unparsedPara)
  {
    // TODO
    return null;
  }

  public Object visitVarDecl(VarDecl varDecl)
  {
    printTermList(varDecl.getDeclName());
    print(Sym.COLON);
    varDecl.getExpr().accept(this);
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    List parents = zSect.getParent();
    print(Sym.ZED);
    print(Sym.SECTION);
    print(Sym.DECORWORD, zSect.getName());
    if (parents.size() > 0) {
      print(Sym.PARENTS);
      VisitorUtils.visitList(this, zSect.getParent());
    }
    print(Sym.END);
    VisitorUtils.visitList(this, zSect.getPara());
    return null;
  }

  private void printTermList(List list)
  {
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      term.accept(this);
      if (iter.hasNext()) {
        print(Sym.COMMA);
      }
    }
  }

  private void printTermList(List list, int separator)
  {
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      term.accept(this);
      if (iter.hasNext()) {
        print(separator);
      }
    }
  }

  private void print(int type)
  {
    printer_.printSymbol(new Symbol(type));
  }

  private void print(int type, Object value)
  {
    printer_.printSymbol(new Symbol(type, value));
  }

  /**
   * A printer that can print Z symbols.
   */
  interface ZPrinter
  {
    void printSymbol(Symbol symbol);
  }
}

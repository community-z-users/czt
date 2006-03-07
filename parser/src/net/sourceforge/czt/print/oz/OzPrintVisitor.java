/*
  Copyright (C) 2004, 2005, 2006 Petra Malik, Tim Miller
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

package net.sourceforge.czt.print.oz;

import java.util.List;
import java.util.Iterator;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.print.z.WhereWord;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.parser.oz.OzToken;
import net.sourceforge.czt.parser.z.Keyword;
import net.sourceforge.czt.parser.z.TokenName;

/**
 * An Object-Z visitor used for printing.
 *
 * @author Petra Malik, Tim Miller
 */
public class OzPrintVisitor
  extends net.sourceforge.czt.print.z.ZPrintVisitor
  implements OzVisitor
{
  /**
   * Creates a new Object-Z print visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public OzPrintVisitor(ZPrinter printer)
  {
    super(printer);
  }

  public Object visitClassPara(ClassPara classPara)
  {
    //print the header information
    if (classPara.getFormalParameters().size() == 0) {
      print(OzToken.CLASS);
      visit(classPara.getDeclName());
    }
    else {
      print(OzToken.GENCLASS);
      visit(classPara.getDeclName());
      print(TokenName.LSQUARE);
      printTermList(classPara.getFormalParameters());
      print(TokenName.RSQUARE);
    }
    print(TokenName.NL);

    visit(classPara.getVisibilityList());

    //visit each inherited class, putting a NL between them
    if (classPara.getInheritedClass() instanceof ZExprList) {
      ZExprList inheritedClass = (ZExprList) classPara.getInheritedClass();
      for (Expr expr : inheritedClass) {
        visit(expr);
        print(TokenName.NL);
      }
    }
    else {
      throw new
        UnsupportedOperationException("Non-ZExprList as Inherited Class");
    }

    //visit each inner paragraph, putting a NL between them
    for (Para para : classPara.getLocalDef()) {
      if (para instanceof AxPara) {
        AxPara axPara = (AxPara) para;
        visitInnerAxPara(axPara);
      }
      else if (para instanceof FreePara) {
        FreePara freePara = (FreePara) para;
        visitInnerFreePara(freePara);
      }
      else {
        visit(para);
        print(TokenName.NL);
      }
    }

    //visit the state and inital predicate
    visit(classPara.getState());
    visit(classPara.getInitialState());

    //visit each operation, putting a NL between them
    for (Iterator<Operation> iter = classPara.getOperation().iterator();
         iter.hasNext(); ) {
      Operation operation = iter.next();
      visit(operation);
      if (iter.hasNext()) {
        print(TokenName.NL);
      }
    }
    print(TokenName.END);
    return null;
  }

  protected Object visitInnerAxPara(AxPara axPara)
  {
    Box box = axPara.getBox();
    if (Box.OmitBox.equals(box)) {
      visit(axPara.getSchText());
    }
    else {
      assert false : "Inner AxPara with OmitBox";
    }
    return null;
  }

  protected Object visitInnerFreePara(FreePara freePara)
  {
    printTermList(freePara.getFreetype(), Keyword.ANDALSO);
    print(TokenName.NL);
    return null;
  }

  public Object visitVisibilityList(VisibilityList visibilityList)
  {
    if (visibilityList != null) {
      print(Keyword.PROJECT);
      print(TokenName.LPAREN);
      printTermList(visibilityList.getRefName());
      print(TokenName.RPAREN);
      print(TokenName.NL);
    }
    return null;
  }

  public Object visitInitialState(InitialState initialState)
  {
    if (initialState != null) {
      boolean isBox = Box.SchBox.equals(initialState.getBox());
      if (isBox) {
        print(OzToken.INIT);
        print(TokenName.NL);
        visit(initialState.getPred());
        print(TokenName.END);
      }
      else {
        printDecorword(OzString.INITWORD + ZString.SPACE +
                       OzString.SDEF + ZString.SPACE);
        print(TokenName.LSQUARE);
        visit(initialState.getPred());
        print(TokenName.RSQUARE);
      }
      print(TokenName.NL);
    }
    return null;
  }

  public Object visitState(State state)
  {
    if (state != null) {
      boolean isBox = Box.SchBox.equals(state.getBox());
      if (isBox) {
        print(OzToken.STATE);
        print(TokenName.NL);
      }
      else {
        print(TokenName.LSQUARE);
      }

      DeclList pDeclList = state.getPrimaryDecl().getDeclList();
      if (pDeclList instanceof ZDeclList) {
        ZDeclList zDeclList = (ZDeclList) pDeclList;
        if (zDeclList.size() > 0) {
          visit(state.getPrimaryDecl());
        }
      }
      else {
        throw new
          UnsupportedOperationException("Non-ZDeclList in PrimaryDecl");
      }

      DeclList sDeclList = state.getSecondaryDecl().getDeclList();
      if (sDeclList instanceof ZDeclList) {
        ZDeclList zDeclList = (ZDeclList) sDeclList;
        if (zDeclList.size() > 0) {
          print(TokenName.NL);
          printDecorword(OzString.DELTA);
          print(TokenName.NL);
          visit(state.getSecondaryDecl());
        }
      }
      else {
        throw new
          UnsupportedOperationException("Non-ZDeclList in SecondayDecl");
      }

      if (state.getPred() != null) {
        if (isBox) {
          print(TokenName.DECORWORD, new WhereWord());
          visit(state.getPred());
        }
        else {
          print(Keyword.BAR);
          visit(state.getPred());
          print(TokenName.RSQUARE);
        }
      }

      if (isBox) {
        print(TokenName.END);
      }
      print(TokenName.NL);
    }
    return null;
  }

  public Object visitPrimaryDecl(PrimaryDecl primaryDecl)
  {
    visit(primaryDecl.getDeclList());
    return null;
  }

  public Object visitSecondaryDecl(SecondaryDecl secondaryDecl)
  {
    visit(secondaryDecl.getDeclList());
    return null;
  }

  public Object visitOperation(Operation operation)
  {
    boolean isBox = Box.SchBox.equals(operation.getBox());
    if (isBox) {
      print(OzToken.OPSCH);
      visit(operation.getOpName());
      print(TokenName.NL);

      assert operation.getOpExpr() instanceof AnonOpExpr;
      AnonOpExpr anonOpExpr = (AnonOpExpr) operation.getOpExpr();
      OpText opText = anonOpExpr.getOpText();

      visit(opText.getDeltaList());

      if (opText.getSchText() instanceof ZSchText) {
        ZSchText zSchText = (ZSchText) opText.getSchText();
        visit(zSchText.getDeclList());
        if (zSchText.getPred() != null) {
          print(TokenName.DECORWORD, new WhereWord());
          visit(zSchText.getPred());
        }
      }
      else {
        throw new UnsupportedOperationException("Non-ZSchText in Operation");
      }
      print(TokenName.END);
    }
    else {
      visit(operation.getOpName());
      print(OzToken.SDEF);
      visit(operation.getOpExpr());
    }
    return null;
  }

  public Object visitOpText(OpText opText)
  {
    visit(opText.getDeltaList());
    visit(opText.getSchText());
    return null;
  }

  public Object visitDeltaList(DeltaList deltaList)
  {
    printDecorword(OzString.DELTA);
    print(TokenName.LPAREN);
    printTermList(deltaList.getRefName());
    print(TokenName.RPAREN);
    print(TokenName.NL);
    return null;
  }

  public Object visitPredExpr(PredExpr predExpr)
  {
    printLPAREN(predExpr);
    visit(predExpr.getPred());
    printRPAREN(predExpr);
    return null;
  }

  public Object visitClassUnionExpr(ClassUnionExpr classUnionExpr)
  {
    printLPAREN(classUnionExpr);
    visit(classUnionExpr.getLeftExpr());
    printDecorword(OzString.CLASSUNION);
    visit(classUnionExpr.getRightExpr());
    printRPAREN(classUnionExpr);
    return null;
  }

  public Object visitPolyExpr(PolyExpr polyExpr)
  {
    printLPAREN(polyExpr);
    printDecorword(OzString.POLY);
    visit(polyExpr.getExpr());
    printRPAREN(polyExpr);
    return null;
  }

  public Object visitContainmentExpr(ContainmentExpr containmentExpr)
  {
    printLPAREN(containmentExpr);
    visit(containmentExpr.getExpr());
    printDecorword(OzString.CONTAINMENT);
    printRPAREN(containmentExpr);
    return null;
  }

  public Object visitOpPromotionExpr(OpPromotionExpr opPromotionExpr)
  {
    printLPAREN(opPromotionExpr);
    if (opPromotionExpr.getExpr() != null) {
      visit(opPromotionExpr.getExpr());
      print(Keyword.DOT);
    }
    visit(opPromotionExpr.getRefName());
    printRPAREN(opPromotionExpr);
    return null;
  }

  public Object visitDistConjOpExpr(DistConjOpExpr distConjOpExpr)
  {
    printLPAREN(distConjOpExpr);
    printDecorword(OzString.DCNJ);
    visit(distConjOpExpr.getSchText());
    print(Keyword.SPOT);
    visit(distConjOpExpr.getOpExpr());
    printRPAREN(distConjOpExpr);
    return null;
  }

  public Object visitDistSeqOpExpr(DistSeqOpExpr distSeqOpExpr)
  {
    printLPAREN(distSeqOpExpr);
    print(Keyword.ZCOMP);
    visit(distSeqOpExpr.getSchText());
    print(Keyword.SPOT);
    visit(distSeqOpExpr.getOpExpr());
    printRPAREN(distSeqOpExpr);
    return null;
  }

  public Object visitDistChoiceOpExpr(DistChoiceOpExpr distChoiceOpExpr)
  {
    printLPAREN(distChoiceOpExpr);
    printDecorword(OzString.DGCH);
    visit(distChoiceOpExpr.getSchText());
    print(Keyword.SPOT);
    visit(distChoiceOpExpr.getOpExpr());
    printRPAREN(distChoiceOpExpr);
    return null;
  }

  public Object visitAnonOpExpr(AnonOpExpr anonOpExpr)
  {
    printLPAREN(anonOpExpr);
    print(TokenName.LSQUARE);
    visit(anonOpExpr.getOpText());
    print(TokenName.RSQUARE);
    printRPAREN(anonOpExpr);
    return null;
  }

  public Object visitConjOpExpr(ConjOpExpr conjOpExpr)
  {
    printLPAREN(conjOpExpr);
    visit(conjOpExpr.getLeftOpExpr());
    print(Keyword.AND);
    visit(conjOpExpr.getRightOpExpr());
    printRPAREN(conjOpExpr);
    return null;
  }

  public Object visitParallelOpExpr(ParallelOpExpr parallelOpExpr)
  {
    printLPAREN(parallelOpExpr);
    visit(parallelOpExpr.getLeftOpExpr());
    printDecorword(OzString.PARALLEL);
    visit(parallelOpExpr.getRightOpExpr());
    printRPAREN(parallelOpExpr);
    return null;
  }

  public Object visitAssoParallelOpExpr(AssoParallelOpExpr assoParallelOpExpr)
  {
    printLPAREN(assoParallelOpExpr);
    visit(assoParallelOpExpr.getLeftOpExpr());
    printDecorword(OzString.ASSOPARALLEL);
    visit(assoParallelOpExpr.getRightOpExpr());
    printRPAREN(assoParallelOpExpr);
    return null;
  }

  public Object visitExChoiceOpExpr(ExChoiceOpExpr exChoiceOpExpr)
  {
    printLPAREN(exChoiceOpExpr);
    visit(exChoiceOpExpr.getLeftOpExpr());
    printDecorword(OzString.GCH);
    visit(exChoiceOpExpr.getRightOpExpr());
    printRPAREN(exChoiceOpExpr);
    return null;
  }

  public Object visitSeqOpExpr(SeqOpExpr seqOpExpr)
  {
    printLPAREN(seqOpExpr);
    visit(seqOpExpr.getLeftOpExpr());
    print(Keyword.ZCOMP);
    visit(seqOpExpr.getRightOpExpr());
    printRPAREN(seqOpExpr);
    return null;
  }

  public Object visitScopeEnrichOpExpr(ScopeEnrichOpExpr scopeEnrichExpr)
  {
    printLPAREN(scopeEnrichExpr);
    visit(scopeEnrichExpr.getLeftOpExpr());
    print(Keyword.SPOT);
    visit(scopeEnrichExpr.getRightOpExpr());
    printRPAREN(scopeEnrichExpr);
    return null;
  }

  public Object visitHideOpExpr(HideOpExpr hideOpExpr)
  {
    printLPAREN(hideOpExpr);
    visit(hideOpExpr.getOpExpr());
    print(Keyword.HIDE);
    print(TokenName.LPAREN);
    visit(hideOpExpr.getRefNameList());
    print(TokenName.RPAREN);
    printRPAREN(hideOpExpr);
    return null;
  }

  public Object visitRenameOpExpr(RenameOpExpr renameOpExpr)
  {
    printLPAREN(renameOpExpr);
    visit(renameOpExpr.getOpExpr());
    print(TokenName.LSQUARE);
    visit(renameOpExpr.getRenameList());
    print(TokenName.RSQUARE);
    printRPAREN(renameOpExpr);
    return null;
  }

  public Object visitClassRefType(ClassRefType classRefType)
  {
    throw new UnsupportedOperationException("Unexpected term ClassRefType.");
  }

  public Object visitClassPolyType(ClassPolyType classPolyType)
  {
    throw new UnsupportedOperationException("Unexpected term ClassPolyType.");
  }

  public Object visitClassUnionType(ClassUnionType classUnionType)
  {
    throw new UnsupportedOperationException("Unexpected term ClassUnionType.");
  }

  public Object visitClassRef(ClassRef classRef)
  {
    throw new UnsupportedOperationException("Unexpected term ClassRef.");
  }

  public Object visitNameSignaturePair(NameSignaturePair nameSignaturePair)
  {
    throw new UnsupportedOperationException("Unexpected term NameSignaturePair.");
  }

  public Object visitClassSig(ClassSig classSig)
  {
    throw new UnsupportedOperationException("Unexpected term ClassSig.");
  }

  protected void printLPAREN(TermA termA)
  {
    final boolean braces = termA.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
  }

  protected void printRPAREN(TermA termA)
  {
    final boolean braces = termA.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.RPAREN);
  }
}

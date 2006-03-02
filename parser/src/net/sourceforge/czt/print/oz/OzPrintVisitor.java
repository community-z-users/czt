/*
  Copyright (C) 2004, 2005 Petra Malik, Tim Miller
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
import net.sourceforge.czt.parser.util.DebugUtils;
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
  public static int OZ = Z + 1;

  /**
   * Creates a new Object-Z print visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public OzPrintVisitor(ZPrinter printer)
  {
    super(printer);
  }

  protected void ozPrint(int type)
  {
    print(type, OZ);
  }

  protected void ozPrint(int type, Object value)
  {
    print(type, OZ, value);
  }

  public Object visitClassPara(ClassPara classPara)
  {
    //print the header information
    if (classPara.getFormalParameters().size() == 0) {
      ozPrint(Sym.CLASS);
      visit(classPara.getDeclName());
    }
    else {
      ozPrint(Sym.GENCLASS);
      visit(classPara.getDeclName());
      zPrint(TokenName.LSQUARE);
      printTermList(classPara.getFormalParameters());
      zPrint(TokenName.RSQUARE);
    }
    zPrint(TokenName.NL);

    visit(classPara.getVisibilityList());

    //visit each inherited class, putting a NL between them
    if (classPara.getInheritedClass() instanceof ZExprList) {
      ZExprList inheritedClass = (ZExprList) classPara.getInheritedClass();
      for (Expr expr : inheritedClass) {
        visit(expr);
        zPrint(TokenName.NL);
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
        zPrint(TokenName.NL);
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
        zPrint(TokenName.NL);
      }
    }
    zPrint(TokenName.END);
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
    printTermList(freePara.getFreetype(), ZString.ANDALSO);
    zPrint(TokenName.NL);
    return null;
  }

  public Object visitVisibilityList(VisibilityList visibilityList)
  {
    if (visibilityList != null) {
      printKeyword(ZString.ZPROJ);
      zPrint(TokenName.LPAREN);
      printTermList(visibilityList.getRefName());
      zPrint(TokenName.RPAREN);
      zPrint(TokenName.NL);
    }
    return null;
  }

  public Object visitInitialState(InitialState initialState)
  {
    if (initialState != null) {
      boolean isBox = Box.SchBox.equals(initialState.getBox());
      if (isBox) {
        ozPrint(Sym.INIT);
        zPrint(TokenName.NL);
        visit(initialState.getPred());
        zPrint(TokenName.END);
      }
      else {
        printKeyword(OzString.INITWORD + ZString.SPACE +
                     OzString.SDEF + ZString.SPACE);
        zPrint(TokenName.LSQUARE);
        visit(initialState.getPred());
        zPrint(TokenName.RSQUARE);
      }
      zPrint(TokenName.NL);
    }
    return null;
  }

  public Object visitState(State state)
  {
    if (state != null) {
      boolean isBox = Box.SchBox.equals(state.getBox());
      if (isBox) {
        ozPrint(Sym.STATE);
        zPrint(TokenName.NL);
      }
      else {
        zPrint(TokenName.LSQUARE);
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
          zPrint(TokenName.NL);
          printKeyword(OzString.DELTA);
          zPrint(TokenName.NL);
          visit(state.getSecondaryDecl());
        }
      }
      else {
        throw new
          UnsupportedOperationException("Non-ZDeclList in SecondayDecl");
      }

      if (state.getPred() != null) {
        if (isBox) {
          zPrint(TokenName.DECORWORD, new WhereWord());
          visit(state.getPred());
        }
        else {
          printKeyword(ZString.BAR);
          visit(state.getPred());
          zPrint(TokenName.RSQUARE);
        }
      }

      if (isBox) {
        zPrint(TokenName.END);
      }
      zPrint(TokenName.NL);
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
      ozPrint(net.sourceforge.czt.print.oz.Sym.OPSCH);
      visit(operation.getOpName());
      zPrint(TokenName.NL);

      assert operation.getOpExpr() instanceof AnonOpExpr;
      AnonOpExpr anonOpExpr = (AnonOpExpr) operation.getOpExpr();
      OpText opText = anonOpExpr.getOpText();

      visit(opText.getDeltaList());

      if (opText.getSchText() instanceof ZSchText) {
        ZSchText zSchText = (ZSchText) opText.getSchText();
        visit(zSchText.getDeclList());
        if (zSchText.getPred() != null) {
          zPrint(TokenName.DECORWORD, new WhereWord());
          visit(zSchText.getPred());
        }
      }
      else {
        throw new UnsupportedOperationException("Non-ZSchText in Operation");
      }
      zPrint(TokenName.END);
    }
    else {
      visit(operation.getOpName());
      ozPrint(net.sourceforge.czt.print.oz.Sym.SDEF);
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
    printKeyword(ZString.DELTA);
    zPrint(TokenName.LPAREN);
    printTermList(deltaList.getRefName());
    zPrint(TokenName.RPAREN);
    zPrint(TokenName.NL);
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
    printKeyword(OzString.CLASSUNION);
    visit(classUnionExpr.getRightExpr());
    printRPAREN(classUnionExpr);
    return null;
  }

  public Object visitPolyExpr(PolyExpr polyExpr)
  {
    printLPAREN(polyExpr);
    printKeyword(OzString.POLY);
    visit(polyExpr.getExpr());
    printRPAREN(polyExpr);
    return null;
  }

  public Object visitContainmentExpr(ContainmentExpr containmentExpr)
  {
    printLPAREN(containmentExpr);
    visit(containmentExpr.getExpr());
    printKeyword(OzString.CONTAINMENT);
    printRPAREN(containmentExpr);
    return null;
  }

  public Object visitOpPromotionExpr(OpPromotionExpr opPromotionExpr)
  {
    printLPAREN(opPromotionExpr);
    if (opPromotionExpr.getExpr() != null) {
      visit(opPromotionExpr.getExpr());
      printKeyword(ZString.DOT);
    }
    visit(opPromotionExpr.getRefName());
    printRPAREN(opPromotionExpr);
    return null;
  }

  public Object visitDistConjOpExpr(DistConjOpExpr distConjOpExpr)
  {
    printLPAREN(distConjOpExpr);
    printKeyword(OzString.DCNJ);
    visit(distConjOpExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(distConjOpExpr.getOpExpr());
    printRPAREN(distConjOpExpr);
    return null;
  }

  public Object visitDistSeqOpExpr(DistSeqOpExpr distSeqOpExpr)
  {
    printLPAREN(distSeqOpExpr);
    printKeyword(ZString.ZCOMP);
    visit(distSeqOpExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(distSeqOpExpr.getOpExpr());
    printRPAREN(distSeqOpExpr);
    return null;
  }

  public Object visitDistChoiceOpExpr(DistChoiceOpExpr distChoiceOpExpr)
  {
    printLPAREN(distChoiceOpExpr);
    printKeyword(OzString.DGCH);
    visit(distChoiceOpExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(distChoiceOpExpr.getOpExpr());
    printRPAREN(distChoiceOpExpr);
    return null;
  }

  public Object visitAnonOpExpr(AnonOpExpr anonOpExpr)
  {
    printLPAREN(anonOpExpr);
    zPrint(TokenName.LSQUARE);
    visit(anonOpExpr.getOpText());
    zPrint(TokenName.RSQUARE);
    printRPAREN(anonOpExpr);
    return null;
  }

  public Object visitConjOpExpr(ConjOpExpr conjOpExpr)
  {
    printLPAREN(conjOpExpr);
    visit(conjOpExpr.getLeftOpExpr());
    printKeyword(ZString.AND);
    visit(conjOpExpr.getRightOpExpr());
    printRPAREN(conjOpExpr);
    return null;
  }

  public Object visitParallelOpExpr(ParallelOpExpr parallelOpExpr)
  {
    printLPAREN(parallelOpExpr);
    visit(parallelOpExpr.getLeftOpExpr());
    printKeyword(OzString.PARALLEL);
    visit(parallelOpExpr.getRightOpExpr());
    printRPAREN(parallelOpExpr);
    return null;
  }

  public Object visitAssoParallelOpExpr(AssoParallelOpExpr assoParallelOpExpr)
  {
    printLPAREN(assoParallelOpExpr);
    visit(assoParallelOpExpr.getLeftOpExpr());
    printKeyword(OzString.ASSOPARALLEL);
    visit(assoParallelOpExpr.getRightOpExpr());
    printRPAREN(assoParallelOpExpr);
    return null;
  }

  public Object visitExChoiceOpExpr(ExChoiceOpExpr exChoiceOpExpr)
  {
    printLPAREN(exChoiceOpExpr);
    visit(exChoiceOpExpr.getLeftOpExpr());
    printKeyword(OzString.GCH);
    visit(exChoiceOpExpr.getRightOpExpr());
    printRPAREN(exChoiceOpExpr);
    return null;
  }

  public Object visitSeqOpExpr(SeqOpExpr seqOpExpr)
  {
    printLPAREN(seqOpExpr);
    visit(seqOpExpr.getLeftOpExpr());
    printKeyword(ZString.ZCOMP);
    visit(seqOpExpr.getRightOpExpr());
    printRPAREN(seqOpExpr);
    return null;
  }

  public Object visitScopeEnrichOpExpr(ScopeEnrichOpExpr scopeEnrichExpr)
  {
    printLPAREN(scopeEnrichExpr);
    visit(scopeEnrichExpr.getLeftOpExpr());
    printKeyword(ZString.SPOT);
    visit(scopeEnrichExpr.getRightOpExpr());
    printRPAREN(scopeEnrichExpr);
    return null;
  }

  public Object visitHideOpExpr(HideOpExpr hideOpExpr)
  {
    printLPAREN(hideOpExpr);
    visit(hideOpExpr.getOpExpr());
    printKeyword(ZString.ZHIDE);
    zPrint(TokenName.LPAREN);
    visit(hideOpExpr.getRefNameList());
    zPrint(TokenName.RPAREN);
    printRPAREN(hideOpExpr);
    return null;
  }

  public Object visitRenameOpExpr(RenameOpExpr renameOpExpr)
  {
    printLPAREN(renameOpExpr);
    visit(renameOpExpr.getOpExpr());
    zPrint(TokenName.LSQUARE);
    visit(renameOpExpr.getRenameList());
    zPrint(TokenName.RSQUARE);
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
    if (braces) zPrint(TokenName.LPAREN);
  }

  protected void printRPAREN(TermA termA)
  {
    final boolean braces = termA.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.RPAREN);
  }
}

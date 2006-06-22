/*
  Copyright (C) 2004, 2005, 2006 Petra Malik, Leo Freitas
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

package net.sourceforge.czt.print.circus;

import java.util.List;
import java.util.Iterator;
import net.sourceforge.czt.parser.circus.CircusKeyword;
import net.sourceforge.czt.parser.util.Token;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.circus.util.CircusString;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.print.z.WhereWord;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.visitor.*;
import net.sourceforge.czt.parser.circus.CircusToken;
import net.sourceforge.czt.parser.z.Keyword;
import net.sourceforge.czt.parser.z.TokenName;

/**
 * An Object-Z visitor used for printing.
 *
 * @author Petra Malik, Leo Freitas
 */
public class CircusPrintVisitor
  extends net.sourceforge.czt.print.z.ZPrintVisitor
  implements CircusVisitor
{
  /**
   * Creates a new Object-Z print visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public CircusPrintVisitor(ZPrinter printer)
  {
    super(printer);
  }
  
  /*********************************************************** 
   * Auxiliary methods 
   ***********************************************************/
  
  protected void print(CircusKeyword keyword) {
    /* CIRCDEF is the only Keyword that is a scanner token */
    if (keyword.equals(CircusKeyword.CIRCDEF))
      print((Token) keyword);
    else
      printDecorword(keyword.spelling());
  }
  
  protected boolean isChannelFromDecl(ChannelDecl term) {
    return (term.getDeclNameList() == null && term.getExpr() instanceof RefExpr);
  }

  /*********************************************************** 
   * Channel related    
   ***********************************************************/
  public Object visitChannelPara(ChannelPara term) {
    //TODO: Change this to CIRCUS for \begin{circus} at some point.
    print(TokenName.ZED);
    visit(term.getChannelDecl());    
    print(TokenName.END);   
    return null;
  } 
  
  public Object visitChannelDecl(ChannelDecl term) {    
    if (isChannelFromDecl(term)) {
      print(CircusKeyword.CIRCCHANFROM);
      printGenericFormals(term.getGenFormals());
      assert term.getExpr() != null;
      visit(term.getExpr());
    } else {  
      print(CircusKeyword.CIRCCHAN);
      printGenericFormals(term.getGenFormals());
      visit(term.getDeclNameList());      
      if (term.getExpr() != null) {
        print(Keyword.COLON);
        visit(term.getExpr());
      }
    }
    print(TokenName.NL);
    return null;
  }  
  
  /*********************************************************** 
   * Channel set related    
   ***********************************************************/
  public Object visitChannelSetPara(ChannelSetPara term) {
    print(TokenName.ZED);
    print(CircusKeyword.CIRCCHANSET);
    printGenericFormals(term.getGenFormals());
    visit(term.getName());    
    print(Keyword.DEFEQUAL);    
    visit(term.getChannelSet());
    print(TokenName.END);    
    return null;
  }

  public Object visitChannelSet(ChannelSet term) {
    visit(term.getExpr());
    return null;
  }
  
  public Object visitBasicChannelSetExpr(BasicChannelSetExpr term) {
    print(CircusToken.LCIRCCHANSET);
    printTermList(term.getZExprList());    
    print(CircusToken.RCIRCCHANSET);
    return null;
  }
  
  /*********************************************************** 
   * Process related    
   ***********************************************************/

  public Object visitProcessPara(ProcessPara term) {
    return null;
  }

  public Object visitBasicProcess(BasicProcess term) {
    return null;
  }
  
  public Object visitCallProcess(CallProcess term) {
    return null;
  }

  public Object visitHideProcess(HideProcess term) {
    return null;
  }
  
  public Object visitRenameProcess(RenameProcess term) {
    return null;
  }

  public Object visitSeqProcess(SeqProcess term) {
    return null;
  }

  public Object visitExtChoiceProcess(ExtChoiceProcess term) {
    return null;
  }

  public Object visitIntChoiceProcess(IntChoiceProcess term) {
    return null;
  }

  public Object visitParallelProcess(ParallelProcess term) {
    return null;
  }
  
  public Object visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term) {
    return null;
  }

  public Object visitInterleaveProcess(InterleaveProcess term) {
    return null;
  }  

  public Object visitParamProcess(ParamProcess term) {
    return null;
  }

  public Object visitSeqProcessIte(SeqProcessIte term) {
    return null;
  }

  public Object visitExtChoiceProcessIte(ExtChoiceProcessIte term) {
    return null;
  }

  public Object visitIntChoiceProcessIte(IntChoiceProcessIte term) {
    return null;
  }
    
  public Object visitParallelProcessIte(ParallelProcessIte term) {
    return null;
  }

  public Object visitAlphabetisedParallelProcessIte(AlphabetisedParallelProcessIte term) {
    return null;
  }
  
  public Object visitInterleaveProcessIte(InterleaveProcessIte term) {
    return null;
  }
  
  public Object visitIndexedProcess(IndexedProcess term) {
    return null;
  }

  public Object visitSeqProcessIdx(SeqProcessIdx term) {
    return null;
  }

  public Object visitExtChoiceProcessIdx(ExtChoiceProcessIdx term) {
    return null;
  }

  public Object visitIntChoiceProcessIdx(IntChoiceProcessIdx term) {
    return null;
  }

  public Object visitParallelProcessIdx(ParallelProcessIdx term) {
    return null;
  }

  public Object visitAlphabetisedParallelProcessIdx(AlphabetisedParallelProcessIdx term) {
    return null;
  }

  public Object visitInterleaveProcessIdx(InterleaveProcessIdx term) {
    return null;
  }
  
  /*********************************************************** 
   * Action related    
   ***********************************************************/
  public Object visitChaosAction(ChaosAction term) {    
    print(CircusKeyword.CIRCCHAOS);
    return null;
  }

  public Object visitSkipAction(SkipAction term) {
    print(CircusKeyword.CIRCSKIP);
    return null;
  }
  
  public Object visitStopAction(StopAction term) {
    print(CircusKeyword.CIRCSTOP);
    return null;
  }
  
  public Object visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term) {
    return null;
  }
    
  public Object visitAlphabetisedParallelAction(AlphabetisedParallelAction term) {
    return null;
  }

  
  /*********************************************************** 
   * Command related    
   ***********************************************************/
  
  /*********************************************************** 
   * Unexpected terms 
   ***********************************************************/
  
  public Object visitChannelType(ChannelType term) {
    throw new UnsupportedOperationException("Unexpected term ChannelType.");    
  }

  public Object visitChannelSetType(ChannelSetType term) {
    throw new UnsupportedOperationException("Unexpected term ChannelSetType.");    
  }

  public Object visitProcessType(ProcessType term) {
    throw new UnsupportedOperationException("Unexpected term ProcessType.");    
  }

  public Object visitActionType(ActionType term) {
    throw new UnsupportedOperationException("Unexpected term ActionType.");    
  }

  public Object visitNameSetType(NameSetType term) {
    throw new UnsupportedOperationException("Unexpected term NameSetType.");    
  }

  public Object visitProcessSignature(ProcessSignature term) {
    throw new UnsupportedOperationException("Unexpected term ProcessSignature.");    
  }

  public Object visitBasicProcessSignature(BasicProcessSignature term) {
    throw new UnsupportedOperationException("Unexpected term BasicProcessSignature.");    
  }

  public Object visitActionSignature(ActionSignature term) {
    throw new UnsupportedOperationException("Unexpected term ActionSignature.");    
  }
  
  public Object visitCircusStateAnn(CircusStateAnn term) {
    throw new UnsupportedOperationException("Unexpected term CircusStateAnn.");    
  }

  /*********************************************************** 
   * Others 
   ***********************************************************/
  
    public Object visitParamAction(ParamAction term) {
    return null;
  }


  public Object visitParallelActionIte(ParallelActionIte term) {
    return null;
  }

  

  public Object visitIntChoiceActionIte(IntChoiceActionIte term) {
    return null;
  }

  public Object visitOutputField(OutputField term) {
    return null;
  }

  public Object visitIntChoiceAction(IntChoiceAction term) {
    return null;
  }

  public Object visitIfGuardedCommand(IfGuardedCommand term) {
    return null;
  }

  public Object visitSchExprAction(SchExprAction term) {
    return null;
  }

  public Object visitSeqAction(SeqAction term) {
    return null;
  }

  public Object visitRefinementConjPara(RefinementConjPara term) {
    return null;
  }

  public Object visitNameSetPara(NameSetPara term) {
    return null;
  }

  public Object visitOnTheFlyDefAnn(OnTheFlyDefAnn term) {
    /* Annotations need special treatment, see ZPrintVisitor */
    return null;
  }

  public Object visitActionPara(ActionPara term) {
    return null;
  }

  public Object visitCommunication(Communication term) {
    return null;
  }

  public Object visitExtChoiceActionIte(ExtChoiceActionIte term) {
    return null;
  }

  public Object visitPrefixingAction(PrefixingAction term) {
    return null;
  }

  public Object visitParallelAction(ParallelAction term) {
    return null;
  }

  public Object visitHideAction(HideAction term) {
    return null;
  }

  public Object visitMuAction(MuAction term) {
    return null;
  }

  public Object visitCircusFieldList(CircusFieldList term) {
    return null;
  }

  public Object visitSigmaExpr(SigmaExpr term) {
    return null;
  }

  public Object visitLetVarAction(LetVarAction term) {
    return null;
  }

  public Object visitSpecStmtCommand(SpecStmtCommand term) {
    return null;
  }

  public Object visitDotField(DotField term) {
    return null;
  }

  public Object visitNameSet(NameSet term) {
    return null;
  }

  public Object visitInputField(InputField term) {
    return null;
  }

  public Object visitSeqActionIte(SeqActionIte term) {
    return null;
  }

  public Object visitGuardedAction(GuardedAction term) {
    return null;
  }

  public Object visitAssignmentCommand(AssignmentCommand term) {
    return null;
  }

  public Object visitSubstitutionAction(SubstitutionAction term) {
    return null;
  }

  public Object visitLetMuAction(LetMuAction term) {
    return null;
  }

  public Object visitQualifiedDecl(QualifiedDecl term) {
    return null;
  }

  public Object visitCallAction(CallAction term) {
    return null;
  }

  public Object visitInterleaveActionIte(InterleaveActionIte term) {
    return null;
  }

  public Object visitExtChoiceAction(ExtChoiceAction term) {
    return null;
  }

  public Object visitInterleaveAction(InterleaveAction term) {
    return null;
  }

  public Object visitVarDeclCommand(VarDeclCommand term) {
    return null;
  }
}

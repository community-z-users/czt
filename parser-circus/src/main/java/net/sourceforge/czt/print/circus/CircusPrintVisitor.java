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
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * An Circus visitor used for printing.
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
    return (term.getNameList() == null && term.getExpr() instanceof RefExpr);
  }
  
  private boolean isOnTheFly(Term term) {
     return term.getAnn(OnTheFlyDefAnn.class) != null;
  }
  
  private void printActualParams(ZExprList term, boolean indexes) {
    if (term != null && !term.isEmpty()) {
      print(indexes ? CircusToken.CIRCLINST : TokenName.LPAREN);
      visit(term);
      print(indexes ? CircusToken.CIRCRINST : TokenName.RPAREN);
    }
  }
  
  protected void printFormalParameters(ZDeclList term) {
    assert term != null;
    if (term.isEmpty())        
        throw new PrintException("Empty formal parameters list.");
    visit(term);
  }
  
  protected void printProcessD(ProcessD term, boolean indexes) {
    if (!isOnTheFly(term)) {
      printFormalParameters(term.getZDeclList());      
      print(indexes ? CircusKeyword.CIRCINDEX : Keyword.SPOT);
      visit(term.getCircusProcess());
    } else {
      throw new PrintException("On-the-fly parameterised process (" + 
         term.getClass().getName() + ") must be processed by the AstToPrintTreeVisitor.");
    }
  }
  
  protected void printActionD(ActionD term) {
    if (!isOnTheFly(term)) {      
      printFormalParameters(term.getZDeclList());      
      print(Keyword.SPOT);
      visit(term.getCircusAction());
    } else {
      throw new PrintException("On-the-fly parameterised action (" + 
         term.getClass().getName() + ") must be processed by the AstToPrintTreeVisitor.");
    }
  }

  /*********************************************************** 
   * Channel related    
   ***********************************************************/
  public Object visitChannelPara(ChannelPara term) {
    //TODO: Change this to CIRCUS for \begin{circus} at some point.
    print(TokenName.ZED);
    visit(term.getDeclList());    
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
      visit(term.getNameList());      
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

  public Object visitCircusChannelSet(CircusChannelSet term) {
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
  
  /**
   * The AstToPrintTreeVisitor must have changed OnTheFly paragraphs 
   * from ProcessPara to a special form of action call.
   */
  public Object visitProcessPara(ProcessPara term) {
    // TODO: Check here when we have unboxed versions.
    print(TokenName.ZED);
    print(CircusKeyword.CIRCPROC);
    printGenericFormals(term.getGenFormals());
    visit(term.getProcessName());
    print(CircusKeyword.CIRCDEF);
    visit(term.getCircusProcess());    
    print(TokenName.END);
    return null;
  }

  public Object visitBasicProcess(BasicProcess term) {
    throw new UnsupportedOperationException("not yet!");
  }
  
  public Object visitCallProcess(CallProcess term) {
    printLPAREN(term);
    if (!isOnTheFly(term)) {
      visit(term.getCallExpr());            
      printActualParams(term.getZActuals(), 
          CallKind.Index.equals(term.getCallKind()));          
    } else {
      throw new PrintException("On-the-fly process calls must be processed by the AstToPrintTreeVisitor.");
    }
    printRPAREN(term);
    return null;
  }

  public Object visitHideProcess(HideProcess term) {
    printLPAREN(term);
    visit(term.getCircusProcess());
    print(CircusKeyword.CIRCHIDING);
    visit(term.getChannelSet());
    printRPAREN(term);
    return null;
  }
  
  public Object visitRenameProcess(RenameProcess term) {    
    visit(term.getCircusProcess());
    print(CircusToken.LCIRCRENAME);
    visit(term.getAssignmentPairs());
    print(CircusToken.RCIRCRENAME);    
    return null;
  }

  public Object visitSeqProcess(SeqProcess term) {
    printLPAREN(term);
    visit(term.getLeftProc());
    print(CircusKeyword.CIRCSEQ);
    visit(term.getRightProc());
    printRPAREN(term);
    return null;
  }

  public Object visitExtChoiceProcess(ExtChoiceProcess term) {
    printLPAREN(term);
    visit(term.getLeftProc());
    print(CircusKeyword.EXTCHOICE);
    visit(term.getRightProc());
    printRPAREN(term);
    return null;
  }

  public Object visitIntChoiceProcess(IntChoiceProcess term) {
    printLPAREN(term);
    visit(term.getLeftProc());
    print(CircusKeyword.INTCHOICE);
    visit(term.getRightProc());
    printRPAREN(term);
    return null;
  }

  public Object visitParallelProcess(ParallelProcess term) {
    printLPAREN(term);
    visit(term.getLeftProc());
    print(CircusToken.LPAR);
    visit(term.getChannelSet());
    print(CircusToken.RPAR);
    visit(term.getRightProc());
    printRPAREN(term);
    return null;
  }
  
  public Object visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term) {
    printLPAREN(term);
    visit(term.getLeftProc());
    print(CircusToken.LPAR);
    visit(term.getLeftAlpha());
    print(Keyword.BAR);
    visit(term.getRightAlpha());
    print(CircusToken.RPAR);
    visit(term.getRightProc());
    printRPAREN(term);
    return null;
  }

  public Object visitInterleaveProcess(InterleaveProcess term) {
    printLPAREN(term);
    visit(term.getLeftProc());    
    print(CircusKeyword.INTERLEAVE);
    visit(term.getRightProc());
    printRPAREN(term);
    return null;
  }   
  
  public Object visitParamProcess(ParamProcess term) {
    printProcessD(term, false);
    return null;
  }

  public Object visitSeqProcessIte(SeqProcessIte term) {
    /* For replicated sequential composition, we have no choice but to use ZCOMP 
     * as there are no unicode left :(. We also allow printing the keyword before
     * checking for on-the-fly as it does not matter where the printer breaks.
     */
    print(Keyword.ZCOMP);
    printProcessD(term, false);
    return null;
  }

  public Object visitExtChoiceProcessIte(ExtChoiceProcessIte term) {    
    print(CircusKeyword.REPEXTCHOICE);
    printProcessD(term, false);
    return null;
  }

  public Object visitIntChoiceProcessIte(IntChoiceProcessIte term) {
    print(CircusKeyword.REPINTCHOICE);
    printProcessD(term, false);
    return null;
  }

  public Object visitParallelProcessIte(ParallelProcessIte term) {    
    /* Just like printProcessD, but with the channel set*/
    if (!isOnTheFly(term)) {
      print(CircusKeyword.REPPARALLEL);
      printFormalParameters(term.getZDeclList());
      print(CircusToken.LPAR);
      visit(term.getChannelSet());
      print(CircusToken.RPAR);
      print(Keyword.SPOT);
      visit(term.getCircusProcess());
    } else {
      throw new PrintException("On-the-fly replicated parallel process must be processed by the AstToPrintTreeVisitor.");
    }
    return null;
  }

  public Object visitAlphabetisedParallelProcessIte(AlphabetisedParallelProcessIte term) {    
    throw new PrintException("This AlphabetisedParallelProcessIte terms are to be removed from the AST.");
  }
  
  public Object visitInterleaveProcessIte(InterleaveProcessIte term) {
    print(CircusKeyword.REPINTERLEAVE);
    printProcessD(term, false);
    return null;
  }
  
  public Object visitIndexedProcess(IndexedProcess term) {
    printProcessD(term, false);
    return null;
  }

  public Object visitSeqProcessIdx(SeqProcessIdx term) {
    print(Keyword.ZCOMP);
    printProcessD(term, true);
    return null;
  }

  public Object visitExtChoiceProcessIdx(ExtChoiceProcessIdx term) {
    print(CircusKeyword.REPEXTCHOICE);
    printProcessD(term, true);
    return null;
  }

  public Object visitIntChoiceProcessIdx(IntChoiceProcessIdx term) {
    print(CircusKeyword.REPINTCHOICE);
    printProcessD(term, true);
    return null;
  }

  public Object visitParallelProcessIdx(ParallelProcessIdx term) {
    /* Just like printProcessD, but with the channel set*/
    if (!isOnTheFly(term)) {
      print(CircusKeyword.REPPARALLEL);
      printFormalParameters(term.getZDeclList());
      print(CircusToken.LPAR);
      visit(term.getChannelSet());
      print(CircusToken.RPAR);
      print(CircusKeyword.CIRCINDEX);
      visit(term.getCircusProcess());
    } else {
      throw new PrintException("On-the-fly indexed parallel process must be processed by the AstToPrintTreeVisitor.");
    }
    return null;
  }

  public Object visitAlphabetisedParallelProcessIdx(AlphabetisedParallelProcessIdx term) {
    throw new PrintException("This AlphabetisedParallelProcessIdx terms are to be removed from the AST.");
  }

  public Object visitInterleaveProcessIdx(InterleaveProcessIdx term) {
    print(CircusKeyword.REPINTERLEAVE);
    printProcessD(term, true);
    return null;
  }
  
  /*********************************************************** 
   * Action related    
   ***********************************************************/
  
  public Object visitActionPara(ActionPara term) {
    visit(term.getName());
    print(CircusKeyword.CIRCDEF);
    visit(term.getCircusAction());    
    return null;
  }

  public Object visitSchExprAction(SchExprAction term) {
    if (!isOnTheFly(term)) {
      print(CircusToken.LSCHEXPRACT);
      visit(term.getExpr());
      print(CircusToken.RSCHEXPRACT);
    } else {
      // On-the-fly state need no special brackets.
      visit(term.getExpr());
    }
    return null;
  }
  
  public Object visitChaosAction(ChaosAction term) {    
    // Ignore parenthesied annotations here
    print(CircusKeyword.CIRCCHAOS);
    return null;
  }

  public Object visitSkipAction(SkipAction term) {
    // Ignore parenthesied annotations here
    print(CircusKeyword.CIRCSKIP);
    return null;
  }
  
  public Object visitStopAction(StopAction term) {
    // Ignore parenthesied annotations here
    print(CircusKeyword.CIRCSTOP);
    return null;
  }
  
  public Object visitMuAction(MuAction term) {
    printLPAREN(term);
    print(CircusKeyword.CIRCMU);
    visit(term.getName());
    print(Keyword.SPOT);
    visit(term.getCircusAction());
    printRPAREN(term);
    return null;
  }   

  public Object visitCallAction(CallAction term) {
    printLPAREN(term);
    if (!isOnTheFly(term)) {
      visit(term.getName());                  
      printActualParams(term.getZExprList(), false);//not indexes
    } else {
      throw new PrintException("On-the-fly action calls must be processed by the AstToPrintTreeVisitor.");
    }
    printRPAREN(term);
    return null;
  }  
  
  public Object visitHideAction(HideAction term) {
    printLPAREN(term);
    visit(term.getCircusAction());
    print(CircusKeyword.CIRCHIDING);
    visit(term.getChannelSet());
    printRPAREN(term);
    return null;
  }
  
  public Object visitSubstitutionAction(SubstitutionAction term) {
    visit(term.getCircusAction());
    print(TokenName.LSQUARE);
    visit(term.getRenameList());
    print(TokenName.RSQUARE);        
    return null;
  }

  public Object visitGuardedAction(GuardedAction term) {
    printLPAREN(term);
    print(CircusToken.LCIRCGUARD);
    visit(term.getPred());
    print(CircusToken.RCIRCGUARD);
    // Similar to replicated sequential composition, we need to reuse
    // the guard symbol, as there are no other good unicode char match.
    print(Keyword.ANDALSO);
    visit(term.getCircusAction());
    printRPAREN(term);
    return null;
  }

  public Object visitPrefixingAction(PrefixingAction term) {
    printLPAREN(term);
    visit(term.getCommunication());
    print(CircusKeyword.PREFIXTHEN);
    visit(term.getCircusAction());
    printRPAREN(term);
    return null;
  }

  public Object visitCommunication(Communication term) {    
    //boolean needHardSpace = term.getChannelExpr().getZExprList().isEmpty();
    visit(term.getChannelExpr());
    printDecorword("~");//hard space please
    visit(term.getFieldList());
    return null;
  }
  
  public Object visitOutputField(OutputField term) {
    print(TokenName.OUTSTROKE);
    visit(term.getExpr());
    return null;
  }

  public Object visitDotField(DotField term) {
    print(Keyword.DOT);
    visit(term.getExpr());    
    return null;
  }

  public Object visitInputField(InputField term) {
    print(TokenName.INSTROKE);    
    visit(term.getVariable());
    if (term.getRestriction() != null && !(term.getRestriction() instanceof TruePred)) {
      print(CircusKeyword.PREFIXCOLON);
      visit(term.getRestriction());
    }
    return null;
  }
  
  public Object visitSeqAction(SeqAction term) {
    printLPAREN(term);
    visit(term.getLeftAction());
    print(CircusKeyword.CIRCSEQ);
    visit(term.getRightAction());
    printRPAREN(term);
    return null;
  }

  public Object visitExtChoiceAction(ExtChoiceAction term) {
    printLPAREN(term);
    visit(term.getLeftAction());
    print(CircusKeyword.EXTCHOICE);
    visit(term.getRightAction());
    printRPAREN(term);
    return null;
  }
  
  public Object visitIntChoiceAction(IntChoiceAction term) {
    printLPAREN(term);
    visit(term.getLeftAction());
    print(CircusKeyword.INTCHOICE);
    visit(term.getRightAction());
    printRPAREN(term);
    return null;
  }
  
  public Object visitParallelAction(ParallelAction term) {
    // TODO: Add the simplified version when the namesets are empty.
    printLPAREN(term);
    visit(term.getLeftAction());
    print(CircusToken.LPAR);
    visit(term.getLeftNameSet());
    print(Keyword.BAR);    
    visit(term.getChannelSet());    
    print(Keyword.BAR);    
    visit(term.getRightNameSet());    
    print(CircusToken.RPAR);
    visit(term.getRightAction());
    printRPAREN(term);
    return null;
  }

  public Object visitAlphabetisedParallelAction(AlphabetisedParallelAction term) {
    // TODO: Add the simplified version when the namesets are empty.
    printLPAREN(term);
    visit(term.getLeftAction());
    print(CircusToken.LPAR);
    visit(term.getLeftAlpha());
    print(Keyword.BAR);
    visit(term.getRightAlpha());
    print(CircusToken.RPAR);
    visit(term.getRightAction());
    printRPAREN(term);
    return null;
  }

  public Object visitInterleaveAction(InterleaveAction term) {
    // TODO: Add the simplified version when the namesets are empty.
    printLPAREN(term);
    visit(term.getLeftAction());
    print(CircusToken.LINTER);
    visit(term.getLeftNameSet());
    print(Keyword.BAR);    
    visit(term.getRightNameSet());
    print(CircusToken.RINTER);
    visit(term.getRightAction());
    printRPAREN(term);
    return null;
  }  

  public Object visitParamAction(ParamAction term) {    
    printActionD(term);
    return null;
  }

  public Object visitSeqActionIte(SeqActionIte term) {
    print(Keyword.ZCOMP);
    printActionD(term);
    return null;
  }

  public Object visitExtChoiceActionIte(ExtChoiceActionIte term) {
    print(CircusKeyword.REPEXTCHOICE);
    printActionD(term);
    return null;
  }

  public Object visitIntChoiceActionIte(IntChoiceActionIte term) {
    print(CircusKeyword.REPINTCHOICE);
    printActionD(term);
    return null;
  }

  public Object visitParallelActionIte(ParallelActionIte term) {
    /* Just like printActionD, but with the channel set*/
    if (!isOnTheFly(term)) {
      // TODO: Add the simplified version when the namesets are empty.
      print(CircusToken.LPAR);
      visit(term.getChannelSet());
      print(CircusToken.RPAR);
      printFormalParameters(term.getZDeclList());
      print(Keyword.SPOT);
      print(CircusToken.LPAR);
      visit(term.getNameSet());
      print(CircusToken.RPAR);      
      visit(term.getCircusAction());
    } else {
      throw new PrintException("On-the-fly replicated parallel action must be processed by the AstToPrintTreeVisitor.");
    }
    return null;
  }

  public Object visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term) {
    throw new PrintException("This AlphabetisedParallelActionIte terms are to be removed from the AST.");    
  }
     
  public Object visitInterleaveActionIte(InterleaveActionIte term) {    
    if (!isOnTheFly(term)) {
      // TODO: Add the simplified version when the namesets are empty.
      print(CircusKeyword.REPINTERLEAVE);    
      printFormalParameters(term.getZDeclList());      
      print(CircusToken.LINTER);
      visit(term.getNameSet());
      print(CircusToken.RINTER);      
      print(Keyword.SPOT);      
      visit(term.getCircusAction());
    } else {
      throw new PrintException("On-the-fly replicated interleave action must be processed by the AstToPrintTreeVisitor.");
    }
    return null;
  }
  
  /*********************************************************** 
   * Command related    
   ***********************************************************/
  
  public Object visitVarDeclCommand(VarDeclCommand term) {
    printLPAREN(term);
    print(CircusKeyword.CIRCVAR);
    visit(term.getDeclList());
    print(Keyword.SPOT);
    visit(term.getCircusAction());
    printRPAREN(term);
    return null;
  }
  
  public Object visitAssignmentCommand(AssignmentCommand term) {
    printLPAREN(term);
    visit(term.getAssignmentPairs());
    printRPAREN(term);
    return null;
  }

  public Object visitIfGuardedCommand(IfGuardedCommand term) {
    printLPAREN(term);
    print(Keyword.IF);     
    Iterator<GuardedAction> it = term.getGuardedAction().iterator();
    while (it.hasNext()) {
      GuardedAction ga = it.next();            
      visit(ga.getPred());
      print(CircusKeyword.CIRCTHEN);
      visit(ga.getCircusAction());
      if (it.hasNext()) {                
        print(TokenName.NL);
        print(CircusKeyword.CIRCELSE);        
      }
    }
    // For a single guard, let the if on the same line as the fi
    if (term.getGuardedAction().size() > 1) {
      print(TokenName.NL);
    }    
    print(CircusKeyword.CIRCFI);
    printRPAREN(term);
    return null;
  }

  public Object visitSpecStmtCommand(SpecStmtCommand term) {
    printLPAREN(term);
    if (term.getZFrame().isEmpty()) {
      // Assumption
      if (term.getPost() instanceof TruePred) {
        print(TokenName.LBRACE);
        visit(term.getPre());
        print(TokenName.RBRACE);
      } 
      // Coercion
      else if (term.getPre() instanceof TruePred) {
        print(TokenName.LSQUARE);
        visit(term.getPost());
        print(TokenName.RSQUARE);
      } 
      // Specification stamement with empty frame
      else {
        print(Keyword.COLON);        
        print(TokenName.LSQUARE);
        visit(term.getPre());
        print(Keyword.COMMA);
        visit(term.getPost());
        print(TokenName.RSQUARE);
      }
    } 
    // Specification statement with non-empty frame
    else {
      visit(term.getFrame());
      print(Keyword.COLON);        
      print(TokenName.LSQUARE);
      visit(term.getPre());
      print(Keyword.COMMA);
      visit(term.getPost());
      print(TokenName.RSQUARE);
    }        
    printRPAREN(term);
    return null;
  }  
  
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
  
  public Object visitOnTheFlyDefAnn(OnTheFlyDefAnn term) {
    /* TODO: Annotations need special treatment, see ZPrintVisitor */
    throw new UnsupportedOperationException("Unexpected term OnTheFlyDefAnn.");    
  }  
  
  public Object visitLetMuAction(LetMuAction term) {
    throw new UnsupportedOperationException("Unexpected term LetMuAction.");    
  }  
  
  public Object visitLetVarAction(LetVarAction term) {
    throw new UnsupportedOperationException("Unexpected term LetVarAction.");    
  }  

  /*********************************************************** 
   * Others 
   ***********************************************************/
   
  public Object visitRefinementConjPara(RefinementConjPara term) {
    print(CircusToken.LCIRCGUARD);
    visit(term.getSpecification());
    print(CircusKeyword.CIRCREFINES);
    if (!term.getModel().equals(Model.FlDv)) {
      printDecorword(term.getModel() + "~");
    }
    visit(term.getImplementation());
    print(CircusToken.RCIRCGUARD);    
    return null;
  }
    
  public Object visitQualifiedDecl(QualifiedDecl term) {        
    if (ParamQualifier.Result.equals(term.getParamQualifier())) {            
      print(CircusKeyword.CIRCRES);
    } else if (ParamQualifier.ValueResult.equals(term.getParamQualifier())) {      
      print(CircusKeyword.CIRCVRES);
    } /* else must be by value, so just don't put it */
    if (ZUtils.assertZNameList(term.getNameList()).isEmpty())
      throw new PrintException("Empty list of qualified variables/parameters");
    visit(term.getNameList());
    print(Keyword.COLON);
    visit(term.getExpr());
    return null;
  }

  public Object visitAssignmentPairs(AssignmentPairs term) {
    printTermList(term.getZLHS());
    print(CircusKeyword.CIRCASSIGN);
    printTermList(term.getZRHS());    
    return null;
  }

  public Object visitCircusFieldList(CircusFieldList term) {
    for(Field f : term) {
      visit(f);
    }
    return null;
  }

  public Object visitSigmaExpr(SigmaExpr term) {
    throw new UnsupportedOperationException("not yet!");
  }

  public Object visitNameSetPara(NameSetPara term) {
    /* Hum... need to know if it is boxed or not... */
    visit(term.getName());
    print(Keyword.DEFEQUAL);
    visit(term.getNameSet());
    return null;
  }
  
  public Object visitCircusNameSet(CircusNameSet term) {
    visit(term.getExpr());
    return null;
  }
}

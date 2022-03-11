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

package net.sourceforge.czt.print.circustime;

import java.util.Iterator;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.circus.visitor.CircusVisitor;
import net.sourceforge.czt.circustime.ast.PrefixingTimeAction;
import net.sourceforge.czt.circustime.ast.TimeEndByAction;
import net.sourceforge.czt.circustime.ast.TimeEndByProcess;
import net.sourceforge.czt.circustime.ast.TimeStartByAction;
import net.sourceforge.czt.circustime.ast.TimeStartByProcess;
import net.sourceforge.czt.circustime.ast.TimedinterruptAction;
import net.sourceforge.czt.circustime.ast.TimedinterruptProcess;
import net.sourceforge.czt.circustime.ast.TimeoutAction;
import net.sourceforge.czt.circustime.ast.TimeoutProcess;
import net.sourceforge.czt.circustime.ast.WaitAction;
import net.sourceforge.czt.circustime.ast.WaitExprAction;
import net.sourceforge.czt.parser.circus.CircusKeyword;
import net.sourceforge.czt.parser.circus.CircusToken;
import net.sourceforge.czt.parser.circustime.CircusTimeKeyword;
import net.sourceforge.czt.parser.circustime.CircusTimeToken;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.util.WarningManager;
import net.sourceforge.czt.z.util.ZUtils;
//import net.sourceforge.czt.parser.circustime.CircusTimeToken;

/**
 * An Circus visitor used for printing.
 *
 * @author Petra Malik, Leo Freitas
 */
public class CircusTimePrintVisitor
    extends net.sourceforge.czt.print.z.ZPrintVisitor
    implements CircusVisitor<Object> {
    
    private final WarningManager warningManager_;
    
    /**
     * Creates a new Object-Z print visitor.
     * The section information should be able to provide information of
     * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
     */
    public CircusTimePrintVisitor(SectionInfo si, ZPrinter printer, WarningManager wm) {
        super(si, printer);
        warningManager_ = wm;
    }
    
    public CircusTimePrintVisitor(SectionInfo si, ZPrinter printer, Properties properties, WarningManager wm) {
        super(si, printer, properties);
        warningManager_ = wm;
    }
    
    /***********************************************************
     * Auxiliary methods
     ***********************************************************/
    
    protected void print(CircusKeyword keyword) {
        /* CIRCDEF is the only keyword that is a scanner token */
        if (keyword.equals(CircusKeyword.CIRCDEF))
            print((Token) keyword);
        else
            printDecorword(keyword.spelling());
    }
    
    private void printActualParams(ZExprList term, boolean indexes) {
        if (term != null && !term.isEmpty()) {
            print(indexes ? CircusToken.CIRCLINST : ZToken.LPAREN);
            visit(term);
            print(indexes ? CircusToken.CIRCRINST : ZToken.RPAREN);
        }
    }
    
    protected void printFormalParameters(ZDeclList term) {
        assert term != null;
        if (term.isEmpty())
            throw new CztException(new PrintException(getSectionInfo().getDialect(), "Empty formal parameters list."));
        visit(term);
    }
    
    protected void printProcessD(ProcessD term, boolean indexes) {
        if (!CircusUtils.isOnTheFly(term)) {
            printFormalParameters(term.getZDeclList());
            print(indexes ? CircusKeyword.CIRCINDEX : CircusKeyword.CIRCSPOT);
            visit(term.getCircusProcess());
        } else {
            throw new CztException(new PrintException(getSectionInfo().getDialect(), "On-the-fly parameterised process (" +
                term.getClass().getSimpleName() + ") must be processed by the AstToPrintTreeVisitor."));
        }
    }
    
    protected void printActionD(ActionD term) {
        if (!CircusUtils.isOnTheFly(term)) {
            printFormalParameters(term.getZDeclList());
            print(CircusKeyword.CIRCSPOT);
            visit(term.getCircusAction());
        } else {
            throw new CztException(new PrintException(getSectionInfo().getDialect(), "On-the-fly parameterised action (" +
                term.getClass().getSimpleName() + ") must be processed by the AstToPrintTreeVisitor."));
        }
    }
    
    private void warn(CircusTimePrintMessage cpm, Object... arguments) {
        warningManager_.warn(cpm.getMessage(), arguments);
    }
    
    private void warnUnexpectedTerm(Term term)
    {
      warn(CircusTimePrintMessage.MSG_UNEXPECTED_TERM, term);
    }
    
//    private void warnMissingFor(String msg, BasicProcess term) {
//        warn(CircusTimePrintMessage.MSG_BASIC_PROCESS_MISSING_ENTITY, msg, term);
//    }
//    
//    private void warnBadParagraphFor(String msg, Para para, BasicProcess term) {
//        warn(CircusTimePrintMessage.MSG_BASIC_PROCESS_BAD_PARAGRAPH, msg, para, term);
//    }
//    
//    private void warnLocalOnTheFly(Term para, BasicProcess term) {
//        warn(CircusTimePrintMessage.MSG_BASIC_PROCESS_LOCAL_ONTHEFLY_PARAGRAPH, para, term);
//    }
//    
//    private void warnDuplicatedState(Term term) {
//        warn(CircusTimePrintMessage.MSG_BASIC_PROCESS_DUPLICATED_STATE_PARAGRAPH, term);
//    }
//    
//    private boolean processedState_ = false;
    
    /***********************************************************
     * Channel related
     ***********************************************************/
    @Override
	public Object visitChannelPara(ChannelPara term) {
        //TODO: Change this to CIRCUS for \begin{circus} at some point.
        print(ZToken.ZED);
        visit(term.getDeclList());
        print(ZToken.END);
        return null;
    }
    
    @Override
	public Object visitChannelDecl(ChannelDecl term) {
//        if (CircusUtils.isChannelFromDecl(term)) {
//            print(CircusKeyword.CIRCCHANFROM);
//            printGenericFormals(term.getNameList().get(0));
//            assert term.getExpr() != null;
//            visit(term.getExpr());
//        } else {
            print(CircusKeyword.CIRCCHAN);
            printGenericFormals(term.getNameList().get(0));
            visit(term.getNameList().get(1));
            if (term.getExpr() != null) {
                print(ZKeyword.COLON);
                visit(term.getExpr());
            }
//        }
        print(ZToken.NL);
        return null;
    }
    
    /***********************************************************
     * Channel set related
     ***********************************************************/
    @Override
	public Object visitChannelSetPara(ChannelSetPara term) {
        print(ZToken.ZED);
        print(CircusKeyword.CIRCCHANSET);
        printGenericFormals(term.getGenFormals());
        visit(term.getName());
        print(ZKeyword.DEFEQUAL);
        visit(term.getChannelSet());
        print(ZToken.END);
        return null;
    }
    
    @Override
	public Object visitCircusChannelSet(CircusChannelSet term) {
        visit(term.getExpr());
        return null;
    }
    
    @Override
	public Object visitBasicChannelSetExpr(BasicChannelSetExpr term) {
        print(CircusToken.LCIRCCHANSET);
        printTermList(term.getCircusCommunicationList());
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
    @Override
	public Object visitProcessPara(ProcessPara term) {
        throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term ProcessPara"));
      /*
    // TODO: Check here when we have unboxed versions.
    print(ZToken.ZED);
    print(CircusKeyword.CIRCPROC);
    printGenericFormals(term.getGenFormals());
    visit(term.getProcessName());
    print(CircusKeyword.CIRCDEF);
    boolean isBasicProcess = (term.getCircusProcess() instanceof BasicProcess);
       
    // basic processes will be spread across different environments
    if (isBasicProcess) {
        print(CircusKeyword.CIRCBEGIN);
        print(ZToken.END);
        print(ZToken.NL);
    }
    visit(term.getCircusProcess());
       
    // close the environment for either CIRCEND (basic) or normal processes.
    print(ZToken.END);
    return null;*/
    }
    
    @Override
	public Term visitBasicProcess(BasicProcess term) {
      warnUnexpectedTerm(term);
      return null;
        //throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term BasicProcess"));
    /*
    processedState_ = false;
    boolean hasState = (term.getStatePara() != null);
     
    // basic process state is part of either implicitly declared or local paras
    if (!hasState) {
        // it should not be null if term was created by the parser!
        // thus, raise an warning!
        warnMissingFor("process state", term);
    }
     
    // locally declared paragraph within basic process
    for (Iterator<Para> iter = term.getZLocalPara().iterator();
           iter.hasNext();) {
        Para next = iter.next();
     
        // local para cannot be on-the-fly
        if (CircusUtils.isOnTheFly(next)) {
            warnLocalOnTheFly(next, term);
        } else if (CircusUtils.isStatePara(next)) {
            // if it is state, it can only appear once
            if (processedState_) {
                warnDuplicatedState(next);
            } else {
                // is must be an horizontal definition, as in name == sch-expr
                // see Parser.xml circusProcessState production for details
                assert ZUtils.isHorizontalSchema(next) : "Inconsistent CircusStateAnn for basic process paragrph " + next;
                processedState_ = true;
     
                // since it is an horizontal schema, we must add a circus environment for it
                print(CircusToken.CIRCUSACTION);
                print(CircusKeyword.CIRCSTATE);
                visit(next);
                print(ZToken.END);
                if (iter.hasNext()) print(ZToken.NL);
            }
        } else {
            visit(next);
            if (iter.hasNext()) print(ZToken.NL);
        }
    }
     
    // implicitly declared action paragraphs
    for (Iterator<Para> iter = term.getZOnTheFlyPara().iterator();
           iter.hasNext();) {
        Para next = iter.next();
        if (next instanceof ActionPara) {
            visit(next);
            if (iter.hasNext()) print(ZToken.NL);
        } else {
            warnBadParagraphFor("Implicitly", next, term);
        }
    }
     
    if (term.getMainAction() != null) {
        print(CircusToken.CIRCUSACTION);
        print(CircusKeyword.CIRCSPOT);
        visit(term.getMainAction());
        print(ZToken.NL);
    } else {
        warnMissingFor("main action", term);
    }
    if (hasState && !processedState_) {
        warnMissingFor("locally or implicitly declared process state", term);
    }
     
    print(ZToken.ZED);
    print(CircusKeyword.CIRCEND);
    // the environment closure is done at ProcessPara above
     
    return null;*/
    }
    
    @Override
	public Object visitCallProcess(CallProcess term) {
        printLPAREN(term);
        if (!CircusUtils.isOnTheFly(term)) {
            visit(term.getCallExpr());
            printActualParams(term.getZActuals(),
                CallUsage.Indexed.equals(term.getCallUsage()));
        } else {
            throw new CztException(new PrintException(getSectionInfo().getDialect(), "On-the-fly process calls must be processed by the AstToPrintTreeVisitor."));
        }
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitHideProcess(HideProcess term) {
        printLPAREN(term);
        visit(term.getCircusProcess());
        print(CircusKeyword.CIRCHIDING);
        visit(term.getChannelSet());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitRenameProcess(RenameProcess term) {
        visit(term.getCircusProcess());
        print(CircusToken.LCIRCRENAME);
        visit(term.getAssignmentPairs());
        print(CircusToken.RCIRCRENAME);
        return null;
    }
    
    @Override
	public Object visitSeqProcess(SeqProcess term) {
        printLPAREN(term);
        visit(term.getLeftProcess());
        print(CircusKeyword.CIRCSEQ);
        visit(term.getRightProcess());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitExtChoiceProcess(ExtChoiceProcess term) {
        printLPAREN(term);
        visit(term.getLeftProcess());
        print(CircusKeyword.EXTCHOICE);
        visit(term.getRightProcess());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitIntChoiceProcess(IntChoiceProcess term) {
        printLPAREN(term);
        visit(term.getLeftProcess());
        print(CircusKeyword.INTCHOICE);
        visit(term.getRightProcess());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitParallelProcess(ParallelProcess term) {
        printLPAREN(term);
        visit(term.getLeftProcess());
        print(CircusToken.LPAR);
        visit(term.getChannelSet());
        print(CircusToken.RPAR);
        visit(term.getRightProcess());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term) {
        printLPAREN(term);
        visit(term.getLeftProcess());
        print(CircusToken.LPAR);
        visit(term.getLeftAlpha());
        print(ZKeyword.BAR);
        visit(term.getRightAlpha());
        print(CircusToken.RPAR);
        visit(term.getRightProcess());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitInterleaveProcess(InterleaveProcess term) {
        printLPAREN(term);
        visit(term.getLeftProcess());
        print(CircusKeyword.INTERLEAVE);
        visit(term.getRightProcess());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitParamProcess(ParamProcess term) {
        printProcessD(term, false);
        return null;
    }
    
    @Override
	public Object visitSeqProcessIte(SeqProcessIte term) {
    /* For replicated sequential composition, we have no choice but to use ZCOMP
     * as there are no unicode left :(. We also allow printing the keyword before
     * checking for on-the-fly as it does not matter where the printer breaks.
     */
        print(ZKeyword.ZCOMP);
        printProcessD(term, false);
        return null;
    }
    
    @Override
	public Object visitExtChoiceProcessIte(ExtChoiceProcessIte term) {
        print(CircusKeyword.REPEXTCHOICE);
        printProcessD(term, false);
        return null;
    }
    
    @Override
	public Object visitIntChoiceProcessIte(IntChoiceProcessIte term) {
        print(CircusKeyword.REPINTCHOICE);
        printProcessD(term, false);
        return null;
    }
    
    @Override
	public Object visitParallelProcessIte(ParallelProcessIte term) {
        /* Just like printProcessD, but with the channel set*/
        if (!CircusUtils.isOnTheFly(term)) {
            print(CircusKeyword.REPPARALLEL);
            printFormalParameters(term.getZDeclList());
            print(CircusToken.LPAR);
            visit(term.getChannelSet());
            print(CircusToken.RPAR);
            print(CircusKeyword.CIRCSPOT);
            visit(term.getCircusProcess());
        } else {
            throw new CztException(new PrintException(getSectionInfo().getDialect(), "On-the-fly replicated parallel process must be processed by the AstToPrintTreeVisitor."));
        }
        return null;
    }
    
    @Override
	public Object visitAlphabetisedParallelProcessIte(AlphabetisedParallelProcessIte term) {
        throw new CztException(new PrintException(getSectionInfo().getDialect(), "This AlphabetisedParallelProcessIte terms are to be removed from the AST."));
    }
    
    @Override
	public Object visitInterleaveProcessIte(InterleaveProcessIte term) {
        print(CircusKeyword.REPINTERLEAVE);
        printProcessD(term, false);
        return null;
    }
    
    @Override
	public Object visitIndexedProcess(IndexedProcess term) {
        printProcessD(term, false);
        return null;
    }
    
    @Override
	public Object visitSeqProcessIdx(SeqProcessIdx term) {
        print(ZKeyword.ZCOMP);
        printProcessD(term, true);
        return null;
    }
    
    @Override
	public Object visitExtChoiceProcessIdx(ExtChoiceProcessIdx term) {
        print(CircusKeyword.REPEXTCHOICE);
        printProcessD(term, true);
        return null;
    }
    
    @Override
	public Object visitIntChoiceProcessIdx(IntChoiceProcessIdx term) {
        print(CircusKeyword.REPINTCHOICE);
        printProcessD(term, true);
        return null;
    }
    
    @Override
	public Object visitParallelProcessIdx(ParallelProcessIdx term) {
        /* Just like printProcessD, but with the channel set*/
        if (!CircusUtils.isOnTheFly(term)) {
            print(CircusKeyword.REPPARALLEL);
            printFormalParameters(term.getZDeclList());
            print(CircusToken.LPAR);
            visit(term.getChannelSet());
            print(CircusToken.RPAR);
            print(CircusKeyword.CIRCINDEX);
            visit(term.getCircusProcess());
        } else {
            throw new CztException(new PrintException(getSectionInfo().getDialect(), "On-the-fly indexed parallel process must be processed by the AstToPrintTreeVisitor."));
        }
        return null;
    }
    
    @Override
	public Object visitAlphabetisedParallelProcessIdx(AlphabetisedParallelProcessIdx term) {
        throw new CztException(new PrintException(getSectionInfo().getDialect(), "This AlphabetisedParallelProcessIdx terms are to be removed from the AST."));
    }
    
    @Override
	public Object visitInterleaveProcessIdx(InterleaveProcessIdx term) {
        print(CircusKeyword.REPINTERLEAVE);
        printProcessD(term, true);
        return null;
    }
    
    /***********************************************************
     * Action related
     ***********************************************************/
    
    @Override
	public Object visitActionPara(ActionPara term) {
      warnUnexpectedTerm(term);
      return null;
        //throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term ActionPara"));
   /* print(CircusToken.CIRCUSACTION);
    if (CircusUtils.isStatePara(term)) {
        if (processedState_) {
            warnDuplicatedState(term);
        } else {
            assert CircusUtils.isOnTheFly(term) : "Action para marked as basic process state but not as on-the-fly. PARSER-BUG";
            processedState_ = true;
            print(CircusKeyword.CIRCSTATE);
            visit(term.getCircusAction());
        }
    } else {
        visit(term.getName());
        print(CircusKeyword.CIRCDEF);
        visit(term.getCircusAction());
    }
    print(ZToken.END);
    return null;*/
    }
    
    @Override
	public Object visitSchExprAction(SchExprAction term) {
        if (!CircusUtils.isOnTheFly(term)) {
            print(CircusToken.LSCHEXPRACT);
            visit(term.getExpr());
            print(CircusToken.RSCHEXPRACT);
        } else {
            // On-the-fly state need no special brackets.
            visit(term.getExpr());
        }
        return null;
    }
    
    @Override
	public Object visitChaosAction(ChaosAction term) {
        // Ignore parenthesied annotations here
        print(CircusKeyword.CIRCCHAOS);
        return null;
    }
    
    @Override
	public Object visitSkipAction(SkipAction term) {
        // Ignore parenthesied annotations here
        print(CircusKeyword.CIRCSKIP);
        return null;
    }
    
    @Override
	public Object visitStopAction(StopAction term) {
        // Ignore parenthesied annotations here
        print(CircusKeyword.CIRCSTOP);
        return null;
    }
    
    @Override
	public Object visitMuAction(MuAction term) {
        printLPAREN(term);
        print(CircusKeyword.CIRCMU);
        visit(term.getName());
        print(CircusKeyword.CIRCSPOT);
        visit(term.getCircusAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitCallAction(CallAction term) {
        printLPAREN(term);
//        if (!CircusUtils.isOnTheFly(term)) {
            visit(term.getName());
            printActualParams(term.getZExprList(), false);//not indexes
//        } else {
//            throw new CztException(new PrintException(getSectionInfo().getDialect(), "On-the-fly action calls must be processed by the AstToPrintTreeVisitor."));
//        }
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitHideAction(HideAction term) {
        printLPAREN(term);
        visit(term.getCircusAction());
        print(CircusKeyword.CIRCHIDING);
        visit(term.getChannelSet());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitRenameAction(RenameAction term) {
        visit(term.getCircusAction());
        print(CircusToken.LCIRCRENAME);
        visit(term.getAssignmentPairs());
        print(CircusToken.RCIRCRENAME);
        return null;
    }
    
    @Override
	public Object visitSubstitutionAction(SubstitutionAction term) {
        visit(term.getCircusAction());
        print(ZToken.LSQUARE);
        visit(term.getRenameList());
        print(ZToken.RSQUARE);
        return null;
    }
    
    @Override
	public Object visitGuardedAction(GuardedAction term) {
        printLPAREN(term);
        print(CircusToken.LCIRCGUARD);
        visit(term.getPred());
        print(CircusToken.RCIRCGUARD);
        // Similar to replicated sequential composition, we need to reuse
        // the guard symbol, as there are no other good unicode char match.
        print(ZKeyword.ANDALSO);
        visit(term.getCircusAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitPrefixingAction(PrefixingAction term) {
        printLPAREN(term);
        visit(term.getCommunication());
        print(CircusKeyword.PREFIXTHEN);
        visit(term.getCircusAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitCommunication(Communication term) {
        //boolean needHardSpace = term.getChannelExpr().getZExprList().isEmpty();
        visit(term.getChannelExpr());      
        visit(term.getFieldList());
        return null;
    }
    
    public Object visitOutputField(OutputFieldAnn term) {
        return null;
    }
    
    @Override
	public Object visitDotField(DotField term) {        
        print(term.getAnn(OutputFieldAnn.class) != null ? ZToken.OUTSTROKE : ZKeyword.DOT);
        visit(term.getExpr());
        return null;
    }
    
    @Override
	public Object visitInputField(InputField term) {
        print(ZToken.INSTROKE);
        visit(term.getVariableName());
        if (term.getRestriction() != null && !(term.getRestriction() instanceof TruePred)) {
            print(CircusKeyword.PREFIXCOLON);
            visit(term.getRestriction());
        }
        return null;
    }
    
    @Override
	public Object visitSeqAction(SeqAction term) {
        printLPAREN(term);
        visit(term.getLeftAction());
        print(CircusKeyword.CIRCSEQ);
        visit(term.getRightAction());
        printRPAREN(term);
        return null;
    }

    @Override
	public Object visitInterruptAction(InterruptAction term) {
        printLPAREN(term);
        visit(term.getLeftAction());
        print(CircusKeyword.CIRCINTERRUPT);
        visit(term.getRightAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitExtChoiceAction(ExtChoiceAction term) {
        printLPAREN(term);
        visit(term.getLeftAction());
        print(CircusKeyword.EXTCHOICE);
        visit(term.getRightAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitIntChoiceAction(IntChoiceAction term) {
        printLPAREN(term);
        visit(term.getLeftAction());
        print(CircusKeyword.INTCHOICE);
        visit(term.getRightAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitParallelAction(ParallelAction term) {
        // TODO: Add the simplified version when the namesets are empty.
        printLPAREN(term);
        visit(term.getLeftAction());
        print(CircusToken.LPAR);
        visit(term.getLeftNameSet());
        print(ZKeyword.BAR);
        visit(term.getChannelSet());
        print(ZKeyword.BAR);
        visit(term.getRightNameSet());
        print(CircusToken.RPAR);
        visit(term.getRightAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitAlphabetisedParallelAction(AlphabetisedParallelAction term) {
        // TODO: Add the simplified version when the namesets are empty.
        printLPAREN(term);
        visit(term.getLeftAction());
        print(CircusToken.LPAR);
        visit(term.getLeftAlpha());
        print(ZKeyword.BAR);
        visit(term.getRightAlpha());
        print(CircusToken.RPAR);
        visit(term.getRightAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitInterleaveAction(InterleaveAction term) {
        // TODO: Add the simplified version when the namesets are empty.
        printLPAREN(term);
        visit(term.getLeftAction());
        print(CircusToken.LINTER);
        visit(term.getLeftNameSet());
        print(ZKeyword.BAR);
        visit(term.getRightNameSet());
        print(CircusToken.RINTER);
        visit(term.getRightAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitParamAction(ParamAction term) {
        printActionD(term);
        return null;
    }
    
    @Override
	public Object visitSeqActionIte(SeqActionIte term) {
        print(ZKeyword.ZCOMP);
        printActionD(term);
        return null;
    }
    
    @Override
	public Object visitExtChoiceActionIte(ExtChoiceActionIte term) {
        print(CircusKeyword.REPEXTCHOICE);
        printActionD(term);
        return null;
    }
    
    @Override
	public Object visitIntChoiceActionIte(IntChoiceActionIte term) {
        print(CircusKeyword.REPINTCHOICE);
        printActionD(term);
        return null;
    }
    
    @Override
	public Object visitParallelActionIte(ParallelActionIte term) {
        /* Just like printActionD, but with the channel set*/
        if (!CircusUtils.isOnTheFly(term)) {
            // TODO: Add the simplified version when the namesets are empty.
            print(CircusToken.LPAR);
            visit(term.getChannelSet());
            print(CircusToken.RPAR);
            printFormalParameters(term.getZDeclList());
            print(CircusKeyword.CIRCSPOT);
            print(CircusToken.LPAR);
            visit(term.getNameSet());
            print(CircusToken.RPAR);
            visit(term.getCircusAction());
        } else {
            throw new CztException(new PrintException(getSectionInfo().getDialect(), "On-the-fly replicated parallel action must be processed by the AstToPrintTreeVisitor."));
        }
        return null;
    }
    
    @Override
	public Object visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term) {
        throw new CztException(new PrintException(getSectionInfo().getDialect(), "This AlphabetisedParallelActionIte terms are to be removed from the AST."));
    }
    
    @Override
	public Object visitInterleaveActionIte(InterleaveActionIte term) {
        if (!CircusUtils.isOnTheFly(term)) {
            // TODO: Add the simplified version when the namesets are empty.
            print(CircusKeyword.REPINTERLEAVE);
            printFormalParameters(term.getZDeclList());
            print(CircusToken.LINTER);
            visit(term.getNameSet());
            print(CircusToken.RINTER);
            print(CircusKeyword.CIRCSPOT);
            visit(term.getCircusAction());
        } else {
            throw new CztException(new PrintException(getSectionInfo().getDialect(), "On-the-fly replicated interleave action must be processed by the AstToPrintTreeVisitor."));
        }
        return null;
    }
    
    /***********************************************************
     * Command related
     ***********************************************************/
    
    @Override
	public Object visitVarDeclCommand(VarDeclCommand term) {
        printLPAREN(term);
        print(CircusKeyword.CIRCVAR);
        visit(term.getDeclList());
        print(CircusKeyword.CIRCSPOT);
        visit(term.getCircusAction());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitAssignmentCommand(AssignmentCommand term) {
        printLPAREN(term);
        visit(term.getAssignmentPairs());
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitIfGuardedCommand(IfGuardedCommand term) {
        printLPAREN(term);
        print(ZKeyword.IF);
        Iterator<? extends CircusAction> it = term.getGuardedActionList().iterator();
        while (it.hasNext()) {            
            GuardedAction ga = (GuardedAction)it.next();
            visit(ga.getPred());
            print(CircusKeyword.CIRCTHEN);
            visit(ga.getCircusAction());
            if (it.hasNext()) {
                print(ZToken.NL);
                print(CircusKeyword.CIRCELSE);
            }
        }
        // For a single guard, let the if on the same line as the fi
        if (term.getGuardedActionList().size() > 1) {
            print(ZToken.NL);
        }
        print(CircusKeyword.CIRCFI);
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitDoGuardedCommand(DoGuardedCommand term) {
        printLPAREN(term);
        print(CircusKeyword.CIRCDO);
        Iterator<? extends CircusAction> it = term.getGuardedActionList().iterator();
        while (it.hasNext()) {            
            GuardedAction ga = (GuardedAction)it.next();
            visit(ga.getPred());
            print(CircusKeyword.CIRCTHEN);
            visit(ga.getCircusAction());
            if (it.hasNext()) {
                print(ZToken.NL);
                print(CircusKeyword.CIRCELSE);
            }
        }
        // For a single guard, let the if on the same line as the fi
        if (term.getGuardedActionList().size() > 1) {
            print(ZToken.NL);
        }
        print(CircusKeyword.CIRCOD);
        printRPAREN(term);
        return null;
    }
    
    @Override
	public Object visitSpecStmtCommand(SpecStmtCommand term) {
        printLPAREN(term);
        if (term.getZFrame().isEmpty()) {
            // Assumption
            if (term.getPost() instanceof TruePred) {
                print(ZToken.LBRACE);
                visit(term.getPre());
                print(ZToken.RBRACE);
            }
            // Coercion
            else if (term.getPre() instanceof TruePred) {
                print(ZToken.LSQUARE);
                visit(term.getPost());
                print(ZToken.RSQUARE);
            }
            // Specification stamement with empty frame
            else {
                print(ZKeyword.COLON);
                print(ZToken.LSQUARE);
                visit(term.getPre());
                print(ZKeyword.COMMA);
                visit(term.getPost());
                print(ZToken.RSQUARE);
            }
        }
        // Specification statement with non-empty frame
        else {
            visit(term.getFrame());
            print(ZKeyword.COLON);
            print(ZToken.LSQUARE);
            visit(term.getPre());
            print(ZKeyword.COMMA);
            visit(term.getPost());
            print(ZToken.RSQUARE);
        }
        printRPAREN(term);
        return null;
    }
    
    /***********************************************************
     * Unexpected terms
     ***********************************************************/
    
    @Override
	public Object visitChannelSetType(ChannelSetType term) {
        warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ChannelSetType.");
        return null;
    }
    
    @Override
	public Object visitProcessType(ProcessType term) {
        warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ProcessType.");
        return null;
    }
    
    @Override
	public Object visitActionType(ActionType term) {
        warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ActionType.");
        return null;
    }
    
    @Override
	public Object visitNameSetType(NameSetType term) {
        warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term NameSetType.");
        return null;
    }
    
    @Override
	public Object visitChannelType(ChannelType term) {
        warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ChannelType.");
        return null;
    }
    
    @Override
	public Object visitProcessSignature(ProcessSignature term) {
        warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ProcessSignature.");
        return null;
    }
    
    @Override
	public Object visitActionSignature(ActionSignature term) {
        warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ActionSignature.");
        return null;
    }
    
    @Override
	public Object visitCircusStateAnn(CircusStateAnn term) {
        warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term CircusStateAnn.");
        return null;
    }
    
    @Override
	public Object visitOnTheFlyDefAnn(OnTheFlyDefAnn term) {
        /* TODO: Annotations need special treatment, see ZPrintVisitor */
        //throw new UnsupportedOperationException("Unexpected term OnTheFlyDefAnn.");
      warnUnexpectedTerm(term);
      return null;
    }
    
    @Override
	public Object visitLetMuAction(LetMuAction term) {
        //throw new UnsupportedOperationException("Unexpected term LetMuAction.");
      warnUnexpectedTerm(term);
      return null;
    }
    
    @Override
	public Object visitLetVarAction(LetVarAction term) {
        //throw new UnsupportedOperationException("Unexpected term LetVarAction.");
      warnUnexpectedTerm(term);
      return null;
    }
    
    /***********************************************************
     * Others
     ***********************************************************/
    
    @Override
	public Object visitTransformerPara(TransformerPara term) {
        visit(term.getName());
        print(CircusKeyword.CIRCASSERTREF);        
        visit(term.getTransformerPred());        
        return null;
    }    
    
    protected void visitTransformation(Transformation t, Model m) {
        switch (t) {
            case Refinement:
                print(CircusKeyword.CIRCREFINES);
                if (!m.equals(Model.FlDv)) {
                  printDecorword(m + "~");
                }
                break;
            case Simulation:
                print(CircusKeyword.CIRCSIMULATES);
                break;
            case Equivalence:
                print(ZKeyword.EQUALS);
                break;            
        }
    }
    
    @Override
	public Object visitProcessTransformerPred(ProcessTransformerPred term) {                
        visit(term.getSpec());
        visitTransformation(term.getTransformation(), term.getModel());        
        visit(term.getImpl());
        return null;
    }    
    
    @Override
	public Object visitActionTransformerPred(ActionTransformerPred term) {                
        visit(term.getSpec());
        visitTransformation(term.getTransformation(), term.getModel());        
        visit(term.getImpl());
        return null;
    }
    
    @Override
	public Object visitQualifiedDecl(QualifiedDecl term) {
        if (ParamQualifier.Result.equals(term.getParamQualifier())) {
            print(CircusKeyword.CIRCRES);
        } else if (ParamQualifier.ValueResult.equals(term.getParamQualifier())) {
            print(CircusKeyword.CIRCVRES);
        } /* else must be by value, so just don't put it */
        if (ZUtils.assertZNameList(term.getNameList()).isEmpty())
            throw new CztException(new PrintException(getSectionInfo().getDialect(), "Empty list of qualified variables/parameters"));
        visit(term.getNameList());
        print(ZKeyword.COLON);
        visit(term.getExpr());
        return null;
    }
    
    @Override
	public Object visitAssignmentPairs(AssignmentPairs term) {
        printTermList(term.getZLHS());
        print(CircusKeyword.CIRCASSIGN);
        printTermList(term.getZRHS());
        return null;
    }
    
    @Override
	public Object visitCircusFieldList(CircusFieldList term) {
        for(Field f : term) {
            visit(f);
        }
        return null;
    }
    
    @Override
	public Object visitSigmaExpr(SigmaExpr term) {
        //throw new UnsupportedOperationException("not yet!");
      warnUnexpectedTerm(term);
      return null;
    }
    
    @Override
	public Object visitNameSetPara(NameSetPara term) {
        /* Hum... need to know if it is boxed or not... */
        visit(term.getName());
        print(ZKeyword.DEFEQUAL);
        visit(term.getNameSet());
        return null;
    }
    
    @Override
	public Object visitCircusNameSet(CircusNameSet term) {
        visit(term.getExpr());
        return null;
    }

  @Override
public Object visitImplicitChannelAnn(ImplicitChannelAnn term)
  {
    //throw new UnsupportedOperationException("Unexpected term ImplicitChannelAnn.");
    warnUnexpectedTerm(term);
    return null;
  }

  @Override
public Object visitZSignatureList(ZSignatureList term)
  {
    //throw new UnsupportedOperationException("Unexpected term ZSignatureList.");
    warnUnexpectedTerm(term);
    return null;
  }

  @Override
public Object visitCircusActionList(CircusActionList term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term CircusActionList.");
    return null;
  }

  @Override
public Object visitActionSignatureList(ActionSignatureList term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ActionSignatureList.");
    return null;
  }

  @Override
public Object visitProcessSignatureList(ProcessSignatureList term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ProcessSignatureList.");
    return null;
  }

  @Override
public Object visitCircusCommunicationList(CircusCommunicationList term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term CircusCommunicationList.");
    return null;
  }
  @Override
public Object visitStateUpdate(StateUpdate term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term StateUpdate.");
    return null;
  }
  @Override
public Object visitStateUpdateAnn(StateUpdateAnn term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term StateUpdateAnn.");
    return null;
  }

  @Override
public Object visitProcessSignatureAnn(ProcessSignatureAnn term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ProcessSignatureAnn.");
    return null;
  }

  @Override
public Object visitActionSignatureAnn(ActionSignatureAnn term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term ActionSignatureAnn.");
    return null;
  }
  
  @Override
public Object visitCommunicationType(CommunicationType term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term CommunicationType.");
    return null;
  }

  @Override
  public Object visitOutputFieldAnn(OutputFieldAnn term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Unexpected term OutputFieldAnn.");
    return null;
  }

  @Override
  public Object visitProofObligationAnn(ProofObligationAnn term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Not supported yet.");
    return null;
  }

  @Override
  public Object visitCircusNameSetList(CircusNameSetList term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Not supported yet.");
    return null;
  }

  @Override
  public Object visitCircusChannelSetList(CircusChannelSetList term)
  {
    warnUnexpectedTerm(term);//throw new UnsupportedOperationException("Not supported yet.");
    return null;
  }

   
  /* Support for Circus Time : Process */

  public Object visitTimeEndByProcess(TimeEndByProcess term) {
        printLPAREN(term);
        visit(term.getCircusProcess());
        print(CircusTimeKeyword.CIRCENDBY);
        print(CircusTimeToken.LCIRCTIME);        
        visit(term.getExpr());
        print(CircusTimeToken.RCIRCTIME);        
        printRPAREN(term);
        return null;
    }

public Object visitTimeStartByProcess(TimeStartByProcess term) {
        printLPAREN(term);
        print(CircusTimeToken.LCIRCTIME);        
        visit(term.getExpr());
        print(CircusTimeToken.RCIRCTIME);        
        print(CircusTimeKeyword.CIRCSTARTBY);
        visit(term.getCircusProcess());
        printRPAREN(term);
        return null;
    }

public Object visitTimeoutProcess(TimeoutProcess term) {
        printLPAREN(term);
        visit(term.getLeftProcess());
        print(CircusTimeKeyword.CIRCTIMEOUT);
        print(CircusTimeToken.LCIRCTIME);        
        visit(term.getExpr());
        print(CircusTimeToken.RCIRCTIME);        
        visit(term.getRightProcess());
        printRPAREN(term);
        return null;
    }


public Object visitTimedinterruptProcess(TimedinterruptProcess term) {
        printLPAREN(term);
        visit(term.getLeftProcess());
        print(CircusTimeToken.LCIRCTIME);        
        visit(term.getExpr());
        print(CircusTimeToken.RCIRCTIME);        
        visit(term.getRightProcess());
        printRPAREN(term);
        return null;
    }



 /* Support for Circus Time : Action */

  public Object visitTimeEndByAction(TimeEndByAction term) {
        printLPAREN(term);
        visit(term.getCircusAction());
        print(CircusTimeKeyword.CIRCENDBY);
        print(CircusTimeToken.LCIRCTIME); 
        visit(term.getExpr());
        print(CircusTimeToken.RCIRCTIME); 
        printRPAREN(term);
        return null;
    }

public Object visitTimeStartByAction(TimeStartByAction term) {
        printLPAREN(term);
        print(CircusTimeToken.LCIRCTIME);
        visit(term.getExpr());
        print(CircusTimeToken.RCIRCTIME);
        print(CircusTimeKeyword.CIRCSTARTBY);
        visit(term.getCircusAction());
        printRPAREN(term);
        return null;
    }

public Object visitTimeoutAction(TimeoutAction term) {
        printLPAREN(term);
        visit(term.getLeftAction());
        print(CircusTimeKeyword.CIRCTIMEOUT);
        print(CircusTimeToken.LCIRCTIME);
        visit(term.getExpr());
        print(CircusTimeToken.RCIRCTIME);
        visit(term.getRightAction());
        printRPAREN(term);
        return null;
    }


public Object visitTimedinterruptAction(TimedinterruptAction term) {
        printLPAREN(term);
        visit(term.getLeftAction());
        print(CircusTimeToken.LCIRCTIME);
        visit(term.getExpr());
        print(CircusTimeToken.RCIRCTIME);
        visit(term.getRightAction());
        printRPAREN(term);
        return null;
    }

public Object visitWaitAction(WaitAction term) {
    printLPAREN(term);
    print(CircusTimeKeyword.CIRCWAIT);
    visit(term.getExpr());
    printRPAREN(term);
    return null;
}

public Object visitWaitExprAction(WaitExprAction term) {
        printLPAREN(term);
        print(CircusTimeKeyword.CIRCWAIT);
        visit(term.getName());
        print(ZKeyword.COLON);
        visit(term.getExpr());
        print(CircusKeyword.CIRCSPOT);
        visit(term.getCircusAction());
        printRPAREN(term);
        return null;
    }

public Object visitPrefixingTimeAction(PrefixingTimeAction term) {
        printLPAREN(term);
        visit(term.getCommunication());
	if(term.isAtPrefixingAction())
	{
		print(CircusTimeKeyword.ATTIME);
	        print(CircusKeyword.PREFIXTHEN);       
	        visit(term.getCircusAction());
	}
	else if (term.isPrefixingExprAction())
	{
		print(CircusKeyword.PREFIXTHEN);
	        print(CircusTimeToken.LCIRCTIME);
	        visit(term.getExpr());
        	print(CircusTimeToken.RCIRCTIME);       
        	visit(term.getCircusAction());
	}
	else if (term.isAtPrefixingExprAction())
	{	
		print(CircusTimeKeyword.ATTIME);
	        print(CircusKeyword.PREFIXTHEN);
	        print(CircusTimeToken.LCIRCTIME);
	        visit(term.getExpr());
	        print(CircusTimeToken.RCIRCTIME);       
	        visit(term.getCircusAction());
	}
	printRPAREN(term);
	return null;
    }

//public Object visitAtPrefixingAction(AtPrefixingAction term) {
//        printLPAREN(term);
//	visit(term.getCommunication());
//        print(CircusTimeKeyword.ATTIME);
//        print(CircusKeyword.PREFIXTHEN);       
//        visit(term.getCircusAction());
//        printRPAREN(term);
//        return null;
//    }
//
//public Object visitAtPrefixingExprAction(AtPrefixingExprAction term) {
//        printLPAREN(term);
//	visit(term.getCommunication());
//	print(CircusTimeKeyword.ATTIME);
//        print(CircusKeyword.PREFIXTHEN);
//        print(CircusTimeToken.LCIRCTIME);
//        //visit(term.getExpr());
//        print(CircusTimeToken.RCIRCTIME);       
//        visit(term.getCircusAction());
//        printRPAREN(term);
//        return null;
//    }
}

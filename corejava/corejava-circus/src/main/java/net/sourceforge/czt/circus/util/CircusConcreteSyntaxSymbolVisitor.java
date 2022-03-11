/*
 * CircusConcreteSyntaxSymbolVisitor.java
 *
 * Created on 08 June 2006, 15:53
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.circus.util;

import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.ast.OutputFieldAnn;
import net.sourceforge.czt.circus.ast.RenameAction;
import net.sourceforge.czt.circus.visitor.*;

import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.util.IsEmptyNameList;
import net.sourceforge.czt.z.util.StandardZ;

/**
 * This visitor classifies a given AST node as a concrete syntax
 * symbol {@link CircusConcreteSyntaxSymbol}.  This can be used by the JEdit and
 * Eclipse plugins to produce an outline view (or structure tree) of
 * the source.
 *
 * @author leo
 */
public class CircusConcreteSyntaxSymbolVisitor
  implements CircusVisitor<CircusConcreteSyntaxSymbol>
{

  public CircusConcreteSyntaxSymbolVisitor()
  {
  }

  public CircusConcreteSyntaxSymbolVisitor(Utils utils)
  {
  }

  public CircusConcreteSyntaxSymbol visitProcessSignature(ProcessSignature term)
  {
    return term.isBasicProcessSignature() ?
      CircusConcreteSyntaxSymbol.BASIC_PROCESS_SIGNATURE :
      CircusConcreteSyntaxSymbol.PROCESS_SIGNATURE;
  }

  public CircusConcreteSyntaxSymbol visitChannelSetType(ChannelSetType term)
  {
    return CircusConcreteSyntaxSymbol.CHANNELSET_TYPE;
  }

  public CircusConcreteSyntaxSymbol visitProcessType(ProcessType term)
  {
    return CircusConcreteSyntaxSymbol.PROCESS_TYPE;
  }

  public CircusConcreteSyntaxSymbol visitActionType(ActionType term)
  {
    return CircusConcreteSyntaxSymbol.ACTION_TYPE;    
  }

  public CircusConcreteSyntaxSymbol visitChannelType(ChannelType term)
  {
    return CircusConcreteSyntaxSymbol.CHANNEL_TYPE;    
  }

  public CircusConcreteSyntaxSymbol visitNameSetType(NameSetType term)
  {
    return CircusConcreteSyntaxSymbol.NAMESET_TYPE;   
  }

  public CircusConcreteSyntaxSymbol visitAssignmentPairs(AssignmentPairs term)
  {
    return CircusConcreteSyntaxSymbol.ASSIGNMENT_PAIRS;
  }
 
  public CircusConcreteSyntaxSymbol visitLetVarAction(LetVarAction term)
  {
    return CircusConcreteSyntaxSymbol.LETVAR_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitLetMuAction(LetMuAction term)
  {
    return CircusConcreteSyntaxSymbol.LETMU_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitParamProcess(ParamProcess term)
  {
    return CircusConcreteSyntaxSymbol.PARAM_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitSubstitutionAction(SubstitutionAction term)
  {
    return CircusConcreteSyntaxSymbol.SUBST_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitGuardedAction(GuardedAction term)
  {
    return CircusConcreteSyntaxSymbol.GUARDED_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitParallelAction(ParallelAction term)
  {
    return CircusConcreteSyntaxSymbol.INTPAR_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitSpecStmtCommand(SpecStmtCommand term)
  {
    return CircusConcreteSyntaxSymbol.SPECSTMT_CMD;
  }

  public CircusConcreteSyntaxSymbol visitMuAction(MuAction term)
  {
    return CircusConcreteSyntaxSymbol.MU_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitChannelDecl(ChannelDecl term)
  {
    if (term.getExpr() == null)
    {
      return CircusConcreteSyntaxSymbol.SYNCH_CHANNEL_DECL;
    }
    else if ((term.getExpr() instanceof RefExpr) && term.getNameList() == null)
    {
      return CircusConcreteSyntaxSymbol.SCH_CHANNEL_DECL;
    }
    else
    {
      return CircusConcreteSyntaxSymbol.TYPED_CHANNEL_DECL;
    }
  }

  public CircusConcreteSyntaxSymbol visitHideAction(HideAction term)
  {
    return CircusConcreteSyntaxSymbol.HIDE_ACTION;
  }
  
  public CircusConcreteSyntaxSymbol visitRenameAction(RenameAction term)
  {
    return CircusConcreteSyntaxSymbol.RENAME_ACTION;
  }


  public CircusConcreteSyntaxSymbol visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term)
  {
    return CircusConcreteSyntaxSymbol.ALPHAPAR_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitChaosAction(ChaosAction term)
  {
    return CircusConcreteSyntaxSymbol.CHAOS_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitExtChoiceProcessIte(ExtChoiceProcessIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_EXTCH_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitCircusFieldList(CircusFieldList term)
  {
    return CircusConcreteSyntaxSymbol.FIELD_LIST;
  }
  
  @Override
  public CircusConcreteSyntaxSymbol visitCircusChannelSetList(CircusChannelSetList term)
  {
    return CircusConcreteSyntaxSymbol.CHANNELSET_LIST;
  }
  
  @Override
  public CircusConcreteSyntaxSymbol visitCircusNameSetList(CircusNameSetList term)
  {
    return CircusConcreteSyntaxSymbol.NAMESET_LIST;
  }

  public CircusConcreteSyntaxSymbol visitSigmaExpr(SigmaExpr term)
  {
    return CircusConcreteSyntaxSymbol.SIGMA_EXPR;
  }

  public CircusConcreteSyntaxSymbol visitProcessPara(ProcessPara term)
  {
    return CircusConcreteSyntaxSymbol.PROCESS_PARA;
  }

  public CircusConcreteSyntaxSymbol visitIntChoiceProcessIte(IntChoiceProcessIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_INTCH_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitSeqAction(SeqAction term)
  {
    return CircusConcreteSyntaxSymbol.SEQ_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitInterruptAction(InterruptAction term)
  {
    return CircusConcreteSyntaxSymbol.INTERRUPT_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitAlphabetisedParallelAction(AlphabetisedParallelAction term)
  {
    return CircusConcreteSyntaxSymbol.ALPHAPAR_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitSkipAction(SkipAction term)
  {
    return CircusConcreteSyntaxSymbol.SKIP_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitBasicChannelSetExpr(BasicChannelSetExpr term)
  {
    return CircusConcreteSyntaxSymbol.BASIC_CHANNELSET_EXPR;
  }

  public CircusConcreteSyntaxSymbol visitSeqProcessIdx(SeqProcessIdx term)
  {
    return CircusConcreteSyntaxSymbol.IDX_SEQ_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitSeqActionIte(SeqActionIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_SEQ_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitParamAction(ParamAction term)
  {
    return CircusConcreteSyntaxSymbol.PARAM_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitDotField(DotField term)
  {
    boolean isOutputField = term.getAnn(OutputFieldAnn.class) != null;    
    return isOutputField ? 
        CircusConcreteSyntaxSymbol.OUT_FIELD : 
        CircusConcreteSyntaxSymbol.DOT_FIELD;
  }

  public CircusConcreteSyntaxSymbol visitExtChoiceActionIte(ExtChoiceActionIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_EXTCH_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitCallAction(CallAction term)
  {
    return CircusConcreteSyntaxSymbol.CALL_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitChannelSetPara(ChannelSetPara term)
  {
    return CircusConcreteSyntaxSymbol.CHANNELSET_PARA;
  }

  public CircusConcreteSyntaxSymbol visitQualifiedDecl(QualifiedDecl term)
  {    
    switch(term.getParamQualifier())
    {
      case Value : return CircusConcreteSyntaxSymbol.QUALIFIED_DECL_VAL;    
      case Result: return CircusConcreteSyntaxSymbol.QUALIFIED_DECL_RES;    
      case ValueResult: return CircusConcreteSyntaxSymbol.QUALIFIED_DECL_VALRES;    
    }
    return null;
  }

  public CircusConcreteSyntaxSymbol visitExtChoiceProcessIdx(ExtChoiceProcessIdx term)
  {
    return CircusConcreteSyntaxSymbol.IDX_EXTCH_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitCircusNameSet(CircusNameSet term)
  {
    return CircusConcreteSyntaxSymbol.NAMESET;
  }

  public CircusConcreteSyntaxSymbol visitParallelActionIte(ParallelActionIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_INTPAR_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitCommunication(Communication term)
  {
    return CircusConcreteSyntaxSymbol.COMMUNICATION;
  }

  public CircusConcreteSyntaxSymbol visitActionPara(ActionPara term)
  {
    return CircusConcreteSyntaxSymbol.ACTION_PARA;
  }

  public CircusConcreteSyntaxSymbol visitHideProcess(HideProcess term)
  {
    return CircusConcreteSyntaxSymbol.HIDE_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitParallelProcess(ParallelProcess term)
  {
    return CircusConcreteSyntaxSymbol.INTPAR_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitIndexedProcess(IndexedProcess term)
  {
    return CircusConcreteSyntaxSymbol.IDX_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitIntChoiceAction(IntChoiceAction term)
  {
    return CircusConcreteSyntaxSymbol.INTCH_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitInterleaveAction(InterleaveAction term)
  {
    return CircusConcreteSyntaxSymbol.INTLV_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitParallelProcessIdx(ParallelProcessIdx term)
  {
    return CircusConcreteSyntaxSymbol.IDX_INTPAR_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitIntChoiceProcess(IntChoiceProcess term)
  {
    return CircusConcreteSyntaxSymbol.INTCH_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitSchExprAction(SchExprAction term)
  {
    return CircusConcreteSyntaxSymbol.SCHEXPR_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitRenameProcess(RenameProcess term)
  {
    return CircusConcreteSyntaxSymbol.RENAME_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitChannelPara(ChannelPara term)
  {
    return CircusConcreteSyntaxSymbol.CHANNEL_PARA;
  }

  public CircusConcreteSyntaxSymbol visitCallProcess(CallProcess term)
  {
    return CircusConcreteSyntaxSymbol.CALL_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitIfGuardedCommand(IfGuardedCommand term)
  {
    return CircusConcreteSyntaxSymbol.IF_CMD;
  }
  
  public CircusConcreteSyntaxSymbol visitDoGuardedCommand(DoGuardedCommand term)
  {
    return CircusConcreteSyntaxSymbol.DO_CMD;
  }

  public CircusConcreteSyntaxSymbol visitParallelProcessIte(ParallelProcessIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_INTPAR_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitExtChoiceProcess(ExtChoiceProcess term)
  {
    return CircusConcreteSyntaxSymbol.EXTCH_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitIntChoiceActionIte(IntChoiceActionIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_INTCH_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitStopAction(StopAction term)
  {
    return CircusConcreteSyntaxSymbol.STOP_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitExtChoiceAction(ExtChoiceAction term)
  {
    return CircusConcreteSyntaxSymbol.EXTCH_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitAlphabetisedParallelProcessIte(AlphabetisedParallelProcessIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_ALPHAPAR_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitInterleaveProcessIdx(InterleaveProcessIdx term)
  {
    return CircusConcreteSyntaxSymbol.IDX_INTLV_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_ALPHAPAR_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitInterleaveProcess(InterleaveProcess term)
  {
    return CircusConcreteSyntaxSymbol.INTLV_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitNameSetPara(NameSetPara term)
  {
    return CircusConcreteSyntaxSymbol.NAMESET_PARA;
  }

  public CircusConcreteSyntaxSymbol visitInterleaveActionIte(InterleaveActionIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_INTLV_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitSeqProcess(SeqProcess term)
  {
    return CircusConcreteSyntaxSymbol.SEQ_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitBasicProcess(BasicProcess term)
  {
    return CircusConcreteSyntaxSymbol.BASIC_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitAlphabetisedParallelProcessIdx(AlphabetisedParallelProcessIdx term)
  {
    return CircusConcreteSyntaxSymbol.IDX_ALPHAPAR_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitPrefixingAction(PrefixingAction term)
  {
    return CircusConcreteSyntaxSymbol.PREFIX_ACTION;
  }

  public CircusConcreteSyntaxSymbol visitInterleaveProcessIte(InterleaveProcessIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_INTLV_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitVarDeclCommand(VarDeclCommand term)
  {
    return CircusConcreteSyntaxSymbol.VAR_CMD;
  }

  public CircusConcreteSyntaxSymbol visitAssignmentCommand(AssignmentCommand term)
  {
    return CircusConcreteSyntaxSymbol.ASSIGN_CMD;
  }

  public CircusConcreteSyntaxSymbol visitCircusChannelSet(CircusChannelSet term)
  {
    return CircusConcreteSyntaxSymbol.CHANNELSET;
  }

  public CircusConcreteSyntaxSymbol visitInputField(InputField term)
  {
    return CircusConcreteSyntaxSymbol.IN_FIELD;
  }

  public CircusConcreteSyntaxSymbol visitActionSignature(ActionSignature term)
  {
    return CircusConcreteSyntaxSymbol.ACTION_SIGNATURE;
  }

  public CircusConcreteSyntaxSymbol visitSeqProcessIte(SeqProcessIte term)
  {
    return CircusConcreteSyntaxSymbol.ITE_SEQ_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitIntChoiceProcessIdx(IntChoiceProcessIdx term)
  {
    return CircusConcreteSyntaxSymbol.IDX_INTCH_PROCESS;
  }

  public CircusConcreteSyntaxSymbol visitTransformerPara(TransformerPara term)
  {
    return CircusConcreteSyntaxSymbol.TRANSFORMER_PARA;
  }

  public CircusConcreteSyntaxSymbol visitProcessTransformerPred(ProcessTransformerPred term)
  {
    return CircusConcreteSyntaxSymbol.PROCESS_TRANSFORMER_PRED;
  }

  public CircusConcreteSyntaxSymbol visitActionTransformerPred(ActionTransformerPred term)
  {
    return CircusConcreteSyntaxSymbol.ACTION_TRANSFORMER_PRED;
  }

  public CircusConcreteSyntaxSymbol visitCircusCommunicationList(CircusCommunicationList term)
  {
    return CircusConcreteSyntaxSymbol.COMMUNICATION_LIST;
  }

  public CircusConcreteSyntaxSymbol visitActionSignatureList(ActionSignatureList term)
  {
    return CircusConcreteSyntaxSymbol.ACTION_SIGNATURE_LIST;
  }

  public CircusConcreteSyntaxSymbol visitZSignatureList(ZSignatureList term)
  {
    return CircusConcreteSyntaxSymbol.Z_SIGNATURE_LIST;
  }

  public CircusConcreteSyntaxSymbol visitCircusActionList(CircusActionList term)
  {
    return CircusConcreteSyntaxSymbol.CIRCUS_ACTION_LIST;
  }

  public CircusConcreteSyntaxSymbol visitProcessSignatureList(ProcessSignatureList term)
  {
    return CircusConcreteSyntaxSymbol.PROCESS_SIGNATURE_LIST;
  }

  public CircusConcreteSyntaxSymbol visitCommunicationType(CommunicationType term)
  {
    return CircusConcreteSyntaxSymbol.COMMUNICATION_TYPE;
  } 

  public CircusConcreteSyntaxSymbol visitStateUpdate(StateUpdate term)
  {
    return CircusConcreteSyntaxSymbol.STATE_UPDATE;
  }
  
  public CircusConcreteSyntaxSymbol visitCircusStateAnn(CircusStateAnn term)
  {
    return CircusConcreteSyntaxSymbol.CIRCUS_STATE_ANN;
  }
  
  public CircusConcreteSyntaxSymbol visitImplicitChannelAnn(ImplicitChannelAnn term)
  {
    return CircusConcreteSyntaxSymbol.IMPLICIT_CHANNEL_ANN;
  }
  
  public CircusConcreteSyntaxSymbol visitOnTheFlyDefAnn(OnTheFlyDefAnn term)
  {
    return CircusConcreteSyntaxSymbol.ONTHEFLY_ANN;
  }
  
  public CircusConcreteSyntaxSymbol visitStateUpdateAnn(StateUpdateAnn term)
  {
    return CircusConcreteSyntaxSymbol.STATE_UPDATE_ANN;
  }

  public CircusConcreteSyntaxSymbol visitProcessSignatureAnn(ProcessSignatureAnn term)
  {
    return CircusConcreteSyntaxSymbol.PROCESS_SIGNATURE_ANN;
  }

  public CircusConcreteSyntaxSymbol visitActionSignatureAnn(ActionSignatureAnn term)
  {
    return CircusConcreteSyntaxSymbol.ACTION_SIGNATURE_ANN;
  }
  
  @Override
  public CircusConcreteSyntaxSymbol visitOutputFieldAnn(OutputFieldAnn term)
  {
    return CircusConcreteSyntaxSymbol.OUTPUTFIELD_ANN;
  }
  
  @Override
  public CircusConcreteSyntaxSymbol visitProofObligationAnn(ProofObligationAnn term)
  {
    return CircusConcreteSyntaxSymbol.PROOF_OBLIGATION_ANN;
  }

  public interface Utils
    extends IsEmptyNameList
  {
  }

  public static class UtilsImpl
    extends StandardZ
    implements Utils
  {
  }
}

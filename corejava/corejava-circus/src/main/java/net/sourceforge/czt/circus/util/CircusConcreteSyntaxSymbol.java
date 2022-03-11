/*
 * CircusConcreteSyntaxSymbol.java
 *
 * Created on 08 June 2006, 15:56
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.circus.util;

/**
 * An enumeration of concrete syntax symbols.
 * These are based on the concrete syntax productions in
 * Circus,
 * <p>
 * The {@link CircusConcreteSyntaxSymbolVisitor} in this package can be
 * used to classify most kinds of AST nodes as one of these
 * symbols.
 * </p>
 * @author leo
 */
public enum CircusConcreteSyntaxSymbol
{
  /* Process level paragraphs */
  CHANNEL_PARA("Channel paragraph"),
  CHANNELSET_PARA("Channel set paragraph"),
  PROCESS_PARA("Process paragraph"),
  PROCESS_REF_CONJ_PARA("Process refinement conjecture paragraph"),
  ACTION_REF_CONJ_PARA("Action refinement conjecture paragraph"),
  
  /* Action level paragraphs */
  ACTION_PARA("Action paragraph"),
  NAMESET_PARA("Name set paragraph"),
  
  /* Declarations */
  TYPED_CHANNEL_DECL("Typed channel declaration"),
  SYNCH_CHANNEL_DECL("Synchronisation channel declaration"),
  SCH_CHANNEL_DECL("Channels from schema declaration"),
  QUALIFIED_DECL_VAL("Qualified parameter declaration - by value"),
  QUALIFIED_DECL_RES("Qualified parameter declaration - by result"),
  QUALIFIED_DECL_VALRES("Qualified parameter declaration - by value result"),
  
  /* Special Circus sets */
  CHANNELSET("Channel set"),
  BASIC_CHANNELSET_EXPR("Enumerated channel set"),
  NAMESET("Name set"),
  
  /* (Abstract) Process definitions */
  CIRCUS_PROCESS("Process definition"),                     // CircProcess
  UNARY_PROCESS("Unary process definition"),                // Process1
  BINARY_PROCESS("Binary process definition"),              // Process2
  ITE_PROCESS("Iterated process definition"),               // ProcessIte
  //PARAM_PROCESS("Parameterised process definition"),        // ProcessD
  //IDX_PROCESS("Indexed process definition"),                // ProcessIdx
  
  /* (Concrete) Process definitions */
  PARAM_PROCESS("Parameterised process"),                   // ParamProcess  : Decl @ Process
  IDX_PROCESS("Indexed process"),                           // IndexedProcess: Decl \odot Process
  BASIC_PROCESS("Basic process"),                           // BasicProcess  : Decl @ \circbegin ...
  
  /* (Concrete Special + Unary) Process definitions */
  CALL_PROCESS("Process call"),
  HIDE_PROCESS("Hide process"),
  RENAME_PROCESS("Rename process"),
  
  /* (Concrete Binary) Process definitions */
  SEQ_PROCESS("Sequential composition process"),
  EXTCH_PROCESS("External choice process"),
  INTCH_PROCESS("Internal choice process"),
  INTLV_PROCESS("Interleave process"),
  ALPHAPAR_PROCESS("Alphabetised parallel process"),
  INTPAR_PROCESS("Interface parallel process"),
  
  ITE_SEQ_PROCESS("Iterated sequential composition process"),
  ITE_EXTCH_PROCESS("Iterated external choice process"),
  ITE_INTCH_PROCESS("Iterated internal choice process"),
  ITE_INTLV_PROCESS("Iterated interleave process"),
  ITE_ALPHAPAR_PROCESS("Iterated alphabetised parallel process"),
  ITE_INTPAR_PROCESS("Iterated interface parallel process"),
  
  IDX_SEQ_PROCESS("Indexed sequential composition process"),
  IDX_EXTCH_PROCESS("Indexed external choice process"),
  IDX_INTCH_PROCESS("Indexed internal choice process"),
  IDX_INTLV_PROCESS("Indexed interleave process"),
  IDX_ALPHAPAR_PROCESS("Indexed alphabetised parallel process"),
  IDX_INTPAR_PROCESS("Indexed interface parallel process"),
  
  
  /* (Abstract) Action definitions */
  CIRCUS_ACTION("Action definition"),                     // CircAction
  UNARY_ACTION("Unary action definition"),                // Action1
  BINARY_ACTION("Binary action definition"),              // Action2
  ITE_ACTION("Iterated action definition"),               // ActionIte
  //PARAM_ACTION("Parameterised action definition"),        // ActionD
  
  /* (Concrete Special + Unary) Action definitions */
  SKIP_ACTION("Skip action"),
  STOP_ACTION("Stop action"),
  CHAOS_ACTION("Chaos action"),
  SCHEXPR_ACTION("Schema expression action"),             // REMOVE altogether and have call only?
  CALL_ACTION("Action call"),
  PARAM_ACTION("Parameterised action"),                   // ParamAction
  MU_ACTION("Recursive action"),
  GUARDED_ACTION("Guarded action"),
  HIDE_ACTION("Hide action"),
  RENAME_ACTION("Rename action"),
  PREFIX_ACTION("Prefixing action"),
  SUBST_ACTION("Substitution action"),
  LETVAR_ACTION("Local environment for variable declaration"),
  LETMU_ACTION("Local environment for recursive actions"),
  SIGMA_EXPR("Communication expression"),
  
  /* (Concrete Binary) Action definitions */
  SEQ_ACTION("Sequential composition action"),
  INTERRUPT_ACTION("Interrupt action"),
  EXTCH_ACTION("External choice action"),
  INTCH_ACTION("Internal choice action"),
  INTLV_ACTION("Interleave action"),
  ALPHAPAR_ACTION("Alphabetised parallel action"),
  INTPAR_ACTION("Interface parallel action"),
  
  ITE_SEQ_ACTION("Iterated sequential composition action"),
  ITE_EXTCH_ACTION("Iterated external choice action"),
  ITE_INTCH_ACTION("Iterated internal choice action"),
  ITE_INTLV_ACTION("Iterated interleave action"),
  ITE_ALPHAPAR_ACTION("Iterated alphabetised parallel action"),
  ITE_INTPAR_ACTION("Iterated interface parallel action"),
  
  /* Commands */
  COMMAND("Command"),
  SPECSTMT_CMD("Specification statement"),
  ASSIGN_CMD("Assignment"),
  IF_CMD("Guarded alternation - Circus if statement"),
  DO_CMD("Guarded loop - Circus do statement"),
  VAR_CMD("Variable block"),
  
  /* Communication */
  COMMUNICATION("Communication"),
  DOT_FIELD("Dotted (value) communication field"),
  OUT_FIELD("Output (expression) communication field"),
  IN_FIELD("Input communication field"),
  
  /* Circus Lists */
  FIELD_LIST("List of communication fields"),
  COMMUNICATION_LIST("List of communication expressions"),
  PROCESS_SIGNATURE_LIST("Process signature list"),
  ACTION_SIGNATURE_LIST("Action signature list"),
  Z_SIGNATURE_LIST("Z signature list"),
  CIRCUS_ACTION_LIST("Circus action list"),  
  CHANNELSET_LIST("Channel set list"),
  NAMESET_LIST("Name set list"),
  
  /* Circus signatures */
  ACTION_SIGNATURE("Action signature"),
  PROCESS_SIGNATURE("Process signature"),
  BASIC_PROCESS_SIGNATURE("Basic process signature"),
  
  CHANNEL_TYPE("Channel type"),
  CHANNELSET_TYPE("Channel set type"),
  NAMESET_TYPE("Name set type"),
  PROCESS_TYPE("Process type"),
  ACTION_TYPE("Process type"),
  COMMUNICATION_TYPE("Communication type") ,
    
  STATE_UPDATE("State update"),
  ASSIGNMENT_PAIRS("Assignment pairs"),
  
  TRANSFORMER_PARA("Term transformer paragraph"),
  PROCESS_TRANSFORMER_PRED("Process transformer predicate"),
  ACTION_TRANSFORMER_PRED("Action transformer predicate"),
  
  /** Circus annotations */
  CIRCUS_STATE_ANN("Circus state annotation"),
  IMPLICIT_CHANNEL_ANN("Implicit channel annotation"),
  ONTHEFLY_ANN("On-the-fly paragraph annotation"),
  STATE_UPDATE_ANN("State update annotation"),
  PROCESS_SIGNATURE_ANN("Process signature annotation"),
  ACTION_SIGNATURE_ANN("Action signature annotation"),
  OUTPUTFIELD_ANN("Output field annotation"),
  PROOF_OBLIGATION_ANN("Proof obligation annotation")

  ;
  
  private final String description_;
  
  CircusConcreteSyntaxSymbol(String description)
  {
    description_ = description;
  }
  
  public String getDescription()
  {
    return description_;
  }
}

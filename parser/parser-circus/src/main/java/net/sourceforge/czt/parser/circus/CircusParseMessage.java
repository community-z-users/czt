/*
 * CircusParseMessage.java
 *
 * Created on 22 March 2006, 13:53
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.circus;


public enum CircusParseMessage {
  
  MSG_NOT_IMPLEMENTED("{0} feature not implemented yet."),
  MSG_SETDISPLAY_NOTALLOWED_FORCHANNELSET("Expressions in channel set paragraphs can be neither set extension nor set comprehension. It must be a basic channel set expresion instead."),
  //MSG_REFEXPR_EXPECPTED_IN_BASICCHANNELSETEXPR_WARNING("Invalid basic channel set expression index ''{0}'' (of 0..{1}) as ''{2}'' (''{3}'' class) at location ''{4}''."),
  MSG_UNKNOWN_COMMUNICATION_PATTERN("Invalid communication pattern.", "The prefixing communication is neither of synchronisation, input, output, or mixed. This can only happen with specialised implementations of Field that do not obbey follow any available CommType."),
  MSG_UNBALANCED_LISTS("A ''{0}'' list of size {1} cannot be related to a ''{2}'' list of size ''{3}''."),
  MSG_EMPTY_ASSIGNMENT("Invalid assignment, LHS is empty."),
  MSG_INVALID_CHANNEL_RENAMING_EXPR("Invalid channel renaming for channel ''{0}'' at index {1}. It is a ''{2}'' instead of RefExpr."),
  MSG_INVALID_BASICPROCESS_STATE_PARA("State paragraph is not a schema", "Basic process state must be either a horizontal or boxed schema, or a schema expression action."),
  MSG_UNKNOWN_REFINEMENT_MODEL("Unknown refinement model ''{0}''."),
  MSG_DUPLICATE_PROC_STATE_DECL("Process ''{0}'' state name is ''{1}'', but ''{2}'' more state paragraph(s) have been declared. The first duplicate one is named ''{3}'' at ''{4}''."),  
 
  MSG_CIRCUSENV_ERROR("Error occurred within circus environment at symbol ''{0}''."),
  
  MSG_CHANDECL_ERROR("An error occurred inside a channel declaration paragraph. See other messages, or review the \"\\circchannel\\\" keyword."),
  MSG_CHANFROMDECL_ERROR("An error occurred inside a channelfrom declaration paragraph. See other messages, or review the \"\\circchannelfrom\\\" keyword."),
    
  MSG_CHANNELSET_EXPR_ERROR("Invalid expression for channel set paragraph after double equals (==)."),
  MSG_CHANNELSET_MISSING_NAME_ERROR("Missing name in channel set declaration."),
  MSG_CHANNELSET_MISSING_DEFEQUAL_ERROR("Missing DEFEQUAL after name in channel set declaration."),
  MSG_CHANNELSET_ERROR("An error occurred inside a channelset paragraph. See other messages, or review the \"\\circchannelset\\\" keyword."),
  
  MSG_PROCESSPARA_DESC_ERROR("Invalid process description for ''{0}''. See other messages or review the \"\\circprocess\\\" keyword."),
  MSG_PROCESSPARA_MISSING_CIRCDEF_ERROR("Missing CIRCDEF after process name in process paragraph declaration."),
  MSG_PROCESSPARA_MISSING_NAME_ERROR("Missing process name in process paragraph declaration."),
  
  MSG_DUPLICATED_BASIC_PROCESS_STATE("Duplicated ({0}) state paragraph for basic process at ''{1}''."),
  MSG_DUPLICATED_BASIC_PROCESS_MAINACTION("Duplicated main action for basic process."),
  MSG_FAIL_CHECK_INNER_PROC_ELEM_BASIC_PROC_SCOPE("No basic process scope for enclosing basic process inner paragraphs at {0}."),
  MSG_INVALID_BASIC_PROCESS_SCOPE_WARNING("Unmatched ({0}) scope for basic process ({1}) at ''{2}''."),
  MSG_DUPlICATED_BASIC_PROCESS_SCOPE("Circus does not allow nested basic processes (from {0}) at {1}."),
  MSG_MISSING_BASIC_PROCESS_CIRCEND("Missing enclosing CIRCEND for multiple environment basic process ''{0}'' at {1}."),
  MSG_OUTSITE_BASIC_PROCESS_SCOPE_WARNING("{0} {1} at \n {2}.",
      "\nThis is a serious warning as type checking will assume the paragraph declared outside a process\n" +
      "is included into the closest enclosing basic process."),      
  MSG_PROCESS_PARA_NAME_MISMATCH_FOR_CIRCEND_WARNIING("Mismatch process name (''{0}'') while trying to remove " +
      "CIRCEND warning for multiple environment basic process ''{1}'' declared @ ''{2}'' with CIRCEND-LOC @ ''{3}''.",
      "\nThis is a seriouc warning and should be looked carefully. It means there must be scoping problems at the given locations."),      
  MSG_INVALID_MULTIENV_BASIC_PROCESS_CIRCEND("Basic process scope from multiple environments was closed without been previouly opened at ''{0}''."),  
  MSG_INVALID_INNER_PROCESS_PARA("Invalid unboxed paragraph (i.e. within ZED env) for Circus basic process scope. " +
      "Only Z paragraphs are valid within Z unboxed paragraph environment but a ''{0}'' was found at {1}."),   
      
  MSG_INVALID_CIRCUS_PARA_IN_ZED("Invalid Circus ''{0}'' paragraph within ZED environment. It must be declared within a ''{1}'' environment."),      
  MSG_CHANNEL_TYPE_ERROR("Channel type expression is missing or is incorrect at colon."),
  
  MSG_COMMPATTERN_NOT_RECOGNISED("Channel or field name ''{0}'' in communication pattern could not be recognised. This is an error within the nearest prefix action."),
  MSG_COMMPATTERN_PREFIXCOLON_NOT_RECOGNISED("Possible missing parenthesis around predicate for input field ''{0}''"),
  MSG_CIRCNAME_DOESNOT_ALLOW_STROKES("Circus name ''{0}'' does not accept strokes."),
  
  MSG_MISSING_PREFIXTHEN_PREFIXACTION("Missing PREFIXTHEN after communication pattern."),
  MSG_ERRORDECL_IN_PARAMACTION("Parameterised actions/commands can only contain variable/qualified declarations."),
  MSG_NESTED_PARAMACTION("Nested action parameters are not allowed."),
  MSG_WRONG_NUMBER_FIELD_STROKES("Wrong number of fields in communication pattern." +
      "\n\tChannel.: {0}" +
      "\n\tExpected: {1}" +
      "\n\tFound...: {2}", //+
//      "\n\tSymbol..: {3}",
    "\n\tThe number of fields in a communication pattern is determined by the right scanning " +
    "\n\tof tokens, and a mismatch has been found. This usually happens due to missing parenthesis " +
    "\n\tin output field expressions, input field restriction predicates, or field separators with fields."),
    //+ "\n\tIf the counters are negative, some processing error must have occurred at the SmartScanner.")
    
  MSG_UNMATCHED_CIRCUSTOOLS_OFF("Missing ''\\circtoolson'' - nesting of tool flag switch is not allowed.")
  ;    
  
  private final String message_;
  private final String explanation_;
  private boolean flagged_;

  CircusParseMessage(String message)
  {
    this(message, null);
  }

  CircusParseMessage(String message, String explanation)
  {    
    message_ = message;
    explanation_ = explanation;
    flagged_ = false;
  }

  public String getMessage()
  {
    return message_;
  }

  public String getExplanation()
  {
    String result = explanation_;
    flagged_ = true;
    return result;
  }
  
  public boolean alreadyFlagged()
  {
    return flagged_;
  }
  
  public String getFullMessage()
  {
    String result = getMessage();
    if (!flagged_) result += getExplanation();
    return result;
  }  
}

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
  MSG_REFEXPR_EXPECPTED_IN_BASICCHANNELSETEXPR_WARNING("Invalid basic channel set expression at index {0}."),
  MSG_UNKNOWN_COMMUNICATION_PATTERN("Invalid communication pattern.", "The prefixing communication is neither of synchronisation, input, output, or mixed. This can only happen with specialised implementations of Field that do not obbey follow any available CommType."),
  MSG_UNBALANCED_LISTS("A {0} list of size {1} cannot be related to a {2} list of size {3}."),
  MSG_EMPTY_ASSIGNMENT("Invalid assignment, LHS is empty."),
  MSG_INVALID_CHANNEL_RENAMING_EXPR("Invalid channel renaming for channel {0} at index {1}. It is a {2} instead of RefExpr."),
  MSG_INVALID_BASICPROCESS_STATE_PARA("State paragraph is not a schema", "Basic process state must be either a horizontal or boxed schema, or a schema expression action."),
  MSG_UNKNOWN_REFINEMENT_MODEL("Unknown refinement model {0}."),
  MSG_DUPLICATE_PROC_STATE_DECL("Process {0} state name is {1}, but {2} more state paragraph(s) have been declared. The first duplicate one is named {3} at {4}."),  
 
  MSG_CIRCUSENV_ERROR("Error occurred within circus environment at symbol {0}."),
  
  MSG_CHANDECL_ERROR("An error occurred inside a channel declaration paragraph. See other messages, or review the \"\\circchannel\\\" keyword."),
  MSG_CHANFROMDECL_ERROR("An error occurred inside a channelfrom declaration paragraph. See other messages, or review the \"\\circchannelfrom\\\" keyword."),
    
  MSG_CHANNELSET_EXPR_ERROR("Invalid expression for channel set paragraph after double equals (==)."),
  MSG_CHANNELSET_MISSING_NAME_ERROR("Missing name in channel set declaration."),
  MSG_CHANNELSET_MISSING_DEFEQUAL_ERROR("Missing DEFEQUAL after name in channel set declaration."),
  MSG_CHANNELSET_ERROR("An error occurred inside a channelset paragraph. See other messages, or review the \"\\circchannelset\\\" keyword."),
  
  MSG_PROCESSPARA_DESC_ERROR("Invalid process description for {0}. See other messages or review the \"\\circprocess\\\" keyword."),
  MSG_PROCESSPARA_MISSING_CIRCDEF_ERROR("Missing CIRCDEF after process name in process paragraph declaration."),
  MSG_PROCESSPARA_MISSING_NAME_ERROR("Missing process name in process paragraph declaration."),
  
  MSG_DUPLICATED_BASIC_PROCESS_STATE("Duplicated state paragraph for basic process at {0}."),
  MSG_FAIL_CHECK_INNER_PROC_ELEM_BASIC_PROC_SCOPE("No basic process scope for enclosing basic process inner paragraphs at {0}."),
  MSG_INVALID_BASIC_PROCESS_SCOPE_WARNING("Unmatched ({0}) scope for basic process ({1}) at {2}."),
  MSG_DUPlICATED_BASIC_PROCESS_SCOPE("Circus does not allow nested basic processes (from {0}) at {1}."),
  MSG_OUTSITE_BASIC_PROCESS_SCOPE_WARNING("Cannot {0}{1} outside a basic process scope at \n {2}.\n " +
      "This is a serious warning as type checking will assume the paragraph declared outside a process\n" +
      "is included into the closest enclosing basic process."),
  MSG_INVALID_MULTIENV_BASIC_PROCESS_CIRCEND("Basic process scope from multiple environments was closed without been previouly opened at {0}."),  
  MSG_CHANNEL_TYPE_ERROR("Channel type expression is missing or is incorrect at colon.");  
  
  private final String message_;
  private final String explanation_;

  CircusParseMessage(String message)
  {
    message_ = message;
    explanation_ = null;
  }

  CircusParseMessage(String message, String explanation)
  {
    message_ = message;
    explanation_ = explanation;
  }

  String getMessage()
  {
    return message_;
  }

  String getExplanation()
  {
    return explanation_;
  }   
}

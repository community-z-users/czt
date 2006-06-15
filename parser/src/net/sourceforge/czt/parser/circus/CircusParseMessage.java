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
  
  MSG_SETDISPLAY_NOTALLOWED_FORCHANNELSET("Expressions in channel set paragraphs can be neither set extension nor set comprehension. It must be a basic channel set expresion instead."),
  MSG_REFEXPR_EXPECPTED_IN_BASICCHANNELSETEXPR("Invalid basic channel set expression at index {0}."),
  MSG_UNKNOWN_COMMUNICATION_PATTERN("Invalid communication pattern.", "The prefixing communication is neither of synchronisation, input, output, or mixed. This can only happen with specialised implementations of Field that do not obbey follow any available CommType."),
  MSG_UNBALANCED_LISTS("A {0} list of size {1} cannot be related to a {2} list of size {3}."),
  MSG_INVALID_BASICPROCESS_STATE_PARA("State paragraph is not a schema", "Basic process state must be either a horizontal or boxed schema, or a schema expression action."),
  MSG_DUPLICATE_PROC_STATE_DECL("Process {0} state name is {1}, but {2} more state paragraph(s) have been declared. The firs duplicate one is named {3}.");

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

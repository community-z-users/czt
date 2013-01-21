/*
 * CircusParseMessage.java
 *
 * Created on 22 March 2006, 13:53
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.circustime;


public enum CircusTimeParseMessage {
  
  MSG_NOT_IMPLEMENTED_CIRCUS_TIME("{0} feature not implemented yet.")
    ;    
  
  private final String message_;
  private final String explanation_;
  private boolean flagged_;

  CircusTimeParseMessage(String message)
  {
    this(message, null);
  }

  CircusTimeParseMessage(String message, String explanation)
  {    
    message_ = message;
    explanation_ = explanation;
    flagged_ = false;
  }

  String getMessage()
  {
    return message_;
  }

  String getExplanation()
  {
    String result = explanation_;
    flagged_ = true;
    return result;
  }
  
  boolean alreadyFlagged()
  {
    return flagged_;
  }
  
  String getFullMessage()
  {
    String result = getMessage();
    if (!flagged_) result += getExplanation();
    return result;
  }  
}

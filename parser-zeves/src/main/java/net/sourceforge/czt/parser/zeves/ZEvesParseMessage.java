/*
 * CircusParseMessage.java
 *
 * Created on 22 March 2006, 13:53
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.zeves;


public enum ZEvesParseMessage {
  
  MSG_NOT_WITHIN_PROOFSCRIPT("Recognised proof command word '{0}' outside zproof environment", "The lexer is identifying a proof command word from a part of the specification outside a zproof. Try and see if you have any name overlap with any of the possible proof command words")
  ;    
  
  private final String message_;
  private final String explanation_;
  private boolean flagged_;

  ZEvesParseMessage(String message)
  {
    this(message, null);
  }

  ZEvesParseMessage(String message, String explanation)
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

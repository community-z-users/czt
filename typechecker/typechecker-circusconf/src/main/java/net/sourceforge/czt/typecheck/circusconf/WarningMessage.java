/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.typecheck.circusconf;

/**
 *
 * @author leo
 */
public enum WarningMessage {
  // NOTE: in "\n\tXXX.......":, the "XXX.......".length()= 10 for beautification (see WarningManager loc info)
  
  CIRCUS_CONF_WARNING_XXXX(
    "Warning bla bla bla." +
      "\n\tProcess...: {0}" +
      "\n\tAction....: {1}" +
      "\n\tExpression: {2}",
    "Detailed comment.\n\t bla bla bla."),
 
  ;
  
  private final String message_;
  private final String explanation_;
  private boolean flagged_;

  WarningMessage(String message)
  {
    this(message, null);
  }

  WarningMessage(String message, String explanation)
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
    if (!flagged_) result += "\n\t" + getExplanation();
    return result;
  }
}

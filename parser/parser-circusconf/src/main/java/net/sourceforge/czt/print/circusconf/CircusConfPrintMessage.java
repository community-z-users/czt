/*
 * CircusPrintMessage.java
 *
 * Created on 01 May 2007, 08:41
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circusconf;

/**
 *
 * @author leo
 */
public enum CircusConfPrintMessage {
  
  MSG_TODO_TERM("Unexpected Circus term ''{0}'' to print\n\t''{1}''");  

 
  private final String message_;
  private final String explanation_;

  CircusConfPrintMessage(String message)
  {
    message_ = message;
    explanation_ = null;
  }

  CircusConfPrintMessage(String message, String explanation)
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

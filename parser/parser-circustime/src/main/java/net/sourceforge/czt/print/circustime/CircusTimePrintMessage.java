/*
 * CircusPrintMessage.java
 *
 * Created on 01 May 2007, 08:41
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circustime;

/**
 *
 * @author leo
 */
public enum CircusTimePrintMessage {
  
  MSG_NOT_IMPLEMENTED_CIRCUS_TIME("{0} feature not implemented yet.");    

    
  private final String message_;
  private final String explanation_;

  CircusTimePrintMessage(String message)
  {
    message_ = message;
    explanation_ = null;
  }

  CircusTimePrintMessage(String message, String explanation)
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

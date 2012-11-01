/*
 * CircusPrintMessage.java
 *
 * Created on 01 May 2007, 08:41
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circus;

/**
 *
 * @author leo
 */
public enum CircusPrintMessage {
  
  MSG_BASIC_PROCESS_MISSING_ENTITY("Missing ''{0}'' for basic process while printing AST:\n\t''{1}''"),
  MSG_BASIC_PROCESS_LOCAL_ONTHEFLY_PARAGRAPH("Cannot have an on-the-fly paragraph declared as local: ''{0}'' in basic process\n\t''{1}''"),
  MSG_BASIC_PROCESS_DUPLICATED_STATE_PARAGRAPH("Duplicated state paragraph ''{0}'' for basic process."),
  MSG_BASIC_PROCESS_BAD_PARAGRAPH("''{0}'' declared paragraph ''{1}'' is not allowed within basic process\n\t''{2}''"),  
  MSG_UNEXPECTED_TERM("Unexpected Circus term ''{0}'' to print\n\t''{1}''");  
    
  private final String message_;
  private final String explanation_;

  CircusPrintMessage(String message)
  {
    message_ = message;
    explanation_ = null;
  }

  CircusPrintMessage(String message, String explanation)
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

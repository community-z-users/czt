/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.typecheck.circus;

/**
 *
 * @author leo
 */
public enum WarningMessage {
  SCHEXPR_CALL_ACTION_WITHOUT_BRAKET(
    "Missing schema expression action brackets." +
      "\n\tProcess...: {0}" +
      "\n\tAction....: {1}" +
      "\n\tExpression: {2}",
    "Without the special brackets, schema expression actions are wrongly interpreted as action calls.\n\t " +
    "For simple schema reference, the type checker can recover and continue. For references with generic\n\t " +
    "actuals or variable substitution, it is not possible to recover and an error is raised.\n\t " +
    "The warning is mostly for other tools, which will also need to care about such special case."),
  INVALID_DECL_IN_VARDECLCOMMAND("Variable declaration command does accept {2}." +
    "\n\tProcess: {0}" +
    "\n\tAction: {1}");
  
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
    if (!flagged_) result += getExplanation();
    return result;
  }
}

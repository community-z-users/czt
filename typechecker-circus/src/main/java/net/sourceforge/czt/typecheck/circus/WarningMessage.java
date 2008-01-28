/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.typecheck.circus;

import net.sourceforge.czt.print.circus.CircusPrintMessage;

/**
 *
 * @author leo
 */
public enum WarningMessage {
  SCHEXPR_CALL_ACTION_WITHOUT_BRAKET(
    "Missing schema expression action brackets.\n\tExpression: {2}\n\tAction    : {1}\n\tProcess   : {0}",
    "Without the special brackets, schema expression actions are wrongly interpreted as action calls. " +
    "For simple schema reference, the type checker can recover and continue. For references with generic " +
    "actuals or variable substitution, it is not possible to recover and an error is raised. " +
    "The warning is mostly for other tools, which will also need to care about such special case."),
  INVALID_DECL_IN_VARDECLCOMMAND("Variable declaration command does accept {2}.\n\tAction: {1}\n\tProcess: {0}");
     
  private final String message_;
  private final String explanation_;

  WarningMessage(String message)
  {
    message_ = message;
    explanation_ = null;
  }

  WarningMessage(String message, String explanation)
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

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
    "Without the special brackets, schema expression actions are wrongly interpreted as action calls.\n\t" +
    "For simple schema reference, the type checker can recover and continue. For references with generic\n\t" +
    "actuals or variable substitution, it is not possible to recover and an error is raised.\n\t" +
    "The warning is mostly for other tools, which will also need to care about such special case."),
  INVALID_DECL_IN_VARDECLCOMMAND("Variable declaration command does accept ''{2}''." +
    "\n\tProcess: {0}" +
    "\n\tAction: {1}",
    "Variable declaration commands only accept a list of (possibly qualified) variables.\n\t" +
    "That is, schema inclusions, constant declarations, and other forms are not allowed."),
  INVALID_COMMUNICATION_PATTERN_WRT_CHANNEL_TYPE("Invalid field list encountered during typechecking: wrong number of variables w.r.t. field count." +
    "\n\tProcess...: {0}" +
    "\n\tAction....: {1}" +
    "\n\tChannel...: {2}" +    
    "\n\tExpected..: {3} (''{4}*4'' from input + ''{5}'' from output)" + 
    "\n\tFound.....: {6}",
    "The number of expressions found (i.e., declared variable references or expressions themselves)\n\t" +
    "does not match the expected count. That can only happen because of a type mismatch on some\n\t" +
    "output prefix expression with respect to the remainder type dimensions of a particular\n\t" +
    "communication pattern (e.g., c?x!y, where c has A x B x C type, but y has a type not unifiable with B x C).\n\t" +
    "This generates a type error. If you see this warning without a type error, please report this as a bug.")
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

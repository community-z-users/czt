
  /**
   * Returns whether this MemPred represents an equality.
   * This is the case iff mixfix is true and the
   * right expression is an instance of SetExpr containing
   * just one expression.
   */
  boolean isEquality();


  /**
   * Check the correctness of this side-condition.
   * The result of the check can be accessed via the getStatus method.
   */
  void check();

  /**
   * Returns the status.
   */
  Status getStatus();

  enum Status
  {
    /**
     * The side-condition has not been checked.
     */
    UNCHECKED,
    /**
     * The side-condition has been checked and is true.
     */
    PASS,
    /**
     * The side-condition has been checked and is false.
     */
    FAIL,
    /**
     * The side-condition needs to be checked later when the
     * sequent is instantiated more fully.
     */
    UNKNOWN;
  }

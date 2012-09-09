  /**
   * This is a convenience method.
   * It returns the CircusActionList if ActionList is an instance of
   * CircusActionList  or throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.CircusActionList getGuardedActionList();

  int getNumberOfGuards();
  net.sourceforge.czt.circus.ast.GuardedAction getGuardedAction(int index);
  public net.sourceforge.czt.circus.ast.CircusActionList getGuardedAction()
  {
    net.sourceforge.czt.circus.ast.ActionList al = getActionList();
    if (al instanceof net.sourceforge.czt.circus.ast.CircusActionList) {
      return (net.sourceforge.czt.circus.ast.CircusActionList) al;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
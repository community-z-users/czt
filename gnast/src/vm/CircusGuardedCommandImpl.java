  public net.sourceforge.czt.circus.ast.CircusActionList getGuardedActionList()
  {
    net.sourceforge.czt.circus.ast.ActionList al = getActionList();
    if (al instanceof net.sourceforge.czt.circus.ast.CircusActionList) {
      return (net.sourceforge.czt.circus.ast.CircusActionList) al;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public int getNumberOfGuards()
  {
    return getGuardedActionList().size(); 
  } 

  public net.sourceforge.czt.circus.ast.GuardedAction getGuardedAction(int index)
  {
    net.sourceforge.czt.circus.ast.CircusAction ca = getGuardedActionList().get(index);	  
    if (ca instanceof net.sourceforge.czt.circus.ast.GuardedAction) {
       return (net.sourceforge.czt.circus.ast.GuardedAction)ca;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
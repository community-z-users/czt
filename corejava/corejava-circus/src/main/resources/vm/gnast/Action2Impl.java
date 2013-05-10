  public net.sourceforge.czt.circus.ast.CircusAction getLeftAction()
  {
	  net.sourceforge.czt.circus.ast.CircusAction result = null;
    if (getCircusAction().size() > 0) {
      result = getCircusAction().get(0);
    }
    return result;
  }

  public void setLeftAction(net.sourceforge.czt.circus.ast.CircusAction action)
  {
    if (getCircusAction().size() > 0) {
      getCircusAction().set(0, action);
    }
    else {
      getCircusAction().add(action);
    }
  }

  public net.sourceforge.czt.circus.ast.CircusAction getRightAction()
  {
	  net.sourceforge.czt.circus.ast.CircusAction result = null;
    if (getCircusAction().size() > 1) {
      result = getCircusAction().get(1);
    }
    return result;
  }

  public void setRightAction(net.sourceforge.czt.circus.ast.CircusAction action)
  {
    if (getCircusAction().size() == 0) {
      getCircusAction().add(null);
    }
    if (getCircusAction().size() > 1) {
      getCircusAction().set(1, action);
    }
    else {
      getCircusAction().add(action);
    }
  }

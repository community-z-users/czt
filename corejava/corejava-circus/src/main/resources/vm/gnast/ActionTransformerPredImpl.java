  public net.sourceforge.czt.circus.ast.CircusAction getSpec()
  {
	  net.sourceforge.czt.circus.ast.CircusAction result = null;
    if (getCircusAction().size() > 0) {
      result = getCircusAction().get(0);
    }
    return result;
  }

  public void setSpec(net.sourceforge.czt.circus.ast.CircusAction action)
  {
    if (getCircusAction().size() > 0) {
      getCircusAction().set(0, action);
    }
    else {
      getCircusAction().add(action);
    }
  }

  public net.sourceforge.czt.circus.ast.CircusAction getImpl()
  {
	  net.sourceforge.czt.circus.ast.CircusAction result = null;
    if (getCircusAction().size() > 1) {
      result = getCircusAction().get(1);
    }
    return result;
  }

  public void setImpl(net.sourceforge.czt.circus.ast.CircusAction action)
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

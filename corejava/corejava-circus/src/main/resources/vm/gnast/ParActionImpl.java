  public net.sourceforge.czt.circus.ast.NameSet getLeftNameSet()
  {
	  net.sourceforge.czt.circus.ast.NameSet result = null;
    if (getNameSet().size() > 0) {
      result = getNameSet().get(0);
    }
    return result;
  }

  public void setLeftNameSet(net.sourceforge.czt.circus.ast.NameSet alpha)
  {
    if (getNameSet().size() > 0) {
      getNameSet().set(0, alpha);
    }
    else {
      getNameSet().add(alpha);
    }
  }

  public net.sourceforge.czt.circus.ast.NameSet getRightNameSet()
  {
	  net.sourceforge.czt.circus.ast.NameSet result = null;
    if (getNameSet().size() > 1) {
      result = getNameSet().get(1);
    }
    return result;
  }

  public void setRightNameSet(net.sourceforge.czt.circus.ast.NameSet alpha)
  {
    if (getNameSet().size() == 0) {
      getNameSet().add(null);
    }
    if (getNameSet().size() > 1) {
      getNameSet().set(1, alpha);
    }
    else {
      getNameSet().add(alpha);
    }
  }

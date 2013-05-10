  public net.sourceforge.czt.circus.ast.CircusProcess getSpec()
  {
	  net.sourceforge.czt.circus.ast.CircusProcess result = null;
    if (getCircusProcess().size() > 0) {
      result = getCircusProcess().get(0);
    }
    return result;
  }

  public void setSpec(net.sourceforge.czt.circus.ast.CircusProcess process)
  {
    if (getCircusProcess().size() > 0) {
      getCircusProcess().set(0, process);
    }
    else {
      getCircusProcess().add(process);
    }
  }

  public net.sourceforge.czt.circus.ast.CircusProcess getImpl()
  {
	  net.sourceforge.czt.circus.ast.CircusProcess result = null;
    if (getCircusProcess().size() > 1) {
      result = getCircusProcess().get(1);
    }
    return result;
  }

  public void setImpl(net.sourceforge.czt.circus.ast.CircusProcess process)
  {
    if (getCircusProcess().size() == 0) {
      getCircusProcess().add(null);
    }
    if (getCircusProcess().size() > 1) {
      getCircusProcess().set(1, process);
    }
    else {
      getCircusProcess().add(process);
    }
  }

  public CircusProcess getLeftProc()
  {
    CircusProcess result = null;
    if (getCircusProcess().size() > 0) {
      result = getCircusProcess().get(0);
    }
    return result;
  }

  public void setLeftProc(CircusProcess proc)
  {
    if (getCircusProcess().size() > 0) {
      getCircusProcess().set(0, proc);
    }
    else {
      getCircusProcess().add(proc);
    }
  }

  public CircusProcess getRightProc()
  {
    CircusProcess result = null;
    if (getCircusProcess().size() > 1) {
      result = getCircusProcess().get(1);
    }
    return result;
  }

  public void setRightProc(CircusProcess proc)
  {
    if (getCircusProcess().size() == 0) {
      getCircusProcess().add(null);
    }
    if (getCircusProcess().size() > 1) {
      getCircusProcess().set(1, proc);
    }
    else {
      getCircusProcess().add(proc);
    }
  }

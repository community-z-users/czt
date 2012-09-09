  public CircusProcess getSpec()
  {
    CircusProcess result = null;
    if (getCircusProcess().size() > 0) {
      result = getCircusProcess().get(0);
    }
    return result;
  }

  public void setSpec(CircusProcess process)
  {
    if (getCircusProcess().size() > 0) {
      getCircusProcess().set(0, process);
    }
    else {
      getCircusProcess().add(process);
    }
  }

  public CircusProcess getImpl()
  {
    CircusProcess result = null;
    if (getCircusProcess().size() > 1) {
      result = getCircusProcess().get(1);
    }
    return result;
  }

  public void setImpl(CircusProcess process)
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

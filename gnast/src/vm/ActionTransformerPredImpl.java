  public CircusAction getSpec()
  {
    CircusAction result = null;
    if (getCircusAction().size() > 0) {
      result = getCircusAction().get(0);
    }
    return result;
  }

  public void setSpec(CircusAction action)
  {
    if (getCircusAction().size() > 0) {
      getCircusAction().set(0, action);
    }
    else {
      getCircusAction().add(action);
    }
  }

  public CircusAction getImpl()
  {
    CircusAction result = null;
    if (getCircusAction().size() > 1) {
      result = getCircusAction().get(1);
    }
    return result;
  }

  public void setImpl(CircusAction action)
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

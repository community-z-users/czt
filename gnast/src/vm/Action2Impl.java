  public CircusAction getLeftAction()
  {
    CircusAction result = null;
    if (getCircusAction().size() > 0) {
      result = getCircusAction().get(0);
    }
    return result;
  }

  public void setLeftAction(CircusAction action)
  {
    if (getCircusAction().size() > 0) {
      getCircusAction().set(0, action);
    }
    else {
      getCircusAction().add(action);
    }
  }

  public CircusAction getRightAction()
  {
    CircusAction result = null;
    if (getCircusAction().size() > 1) {
      result = getCircusAction().get(1);
    }
    return result;
  }

  public void setRightAction(CircusAction action)
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

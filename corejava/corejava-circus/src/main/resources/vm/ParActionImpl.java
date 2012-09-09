  public NameSet getLeftNameSet()
  {
    NameSet result = null;
    if (getNameSet().size() > 0) {
      result = getNameSet().get(0);
    }
    return result;
  }

  public void setLeftNameSet(NameSet alpha)
  {
    if (getNameSet().size() > 0) {
      getNameSet().set(0, alpha);
    }
    else {
      getNameSet().add(alpha);
    }
  }

  public NameSet getRightNameSet()
  {
    NameSet result = null;
    if (getNameSet().size() > 1) {
      result = getNameSet().get(1);
    }
    return result;
  }

  public void setRightNameSet(NameSet alpha)
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

  public ChannelSet getLeftAlpha()
  {
    ChannelSet result = null;
    if (getChannelSet().size() > 0) {
      result = getChannelSet().get(0);
    }
    return result;
  }

  public void setLeftAlpha(ChannelSet alpha)
  {
    if (getChannelSet().size() > 0) {
      getChannelSet().set(0, alpha);
    }
    else {
      getChannelSet().add(alpha);
    }
  }

  public ChannelSet getRightAlpha()
  {
    ChannelSet result = null;
    if (getChannelSet().size() > 1) {
      result = getChannelSet().get(1);
    }
    return result;
  }

  public void setRightAlpha(ChannelSet alpha)
  {
    if (getChannelSet().size() == 0) {
      getChannelSet().add(null);
    }
    if (getChannelSet().size() > 1) {
      getChannelSet().set(1, alpha);
    }
    else {
      getChannelSet().add(alpha);
    }
  }

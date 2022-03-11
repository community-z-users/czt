  public net.sourceforge.czt.circus.ast.ChannelSet getLeftAlpha()
  {
	  net.sourceforge.czt.circus.ast.ChannelSet result = null;
    if (getChannelSet().size() > 0) {
      result = getChannelSet().get(0);
    }
    return result;
  }

  public void setLeftAlpha(net.sourceforge.czt.circus.ast.ChannelSet alpha)
  {
    if (getChannelSet().size() > 0) {
      getChannelSet().set(0, alpha);
    }
    else {
      getChannelSet().add(alpha);
    }
  }

  public net.sourceforge.czt.circus.ast.ChannelSet getRightAlpha()
  {
	  net.sourceforge.czt.circus.ast.ChannelSet result = null;
    if (getChannelSet().size() > 1) {
      result = getChannelSet().get(1);
    }
    return result;
  }

  public void setRightAlpha(net.sourceforge.czt.circus.ast.ChannelSet alpha)
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

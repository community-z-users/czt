  public net.sourceforge.czt.z.ast.ZNameList getZGenFormals()
  {
    if (getNameList().size() > CHANNEL_GENFORMAL_INDEX) {
      net.sourceforge.czt.z.ast.NameList rnl = getNameList().get(CHANNEL_GENFORMAL_INDEX);
      if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
        return (net.sourceforge.czt.z.ast.ZNameList) rnl;
      }
      final String message = "Expected the default (Z) implementation of NameList" +
        " but found " + String.valueOf(rnl);
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
    }
    final String message = "Invalid channel declaration name list size. Expected a value greater than " + 
        CHANNEL_GENFORMAL_INDEX + " but found " + getNameList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.ZNameList getZChannelNameList()
  {
    if (getNameList().size() > CHANNEL_NAMELIST_INDEX) {
      net.sourceforge.czt.z.ast.NameList rnl = getNameList().get(CHANNEL_NAMELIST_INDEX);
      if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
        return (net.sourceforge.czt.z.ast.ZNameList) rnl;
      }
      final String message = "Expected the default (Z) implementation of NameList" +
        " but found " + String.valueOf(rnl);
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
    }
    final String message = "Invalid channel declaration name list size. Expected a value greater than " + 
        CHANNEL_NAMELIST_INDEX + " but found " + getNameList().size();
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

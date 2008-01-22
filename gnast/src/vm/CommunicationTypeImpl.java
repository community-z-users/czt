  protected net.sourceforge.czt.z.ast.NameTypePair getChannelNTP()
  {
    if (getSignature().getNameTypePair().size() > CHANNEL_NTP_INDEX) {
      return getSignature().getNameTypePair().get(CHANNEL_NTP_INDEX);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
 
  public net.sourceforge.czt.z.ast.Name getChannelName()
  {
    return getChannelNTP().getName();  
  }  
  
  public net.sourceforge.czt.z.ast.ZName getChannelZName()
  {
    return getChannelNTP().getZName();  
  }
  
  public net.sourceforge.czt.z.ast.Type getChannelType()
  {
    return getChannelNTP().getType();  
  }
  
  public java.util.List<net.sourceforge.czt.z.ast.NameTypePair>  getCommunicationPattern()
  {
    int size = getSignature().getNameTypePair().size();
    if (size > COMM_PATTERN_INDEX) {
      return getSignature().getNameTypePair().subList(COMM_PATTERN_INDEX, size);
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();    
  }
  
  public boolean isSynchronisation()
  {
    boolean result = 
        net.sourceforge.czt.z.util.ZUtils.namesEqual(
            net.sourceforge.czt.circus.util.CircusUtils.FACTORY.getCircusFactory().createSynchName(), 
            getChannelNTP().getName());
    return result;
  }

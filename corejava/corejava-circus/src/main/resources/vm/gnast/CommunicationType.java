  static final int CHANNEL_NTP_INDEX  = 0;
  static final int COMM_PATTERN_INDEX = 1;

  /**
   * This is a convenience method. It represents the non-null channel name
   * for this communication type. It returns the Name from the first element
   * in the underlying signature as getSignature().getNameTypePair().get(CHANNEL_NTP_INDEX).getName().
   */
  net.sourceforge.czt.z.ast.Name getChannelName();
  
  /**
   * This is a convenience method. It represents the non-null channel name
   * for this communication type. It returns the Name from the first element
   * in the underlying signature as getSignature().getNameTypePair().get(CHANNEL_NTP_INDEX).getName().
   * It may throw a UnsupportedAstClassException in case the name is not a ZName
   */
  net.sourceforge.czt.z.ast.ZName getChannelZName();
  
  /**
   * This is a convenience method. It represents the non-null channel type
   * for this communication type. It returns the Type from the first element
   * in the underlying signature as getSignature().getNameTypePair().get(CHANNEL_NTP_INDEX).getType().
   * The reulst should have its generic type resolved (i.e., be an instance of Type2).
   */
  net.sourceforge.czt.z.ast.Type getChannelType();
  
  /**
   * This is a convenience method. It represents the non-null non-empty signature
   * corresponding to the communication pattern for this communication type. It 
   * returns the remainder signature from getSignature().getNameTypePair().sublist(COMM_PATTERN_INDEX, getSignature().getNameTypePair().size()).
   */
  java.util.List<net.sourceforge.czt.z.ast.NameTypePair> getCommunicationPattern();
   
  /**
   * Returns whether or not the communication type is a synchronisation or not.
   */ 
  boolean isSynchronisation();


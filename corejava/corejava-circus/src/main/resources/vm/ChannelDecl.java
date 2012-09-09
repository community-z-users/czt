  final static int CHANNEL_GENFORMAL_INDEX = 0;
  final static int CHANNEL_NAMELIST_INDEX = 1;

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of generic formal parameters for this channel declaration.
   * 
   * It returns the ZNameList from getNameList().get(0) if it is an instance of
   * ZNameList, or throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZNameList getZGenFormals();

  /**
   * This is a convenience method. It represents the non-null (possibly empty)
   * list of declared channel names for this channel declaration. If the list is
   * empty, this represennt a "channelfrom" declaration, where the getExpr() returns
   * the SchExpr the delcared channels can be found.
   *
   * It returns the ZNameList if NameList is an instance of
   * ZNameList or throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.z.ast.ZNameList getZChannelNameList();

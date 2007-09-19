  /**
   * Convenience method for backward compatibility (and clarity). It just
   * returns #getCircusCommunicationList.
   */
  net.sourceforge.czt.circus.ast.CircusCommunicationList getCommunication();

  /**
   * This is a convenience method.
   * It returns the CircusCommunicationList if CommunicationList  is an instance of
   * CircusCommunicationList or throws an UnsupportedAstClassException otherwise.
   */
  net.sourceforge.czt.circus.ast.CircusCommunicationList getCircusCommunicationList();
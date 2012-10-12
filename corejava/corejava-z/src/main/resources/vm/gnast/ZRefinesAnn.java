  Name getAbstractName();
  void setAbstractName(Name name);
  Name getConcreteName();
  void setConcreteName(Name name);

  /**
   * This is a convenience method.
   * It returns the ZName if DeclName (AbstractName) is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  ZName getZAbstractName();

  /**
   * This is a convenience method.
   * It returns the ZName if RefName (ConcreteName) is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  ZName getZConcreteName();

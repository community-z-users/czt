  Name getNewName();
  void setNewName(Name name);
  Name getOldName();
  void setOldName(Name name);

  /**
   * This is a convenience method.
   * It returns the ZName if DeclName (NewName) is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  ZName getZDeclName();

  /**
   * This is a convenience method.
   * It returns the ZName if RefName (OldName) is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  ZName getZRefName();

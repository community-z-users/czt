
  /**
   * This is a convenience method for getting the name of a conjecture.
   * Conjecture names are currently optional at the Unicode level, and 
   * are stored as annotations rather than as normal entries in the
   * CZT XML format.  This method returns a non-null String if the conjecture
   * has a name annotation, or null otherwise.  If the Z standard is
   * extended in the future so that conjecture names are compulsory
   * in the Unicode markup (as they are in the LaTeX markup), then
   * this method may be replaced by an equivalent method that
   * is automatically generated from the CZT XML schema.
   */
  String getName();
  
  void setName(Name name);

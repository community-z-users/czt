
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
  public String getName()
  {
    Name name = this.getAnn(Name.class);
    if (name instanceof ZName) {
      return ((ZName) name).getWord();
    }
    return null;
  }
  
  public void setName(Name name)
  {
    Name zname = this.getAnn(Name.class);
    if (zname != null)
    {      
      java.util.List anns = getAnns();
      for (java.util.Iterator iter = anns.iterator(); iter.hasNext(); )
      {
        Object ann = iter.next();
        if (Name.class.isInstance(ann))
        {
          iter.remove();
        }
      }
    }
    this.getAnns().add(name);
  }

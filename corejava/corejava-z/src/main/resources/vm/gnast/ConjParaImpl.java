
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
	  net.sourceforge.czt.z.ast.Name name = this.getAnn(net.sourceforge.czt.z.ast.Name.class);
    if (name instanceof net.sourceforge.czt.z.ast.ZName) {
      return ((net.sourceforge.czt.z.ast.ZName) name).getWord();
    }
    return null;
  }
  
  public void setName(net.sourceforge.czt.z.ast.Name name)
  {
	  net.sourceforge.czt.z.ast.Name zname = this.getAnn(net.sourceforge.czt.z.ast.Name.class);
    if (zname != null)
    {      
      java.util.List<Object> anns = getAnns();
      for (java.util.Iterator<Object> iter = anns.iterator(); iter.hasNext(); )
      {
        Object ann = iter.next();
        if (net.sourceforge.czt.z.ast.Name.class.isInstance(ann))
        {
          iter.remove();
        }
      }
    }
    this.getAnns().add(name);
  }

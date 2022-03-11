
  public net.sourceforge.czt.z.util.OperatorName getOperatorName()
  {
    try {
      return new net.sourceforge.czt.z.util.OperatorName(this);
    }
    catch(net.sourceforge.czt.z.util.OperatorName.OperatorNameException e) {
      return null;
    }
  }
  
  public net.sourceforge.czt.z.util.OperatorName getOperatorName(
    net.sourceforge.czt.z.util.Fixity fixity)
  {
    try {
      return new net.sourceforge.czt.z.util.OperatorName(this.getWord(), this.getStrokeList(), fixity);
    }
    catch(net.sourceforge.czt.z.util.OperatorName.OperatorNameException e) {
      return null;
    }  
  }
  

  /**
   * This is a convenience method.
   * It returns the ZStrokeList if ZStrokeList is an instance of
   * ZStrokeList and throws an UnsupportedAstClassException otherwise.
   */
  public net.sourceforge.czt.z.ast.ZStrokeList getZStrokeList()
  {
	  net.sourceforge.czt.z.ast.StrokeList strokeList = getStrokeList();
    if (strokeList instanceof net.sourceforge.czt.z.ast.ZStrokeList) {
      return (net.sourceforge.czt.z.ast.ZStrokeList) strokeList;
    }
    final String message = "Expected the default (Z) implementation of StrokeList" +
      " but found " + String.valueOf(strokeList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

   private static java.util.Set<String> idPool_ = null;	
   private static java.util.Map<String, java.util.Set<String>> nameIdPool_ = new java.util.TreeMap<String, java.util.Set<String>>(); 
   
   public static java.util.Map<String, java.util.Set<String>> nameIdPool()
   {
     return java.util.Collections.unmodifiableMap(nameIdPool_);
   }
   
   private static boolean debugZName_ = false;
   
   public static final void setDebugZName(boolean v)
   {
	   debugZName_ = v;
   }
   
   public static final boolean getDebugZName()
   {
	   return debugZName_;
   }
   

  private void setWordInternal(String word)
  {
    word_ = word;
    if (debugZName_)
    {
	    if (!nameIdPool_.containsKey(word))
	    {
	      nameIdPool_.put(word, new java.util.TreeSet<String>());
	      idPool_ = nameIdPool_.get(word);
	      //assert id_ == null; ??? could this be non-null? set id before the name?
	    }
		if (id_ != null)
		{
	      assert idPool_ != null;
		  idPool_.add(id_);
		}
	    StringBuffer result = new StringBuffer("\t\t " + instanceCount() + " setWord \t");
	    net.sourceforge.czt.z.util.ZUtils.unicodeToAscii(word, result);
	    net.sourceforge.czt.base.util.TermInstanceCountManager.log(this, result.toString());
    }
  }
  
  private void setIdInternal(String id)
  {
    id_ = id;
    if (debugZName_)
    {
	    assert idPool_ != null && word_ != null;
	    assert nameIdPool_.containsKey(word_);
	    idPool_.add(String.valueOf(id));// might be null
	    
	    StringBuffer result = new StringBuffer("\t\t " + instanceCount() + " setId \t");
	    if (id != null) net.sourceforge.czt.z.util.ZUtils.unicodeToAscii(id, result); else result.append("null");
	    net.sourceforge.czt.base.util.TermInstanceCountManager.log(this, result.toString());
    }
  }
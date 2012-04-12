
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
  public ZStrokeList getZStrokeList()
  {
    StrokeList strokeList = getStrokeList();
    if (strokeList instanceof ZStrokeList) {
      return (ZStrokeList) strokeList;
    }
    final String message = "Expected the default (Z) implementation of StrokeList" +
      " but found " + String.valueOf(strokeList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

   private static Set<String> idPool_ = null;	
   private static Map<String, Set<String>> nameIdPool_ = new TreeMap<String, Set<String>>(); 
   public static Map<String, Set<String>> nameIdPool()
   {
     return Collections.unmodifiableMap(nameIdPool_);
   }

  private void internalSetWord(String word)
  {
    word_ = word;
    if (!nameIdPool_.containsKey(word))
    {
      nameIdPool_.put(word, new TreeSet<String>());
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
    TermInstanceCountManager.log(this, result.toString());
  }
  
  private void internalSetId(String id)
  {
    id_ = id;
    assert idPool_ != null && word_ != null;
    assert nameIdPool_.containsKey(word_);
    idPool_.add(String.valueOf(id));// might be null
    
    StringBuffer result = new StringBuffer("\t\t " + instanceCount() + " setId \t");
    if (id != null) net.sourceforge.czt.z.util.ZUtils.unicodeToAscii(id, result); else result.append("null");
    TermInstanceCountManager.log(this, result.toString());
  }

  public net.sourceforge.czt.z.ast.ZParaList getZParaList()
  {
    net.sourceforge.czt.z.ast.ParaList pl = getParaList();
    if (pl instanceof net.sourceforge.czt.z.ast.ZParaList) {
      return (net.sourceforge.czt.z.ast.ZParaList) pl;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }
  
  // TODO: MAKE THIS MORE EFFICIENT?
  public net.sourceforge.czt.z.ast.Para getStatePara()
  {
    List<net.sourceforge.czt.z.ast.Para> result = new ArrayList<net.sourceforge.czt.z.ast.Para>();
    for(net.sourceforge.czt.z.ast.Para para : getZParaList())
    {
      if (net.sourceforge.czt.circus.util.CircusUtils.isCircusState(para))
      {
        result.add(para);
      }
    }
    // if 0 = invalid; if >1 duplicated.
    if (result.size() != 1)
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException("Invalid state paragraph for basic process.");
    
    net.sourceforge.czt.z.ast.Para r = result.get(0);
    
    assert result.size() == 1 && 
           net.sourceforge.czt.circus.util.CircusUtils.isCircusState(r);
    
    // state  is actionPara ==> OnTheFlyAction    
    assert (!(r instanceof net.sourceforge.czt.circus.ast.ActionPara) || 
            net.sourceforge.czt.circus.util.CircusUtils.isOnTheFly(r)
           );
    return r;
  }
  
  public net.sourceforge.czt.circus.ast.CircusAction getMainAction()
  {  
    List<net.sourceforge.czt.circus.ast.ActionPara> result = new ArrayList<net.sourceforge.czt.circus.ast.ActionPara>();
    for(net.sourceforge.czt.z.ast.Para para : getOnTheFlyPara())
    {
      assert net.sourceforge.czt.circus.util.CircusUtils.isOnTheFly(para);
      net.sourceforge.czt.circus.ast.ActionPara ap = (net.sourceforge.czt.circus.ast.ActionPara)para;      
      if (ap.getZName().getWord().equals(net.sourceforge.czt.circus.util.CircusUtils.DEFAULT_MAIN_ACTION_NAME))
      {
        result.add(ap);
      }      
    }
    
    // if 0 = invalid; if >1 duplicated.
    if (result.size() != 1)
      throw new net.sourceforge.czt.base.util.UnsupportedAstClassException("Invalid main action for basic process.");
    
    assert result.size() == 1 && 
           net.sourceforge.czt.circus.util.CircusUtils.isOnTheFly(result.get(0)) &&
           result.get(0).getZName().getWord().equals(net.sourceforge.czt.circus.util.CircusUtils.DEFAULT_MAIN_ACTION_NAME);
    return result.get(0).getCircusAction();
  }

  public java.util.List<? extends net.sourceforge.czt.z.ast.Para> getLocalPara()
  {
    net.sourceforge.czt.z.ast.ZParaList result = net.sourceforge.czt.z.util.ZUtils.FACTORY.createZParaList();    
    result.addAll(getZParaList());
    
    java.util.List<net.sourceforge.czt.circus.ast.ActionPara> onTheFly = getOnTheFlyPara();    
    result.removeAll(onTheFly);
    
    assert (result.size() == getZParaList().size() - onTheFly.size());    
    return java.util.Collections.unmodifiableList(result);
  }  
  
  public java.util.List<net.sourceforge.czt.circus.ast.ActionPara> getOnTheFlyPara()
  {
    java.util.List<net.sourceforge.czt.circus.ast.ActionPara> result = 
      new java.util.ArrayList<net.sourceforge.czt.circus.ast.ActionPara>();
    for(net.sourceforge.czt.z.ast.Para para : getZParaList())
    {
      if (para instanceof net.sourceforge.czt.circus.ast.ActionPara)
      {
        net.sourceforge.czt.circus.ast.ActionPara ap = (net.sourceforge.czt.circus.ast.ActionPara)para;
        if (ap.getCircusAction().getAnn(net.sourceforge.czt.circus.ast.OnTheFlyDefAnn.class) != null)
        {
          result.add(ap);
        }
      }
    }
    return java.util.Collections.unmodifiableList(result);
  }  


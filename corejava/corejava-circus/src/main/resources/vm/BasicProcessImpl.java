  public net.sourceforge.czt.z.ast.ZParaList getZParaList()
  {
    net.sourceforge.czt.z.ast.ParaList pl = getParaList();
    if (pl instanceof net.sourceforge.czt.z.ast.ZParaList) {
      return (net.sourceforge.czt.z.ast.ZParaList) pl;
    }
    final String message = "Expected the default (Z) implementation of ParaList" +
      " but found " + String.valueOf(pl);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
    
  public net.sourceforge.czt.z.ast.AxPara getStatePara()
  {       
    for(net.sourceforge.czt.z.ast.Para para : getZParaList())
    {
      if (net.sourceforge.czt.circus.util.CircusUtils.isStatePara(para))
      {        
        assert net.sourceforge.czt.z.util.ZUtils.isHorizontalDef(para) : "state para is not horizontal AxPara";
        return (net.sourceforge.czt.z.ast.AxPara)para;
      }
    }
    return null;    
    // DESIGN: Parser now make both versions a horizontal box.
    //         This makes the type checker life easier and more uniform
    // state  is actionPara ==> OnTheFlyAction    
    // assert (!(r instanceof net.sourceforge.czt.circus.ast.ActionPara) || 
    //        net.sourceforge.czt.circus.util.CircusUtils.isOnTheFly(r)
    //       );
  }
  
  public boolean isStateValid()
  {
    net.sourceforge.czt.z.ast.AxPara state = getStatePara();
    boolean result = state != null;    
    if (result)
    {
      for(net.sourceforge.czt.z.ast.Para para : getZParaList())
      {
        if (net.sourceforge.czt.circus.util.CircusUtils.isStatePara(para))
        {        
          // if more than one is found, then stop and say "false".
          result = (para == state);
          if (!result) break;
        }
      }
    }
    return result;
  }
  
  public boolean isDefaultState()
  {
    boolean result = isStateValid();
    if (result)
    {
      net.sourceforge.czt.z.ast.AxPara state = getStatePara();
      result = net.sourceforge.czt.z.util.ZUtils.assertZName(
        net.sourceforge.czt.z.util.ZUtils.getSchemaName(state)).getWord().startsWith(
          net.sourceforge.czt.circus.util.CircusUtils.DEFAULT_PROCESS_STATE_NAME);
    }
    return result;
  }
  
  public net.sourceforge.czt.circus.ast.CircusAction getMainAction()
  {      
    for(net.sourceforge.czt.z.ast.Para para : getOnTheFlyPara())
    {
      if (para instanceof net.sourceforge.czt.circus.ast.ActionPara &&
          net.sourceforge.czt.circus.util.CircusUtils.isOnTheFly(para) &&
          ((net.sourceforge.czt.circus.ast.ActionPara)para).getZName().getWord().startsWith(
              net.sourceforge.czt.circus.util.CircusUtils.DEFAULT_MAIN_ACTION_NAME))          
      {
        return ((net.sourceforge.czt.circus.ast.ActionPara)para).getCircusAction();
      }  
    }
    return null;
  }
  
  public boolean isMainActionValid()
  {
    net.sourceforge.czt.circus.ast.CircusAction ma = getMainAction();
    boolean result = ma != null;    
    if (result)
    {
      for(net.sourceforge.czt.z.ast.Para para : getOnTheFlyPara())
      {
        if (para instanceof net.sourceforge.czt.circus.ast.ActionPara &&
            net.sourceforge.czt.circus.util.CircusUtils.isOnTheFly(para) &&
            ((net.sourceforge.czt.circus.ast.ActionPara)para).getZName().getWord().startsWith(
                net.sourceforge.czt.circus.util.CircusUtils.DEFAULT_MAIN_ACTION_NAME))          
        {
          // if more than one is found, then stop and say "false".
          result = (((net.sourceforge.czt.circus.ast.ActionPara)para).getCircusAction() == ma);
          if (!result) break;
        }  
      }
    }
    return result;
  }

  public java.util.List<? extends net.sourceforge.czt.z.ast.Para> getLocalPara()
  {
    net.sourceforge.czt.z.ast.ZParaList result = net.sourceforge.czt.z.util.ZUtils.FACTORY.createZParaList();    
    result.addAll(getZParaList());
    
    java.util.List<? extends net.sourceforge.czt.z.ast.Para> onTheFly = getOnTheFlyPara();    
    result.removeAll(onTheFly);
    
    assert (result.size() == getZParaList().size() - onTheFly.size());    
    return java.util.Collections.unmodifiableList(result);
  }  
  
  public java.util.List<? extends net.sourceforge.czt.z.ast.Para> getOnTheFlyPara()
  {
    net.sourceforge.czt.z.ast.ZParaList result = net.sourceforge.czt.z.util.ZUtils.FACTORY.createZParaList();    
    for(net.sourceforge.czt.z.ast.Para para : getZParaList())
    {
      if (net.sourceforge.czt.circus.util.CircusUtils.isOnTheFly(para))
      {
        result.add(para);
      }      
    }
    return java.util.Collections.unmodifiableList(result);
  }  

  public net.sourceforge.czt.z.ast.Name getStateParaName()
  {
    net.sourceforge.czt.z.ast.Name result = null;
    net.sourceforge.czt.z.ast.AxPara state = getStatePara();
    if (state != null)
    {
      result = net.sourceforge.czt.circus.util.CircusUtils.getSchemaName(state);
    }
    return result;    
  }

  public net.sourceforge.czt.z.ast.ZName getStateParaZName()
  {
    net.sourceforge.czt.z.ast.Name result = getStateParaName();
    if (result != null)
    {
      return net.sourceforge.czt.z.util.ZUtils.assertZName(result);
    }
    return null;
  }


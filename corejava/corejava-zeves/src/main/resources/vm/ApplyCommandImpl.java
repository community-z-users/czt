
  public net.sourceforge.czt.z.ast.Name getThmName()
  {
    net.sourceforge.czt.z.ast.ZNameList names = getZNameList();
    if (names.size() == 1)
    {
    	return names.get(0);
    }
    else
    {
    	final String message = "Expected a singleton ZNameList for ApplyCommand theorem name, but found " + String.valueOf(names);
    	throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
	}
  }

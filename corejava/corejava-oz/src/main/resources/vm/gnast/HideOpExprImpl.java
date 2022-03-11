
  public net.sourceforge.czt.z.ast.ZNameList getName()
  {
	  net.sourceforge.czt.z.ast.NameList refNameList = getNameList();
    if (refNameList instanceof net.sourceforge.czt.z.ast.ZNameList) {
      return ((net.sourceforge.czt.z.ast.ZNameList) refNameList).getName();
    }
    final String message = "Expected the default (Z) implementation of NameList" +
      " but found " + String.valueOf(refNameList);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }


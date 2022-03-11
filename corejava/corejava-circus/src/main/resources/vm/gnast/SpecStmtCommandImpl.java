
  public net.sourceforge.czt.z.ast.ZNameList getZFrame()
  {
    net.sourceforge.czt.z.ast.NameList rnl = getFrame();
    if (rnl instanceof net.sourceforge.czt.z.ast.ZNameList) {
      return (net.sourceforge.czt.z.ast.ZNameList) rnl;
    }
    final String message = "Expected the default (Z) implementation of NameList" +
      " but found " + String.valueOf(rnl);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }
  
  public net.sourceforge.czt.z.ast.Pred getPre()
  {
    net.sourceforge.czt.z.ast.Pred result = null;
    if (getPred().size() > 0) {
      result = getPred().get(0);
    }
    return result;
  }

  public void setPre(net.sourceforge.czt.z.ast.Pred pred)
  {
    if (getPred().size() > 0) {
      getPred().set(0, pred);
    }
    else {
      getPred().add(pred);
    }
  }

  public net.sourceforge.czt.z.ast.Pred getPost()
  {
    net.sourceforge.czt.z.ast.Pred result = null;
    if (getPred().size() > 1) {
      result = getPred().get(1);
    }
    return result;
  }

  public void setPost(net.sourceforge.czt.z.ast.Pred pred)
  {
    if (getPred().size() == 0) {
      getPred().add(null);
    }
    if (getPred().size() > 1) {
      getPred().set(1, pred);
    }
    else {
      getPred().add(pred);
    }
  }



  public net.sourceforge.czt.z.util.OperatorName getOperatorName()
  {
    try {
      return new net.sourceforge.czt.z.util.OperatorName(this);
    }
    catch(net.sourceforge.czt.z.util.OperatorName.OperatorNameException e) {
      return null;
    }
  }

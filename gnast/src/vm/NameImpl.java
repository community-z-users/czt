
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append(getWord());
    for (Iterator iter = getStroke().iterator(); iter.hasNext(); ) {
      Stroke stroke = (Stroke) iter.next();
      result.append(stroke.toString());
    }
    return result.toString();
  }

  public net.sourceforge.czt.z.util.OperatorName getOperatorName()
  {
    try {
      return new net.sourceforge.czt.z.util.OperatorName(getWord());
    }
    catch(net.sourceforge.czt.z.util.OperatorName.OperatorNameException e) {
      return null;
    }
  }

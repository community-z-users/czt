
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("(");
    for (java.util.Iterator iter = getType().iterator(); iter.hasNext(); ) {
      result.append(iter.next().toString());
      if (iter.hasNext()) result.append(" x ");
    }
    result.append(")");
    return result.toString();
  }


  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("[");
    java.util.List list = getSignature().getNameTypePair();
    for (java.util.Iterator iter = list.iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      result.append(pair.getName());
      result.append(" : "); 
      result.append(pair.getType());
      if (iter.hasNext()) result.append("; ");
    }
    result.append("]");
    return result.toString();
  }

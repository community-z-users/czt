
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("[");
    java.util.List list = getSignature().getNameTypePair();
    for (java.util.Iterator iter = list.iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      result.append(pair.getName().toString());
      result.append(" : "); 
      result.append(pair.getType().toString());
      if (iter.hasNext()) result.append("; ");
    }
    return result.toString();
  }

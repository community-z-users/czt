  public String toString()
  {
    StringBuffer result = new StringBuffer();
    java.util.List list = getNameTypePair();
    for (java.util.Iterator iter = list.iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      result.append(pair.getName());
      result.append(" : ");
      result.append(pair.getType());
      if (iter.hasNext()) result.append("; ");
    }
    return result.toString();
  }

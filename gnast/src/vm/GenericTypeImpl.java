
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append("[");
    for (java.util.Iterator iter = getName().iterator(); iter.hasNext(); ) {
      result.append(iter.next());
      if (iter.hasNext()) result.append(", ");
    }
    result.append("] ");
    result.append(getType());
    if (getOptionalType() != null) {
      result.append(", ");
      result.append(getOptionalType());
    }
    return result.toString();
  }

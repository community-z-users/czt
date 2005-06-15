
  public String toString()
  {
    String result = new String();
    List classes = getClasses();
    if (classes.size() > 0) {
      result += "{";
      for (Iterator iter = classes.iterator(); iter.hasNext(); ) {
        ClassRef classRef = (ClassRef) iter.next();
        result += classRef.toString();
        if (iter.hasNext()) {
          result += ", ";
        }
      }
      result += "}";
    }
    return result;
  }

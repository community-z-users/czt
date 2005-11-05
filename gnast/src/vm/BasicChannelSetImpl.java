  public String toString()
  {
    StringBuilder builder = new StringBuilder("{| ");
    if (getRefNameList() instanceof ZRefNameList) {
      java.util.Iterator<RefName> it = getZRefNameList().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
              builder.append(", ");
      }
    } else {
      builder.append(String.valueOf(getRefNameList()));
    } 
    builder.append(" |}");
    return builder.toString();
  }


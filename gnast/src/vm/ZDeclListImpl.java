  public String toString()
  {
    StringBuilder builder = new StringBuilder();
    java.util.Iterator<Decl> it = iterator();
    while(it.hasNext()) {
        builder.append(it.next().toString());
        if (it.hasNext())
          builder.append("\n");
    }
    return builder.toString();
  } 

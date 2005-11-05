  public String toString()
  {
    StringBuilder builder = new StringBuilder();
    if (getDeclName() != null) {
      java.util.Iterator<DeclName> it = getDeclName().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
            builder.append(", ");
      }
    }
    builder.append(": ");
    builder.append(String.valueOf(getExpr()));
    return builder.toString();
  }

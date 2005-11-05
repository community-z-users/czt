  public String toString()
  {
    StringBuilder builder = new StringBuilder();
    if (getDeclList() != null) {
      builder.append(String.valueOf(getDeclList()));
    }
    builder.append(" | ");
    if (getPred() != null) {
      builder.append(String.valueOf(getPred()));
    }
    return builder.toString();
  } 

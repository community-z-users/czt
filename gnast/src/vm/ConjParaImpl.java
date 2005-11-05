  public String toString()
  {
    StringBuilder builder = new StringBuilder();
    if (getDeclName() != null)
        builder.append(getDeclName().toString());
    builder.append(" |-? ");
    builder.append(String.valueOf(getPred()));
    return builder.toString();
  } 

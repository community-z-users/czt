  public String toString()
  {
    StringBuilder builder = new StringBuilder("process ");
    builder.append(String.valueOf(getDeclName()));
    if (getGenFormals() != null)
      builder.append(String.valueOf(getGenFormals()));
    builder.append(String.valueOf(getCircusProcess()));
    return builder.toString();
  }


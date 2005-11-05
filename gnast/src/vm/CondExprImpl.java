  public String toString()
  {
    StringBuilder builder = new StringBuilder("if ");
    builder.append(String.valueOf(getPred()));
    builder.append(" then \n\t ");
    builder.append(String.valueOf(getLeftExpr()));
    if (getRightExpr() != null) {
      builder.append(" \nelse \n\t");
      builder.append(getRightExpr().toString());
    }
    return builder.toString();
  }
 

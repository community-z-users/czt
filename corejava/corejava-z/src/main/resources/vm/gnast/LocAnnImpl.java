
  public java.math.BigInteger getEnd()
  {
    if (getStart() != null && getLength() != null) {
      return getStart().add(getLength());
    }
    return null;
  }

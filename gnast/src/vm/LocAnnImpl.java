
  public java.math.BigInteger getEnd()
  {
    if (getStart() != null && getLength() != null) {
      return getStart().add(getLength());
    }
    return null;
  }

  public void setLine(int line)
  {
    setLine(java.math.BigInteger.valueOf(line));
  }

  public void setCol(int col)
  {
    setCol(java.math.BigInteger.valueOf(col));
  }

  public void setStart(int start)
  {
    setStart(java.math.BigInteger.valueOf(start));
  }

  public void setLength(int length)
  {
    setLength(java.math.BigInteger.valueOf(length));
  }

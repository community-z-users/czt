
  /**
   * This is a convenience method.
   * It returns the ZNumeral if Numeral is an instance of
   * ZNumeral and throws an UnsupportedAstClassException otherwise.
   */
  public ZNumeral getZNumeral()
  {
    Numeral numeral = getNumeral();
    if (numeral instanceof ZNumeral) {
      return (ZNumeral) numeral;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  /**
   * This is a convenience method.
   * It returns the value of the ZNumeral if Numeral is an instance of
   * ZNumeral and throws an UnsupportedAstClassException otherwise.
   */
  public java.math.BigInteger getValue()
  {
    Numeral numeral = getNumeral();
    if (numeral instanceof ZNumeral) {
      return new java.math.BigInteger(((ZNumeral) numeral).getValue().toString());
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }


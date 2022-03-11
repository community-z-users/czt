
  /**
   * This is a convenience method.
   * It returns the net.sourceforge.czt.z.ast.ZNumeral if Numeral is an instance of
   * net.sourceforge.czt.z.ast.ZNumeral and throws an UnsupportedAstClassException otherwise.
   */
  public net.sourceforge.czt.z.ast.ZNumeral getZNumeral()
  {
	  net.sourceforge.czt.z.ast.Numeral numeral = getNumeral();
    if (numeral instanceof net.sourceforge.czt.z.ast.ZNumeral) {
      return (net.sourceforge.czt.z.ast.ZNumeral) numeral;
    }
    final String message = "Expected the default (Z) implementation of Numeral" +
      " but found " + String.valueOf(numeral);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  /**
   * This is a convenience method.
   * It returns the value of the net.sourceforge.czt.z.ast.ZNumeral if Numeral is an instance of
   * net.sourceforge.czt.z.ast.ZNumeral and throws an UnsupportedAstClassException otherwise.
   */
  public java.math.BigInteger getValue()
  {
    net.sourceforge.czt.z.ast.Numeral numeral = getNumeral();
    if (numeral instanceof net.sourceforge.czt.z.ast.ZNumeral) {
      return new java.math.BigInteger(((net.sourceforge.czt.z.ast.ZNumeral) numeral).getValue().toString());
    }
    final String message = "Expected the default (Z) implementation of Numeral" +
      " but found " + String.valueOf(numeral);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }


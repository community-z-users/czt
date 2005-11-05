
  /**
   * This is a convenience method.
   * It returns the ZSchText if SchText is an instance of
   * ZSchText and throws an UnsupportedAstClassException otherwise.
   */
  public ZSchText getZSchText()
  {
    SchText schText = getSchText();
    if (schText instanceof ZSchText) {
      return (ZSchText) schText;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public String toString()
  {
    StringBuilder builder = new StringBuilder();
    if (getDeclName() != null)
      builder.append(getDeclName().toString());
    switch(getBox()) {
      case AxBox:
        builder.append(String.valueOf(getSchText()));
        break;
      case OmitBox:
      case SchBox:
        if ((getSchText() instanceof ZSchText) &&
             getZSchText().getDeclList() instanceof ZDeclList) {
            ConstDecl cd = (ConstDecl)getZSchText().getZDeclList().get(0);
            builder.append(String.valueOf(cd));
        } else {
            builder.append(String.valueOf(getSchText()));
        }
        break;
    }
    return builder.toString();
  }


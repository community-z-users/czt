  public String toString()
  {
    StringBuilder builder = new StringBuilder("(");
    if (getDeclList() instanceof ZDeclList) {
      java.util.Iterator<Decl> it = getZDeclList().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
              builder.append("; ");
      }
    } else {
      builder.append(String.valueOf(getDeclList()));
    }
    builder.append(") @ (");
    builder.append(String.valueOf(getCircusAction()));
    builder.append(")");
    return builder.toString();
  }





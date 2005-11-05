  public String toString()
  {
    StringBuilder builder = new StringBuilder("(");
      if (getExprList() instanceof ZExprList) {
          java.util.Iterator<Expr> it = getZExprList().iterator();
          while(it.hasNext()) {
              builder.append(it.next().toString());
              if (it.hasNext())
                  builder.append(", ");
          }
      } else {
          builder.append(String.valueOf(getExprList()));
      }
      builder.append(")");
      return builder.toString();
  } 

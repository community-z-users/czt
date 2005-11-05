  public String toString()
  {
    if (getExprList() instanceof ZExprList) {
        StringBuilder builder = new StringBuilder("(");
        java.util.Iterator<Expr> it = getZExprList().iterator();
        while(it.hasNext()) {
            builder.append(it.next().toString());
            if (it.hasNext())
                builder.append(" X ");
        }
        builder.append(")");
        return builder.toString();
    } else {
        return super.toString();
    }
  } 

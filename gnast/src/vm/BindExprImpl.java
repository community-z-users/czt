  public String toString()
  {
    StringBuilder builder = new StringBuilder("{| ");
    if (getDeclList() instanceof ZDeclList) {
        java.util.Iterator<Decl> it = getZDeclList().iterator();
        while(it.hasNext()) {
            builder.append(it.next().toString());
            if (it.hasNext())
                builder.append(";\n");
        }
    } else {
        builder.append(super.toString());
    }
    builder.append(" |}");
    return builder.toString();
  }
  

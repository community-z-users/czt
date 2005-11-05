  public String toString()
    {
        StringBuilder builder = new StringBuilder("Theta ");
        builder.append(String.valueOf(getExpr()));
        if (getStroke() != null) {
          java.util.Iterator<Stroke> it = getStroke().iterator();
          while(it.hasNext()) {
              builder.append(it.next().toString());
          }
        }
        return builder.toString();
    } 

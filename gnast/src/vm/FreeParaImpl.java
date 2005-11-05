  public String toString()
  {
    StringBuilder builder = new StringBuilder();
    if (getFreetype() != null) {
      java.util.Iterator<Freetype> it = getFreetype().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
              builder.append(" & \n");
      }
    }
    return builder.toString();
  } 

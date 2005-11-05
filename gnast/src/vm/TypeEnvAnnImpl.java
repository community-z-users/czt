  public String toString()
  {
    StringBuilder builder = new StringBuilder("TypeEnv[");
    if (getNameTypePair() != null) {
      java.util.Iterator<NameTypePair> it = getNameTypePair().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
              builder.append("\n");
      }
    }
    builder.append("]");
    return builder.toString();
  }
 

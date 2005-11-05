  public String toString()
  {
    StringBuilder builder = new StringBuilder("channel ");
    if (getChannelDecl() != null) {
      java.util.Iterator<ChannelDecl> it = getChannelDecl().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
              builder.append("; ");
      }
    }
    return builder.toString();
  }




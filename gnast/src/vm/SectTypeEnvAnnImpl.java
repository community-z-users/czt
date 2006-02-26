  public String toString()
  {
    StringBuilder builder = new StringBuilder("SectTypeEnv[");
    if (getNameSectTypeTriple() != null) {
      java.util.Iterator<NameSectTypeTriple> it = getNameSectTypeTriple().iterator();
      while(it.hasNext()) {
          builder.append(it.next().toString());
          if (it.hasNext())
              builder.append("\n");
      }
    }
    builder.append("]");
    return builder.toString();
  }
 

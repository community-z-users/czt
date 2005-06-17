
  public String toString()
  {
    String result = getRefName().toString();
    List types = getType2();
    if (types.size() > 0) {
      result += "[";
      for (Iterator iter = types.iterator(); iter.hasNext(); ) {
        Type2 type2 = (Type2) iter.next();
        result += type2.toString();
        if (iter.hasNext()) {
          result += ", ";
        }
      }
      result += "]";
    }
    List rename = getNameNamePair(); 	 
    if (rename.size() > 0) { 	 
      result += "["; 	 
      for (Iterator iter = types.iterator(); iter.hasNext(); ) { 	 
        NameNamePair pair = (NameNamePair) iter.next(); 	 
        result += pair.getNewName() + "/" + pair.getOldName(); 	 
        if (iter.hasNext()) { 	 
          result += ", "; 	 
        } 	 
      } 	 
      result += "]"; 	 
    }
    return result;
  }

  /**
   * This is a convenience method.
   * It returns the ZRefName if RefName is an instance of
   * ZRefName and throws an UnsupportedAstClassException otherwise.
   */
  public ZRefName getZRefName()
  {
    RefName refName = getRefName();
    if (refName instanceof ZRefName) {
      return (ZRefName) refName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public String toString()
  {
    String result = getRefName().toString();
    List<Type2> types = getType();
    if (types.size() > 0) {
      result += "[";
      for (Iterator<Type2> iter = types.iterator(); iter.hasNext(); ) {
        Type2 type = iter.next();
        result += type.toString();
        if (iter.hasNext()) {
          result += ", ";
        }
      }
      result += "]";
    }
    List<NewOldPair> rename = getNewOldPair();
    if (rename.size() > 0) {
      result += "[";
      for (Iterator<NewOldPair> iter = rename.iterator(); iter.hasNext(); ) {
        NewOldPair pair = iter.next();
        result += pair.getNewName() + "/" + pair.getOldName();
        if (iter.hasNext()) {
          result += ", ";
        }
      }
      result += "]";
    }
    return result;
  }

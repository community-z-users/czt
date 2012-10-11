  public Name getAbstractName()
  {
    if (getName().size() > 0) {
      return getName().get(0);
    }
    return null;
  }

  public void setAbstractName(Name name)
  {
    if (getName().size() > 0) {
      getName().set(0, name);
    }
    else {
      getName().add(name);
    }
  }

  public Name getConcreteName()
  {
    if (getName().size() > 1) {
      return getName().get(1);
    }
    return null;
  }

  public void setConcreteName(Name name)
  {
    if (getName().size() == 0) {
      getName().add(null);
    }
    if (getName().size() > 1) {
      getName().set(1, name);
    }
    else {
      getName().add(name);
    }
  }

  public ZName getZAbstractName()
  {
    Name declName = getAbstractName();
    if (declName instanceof ZName) {
      return (ZName) declName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(declName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public ZName getZConcreteName()
  {
    Name refName = getConcreteName();
    if (refName instanceof ZName) {
      return (ZName) refName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(refName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }


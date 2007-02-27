  public Name getNewName()
  {
    if (getName().size() > 0) {
      return getName().get(0);
    }
    return null;
  }

  public void setNewName(Name name)
  {
    if (getName().size() > 0) {
      getName().set(0, name);
    }
    else {
      getName().add(name);
    }
  }

  public Name getOldName()
  {
    if (getName().size() > 1) {
      return getName().get(1);
    }
    return null;
  }

  public void setOldName(Name name)
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

  public ZName getZDeclName()
  {
    Name declName = getNewName();
    if (declName instanceof ZName) {
      return (ZName) declName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }

  public ZName getZRefName()
  {
    Name refName = getOldName();
    if (refName instanceof ZName) {
      return (ZName) refName;
    }
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException();
  }


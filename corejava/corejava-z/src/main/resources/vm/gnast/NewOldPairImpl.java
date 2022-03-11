  public net.sourceforge.czt.z.ast.Name getNewName()
  {
    if (getName().size() > 0) {
      return getName().get(0);
    }
    return null;
  }

  public void setNewName(net.sourceforge.czt.z.ast.Name name)
  {
    if (getName().size() > 0) {
      getName().set(0, name);
    }
    else {
      getName().add(name);
    }
  }

  public net.sourceforge.czt.z.ast.Name getOldName()
  {
    if (getName().size() > 1) {
      return getName().get(1);
    }
    return null;
  }

  public void setOldName(net.sourceforge.czt.z.ast.Name name)
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

  public net.sourceforge.czt.z.ast.ZName getZDeclName()
  {
	  net.sourceforge.czt.z.ast.Name declName = getNewName();
    if (declName instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) declName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(declName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public net.sourceforge.czt.z.ast.ZName getZRefName()
  {
	  net.sourceforge.czt.z.ast.Name refName = getOldName();
    if (refName instanceof net.sourceforge.czt.z.ast.ZName) {
      return (net.sourceforge.czt.z.ast.ZName) refName;
    }
    final String message = "Expected the default (Z) implementation of Name" +
      " but found " + String.valueOf(refName);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }


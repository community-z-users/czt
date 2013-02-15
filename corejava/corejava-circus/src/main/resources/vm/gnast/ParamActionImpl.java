  public boolean isParamCommand()
  {        
    // if not ZDeclList, assume it is ParamAction with Jokers
    // NOTE: this doesn't resolve ParamCommand with jokers
    if (getDeclList() instanceof net.sourceforge.czt.z.ast.ZDeclList)
    {
      for(net.sourceforge.czt.z.ast.Decl d : getZDeclList())
      {
        // if not qualified decl, it must be ParamAction - return false
        if (!(d instanceof net.sourceforge.czt.circus.ast.QualifiedDecl))
          return false;
      }
      // otherwise if all are QualifiedDecl, then it is ParamCommand
      return true;
    }
    return false;    
  }

package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.TypeEnvAnn;
import net.sourceforge.czt.z.ast.ZFactory;

import net.sourceforge.czt.typecheck.util.typeerror.*;

import net.sourceforge.czt.typecheck.z.TypeChecker;

public class VariableTypeEnv
  implements TypeEnvInt
{
  private ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  public NameTypePair addNameTypePair(NameTypePair ntPair)
    throws TypeException
  {
    return null;
  }

  public NameTypePair search(DeclName dn)
  {
    return null;
  }

  public void enterScope()
  {
  }

  public TypeEnvAnn exitScope()
  {
    return factory_.createTypeEnvAnn();
  }
}

package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.TypeEnvAnn;

import net.sourceforge.czt.typecheck.util.typeerror.*;

import net.sourceforge.czt.typecheck.z.TypeChecker;

public interface TypeEnvInt
{
  NameTypePair addNameTypePair(NameTypePair ntPair) throws TypeException;
  NameTypePair search(DeclName dn);
  void enterScope();
  TypeEnvAnn exitScope();
}

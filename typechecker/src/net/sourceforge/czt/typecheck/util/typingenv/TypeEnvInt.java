package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.TypeEnvAnn;

import net.sourceforge.czt.typecheck.util.typeerror.*;

import net.sourceforge.czt.typecheck.z.TypeChecker;

public interface TypeEnvInt {
	public NameTypePair addNameTypePair(NameTypePair ntPair) throws TypeException;
	
	public NameTypePair search(DeclName dn);
	
	public void enterScope();
	
	public TypeEnvAnn exitScope();
}
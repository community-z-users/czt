package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
//import java.util.Stack;
import java.util.Vector;
import java.util.List;

import net.sourceforge.czt.typecheck.util.typeerror.*;
//import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.z.*;

import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.TypeEnvAnn;
import net.sourceforge.czt.z.ast.ZFactory;

public class TypeEnv implements TypeEnvInt {
	ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
	Vector TypeEnvAnns;
	int curDepth;

	public TypeEnv () {
		curDepth = 2;
		TypeEnvAnns = new Vector(curDepth);
		for (int i = 0; i < curDepth; i++) {
			TypeEnvAnns.add(i, factory_.createTypeEnvAnn());
		}
	}

	public void enterScope() {
		TypeEnvAnns.add(curDepth++, factory_.createTypeEnvAnn());
	}

	public TypeEnvAnn  exitScope() {
		return (TypeEnvAnn) TypeEnvAnns.remove(--curDepth);
	}

	public NameTypePair addNameTypePair(NameTypePair ntPair) throws TypeException {
		NameTypePair result = null;

		DeclName dn = ntPair.getName();
		String name = dn.getWord();
		NameTypePair pair1 = search(dn);

		if (pair1 == null) {
			add(ntPair);
			result = ntPair;
		}
		else {
			Type ntType = ntPair.getType();
			Type type1 = pair1.getType();
			if (TypeChecker.unify(ntType, type1) == false) {
				result = pair1;
				throw new TypeException(ErrorKind.REDECLARATION, ntPair);
			}
			else {
				result = ntPair;
			}
		}

		return result;
	}

	private void add(NameTypePair ntPair) {
		TypeEnvAnn env = top();
		List nameTypePairs = env.getNameTypePair();
		nameTypePairs.add(ntPair);
	}

	public NameTypePair search(DeclName dn) {
		NameTypePair result = null;
		for (int i = curDepth - 1; i >= 0; i--) {
			TypeEnvAnn env = (TypeEnvAnn) TypeEnvAnns.get(i);
			NameTypePair temp = searchLocal(env, dn);
			if (temp != null) {
				result = temp;
				break;
			}
		}
		return result;
	}

	// changed this method and now it search for NameTypePair not only by the name string,
	// but also by the strokes & Ids
	private NameTypePair searchLocal(TypeEnvAnn env, DeclName dn) {
		NameTypePair result = null;
		NameTypePair temp = null;
		List list = env.getNameTypePair();
		String name = dn.getWord();
		
		DeclName dn1 = null;
		for (int i = 0; i < list.size(); i++) {
			temp = (NameTypePair) list.get(i);
			dn1 = temp.getName();
			String name1 = dn1.getWord();
			if (name.equals(name1)) {
				if (TypeChecker.strokesAgree(dn.getStroke(), dn1.getStroke()) && TypeChecker.IdsAgree(dn, dn1)) {
					result = temp;
					break;
				}
			}
		}

		return result;
	}

	private TypeEnvAnn top() {
		TypeEnvAnn env = (TypeEnvAnn) TypeEnvAnns.get(curDepth-1);

		return env;
	}

	public int getCount() {
		int result = 0;
		for (int i = 0; i < curDepth; i++) {
			TypeEnvAnn env = (TypeEnvAnn) TypeEnvAnns.get(i);
			result += env.getNameTypePair().size();
		}

		return result;
	}
}
package net.sourceforge.czt.eclipse.editors.parser;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.visitor.NodeNameVisitor;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * @author Chengdong Xu
 */
public class TypesFinder {
	private static Visitor<String> getNodeNameVisitor_ = new NodeNameVisitor();
	
	public static List<Triple> getTypes(Spec spec, SectionManager manager) {
		List<Triple> triples = new ArrayList<Triple>();
		if (spec != null) {
			for (Sect sect : spec.getSect()) {
				if (sect instanceof ZSect)
					triples.addAll(visitZSect((ZSect)sect, manager));
			}
		}
		
		return triples;
	}

	private static List<Triple> visitZSect(ZSect zSect, SectionManager manager) {
		List<Triple> triples = new ArrayList<Triple>();
		String section = zSect.getName();
		
		try {
			SectTypeEnvAnn steAnn = (SectTypeEnvAnn) manager.get(
					new Key(section, SectTypeEnvAnn.class));
			ListTerm nstTriples = steAnn.getNameSectTypeTriple();
			for (int i = 0; i < nstTriples.size(); i++) {
				NameSectTypeTriple triple = (NameSectTypeTriple) nstTriples.get(i);
				DeclName name = triple.getZDeclName();
				String type = triple.getType().accept(getNodeNameVisitor_);
				triples.add(new Triple(name, section, type));
			}
		} catch (CommandException e) {
			System.out.println("CommandException");
		}
		
		triples.addAll((visitChildrenOfTerm(zSect, section)));

		return triples;
	}
	
	private static List<Triple> visitTerm(Term term, String section) {
		List<Triple> triples = new ArrayList<Triple>();
		if (term != null) {
			if (term instanceof VarDecl) {
				String type = ((VarDecl)term).getExpr().accept(getNodeNameVisitor_);
				for (DeclName name : ((VarDecl)term).getDeclName()) {
					triples.add(new Triple(name, section, type));
				}
			}
			triples.addAll(visitChildrenOfTerm(term, section));
		}
		
		return triples;
	}
	
	private static List<Triple> visitChildrenOfTerm(Term term, String section) {
		List<Triple> triples = new ArrayList<Triple>();
		for (Object child : term.getChildren()) {
			if (child != null)
				if (child instanceof Term)
					triples.addAll(visitTerm((Term)child, section));
		}
		
		return triples;
	}
}

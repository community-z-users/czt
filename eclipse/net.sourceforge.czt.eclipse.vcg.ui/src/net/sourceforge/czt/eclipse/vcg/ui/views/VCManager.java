package net.sourceforge.czt.eclipse.vcg.ui.views;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.AbstractMap.SimpleEntry;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.Position;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.eclipse.core.compile.IZCompileData;
import net.sourceforge.czt.eclipse.ui.CztUI;
import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.vcg.ui.VcgUIPlugin;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.vcg.util.VCNameFactory;
import net.sourceforge.czt.vcg.z.VCG;
import net.sourceforge.czt.vcg.z.PredVC;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCConfig.Precedence;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.vcg.z.VCSource;
import net.sourceforge.czt.vcg.z.feasibility.FSBVCNameFactory;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.zeves.ast.LabelAbility;
import net.sourceforge.czt.zeves.ast.LabelUsage;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;
import net.sourceforge.czt.zeves.util.ZEvesUtils;

public class VCManager<T, B> {

	private final IZEditor editor;
	private final VCG<T, B> vcg;
	private final IZCompileData parsedData;
	private final ZSect specSect;
	
	private final VcgAnnotations markers;
	
	private VCEnvAnn vcAnn = null;
	private ZSect vcSect = null;
	
	private Map<String, Para> specParas = null;
	
	private final List<Entry<ZSchText, Pred>> originalPreds = new ArrayList<Entry<ZSchText, Pred>>();
	private final List<Entry<ZName, String>> originalIds = new ArrayList<Entry<ZName, String>>();
	private final Set<String> ignoreSources = new HashSet<String>();
	private final Set<String> ignoreSchemas = new HashSet<String>();
	
	public VCManager(IZEditor editor, VCG<T, B> vcg, IZCompileData parsedData, ZSect specSect) {
		super();
		this.editor = editor;
		this.vcg = vcg;
		this.parsedData = parsedData;
		this.specSect = specSect;
		
		this.markers = new VcgAnnotations(
				ZEditorUtil.getEditorResource(editor),
				ZEditorUtil.getDocument(editor));
	}
	
	public List<VCEntry> generateVCs() throws CommandException {
		
		// clear before executing, in case the method is executed twice
		clear();
		
		vcAnn = vcg.createVCEnvAnn(specSect);
		
		vcSect = vcg.getManager().get(new Key<ZSect>(
						vcAnn.getVCSectName(),
						ZSect.class));

		/*
		 * First go through generated schemas and merge the predicates. this is
		 * needed because user may configure some of the signature predicates
		 */
		VCNameFactory nameFactory = vcg.getVCCollector().getVCNameFactory();
		FSBVCNameFactory fsbNameFactory = nameFactory instanceof FSBVCNameFactory ? 
				(FSBVCNameFactory) nameFactory : null;
		
		for (Para vcPara : vcSect.getZParaList()) {
			if (vcPara instanceof AxPara) {
				mergeVCSchemaWithSpec((AxPara) vcPara);
				populateIgnoreSets(vcPara, fsbNameFactory);
			}
		}
		
		List<VCEntry> vcs = new ArrayList<VCEntry>();
		
		try {
			
			/*
			 * Now go through all generated paragraphs and check whether they have a
			 * corresponding one in the specification
			 */
			for (Para vcPara : vcSect.getZParaList()) {
	
				VCEntry vcEntry = processVCPara(vcPara);
				if (vcEntry != null) {
					vcs.add(vcEntry);
				}
			}
		
		} finally {
			// restore data
			restoreOriginalPreds();
			restoreOriginalIds();
			
			// flush markers
			markers.flushPendingMarkers();
		}
		
		return vcs;
	}

	private void clear() {
		specParas = null;
		originalPreds.clear();
		originalIds.clear();
		ignoreSources.clear();
		ignoreSchemas.clear();
		vcAnn = null;
		vcSect = null;
		
		try {
			markers.clearMarkers();
		} catch (CoreException e) {
			VcgUIPlugin.getDefault().log(e);
		}
	}

	private void populateIgnoreSets(Para vcPara, FSBVCNameFactory nameFactory) {
		String vcSchName = getVCParaName(vcPara);
		
		// ignore conjectures arising from VC sources
		ignoreSources.add(vcSchName);
		// ignore other VC schemas that are based on VC sources
		ignoreSchemas.add(nameFactory.getSigSchemaName(vcSchName));
	}
	
	private void mergeVCSchemaWithSpec(AxPara vcSchema) throws VCGException {
		String schName = getVCParaName(vcSchema);
		if (schName == null) {
			return;
		}
		
		// get a schema with the same name in specification
		Para specSchema = getSpecPara(schName);
		if (specSchema == null) {
			// not in specification, no merge
			return;
		}
		
		ZSchText specSchText = getSchemaText(specSchema);
		if (specSchText == null) {
			// invalid schema?
			return;
		}
		
		// replace VC schema predicate with the one from specification
		ZSchText vcSchText = getSchemaText(vcSchema);
		
		// mark the original predicate to restore afterwards
		originalPreds.add(new SimpleEntry<ZSchText, Pred>(vcSchText, vcSchText.getPred()));
		
		vcSchText.setPred(specSchText.getPred());
	}

	public static ZSchText getSchemaText(Term term) {
		Expr schExpr = ZUtils.getSchemaDefExpr(term);
		if (schExpr instanceof SchExpr) {
			return ((SchExpr) schExpr).getZSchText();
		}
		
		return null;
	}
	
	private VCEntry processVCPara(Para vcPara) throws VCGException {
		
		if (vcPara instanceof NarrPara) {
			return null;
		}
		
		boolean alreadyInSpec = false;
		
		if (vcPara instanceof ConjPara) {
			// fix name to use ZEves labels
			fixConjVCName(vcPara);
		}
		
		// get para name of the VC para
		String name = getVCParaName(vcPara);
		// check whether this paragraph is ignore (e.g. it is a VC of a VC)
		if (ignoreSchemas.contains(name)) {
			// ignore this VC para
			return null;
		}
		
		// also check whether VC's source paragraph is ignored, then VC is also ignored
		Para sourcePara = getSourcePara(vcPara);
		if (sourcePara != null && ignoreSources.contains(getVCParaName(sourcePara))) {
			// ignore this VC para
			return null;
		}
		
		// check whether such para already exists in the specification
		Para specPara = getSpecPara(name);
		if (specPara != null) {
			/*
			 * Specification has a paragraph with the same name, so we need to
			 * check whether that is the same paragraph. We check for AST
			 * equality, and if both are equal, we consider the VC to already be
			 * in the specification. Otherwise, flag as error - an invalid VC is
			 * in the specification.
			 * 
			 * We need to strip IDs before comparing, otherwise they will always
			 * be different.
			 */
			// TODO check maybe move this up to be done on the whole of section once? 
			stripNameIds(vcPara);
			stripNameIds(specPara);
			if (termsEquiv(vcPara, specPara)) {
				// mark as already in spec
				alreadyInSpec = true;
				
				// check precedence
				checkPrecedence(vcPara, specPara);
			} else {
				try {
					markers.createErrorMarker(
							getPosition(specPara),
							"The paragraph differs from the one generated by Verification Condition Generator. " +
							"Replace with generated.");
				} catch (CoreException e) {
					VcgUIPlugin.getDefault().log(e);
				}
			}
		}
		
		return new VCEntry(editor, vcg.getManager(), vcSect, vcPara, sourcePara, alreadyInSpec);
	}
	
	private Position getPosition(Term term) {
		return parsedData.getTermPosition(term);
	}
	
	private void checkPrecedence(Para vcPara, Para specPara) {
		
		Precedence prec = getPrecedence(vcPara);
		if (prec == null) {
			// precedence not indicated
			return;
		}
		
		Para sourcePara = getSourcePara(vcPara);
		if (sourcePara == null) {
			// no source paragraph - cannot check precedence
			return;
		}
		
		Position sourcePos = getPosition(sourcePara);
		Position actualPos = getPosition(specPara);

		if (prec == Precedence.AFTER) {
			if (actualPos.getOffset() < sourcePos.getOffset() + sourcePos.getLength()) {
				// the actual position is before the end of source paragraph,
				// thus the position is BEFORE - invalid
				try {
					markers.createErrorMarker(
							actualPos,
							"The paragraph must be located after " + getLabel(sourcePara));
				} catch (CoreException e) {
					VcgUIPlugin.getDefault().log(e);
				}
			}
		} else {
			if (actualPos.getOffset() + actualPos.getLength() > sourcePos.getOffset()) {
				// the actual position is after the beginning of source paragraph,
				// thus the position is AFTER - invalid
				try {
					markers.createErrorMarker(
							actualPos,
							"The paragraph must be located before " + getLabel(sourcePara));
				} catch (CoreException e) {
					VcgUIPlugin.getDefault().log(e);
				}
			}
		}
	}
	
	private Precedence getPrecedence(Para vcPara) {
		VCSource sourceInfo = vcPara.getAnn(VCSource.class);
		if (sourceInfo != null) {
			
			VC<?> vc = sourceInfo.getSourceVC();
			if (vc instanceof PredVC) {
				return ((PredVC) vc).getPrecedence();
			}
		}
		
		return null;
	}
	
	private String getLabel(Term term) {
		return CztUI.getTermLabel(term);
	}

	private void fixConjVCName(Para vcPara) {
		ZName nameAnn = vcPara.getAnn(ZName.class);
		if (nameAnn != null) {
			ZEvesLabel label = ZEvesUtils.FACTORY.createZEvesLabel(nameAnn,
					LabelAbility.none, LabelUsage.none);
			vcPara.getAnns().add(label);
		}
	}
	
	private Para getSourcePara(Para vcPara) {
		
		VCSource sourceInfo = vcPara.getAnn(VCSource.class);
		if (sourceInfo != null) {
			return sourceInfo.getSourcePara();
		}
		
		// unknown
		return null;
	}
	
	private Para getSpecPara(String name) throws VCGException {
		if (specParas == null) {
			specParas = getVCParas(specSect);
		}
		
		return specParas.get(name);
	}
	
	// TODO check VC paras in other sections?
	private Map<String, Para> getVCParas(ZSect sect) throws VCGException {
		
		Map<String, Para> paras = new HashMap<String, Para>();
		
		for (Para para : sect.getZParaList()) {
			
			String name = getVCParaName(para);
			if (name != null) {
				if (paras.containsKey(name)) {
					throw new VCGException(this.vcg.getManager().getDialect(), "Duplicate paragraph name in specification: " + name);
				}
				
				paras.put(name, para);
			}
		}
		
		return paras;
	}
	
	private ZName getVCParaZName(Para para) {
		if (para instanceof ConjPara) {
			ZEvesLabel label = ZEvesUtils.getLabel(para);
			if (label != null) {
				return label.getZName();
			}
			
			// otherwise Z-style conjectures, check name annotation
			return para.getAnn(ZName.class);
			
		} else if (para instanceof AxPara) {
			Name name = ZUtils.getSchemaName(para);
			if (name != null) {
				return ZUtils.assertZName(name);
			}
		}
		
		return null;
	}
	
	private String getVCParaName(Para para) {
		ZName paraName = getVCParaZName(para);
		if (paraName != null) {
			// TODO stroke list?
			return paraName.getWord();
		}
		
		return null;
	}
	
	private boolean termsEquiv(Term term1, Term term2) {
		return term1.equals(term2);
//		return termsPrintEquiv(term1, term2);
	}
	
//	/**
//	 * Checks whether the terms are print-equivalent. This can be used to check
//	 * when terms are parsed into different but equivalent ASTs.
//	 * 
//	 * @param term1
//	 * @param term2
//	 * @return
//	 */
//	private boolean termsPrintEquiv(Term term1, Term term2) {
//		StringWriter out1 = new StringWriter();
//		StringWriter out2 = new StringWriter();
//		PrintUtils.print(term1, out1, parsedData.getSectionManager(), specSect.getName(), Markup.UNICODE);
//		PrintUtils.print(term2, out2, parsedData.getSectionManager(), specSect.getName(), Markup.UNICODE);
//		
//		return out1.toString().equals(out2.toString());
//	}
	
	private void restoreOriginalPreds() {
		for (Entry<ZSchText, Pred> predEntry : originalPreds) {
			ZSchText sch = predEntry.getKey();
			Pred pred = predEntry.getValue();
			sch.setPred(pred);
		}
	}
	
	private void restoreOriginalIds() {
		for (Entry<ZName, String> idEntry : originalIds) {
			ZName name = idEntry.getKey();
			String id = idEntry.getValue();
			name.setId(id);
		}
	}
	
	private void stripNameIds(Term term) {
		term.accept(new StripNameIdVisitor());
	}
	
	private class StripNameIdVisitor implements TermVisitor<Object>, ZNameVisitor<Object> {

		@Override
		public Object visitZName(ZName term) {
			String id = term.getId();
			if (id != null) {
				// store original id to restore afterwards
				originalIds.add(new SimpleEntry<ZName, String>(term, id));
			}
			// strip current name id
			term.setId(null);
			return null;
		}

		@Override
		public Object visitTerm(Term term) {
			VisitorUtils.visitTerm(this, term);
			return null;
		}
	}
	
}

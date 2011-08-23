package net.sourceforge.czt.eclipse.vcg.views;

import org.eclipse.core.runtime.PlatformObject;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.outline.TermLabelVisitorFactory;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZSect;

public class VCEntry extends PlatformObject {
	
	private final ZEditor editor;
	private final SectionManager sectInfo;
	private final ZSect section;
	
	private final Para vcPara;
	private final Para sourcePara;
	private final boolean alreadyInSpec;
	
	public VCEntry(ZEditor editor, SectionManager sectInfo, ZSect section, Para vcPara,
			Para sourcePara, boolean alreadyInSpec) {
		super();
		this.editor = editor;
		this.sectInfo = sectInfo;
		this.section = section;
		this.vcPara = vcPara;
		this.sourcePara = sourcePara;
		this.alreadyInSpec = alreadyInSpec;
	}
	
	public Para getVCPara() {
		return vcPara;
	}

	public String getVCName() {
		return getName(vcPara);
	}

	public String getSourceParagraph() {
		return getName(sourcePara);
	}
	
	private String getName(Para para) {
		if (para == null) {
			return "";
		}
		
		return para.accept(TermLabelVisitorFactory.getTermLabelVisitor(true));
	}
	
	public boolean isInSpecification() {
		return alreadyInSpec;
	}
	
	public ZEditor getEditor() {
		return editor;
	}
	
	public String getSectionName() {
		return section != null ? section.getName() : null;
	}
	
	public SectionManager getSectionManager() {
		return sectInfo;
	}
}
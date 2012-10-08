package net.sourceforge.czt.eclipse.vcg.ui.views;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.PlatformObject;

import net.sourceforge.czt.eclipse.ui.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.outline.TermLabelVisitorFactory;
import net.sourceforge.czt.eclipse.ui.views.IZInfoObject;
import net.sourceforge.czt.eclipse.vcg.ui.VcgPlugin;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
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
	
	private IZInfoObject info;
	
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

	@Override
	public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
		
		if (adapter == IZInfoObject.class) {
			if (info == null) {
				info = new VCEntryInfo();
			}
			
			return info;
		}
		
		return super.getAdapter(adapter);
	}
	
	private class VCEntryInfo implements IZInfoObject {
		
		private String contents = null;
		
		@Override
		public Markup getMarkup() {
			return editor.getMarkup();
		}

		@Override
		public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException {
			
			if (contents != null) {
				return contents;
			}

			try {
				contents = ZEditorUtil.print(vcPara, sectInfo, getSectionName(), markup, 80, true);
			} catch (CommandException e) {
				throw new CoreException(VcgPlugin.newErrorStatus(e.getMessage(), e));
			}
			return contents;
		}

		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException {
			return "VC: " + getVCName();
		}
		
	}
	
}
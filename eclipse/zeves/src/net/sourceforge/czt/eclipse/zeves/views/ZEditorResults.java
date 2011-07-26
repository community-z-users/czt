package net.sourceforge.czt.eclipse.zeves.views;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.zeves.ZEvesFileState;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.editor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesPosVisitor;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.response.ZEvesOutput;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;

public class ZEditorResults {

	private static ZEvesFileState getSnapshot(ZEditor editor) {
		
		IResource resource = ZEditorUtil.getEditorResource(editor);
		
		if (resource == null) {
			return null;
		}
		
		return ZEvesPlugin.getZEves().getState(resource, false);
	}
	
	public static IZEvesElement getZEvesResult(ZEditor editor, ITextSelection selection, int caretPos) {
		
		final ZEvesFileState snapshot = getSnapshot(editor);
		if (snapshot == null) {
			return null;
		}
		
		final IZEvesElement[] data = new IZEvesElement[1];
		
		ZEvesPosVisitor commandVisitor = new ZEvesPosVisitor(caretPos, caretPos) {

			@Override
			protected void visitPara(Para term, Position position) {
				
				Object result = snapshot.getParaResult(term);
				
				if (result == null) {
					return;
				}
				
				data[0] = new ParagraphElement(term, result);
			}

			@Override
			protected boolean visitProofScriptHead(ProofScript term, Position pos) {
				// for proof script head, show the goal - 1st step
				visitProofScriptStep(term, 1);
				return true;
			}

			@Override
			protected void visitProofCommand(ProofScript script, ProofCommand command, Position pos) {
				visitProofScriptStep(script, command.getProofStep().intValue());
			}
			
			private void visitProofScriptStep(ProofScript script, int step) {
				ZEvesOutput result = snapshot.getProofResult(script, step);
				
				if (result == null) {
					return;
				}
				
				// FIXME
				data[0] = new ParagraphElement(null, result);
			}
		};
		
		commandVisitor.execSpec(editor.getParsedData().getSpec());
		
		return data[0];
	}
	
	public static class ParagraphElement implements IZEvesElement {

		private final Para para;
		private final Object zEvesPara;
		
		public ParagraphElement(Para para, Object zEvesPara) {
			super();
			this.para = para;
			this.zEvesPara = zEvesPara;
		}
		
		public Para getParagraph() {
			return para;
		}

		@Override
		public String getDescription() {
			return "";
		}

		@Override
		public Object loadContents(ZEvesApi api) throws ZEvesException {
			return zEvesPara;
		}
		
	}
	
}

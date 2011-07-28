package net.sourceforge.czt.eclipse.zeves.views;

import java.io.IOException;
import java.util.List;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.outline.TermLabelVisitorFactory;
import net.sourceforge.czt.eclipse.zeves.ZEvesFileState;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.editor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesPosVisitor;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesResultConverter;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.response.ZEvesOutput;
import net.sourceforge.czt.zeves.response.ZEvesProverCmd;
import net.sourceforge.czt.zeves.response.form.ZEvesBlurb;
import net.sourceforge.czt.zeves.response.form.ZEvesName;

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
	
	public static IZEvesElement getZEvesResult(final ZEditor editor, ITextSelection selection,
			int caretPos) {
		
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
			protected void visitProofScriptHead(ProofScript term, Position pos) {
				// for proof script head, show the goal step
				visitProofScriptStep(term, ZEvesFileState.PROOF_GOAL_STEP);
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
				
				data[0] = new ProofResultElement(
						editor.getParsedData().getSectionManager().clone(), 
						editor.getMarkup(), getCurrentSect(), 
						script, step, result);
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
		public Object loadContents(ZEvesApi api, Markup markup) throws ZEvesException {
			return zEvesPara;
		}
		
	}
	
	public static class ProofResultElement implements IZEvesElement {
		
		private final SectionManager sectInfo;
		private final Markup originalMarkup;
		private final ZSect section;
		private final ProofScript script;
		private final int step;
		private final ZEvesOutput result;
		
		public ProofResultElement(SectionManager sectInfo, Markup markup, ZSect section, 
				ProofScript script,	int step, ZEvesOutput result) {
			this.sectInfo = sectInfo;
			this.originalMarkup = markup;
			this.section = section;
			this.script = script;
			this.step = step;
			this.result = result;
		}

		@Override
		public String getDescription() {
			
			if (step == ZEvesFileState.PROOF_GOAL_STEP) {
				return "Proof goal for: " + script.getZName().accept(TermLabelVisitorFactory.getTermLabelVisitor(true));
			}
			
			ProofCommand proofCommand = getProofCommand();
			
			String commandStr;
			if (proofCommand == null) {
				commandStr = "[Invalid proof command]";
			} else {
				commandStr = proofCommand.accept(TermLabelVisitorFactory.getTermLabelVisitor(true));
			}
			
			return "Proof results for: " + commandStr;
		}

		@Override
		public Object loadContents(ZEvesApi api, Markup markup) throws ZEvesException {

			if (markup == null) {
				markup = this.originalMarkup;
			}
			
			ZEvesProverCmd sentCommand = result.getCommand();
			ZEvesBlurb info = result.getInfo();
			List<?> results = result.getResults();
			
			StringBuilder out = new StringBuilder();
			
			if (sentCommand != null) {
				out.append("Command sent: " + sentCommand.toString());
				out.append("\n");
			}
			
			String sectName = section != null ? section.getName() : null;
			
			if (info != null) {
				
				StringBuilder infoOut = new StringBuilder();
				
				List<?> infoContent = info.getContent();
				String delim = "";
				for (Object i : infoContent) {
					// no text width - everything in single line for now
					infoOut.append(delim).append(
							convertBlurbElement(sectInfo, sectName, markup, -1, i));
					delim = " ";
				}
				
				out.append(infoOut);
				out.append("\n");
			}
			
			boolean first = true;
			for (Object res : results) {
				
				if (first) {
					first = false;
					out.append(convertResult(sectInfo, sectName, markup, 80, res));
				} else {
					// just output others in newlines
					out.append(res);
				}
				
				out.append("\n");
			}
			
			return out;
		}
		
		private String convertBlurbElement(SectionManager sectInfo, String sectName,
				Markup markup, int textWidth, Object elem) {

			if (elem instanceof String) {
				return (String) elem;
			}
			
			if (elem instanceof ZEvesName) {
				// do not convert - just get the ident
				return ((ZEvesName) elem).getIdent();
			}
			
			String str = elem.toString();
			
			try {
				return ZEvesResultConverter.convert(sectInfo, sectName, str, markup, textWidth);
			} catch (IOException e) {
				// ignore here?
			} catch (CommandException e) {
				// ignore here?
				e.printStackTrace();
			}
			
			// problems - return unparsed
			return str;
		}
		
		private String convertResult(SectionManager sectInfo, String sectName,
				Markup markup, int textWidth, Object result) {

			String str = result.toString();
			
			try {
				return ZEvesResultConverter.convertPred(sectInfo, sectName, str, markup, textWidth);
			} catch (IOException e) {
				ZEvesPlugin.getDefault().log(e);
				return withWarning("I/O problems parsing Z/Eves result: " + e.getMessage(), str);
			} catch (CommandException e) {
				// TODO log this exception as well?
				Throwable cause = e.getCause();
				if (cause == null) {
					cause = e;
				}
				return withWarning("Cannot parse Z/Eves result: " + cause.getMessage(), str);
			}
		}
		
		private String withWarning(String warning, String result) {
			return "***\n" + warning + "\n***\n" + result;
		}
		
		private ProofCommand getProofCommand() {
			
			int listStep = step - 1;
			
			List<ProofCommand> commands = this.script.getProofCommandList();
			if (listStep >= 0 && listStep < commands.size()) {
				return commands.get(listStep);
			}
			
			return null;
		}
		
	}
	
}

package net.sourceforge.czt.eclipse.zeves.views;

import java.io.IOException;
import java.util.List;

import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
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
		
		// support selection just after or just before the actual caret position,
		// however priority is given for exact match
		final IZEvesElement[] data = new IZEvesElement[3];
		final Position exactPos = new Position(caretPos, 0);
		int beforeOffset = caretPos == 0 ? 0 : caretPos - 1;
		final Position beforePos = new Position(beforeOffset, 0);
		final Position afterPos = new Position(caretPos + 1, 0);
		
		ParsedData parsedData = editor.getParsedData();
		ZEvesPosVisitor commandVisitor = new ZEvesPosVisitor(parsedData, beforeOffset, caretPos + 1) {

			@Override
			protected void visitPara(Para term, Position position) {
				
				Object result = snapshot.getParaResult(term);
				
				if (result == null) {
					return;
				}
				
				collect(position, new ParagraphElement(term, result));
			}

			@Override
			protected void visitProofScriptHead(ProofScript term, Position pos) {
				// for proof script head, show the goal step
				visitProofScriptStep(term, ZEvesFileState.PROOF_GOAL_STEP, pos);
			}

			@Override
			protected void visitProofCommand(ProofScript script, ProofCommand command, Position pos) {
				visitProofScriptStep(script, command.getProofStep().intValue(), pos);
			}
			
			private void visitProofScriptStep(ProofScript script, int step, Position pos) {
				Object result = snapshot.getProofResult(script, step);
				
				if (result == null) {
					return;
				}
				
				if (!(result instanceof ZEvesOutput)) {
					// just output currently whatever the result
					collect(pos, new ParagraphElement(null, result));
					return ;
				}
				
				Integer zEvesStepIndex = snapshot.getProofStepIndex(script, step);
				
				collect(pos, new ProofResultElement(editor, getCurrentSect(), 
						script, step, zEvesStepIndex, (ZEvesOutput) result, pos));
			}
			
			private void collect(Position pos, IZEvesElement result) {
				
				if (includePos(pos, exactPos)) {
					data[0] = result;
				} else if (includePos(pos, afterPos)) {
					data[1] = result;
				} else if (includePos(pos, beforePos)) {
					data[2] = result;
				} 
			}
			
			private boolean includePos(Position pos, Position range) {
				return includePos(pos, range.getOffset(), range.getLength());
			}
		};
		
		commandVisitor.execSpec(parsedData.getSpec());
		
		for (IZEvesElement result : data) {
			if (result != null) {
				return result;
			}
		}
		
		return null;
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
		
		private final ZEditor editor;
		private final ZSect section;
		private final ProofScript script;
		private final int step;
		private final Integer zEvesStepIndex;
		private final ZEvesOutput result;
		
		private final Position position;
		
		public ProofResultElement(ZEditor editor, ZSect section, ProofScript script, int step,
				Integer stepIndex, ZEvesOutput result, Position position) {
			this.editor = editor;
			this.section = section;
			this.script = script;
			this.step = step;
			this.zEvesStepIndex = stepIndex;
			this.result = result;
			this.position = position;
		}
		
		public ZEditor getEditor() {
			return editor;
		}
		
		public Position getPosition() {
			return position;
		}
		
		public String getSectionName() {
			return section != null ? section.getName() : null;
		}
		
		public boolean isGoal() {
			return step == ZEvesFileState.PROOF_GOAL_STEP;
		}
		
		public int getZEvesStepIndex() {
			return zEvesStepIndex;
		}
		
		public String getGoalName() {
			return script.getZName().accept(TermLabelVisitorFactory.getTermLabelVisitor(true));
		}

		@Override
		public String getDescription() {
			
			if (isGoal()) {
				return "Proof goal for: " + getGoalName();
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
				markup = editor.getMarkup();
			}
			
			ZEvesProverCmd sentCommand = result.getCommand();
			ZEvesBlurb info = result.getInfo();
			List<?> results = result.getResults();
			
//			StringBuilder out = new StringBuilder();
			
			String sentCmdStr = sentCommand != null ? sentCommand.toString() : null;
//			if (sentCommand != null) {
//				out.append("Command sent: " + sentCommand.toString());
//				out.append("\n");
//			}
			
			String sectName = getSectionName();
			SectionManager sectInfo = editor.getParsedData().getSectionManager().clone();
			
			String infoStr = null;
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
				
				infoStr = infoOut.toString();
//				out.append(infoOut);
//				out.append("\n");
			}
			
			StringBuilder out = new StringBuilder();
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
			
//			return out;
			return new ProofResultInfo(sentCmdStr, infoStr, out.toString());
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
		
		public interface IProofResultInfo {
			public String getCommand();
			public String getInfo();
			public String getResult();
		}
		
		private class ProofResultInfo implements IProofResultInfo {
			private final String command;
			private final String info;
			private final String result;
			
			public ProofResultInfo(String command, String info, String result) {
				super();
				this.command = command;
				this.info = info;
				this.result = result;
			}

			@Override
			public String getCommand() {
				return command;
			}

			@Override
			public String getInfo() {
				return info;
			}

			@Override
			public String getResult() {
				return result;
			}

			@Override
			public String toString() {
				
				StringBuilder out = new StringBuilder();
				if (command != null) {
					out.append("Command sent: " + command + "\n");
				}
				
				if (info != null) {
					out.append(info + "\n");
				}
				
				out.append(result);
				return out.toString();
			}
		}
		
	}
	
}

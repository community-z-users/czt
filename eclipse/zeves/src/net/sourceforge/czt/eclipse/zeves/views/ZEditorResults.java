package net.sourceforge.czt.eclipse.zeves.views;

import java.io.IOException;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.parser.IPositionProvider;
import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.editors.parser.TermPositionProvider;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.outline.TermLabelVisitorFactory;
import net.sourceforge.czt.eclipse.views.IZInfoObject;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.core.ResourceUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesExecVisitor;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesPosVisitor;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesResultConverter;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesSnapshot;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesSnapshot.ProofResult;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.response.ZEvesOutput;
import net.sourceforge.czt.zeves.response.ZEvesProverCmd;
import net.sourceforge.czt.zeves.response.form.ZEvesBlurb;
import net.sourceforge.czt.zeves.response.form.ZEvesName;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;


public class ZEditorResults {

	public static IZInfoObject getZEvesResult(final ZEditor editor, ITextSelection selection,
			int caretPos) {
		
		IResource resource = ZEditorUtil.getEditorResource(editor);
		if (resource == null) {
			return null;
		}
		
		IDocument document = ZEditorUtil.getDocument(editor);
		IPositionProvider<Term> posProvider = new TermPositionProvider(document);
		
		final String filePath = ResourceUtil.getPath(resource);
		final ZEvesSnapshot snapshot = ZEvesPlugin.getZEves().getSnapshot();
		
		// support selection just after or just before the actual caret position,
		// however priority is given for exact match
		final IZInfoObject[] data = new IZInfoObject[3];
		final Position exactPos = new Position(caretPos, 0);
		int beforeOffset = caretPos == 0 ? 0 : caretPos - 1;
		final Position beforePos = new Position(beforeOffset, 0);
		final Position afterPos = new Position(caretPos + 1, 0);
		
		ParsedData parsedData = editor.getParsedData();
		ZEvesPosVisitor commandVisitor = new ZEvesPosVisitor(posProvider, beforeOffset, caretPos + 1) {

			@Override
			protected void visitPara(Para term, Position position) {
				
				Object result = snapshot.getResult(filePath, getCurrentSectionName(), position);
				
				if (result == null) {
					return;
				}
				
				IZInfoObject resultInfo;
				if (result instanceof ZEvesException) {
					resultInfo = new ZEvesErrorObject(
							editor, getCurrentSect(), position, term, (ZEvesException) result);
				} else {
					resultInfo = new ZEvesParaObject(
							editor, getCurrentSect(), position, term, result);
				}
				
				collect(position, resultInfo);
			}

			@Override
			protected void visitProofScriptHead(ProofScript term, Position pos) {
				// for proof script head, show the goal step
				visitProofScriptStep(term, null, pos);
			}

			@Override
			protected void visitProofCommand(ProofScript script, ProofCommand command, Position pos) {
				visitProofScriptStep(script, command, pos);
			}
			
			private void visitProofScriptStep(ProofScript script, ProofCommand command, Position pos) {
				Object result = snapshot.getProofResult(filePath, getCurrentSectionName(), pos);
				
				if (result == null) {
					return;
				}
				
				IZInfoObject resultInfo;
				if (result instanceof ZEvesException) {
					resultInfo = new ZEvesErrorObject(
							editor, getCurrentSect(), pos, script, (ZEvesException) result);
				} else if (command == null && result instanceof ZEvesOutput) {
					
					// goal
					resultInfo = new ZEvesProofObject(
							editor, getCurrentSect(), pos, script, command, 
							ZEvesExecVisitor.GOAL_STEP_INDEX, (ZEvesOutput) result);
					
				} else if (result instanceof ProofResult) {
					
					ProofResult proofResult = (ProofResult) result;
					resultInfo = new ZEvesProofObject(
							editor, getCurrentSect(), pos, script, command, 
							proofResult.getStepIndex(), proofResult.getResult());
				} else {
					// just output currently whatever the result
					// TODO proof command?
					resultInfo = new ZEvesParaObject(
							editor, getCurrentSect(), pos, script, result);
				}
				
				collect(pos, resultInfo);
			}
			
			private void collect(Position pos, IZInfoObject result) {
				
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
		
		for (IZInfoObject result : data) {
			if (result != null) {
				return result;
			}
		}
		
		return null;
	}
	
	private static abstract class ZEditorObject<T extends Term> 
		extends PlatformObject implements IZInfoObject {
		
		private final ZEditor editor;
		private final ZSect section;
		private final Position position;
		private final T term;
		
		public ZEditorObject(ZEditor editor, ZSect section, Position position, T term) {
			super();
			this.editor = editor;
			this.section = section;
			this.position = position;
			this.term = term;
		}

		public ZEditor getEditor() {
			return editor;
		}

		public ZSect getSection() {
			return section;
		}
		
		public String getSectionName() {
			return section != null ? section.getName() : null;
		}

		public Position getPosition() {
			return position;
		}

		public T getTerm() {
			return term;
		}

		@Override
		public Markup getMarkup() {
			return editor.getMarkup();
		}
	}
	
	public static class ZEvesErrorObject extends ZEditorObject<Term> implements IZInfoObject {

		private final ZEvesException ex;
		
		public ZEvesErrorObject(ZEditor editor, ZSect section, Position position, Term term,
				ZEvesException ex) {
			super(editor, section, position, term);
			this.ex = ex;
		}
		
		@Override
		public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException {
			return ex.getMessage();
		}

		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException {
			return null;
		}
	}
	
	public static class ZEvesParaObject extends ZEditorObject<Para> implements IZInfoObject {

		private final Object zEvesPara;
		
		public ZEvesParaObject(ZEditor editor, ZSect section, Position position, Para term,
				Object zEvesPara) {
			super(editor, section, position, term);
			this.zEvesPara = zEvesPara;
		}
		
		@Override
		public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException {
			
			String unicodeStr = zEvesPara.toString();
			if (markup == Markup.UNICODE) {
				return unicodeStr;
			}
			
			// TODO fix the non-unicode output
			return unicodeStr;
//			SectionManager sectMan = getEditor().getParsedData().getSectionManager().clone();
//			return convertResult(sectMan, getSectionName(), markup, 80, unicodeStr);
		}

		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException {
			return null;
		}
	}
	
	public static class ZEvesProofObject extends ZEditorObject<ProofCommand> implements IZInfoObject {
		
		private final ProofScript script;
		private final Integer zEvesStepIndex;
		private final ZEvesOutput result;
		
		private IProofResultInfo loadedResult;
		
		public ZEvesProofObject(ZEditor editor, ZSect section, Position position, ProofScript script,
				ProofCommand command, Integer zEvesStepIndex, ZEvesOutput result) {
			
			super(editor, section, position, command);
			this.script = script;
			this.zEvesStepIndex = zEvesStepIndex;
			this.result = result;
		}

		public boolean isGoal() {
			return getTerm() == null;
		}
		
		public int getZEvesStepIndex() {
			return zEvesStepIndex;
		}
		
		public String getGoalName() {
			return script.getZName().accept(TermLabelVisitorFactory.getTermLabelVisitor(true));
		}

		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException {
			
			ProofCommand command = getTerm();
			if (command == null) {
				return "Proof goal for: " + getGoalName();
			}
			
			String commandStr = command.accept(TermLabelVisitorFactory.getTermLabelVisitor(true));
			return "Proof results for: " + commandStr;
		}
		
		@Override
		public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException {

			ZEvesProverCmd sentCommand = result.getCommand();
			ZEvesBlurb info = result.getInfo();
			List<?> results = result.getResults();
			
			String sentCmdStr = sentCommand != null ? sentCommand.toString() : null;
			
			String sectName = getSectionName();
			SectionManager sectInfo = getEditor().getParsedData().getSectionManager().clone();
			
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
			
			this.loadedResult = new ProofResultInfo(sentCmdStr, infoStr, out.toString());
			return this.loadedResult.toString();
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
		
		@Override
		public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
			
			if (adapter == IProofResultInfo.class) {
				return loadedResult;
			}
			
			return super.getAdapter(adapter);
		}
	}
	
	private static String convertResult(SectionManager sectInfo, String sectName,
			Markup markup, int textWidth, Object result) {

		String str = result.toString();
		
		try {
			return ZEvesResultConverter.convertPred(sectInfo, sectName, str, markup, textWidth);
		} catch (IOException e) {
			ZEvesPlugin.getDefault().log(e);
			return withWarning("I/O problems parsing Z/Eves result: " + e.getMessage(), str);
		} catch (CommandException e) {
			Throwable cause = e.getCause();
			if (cause == null) {
				cause = e;
			}
			ZEvesPlugin.getDefault().log(cause);
			return withWarning("Cannot parse Z/Eves result: " + cause.getMessage(), str);
		}
	}
	
	private static String withWarning(String warning, String result) {
		return "***\n" + warning + "\n***\n" + result;
	}
	
	public interface IProofResultInfo {
		public String getCommand();
		public String getInfo();
		public String getResult();
	}
	
	private static class ProofResultInfo implements IProofResultInfo {
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

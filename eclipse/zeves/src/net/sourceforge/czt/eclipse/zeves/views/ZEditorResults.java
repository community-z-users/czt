package net.sourceforge.czt.eclipse.zeves.views;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.outline.TermLabelVisitorFactory;
import net.sourceforge.czt.eclipse.views.IZInfoObject;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.core.ResourceUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesPosVisitor;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesResultConverter;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesSnapshot;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesSnapshot.IProofSnapshotEntry;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesSnapshot.ISnapshotEntry;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.response.ZEvesOutput;
import net.sourceforge.czt.zeves.response.ZEvesProofTrace;
import net.sourceforge.czt.zeves.response.ZEvesProverCmd;
import net.sourceforge.czt.zeves.response.ZEvesResponsePrinter;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.response.form.ZEvesNumber;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.jface.text.BadLocationException;
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
		
		final String filePath = ResourceUtil.getPath(resource);
		final ZEvesSnapshot snapshot = ZEvesPlugin.getZEves().getSnapshot();
		
		// calculate "target" positions for the indicated. We specify a decreasing priority
		// order of positions that could apply to locate results. Then the first result
		// that is available in the decreasing order is used as overall result 
		final List<Position> targetPositions = getTargetPositions(document, caretPos);
		
		Position first = targetPositions.get(0);
		int beforeOffset = first.getOffset();
		int afterOffset = first.getOffset() + first.getLength();
		
		for (Position pos : targetPositions) {
			if (pos != null) {
				beforeOffset = Math.min(beforeOffset, pos.getOffset());
				afterOffset = Math.max(afterOffset, pos.getOffset() + pos.getLength());
			}
		}
		
		final IZInfoObject[] data = new IZInfoObject[targetPositions.size()];
		
		// find all entries in the snapshot for the given position
		List<ISnapshotEntry> snapshotEntries = snapshot.getEntries(filePath, 
				new Position(beforeOffset, afterOffset - beforeOffset));
		
		for (ISnapshotEntry entry : snapshotEntries) {

			String sectionName = entry.getSectionName();
			Position pos = entry.getPosition();
			
			IZInfoObject resultInfo;
			if (entry instanceof IProofSnapshotEntry) {
				
				IProofSnapshotEntry proofEntry = (IProofSnapshotEntry) entry;
				
				// proof/goal entry
				resultInfo = new ZEvesProofObject(
						editor, sectionName, pos, 
						proofEntry.getGoalName(), proofEntry.getStepIndex(), 
						proofEntry.getSource(), proofEntry.getResult(), proofEntry.getTrace());
			} else {
				
				Object result = entry.getResult();
				Term source = entry.getSource();
				if (result instanceof ZEvesException) {
					// error
					resultInfo = new ZEvesErrorObject(
							editor, sectionName, pos, source, (ZEvesException) result);
					
				} else if (result != null) {
					resultInfo = new ZEvesParaObject(
							editor, sectionName, pos, (Para) source, result);
				} else {
					resultInfo = null;
				}
			}
			
			// collect into respective slots
			for (int index = 0; index < targetPositions.size(); index++) {
				Position targetPos = targetPositions.get(index);
				if (includePos(pos, targetPos)) {
					data[index] = resultInfo;
					break;
				}
			}
		}
		
		for (IZInfoObject result : data) {
			if (result != null) {
				return result;
			}
		}
		
		return null;
	}
	
	private static boolean includePos(Position pos, Position range) {
		if (range == null) {
			return false;
		}
		
		return ZEvesPosVisitor.includePos(pos, range.getOffset(), range.getLength());
	}

	private static List<Position> getTargetPositions(IDocument document, int caretPos) {
		// support selection just after or just before the actual caret position,
		// however priority is given for exact match
		// also support selection for the same line, or for the 
		// lines before and after (in lowering priority)
		Position exactPos = new Position(caretPos);
		Position beforePos = null;
		Position afterPos = null;
		Position linePos = null;
		Position preLinePos = null;
		Position postLinePos = null;
		
		try {		
		
			int line = document.getLineOfOffset(caretPos);
			
			if (caretPos > 0) {
				int beforeOffset = caretPos - 1;
				int beforeOffsetLine = document.getLineOfOffset(beforeOffset);
				if (line == beforeOffsetLine) {
					// before position only supported if in the same line, 
					// otherwise "line" position gets priority
					beforePos = new Position(beforeOffset);
				}
			}
			
			if (caretPos < document.getLength() - 1) {
				int afterOffset = caretPos + 1;
				int afterOffsetLine = document.getLineOfOffset(afterOffset);
				if (line == afterOffsetLine) {
					// before position only supported if in the same line, 
					// otherwise "line" position gets priority
					afterPos = new Position(afterOffset);
				}
			}
			
			int lineOffset = document.getLineOffset(line);
			int lineLength = document.getLineLength(line);
			linePos = new Position(lineOffset, lineLength);
			
			if (line > 0) {
				int preLine = line - 1;
				int preLineOffset = document.getLineOffset(preLine);
				int preLineLength = document.getLineLength(preLine);
				preLinePos = new Position(preLineOffset, preLineLength);
			}
			
			if (line < document.getNumberOfLines() - 1) {
				int postLine = line + 1;
				int postLineOffset = document.getLineOffset(postLine);
				int postLineLength = document.getLineLength(postLine);
				postLinePos = new Position(postLineOffset, postLineLength);
			}
		} catch (BadLocationException ex) {
			ZEvesPlugin.getDefault().log(ex);
		}
		
		// order the priority of positions
		final List<Position> targetPositions = 
				Arrays.asList(exactPos, beforePos, afterPos, linePos, preLinePos, postLinePos);
		return targetPositions;
	}
	
	public static abstract class ZEditorObject<T extends Term> 
		extends PlatformObject implements IZInfoObject {
		
		private final ZEditor editor;
		private final String sectionName;
		private final Position position;
		private final T source;
		
		public ZEditorObject(ZEditor editor, String sectionName, Position position, T source) {
			super();
			this.editor = editor;
			this.sectionName = sectionName;
			this.position = position;
			this.source = source;
		}

		public ZEditor getEditor() {
			return editor;
		}
		
		public String getSectionName() {
			return sectionName;
		}

		public Position getPosition() {
			return position;
		}
		
		public Term getSource() {
			return source;
		}

		@Override
		public Markup getMarkup() {
			return editor.getMarkup();
		}
	}
	
	public static class ZEvesErrorObject extends ZEditorObject<Term> implements IZInfoObject {

		private final ZEvesException ex;
		
		public ZEvesErrorObject(ZEditor editor, String sectionName, Position position,
				Term source, ZEvesException ex) {
			super(editor, sectionName, position, source);
			this.ex = ex;
		}
		
		@Override
		public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException {
			return ex.getMessage();
		}

		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException {
			Term source = getSource();
			if (source == null) {
				return null;
			}
			
			return "Z/Eves error for: "
					+ source.accept(TermLabelVisitorFactory.getTermLabelVisitor(true));
		}
	}
	
	public static class ZEvesParaObject extends ZEditorObject<Para> implements IZInfoObject {

		private final Object zEvesPara;
		
		public ZEvesParaObject(ZEditor editor, String sectionName, Position position,
				Para source, Object zEvesPara) {
			super(editor, sectionName, position, source);
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
			Term source = getSource();
			if (source == null) {
				return null;
			}
			
			return "Z/Eves paragraph result for: "
					+ source.accept(TermLabelVisitorFactory.getTermLabelVisitor(true));
		}
	}
	
	public static class ZEvesProofObject extends ZEditorObject<ProofCommand> implements IZInfoObject {
		
		private final String goalName;
		private final Integer zEvesStepIndex;
		private final ZEvesOutput result;
		private final List<ZEvesOutput> trace;
		
		private IProofResultInfo loadedResult;
		private List<IProofResultInfo> loadedTrace = new ArrayList<IProofResultInfo>();
		
		public ZEvesProofObject(ZEditor editor, String sectionName, Position position, 
				String goalName, Integer zEvesStepIndex, ProofCommand source, 
				ZEvesOutput result, List<ZEvesOutput> trace) {
			
			super(editor, sectionName, position, source);
			this.goalName = goalName;
			this.zEvesStepIndex = zEvesStepIndex;
			this.result = result;
			this.trace = new ArrayList<ZEvesOutput>(trace);
		}

		public boolean isGoal() {
			return zEvesStepIndex == ZEvesSnapshot.GOAL_STEP_INDEX;
		}
		
		public int getZEvesStepIndex() {
			return zEvesStepIndex;
		}
		
		public String getGoalName() {
			return goalName;
		}

		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException {
			
			if (isGoal()) {
				return "Proof goal for: " + getGoalName();
			}
			
			ProofCommand command = (ProofCommand) getSource();
			
			String caseId = getCaseId();
			String desc = caseId.isEmpty() ? "Proof results for: " : caseId + ", results for: ";
			
			String commandStr = command != null ? 
					command.accept(TermLabelVisitorFactory.getTermLabelVisitor(true)) : 
					"unknown";
					
			return desc + commandStr;
		}
		
		@Override
		public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException {

			this.loadedResult = convertResult(markup, result);
			
			this.loadedTrace.clear();
			for (ZEvesOutput traceOutput : trace) {
				
				IProofResultInfo loaded;
				if (traceOutput == result) {
					// already loaded - the result
					loaded = loadedResult;
				} else {
					loaded = convertResult(markup, traceOutput);
				}
				
				loadedTrace.add(loaded);
			}
			
			return loadedResult.toString();
		}
		
		private String getCaseId() {
			List<Integer> caseInfo = result.getProofCase();
			if (caseInfo.isEmpty()) {
				return "";
			}
			
			return "Proof case #" + ZEvesResponseUtil.concat(caseInfo, ".");
		}

		private IProofResultInfo convertResult(final Markup markup, ZEvesOutput result) {
			ZEvesProverCmd sentCommand = result.getCommand();
			List<?> results = result.getResults();
			
			ZEvesProofTrace trace = result.getProofTrace();
			
			final String sectName = getSectionName();
			final SectionManager sectInfo = getEditor().getParsedData().getSectionManager().clone();
			final int textWidth = 80;
			
			String sentCmdStr = null;
			if (sentCommand != null) {
				sentCmdStr = sentCommand.print(new ZEvesResponsePrinter() {
					@Override
					public String print(Object zEvesElem) {
						return convertBlurbElement(sectInfo, sectName, markup, textWidth, zEvesElem);
					}
				});
			}
			
			String infoStr = convertTrace(sectInfo, sectName, markup, textWidth, trace);
			String caseId = getCaseId();
			if (!caseId.isEmpty()) {
				infoStr = infoStr + "\n" + caseId;
			}
			
			StringBuilder out = new StringBuilder();
			boolean first = true;
			for (Object res : results) {
				
				if (first) {
					first = false;
					out.append(convertResultPred(sectInfo, sectName, markup, textWidth, res));
				} else if (res instanceof ZEvesNumber) {
					// case number - ignore, as it is printed in other ways
					continue;
				} else {
					// just output others in newlines
					out.append("\n");
					out.append(res);
				}
				
			}
			
			return new ProofResultInfo(sentCmdStr, infoStr, out.toString());
		}

		private String convertTrace(SectionManager sectInfo, String sectName,
				Markup markup, int textWidth, ZEvesProofTrace trace) {
			
			List<String> textElems = new ArrayList<String>();
			for (Entry<String, List<Object>> traceContent : trace.getTraceContents().entrySet()) {
				textElems.add(traceContent.getKey());
				
				for (Iterator<?> it = traceContent.getValue().iterator(); it.hasNext(); ) {
					Object i = it.next();
					// add commas for non-last elements per trace type
					String comma = it.hasNext() ? "," : "";
					textElems.add(convertBlurbElement(sectInfo, sectName, markup, -1, i).trim() + comma);
				}
			}
			
			StringBuilder infoOut = new StringBuilder();
			
			String delim = "";
			for (String str : textElems) {
				
				int lastLineStart = infoOut.lastIndexOf("\n");
				if (lastLineStart < 0) {
					lastLineStart = 0;
				}
				
				String sep = delim;
				if (textWidth > 0 && 
						infoOut.length() + str.length() + 1 - lastLineStart > textWidth) {
					// the text will go outside of the line
					// so move it to new line (if not the first string added)
					if (infoOut.length() > 0) {
						sep = "\n";
					}
				}
				
				infoOut.append(sep).append(str);
				
				delim = " ";
			}
			
			return infoOut.toString();
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
				return ZEvesResultConverter.convert(sectInfo, sectName, str, markup, textWidth, true);
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
			
			if (adapter == IProofTrace.class) {
				return new ProofTrace(loadedTrace);
			}
			
			return super.getAdapter(adapter);
		}
	}
	
	private static String convertResultPred(SectionManager sectInfo, String sectName,
			Markup markup, int textWidth, Object result) {

		String str = result.toString();
		
		try {
			return ZEvesResultConverter.convertPred(sectInfo, sectName, str, markup, textWidth, true);
		} catch (IOException e) {
			ZEvesPlugin.getDefault().log(e);
			return withWarning("I/O problems parsing Z/Eves result: " + e.getMessage(), str);
		} catch (CommandException e) {
			Throwable cause = e.getCause();
			if (cause == null) {
				cause = e;
			}
			ZEvesPlugin.getDefault().log("Cannot parse Z/Eves result: " + cause.getMessage().trim(), cause);
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
				out.append("Command sent: " + command + "\n\n");
			}
			
			if (info != null) {
				out.append(info + "\n\n");
			}
			
			out.append(result);
			return out.toString();
		}
	}
	
	public interface IProofTrace {
		public List<IProofResultInfo> getTrace();
	}
	
	private static class ProofTrace implements IProofTrace {
		
		private List<IProofResultInfo> trace;

		public ProofTrace(List<IProofResultInfo> trace) {
			this.trace = new ArrayList<IProofResultInfo>(trace);
		}

		@Override
		public List<IProofResultInfo> getTrace() {
			return Collections.unmodifiableList(trace);
		}
		
	}
	
}

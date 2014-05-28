package net.sourceforge.czt.eclipse.zeves.ui.views;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.core.compile.IZCompileData;
import net.sourceforge.czt.eclipse.core.document.DocumentUtil;
import net.sourceforge.czt.eclipse.ui.CztUI;
import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.views.IZInfoObject;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesPosVisitor;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesResultConverter;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ResourceUtil;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.response.ZEvesError;
import net.sourceforge.czt.zeves.response.ZEvesErrorMessage;
import net.sourceforge.czt.zeves.response.ZEvesOutput;
import net.sourceforge.czt.zeves.response.ZEvesProofTrace;
import net.sourceforge.czt.zeves.response.ZEvesProverCmd;
import net.sourceforge.czt.zeves.response.ZEvesResponsePrinter;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.zeves.response.ZEvesProofTrace.TraceType;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.response.form.ZEvesNumber;
import net.sourceforge.czt.zeves.snapshot.ISnapshotEntry;
import net.sourceforge.czt.zeves.snapshot.SnapshotUtil;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot.ResultType;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

import static net.sourceforge.czt.eclipse.ui.util.TextUtil.*;

public class ZEditorResults {

	private static int TEXT_WIDTH = 160;
	
	public static ISnapshotEntry getSnapshotEntryApprox(String filePath, IDocument document,
			int offset, Set<ResultType> allowedTypes) {
		
		ZEvesSnapshot snapshot = ZEvesCore.getSnapshot();
		
		// calculate "target" positions for the indicated. We specify a decreasing priority
		// order of positions that could apply to locate results. Then the first result
		// that is available in the decreasing order is used as overall result 
		List<Position> targetPositions = getTargetPositions(document, offset);
		
		Position first = targetPositions.get(0);
		int beforeOffset = first.getOffset();
		int afterOffset = first.getOffset() + first.getLength();
		
		for (Position pos : targetPositions) {
			if (pos != null) {
				beforeOffset = Math.min(beforeOffset, pos.getOffset());
				afterOffset = Math.max(afterOffset, pos.getOffset() + pos.getLength());
			}
		}
		
		final ISnapshotEntry[] data = new ISnapshotEntry[targetPositions.size()];
		
		// find all entries in the snapshot for the given position
		List<ISnapshotEntry> snapshotEntries = snapshot.getEntries(filePath, 
				net.sourceforge.czt.text.Position.createStartEnd(beforeOffset, afterOffset));
		
		for (ISnapshotEntry entry : snapshotEntries) {
			
			Position pos = jfacePos(entry.getPosition());
			
			if (!allowedTypes.contains(entry.getType())) {
				continue;
			}
			
			// collect into respective slots
			for (int index = 0; index < targetPositions.size(); index++) {
				Position targetPos = targetPositions.get(index);
				if (includePos(pos, targetPos)) {
					data[index] = entry;
					break;
				}
			}
		}
		
		for (ISnapshotEntry result : data) {
			if (result != null) {
				return result;
			}
		}
		
		return null;
	}
	
	public static IZInfoObject getZEvesResult(final IZEditor editor, int caretPos) {
		
		IResource resource = ZEditorUtil.getEditorResource(editor);
		if (resource == null) {
			return null;
		}
		
		IDocument document = ZEditorUtil.getDocument(editor);
		
		final String filePath = ResourceUtil.getPath(resource);
		
		ISnapshotEntry entry = getSnapshotEntryApprox(filePath, document, caretPos, 
				EnumSet.of(ResultType.GOAL, ResultType.PROOF, ResultType.ERROR, ResultType.PARA));
		
		if (entry == null) {
			return null;
		}
		
		return getInfoObject(editor, entry);
	}
	
	private static IZInfoObject getInfoObject(IZEditor editor, ISnapshotEntry entry) {
		switch (entry.getType()) {
		case GOAL:
		case PROOF: return new ZEvesProofObject(editor, entry);
		case ERROR: return new ZEvesErrorObject(editor, entry);
		case PARA: return new ZEvesParaObject(editor, entry);
		default: return null;
		}
	}
	
	private static boolean includePos(Position pos, Position range) {
		if (range == null) {
			return false;
		}
		
		return ZEvesPosVisitor.includePos(cztPos(pos), range.getOffset(), range.getLength());
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
			ZEvesUIPlugin.getDefault().log(ex);
		}
		
		// order the priority of positions
		final List<Position> targetPositions = 
				Arrays.asList(exactPos, beforePos, afterPos, linePos, preLinePos, postLinePos);
		return targetPositions;
	}
	
	private static abstract class ZEditorObject<T extends Term> 
		extends PlatformObject implements IZInfoObject, IZEditorObject {
		
		private final IZEditor editor;
		private final ISnapshotEntry snapshotEntry;
		
		public ZEditorObject(IZEditor editor, ISnapshotEntry snapshotEntry) {
			super();
			this.editor = editor;
			this.snapshotEntry = snapshotEntry;
		}

		@Override
		public IZEditor getEditor() {
			return editor;
		}
		
		public String getSectionName() {
			return snapshotEntry.getSectionName();
		}

		@Override
		public Position getPosition() {
			return jfacePos(snapshotEntry.getPosition());
		}
		
		public Term getSource() {
			return snapshotEntry.getData().getTerm();
		}

		@Override
		public Markup getMarkup() {
			return editor.getMarkup();
		}
		
		protected ISnapshotEntry getSnapshotEntry() {
			return snapshotEntry;
		}

		@Override
		public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
			if (adapter == ISnapshotEntry.class) {
				return getSnapshotEntry();
			}
			
			return super.getAdapter(adapter);
		}
		
	}
	
	private static class ZEvesErrorObject extends ZEditorObject<Term> 
		implements IZEvesInfoProvider {

		public ZEvesErrorObject(IZEditor editor, ISnapshotEntry snapshotEntry) {
			super(editor, snapshotEntry);
		}
		
		@Override
		public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException {
			return loadContents(markup, true, monitor).getDocument().get();
		}

		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException {
			Term source = getSource();
			if (source == null) {
				return null;
			}
			
			String caseText = null;

			// add case information if within the proof
			if (source instanceof ProofCommand) {
				// check if it was a Z/EVES error - then add the previous goal case ID
				ZEvesException error = (ZEvesException) getSnapshotEntry().getData().getResult();
				if (error.getZEvesError() != null) {
					ISnapshotEntry proofEntry = getPreviousProofEntry();
					if (proofEntry != null) {
						caseText = getCaseText(proofEntry);
					}
				}
			}
			
			String descStart = caseText != null ? caseText + ", " : "";
			
			return descStart + "Z/EVES error for: " + CztUI.getTermLabel(source);
		}

		@Override
		public IZInfoConfiguration loadContents(Markup markup, boolean showTrace,
				IProgressMonitor monitor) throws CoreException {
			
			List<PartitionString> output = new ArrayList<PartitionString>();
			
			ZEvesException error = (ZEvesException) getSnapshotEntry().getData().getResult();
			output.addAll(convertError(error));

			// check if it was a Z/EVES error - then add the previous goal state
			if (error.getZEvesError() != null) {
				output(output, "\n");
				
				ISnapshotEntry proofEntry = getPreviousProofEntry();
				if (proofEntry != null) {
					IZCompileData parsedData = getEditor().getParsedData();
					output.addAll(convertProofResult(
							parsedData.getSectionManager(), 
							getSectionName(), markup, proofEntry, TEXT_WIDTH, showTrace));
				}
			}
			
			Map<Annotation, Position> annotations = new HashMap<Annotation, Position>();
			IDocument document = createDocument(markup, output, annotations);
			return new ZInfoConfiguration(null, document, annotations);
		}
		
		private List<PartitionString> convertError(ZEvesException ex) {
			
			List<String> messages = new ArrayList<String>();
			
			ZEvesError error = ex.getZEvesError();
			if (error != null) {
				for (ZEvesErrorMessage msg : error.getMessages()) {
					messages.add(msg.getMessage());
				}
			} else {
				messages.add(ex.getMessage());
			}
			
			List<PartitionString> output = new ArrayList<PartitionString>();
			
			for (String msg : messages) {
				outputE(output, msg);
				output(output, "\n");
			}
			
			return output;
		}
		
		private ISnapshotEntry getPreviousProofEntry() {
			return SnapshotUtil.getPreviousProofEntry(getSnapshotEntry(), false);
		}

		@Override
		public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
			
			if (adapter == IProofObject.class) {
				ISnapshotEntry proofEntry = getPreviousProofEntry();
				
				if (proofEntry != null) {
					return new ZEvesProofObject(getEditor(), proofEntry) {

						@Override
						public Position getPosition() {
							// override position to use the error's
							return ZEvesErrorObject.this.getPosition();
						}
					};
				}
			}
			
			return super.getAdapter(adapter);
		}
	}
	
	private static class ZEvesParaObject extends ZEditorObject<Para> implements IZEvesInfoProvider {

		public ZEvesParaObject(IZEditor editor, ISnapshotEntry snapshotEntry) {
			super(editor, snapshotEntry);
		}
		
		@Override
		public IZInfoConfiguration loadContents(Markup markup, boolean showTrace,
				IProgressMonitor monitor) throws CoreException {
			
			List<PartitionString> output = new ArrayList<PartitionString>();
			
			Object result = getSnapshotEntry().getData().getResult();
			IZCompileData parsedData = getEditor().getParsedData();
			output.addAll(convertOutputResult(parsedData.getSectionManager(),
					getSectionName(), markup, TEXT_WIDTH, result, false));
			
			Map<Annotation, Position> annotations = new HashMap<Annotation, Position>();
			IDocument document = createDocument(markup, output, annotations);
			return new ZInfoConfiguration(null, document, annotations);
		}
		
		@Override
		public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException {
			return loadContents(markup, true, monitor).getDocument().get();
		}

		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException {
			Term source = getSource();
			if (source == null) {
				return null;
			}
			
			return "Z/EVES paragraph result for: " + CztUI.getTermLabel(source);
		}
	}
	
	private static class ZEvesProofObject extends ZEditorObject<ProofCommand> 
		implements IZEvesInfoProvider, IProofObject {
		
		public ZEvesProofObject(IZEditor editor, ISnapshotEntry snapshotEntry) {
			super(editor, snapshotEntry);
		}

		public boolean isGoal() {
			return getZEvesStepIndex() == ZEvesSnapshot.GOAL_STEP_INDEX;
		}
		
		@Override
		public int getZEvesStepIndex() {
			return getSnapshotEntry().getData().getProofStepIndex();
		}
		
		@Override
		public String getGoalName() {
			return getSnapshotEntry().getData().getGoalName();
		}

		@Override
		public SectionManager getSectionManager() {
			IZCompileData parsedData = getEditor().getParsedData();
			return parsedData.getSectionManager();
		}

		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException {
			
			if (isGoal()) {
				return "Proof goal for: " + getGoalName();
			}
			
			ProofCommand command = (ProofCommand) getSource();
			
			String caseText = getCaseText(getSnapshotEntry());
			String desc = caseText == null ? "Proof results for: " : caseText + ", results for: ";
			
			String commandStr = command != null ? CztUI.getTermLabel(command) : "unknown";
			return desc + commandStr;
		}
		
		@Override
		public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException {
			return loadContents(markup, true, monitor).getDocument().get();
		}

		@Override
		public IZInfoConfiguration loadContents(Markup markup, boolean showTrace,
				IProgressMonitor monitor) throws CoreException {

			IZCompileData parsedData = getEditor().getParsedData();
			List<PartitionString> output = convertProofResult(
					parsedData.getSectionManager(),
					getSectionName(), 
					markup, getSnapshotEntry(), TEXT_WIDTH, showTrace);
			
			Map<Annotation, Position> annotations = new HashMap<Annotation, Position>();
			IDocument document = createDocument(markup, output, annotations);
			return new ZInfoConfiguration(null, document, annotations);
		}

	}
	
	private static String getCaseId(ZEvesOutput result) {
		List<Integer> caseInfo = result.getProofCase();
		if (caseInfo.isEmpty()) {
			return null;
		}
		
		return ZEvesResponseUtil.concat(caseInfo, ".");
	}
	
	private static String getCaseText(ISnapshotEntry entry) {
		
		String caseId = getCaseId((ZEvesOutput) entry.getData().getResult());
		
		if (caseId == null) {
			return null;
		}
		
		return "Proof case #" + caseId;
	}
	
	private static List<PartitionString> convertProofResult(SectionManager sectInfo,
			String sectName, Markup markup, ISnapshotEntry snapshotEntry,
			int textWidth, boolean showTrace) {
		
		List<ZEvesOutput> results = showTrace ?
				snapshotEntry.getData().getTrace() :
				Collections.singletonList((ZEvesOutput) snapshotEntry.getData().getResult());
				
		List<PartitionString> output = new ArrayList<PartitionString>();
		
		String resultDelim = "";
		for (ZEvesOutput result : results) {
			
			output(output, resultDelim);
			
			output.addAll(convertResult(sectInfo, sectName, textWidth, markup, showTrace, result));
			
			if (resultDelim.isEmpty()) {
				resultDelim = createProofResultDelimiter(markup == Markup.UNICODE ? 50 : 80);
			}
		}
		return output;
	}
	
	private static List<PartitionString> convertResult(final SectionManager sectInfo, 
			final String sectName, final int textWidth, 
			final Markup markup, boolean showTrace, ZEvesOutput result) {
		
		List<?> results = result.getResults();
		
		List<PartitionString> output = new ArrayList<PartitionString>();
		
		if (showTrace) {
			String commandStr = convertSentCommand(sectInfo, sectName, textWidth, markup, result);
			
			output(output, "Proof command: ");
			outputI(output, commandStr);
			output(output, "\n\n");
			
			List<PartitionString> traceOutput = convertTrace(sectInfo, sectName, markup, textWidth, result);
			if (!traceOutput.isEmpty()) {
				output.addAll(traceOutput);
				output(output, "\n\n");
			}
			
		}
		
		boolean first = true;
		for (Object res : results) {
			
			if (first) {
				first = false;
				output.addAll(convertOutputResult(sectInfo, sectName, markup, textWidth, res, true));
			} else if (res instanceof ZEvesNumber) {
				// case number - ignore, as it is printed in other ways
				continue;
			} else {
				// just output others in newlines
				output(output, "\n");
				output(output, String.valueOf(res));
			}
			
		}
		
		return output;
	}

	private static String convertSentCommand(final SectionManager sectInfo, final String sectName,
			final int textWidth, final Markup markup, ZEvesOutput result) {
		
		ZEvesProverCmd sentCommand = result.getCommand();
		if (sentCommand == null) {
			return "<unknown>";
		}
		
		return sentCommand.print(new ZEvesResponsePrinter() {
			@Override
			public String print(Object zEvesElem) {
				return convertBlurbElement(sectInfo, sectName, markup, textWidth, zEvesElem);
			}
		});
	}

	private static List<PartitionString> convertTrace(SectionManager sectInfo, String sectName,
			Markup markup, int textWidth, ZEvesOutput result) {
		
		ZEvesProofTrace trace = result.getProofTrace();
		
		List<PartitionString> output = new ArrayList<PartitionString>();
		
		boolean hasCase = false;
		
		String traceTypeDelim = "";
		for (TraceType traceType : TraceType.values()) {
			List<Object> traceElements = trace.getTraceElements(traceType);
			if (traceElements.isEmpty()) {
				continue;
			}
			
			if (traceType == TraceType.CASE) {
				hasCase = true;
			}
			
			output(output, traceTypeDelim);
			
			output(output, getTraceTypeTextFormatted(traceType));
			
			String delim = "";
			for (Object i : traceElements) {
				
				output(output, delim);
				outputI(output, convertBlurbElement(sectInfo, sectName, markup, -1, i).trim());
				
				delim = ", ";
			}
			
			traceTypeDelim = "\n";
		}
		
		if (!hasCase) {
			
			String caseId = getCaseId(result);
			if (caseId != null) {
				
				if (!output.isEmpty()) {
					output(output, "\n");
				}
				
				output(output, "Proof case: \t");
				outputI(output, caseId);
			}
		}
		
		// The code below prints trace contents as they are output from Z/EVES
//		for (Entry<String, List<Object>> traceContent : trace.getTraceContents().entrySet()) {
//			
//			output(output, traceContent.getKey());
//			output(output, " ");
//			
//			for (Iterator<?> it = traceContent.getValue().iterator(); it.hasNext(); ) {
//				Object i = it.next();
//
//				outputI(output, convertBlurbElement(sectInfo, sectName, markup, -1, i).trim());
//				
//				// add commas for non-last elements per trace type
//				if (it.hasNext()) {
//					output(output, ",");
//				}
//				
//				output(output, " ");
//			}
//		}
		
		// The code below used to do output wrapping within textWidth
//		StringBuilder infoOut = new StringBuilder();
//		
//		String delim = "";
//		for (PartitionString str : output) {
//			
//			int lastLineStart = infoOut.lastIndexOf("\n");
//			if (lastLineStart < 0) {
//				lastLineStart = 0;
//			}
//			
//			String sep = delim;
//			if (textWidth > 0 && 
//					infoOut.length() + str.text.length() + 1 - lastLineStart > textWidth) {
//				// the text will go outside of the line
//				// so move it to new line (if not the first string added)
//				if (infoOut.length() > 0) {
//					sep = "\n";
//				}
//			}
//			
//			infoOut.append(sep).append(str);
//			
//			delim = " ";
//		}
		
		return output;
	}
	
	private static String getTraceTypeTextFormatted(TraceType type) {
		return getTraceTypeText(type) + "\t";
	}
	
	private static String getTraceTypeText(TraceType type) {
		switch(type) {
		case APPLY: return "Applying lemma: ";
		case APPLY_TARGET: return "Target: ";
		case BEGIN_PROOF: return "Beginning proof: ";
		case CASE: return "Starting case: ";
		case CASE_COMPLETE: return "Completing case: ";
		case EQUALITY_SUB: return "Substituting: ";
		case FRULE: return "Using forward rules: ";
		case GRULE: return "Using assumptions: ";
		case INSTANTIATE: return "Instantiating: ";
		case INVOKE: return "Invoking: ";
		case REWRITE: return "Using rewrite rules: ";
		case USE: return "Using lemma: ";
		case SPLIT: return "Splitting on: ";
		default: return type.toString() + ": ";
		}
	}
	
	private static String convertBlurbElement(SectionManager sectInfo, String sectName,
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
	
	private static String createProofResultDelimiter(int textWidth) {
		StringBuilder delim = new StringBuilder("\n\n");
		
		for (int index = 0; index < textWidth; index++) {
			delim.append("\u2500");
		}
		
		delim.append("\n\n");
		
		return delim.toString();
	}
	
	private static IDocument createDocument(Markup markup, List<PartitionString> output,
			Map<Annotation, Position> annotations) {

		PredefinedTokenScanner scanner = new PredefinedTokenScanner();
		
		StringBuilder out = new StringBuilder();
		for (PartitionString token : output) {
			
			String text = token.text;
			
			if (text.isEmpty()) {
				continue;
			}
			
			int prevLength = out.length();
			out.append(text);

			Position resultPos = new Position(prevLength, text.length());
			
			String partition = getPartition(markup, token.partitionType);
			if (partition != null) {
				scanner.addTokenPosition(resultPos, partition);
			}
			
			String annotationType = getAnnotationType(token.partitionType);
			if (annotationType != null) {
				Annotation annotation = new Annotation(false);
				annotation.setType(annotationType);
				annotations.put(annotation, resultPos);
			}
		}
		
	    Document document = new Document(out.toString());
	    
//		CZTPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
//				document, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_UTF8);
	    
	    String[] contentTypes = scanner.getContentTypes().toArray(new String[0]);
	    IDocumentPartitioner partitioner = new FastPartitioner(scanner, contentTypes);
	    document.setDocumentPartitioner(IZPartitions.Z_PARTITIONING, partitioner);
	    partitioner.connect(document);
	    
	    return document;
	}
	
	private static void outputE(List<PartitionString> output, String text){
		output.add(new PartitionString(ResultPartitionType.ERROR, text));
	}
	
	private static void outputW(List<PartitionString> output, String text){
		output.add(new PartitionString(ResultPartitionType.WARNING, text));
	}
	
	private static void outputZ(List<PartitionString> output, String text){
		output.add(new PartitionString(ResultPartitionType.Z, text));
	}
	
	private static void outputI(List<PartitionString> output, String text){
		output.add(new PartitionString(ResultPartitionType.Z_INFO, text));
	}
	
	private static void output(List<PartitionString> output, String text){
		output.add(new PartitionString(ResultPartitionType.COMMENT, text));
	}
	
	private enum ResultPartitionType {
		Z,
		Z_INFO,
		COMMENT,
		ERROR,
		WARNING
	}
	
	private static String getPartition(Markup markup, ResultPartitionType type) {
		
		switch (type) {
		case Z_INFO:
		case Z:
			return markup == Markup.UNICODE ? 
					IZPartitions.Z_PARAGRAPH_UNICODE_ZSECTION : 
					IZPartitions.Z_PARAGRAPH_LATEX_ZED;
		case COMMENT:
			return null;
		default:
			return null;
		}
	}
	
	private static String getAnnotationType(ResultPartitionType type) {

		switch (type) {
		case ERROR:
			return "net.sourceforge.czt.eclipse.zeves.ui.annotation.output.error";
		case WARNING:
			return "net.sourceforge.czt.eclipse.zeves.ui.annotation.output.warning";
		default:
			return null;
		}
	}
	
	private static class PartitionString {
		private final String text;
		private final ResultPartitionType partitionType;
		
		public PartitionString(ResultPartitionType partitionType, String text) {
			super();
			this.text = text;
			this.partitionType = partitionType;
		}
		
	}
	
	private static List<PartitionString> convertOutputResult(SectionManager sectInfo, 
			String sectName, Markup markup, int textWidth, Object result, boolean isPred) {

		String str = result.toString().trim();
		
		List<PartitionString> output = new ArrayList<PartitionString>();
		
		if (ZEvesOutput.UNPRINTABLE_PREDICATE.equals(str)) {
			// a special case - do not try parsing
			outputW(output, str);
			return output;
		}
		
		try {
			String converted = isPred ? 
					ZEvesResultConverter.convertPred(sectInfo, sectName, str, markup, textWidth, true) : 
					ZEvesResultConverter.convertParas(sectInfo, sectName, str, markup, textWidth, true);

			outputZ(output, converted);
			return output;
			
		} catch (IOException e) {
			ZEvesUIPlugin.getDefault().log(e);
			return withWarning("I/O problems parsing Z/EVES result: " + e.getMessage().trim(), str);
		} catch (CommandException e) {
			Throwable cause = e.getCause();
			if (cause == null) {
				cause = e;
			}
			
			String msg = "Cannot parse Z/EVES result: " + DocumentUtil.clean(cause.getMessage()).trim();
			ZEvesUIPlugin.getDefault().log(msg, cause);
			return withWarning(msg, str);
		}
	}
	
	private static List<PartitionString> withWarning(String warning, String result) {
		
		List<PartitionString> output = new ArrayList<PartitionString>();
		
		outputW(output, warning);
		output(output, "\n\n");
		outputZ(output, result);
		
		return output;
	}
	
	public interface IZEvesInfoProvider extends IZInfoObject {
		
		@Override
		public String loadDescription(IProgressMonitor monitor) throws CoreException;
		
		public IZInfoConfiguration loadContents(Markup markup, 
				boolean showTrace, IProgressMonitor monitor)
				throws CoreException;
	}
	
	public interface IZInfoConfiguration {
		
		public IDocument getDocument();
		
		public SourceViewerConfiguration getConfiguration();
		
		public Map<Annotation, Position> getAnnotations();
	}
	
	private static class ZInfoConfiguration implements IZInfoConfiguration {

		private final SourceViewerConfiguration configuration;
		private final IDocument document;
		private final Map<Annotation, Position> annotations;
		
		public ZInfoConfiguration(SourceViewerConfiguration configuration, IDocument document,
				Map<Annotation, Position> annotations) {
			this.configuration = configuration;
			this.document = document;
			this.annotations = new HashMap<Annotation, Position>(annotations);
		}

		@Override
		public IDocument getDocument() {
			return document;
		}

		@Override
		public SourceViewerConfiguration getConfiguration() {
			return configuration;
		}

		@Override
		public Map<Annotation, Position> getAnnotations() {
			return Collections.unmodifiableMap(annotations);
		}
	}
	
	public interface IZEditorObject {
		
		public IZEditor getEditor();
		
		public Position getPosition();
		
	}
	
	public interface IProofObject extends IZEditorObject {
		
		public String getSectionName();
		
		public SectionManager getSectionManager();
		
		public String getGoalName();
		
		public int getZEvesStepIndex();
	}
	
	/**
	 * A custom token scanner for the output view - it allows to pre-set partitions
	 * based on information displayed in the output. This is necessary, for example, to
	 * print predicates that are not wrapped in any Z paragraph, or to distinguish
	 * the inline comments, etc. 
	 * 
	 * @author Andrius Velykis
	 */
	private static class PredefinedTokenScanner extends RuleBasedScanner implements IPartitionTokenScanner {
		
		private final Map<Position, String> tokenPositions = new LinkedHashMap<Position, String>();
		
		public void addTokenPosition(Position pos, String contentType) {
			tokenPositions.put(pos, contentType);
		}
		
		public Set<String> getContentTypes() {
			return new HashSet<String>(tokenPositions.values());
		}
		
		/*
		 * @see ITokenScanner#nextToken()
		 */
		@Override
		public IToken nextToken() {

			fTokenOffset= fOffset;
			fColumn= UNDEFINED;

			if (read() == EOF) {
				return Token.EOF;
			}
			
			unread();
			
			for (Entry<Position, String> tokenPos : tokenPositions.entrySet()) {
				
				Position pos = tokenPos.getKey();
				
				if (pos.overlapsWith(fTokenOffset, fRangeEnd - fTokenOffset)) {
					
					if (fTokenOffset < pos.getOffset()) {
						// the position does not start yet - read up to its start
						read(fTokenOffset, pos.getOffset());
						return Token.UNDEFINED;
					}
					
					int posEnd = pos.getOffset() + pos.getLength();
					
					read(fTokenOffset, posEnd);
					return new Token(tokenPos.getValue());
				}
			}
			
			// nothing found - read to the end
			read(fTokenOffset, fRangeEnd);
			return Token.UNDEFINED;
		}
		
		private void read(int start, int end) {
			for (int i = start; i < end; i++) {
				read();
			}
		}

		@Override
		public void setPartialRange(IDocument document, int offset, int length, String contentType,
				int partitionOffset) {
			// ignore for now?
		}
		
	}
	
}

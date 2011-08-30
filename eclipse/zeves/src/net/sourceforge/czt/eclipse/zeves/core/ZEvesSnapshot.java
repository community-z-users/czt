package net.sourceforge.czt.eclipse.zeves.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.AbstractMap.SimpleEntry;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.Position;

import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.response.ZEvesOutput;

/**
 * This class represent a snapshot of Z/Eves submit state. When Z/Eves prover is
 * interacted with, the state and results are registered in Z/Eves snapshot,
 * e.g. when paragraphs/commands are submitted, their results and/or errors are
 * stored in the snapshot. Then, when commands are undone, Z/Eves snapshot is
 * updated accordingly.
 * 
 * The snapshot is based on a list of sections and result entries. The sections
 * must be submitted sequentially - if one requires to update a section that was
 * submitted earlier, Z/Eves must be undone until that point, only then adding
 * new results is permitted.
 * 
 * The sections are identified by a pair of file path and section name. This in
 * general allows having more than one section per file.
 * 
 * The entries are identified by their {@link Position} in specification file.
 * Therefore, when term positions in specification change (e.g. due to editing),
 * the invalid entries must be removed from the snapshot and resubmitted to
 * Z/Eves afterwards. Use {@link #undoThrough(ZEvesApi, String, int)} to undo
 * the snapshot (and Z/Eves) until a certain offset in a specification file.
 * 
 * Results are added to the snapshot with various add(Target)Result() methods.
 * However, before adding results for a particular section, it must be indicated
 * that the section is being updated with the
 * {@link #updatingSection(Position, String, String)} method.
 * 
 * To indicate that a section has been submitted completely (and therefore
 * should not be resubmitted),
 * {@link #completeSection(Position, String, String)} must be called upon
 * section end.
 * 
 * @author Andrius Velykis
 */
public class ZEvesSnapshot {
	
	private enum ResultType {
		/** Used for section begin/end entries */
		SECTION,
		PARA,
		GOAL,
		PROOF,
		ERROR
	}
	
	private final PositionOverlapComparator posOverlapComparator = new PositionOverlapComparator();

	/**
	 * Sequential list of unique sections that have result entries within the snapshot
	 */
	private final List<FileSection> sections = new ArrayList<FileSection>();
	
	/**
	 * Map that stores indices of last entries per section. The index can be
	 * used to retrieve section's last entry from {@link #positionResults} map.
	 */
	private final Map<FileSection, Integer> lastEntryIndices = new HashMap<FileSection, Integer>();
	
	/**
	 * Set of completed sections
	 */
	private final Set<FileSection> completedSections = new HashSet<FileSection>();
	
	/**
	 * A sequential list of Z/Eves submit results per section. Each entry
	 * represents a single result for a certain section. It is ensured that
	 * lists of section-entries are in the same sequence as in {@link #sections}
	 * list, i.e. if {@link #sections} contains sections [A, B, C] in the
	 * sequence, then {@link #positionResults} contains their entries in the
	 * same order: [(A, A1), (A, A2), ..., (A, An), (B, B1), ..., (C, C1), ...].
	 */
	private final List<Entry<PositionInfo, Object>> positionResults = new ArrayList<Entry<PositionInfo, Object>>();
	
	/**
	 * Currently active (updating) section
	 */
	private FileSection updatingSection = null;
	
	/**
	 * Mark the given section (filePath + sectionName) to be updating. This
	 * section must either be a new section in the snapshot, or be the last
	 * section already (e.g. continuing to update the last section).
	 * 
	 * @param pos
	 *            Position of section header
	 * @param filePath
	 *            Path of the file containing the section
	 * @param sectionName
	 *            Name of section
	 */
	public void updatingSection(Position pos, String filePath, String sectionName) {
		
		FileSection section = new FileSection(filePath, sectionName);
		int sectionIndex = sections.indexOf(section);
		int lastIndex = sections.size() - 1;
		Assert.isLegal(sectionIndex < 0 || sectionIndex == lastIndex,
				"Cannot update non-last section: undo first");
		Assert.isLegal(!isSectionCompleted(section), 
				"Cannot update a completed section: undo first");
		
		this.updatingSection = section;
		
		if (sectionIndex < 0) {
			// new section
			sections.add(updatingSection);
			
			Assert.isLegal(pos != null, "No section header position indicated for a new section");
			
			// also add an entry for the section to signal its start
			// note that this also ensures that sections will always have at least one entry
			addResult(new PositionInfo(updatingSection, pos, ResultType.SECTION), null);
		}
	}
	
	/**
	 * Marks the section completed. Then one can query
	 * {@link #isSectionCompleted(String, String)} to check and do not resubmit
	 * a section in the future. Note that the indicated section must be the last
	 * updated section.
	 * 
	 * @param pos
	 *            Position of section footer (section end)
	 * @param filePath
	 *            Path of the file containing the section
	 * @param sectionName
	 *            Name of section
	 */
	public void completeSection(Position pos, String filePath, String sectionName) {
		FileSection section = new FileSection(filePath, sectionName);
		int sectionIndex = sections.indexOf(section);
		Assert.isLegal(sectionIndex == sections.size() - 1, "Cannot complete non-last section");
		
		// mark complete
		markSectionCompleted(section, true);
		
		// also add an entry for the section end
		addResult(new PositionInfo(section, pos, ResultType.SECTION), null);
	}

	/**
	 * Adds a Z/Eves result for a submitted paragraph (non-ProofScript) to the
	 * snapshot. Each paragraph in Z/Eves is assigned a history index, which
	 * must be indicated here. The history index is used to undo in Z/Eves
	 * afterwards.
	 * 
	 * Results must be added in increasing position order, as well as increasing
	 * history index order.
	 * 
	 * @param pos
	 *            Position of paragraph in the specification file
	 * @param historyIndex
	 *            Z/Eves history index assigned for the submitted paragraph
	 * @param result
	 *            Z/Eves result for the submitted paragraph (can be various
	 *            representations, e.g. ZEvesAxDef, ZEvesGivenDef, etc.)
	 */
	public void addParaResult(Position pos, int historyIndex, Object result) {

		assertPositionLegal(pos);

		// check that paragraphs are submitted in increasing order
		ParaPosition lastPos = (ParaPosition) getLastPositionInfo(ResultType.PARA);
		if (lastPos != null) {
			Assert.isLegal(historyIndex > lastPos.getHistoryIndex(),
					"Paragraph history must be added in increasing order. " 
							+ "Last index: [" + lastPos.getHistoryIndex() 
							+ "], new: [" + historyIndex + "]");
		}
		
		addResult(new ParaPosition(updatingSection, pos, historyIndex), result);
	}
	
	private void assertPositionLegal(Position pos) {
		
		// check positions are added in increasing order for the same section
		PositionInfo lastPos = getLastPositionInfo();
		if (lastPos != null && lastPos.getSection().equals(updatingSection)) {
			
			int lastEnd = getEnd(lastPos.getPosition());
			Assert.isLegal(pos.getOffset() >= lastEnd,
					"Result positions must be added in increasing order. " 
							+ "Last position: [" + lastEnd 
							+ "], new: [" + pos + "]");
		}
	}
	
	private PositionInfo getLastPositionInfo() {
		if (positionResults.isEmpty()) {
			return null;
		}
		
		return positionResults.get(positionResults.size() - 1).getKey();
	}
	
	private static int getEnd(Position pos) {
		return pos != null ? pos.getOffset() + pos.getLength() : -1;
	}
	
	private PositionInfo getLastPositionInfo(ResultType type) {
		
		for (int index = positionResults.size() - 1; index >= 0; index--) {
			Entry<PositionInfo, Object> result = positionResults.get(index);
			if (result.getKey().getType() == type) {
				return result.getKey();
			}
		}
		
		return null;
	}
	
	private void addResult(PositionInfo posInfo, Object result) {
		positionResults.add(new SimpleEntry<PositionInfo, Object>(posInfo, result));
		
		// mark the last entry index for the section
		lastEntryIndices.put(posInfo.getSection(), positionResults.size() - 1);
	}

	/**
	 * Adds an error result (a Z/Eves error) for a certain position to the
	 * snapshot. The error is indicated by a {@link ZEvesException}.
	 * 
	 * Results must be added in increasing position order.
	 * 
	 * @param pos
	 *            Position of specification part that caused the Z/Eves error
	 * @param ex
	 *            The error as ZEvesException
	 */
	public void addError(Position pos, ZEvesException ex) {
		assertPositionLegal(pos);
		addResult(new PositionInfo(updatingSection, pos, ResultType.ERROR), ex);
	}
	
	/**
	 * Adds a Z/Eves result for a proof script goal ("try-lemma") to the
	 * snapshot. This method differentiates from a general
	 * {@link #addProofResult(Position, ProofScript, Integer, ZEvesOutput)} in
	 * the way that it will not need to be "undone" during undo: this command
	 * does not change Z/Eves state.
	 * 
	 * Results must be added in increasing position order.
	 * 
	 * @param pos
	 *            Position of proof script header in the specification file
	 * @param result
	 *            Z/Eves result for "try-lemma"
	 */
	public void addGoalResult(Position pos, ZEvesOutput result) {
		assertPositionLegal(pos);
		addResult(new PositionInfo(updatingSection, pos, ResultType.GOAL), result);
	}
	
	/**
	 * Adds a Z/Eves result for a submitted proof command to the snapshot. Each
	 * proof command in Z/Eves is assigned an index, which must be indicated
	 * here. Each submitted result is undone with a single "back" during undo
	 * afterwards.
	 * 
	 * Results must be added in increasing position order.
	 * 
	 * @param pos
	 *            Position of proof command in the specification file
	 * @param script
	 *            Parent proof script of the command
	 * @param zEvesStepIndex
	 *            Z/Eves proof step index assigned for the submitted command
	 * @param result
	 *            Z/Eves goal for this proof step
	 */
	public void addProofResult(Position pos, ProofScript script, Integer zEvesStepIndex,
			ZEvesOutput result) {
		
		assertPositionLegal(pos);
		
		String goalName = script.getZName().getWord();
		addResult(new ProofStepPosition(updatingSection, pos, goalName, zEvesStepIndex), result);
	}
	
	
	/**
	 * Retrieves the max offset in the snapshot for the given file. Note that
	 * several sections could have been submitted in a certain file. This method
	 * will give the end offset of submitted entries of the last section in the
	 * given file.
	 * 
	 * @param filePath
	 *            Path of file in question
	 * @return end offset of the last submitted result for the file, or -1 if
	 *         nothing has been submitted for the file
	 */
	public int getLastPositionOffset(String filePath) {
		int lastEntryIndex = getLastEntryIndex(filePath);
		if (lastEntryIndex < 0) {
			// nothing submitted
			return -1;
		}
		
		return getEnd(positionResults.get(lastEntryIndex).getKey().getPosition());
	}
	
	private int getLastEntryIndex(String filePath) {
		int maxIndex = -1;
		for (FileSection section : sections) {
			if (section.getFilePath().equals(filePath)) {
				maxIndex = Math.max(maxIndex, lastEntryIndices.get(section));
			}
		}
		
		return maxIndex;
	}
	
	/**
	 * Checks whether undo is necessary if updates are to be done at the given
	 * offset of file. Undo is required if the file has results submitted after
	 * the given offset, or if there are other sections submitted after the file
	 * has been submitted.
	 * 
	 * @param filePath
	 *            Path of file in question
	 * @param offset
	 *            Offset within the given file
	 * @return true if undo is necessary before updating at the given offset
	 *         (e.g. editing, or submitting to Z/Eves), false otherwise
	 */
	public boolean needUndo(String filePath, int offset) {
		int lastIndexBefore = getLastIndexBeforeOffset(filePath, offset);
		
		// check whether the last untouched index is not the last ever
		return lastIndexBefore < positionResults.size() - 1;
	}
	
	/**
	 * Retrieves a result in the snapshot for the given section and position in
	 * its specification file. A result that has a position overlapping the
	 * given position is returned. Note that the behavior is undetermined if
	 * there are multiple results overlapping the given position, but it is
	 * guaranteed that one of the results is returned.
	 * 
	 * @param filePath
	 *            Path of file containing the section
	 * @param sectionName
	 *            Name of section
	 * @param pos
	 *            Position in the specification file
	 * @return The result with a position that overlaps given position. Can be
	 *         any of the submitted results (e.g. error, paragraph result or
	 *         proof result)
	 */
	public Object getResult(String filePath, String sectionName, Position pos) {
		
		Entry<PositionInfo, Object> result = getResultEntry(new FileSection(filePath, sectionName), pos);
		if (result == null) {
			return null;
		}
		
		return result.getValue();
	}
	
	/*
	 * Finds a result entry for the given position. Used binary search algorithm
	 * to perform the search, because the results list is sorted in increasing
	 * order (by section index, then by position).
	 */
	private Entry<PositionInfo, Object> getResultEntry(FileSection section, Position pos) {
		// wrap the position into entry to allow for searching
		Entry<PositionInfo, Object> posKey = 
				new SimpleEntry<PositionInfo, Object>(new PositionInfo(section, pos, null), null);
		
		// do binary search that stops if a position overlapping the given is found
		int found = Collections.binarySearch(positionResults, posKey, posOverlapComparator);
		if (found < 0) {
			return null;
		}
		
		return positionResults.get(found);
	}
	
	/**
	 * A specialized version of {@link #getResult(String, String, Position)},
	 * which only differs if the found result is a proof result. In that case,
	 * returns a {@link ProofResult} object with the result and its Z/Eves step
	 * index.
	 * 
	 * @param filePath
	 *            Path of file containing the section
	 * @param sectionName
	 *            Name of section
	 * @param pos
	 *            Position in the specification file
	 * @return The result with a position that overlaps given position. Can be
	 *         any of the submitted results (e.g. error, paragraph result or
	 *         proof result). For proof result, returns a {@link ProofResult}
	 *         object.
	 * 
	 * @see #getResult(String, String, Position)
	 */
	public Object getProofResult(String filePath, String sectionName, Position pos) {
		
		Entry<PositionInfo, Object> result = getResultEntry(new FileSection(filePath, sectionName), pos);
		if (result == null) {
			return null;
		}
		
		PositionInfo posInfo = result.getKey();
		if (posInfo.getType() == ResultType.PROOF) {
			int stepIndex = ((ProofStepPosition) posInfo).getStepIndex();
			return new ProofResult(stepIndex, (ZEvesOutput) result.getValue());
		}
		
		return result.getValue();
	}
	
	/**
	 * Clears the data stored in Z/Eves snapshot (to be used with accompanying
	 * {@link ZEvesApi#reset()}).
	 * 
	 * @return list of file paths that were cleared - to allow for removal of
	 *         markers, etc.
	 */
	public Set<String> clear() {
		positionResults.clear();
		
		Set<String> clearedPaths = new LinkedHashSet<String>();
		for (FileSection section : sections) {
			clearedPaths.add(section.getFilePath());
		}
		
		sections.clear();
		lastEntryIndices.clear();
		completedSections.clear();
		updatingSection = null;
		
		return clearedPaths;
	}
	
	/**
	 * Undoes Z/Eves commands up to (and including) the given offset. Calculates
	 * paragraphs and proof commands that have been submitted after the given
	 * offset, and undoes them in Z/Eves prover. The undone results are removed
	 * from the snapshot as well, and the last affected section is marked
	 * incomplete.
	 * 
	 * This undoes commands in the given file path, as well as all sections
	 * submitted after the offset.
	 * 
	 * @param zEvesApi
	 *            Z/Eves API to perform undo calls
	 * @param filePath
	 *            Path of specification file
	 * @param offset
	 *            Offset in the given specification file
	 * @return Mapping from file paths to offsets from which commands were
	 *         undone
	 * @throws ZEvesException
	 *             If errors occur during Z/Eves communication
	 */
	public Map<String, Integer> undoThrough(ZEvesApi zEvesApi, String filePath, int offset)
			throws ZEvesException {
		
		// find last index to keep (before the given offset)
		int lastRetainedEntryIndex = getLastIndexBeforeOffset(filePath, offset);
		
		// undo everything after the index
		return undoFromIndex(zEvesApi, lastRetainedEntryIndex);
	}
	
	/*
	 * Scans the results stored in the snapshot and finds the last index of an
	 * entry that is strictly before the given offset. Can be used to check
	 * whether something needs to be removed after certain offset, or to find
	 * where to start removing from.
	 */
	private int getLastIndexBeforeOffset(String filePath, int offset) {
		
		int fileLastEntryIndex = getLastEntryIndex(filePath);
		if (fileLastEntryIndex < 0) {
			// this file does not have any results - everything is "before"
			return positionResults.size() - 1;
		}
		
		int index = 0;
		int skipUntilAfter = -1;
		for (Iterator<Entry<PositionInfo, Object>> it = positionResults.iterator(); it.hasNext(); index++) {
			
			PositionInfo resultPos = it.next().getKey();
			
			if (index <= skipUntilAfter) {
				// skipping - still before the position
				continue;
			}
			
			FileSection section = resultPos.getSection();
			if (!section.getFilePath().equals(filePath)) {
				// this section is from other file path - skip until its end
				skipUntilAfter = lastEntryIndices.get(section);
				continue;
			}
			
			if (index == fileLastEntryIndex) {
				/*
				 * Reached the last ever entry for this file, which means that
				 * editing is done after the last entry. Therefore, it makes
				 * this entry to be the last entry before given offset (next
				 * step will switch into another section).
				 */
				return index;
			}
			
			// here we are in the correct file section, check the position
			if (getEnd(resultPos.getPosition()) < offset) {
				// still before the position
				continue;
			}
			
			return index - 1;
		}
		
		// this means last index ever is before offset (e.g. nothing to remove)
		return positionResults.size() - 1;
	}

	/*
	 * Performs undo for all results submitted after the given index (excluding the index).
	 */
	private Map<String, Integer> undoFromIndex(ZEvesApi zEvesApi, int lastRetainedEntryIndex)
			throws ZEvesException {
		
		if (lastRetainedEntryIndex >= positionResults.size() - 1) {
			// nothing to undo
			return new HashMap<String, Integer>(); 
		}
		
		int undoThroughHistoryIndex = -1;
		Map<String, Integer> proofUndoCounts = new HashMap<String, Integer>();

		Map<String, Integer> fileUndoOffsets = new HashMap<String, Integer>();
		
		FileSection lastRetainedSection = null;
		if (lastRetainedEntryIndex >= 0) {
			// mark its section's last index to be this
			lastRetainedSection = positionResults.get(lastRetainedEntryIndex).getKey().getSection();
			
			int previousLastIndex = lastEntryIndices.get(lastRetainedSection);
			if (lastRetainedEntryIndex < previousLastIndex) {
				// lost entries within the section - mark it incomplete
				markSectionCompleted(lastRetainedSection, false);
				
				// update with the new last entry index
				lastEntryIndices.put(lastRetainedSection, lastRetainedEntryIndex);
			}
		}
		
		List<Entry<PositionInfo, Object>> removeSubList = 
				positionResults.subList(lastRetainedEntryIndex + 1, positionResults.size());
		
		// analyze removed results to know how much to undo the prover
		for (Entry<PositionInfo, Object> resultEntry : removeSubList) {
			
			PositionInfo resultPos = resultEntry.getKey();
			
			FileSection section = resultPos.getSection();
			String resultPath = section.getFilePath();
			Integer undoOffset = fileUndoOffsets.get(resultPath);
			if (undoOffset == null) {
				// first undo offset for this file - mark it down
				fileUndoOffsets.put(resultPath, resultPos.getPosition().getOffset());
			}
			
			switch (resultPos.getType()) {
			case PARA: {
				/*
				 * For paragraphs, mark the first history index available in the
				 * "remove" zone - then undo through to (including) this
				 */
				if (undoThroughHistoryIndex < 0) {
					undoThroughHistoryIndex = ((ParaPosition) resultPos).getHistoryIndex();
				}
				break;
			}
			case PROOF: {
				/*
				 * For proofs, increment undo count for the given goal name -
				 * each proof steps means one "back" sent to Z/Eves for that
				 * particular goal
				 */
				ProofStepPosition proofPos = (ProofStepPosition) resultPos;
				String goalName = proofPos.getGoalName();
				
				// increment undo count
				Integer undoCount = proofUndoCounts.get(goalName);
				proofUndoCounts.put(goalName, (undoCount != null ? undoCount.intValue() : 0) + 1);
				break;
			}
			default: {
				/*
				 * For the rest (goals and errors), do nothing special, they
				 * will be just removed from the list, since we do not need to
				 * undo them in Z/Eves. Errors are not sent to Z/Eves at all,
				 * while goals are attached to the theorem paragraphs.
				 */
			}
			}
		}
		
		if (lastRetainedSection == null) {
			// all entries removed
			sections.clear();
			lastEntryIndices.clear();
			completedSections.clear();
		} else {
			// remove sections after the last retained one
			int keepIndex = sections.indexOf(lastRetainedSection);
			for (int index = sections.size() - 1; index > keepIndex; index--) {
				FileSection section = sections.get(index);
				
				sections.remove(index);
				lastEntryIndices.remove(section);
				completedSections.remove(section);
			}
		}
		
		// remove contents from the list
		removeSubList.clear();
		
		// undo proofs
		for (Entry<String, Integer> countEntry : proofUndoCounts.entrySet()) {
			String goalName = countEntry.getKey();
			int undoCount = countEntry.getValue();
			
			zEvesApi.setCurrentGoalName(goalName);
			zEvesApi.back(undoCount);
		}
		
		// undo paragraphs
		if (undoThroughHistoryIndex > 0) {
			zEvesApi.undoBackThrough(undoThroughHistoryIndex);
		}
		
		// reset updating section - it needs to be specified again after undo
		updatingSection = null;
		return fileUndoOffsets;
	}
	
	/**
	 * Undoes Z/Eves commands up to (and including) the given section.
	 * Calculates paragraphs and proof commands that have been submitted for the
	 * given section, and all sections after it, and undoes them in Z/Eves
	 * prover. The undone results are removed from the snapshot as well.
	 * 
	 * @param zEvesApi
	 *            Z/Eves API to perform undo calls
	 * @param section
	 *            section to undo (inclusive)
	 * @return Mapping from file paths to offsets from which commands were
	 *         undone
	 * @throws ZEvesException
	 *             If errors occur during Z/Eves communication
	 */
	public Map<String, Integer> undoThrough(ZEvesApi zEvesApi, FileSection section)
			throws ZEvesException {
		
		int sectionIndex = sections.indexOf(section);
		if (sectionIndex < 0) {
			// not submitted
			return new HashMap<String, Integer>();
		}
		
		// get the section to keep (one before the removed one)
		FileSection keepSection = null;
		if (sectionIndex > 0) {
			keepSection = sections.get(sectionIndex - 1);
		}

		// if no section to keep, last retained index is -1
		int lastRetainedEntryIndex = keepSection != null ? lastEntryIndices.get(keepSection) : -1;
		
		return undoFromIndex(zEvesApi, lastRetainedEntryIndex);
	}
	
	/**
	 * Retrieves the list of sections that have entries in the snapshot
	 * 
	 * @return List of sections
	 */
	public List<FileSection> getSections() {
		return new ArrayList<FileSection>(sections);
	}
	
	private void markSectionCompleted(FileSection section, boolean complete) {
		if (complete) {
			completedSections.add(section);
		} else {
			completedSections.remove(section);
		}
	}
	
	/**
	 * Checks if the given section is marked completed (i.e. submitted fully to
	 * Z/Eves)
	 * 
	 * @param filePath
	 *            Path of file containing the section
	 * @param sectionName
	 *            Name of section
	 * @return true if section is marked completed, false otherwise
	 */
	public boolean isSectionCompleted(String filePath, String sectionName) {
		return isSectionCompleted(new FileSection(filePath, sectionName));
	}
	
	private boolean isSectionCompleted(FileSection section) {
		return completedSections.contains(section);
	}
	
	private static class PositionInfo {
		
		private final FileSection section;
		private final Position pos;
		private final ResultType type;
		
		public PositionInfo(FileSection section, Position pos, ResultType type) {
			Assert.isNotNull(section, "File section must be indicated before update");
			this.section = section;
			this.pos = pos;
			this.type = type;
		}
		
		public FileSection getSection() {
			return section;
		}

		public Position getPosition() {
			return pos;
		}

		public ResultType getType() {
			return type;
		}
	}
	
	private static class ParaPosition extends PositionInfo {
		
		private final int historyIndex;
		
		public ParaPosition(FileSection section, Position pos, int historyIndex) {
			super(section, pos, ResultType.PARA);
			this.historyIndex = historyIndex;
		}
		
		public int getHistoryIndex() {
			return historyIndex;
		}
	}
	
	private static class ProofStepPosition extends PositionInfo {
		
		private final String goalName;
		private final Integer zEvesStepIndex;
		
		public ProofStepPosition(FileSection section, Position pos, String goalName, Integer zEvesStepIndex) {
			super(section, pos, ResultType.PROOF);
			this.goalName = goalName;
			this.zEvesStepIndex = zEvesStepIndex;
		}
		
		public String getGoalName() {
			return goalName;
		}

		public Integer getStepIndex() {
			return zEvesStepIndex;
		}
	}
	
	private class PositionOverlapComparator implements Comparator<Entry<PositionInfo, Object>> {

		@Override
		public int compare(Entry<PositionInfo, Object> o1, Entry<PositionInfo, Object> o2) {
			
			FileSection s1 = o1.getKey().getSection();
			FileSection s2 = o2.getKey().getSection();
			
			// first check whether the sections are different
			if (!s1.equals(s2)) {
				int sectCompare = sections.indexOf(s1) - sections.indexOf(s2);
				Assert.isTrue(sectCompare != 0, "No duplicates can be in the section list");
				return sectCompare;
			}
			
			Position p1 = o1.getKey().getPosition();
			Position p2 = o2.getKey().getPosition();
			
			if (p1.overlapsWith(p2.getOffset(), p2.getLength())) {
				// consider them equal
				return 0;
			}
			
			if (p1.getOffset() <= p2.getOffset()) {
				return -1;
			} else {
				return 1;
			}
		}
		
	}
	
	public static class ProofResult {
		private final Integer stepIndex;
		private final ZEvesOutput result;
		
		public ProofResult(Integer stepIndex, ZEvesOutput result) {
			this.stepIndex = stepIndex;
			this.result = result;
		}

		public Integer getStepIndex() {
			return stepIndex;
		}

		public ZEvesOutput getResult() {
			return result;
		}
	}
	
	/**
	 * Immutable structure to identify section within its file. This is used to
	 * have a more general approach of multiple sections per file, thus we need
	 * more identification than just a section name.
	 * 
	 * @author Andrius Velykis
	 */
	public static class FileSection {
		
		private final String filePath;
		private final String sectionName;
		
		public FileSection(String filePath, String sectionName) {
			this.filePath = filePath;
			this.sectionName = sectionName;
		}

		public String getFilePath() {
			return filePath;
		}
		
		public String getSectionName() {
			return sectionName;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((filePath == null) ? 0 : filePath.hashCode());
			result = prime * result + ((sectionName == null) ? 0 : sectionName.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			FileSection other = (FileSection) obj;
			if (filePath == null) {
				if (other.filePath != null)
					return false;
			} else if (!filePath.equals(other.filePath))
				return false;
			if (sectionName == null) {
				if (other.sectionName != null)
					return false;
			} else if (!sectionName.equals(other.sectionName))
				return false;
			return true;
		}
	}
	
}

package net.sourceforge.czt.eclipse.zeves.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.Position;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
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
	
	public static final int GOAL_STEP_INDEX = 1;
	
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
	private final List<SnapshotEntry> positionResults = new ArrayList<SnapshotEntry>();
	
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
			addResult(new SnapshotEntry(updatingSection, pos, ResultType.SECTION, null, null));
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
		addResult(new SnapshotEntry(section, pos, ResultType.SECTION, null, null));
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
	 * @param source
	 *            Source paragraph that generated the result
	 * @param result
	 *            Z/Eves result for the submitted paragraph (can be various
	 *            representations, e.g. ZEvesAxDef, ZEvesGivenDef, etc.)
	 */
	public void addParaResult(Position pos, int historyIndex, Para source, Object result) {

		assertPositionLegal(pos);

		// check that paragraphs are submitted in increasing order
		ParaSnapshotEntry lastEntry = (ParaSnapshotEntry) getLastEntry(ResultType.PARA);
		if (lastEntry != null) {
			Assert.isLegal(historyIndex > lastEntry.getHistoryIndex(),
					"Paragraph history must be added in increasing order. " 
							+ "Last index: [" + lastEntry.getHistoryIndex() 
							+ "], new: [" + historyIndex + "]");
		}
		
		addResult(new ParaSnapshotEntry(updatingSection, pos, historyIndex, source, result));
	}
	
	private void assertPositionLegal(Position pos) {
		
		// check positions are added in increasing order for the same section
		SnapshotEntry lastEntry = getLastEntry();
		if (lastEntry != null && lastEntry.getSection().equals(updatingSection)) {
			
			int lastEnd = getEnd(lastEntry.getPosition());
			Assert.isLegal(pos.getOffset() >= lastEnd,
					"Result positions must be added in increasing order. " 
							+ "Last position: [" + lastEnd 
							+ "], new: [" + pos + "]");
		}
	}
	
	private SnapshotEntry getLastEntry() {
		if (positionResults.isEmpty()) {
			return null;
		}
		
		return positionResults.get(positionResults.size() - 1);
	}
	
	private static int getEnd(Position pos) {
		return pos != null ? pos.getOffset() + pos.getLength() : -1;
	}
	
	private SnapshotEntry getLastEntry(ResultType type) {
		
		for (int index = positionResults.size() - 1; index >= 0; index--) {
			SnapshotEntry result = positionResults.get(index);
			if (result.getType() == type) {
				return result;
			}
		}
		
		return null;
	}
	
	private void addResult(SnapshotEntry entry) {
		positionResults.add(entry);
		
		// mark the last entry index for the section
		lastEntryIndices.put(entry.getSection(), positionResults.size() - 1);
	}

	/**
	 * Adds an error result (a Z/Eves error) for a certain position to the
	 * snapshot. The error is indicated by a {@link ZEvesException}.
	 * 
	 * Results must be added in increasing position order.
	 * 
	 * @param pos
	 *            Position of specification part that caused the Z/Eves error
	 * @param source
	 *            source term that generated the error, if available
	 * @param ex
	 *            The error as ZEvesException
	 */
	public void addError(Position pos, Term source, ZEvesException ex) {
		assertPositionLegal(pos);
		addResult(new SnapshotEntry(updatingSection, pos, ResultType.ERROR, source, ex));
	}
	
	/**
	 * Adds a Z/Eves result for a proof script goal ("try-lemma") to the
	 * snapshot. This method differentiates from a general
	 * {@link #addProofResult(Position, ProofScript, int, ZEvesOutput)} in
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
	public void addGoalResult(Position pos, ProofScript script, ZEvesOutput result) {
		assertPositionLegal(pos);
		
		String goalName = script.getZName().getWord();
		addResult(new ProofSnapshotEntry(updatingSection, pos, ResultType.GOAL, 
				goalName, GOAL_STEP_INDEX, null, result));
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
	 * @param source
	 *            Source proof command that generated the result
	 * @param result
	 *            Z/Eves goal for this proof step
	 */
	public void addProofResult(Position pos, ProofScript script, int zEvesStepIndex,
			ProofCommand source, ZEvesOutput result) {
		
		assertPositionLegal(pos);
		
		String goalName = script.getZName().getWord();
		addResult(new ProofSnapshotEntry(updatingSection, pos, ResultType.PROOF, 
				goalName, zEvesStepIndex, source, result));
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
		
		return getEnd(positionResults.get(lastEntryIndex).getPosition());
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
	public List<ISnapshotEntry> getEntries(String filePath, Position pos) {
		
		/*
		 * first of all check easy cases to short-circuit the algorithm if no
		 * entries are in the file, or if the last entry is before the position
		 * then no results can be found
		 */
		
		int fileLastEntryIndex = getLastEntryIndex(filePath);
		if (fileLastEntryIndex < 0) {
			// this file does not have any results
			return Collections.emptyList();
		}
		
		if (getEnd(positionResults.get(fileLastEntryIndex).getPosition()) < pos.getOffset()) {
			// last file entry is before the position - no results
			return Collections.emptyList();
		}
		
		// there may be some results - start checking thoroughly
		
		List<ISnapshotEntry> overlapEntries = new ArrayList<ISnapshotEntry>();
		
		int prevSectionLastEntryIndex = -1;
		for (int index = 0; index < sections.size(); index++) {
			
			FileSection section = sections.get(index);
			int lastEntryIndex = lastEntryIndices.get(section);
			
			if (section.getFilePath().equals(filePath)) {
				
				// check section items for overlap
				for (int e = prevSectionLastEntryIndex + 1; e <= lastEntryIndex; e++) {
					
					SnapshotEntry entry = positionResults.get(e);
					if (isResultEntry(entry) && overlaps(entry.getPosition(), pos)) {
						overlapEntries.add(entry);
					}
				}
			}
			
			prevSectionLastEntryIndex = lastEntryIndex;
		}
		
		return overlapEntries;
	}
	
	private static boolean overlaps(Position p1, Position p2) {
		return p1.overlapsWith(p2.getOffset(), p2.getLength());
	}
	
	private boolean isResultEntry(SnapshotEntry entry) {
		return entry.getType() != ResultType.SECTION;
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
		
		int prevSectionLastEntryIndex = -1;
		for (int index = 0; index < sections.size(); index++) {
			
			FileSection section = sections.get(index);
			int lastEntryIndex = lastEntryIndices.get(section);
			
			if (section.getFilePath().equals(filePath)) {
				
				// here we are in the correct file section, check the position
				for (int e = prevSectionLastEntryIndex + 1; e <= lastEntryIndex; e++) {
					
					SnapshotEntry entry = positionResults.get(e);
					
					if (getEnd(entry.getPosition()) < offset) {
						// still before the position
						
						if (e == fileLastEntryIndex) {
							/*
							 * Reached the last ever entry for this file, which means that
							 * editing is done after the last entry. Therefore, it makes
							 * this entry to be the last entry before given offset (next
							 * step will switch into another section).
							 */
							return e;
						}
						
					} else {
						// this one is already after, so the one before was the "last before"
						return e - 1;
					}
				}
			}
			
			prevSectionLastEntryIndex = lastEntryIndex;
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
			lastRetainedSection = positionResults.get(lastRetainedEntryIndex).getSection();
			
			int previousLastIndex = lastEntryIndices.get(lastRetainedSection);
			if (lastRetainedEntryIndex < previousLastIndex) {
				// lost entries within the section - mark it incomplete
				markSectionCompleted(lastRetainedSection, false);
				
				// update with the new last entry index
				lastEntryIndices.put(lastRetainedSection, lastRetainedEntryIndex);
			}
		}
		
		List<SnapshotEntry> removeSubList = 
				positionResults.subList(lastRetainedEntryIndex + 1, positionResults.size());
		
		// analyze removed results to know how much to undo the prover
		for (SnapshotEntry resultEntry : removeSubList) {
			
			FileSection section = resultEntry.getSection();
			String resultPath = section.getFilePath();
			Integer undoOffset = fileUndoOffsets.get(resultPath);
			if (undoOffset == null) {
				// first undo offset for this file - mark it down
				fileUndoOffsets.put(resultPath, resultEntry.getPosition().getOffset());
			}
			
			switch (resultEntry.getType()) {
			case PARA: {
				/*
				 * For paragraphs, mark the first history index available in the
				 * "remove" zone - then undo through to (including) this
				 */
				if (undoThroughHistoryIndex < 0) {
					undoThroughHistoryIndex = ((ParaSnapshotEntry) resultEntry).getHistoryIndex();
				}
				break;
			}
			case PROOF: {
				/*
				 * For proofs, increment undo count for the given goal name -
				 * each proof steps means one "back" sent to Z/Eves for that
				 * particular goal
				 */
				ProofSnapshotEntry proofPos = (ProofSnapshotEntry) resultEntry;
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
	
	public interface ISnapshotEntry {
		
		public Position getPosition();
		
		public String getFilePath();
		
		public String getSectionName();
		
		public Term getSource();
		
		public Object getResult();
	}
	
	public interface IProofSnapshotEntry extends ISnapshotEntry {
		
		@Override
		public ZEvesOutput getResult();
		
		@Override
		public ProofCommand getSource();
		
		public String getGoalName();
		
		public int getStepIndex();
		
	}
	
	private static class SnapshotEntry implements ISnapshotEntry {
		
		private final FileSection section;
		private final Position pos;
		private final ResultType type;
		
		private final Term source;
		private final Object result;
		
		public SnapshotEntry(FileSection section, Position pos, ResultType type, Term source, Object result) {
			Assert.isNotNull(section, "File section must be indicated before update");
			this.section = section;
			this.pos = pos;
			this.type = type;
			this.source = source;
			this.result = result;
		}
		
		public FileSection getSection() {
			return section;
		}

		@Override
		public Position getPosition() {
			return pos;
		}

		public ResultType getType() {
			return type;
		}

		@Override
		public String getFilePath() {
			return getSection().getFilePath();
		}

		@Override
		public String getSectionName() {
			return getSection().getSectionName();
		}

		@Override
		public Term getSource() {
			return source;
		}

		@Override
		public Object getResult() {
			return result;
		}
	}
	
	private static class ParaSnapshotEntry extends SnapshotEntry {
	
		private final int historyIndex;

		public ParaSnapshotEntry(FileSection section, Position pos, int historyIndex, 
				Para source, Object result) {
			super(section, pos, ResultType.PARA, source, result);
			this.historyIndex = historyIndex;
		}

		public int getHistoryIndex() {
			return historyIndex;
		}
	}
	
	private static class ProofSnapshotEntry extends SnapshotEntry implements IProofSnapshotEntry {
		
		private final String goalName;
		private final int zEvesStepIndex;
		
		public ProofSnapshotEntry(FileSection section, Position pos, ResultType type,
				String goalName, int zEvesStepIndex, ProofCommand source, ZEvesOutput result) {
			super(section, pos, type, source, result);
			this.goalName = goalName;
			this.zEvesStepIndex = zEvesStepIndex;
		}

		@Override
		public String getGoalName() {
			return goalName;
		}

		@Override
		public int getStepIndex() {
			return zEvesStepIndex;
		}
		
		@Override
		public ZEvesOutput getResult() {
			return (ZEvesOutput) super.getResult();
		}

		@Override
		public ProofCommand getSource() {
			return (ProofCommand) super.getSource();
		}
	}
	
}

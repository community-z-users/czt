package net.sourceforge.czt.zeves.snapshot;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;

import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot.ResultType;

public class SnapshotUtil {

	public static Iterator<ISnapshotEntry> getBackwardsProofIterator(
			ISnapshotEntry entry, boolean includeErrors) {
		
		if (entry == null || !isProofEntry(entry)) {
			return Collections.<ISnapshotEntry>emptyList().iterator();
		}
		
		return new BackwardsProofIterator(entry, includeErrors);
	}
	
	public static ISnapshotEntry getPreviousProofEntry(ISnapshotEntry entry, boolean includeErrors) {
		
		if (entry == null || !isProofEntry(entry)) {
			return null;
		}
		
		return getPreviousProofEntry(entry, includeErrors, new HashSet<ISnapshotEntry>());
	}
	
	private static ISnapshotEntry getPreviousProofEntry(ISnapshotEntry entry, boolean includeErrors,
			Set<ISnapshotEntry> visited) {
		
		if (entry == null) {
			return null;
		}
		
		ISnapshotEntry previous = entry.getPreviousEntry();
		if (previous == null) {
			return null;
		}
		
		if (!isProofEntry(previous)) {
			return null;
		}
		
		String currentGoal = entry.getData().getGoalName();
		if (!currentGoal.equals(previous.getData().getGoalName())) {
			// different goal - not the same proof
			return null;
		}
		
		if (previous.getType() == ResultType.ERROR && !includeErrors) {
			// errors are not included, so continue on the previous recursively
			// first check on possible loops - if already visited, return previous
			if (visited.contains(entry)) {
				return entry;
			}
			
			visited.add(entry);
			
			return getPreviousProofEntry(previous, includeErrors, visited);
		}
		
		return previous;
	}
	
	private static boolean isProofEntry(ISnapshotEntry entry) {
		ResultType type = entry.getType();
		return (type == ResultType.PROOF || type == ResultType.GOAL || type == ResultType.ERROR)
				&& entry.getData().getGoalName() != null;
	}
	
	private static class BackwardsProofIterator implements Iterator<ISnapshotEntry> {

		private ISnapshotEntry currentEntry;
		private boolean includeErrors;
		
		public BackwardsProofIterator(ISnapshotEntry currentEntry, boolean includeErrors) {
			super();
			
			if (currentEntry == null) {
				throw new IllegalArgumentException();
			}
			
			if (!isProofEntry(currentEntry)) {
				throw new IllegalArgumentException();
			}
			
			this.currentEntry = currentEntry;
			this.includeErrors = includeErrors;
		}

		@Override
		public boolean hasNext() {
			return getPreviousProofEntry(currentEntry, includeErrors) != null;
		}

		@Override
		public ISnapshotEntry next() {
			ISnapshotEntry previous = getPreviousProofEntry(currentEntry, includeErrors);
			if (previous == null) {
				throw new NoSuchElementException();
			}
			
			currentEntry = previous;
			return currentEntry;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}
	
}

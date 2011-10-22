package net.sourceforge.czt.eclipse.zeves.core;

import java.util.ArrayList;
import java.util.EventObject;
import java.util.List;

import net.sourceforge.czt.eclipse.zeves.core.ZEvesSnapshot.ISnapshotEntry;

public class SnapshotChangedEvent extends EventObject {

	public enum SnapshotChangeType {
		ADD,
		REMOVE,
		CLEAR
	}
	
	private final SnapshotChangeType type;
	private final List<ISnapshotEntry> changedEntries;
	
	public SnapshotChangedEvent(Object source, SnapshotChangeType type, 
			List<? extends ISnapshotEntry> changedEntries) {
		super(source);
		
		this.type = type;
		
		// copy defensively
		this.changedEntries = new ArrayList<ISnapshotEntry>(changedEntries);
	}

	public SnapshotChangeType getType() {
		return type;
	}

	public List<ISnapshotEntry> getEntries() {
		return changedEntries;
	}

}

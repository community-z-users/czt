package net.sourceforge.czt.eclipse.zeves.ui.core;

import java.util.ArrayList;
import java.util.EventObject;
import java.util.List;

import net.sourceforge.czt.eclipse.zeves.ui.core.ZEvesSnapshot.ISnapshotEntry;

public class SnapshotChangedEvent extends EventObject {

  private static final long serialVersionUID = 4136840641946576490L;

  public enum SnapshotChangeType {
		ADD,
		REMOVE
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

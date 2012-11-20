package net.sourceforge.czt.zeves.snapshot;

import java.util.EventListener;

public interface ISnapshotChangedListener extends EventListener {

	public void snapshotChanged(SnapshotChangedEvent event);
	
}

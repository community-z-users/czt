package net.sourceforge.czt.eclipse.zeves.ui.core;

import java.util.EventListener;

public interface ISnapshotChangedListener extends EventListener {

	public void snapshotChanged(SnapshotChangedEvent event);
	
}

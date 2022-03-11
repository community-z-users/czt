package net.sourceforge.czt.zeves.snapshot;

import net.sourceforge.czt.text.Position;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot.ResultType;

/**
 * @author Andrius Velykis
 */
public interface ISnapshotEntry {
	
	public Position getPosition();
	
	public String getFilePath();
	
	public String getSectionName();
	
	public SnapshotData getData();
	
	public ResultType getType();
	
	public ISnapshotEntry getPreviousEntry();
}

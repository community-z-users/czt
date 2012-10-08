package net.sourceforge.czt.eclipse.zeves.ui.core;

import net.sourceforge.czt.eclipse.ui.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;

public class ZEvesBackCommand extends AbstractUndoCommand {
	
	public ZEvesBackCommand(ZEditor editor) {
		super(editor);
	}
	
	@Override
	protected int getUndoOffset(String filePath) {
        // undo through the last offset - this will undo the last result
		ZEvesSnapshot snapshot = ZEvesUIPlugin.getZEves().getSnapshot();
		return snapshot.getLastPositionOffset(filePath);
	}
	
}
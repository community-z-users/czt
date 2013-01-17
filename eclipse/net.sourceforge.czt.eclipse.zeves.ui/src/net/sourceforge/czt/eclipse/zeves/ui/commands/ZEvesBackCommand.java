package net.sourceforge.czt.eclipse.zeves.ui.commands;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;

public class ZEvesBackCommand extends AbstractUndoCommand {
	
	public ZEvesBackCommand(IZEditor editor) {
		super(editor);
	}
	
	@Override
	protected int getUndoOffset(String filePath) {
        // undo through the last offset - this will undo the last result
		ZEvesSnapshot snapshot = ZEvesCore.getSnapshot();
		return snapshot.getLastPositionOffset(filePath);
	}
	
}

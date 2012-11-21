package net.sourceforge.czt.eclipse.zeves.ui.commands;

import net.sourceforge.czt.eclipse.zeves.core.IZEvesExecCommand;

import org.eclipse.ui.texteditor.ITextEditor;

public class ZEvesUndoCommand extends AbstractUndoCommand {
	
	private final int offset;
	
	public ZEvesUndoCommand(ITextEditor editor, int offset) {
		super(editor);
		this.offset = offset;
	}
	
	@Override
	public boolean canMerge(IZEvesExecCommand command) {
		if (command instanceof ZEvesUndoCommand) {
			return getEditor() == ((ZEvesUndoCommand) command).getEditor();
		}
		
		return false;
	}
	
	@Override
	public IZEvesExecCommand merge(IZEvesExecCommand command) {
		if (offset <= ((ZEvesUndoCommand) command).offset) {
			return this;
		} else {
			return command;
		}
	}

	@Override
	protected int getUndoOffset(String filePath) {
		return offset;
	}
	
}
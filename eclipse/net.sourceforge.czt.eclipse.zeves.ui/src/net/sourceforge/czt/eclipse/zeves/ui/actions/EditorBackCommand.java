package net.sourceforge.czt.eclipse.zeves.ui.actions;

import java.util.List;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ResourceUtil;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ZEvesBackCommand;
import net.sourceforge.czt.text.Position;
import net.sourceforge.czt.zeves.snapshot.ISnapshotEntry;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.handlers.HandlerUtil;


public class EditorBackCommand extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		final IZEditor editor = (IZEditor) HandlerUtil.getActiveEditor(event);
		
		ZEves prover = ZEvesCore.getZEves();
		if (!prover.isRunning()) {
			MessageDialog.openInformation(editor.getSite().getShell(), "Prover Not Running",
					"The Z/EVES prover is not running.");
			return null;
		}
		
		prover.getExecutor().addCommand(new ZEvesBackCommand(editor) {
			@Override
			protected void completed(IStatus result) {
				updateCaretOnBack(editor);
			}
		});
		
		return null;
	}
	
	public static void updateCaretOnBack(final IZEditor editor) {
		IResource resource = ZEditorUtil.getEditorResource(editor);
		if (resource == null) {
			return;
		}
		
		String filePath = ResourceUtil.getPath(resource);
		ZEvesSnapshot snapshot = ZEvesCore.getSnapshot();
		int lastOffset = snapshot.getLastPositionOffset(filePath);
		
		if (lastOffset >= 0) {
			Position peekPos = lastOffset > 0 ? new Position(lastOffset - 1, 1) : new Position(lastOffset);
			List<ISnapshotEntry> entries = snapshot.getEntries(filePath, peekPos);
			if (entries.size() > 0) {
				// get the last one and move the cursor to its start
				Position pos = entries.get(entries.size() - 1).getPosition();
				if (pos.getLength() > 0) {
					// take offset + 1
					lastOffset = pos.getOffset() + 1;
				}
			}
		}
		
		final int caretOffset = lastOffset;
		
		// set caret position in display thread
		PlatformUtil.runInUI(new Runnable() {
			@Override
			public void run() {
				ZEditorUtil.setCaretPosition(editor, caretOffset);
				editor.getSite().getPage().activate(editor);
			}
		});
	}
}

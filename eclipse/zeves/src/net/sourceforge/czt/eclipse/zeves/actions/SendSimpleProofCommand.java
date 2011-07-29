package net.sourceforge.czt.eclipse.zeves.actions;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.editors.parser.ZCompiler;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.util.CztUI;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.editor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.views.IZEvesElement;
import net.sourceforge.czt.eclipse.zeves.views.ZEvesOutputView;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.ProofResultElement;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.ISafeRunnable;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;

public class SendSimpleProofCommand extends AbstractHandler {

	private static final String PARAM_CMD_NAME = ZEvesPlugin.PLUGIN_ID + ".proof.simpleCmd.name";
	
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		String proofCommand = event.getParameter(PARAM_CMD_NAME);
		
		IWorkbenchPart part = HandlerUtil.getActivePart(event);
		if (!(part instanceof ZEvesOutputView)) {
			System.out.println("Not output view");
			return null;
		}
		
		Shell shell = HandlerUtil.getActiveShell(event);
		
		ZEvesOutputView outputView = (ZEvesOutputView) part;
		IZEvesElement currentInput = outputView.getCurrentInput();
		if (!(currentInput instanceof ProofResultElement)) {
			MessageDialog.openError(shell, "Invalid element", "Proof commands must be executed on proof goals.");
			return null;
		}
		
		ProofResultElement proofResult = (ProofResultElement) currentInput;
		
		// insert the command after the proof result position into the editor
		Position pos = proofResult.getPosition();
		final ZEditor editor = proofResult.getEditor();
		IDocument document = ZEditorUtil.getDocument(editor);
		
		if (pos == null || document == null) {
			// invalid
			return null;
		}
		
		// TODO reference proof separator somewhere?
		String separator = ";\n";
		String cmdWithSep;
		int addOffset;
		if (proofResult.isGoal()) {
			cmdWithSep = proofCommand + separator;
			addOffset = 1;
		} else {
			cmdWithSep = separator + proofCommand;
			addOffset = separator.length() + 1;
		}
		
		int posEnd = pos.getOffset() + pos.getLength();
		try {
			document.replace(posEnd, 0, cmdWithSep);
		} catch (BadLocationException e) {
			ZEvesPlugin.getDefault().log(e);
		}
		
		final ParsedData[] data = new ParsedData[1];
		SafeRunner.run(new ISafeRunnable()
        {
          public void run()
          {

            ZCompiler compiler = ZCompiler.getInstance();
            if (compiler != null) {
              compiler.setEditor(editor);
              data[0] = compiler.parse();
            }
          }

          public void handleException(Throwable ex)
          {
            IStatus status = new Status(IStatus.ERROR, CztUI.ID_PLUGIN,
                IStatus.OK, "Error in CZT during reconcile", ex); //$NON-NLS-1$
            CZTPlugin.getDefault().getLog().log(status);
          }
        });
		
		SubmitToPointCommand.submitToOffset(editor, data[0], posEnd + addOffset);
		
		return null;
	}

}

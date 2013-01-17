package net.sourceforge.czt.eclipse.zeves.ui.commands;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesExecContext;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesExecVisitor;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;

public class ZEvesSubmitCommand extends AbstractSubmitCommand {
	
	private final int offset;
	
	public ZEvesSubmitCommand(IZEditor editor, int offset) {
		super(editor);
		this.offset = offset;
	}

	@Override
	protected int getStartOffset(int submittedOffsetInFile) {

		if (offset > submittedOffsetInFile) {
			// when submitting, go from the next symbol than last submitted
			return submittedOffsetInFile + 1;
		}
		
		// undoing - start from offset
		return offset;
	}

	@Override
	protected int getEndOffset(IDocument document) {
		// submit to the offset
		return offset;
	}

	@Override
	protected IStatus submitSpec(IProgressMonitor monitor, ZEvesApi zEvesApi,
	      ZEvesExecContext execContext, ZEvesSnapshot snapshot, 
	      String file, int start, int end,
	      SectionManager sectInfo, Spec specification) {

		ZEvesExecVisitor zEvesExec = new ZEvesExecVisitor(
				zEvesApi, snapshot, execContext, file, sectInfo, 
				start, end, monitor);

		// wrap into try-finally, because OperationCanceledExpression
		// may be thrown from inside
		long time = System.currentTimeMillis();
		try {
			zEvesExec.execSpec(specification);
		} finally {
			zEvesExec.finish();
			time = (System.currentTimeMillis() - time) / 1000;
			System.out.println("Proof execution time = " + time);
		}

		return Status.OK_STATUS;
	}
}
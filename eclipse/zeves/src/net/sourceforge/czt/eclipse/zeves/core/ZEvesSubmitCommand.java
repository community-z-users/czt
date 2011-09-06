package net.sourceforge.czt.eclipse.zeves.core;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.parser.IPositionProvider;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.zeves.ZEvesApi;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;

public class ZEvesSubmitCommand extends AbstractSubmitCommand {
	
	private final int offset;
	
	public ZEvesSubmitCommand(ZEditor editor, int offset) {
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
	protected IStatus submitSpec(IProgressMonitor monitor, ZEvesApi zEvesApi, String filePath,
			ZEvesSnapshot snapshot, int start, int end, IPositionProvider<Term> posProvider,
			ZEvesMarkers markers, SectionManager sectInfo, Spec specification) {

		ZEvesExecVisitor zEvesExec = new ZEvesExecVisitor(
				zEvesApi, snapshot, markers, filePath, posProvider, sectInfo, 
				start, end, monitor);

		// wrap into try-finally, because OperationCanceledExpression
		// may be thrown from inside
		try {
			zEvesExec.execSpec(specification);
		} finally {
			zEvesExec.finish();
		}

		return Status.OK_STATUS;
	}
}
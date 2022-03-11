package net.sourceforge.czt.eclipse.zeves.ui.commands;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesExecContext;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesExecVisitor;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.text.Position;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;


public class ZEvesSubmitNextCommand extends AbstractSubmitCommand {
	
	public ZEvesSubmitNextCommand(IZEditor editor) {
		super(editor);
	}

	@Override
	protected int getStartOffset(int submittedOffsetInFile) {
        // when submitting, go from the next symbol than last submitted
        // if nothing has been submitted, start from 0 (-1 + 1 = 0)
		return submittedOffsetInFile + 1;
	}

	@Override
	protected int getEndOffset(IDocument document) {
		// submit to the end of the document
		return document.getLength();
	}

	@Override
	protected IStatus submitSpec(IProgressMonitor monitor, ZEvesApi zEvesApi,
            ZEvesExecContext execContext, ZEvesSnapshot snapshot, 
            String file, int start, int end,
            SectionManager sectInfo, Spec specification) {
		
		ZEvesExecVisitor zEvesExec = new ZEvesExecVisitor(
				zEvesApi, snapshot, execContext, file, sectInfo, 
				start, end, monitor) {

					@Override
					protected void visitZSectHead(ZSect term, Position position) {
						super.visitZSectHead(term, position);
						throw foundFirst();
					}

					@Override
					protected void visitZSectEnd(ZSect term, Position position) {
						super.visitZSectEnd(term, position);
						// do not stop at section end
//						throw foundFirst();
					}

					@Override
					protected void visitPara(Para term, Position pos) {
						super.visitPara(term, pos);
						throw foundFirst();
					}

					@Override
					protected void visitProofScriptHead(ProofScript term, Position pos) {
						super.visitProofScriptHead(term, pos);
						throw foundFirst();
					}

					@Override
					protected void visitProofScriptEnd(ProofScript term, Position pos) {
						super.visitProofScriptEnd(term, pos);
						// do not stop at proof script end
//						throw foundFirst();
					}

					@Override
					protected void visitProofCommand(ProofScript script, ProofCommand command,
							Position pos) {
						super.visitProofCommand(script, command, pos);
						throw foundFirst();
					}
					
					private RuntimeException foundFirst() {
						return new ExecutedFirstException();
					}
		};

		// wrap into try-finally, because OperationCanceledExpression
		// may be thrown from inside
		try {
			zEvesExec.execSpec(specification);
		} catch (ExecutedFirstException e) {
			// found first - ignore the exception
			// the exception is used to return from the algorithm
		} finally {
			zEvesExec.finish();
		}

		return Status.OK_STATUS;
	}
	
	private static class ExecutedFirstException extends RuntimeException {

		private static final long serialVersionUID = 5233807376445703371L;
	}

}
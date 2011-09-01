package net.sourceforge.czt.eclipse.zeves.core;

import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.ui.texteditor.ITextEditor;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;

/**
 * An executor for Z/Eves commands. The linear executor maintains a queue of
 * commands that affect Z/Eves snapshot and the prover. The queue is executed
 * sequentially by a single Job, so it is ensured that the snapshot or prover are
 * not accessed by several threads simultaneously.
 * 
 * @author Andrius Velykis
 */
public class ZEvesLinearExecutor {

	private Queue<ZEvesExecCommand> commands = new ConcurrentLinkedQueue<ZEvesExecCommand>();
	
	private final Job execJob = new Job("Sending to Z/Eves") {
		
		@Override
		protected IStatus run(IProgressMonitor monitor) {
			
			ZEvesExecCommand command = getNextCommand();
			if (command == null) {
				// nothing to execute
				return Status.OK_STATUS;
			}
			
			return command.execute(monitor);
		}
	};
	
	public ZEvesLinearExecutor() {
		
		execJob.addJobChangeListener(new JobChangeAdapter() {
			@Override
			public void done(IJobChangeEvent event) {
				if (!commands.isEmpty()) {
					// there are outstanding commands, reschedule the job to consume them
					execJob.schedule();
				}
			}
		});
		
	}
	
	public void addCommand(ZEvesExecCommand command) {
		Assert.isNotNull(command);
		
		commands.add(command);
		
		// upon adding the command, schedule the job to execute it
		execJob.schedule();
	}
	
	private ZEvesExecCommand getNextCommand() {
		
		ZEvesExecCommand first = commands.poll();
		if (first == null) {
			return null;
		}
		
		// try merging commands
		ZEvesExecCommand command;
		while ((command = commands.peek()) != null) {
			if (first.canMerge(command)) {
				// merge the commands, so remove from the queue
				commands.poll();
				first = first.merge(command);
			} else {
				break;
			}
		}
		
		return first;
	}
	
}

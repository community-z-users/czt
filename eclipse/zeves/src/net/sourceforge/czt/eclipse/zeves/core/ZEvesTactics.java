package net.sourceforge.czt.eclipse.zeves.core;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.zeves.ast.NormalizationCommand;
import net.sourceforge.czt.zeves.ast.NormalizationKind;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.RewriteKind;
import net.sourceforge.czt.zeves.ast.RewritePower;
import net.sourceforge.czt.zeves.ast.SimplificationCommand;
import net.sourceforge.czt.zeves.ast.SubstitutionKind;
import net.sourceforge.czt.zeves.ast.WithCommand;
import net.sourceforge.czt.zeves.ast.WrappedCommand;
import net.sourceforge.czt.zeves.util.Factory;
import net.sourceforge.czt.zeves.visitor.ProofCommandVisitor;

/**
 * A support for Z/Eves tactic commands, which can be defined as a sequence (or loop)
 * of existing Z/Eves commands. Two such commands are encoded in Z/Eves, namely
 * prove-by-rewrite and prove-by-reduce. The tactics allow sending the commands
 * from the tool and thus keeping full trace eventually.
 * 
 * @author Andrius Velykis
 */
public class ZEvesTactics {

    public static CommandSequence getTacticCommands(ProofCommand tactic, 
    		ProofCommandVisitor<String> printer) {
    	
    	// unwrap the actual commands, if it has any modifiers,
    	// e.g. with normalization .. , or with enabled (..) ..
    	ProofCommand noModCommand = getCommandNoModifiers(tactic);
    	
    	// check for proof commands (e.g. prove-by-rewrite, prove-by-reduce)
    	if (noModCommand instanceof SimplificationCommand) {
    		SimplificationCommand simplCommand = (SimplificationCommand) noModCommand;
    		if (simplCommand.getPower() == RewritePower.Prove) {
    			return createProveSeq(tactic, noModCommand, simplCommand.getKind(), printer);
    		}
    	}
    	
    	// no sequences - just wrap the command into singleton sequence
    	return CommandSequence.createSingle(printCommand(tactic, printer));
    }
    
    private static String printCommand(ProofCommand command, ProofCommandVisitor<String> printer) {
    	return command.accept(printer);
    }
    
    private static ProofCommand getCommandNoModifiers(ProofCommand command) {
    	if (command instanceof WithCommand) {
    		return getCommandNoModifiers(((WithCommand) command).getProofCommand());
    	}
    	
    	if (command instanceof NormalizationCommand) {
    		NormalizationCommand normCmd = (NormalizationCommand) command;
    		if (normCmd.getKind() == NormalizationKind.Command) {
    			return getCommandNoModifiers(normCmd.getProofCommand());
    		}
    	}
    	
    	// no modifiers already
    	return command;
    }
    
	private static CommandSequence createProveSeq(ProofCommand fullCmd, ProofCommand proveCmd,
			RewriteKind rewriteCmdKind, ProofCommandVisitor<String> printer) {

		List<String> loopCommands = new ArrayList<String>();
		
		Factory zEvesFactory = new Factory();
		
		// keep adding to sequence, by replacing the end-command with a subsequent command
		
		ProofCommand prenexCmd = zEvesFactory.createQuantifiersCommand();
		fullCmd = addToSequence(loopCommands, fullCmd, proveCmd, prenexCmd, printer);
		
		ProofCommand rearrangeCmd = zEvesFactory.createNormalizationCommand(BigInteger.ZERO, null,
				NormalizationKind.Rearrange);
		fullCmd = addToSequence(loopCommands, fullCmd, prenexCmd, rearrangeCmd, printer);
		
		ProofCommand eqSubsCmd = zEvesFactory.createSubstitutionCommand(BigInteger.ZERO, null,
				null, null, null, SubstitutionKind.Equality);
		fullCmd = addToSequence(loopCommands, fullCmd, rearrangeCmd, eqSubsCmd, printer);
		
		ProofCommand rewriteCmd = zEvesFactory.createSimplificationCommand(BigInteger.ZERO,
				rewriteCmdKind, RewritePower.None);
		fullCmd = addToSequence(loopCommands, fullCmd, eqSubsCmd, rewriteCmd, printer);
		
		// restore original prove command in the fullCmd
		replaceCommand(fullCmd, rewriteCmd, proveCmd);
		
		// create a loop that would stop if last command (rewrite) has no effect
		return CommandSequence.createEndLoop(loopCommands);
	}

	private static ProofCommand addToSequence(List<String> loopCommands, ProofCommand fullCmd,
			ProofCommand proveCmd, ProofCommand prenexCmd, ProofCommandVisitor<String> printer) {
		
		ProofCommand newFullCmd = replaceCommand(fullCmd, proveCmd, prenexCmd);
		loopCommands.add(printCommand(newFullCmd, printer));
		return newFullCmd;
	}
	
	
	private static ProofCommand replaceCommand(ProofCommand fullCmd, ProofCommand targetCmd,
			ProofCommand newCmd) {

		if (fullCmd == targetCmd) {
			return newCmd;
		}
		
		if (fullCmd instanceof WrappedCommand) {
			WrappedCommand wrappedCmd = (WrappedCommand) fullCmd;
			ProofCommand replaced = replaceCommand(wrappedCmd.getProofCommand(), targetCmd, newCmd);
			if (wrappedCmd.getProofCommand() != replaced) {
				wrappedCmd.setProofCommand(replaced);
			}
			
			return wrappedCmd;
		}
		
		// it should be either wrapped, or replaced command
		throw new IllegalArgumentException("Unexpected command in replace: " + fullCmd);
	}
	
	/**
	 * A wrapper for a sequence of Z/Eves proof commands. A flag whether the
	 * sequence should loop is also supported.
	 * 
	 * @author Andrius Velykis
	 */
	public static class CommandSequence {
		
		private final List<IgnorableCommand> commands = new ArrayList<IgnorableCommand>();
		private final boolean loopCommands;
		
		public CommandSequence(boolean loop) {
			super();
			this.loopCommands = loop;
		}
		
		public boolean isLoopCommands() {
			return loopCommands;
		}
		
		public void addCommand(String command, boolean stopOnNoEffect) {
			commands.add(new IgnorableCommand(command, stopOnNoEffect));
		}
		
		public List<IgnorableCommand> getCommands() {
			return Collections.unmodifiableList(commands);
		}
		
		public static CommandSequence createEndLoop(List<String> commands) {
			
			CommandSequence seq = new CommandSequence(true);
			
			for (Iterator<String> it = commands.iterator(); it.hasNext(); ) {
				String cmd = it.next();
				boolean isLast = !it.hasNext();
				seq.addCommand(cmd, isLast);
			}
			
			return seq;
		}
		
		public static CommandSequence createSingle(String command) {
			CommandSequence seq = new CommandSequence(false);
			seq.addCommand(command, true);
			return seq;
		}
	}
	
	/**
	 * A pair of Z/Eves command string (converted to XML representation)
	 * and whether it should stop if not effective. 
	 * 
	 * @author Andrius Velykis
	 */
	public static class IgnorableCommand {
		
		private final String command;
		private final boolean stopOnNoEffect;
		
		public IgnorableCommand(String command, boolean stopOnNoEffect) {
			super();
			this.command = command;
			this.stopOnNoEffect = stopOnNoEffect;
		}

		public String getCommand() {
			return command;
		}

		public boolean isStopOnNoEffect() {
			return stopOnNoEffect;
		}
	}
	
}

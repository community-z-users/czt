package net.sourceforge.czt.zeves.proof;

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
 * A support for Z/EVES tactic commands, which can be defined as a sequence (or loop)
 * of existing Z/EVES commands. Two such commands are encoded in Z/EVES, namely
 * prove-by-rewrite and prove-by-reduce. The tactics allow sending the commands
 * from the tool and thus keeping full trace eventually.
 * 
 * @author Andrius Velykis
 */
public class ZEvesTactics {
	
	/**
	 * Z/EVES default loop count for prove by rewrite/prove by reduce commands.
	 */
	private static final int PROVE_LOOP_COUNT = 11;

    public static CommandSequence getTacticCommands(ProofCommand tactic, 
    		ProofCommandVisitor<String> printer) {
    	
    	// unwrap the actual commands, if it has any modifiers,
    	// e.g. with normalization .. , or with enabled (..) ..
    	ProofCommand noModCommand = getCommandNoModifiers(tactic);
    	
    	// check for proof commands (e.g. prove-by-rewrite, prove-by-reduce)
    	if (noModCommand instanceof SimplificationCommand) {
    		SimplificationCommand simplCommand = (SimplificationCommand) noModCommand;
    		if (simplCommand.getRewritePower() == RewritePower.Prove) {
    			return createProveSeq(tactic, noModCommand, simplCommand.getRewriteKind(), printer);
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
    		if (normCmd.getNormalizationKind() == NormalizationKind.Command) {
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
		return CommandSequence.createEndLoop(PROVE_LOOP_COUNT, loopCommands);
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
	 * A wrapper for a sequence of Z/EVES proof commands. A flag whether the
	 * sequence should loop is also supported.
	 * 
	 * @author Andrius Velykis
	 */
	public static class CommandSequence {
		
		/**
		 * A predefined constant to indicate unlimited loop of commands
		 */
		public static final int UNLIMITED = -1;
		
		private final List<IgnorableCommand> commands = new ArrayList<IgnorableCommand>();
		private final int loopCount;
		
		public CommandSequence(int loopCount) {
			super();
			this.loopCount = loopCount;
		}
		
		public int getLoopCount() {
			return loopCount;
		}
		
		public void addCommand(String command, boolean stopOnNoEffect, boolean stopOnError) {
			commands.add(new IgnorableCommand(command, stopOnNoEffect, stopOnError));
		}
		
		public List<IgnorableCommand> getCommands() {
			return Collections.unmodifiableList(commands);
		}
		
		public static CommandSequence createEndLoop(int loopCount, List<String> commands) {
			
			CommandSequence seq = new CommandSequence(loopCount);
			
			for (Iterator<String> it = commands.iterator(); it.hasNext(); ) {
				String cmd = it.next();
				boolean isLast = !it.hasNext();
				/*
				 * Ignores errors and no-effect for all commands except the last
				 * one.
				 */
				seq.addCommand(cmd, isLast, isLast);
			}
			
			return seq;
		}
		
		public static CommandSequence createSingle(String command) {
			CommandSequence seq = new CommandSequence(1);
			seq.addCommand(command, true, true);
			return seq;
		}
	}
	
	/**
	 * A pair of Z/EVES command string (converted to XML representation)
	 * and whether it should stop if not effective. 
	 * 
	 * @author Andrius Velykis
	 */
	public static class IgnorableCommand {
		
		private final String command;
		private final boolean stopOnNoEffect;
		private final boolean stopOnError;
		
		public IgnorableCommand(String command, boolean stopOnNoEffect, boolean stopOnError) {
			super();
			this.command = command;
			this.stopOnNoEffect = stopOnNoEffect;
			this.stopOnError = stopOnError;
		}

		public String getCommand() {
			return command;
		}

		public boolean isStopOnNoEffect() {
			return stopOnNoEffect;
		}
		
		public boolean isStopOnError() {
			return stopOnError;
		}
	}
	
}

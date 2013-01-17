package net.sourceforge.czt.eclipse.zeves.core;

import java.util.List;

import org.eclipse.core.runtime.Assert;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.eclipse.core.document.IPositionProvider;
import net.sourceforge.czt.text.Position;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NarrSect;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NarrSectVisitor;
import net.sourceforge.czt.z.visitor.ParaVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zeves.ZEvesIncompatibleASTException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofCommandList;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.visitor.ProofCommandVisitor;
import net.sourceforge.czt.zeves.visitor.ProofScriptVisitor;

/**
 * Special visitor class to traverse top-level Z terms based on their positions
 * in the specification.
 */
public class ZEvesPosVisitor implements 
        TermVisitor<Object>, SpecVisitor<Object>, ZSectVisitor<Object>, ParaVisitor<Object>, 
        NarrParaVisitor<Object>, LatexMarkupParaVisitor<Object>, UnparsedParaVisitor<Object>,
        ProofScriptVisitor<Object>, ProofCommandVisitor<Object>, NarrSectVisitor<Object> {
	
	private final IPositionProvider<? super Term> posProvider;
	private final int startOffset;
	private final int length;
	
	private ZSect currentSect = null;
	private ProofScript currentScript = null;
	
    public ZEvesPosVisitor(IPositionProvider<? super Term> posProvider, int startOffset, int endOffset) {
		super();
		
		Assert.isLegal(startOffset <= endOffset);
		
		this.posProvider = posProvider;
		this.startOffset = startOffset;
		this.length = endOffset - startOffset;
	}
    
    protected boolean includePos(Position pos) {
    	return includePos(pos, startOffset, length);
    }
    
    public static boolean includePos(Position pos, int rangeOffset, int rangeLength) {
    	
    	if (pos == null) {
    		// no position?
    		return false;
    	}
    	
    	return pos.overlapsWith(rangeOffset, rangeLength);
    }

	/**
     * Throws an exception for unexpected items.
     */
    @Override
	public Object visitTerm(Term term) {
        throw new ZEvesIncompatibleASTException("term", term);
    }
    
    @Override
	public Object visitNarrSect(NarrSect term) {
		// ignore - comments, do not send to Z/EVES
		return null;
	}

	@Override
	public Object visitZSect(ZSect term) {
    	
    	Position pos = getPosition(term);
    	if (!includePos(pos)) {
    		return null;
    	}
    	
    	this.currentSect = term;
    	
    	/*
		 * section begin/end cases are special, we need to investigate
		 * locations of its paragraphs to know whether to send begin/end
		 * commands. E.g., if start offset is after the first paragraph
		 * start, the "begin section" is not included and therefore command
		 * should not be executed
		 */
    	ZParaList paraList = term.getZParaList();
    	Position sectDeclPos = getHeadPosition(term, paraList);
    	if (includePos(sectDeclPos)) {
    		visitZSectHead(term, sectDeclPos);
    	}
    	
    	// allow to act once for the section before submitting paragraphs
    	beforeZSectParas(term, pos);
    	
    	boolean includedPara = false;
    	
		for (Para p : paraList) {
			
			if (p instanceof LatexMarkupPara) {
				// a special case - Latex Markup Paragraph is always
				// at the start of the section and does not have a position.
				// It still should be visited if needed
				p.accept(this);
				
				// do not do anything else
				continue;
			}
        	
			Position pPos = getPosition(p);
			if (pPos == null) {
				continue;
			}
			
			if (!includePos(pPos)) {
				
				if (includedPara) {
	        		// first not-included paragraph after an included one, break
					break;
				}
				
				// skip this one
				continue;
			}
        	
        	includedPara = true;
            p.accept(this);
        }
		
		Position sectEndPos = getEndPosition(term, paraList);
		if (includePos(sectEndPos)) {
			visitZSectEnd(term, sectEndPos);
		}
        
        return null;
    }
	
	protected final ZSect getCurrentSect() {
		return currentSect;
	}
	
	protected final String getCurrentSectionName() {
		if (currentSect == null) {
			return null;
		}
		
		return currentSect.getName();
	}
    
    protected void visitZSectHead(ZSect term, Position position) {
    	// do nothing by default
    }
    
	protected void beforeZSectParas(ZSect term, Position pos) {
		// do nothing by default
	}
    
    protected void visitZSectEnd(ZSect term, Position position) {
    	// do nothing by default
    }
    
    protected Position getPosition(Term term) {
    	return posProvider.getPosition(term);
    }

    /**
	 * Translates the all sections within this specification following the
	 * protocol for ZSect terms.
	 */
    @Override
	public Object visitSpec(Spec term) {
    	
        for(Sect sect : term.getSect()) {
            sect.accept(this);
        }
        
        return null;
    }
    
    @Override
	public Object visitPara(Para term) {
    	
    	Position pos = getPosition(term);
    	
    	if (!includePos(pos)) {
    		return null;
    	}

    	visitPara(term, pos);
    	return null;
	}
    
    protected void visitPara(Para term, Position position) {
    	// do nothing by default
    }
    
	@Override
	public Object visitUnparsedPara(UnparsedPara term) {
		// ignore - comments, do not send to Z/EVES
		return null;
	}

	@Override
	public Object visitLatexMarkupPara(LatexMarkupPara term) {
		// ignore - comments, do not send to Z/EVES
		return null;
	}

	@Override
	public Object visitNarrPara(NarrPara term) {
		// ignore - comments, do not send to Z/EVES
		return null;
	}
	
	@Override
	public Object visitProofScript(ProofScript term) {
		
    	Position pos = getPosition(term);
    	if (!includePos(pos)) {
    		return null;
    	}
    	
    	/*
		 * proof script begin/end cases are special, we need to investigate
		 * locations of its commands to know whether to send begin/end
		 * commands. E.g., if start offset is after the first command
		 * start, the "begin proof" is not included and therefore command
		 * should not be executed
		 */
    	ProofCommandList cmdList = term.getProofCommandList();
    	Position scriptHeadPos = getHeadPosition(term, cmdList);
    	if (includePos(scriptHeadPos)) {
    		visitProofScriptHead(term, scriptHeadPos);
    	}
    	
    	this.currentScript = term;
    	
    	// allow to make the goal current in the prover
    	if (!beforeProofScriptCommands(term, pos)) {
    		return null;
    	}
    	
    	boolean includedCmd = false;
    	
		for (ProofCommand cmd : cmdList) {
        	
			Position cmdPos = getPosition(cmd);
			if (cmdPos == null) {
				continue;
			}
			
			if (!includePos(cmdPos)) {
				
				if (includedCmd) {
	        		// first not-included command after an included one, break
					break;
				}
				
				// skip this one
				continue;
			}
        	
        	includedCmd = true;
            cmd.accept(this);
        }
		
		this.currentScript = null;
		
		Position scriptEndPos = getEndPosition(term, cmdList);
		if (includePos(scriptEndPos)) {
			visitProofScriptEnd(term, scriptEndPos);
		}
        
        return null;
	}

	protected void visitProofScriptHead(ProofScript term, Position pos) {
		// do nothing by default
	}
	
	/**
	 * @param term
	 * @param pos
	 * @return false if proof script should not be evaluated, true otherwise
	 */
	protected boolean beforeProofScriptCommands(ProofScript term, Position pos) {
		// do nothing by default
		return true;
	}
	
	protected void visitProofScriptEnd(ProofScript term, Position pos) {
		// do nothing by default
	}
	
	@Override
	public Object visitProofCommand(ProofCommand term) {
		
    	Position pos = getPosition(term);
    	
    	if (!includePos(pos)) {
    		return null;
    	}
    	
    	visitProofCommand(currentScript, term, pos);
    	return null;
	}
	
	protected void visitProofCommand(ProofScript script, ProofCommand command, Position pos) {
		// do nothing by default
	}
    
    public void execSpec(Spec term) {
    	
    	if (term == null) {
    		return;
    	}
    	
        term.accept(this);
    }
    
    private Position getHeadPosition(Term term, List<? extends Term> elements) {
    	
    	Position tPos = getPosition(term);
    	if (tPos == null) {
    		return null;
    	}
    	
    	Position firstElemPos = null;
    	
    	for (Term elem : elements) {
    		firstElemPos = getPosition(elem);
    		
    		if (firstElemPos != null) {
    			break;
    		}
    	}
    	
    	if (firstElemPos == null) {
    		// no element positions - use the whole thing as term head position
    		return tPos;
    	}
    	
    	// term head position is everything up to the offset of first element
    	return new Position(tPos.getOffset(), firstElemPos.getOffset() - tPos.getOffset());
    }
    
    private Position getEndPosition(Term term, List<? extends Term> elements) {
    	
    	Position tPos = getPosition(term);
    	if (tPos == null) {
    		return null;
    	}
    	
    	Position lastElemPos = null;
    	
    	// go backwards
    	for (int index = elements.size() - 1; index >= 0; index--) {
    		Term elem = elements.get(index);
    		lastElemPos = getPosition(elem);
    		
    		if (lastElemPos != null) {
    			break;
    		}
    	}
    	
    	if (lastElemPos == null) {
    		// no element positions - use the whole thing as term end position
    		return tPos;
    	}
    	
    	// term end position is everything after end of last element
    	int lastParaEnd = lastElemPos.getEndOffset();
    	return Position.createStartEnd(lastParaEnd, tPos.getEndOffset());
    }
    
    protected int getEndOffset() {
    	return startOffset + length;
    }
    
}

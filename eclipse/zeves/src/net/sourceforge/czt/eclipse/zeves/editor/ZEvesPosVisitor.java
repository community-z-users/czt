package net.sourceforge.czt.eclipse.zeves.editor;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.UnparsedPara;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.ParaVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.UnparsedParaVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zeves.ZEvesIncompatibleASTException;

/**
 * Special visitor class to traverse top-level Z terms based on their positions
 * in the specification.
 */
public class ZEvesPosVisitor implements 
        TermVisitor<Object>, SpecVisitor<Object>, ZSectVisitor<Object>, ParaVisitor<Object>, 
        NarrParaVisitor<Object>, LatexMarkupParaVisitor<Object>, UnparsedParaVisitor<Object> {
	
	private final int startOffset;
	private final int endOffset;
	
	// TODO remove afterwards (when moving to parsed proof script)
	private final IDocument document;
	
    public ZEvesPosVisitor(int startOffset, int endOffset, IDocument document) {
		super();
		
		Assert.isLegal(startOffset <= endOffset);
		
		this.startOffset = startOffset;
		this.endOffset = endOffset;
		this.document = document;
	}
    
    protected boolean includePos(Position pos) {
    	
    	if (pos == null) {
    		// no position?
    		return false;
    	}
    	
    	// the position [start;end] must intersect [startOffset;endOffset]
    	return getEnd(pos) >= startOffset && pos.getOffset() <= endOffset;
    }

	/**
     * Throws an exception for unexpected items.
     */
    @Override
	public Object visitTerm(Term term) {
        throw new ZEvesIncompatibleASTException("term", term);
    }
    
    @Override
	public Object visitZSect(ZSect term) {
    	
    	Position pos = getPosition(term);
    	if (!includePos(pos)) {
    		return null;
    	}
    	
    	/*
		 * section begin/end cases are special, we need to investigate
		 * locations of its paragraphs to know whether to send begin/end
		 * commands. E.g., if start offset is after the first paragraph
		 * start, the "begin section" is not included and therefore command
		 * should not be executed
		 */
    	Position sectDeclPos = getSectHeadPosition(term);
    	if (includePos(sectDeclPos)) {
    		visitZSectHead(term, sectDeclPos);
    	}
    	
    	boolean includedPara = false;
    	
		for (Para p : term.getZParaList()) {
        	
			Position pPos = getPosition(p);
			if (pPos == null) {
				continue;
			}
			
			if (!includePos(pos)) {
				
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
		
		Position sectEndPos = getSectEndPosition(term);
		if (includePos(sectEndPos)) {
			visitZSectEnd(term, sectEndPos);
		}
        
        return null;
    }
    
    protected void visitZSectHead(ZSect term, Position position) {
    	// do nothing by default
    }
    
    protected void visitZSectEnd(ZSect term, Position position) {
    	// do nothing by default
    }
    
    protected static Position getPosition(Term term) {
    	return position(term.getAnn(LocAnn.class));
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
		// ignore - comments, do not send to Z/Eves
		return null;
	}

	@Override
	public Object visitLatexMarkupPara(LatexMarkupPara term) {
		// ignore - comments, do not send to Z/Eves
		return null;
	}

	@Override
	public Object visitNarrPara(NarrPara term) {
//		// ignore - comments, do not send to Z/Eves
//		return null;

	    // FIXME move to actual ProofScript after implementation
    	Position pos = getPosition(term);
    	if (!includePos(pos)) {
    		return null;
    	}
    	
		String zproofStart = "\\begin{zproof}[";
		
		String narrText = (String) term.getContent().get(0);
		
		int start = narrText.indexOf(zproofStart);
		if (start < 0) {
			return null;
		}
		
		// found start - get everything after
		narrText = narrText.substring(start);
		
		int end = narrText.indexOf("]");
		if (end < 0) {
			return null;
		}
		
		String theoremName = narrText.substring(zproofStart.length(), end).trim();
		
        // need to sanitize the name, e.g. Z/Eves MySchema\$domainCheck - need to remove the backslash
		theoremName = theoremName.replace("\\$", "$");
		
		System.out.println("Found proof for " + theoremName);
		
		int startOffset = pos.getOffset() + start;
		int endOffset = startOffset + end;
		
		Position scriptHeadPos = new Position(startOffset, end + 1);
		if (includePos(scriptHeadPos)) {
			visitProofScriptHead(theoremName, scriptHeadPos);
			// TODO ensure that current goal is this one before running into commands
		}
		
		try {
			int endLine = document.getLineOfOffset(endOffset);
			
	    	int index = 1;
	    	for (String proofCmd : getProofScript(theoremName)) {
	    		
	    		int cmdLine = endLine + index;
	    		
	    		Position cmdPos = new Position(document.getLineOffset(cmdLine), document.getLineLength(cmdLine));
	    		
	    		if (includePos(cmdPos)) {
	    			visitProofCommand(theoremName, index, proofCmd, cmdPos);
	    		}
	    		
	    		index++;
	    	}
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
		
		String zProofEnd = "\\end{zproof}";
		int scriptEndStart = narrText.indexOf(zProofEnd);
		if (scriptEndStart < 0) {
			return null;
		}
		
		Position scriptEndPos = new Position(startOffset + scriptEndStart, zProofEnd.length());
		if (includePos(scriptEndPos)) {
			visitProofScriptEnd(theoremName, scriptEndPos);
		}
		
		return null;
	}
	
	/**
	 * @param theoremName
	 * @param pos
	 * @return false if proof script should not be evaluated, true otherwise
	 */
	protected boolean visitProofScriptHead(String theoremName, Position pos) {
		// do nothing by default
		return true;
	}
	
	protected void visitProofScriptEnd(String theoremName, Position pos) {
		// do nothing by default
	}
	
	protected void visitProofCommand(String theoremName, int commandIndex, String command, Position pos) {
		// do nothing by default
	}
	
	protected List<String> getProofScript(String theoremName) {
		return Collections.emptyList();
	}
    
    public void execSpec(Spec term) {
    	
    	if (term == null) {
    		return;
    	}
    	
        term.accept(this);
    }
    
    private Position getSectHeadPosition(ZSect sect) {
    	
    	Position sPos = getPosition(sect);
    	if (sPos == null) {
    		return null;
    	}
    	
    	Position firstParaPos = null;
    	
    	for (Para para : sect.getZParaList()) {
    		firstParaPos = getPosition(para);
    		
    		if (firstParaPos != null) {
    			break;
    		}
    	}
    	
    	if (firstParaPos == null) {
    		// no paragraph positions - use the whole thing as section position
    		return sPos;
    	}
    	
    	// section declaration position is everything up to the offset of first paragraph
    	return new Position(sPos.getOffset(), firstParaPos.getOffset() - sPos.getOffset());
    }
    
    private Position getSectEndPosition(ZSect sect) {
    	
    	Position sPos = getPosition(sect);
    	if (sPos == null) {
    		return null;
    	}
    	
    	Position lastParaPos = null;
    	
    	// go backwards
    	List<Para> paraList = sect.getZParaList();
    	for (int index = paraList.size() - 1; index >= 0; index--) {
    		Para para = paraList.get(index);
    		lastParaPos = getPosition(para);
    		
    		if (lastParaPos != null) {
    			break;
    		}
    	}
    	
    	if (lastParaPos == null) {
    		// no paragraph positions - use the whole thing as section position
    		return sPos;
    	}
    	
    	// section end position is everything after end of last paragraph
    	int lastParaEnd = getEnd(lastParaPos);
    	return new Position(lastParaEnd, getEnd(sPos) - lastParaEnd);
    }
    
    public static Position position(LocAnn location) {
    	if (location == null) {
    		return null;
    	}
    	
    	return new Position(location.getStart().intValue(), location.getLength().intValue());
    }
    
    public static int getEnd(Position position) {
    	return position.getOffset() + position.getLength();
    }
    
    protected int getEndOffset() {
    	return endOffset;
    }
    
}

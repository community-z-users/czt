package net.sourceforge.czt.eclipse.ui.internal.outline;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.TransformerPara;
import net.sourceforge.czt.circus.visitor.ChannelDeclVisitor;
import net.sourceforge.czt.circus.visitor.ChannelParaVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetParaVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus.visitor.TransformerParaVisitor;
import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.ParsedData;
import net.sourceforge.czt.oz.ast.ClassPara;
import net.sourceforge.czt.oz.visitor.ClassParaVisitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.OptempParaVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;
import net.sourceforge.czt.zeves.util.ZEvesUtils;
import net.sourceforge.czt.zeves.visitor.ProofScriptVisitor;

import org.eclipse.jface.text.Position;

/**
 * A factory to create CztTreeNode item for a Term. The term's position and 
 * name position are also calculated. This is for top-level Para subclasses
 *  
 * @author Andrius Velykis
 */
public class CztTreeNodeFactory
{
  
  private final ParsedData parsedData;
  private final IZEditor editor;
  private final NamePositionVisitor namePosVisitor = new NamePositionVisitor();
  
  public CztTreeNodeFactory(IZEditor editor, ParsedData parsedData)
  {
    super();
    this.editor = editor;
    this.parsedData = parsedData;
  }
  
  private Position getNamePosition(Term term, Position def) {
    Position namePosition = term.accept(namePosVisitor);
    if (namePosition == null) {
      return def;
    }
    
    return namePosition;
  }

  public CztTreeNode createTreeNode(Term term)
  {
    if (term == null) {
      return null;
    }
    
    Position range = getPosition(term);
    Position namePosition = getNamePosition(term, range);
    
    return new CztTreeNode(editor, term, range, namePosition);
  }

  private Position getNamePosition(ZNameList nameList)
  {
    int start = -1;
    int end = -1;
    int index;
    for (index = 0; index < nameList.size(); index++) {
      if (start > -1)
        break;
      Position pos = getPosition(nameList.get(index));
      if (pos != null) {
        start = pos.getOffset();
        end = start + pos.getLength() - 1;
      }
    }
    if (start < 0)
      return null;
    for (; index < nameList.size(); index++) {
      Position pos = getPosition(nameList.get(index));
      if (pos != null)
        end = pos.getOffset() + pos.getLength() - 1;
    }

    if ((start > -1) && (end >= start))
      return new Position(start, end - start + 1);

    return null;
  }

  private Position getPosition(Term term)
  {
    if (term == null) {
      return null;
    }
    
    return parsedData.getTermPosition(term);
  }

  /**
   * A visitor to calculate position of term name
   * 
   * @author Andrius Velykis
   */
  private class NamePositionVisitor
      implements
        TermVisitor<Position>,
        GivenParaVisitor<Position>,
        AxParaVisitor<Position>,
        FreeParaVisitor<Position>,
        ConjParaVisitor<Position>,
        OptempParaVisitor<Position>,
        ConstDeclVisitor<Position>,
        VarDeclVisitor<Position>,
        // Object-Z
        ClassParaVisitor<Position>,
        // Z/EVES
        ProofScriptVisitor<Position>,
        // Circus
        ChannelDeclVisitor<Position>,
        ChannelParaVisitor<Position>,
        ChannelSetParaVisitor<Position>,
        ProcessParaVisitor<Position>,
        TransformerParaVisitor<Position>
  		// Circus Time has no Para or Decl
  {
    
    @Override
    public Position visitTerm(Term zedObject)
    {
      // no name position by default
      return null;
    }

    @Override
    public Position visitGivenPara(GivenPara term)
    {
      return getNamePosition(term.getNames());
    }
    
    @Override
    public Position visitAxPara(AxPara term)
    {

      ZDeclList declList = term.getZSchText().getZDeclList();

      Position namePosition = null;

      for (Decl decl : declList) {

        if (decl instanceof ConstDecl) {
          namePosition = getPosition(((ConstDecl) decl).getZName());
        }
        else if (decl instanceof VarDecl) {
          namePosition = getNamePosition(((VarDecl) decl).getName());
        }

        if (namePosition != null) {
          return namePosition;
        }
      }

      return null;
    }

    @Override
    public Position visitFreePara(FreePara term)
    {
      ZFreetypeList list = (ZFreetypeList) term.getFreetypeList();

      for (Freetype type : list) {
        Position namePosition = getPosition(type.getZName());

        if (namePosition != null) {
          return namePosition;
        }
      }
      return null;
    }

    @Override
    public Position visitConjPara(ConjPara term)
    {
      // check for label annotation
      ZEvesLabel l = ZEvesUtils.getLabel(term);
      if (l != null) {
        Position pos = getPosition(l.getName());
        if (pos != null) {
          return pos;
        }
      }
      
      return getNamePosition(term.getZNameList());
    }

    @Override
    public Position visitOptempPara(OptempPara term)
    {
      for (Oper oper : term.getOper()) {
        Position namePosition = getPosition(oper);
        if (namePosition != null) {
          return namePosition;
        }
      }

      return null;
    }

    @Override
    public Position visitConstDecl(ConstDecl term)
    {
      return getPosition(term.getZName());
    }

    @Override
    public Position visitVarDecl(VarDecl term)
    {
      return getNamePosition(term.getName());
    }

    @Override
    public Position visitClassPara(ClassPara term)
    {
      return getPosition(term.getName());
    }
    
    // Z/EVES

    @Override
    public Position visitProofScript(ProofScript term)
    {
      return getPosition(term.getName());
    }
    
    // Circus

	@Override
	public Position visitTransformerPara(TransformerPara term) {
		return getPosition(term.getName());
	}

	@Override
	public Position visitProcessPara(ProcessPara term) {
		return getPosition(term.getName());
	}

	@Override
	public Position visitChannelSetPara(ChannelSetPara term) {
		return getPosition(term.getName());
	}

    @Override
    public Position visitChannelDecl(ChannelDecl term)
    {
      return getNamePosition(term.getZChannelNameList());
    }

	@Override
	public Position visitChannelPara(ChannelPara term) {
		ZDeclList declList = term.getZDeclList();
		Position namePosition = null;

	      for (Decl decl : declList) {
	    	  // not sure, but think only the ChannelDecl is needed. see Parser.xml for channelPara ::= production
	        //if (decl instanceof ConstDecl) {
	        //  namePosition = getPosition(((ConstDecl) decl).getZName());
	        //}
	        //else if (decl instanceof VarDecl) {
	        //  namePosition = getNamePosition(((VarDecl) decl).getName());
	        //}
	        //else 
	    	if (decl instanceof ChannelDecl) {
	          namePosition = getNamePosition(((ChannelDecl)decl).getZChannelNameList());
	        }

	        if (namePosition != null) {
	          return namePosition;
	        }
	      }

	      return null;
	}
  }

}

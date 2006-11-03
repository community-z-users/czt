
package net.sourceforge.czt.eclipse.editors.parser;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.outline.NodeNameVisitor;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZString;

/**
 * @author Chengdong Xu
 */
public class NameInfoResolver
{
  private static Visitor<String> getTypeNameVisitor_ = new NodeNameVisitor();
  private static final String ID_DELTAXI = "deltaxi"; // special ID for names starting with XI/DELTA
  private static final String DELTA = ZString.DELTA;
  private static final String XI = ZString.XI;
  
  public static List<NameInfo> resolve(Spec spec, SectionManager manager)
  {
    List<NameInfo> nameInfoList = new ArrayList<NameInfo>();
    if (spec != null) {
      for (Sect sect : spec.getSect()) {
        if (sect instanceof ZSect) {
          ZSect zSect = (ZSect) sect;
          nameInfoList.addAll(visitZSect(zSect, manager));
        }
      }
    }
    
    return nameInfoList;
  }
  
  /**
   * A utility method for retrieve the information for a ZName from a list of NameInfo
   * @param nameInfoList the list of name information
   * @param name the name to find
   * @return the NameInfo instance, if the specified name is found, or <i>null</i>; 
   */
  public static NameInfo findInfo(List<NameInfo> nameInfoList, ZName name)
  {
    if (name == null)
      return null;
    
    String id = name.getId();
    String word = name.getWord();
    if (id == null || word == null)
      return null;
    
//    System.out.println("ID: " + id);
//    System.out.println("WORD: " + word);
    
    // Check whether the word starts with DELTA/XI. In AST, the prefix is always a single
    // character (¦¤/¦®) for both LaTeX and Unicode mode.
    if (id.equals(ID_DELTAXI)) {
      while ((word != null) && (word.startsWith(DELTA) || word.startsWith(XI)))
      {
        word = word.substring(1);
        if (word != null) {
          for (NameInfo info :nameInfoList)
            if(!info.isLocal() && word.equals(info.getName().getWord()))
              return info;
        }
      }
    }
    else {
      for (NameInfo info :nameInfoList)
        if(id.equals(info.getName().getId()) && word.equals(info.getName().getWord()))
          return info;
    }
    
    return null;
  }

  private static List<NameInfo> visitZSect(ZSect zSect, SectionManager manager)
  {
    List<NameInfo> nameInfoList = new ArrayList<NameInfo>();
    String section = zSect.getName();

    try {
      SectTypeEnvAnn steAnn = (SectTypeEnvAnn) manager.get(new Key(section,
          SectTypeEnvAnn.class));
      if (steAnn != null) {
        for (NameSectTypeTriple triple : steAnn.getNameSectTypeTriple()) {
          ZName name = triple.getZName();
          String type = triple.getType().accept(getTypeNameVisitor_);
          nameInfoList.add(new NameInfo(name, section, type, false));
        }
      }
    } catch (CommandException e) {
      System.out.println("CommandException");
    }
    
    // add local variables
    nameInfoList.addAll((visitChildrenOfTerm(zSect, zSect.getName())));
    
    return nameInfoList;
  }

  private static List<NameInfo> visitTerm(Term term, String section)
  {
    List<NameInfo> triples = new ArrayList<NameInfo>();
    if (term != null) {
      if (term instanceof VarDecl) {
        String type = ((VarDecl) term).getExpr().accept(getTypeNameVisitor_);
        for (Name name : ((VarDecl) term).getName()) {  
          triples.add(new NameInfo((ZName)name, section, type, true));
        }
      }
      
      triples.addAll(visitChildrenOfTerm(term, section));
    }

    return triples;
  }

  private static List<NameInfo> visitChildrenOfTerm(Term term, String section)
  {
    List<NameInfo> nameInfoList = new ArrayList<NameInfo>();
    for (Object child : term.getChildren()) {
      if (child != null)
        if (child instanceof Term)
          nameInfoList.addAll(visitTerm((Term) child, section));
    }

    return nameInfoList;
  }
}

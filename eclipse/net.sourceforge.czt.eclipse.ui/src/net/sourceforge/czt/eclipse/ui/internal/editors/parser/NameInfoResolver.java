
package net.sourceforge.czt.eclipse.ui.internal.editors.parser;

import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.GenericType;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.PrintVisitor;

/**
 * @author Chengdong Xu
 */
public class NameInfoResolver
{
  private static Visitor<String> getTypeNameVisitor_ = new PrintVisitor();
//  private static final String ID_DELTAXI = "deltaxi"; // special ID for names starting with XI/DELTA
//  private static final String DELTA = ZString.DELTA;
//  private static final String XI = ZString.XI;
  
  public static Map<ZName, NameInfo> resolve(Spec spec, SectionManager manager)
  {
    Map<ZName, NameInfo> names = new HashMap<ZName, NameInfo>();
    
    if (spec != null) {
      for (Sect sect : spec.getSect()) {
        if (sect instanceof ZSect) {
          ZSect zSect = (ZSect) sect;
          visitZSect(names, zSect, manager);
        }
      }
    }
    
    return names;
  }
  

  /**
   * A utility method for retrieve the information for a ZName from a list of NameInfo
   * @param nameInfoList the list of name information
   * @param name the name to find
   * @return the NameInfo instance, if the specified name is found, or <i>null</i>; 
   */
  public static NameInfo findInfo(Map<ZName, NameInfo> names, ZName name)
  {
    if (names == null || name == null)
      return null;
    
    String id = name.getId();
    String word = name.getWord();
    if (id == null || word == null)
      return null;
    
//    System.out.println("ID: " + id);
//    System.out.println("WORD: " + word);
    
    // Check whether the word starts with DELTA/XI. In AST, the prefix is always
    // a single unicode character (Delta or Xi) for both LaTeX and Unicode mode.
//    if (id.equals(ID_DELTAXI)) {
//      while ((word != null) && (word.startsWith(DELTA) || word.startsWith(XI)))
//      {
//        word = word.substring(1);
//        if ((word != null) && word.length() > 0) {
//          for (NameInfo info :nameInfoList)
//            if(!info.isLocal() && word.equals(info.getName().getWord()))
//              return info;
//        }
//      }
//    }
//    else {
//      for (NameInfo info :nameInfoList)
//        if(id.equals(info.getName().getId()) && word.equals(info.getName().getWord()))
//          return info;
//    }
    if (names.containsKey(name))
      return names.get(name);
    
    return null;
  }

  private static void visitZSect(Map<ZName, NameInfo> existingNames, ZSect zSect, SectionManager manager)
  {
    if (existingNames == null || zSect == null || manager == null)
      return;
    
    String section = zSect.getName();

    try {
      SectTypeEnvAnn steAnn = manager.get(new Key<SectTypeEnvAnn>(section, SectTypeEnvAnn.class));
      if (steAnn != null) {
        for (NameSectTypeTriple triple : steAnn.getNameSectTypeTriple()) {
          ZName name = triple.getZName();
          Type type = triple.getType();
          
          // Add the name into the list if it is not already included 
          if (!existingNames.containsKey(name))
            existingNames.put(name, new NameInfo(name, triple.getSect(), type.accept(getTypeNameVisitor_), false));
          
          // Retrieve names from the type hierachy
          visitType(existingNames, type, triple.getSect());
        }
      }
      // Add names inside a declaration
      visitChildrenOfTerm(existingNames, zSect, section);
    } catch (CommandException e) {
      System.out.println("CommandException in NameInfoResolver: "+e);
    }
  }
  
  private static void visitType (Map<ZName, NameInfo> existingNames, Type type, String section)
  {
    if (type == null)
      return;
    
    if (type instanceof GenericType)
      visitGenericType(existingNames, (GenericType) type, section);
    
    if (type instanceof PowerType) {
      Type pt = ((PowerType)type).getType();
      if (pt != null && pt instanceof SchemaType)
        visitSchemaType(existingNames, (SchemaType)pt, section);
    }
  }
  
  private static void visitSchemaType (Map<ZName, NameInfo> existingNames, SchemaType schemaType, String section)
  {
    if (schemaType == null)
      return; 
    
    Signature sig = ((SchemaType) schemaType).getSignature();
    
    if (sig == null)
      return;
    
    for (NameTypePair pair : sig.getNameTypePair()) {
      Type type = pair.getType();
      if (type == null)
        continue;
      
      ZName name = pair.getZName();
      String t = type.accept(getTypeNameVisitor_);
      if (name != null && t != null && !existingNames.containsKey(name)) {
          existingNames.put(name, new NameInfo(name, section, t, false));
      }
      
      visitType(existingNames, type, section);
    }
  }
  
  private static void visitGenericType (Map<ZName, NameInfo> existingNames, GenericType genericType, String section)
  {
    if (genericType == null)
      return;
    
    ListTerm<Type2> type = genericType.getType();
    if (type == null || type.isEmpty())
      return;
    
    ZNameList nameList = genericType.getZNameList();
    String t = type.accept(getTypeNameVisitor_);
    if (nameList != null && t != null) {
      for (Name name : nameList)
        if (name != null && name instanceof ZName) {
          ZName zName = (ZName)name;
          if(!existingNames.containsKey(zName))
            existingNames.put(zName, new NameInfo(zName, section, t, false));
        }
    }
    
    // WAS: visitType(existingNames, type, section);
    // MarkU: changed this to iterate thru the getType list, but it is not
    //   clear from the docs whether this is the right thing to do.
    for (Type2 t2 : type) {
    	visitType(existingNames, t2, section);
    }
  }

  private static void visitChildrenOfTerm(Map<ZName, NameInfo> existingNames, Term term, String section)
  {
    if (term == null)
      return;
    
    for (Object child : term.getChildren()) {
      if (child != null && child instanceof Term) {
        if (child instanceof ConstDecl)
          visitConstDecl(existingNames, (ConstDecl) child, section);
        else if (child instanceof VarDecl)
          visitVarDecl(existingNames, (VarDecl) child, section);
        else if (child instanceof InclDecl)
          visitInclDecl(existingNames, (InclDecl) child, section);
//        else if (child instanceof Expr)
//          visitExpr(existingNames, (Expr) term, section);
        else
          visitChildrenOfTerm(existingNames, (Term)child, section);
      }
    }
  }
  
  private static void visitConstDecl(Map<ZName, NameInfo> existingNames, ConstDecl constDecl, String section)
  {
    if (existingNames == null || constDecl == null)
      return;
    
    Expr expr = constDecl.getExpr();
    if (expr == null)
      return;
    
    ZName name = constDecl.getZName();
    TypeAnn typeAnn = expr.getAnn(TypeAnn.class);
    if (name != null && typeAnn != null) {
      Type type = typeAnn.getType();
      if (type != null) {
        String toe = type.accept(getTypeNameVisitor_);
        if (toe != null && toe.length() > 5 && toe.startsWith("POWER")) {
          String t = toe.substring(5).trim();
          if (t != null && !t.equals(""))
            existingNames.put(name, new NameInfo(name, section, t, false));
        }
      } 
    }
    
    // Retrieve names from the expression
    visitExpr(existingNames, expr, section);
  }
  
  private static void visitVarDecl(Map<ZName, NameInfo> existingNames, VarDecl varDecl, String section)
  {
    if (existingNames == null || varDecl == null)
      return;
    
    Expr expr = varDecl.getExpr();
    if (expr == null)
      return;
    
    ZNameList nameList = varDecl.getName();
    TypeAnn typeAnn = expr.getAnn(TypeAnn.class);
    
    if (nameList != null && typeAnn != null) {
      Type type = typeAnn.getType();
      if (type != null) {
        String toe = type.accept(getTypeNameVisitor_);
        if (toe != null && toe.length() > 5 && toe.startsWith("POWER"))
          toe = toe.substring(5).trim();
          
        if (toe != null && !toe.equals("")) {
          for (Name name : nameList) {
            // System.out.println("Name: " + name);
            if (name != null && name instanceof ZName) {
              ZName zName = (ZName)name;
              if (!existingNames.containsKey(zName)) {
                existingNames.put(zName, new NameInfo(zName, section, toe, false));
                //System.out.println("Insert into table from VarDecl - " + name.accept(getTypeNameVisitor_));
              }
            }
          }
        }
      }
    }
    
    //  Retrieve names from the expression
    visitExpr(existingNames, expr, section);
    
  }
  
  private static void visitInclDecl(Map<ZName, NameInfo> existingNames, InclDecl inclDecl, String section)
  {
    if (existingNames == null || inclDecl == null)
      return;
    
    TypeAnn typeAnn = inclDecl.getAnn(TypeAnn.class);
    if (typeAnn != null) {
      Type type = typeAnn.getType();
      if (type != null && type instanceof PowerType) {
        Type t_pt = ((PowerType)type).getType();
        if (t_pt != null && t_pt instanceof SchemaType) {
          Signature sig = ((SchemaType)t_pt).getSignature();
          if (sig != null) {
            ListTerm<NameTypePair> pairs = sig.getNameTypePair();
            if (pairs != null)
              for (NameTypePair pair : pairs) {
                ZName name = pair.getZName();
                Type t_pair = pair.getType();
                if (name != null && t_pair != null) {
                  String t = t_pair.accept(getTypeNameVisitor_);
                  if (t != null)
                    t = t.trim();
                  if (t != null && t.equals("") && !existingNames.containsKey(name)) {
                    existingNames.put(name, new NameInfo(name, section, t, false));
                    // System.out.println("Insert into table from InclDecl - " + name.accept(getTypeNameVisitor_));
                  }
                }
              }
          }
        }
      }
    }
    
    visitExpr(existingNames, inclDecl.getExpr(), section);
  }
  
  private static void visitExpr(Map<ZName, NameInfo> existingNames, Expr expr, String section)
  {
    if (existingNames == null || expr == null)
      return;
    
    if (expr instanceof RefExpr) {
      RefExpr ref = (RefExpr) expr;
      ZName name = ref.getZName();
      TypeAnn typeAnn = ref.getAnn(TypeAnn.class);
      if (name != null && typeAnn != null) {
        Type type = typeAnn.getType();
        if (type != null) {
          String t = type.accept(getTypeNameVisitor_);
          if (t != null && !existingNames.containsKey(name)) {
            existingNames.put(name, new NameInfo(name, section, t, false));
            // System.out.println("Insert into table from Expr - " + name.accept(getTypeNameVisitor_));
          }  
        }
      }  
    }
    
    visitChildrenOfTerm (existingNames, expr, section);
  }
  
  // TODO: for extending to Circus needs to add all the Expr / Decl / Para to resolve known names.
}

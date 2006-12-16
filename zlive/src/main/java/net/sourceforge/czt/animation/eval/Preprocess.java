/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2005 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.Rewrite;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.ProverUtils.GetZSectNameVisitor;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.QntExpr;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.visitor.QntExprVisitor;
import net.sourceforge.czt.z.visitor.QntPredVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.zpatt.util.Factory;

/** Preprocesses a term to get it ready for evaluation.
 *  This unfolds some Z constructs into simpler ones,
 *  using sets of rewrite rules.
 *  
 * @author marku
 */
public class Preprocess
{
  private static final Logger LOG =
    Logger.getLogger("net.sourceforge.czt.animation.eval");
  
  private SectionManager sectman_;
  
  private RuleTable rules_;
  
  /** Create a term preprocessor that will apply a set
   *  of rules (see setRules) to a given term.
   * @param sectman  The section manager used to find rule tables.
   */
  public Preprocess(SectionManager sectman)
  {
    sectman_ = sectman;
  }

  /**
   * Collects the rules of the first ZSect in a given source file.
   * @param rulesFile  The name of the source file that contains the rules.
   */
  public void setRules(String rulesFile)
    throws IOException, ParseException, CommandException
  {
    URL url = getClass().getResource(rulesFile);
    if (url == null)
      throw new IOException("Cannot getResource("+rulesFile+")");
    sectman_.put(new Key(url.toString(), Source.class), new UrlSource(url));
    Term term = (Spec) sectman_.get(new Key(url.toString(), Spec.class));
    String sectname = term.accept(new GetZSectNameVisitor());
    sectman_.get(new Key(sectname, SectTypeEnvAnn.class)); // typecheck sect
    rules_ = (RuleTable) sectman_.get(new Key(sectname, RuleTable.class));
    // for debugging only...
    for (String ruleName : rules_.getRules().keySet())
      System.out.println("loaded rule "+ruleName);
  }
  
  /** Rewrites the given term by firstly unfolding VarDecls
   *  with multiple variables (x,y:T), then appling all the rewrite 
   *  rules of this Preprocess object to that term.  This should be 
   *  called after type checking, so that VarDecls with multiple
   *  variables can be expanded correctly.  (Section C.7.3.1
   *  of the Z standard implies that x,y:T cannot be expanded
   *  until any generics in type T have been fully instantiated).
   *  
   * @param sectname Gives the context for the proofs of rewrite rules.
   * @param term     The input term to rewrite.
   * @return         The rewritten term.
   */
  public Term preprocess(String sectname, Term term)
  {
    if (rules_ == null)
      throw new RuntimeException("preprocessing error: no rules!");
    Factory factory = new Factory(new ProverFactory());
    Term term2 = term.accept(new CopyVisitor(factory));
    Term term3 = Rewrite.rewrite(sectman_, sectname, term2, rules_);
    return term3;
  }

  /** A temporary hack to fix up any incorrect ZName ids
   *  left/created by the typechecker.
   */
  public Term fixIds(Term term) {
    return term.accept(new FixIdVisitor());
  }

  /** A temporary hack to fix up any incorrect ZName ids
   *  left/created by the typechecker.
   */
  public class FixIdVisitor
  implements TermVisitor<Term>,
    QntExprVisitor<Term>,
    QntPredVisitor<Term>,
    ZNameVisitor<Term>
  {
    /** This records all the local ZNames we have seen during the visit.
     *  Each quantifier pushes and pops a new level on the end of this.
     *  It does not quite implement the Z scope rules correctly,
     *  because in [x,y:E;...], the type expression E is considered to
     *  be within the scope of x and y.  However, this does not matter
     *  for ZLive, because this visitor is used after all declarations
     *  have been normalised, so types will contain global names only.
     */
    private List<Map<String,ZName>> seen;
    
    PrintVisitor printer = new PrintVisitor(false);
    
    public FixIdVisitor()
    {
      VisitorUtils.checkVisitorRules(this);
      seen = new ArrayList<Map<String,ZName>>();
      seen.add(new HashMap<String,ZName>());
    }

    private void startScope(ZSchText stext)
    {
      Map<String,ZName> map = new HashMap<String,ZName>();
      seen.add(map);
      for (Decl decl : stext.getZDeclList()) {
        if (decl instanceof VarDecl) {
          VarDecl vdecl = (VarDecl) decl;
          for (Name n : vdecl.getZNameList())
            declareName( (ZName)n );
        }
        else if (decl instanceof ConstDecl) {
          ConstDecl cdecl = (ConstDecl) decl;
          declareName(cdecl.getZName());
        }
        else {
          warning("InclDecl not unfolded: "+decl);
        }
      }
    }
    
    private void declareName(ZName name)
    {
      Map<String,ZName> map = seen.get(seen.size()-1);
      map.put(nameString(name), name);
    }

    /** Converts a ZName into a string, without any id information. */
    private String nameString(ZName name)
    {
      // StringBuffer not necessary here, since multi-decorations are rare.
      String result = name.getWord();
      for (Stroke s : name.getZStrokeList()) {
        result = result + s.accept(printer);
      }
      return result;
    }

    private void endScope()
    {
      assert seen.size() > 0;
      seen.remove(seen.size()-1);
    }

    private void warning(String msg)
    {
      System.out.println("WARNING: "+msg);
    }

    public Term visitTerm(Term term)
    {
      return VisitorUtils.visitTerm(this, term, true);
    }

    public Term visitZName(ZName name)
    {
      // get the string form of this name.
      String str = nameString(name);
      
      String id = name.getId();
      if (id == null)
        warning("ZName "+str+" has no id.");

      //TODO iterate from end to start
      for (int i=seen.size()-1; i >= 0; i--) {
        Map<String, ZName> scope = seen.get(i);
        ZName found = scope.get(str);
        if (found != null) {
          String newId = found.getId();
          if ( id==null && newId==null) {
            // do nothing (we've already warned about the missing id.)
          }
          else if (id == null ||
                   ! name.getId().equals(found.getId())) {
            warning("changing "+str+" id from "+id+" to "+newId);
            name.setId(newId);
          }
          return name;
        }
      }
      // this name was not locally declared, so we assume
      // that it is global and that its id is correct.
      return name;
    }

    public Term visitQntExpr(QntExpr term)
    {
      
      startScope(term.getZSchText());
      Term result = visitTerm(term);
      endScope();
      return result;
    }
    
    public Term visitQntPred(QntPred pred)
    {
      startScope(pred.getZSchText());
      Term result = visitTerm(pred);
      endScope();
      return result;
    }
  }
}

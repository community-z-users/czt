/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

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

import java.io.*;
import java.util.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;
import net.sourceforge.czt.print.z.PrintUtils;

public class ZLive
{
  private Factory factory_;

  private Flatten flatten_;
  
  /** A Writer interface to System.out. */
  protected Writer writer = new BufferedWriter(new OutputStreamWriter(System.out));

  protected SectionManager sectman_;

  /** The name of the section in which all evaluations will be done.
      Evaluations are illegal until this is set.
   */
  protected String currSectName_;

  /** The definition table for the current section. */
  protected DefinitionTable defnTable_;

  /** Stores the code used in the most recent evaluation. */
  protected FlatPredList predlist_;

  private static long newNameNum = 0;

  private static final List empty = new ArrayList();

  /** Generates a fresh temporary name. */
  public RefName createNewName()
  {
    return factory_.createRefName("tmp"+(newNameNum++), empty, null);
  }

  /** Recognises the RefNames produced by createNewName. */
  public /*@pure@*/ boolean isNewName(/*@non_null@*/ RefName name) {
    String word = name.getWord();
    return word.matches("tmp[0-9]+");
  }

  public ZLive() {
    factory_ = new Factory();
    flatten_ = new Flatten(this);
    sectman_ = new SectionManager();
    try {
      String defaultSpec = "\\begin{zsection} "
                        + "\\SECTION ZLiveDefault "
                        + "\\parents standard\\_toolkit "
                        + "\\end{zsection}";
      Spec spec = (Spec)sectman_.addLatexSpec(defaultSpec);
      ZSect sect = (ZSect)spec.getSect().get(0);
      setCurrentSection(sect.getName());
    }
    catch (Exception e) {
      System.out.println("ERROR: cannot create default section in section manager: " + e);
      e.printStackTrace();
    }
  }

  /**
   * Returns the factory used for creating AST objects.
   */
  public Factory getFactory()
  {
    return factory_;
  }

  /**
   * Sets the AST factory used for creating AST objects.
   **/
  public void setFactory(Factory fact)
  {
    factory_ = fact;
  }

  /** Get the current section manager. */
  public SectionManager getSectionManager()
  { return sectman_; }

  /** Get a flatten visitor. */
  public Flatten getFlatten()
  { return flatten_; }

   /** Set the section manager which will be used during evaluation. */
  //@ requires sm != null;
  public void setSectionManager(SectionManager sm)
  { sectman_ = sm; }

  /** Which section evaluations are being done in. */
  public String getCurrentSection()
  { return currSectName_; }

  /** Say which section future evaluations will be done in. */
  public void setCurrentSection(String name)
  {
    DefinitionTable newTable = (DefinitionTable) sectman_.getInfo(name, DefinitionTable.class);
    if (newTable == null) {
      throw new CztException("Cannot get definition table!");
    }
    else {
      defnTable_ = newTable;
      currSectName_ = name;
    }
  }

  /** Evaluate a Pred.
      This throws some kind of EvalException if pred is too difficult
      to evaluate or contains an undefined expression.
      @param pred  A net.sourceforge.czt.z.ast.Pred object.
      @return      Usually an instance of TruePred or FalsePred.
  */
  public Pred evalPred(Pred pred)
    throws EvalException
  {
    if (currSectName_ == null || defnTable_ == null) {
      throw new CztException("Must choose a section!");
    }
    predlist_ = new FlatPredList(this);
    predlist_.addPred(pred);
    Envir env0 = new Envir();
    Mode m = predlist_.chooseMode(env0);
    if (m == null)
      throw new EvalException("Cannot find mode to evaluate " + pred);
    predlist_.startEvaluation(m,env0);
    if (predlist_.nextEvaluation())
      return factory_.createTruePred();
    else
      return factory_.createFalsePred();
  }

  /** Prints the list of FlatPreds used in the last call
    * to evalPred or evalExpr.
    */
    public void printCode()
    {
      if(predlist_ == null) {
        System.out.println("No previous evaluations");
      }
      else {
        try {
          System.out.println("Printing " + predlist_.size() + " preds:");
          writer.write("Start of the Loop\n");
          for (Iterator i = predlist_.iterator(); i.hasNext(); ) {
            FlatPred p = (FlatPred) i.next();
            writer.write("Print flat " + p.toString() + "\n");
            //print(p, writer);
            //writer.write("Printed flat " + p.toString() + "\n");
          }
          writer.write("End of the loop\n");
          writer.flush();
          //writer.close();
        }
        catch (Exception e) {
          e.printStackTrace();
        }
        System.out.println("END");
      }
    }

  private void print(Term t, Writer writer) throws IOException
  {
    ZLiveToAstVisitor toAst = new ZLiveToAstVisitor();
    Term ast = (Term) t.accept(toAst);
    //writer.write(ast);
    PrintUtils.printUnicode(ast, writer, sectman_);
    writer.write("\n");
  }

  /** Evaluate an Expr.
      This throws some kind of EvalException if expr is too difficult
      to evaluate or contains an undefined expression.
      @param expr  A net.sourceforge.czt.z.ast.Pred object.
      @return      Usually an instance of EvalSet, or some other expr.
  */
  public Expr evalExpr(Expr expr)
    throws EvalException
  {
	//  return expr;
    throw new EvalException("Not implemented yet: " + expr);
  }

  public static void main(String args[])
  {
    System.out.println("ZLive version 0.0");
  }
}

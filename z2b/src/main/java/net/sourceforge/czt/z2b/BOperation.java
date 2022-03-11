/**
Copyright 2003, 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.z2b;

import java.util.*;

// the CZT classes for Z.
import net.sourceforge.czt.z.ast.*;



/**
 * This class represents a B operation (not initialisation).
 * It has input and output variables and pre and postcondition.
 *
 * @author Mark Utting
*/
public class BOperation
{
  /** The name of the operation */
  protected String name;

  /** The B machine that this operation belongs to */
  protected BMachine machine;
  
  /** The names of inputs */
  private List<String> inputs_ = new ArrayList<String>();

  /** The names of outputs */
  private List<String> outputs_ = new ArrayList<String>();

  /** Preconditions */
  private List<Pred> pre_ = new ArrayList<Pred>();

  /** Postconditions */
  private List<Pred> post_ = new ArrayList<Pred>();

  /**
   * Constructor for BOperation
   *
   * @param opName     The name of the operation.
   * @param opMachine  The machine that this operation belongs to.
   */
  public BOperation(String opName, BMachine opMachine) {
    name = opName;
    machine = opMachine;
  }


  //=============== Access functions =====================

  /** Returns the input names of this operation. */
  public List<String> getInputs() { return inputs_; }

  /** Returns the output names of this operation. */
  public List<String> getOutputs() { return outputs_; }

  /** Returns the precondition predicates of the operation */
  public List<Pred> getPre() { return pre_; }

  /** Returns the postcondition predicates of the operation */
  public List<Pred> getPost() { return post_; }


  /** Prints the operation out to the given file, in *.mch syntax
   *  @param bWriter  the file where the output should go.
   */
  public void print(BWriter bWriter) {
    bWriter.nl();
    if (outputs_.size() > 0) {
      printNames(bWriter, outputs_);
      bWriter.print(" <-- ");
    }
    bWriter.printName(name);
    if (inputs_.size() > 0) {
      bWriter.print("(");
      printNames(bWriter, inputs_);
      bWriter.print(")");
    }
    bWriter.print(" =");
    bWriter.nl();
    bWriter.startSection("PRE");
    if (pre_.size() > 0) bWriter.printPreds(pre_);
    else bWriter.print("1=1");
    bWriter.continueSection("PRE","THEN");
    // Now we output the postcondition as a generalised substitution:
    //    ANY frame' WHERE post2 THEN frame := frame' END
    // Note: frame is state vars plus output vars (eg. x, y!),
    //       and frame' is those same vars primed (eg. x', y!').
    //       Also, post2 is post with output vars primed.
    List<Pred> post2 = new ArrayList<Pred>();
    // Create primed versions of the output variables.
    Map<String,ZName> rename = new HashMap<String,ZName>();
    for (String name : outputs_) {
      rename.put(name, Create.prime(name));
    }
    // Rename outputs to outputs' in the postconditions.
    // Note that (final) state vars in post are already primed.
    RenameVisitor outPrimer = new RenameVisitor(rename);
    for (Pred pred : post_) {
      post2.add((Pred) outPrimer.rename(pred));
    }
    // Extend the rename map to include (x,x') for all state vars x.
    for (String name : machine.getVariables()) {
      rename.put(name, Create.prime(name));
    }
    bWriter.printAnyAssign(rename, post2);
    bWriter.endSection("PRE");
  }


  /** Prints a list of names in concise format, separated by commas. */
  //@ requires dest != null;
  //@ requires names != null && names.size() > 0;
  protected void printNames(BWriter dest, Collection<String> names) {
    Iterator<String> i = names.iterator();
    assert i.hasNext();
    while (true) {
      String name = i.next();
      dest.printName(name);
      if ( ! i.hasNext())
	break;
      dest.print(",");
    }
  }
}

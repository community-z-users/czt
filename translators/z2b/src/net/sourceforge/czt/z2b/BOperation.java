/**
Copyright 2003 Mark Utting
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
import java.util.logging.Logger;

// the CZT classes for Z.
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;

// our classes
import net.sourceforge.czt.z2b.*;


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
  List/*<Name>*/  inputs = new ArrayList();

  /** The names of outputs */
  List/*<Name>*/  outputs = new ArrayList();

  /** Preconditions */
  List/*<Pred>*/  pre = new ArrayList();

  /** Postconditions */
  List/*<Pred>*/  post = new ArrayList();

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
  public List/*<Name>*/ getInputs() { return inputs; }

  /** Returns the output names of this operation. */
  public List/*<Name>*/ getOutputs() { return outputs; }

  /** Returns the precondition predicates of the operation */
  public List/*<Pred>*/ getPre() { return pre; }

  /** Returns the postcondition predicates of the operation */
  public List/*<Pred>*/ getPost() { return post; }


  /** Prints the operation out to the given file, in *.mch syntax
   *  @param dest  the file where the output should go.
   */
  public void print(BWriter dest) {
    dest.nl();
    if (outputs.size() > 0) {
      printNames(dest,outputs);
      dest.print(" <-- ");
    }
    dest.printName(name);
    if (inputs.size() > 0) {
      dest.print("(");
      printNames(dest,inputs);
      dest.print(")");
    }
    dest.nl();
    dest.startSection("PRE");
    dest.printPreds(pre);
    dest.continueSection("PRE","THEN");
    // Now we output the postcondition as a generalised substitution:
    //    ALL frame' WHERE post2 THEN frame := frame' END
    // Note: frame is state vars plus output vars (eg. x, y!),
    //       and frame' is those same vars primed (eg. x', y!').
    //       Also, post2 is post with output vars primed.
    List post2 = new ArrayList();
    // Create primed versions of the output variables.
    Map rename = new HashMap();
    for (Iterator i = outputs.iterator(); i.hasNext(); ) {
      Name n = (Name)i.next();
      rename.put(Create.stringName(n), prime(n));
    }
    // Rename outputs to outputs' in the postconditions.
    RenameVisitor outPrimer = new RenameVisitor(rename);
    for (Iterator i = post.iterator(); i.hasNext(); ) {
      post2.add(outPrimer.rename((Pred)i.next()));
    }
    // Extend the rename map to include (x,x') for all state vars x.
    for (Iterator i = machine.getVariables().iterator(); i.hasNext(); ) {
      Name n = (Name)i.next();
      rename.put(Create.stringName(n), prime(n));
    }
    // now print the ANY..END statement.
    dest.startSection("ANY");
    printNames(dest, rename.values());
    dest.continueSection("ANY", "WHERE");
    dest.printPreds(post2);
    dest.continueSection("ANY", "THEN");
    for (Iterator i = rename.entrySet().iterator(); i.hasNext(); ) {
      Map.Entry entry = (Map.Entry)i.next();
      String v = (String)entry.getKey();
      Name v2 = (Name)entry.getValue();
      // output the assignment v := e
      dest.beginPrec(BTermWriter.ASSIGN_PREC);
      dest.printName(v);
      dest.print(" := ");
      dest.printName(v2);
      dest.endPrec(BTermWriter.ASSIGN_PREC);
      if (i.hasNext())
        dest.printSeparator(" || ");
    }
    dest.endSection("END");
    dest.endSection("PRE");
    dest.nl();
  }


  /** Prime a Name */
  public RefName prime(Name n) {
    RefName n2 = Create.refName(n);
    n2.getStroke().add(Create.nextStroke());
    return n2;
  }


  /** Prints a list of names in concise format, separated by commas. */
  //@ requires dest != null;
  //@ requires names != null && names.size() > 0;
  protected void printNames(BWriter dest, Collection names) {
    Iterator i = names.iterator();
    assert i.hasNext();
    while (true) {
      Name n = (Name)i.next();
      dest.printName(n);
      if ( ! i.hasNext())
	break;
      dest.print(",");
    }
  }
}


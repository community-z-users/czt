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
   * @param name  The name of the operation.
   */
  public BOperation(String name) {
    this.name = name;
  }


  //=============== Access functions =====================

  /** Returns the input names of this operation. */
  public List/*<Name>*/ getInputs() { return inputs; }

  /** Returns the output names of this operation. */
  public List/*<Name>*/ getOutputs() { return outputs; }

  /** Returns the precondition predicates of the operation */
  public List/*<Pred>*/ getPre() { return pre; }

  /** Returns the psotcondition predicates of the operation */
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
    dest.printPreds(post);
    dest.endSection("PRE");
    dest.nl();
  }


  /** Prints a list of names in concise format, separated by commas. */
  //@ requires dest != null;
  //@ requires names != null && names.size() > 0;
  protected void printNames(BWriter dest, List names) {
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


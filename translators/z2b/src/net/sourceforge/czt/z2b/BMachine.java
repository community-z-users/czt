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
 * This class represents a B abstract machine.
 * It has state variables and operations that manipulate them.
 *
 * Because it is designed for converting Z specs to B, the machine stores Z
 * expressions, predicates names etc.  For example, names can have
 * decorations.  Operations are specified with a pre/postcondition and
 * initialisation is specified with a predicate.
 *
 * @author Mark Utting
 */
public class BMachine
{
  /** The name of the machine */
  protected String name;

  /** The source location, where the machine came from*/
  protected String source;

  /** The constants and their properties */
  List/*<Name>*/  constants = new ArrayList();
  List/*<Pred>*/  properties = new ArrayList();

  /** State variables and their invariants */
  List/*<Name>*/  variables = new ArrayList();
  List/*<Pred>*/  invariant = new ArrayList();

  /** Initialisation variables and their invariants */
  List/*<Pred>*/  initialisation = new ArrayList();

  List/*<BOperation>*/ operations = new ArrayList();


  /**
   * Constructor for BMachine
   *
   * @param name   The name of the machine.
   * @param source The name of the file/URL where this machine came from.
   */
  public BMachine(String name, String source) {
    this.name = name;
    this.source = source;
  }


  //=============== Access functions =====================

  /** Returns the constant 'Name's of this machine. */
  public List/*<Name>*/ getConstants() { return constants; }

  /** Returns the properties of the constants */
  public List/*<Pred>*/ getProperties() { return properties; }

  /** Returns the state variables of this machine.  They have type Name. */
  public List/*<Name>*/ getVariables() { return variables; }

  /** Returns the invariant predicates */
  public List/*<Pred>*/ getInvariant() { return invariant; }

  /** Returns the initialisation predicates of this machine. */
  public List/*<Pred>*/ getInitialisation() { return initialisation; }

  /** Returns the operations of this machine.  They have type BOperation. */
  public List/*<BOperation>*/ getOperations() { return operations; }



  /** Prints the machine out to the given file, in *.mch syntax
   *  @param dest  the file where the output should go.
   */
  public void print(BWriter dest) {
    dest.startSection("MACHINE");
    dest.printName(name);
    if (constants.size() > 0) {
      dest.continueSection("MACHINE","CONSTANTS");
      printNames(dest,constants);
      assert properties.size() > 0;
      dest.continueSection("MACHINE","PROPERTIES");
      dest.printPreds(properties);
    }
    if (variables.size() > 0) {
      dest.continueSection("MACHINE","VARIABLES");
      printNames(dest,variables);
      assert properties.size() > 0;
      dest.continueSection("MACHINE","INVARIANT");
      dest.printPreds(invariant);
    }
    dest.continueSection("MACHINE","INITIALISATION");
    if (operations.size() > 0) {
      dest.continueSection("MACHINE","OPERATIONS");
      Iterator i = operations.iterator();
      while (i.hasNext()) {
	BOperation op = (BOperation)i.next();
	op.print(dest);
      }
    }
    dest.endSection("MACHINE");
  }


  /** Writes a list of names, separated by commas.
   *  <esc> requires names.size() > 0 </esc>
   */
  protected void printNames(BWriter dest, List names) {
    Iterator i = names.iterator();
    assert i.hasNext();
    while (true) {
      Name n = (Name)i.next();
      dest.printName(n);
      if ( ! i.hasNext())
	break;
      dest.printSeparator(",");
    }
  }

  //throw new BException("Z specification must contain one section");
}


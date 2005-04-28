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
 * Because it is designed for converting Z specs to B, the machine stores
 * Z expressions and predicates etc.  The Z names in the lists and maps
 * are represented as strings, but these may include Z decorations.
 * Operations are specified with pre/postconditions and
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

  /** Parameter types */
  List/*<String>*/  params = new ArrayList();

  /** Sets of constants */
  Map/*<String,List<String>>*/ sets = new HashMap();

  /** The constants and their properties */
  List/*<String>*/  constants = new ArrayList();
  List/*<Pred>*/  properties = new ArrayList();

  /** Definitions */
  Map/*<String,Expr>*/ defns = new HashMap();

  /** State variables and their invariants */
  List/*<String>*/  variables = new ArrayList();
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

  /** Returns the sets used in this machine.
   *  The name of each set is mapped to its list of members (DeclNames),
   *  or to null if the set has unknown contents.
   */
  public Map/*<String,List<String>>*/ getSets() { return sets; }

  /** Returns the constant 'Name's of this machine. */
  public List/*<String>*/ getConstants() { return constants; }

  /** Returns the properties of the constants */
  public List/*<Pred>*/ getProperties() { return properties; }

  /** Stores all Name == Expr definitions. */
  public Map/*<String,Expr>*/ getDefns() { return defns; }

  /** Returns the state variables of this machine.  They have type Name. */
  public List/*<String>*/ getVariables() { return variables; }

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
    if (sets.size() > 0) {
      dest.continueSection("MACHINE","SETS");
      Iterator i = sets.keySet().iterator();
      while (i.hasNext()) {
	String n = (String)i.next();
	dest.printName(n);
	List members = (List)sets.get(n);
	if (members != null) {
	  dest.print(" = {");
	  Iterator mem = members.iterator();
	  while (mem.hasNext()) {
	    dest.printName((String)mem.next());
	    if (mem.hasNext())
	      dest.print(",");
	  }
	  dest.print("}");
	}
	if (i.hasNext())
	  dest.printSeparator(";");
      }
    }
    if (constants.size() > 0) {
      dest.continueSection("MACHINE","CONSTANTS");
      printNames(dest,constants);
      assert properties.size() > 0;
      dest.continueSection("MACHINE","PROPERTIES");
      dest.printPreds(properties);
    }
    if (defns.size() > 0) {
      dest.continueSection("MACHINE","DEFINITIONS");
      for (Iterator i = defns.entrySet().iterator(); i.hasNext(); ) {
        Map.Entry entry = (Map.Entry)i.next();
        dest.beginPrec(BTermWriter.DEFN_PREC);
        dest.printName((String)entry.getKey());
        dest.print(" == ");
        dest.printExpr((Expr)entry.getValue());
        dest.endPrec(BTermWriter.DEFN_PREC);
        if (i.hasNext())
          dest.printSeparator(";");
      }
    }
    if (variables.size() > 0) {
      dest.continueSection("MACHINE","VARIABLES");
      printNames(dest,variables);
      assert invariant.size() > 0;
      dest.continueSection("MACHINE","INVARIANT");
      dest.printPreds(invariant);
    }
    dest.continueSection("MACHINE","INITIALISATION");
    if (initialisation.size() == 0)
      throw new BException("no initialisation predicates");
    // We use:  ANY state' WHERE init' THEN state := state' END
    // Rename outputs to outputs' in the postconditions.
    Map initRename = new HashMap();
    for (Iterator i = variables.iterator(); i.hasNext(); ) {
      String name = (String)i.next();
      initRename.put(name, Create.prime(name));
    }
    RenameVisitor initPrimer = new RenameVisitor(initRename);
    List initPreds = new ArrayList();
    for (Iterator i = initialisation.iterator(); i.hasNext(); ) {
      initPreds.add(initPrimer.rename((Pred)i.next()));
    }
    dest.printAnyAssign(initRename, initPreds);
    
    // Now the operations
    if (operations.size() > 0) {
      dest.continueSection("MACHINE","OPERATIONS");
      Iterator i = operations.iterator();
      while (i.hasNext()) {
	BOperation op = (BOperation)i.next();
	op.print(dest);
        if (i.hasNext())
          dest.printSeparator(";");
      }
    }
    dest.endSection("MACHINE");
  }


  /** Writes a list of names, separated by commas. */
  //@ requires names != null && names.size() > 0;
  //@ requires dest != null;
  protected void printNames(BWriter dest, List names) {
    Iterator i = names.iterator();
    assert i.hasNext();
    while (true) {
      String n = (String)i.next();
      dest.printName(n);
      if ( ! i.hasNext())
	break;
      dest.printSeparator(",");
    }
  }

  //throw new BException("Z specification must contain one section");
}


/**
Copyright (C) 2004 Mark Utting, Petra Malik
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.util;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * An operator table manages all the operator definitions of a section.
 * It provides search facilities for all the operators defined in this
 * section or inherited from  parent sections,
 * plus facilities for defining new operators.
 */
public class OpTable
{
  /**
   * Records all operators defined in this section.
   *
   * @czt.todo should the domain be String, Name or DeclName?
   */
  protected /*@non_null@*/ SortedMap/*<String,OpInfo>*/ ops_ = new TreeMap();

  /**
   * Records the operator tables of all direct parents.
   *
   * @czt.todo Why is this non null?  What about the operator table for
   *           the prelude section?
   * @czt.todo Why do we need this?  How about using <code>ops_</code>
   *           defined above since we have to go through all the parent's
   *           operator tables anyway to check whether they contain
   *           duplicated entries.
   */
  protected /*@non_null@*/ Set/*<OpInfo>*/ parentOps_;

  /**
   * Constructs an operator table for a new section.
   * It checks that the operators defined in the parents are
   * consistent, according to the 3 rules in the Z standard.
   *
   * @param parents Operator tables of all direct parents of the new section.
   * @czt.todo we could take a set/map of Sections here?
   *           Or the section manager plus a set of parent names?
   * @czt.todo Why not just take a List of OpTable?
   *           When we use a Set of OpTable, we must be very careful with
   *           equals and hashCode methods for OpTable and I do not see
   *           the importance why we should do that.
   */
  public OpTable(Set/*<OpTable>*/  /*@non_null@*/ parents)
  {
    parentOps_ = parents;
  }


  /**
   * A convenience constructor for sections with just one parent.
   *
   * @param parent  The operator table of the only parent section.
   */
  public OpTable(OpTable /*@non_null@*/ parent)
  {
  }

  /**
   * Looks up opname to see if it is defined as an operator
   * in this section or in any of the ancestor sections.
   * The resulting OpInfo structure contains all the details about
   * the operator, including the name of the section it was defined in.
   *
   * @param opname Operator name.  Example " _ + _ ".
   * @return       Returns <code>null</code> if <code>opname</code>
   *               is not an operator. 
   */
  public OpInfo lookup(String /*@non_null@*/ opname)
  {
    Iterator i = parentOps_.iterator();
    OpInfo info = (OpInfo) ops_.get(opname);
    while (info == null && i.hasNext()) {
      info = ((OpTable) i.next()).lookup(opname); // depth-first search
    }
    return info;
  }


  /**
   * Adds a new operator.
   *
   * @throws OperatorException if operator is incompatible
   *                           with existing operators.
   */
  public void add(String opname, OpInfo info)
    throws OperatorException
  {
  }

  /**
   * @czt.todo What is the difference between OptempPara defined
   *           in the AST and this OpInfo class?
   */
  public class OpInfo
  {
  }

  /**
   * @czt.todo How should this class look like?
   */
  public class OperatorException
    extends Exception
  {
  }
}

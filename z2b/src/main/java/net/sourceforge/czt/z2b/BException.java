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



/**
 * This exception is raised when the Z spec cannot be translated into B.
 *
 * This might be because of problems with:
 * <ol>
 *   <li> the Z spec (for example, it has no state schema)
 *   <li> the translator tool (for example, the Gaffe plugins cannot 
 *        decide which schema is the state schema.
 *   <li> limitations of the B format (for example, some Z operators
 *        or constructs are not allowed in B or are not yet handled
 *        by this translator).
 * </ol>
 *
 * Note: It extends net.sourceforge.czt.util.CztException because it may need to be thrown from
 * within visitor methods, and they currently do not allow other exceptions.
 *
 * @author Mark Utting
 */
public class BException
    extends net.sourceforge.czt.util.CztException
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 7060393204111699512L;

/**
   * Constructor for BException
   *
   * @param msg A description of why the exception was thrown
   */
  public BException(String msg) {
    super(msg);
  }
}

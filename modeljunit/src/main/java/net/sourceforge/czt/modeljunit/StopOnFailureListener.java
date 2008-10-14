/**
 Copyright (C) 2008 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License as published
 by the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit;

/** An implementation of ModelListener that throws an exception
 *  when the first test failure is detected.
 */
public class StopOnFailureListener extends AbstractListener
{
  public StopOnFailureListener()
  {
  }

  @Override
  public String getName()
  {
    return "stop on failure";
  }

  public void failure(TestFailureException ex)
  {
    throw ex;
  }
}

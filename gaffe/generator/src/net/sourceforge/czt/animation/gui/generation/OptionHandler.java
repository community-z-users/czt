/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley
 
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

package net.sourceforge.czt.animation.gui.generation;

/**
 * Interface to wrap code run when an {@link Option Option} is found on the command line.
 * Similar in purpose to an EventListener.
 * @author Nicholas Daley
 */
public interface OptionHandler
{
  /**
   * The method to run.
   * @param opt The command line option encountered.
   * @param argument The argument to the option, or null if no argument was given for the option.
   */
  public void handleOption(Option opt, String argument)
      throws BadOptionException;
};

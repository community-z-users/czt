/*
  Copyright (C) 2012 Andrius Velykis
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

import java.util.Collections;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * <p>
 * A command to compute an information object (e.g. info table - OpTable) based on a Z section. This
 * class abstracts common functionality when the info table can be calculated during the parsing of
 * Z section, hence the SectParsable name.
 * </p>
 * <p>
 * The command manages the transactions needed if the info table is calculated during parsing, and
 * performs the required transaction "move".
 * </p>
 * 
 * @param <T>
 *          The type of command result.
 * @author Andrius Velykis
 */
public abstract class SectParsableCommand<T> implements Command
{
  /**
   * <p>
   * Computes info table for a given ZSection name. The calculation requires a ZSect to provide the
   * content, thus first the ZSect is retrieved. Note, that if the ZSect is not parsed yet, the
   * command may trigger parsing of the ZSect.
   * </p>
   * <p>
   * This command is optimised for info tables that may be calculated on-the-fly during the parsing.
   * In that case, the incoming transaction is postponed to avoid recursive start of transaction
   * during the parsing.
   * </p>
   * <p>
   * If the parsing creates the info table, it will be cached and found. For other cases, e.g. when
   * the ZSect is added manually, it calculates the info table using
   * {@link #calculateFromSect(ZSect, SectionManager)}, on an already parsed ZSect. The calculations
   * are wrapped in an appropriate info table transaction, indicated by {@link #getKey(String)}.
   * </p>
   * 
   * @param name
   * @param manager
   * @return
   * @throws CommandException
   */
  @Override
  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    final Key<T> infoTKey = getKey(name);
    final Key<ZSect> zkey = new Key<ZSect>(name, ZSect.class);
    
    if (!manager.isCached(zkey)) {
      /*
       * The ZSect is not cached, so it will be parsed upon <code>manager.get(zkey)</code>. Parsing
       * can create ZSect's info table (the Parsable) on the fly, and will manage its transactions
       * there. So we will get transaction chain as, e.g. OpTable > ZSect > OpTable, which is
       * invalid. For that reason, we need to "postpone" current outstanding info table transaction
       * (started via SectionInfo.get()). We do this by canceling the current outstanding
       * transaction and allowing the parser to resolve its transactions correctly.
       */
      manager.postponeTransaction(infoTKey, zkey);
    }
    
    // get the section manager - either parse or retrieve a cached one
    ZSect zSect = manager.get(zkey);
    
    // during the parse, the info table may have been created, so check for that - otherwise 
    // allow the implementors to calculate it
    if (!manager.isCached(infoTKey))
    {
      /*
       * The info table is not calculated, e.g. because the ZSect was already cached. We allow the
       * extending class to calculate it, which may inspect the section and its parents. To capture
       * the dependencies correctly, we restart the transaction - if it was cancelled before parsing
       * (see above).
       */
      manager.ensureTransaction(infoTKey);
      
      /*
       * Run the calculation - note that we do not need to handle the cancellation of the info table
       * transaction explicitly. If an exception is thrown, the outer SectionInfo.get() will catch
       * and cancel it correctly.
       */
      T infoTable = calculateFromSect(zSect, manager);
      
      if (infoTable != null){
        // add explicit dependency on the ZSect, in case the transaction was cancelled above
        manager.endTransaction(infoTKey, infoTable, Collections.singleton(zkey));
      } else {
        // could not calculate the info table - cancel the transaction
        manager.cancelTransaction(infoTKey);
      }
    }

    return true;
  }
  
  /**
   * Retrieves the key of the command result.
   * @param name
   * @return
   */
  protected abstract Key<T> getKey(String name);
  
  /**
   * Performs calculation of the expected result from the given ZSect. The method must not add the
   * result to the section manager, as it will be done by the abstract command.
   * 
   * @param sect
   *          section to calculate the info table from
   * @param manager
   * @return the calculated info table
   * @throws CommandException
   */
  protected abstract T calculateFromSect(ZSect sect, SectionManager manager) 
      throws CommandException;
}

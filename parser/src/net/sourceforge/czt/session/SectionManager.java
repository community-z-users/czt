/*
  Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.session;

import java.io.*;
import java.net.URL;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.logging.Logger;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;

/**
 * This class is a repository for information about Z specs/sections.
 * It provides several services like computing
 * the markup function for a given section name.
 *
 * @author Petra Malik
 * @author Mark Utting
 */
public class SectionManager
  implements SectionInfo
{
  private Map/*<Key,Object>*/ content_ = new HashMap();


  /**
   * Lookup a key in the section manager.
   *
   * @param key   A (String,Class) pair.
   * @return      An instance of key.getType(), or null.
   *
   * @czt.todo  Call a default command if we cannot find it.
   */
  public Object get(Key key)
  {
    return content_.get(key);
  }

  /**
   * Add a new (Key,Value) pair.
   * It is an error to call add with an existing key.
   *
   * @param key    A (String,Class) pair.
   * @param value  Must be an instance of key.getType().
   */
  public void put(Key key, Object value)
  {
    assert key != null;
    assert value != null;
    if ( ! key.getType().isInstance(value)) {
      String message =
        "SectionManager ERROR: " + value +
        " is not an instance of " + key.getType();
      System.err.println(message);
    }
    assert key.getType().isInstance(value);
    // if (content_.containsKey(key))
    // throw new RuntimeException("Attempt to add duplicate key: " + key);
    content_.put(key, value);
    CztLogger.getLogger(getClass()).finer("SectionManager.put " + key);
  }

  /**
   * Similar to put(key,value).
   * At the moment, the dependencies are ignored.
   */
  public void put(Key key, Object value, Set/*<Key>*/ dependencies)
  {
    put(key, value);
  }

  public void reset()
  {
    // TODO: delete all entries except toolkit ones.
    content_.clear();
    CztLogger.getLogger(getClass()).finer("SectionManager reset");
    //Iterator i = content_.values().iterator();
    //while (i.hasNext()) {...}
  }

  /**
   * Returns the latex markup function for the given section name.
   */
  private LatexMarkupFunction getLatexMarkupFunction(String section)
  {
    Key key = new Key(section, LatexMarkupFunction.class);
    LatexMarkupFunction result = (LatexMarkupFunction) get(key);
    // TODO make this a default command
    if (result == null) {
      try {
        URL url = getLibFile(section + ".tex");
        LatexToUnicode l2u = new LatexToUnicode(url, this);
        while (l2u.next_token().sym != LatexSym.EOF) {
          // do nothing
        }
        Map markupFunctions = l2u.getMarkupFunctions();
        Iterator i = markupFunctions.keySet().iterator();
        while (i.hasNext()) {
          String sectName = (String) i.next();
          put(new Key(sectName, LatexMarkupFunction.class),
                                  markupFunctions.get(sectName));
        }
        result = (LatexMarkupFunction) get(key);
      }
      catch (Exception e) {
        String message =
          "Cannot find latex markup function for section '" + section + "'.";
        CztLogger.getLogger(getClass()).warning(message);
      }
    }
    return result;
  }

  public void putOpTable(String section, OpTable opTable)
  {
    put(new Key(section, OpTable.class), opTable);
  }

  private OpTable getOperatorTable(String section)
  {
    Key key = new Key(section, OpTable.class);
    OpTable result = (OpTable) get(key);

    // TODO: make this a default command
    if (result == null) {
      try {
        URL url = getClass().getResource("/lib/" + section + ".tex");
        Reader reader = new InputStreamReader(url.openStream());
        LatexParser parser =
          new LatexParser(reader, section + ".tex", this);
        parser.parse();
        Map tables = parser.getOperatorTables();
        Iterator i = tables.keySet().iterator();
        while (i.hasNext()) {
          String sectName = (String) i.next();
          put(new Key(sectName, OpTable.class),
                                  tables.get(sectName));
        }
        result = (OpTable) get(key);
      }
      catch (Exception e) {
        result = null;
      }
    }
    if (result == null) {
      OpTableVisitor visitor = new OpTableVisitor(this);
      ZSect zSect = (ZSect) getAst(section);
      if (zSect != null) {
        result = (OpTable) visitor.run(zSect);
        if (result != null) {
          put(key, result);
        }
      }
    }
    if (result == null) {
      String message =
        "Cannot find operator table for section '" + section + "'.";
      Logger logger = CztLogger.getLogger(SectionManager.class);
      logger.warning(message);
    }
    return result;
  }

  private DefinitionTable getDefinitionTable(String section)
  {
    Key key = new Key(section, DefinitionTable.class);
    DefinitionTable result = (DefinitionTable) get(key);
    // TODO: make this a default command
    if (result == null) {
      DefinitionTableVisitor visitor = new DefinitionTableVisitor(this);
      Term term = getAst(section);
      if (term != null) {
        term.accept(visitor);
        result = visitor.getDefinitionTable();
        if (result != null) {
          put(key, result);
        }
      }
    }
    if (result == null) {
      String message =
        "Cannot find definition table for section '" + section + "'.";
      Logger logger = CztLogger.getLogger(SectionManager.class);
      logger.warning(message);
    }
    return result;
  }

  public Term getAst(URL url)
    throws ParseException, IOException
  {
    Key key = new Key(url.toString(), Spec.class);
    Spec spec = (Spec) get(key);
    assert spec == null; // user should have called reset() before re-parsing.
    if (spec == null) {
      spec = (Spec) ParseUtils.parse(url, this);
      put(key, spec);
      // TODO: move this into a separate 'explode' command?
      for (Iterator iter = spec.getSect().iterator(); iter.hasNext(); ) {
        Object o = iter.next();
        if (o instanceof ZSect) {
          ZSect zSect = (ZSect) o;
          String name = zSect.getName();
          put(new Key(name, ZSect.class), zSect);
        }
      }
    }
    return spec;
  }

  public Term addLatexSpec(String latexSpec)
    throws ParseException
  {
    Spec spec = (Spec) ParseUtils.parseLatexString(latexSpec, this);
    for (Iterator iter = spec.getSect().iterator(); iter.hasNext(); ) {
      Object o = iter.next();
      if (o instanceof ZSect) {
        ZSect zSect = (ZSect) o;
        put(new Key(zSect.getName(), ZSect.class), zSect);
      }
    }
    return spec;
  }

  public Term getAst(String section)
  {
    Key key = new Key(section, ZSect.class);
    Term result = (Term) content_.get(key);
    // TODO: make this a default command...
    if (result == null) {
      try {
        URL url = getLibFile(section + ".tex");
        if (url != null) {
          Spec spec = (Spec) ParseUtils.parseLatexURL(url, this);
          for (Iterator iter = spec.getSect().iterator(); iter.hasNext(); ) {
            Object o = iter.next();
            if (o instanceof ZSect) {
              ZSect zSect = (ZSect) o;
              if (zSect.getName().equals(section)) {
                result = zSect;
                put(key, result);
              }
            }
          }
        }
      }
      catch (Exception e) {
        // TODO: return this exception?
        e.printStackTrace();
      }
    }
    if (result == null) {
      String message =
        "Cannot find AST for section '" + section + "'.";
      CztLogger.getLogger(getClass()).warning(message);
    }
    return result;
  }

  public URL getLibFile(String filename)
  {
    return getClass().getResource("/lib/" + filename);
  }

  public Object getInfo(String sectionName, Class infoType)
  {
    if (infoType.equals(ZSect.class) ||
        infoType.equals(Sect.class)) {
      return getAst(sectionName);
    }
    else if (infoType.equals(OpTable.class)) {
      return getOperatorTable(sectionName);
    }
    else if (infoType.equals(DefinitionTable.class)) {
      return getDefinitionTable(sectionName);
    }
    else if (infoType.equals(LatexMarkupFunction.class)) {
      return getLatexMarkupFunction(sectionName);
    }
    else {
      Key key = new Key(sectionName, infoType);
      return get(key);
    }
  }

  public boolean isAvailable(String sectName)
  {
    if (getAst(sectName) != null) return true;
    return false;
  }

  public String toString()
  {
    return "SectionManager contains " + content_.toString();
  }
}

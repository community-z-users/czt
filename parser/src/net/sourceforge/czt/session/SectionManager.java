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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;

/**
 * This class provides some services like computing
 * the markup function for a given section name.
 *
 * @author Petra Malik
 */
public class SectionManager
  implements SectionInfo
{
  private Map ast_ = new HashMap();

  /**
   * A latex markup function cache.
   * It is basically a mapping from String, the name of a section,
   * to its LatexMarkupFunction.
   */
  private Map markupFunctions_ = new HashMap();

  private Map opTable_ = new HashMap();

  private Map definitionTable_ = new HashMap();

  /**
   * Returns the latex markup function for the given section name.
   */
  private LatexMarkupFunction getLatexMarkupFunction(String section)
  {
    LatexMarkupFunction result =
      (LatexMarkupFunction) markupFunctions_.get(section);
    if (result == null) {
      try {
        URL url = getLibFile(section + ".tex");
        LatexToUnicode l2u = new LatexToUnicode(url, this);
        while (l2u.next_token().sym != LatexSym.EOF) {
          // do nothing
        }
        Map markupFunctions = l2u.getMarkupFunctions();
        markupFunctions_.putAll(markupFunctions);
        result = (LatexMarkupFunction) markupFunctions_.get(section);
      }
      catch (Exception e) {
        String message =
          "Cannot find latex markup function for section '" + section + "'.";
        CztLogger.getLogger(getClass()).warning(message);
      }
    }
    return result;
  }

  private OpTable getOperatorTable(String section)
  {
    OpTable result =
      (OpTable) opTable_.get(section);
    if (result == null) {
      try {
        URL url = getClass().getResource("/lib/" + section + ".tex");
        Reader reader = new InputStreamReader(url.openStream());
        LatexParser parser =
          new LatexParser(reader, section + ".tex", this);
        parser.parse();
        Map tables = parser.getOperatorTables();
        opTable_.putAll(tables);
        result = (OpTable) tables.get(section);
      }
      catch (Exception e) {
        result = null;
      }
    }
    if (result == null) {
      OpTableVisitor visitor = new OpTableVisitor(this);
      result = (OpTable) visitor.run((ZSect) getAst(section));
      if (result != null) {
        opTable_.put(section, result);
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
    DefinitionTable result =
      (DefinitionTable) definitionTable_.get(section);
    if (result == null) {
      DefinitionTableVisitor visitor = new DefinitionTableVisitor(this);
      Term term = getAst(section);
      if (term != null) {
        term.accept(visitor);
        result = visitor.getDefinitionTable();
        if (result != null) {
          definitionTable_.put(section, result);
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
    Spec spec = (Spec) ParseUtils.parse(url, this);
    for (Iterator iter = spec.getSect().iterator(); iter.hasNext(); ) {
      Object o = iter.next();
      if (o instanceof ZSect) {
        ZSect zSect = (ZSect) o;
        String name = zSect.getName();
        ast_.put(name, zSect);
        definitionTable_.remove(name);
        markupFunctions_.remove(name);
        opTable_.remove(name);
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
        ast_.put(zSect.getName(), zSect);
      }
    }
    return spec;
  }

  public Term getAst(String section)
  {
    Term result = (Term) ast_.get(section);
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
                ast_.put(section, result);
              }
            }
          }
        }
      }
      catch (Exception e) {
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
    String message = "Unexpected info type '" + infoType + "'.";
    CztLogger.getLogger(getClass()).warning(message);
    return null;
  }

  public boolean isAvailable(String sectName)
  {
    if (getAst(sectName) != null) return true;
    return false;
  }

  public boolean isAvailable(Class infoType)
  {
    if (infoType.equals(ZSect.class) ||
        infoType.equals(Sect.class) ||
        infoType.equals(OpTable.class) ||
        infoType.equals(DefinitionTable.class) ||
        infoType.equals(LatexMarkupFunction.class))
      return true;
    return false;
  }
}

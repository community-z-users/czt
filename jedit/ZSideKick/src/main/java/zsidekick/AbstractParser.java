/*
 * AbstractParser.java
 * Copyright (C) 2006 Petra Malik
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package zsidekick;

import java.io.IOException;
import java.util.Iterator;
import java.util.List;

import org.gjt.sp.jedit.*;
import errorlist.*;
import sidekick.*;

import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.z.ast.*;

public abstract class AbstractParser
  extends SideKickParser
  implements ParsePropertiesKeys
{
  public AbstractParser(String name)
  {
    super(name);
  }

  public abstract Markup getMarkup();

  public abstract SectionManager getManager();

  public SideKickParsedData parse(Buffer buffer,
                                  DefaultErrorSource errorSource)
  {
    ParsedData data = new ParsedData(buffer.getName());
    try {
      SectionManager manager = getManager();
      final String name = buffer.getPath();
      final Source source =
        new StringSource(buffer.getText(0, buffer.getLength()), name);
      source.setEncoding(buffer.getStringProperty("encoding"));
      source.setMarkup(getMarkup());
      manager.put(new Key(name, Source.class), source);
      Spec spec = (Spec) manager.get(new Key(name, Spec.class));
      if (spec.getSect().size() > 0) {
        data.addData(spec, manager, buffer);
        for (Sect sect : spec.getSect()) {
          if (sect instanceof ZSect) {
            manager.get(new Key(((ZSect) sect).getName(),
                                SectTypeEnvAnn.class));
          }
        }
      }
    }
    catch (CommandException exception) {
      errorSource.clear();
      Throwable cause = exception.getCause();
      if (cause instanceof ParseException) {
        List errors = ((ParseException) cause).getErrorList();
        for (Iterator iter = errors.iterator(); iter.hasNext(); ) {
          Object next = iter.next();
          ParseError parseError = (ParseError) next;
          errorSource.addError(ErrorSource.ERROR,
                               buffer.getPath(),
                               parseError.getLine() - 1,
                               parseError.getColumn() - 1,
                               0,
                               parseError.getMessage());
        }
      }
      else if (cause instanceof TypeErrorException) {
        List<ErrorAnn> errors = ((TypeErrorException) cause).errors();
        printErrors(errors, buffer, errorSource);
      }
      else if (cause instanceof IOException) {
        String message = "Input output error: " + cause.getMessage();
        errorSource.addError(ErrorSource.ERROR,
                             buffer.getPath(),
                             0,
                             0,
                             0,
                             message);
      }
      else {
        String message = cause + getClass().getName();
        errorSource.addError(ErrorSource.ERROR,
                             buffer.getPath(),
                             0,
                             0,
                             0,
                             message);
      }
    }
    return data;
  }

  protected void printErrors(List<? extends ErrorAnn> errors,
                             Buffer buffer,
                             DefaultErrorSource errorSource)
  {
    for (ErrorAnn errorAnn : errors) {
      errorSource.addError(ErrorSource.ERROR,
                           buffer.getPath(),
                           errorAnn.getLine() - 1,
                           errorAnn.getColumn() - 1, 0,
                           errorAnn.toString());
    }
  }

  protected void setParseProperties(SectionManager manager)
  {
    String propname =
      ZSideKickPlugin.PROP_EXTRACT_COMMA_OR_SEMI_FROM_DECORWORDS;
    String value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    manager.setProperty(PROP_EXTRACT_COMMA_OR_SEMI_FROM_DECORWORDS, value);
    propname = ZSideKickPlugin.PROP_SPACE_BEFORE_PUNCTATION;
    value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    manager.setProperty(PROP_ADD_SPACE_BEFORE_PUNCTATION, value);
    propname = ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS;
    value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    manager.setProperty(PROP_IGNORE_UNKNOWN_LATEX_COMMANDS, value);
  }
}

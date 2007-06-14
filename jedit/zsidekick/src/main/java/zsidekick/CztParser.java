/*
 * CztParser.java
 * Copyright (C) 2006, 2007 Petra Malik
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

import java.io.File;
import java.io.IOException;
import java.util.Iterator;
import java.util.List;

import org.gjt.sp.jedit.*;
import org.gjt.sp.jedit.textarea.TextAreaPainter;
import errorlist.*;
import sidekick.*;

import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.z.ast.*;

public class CztParser
  extends SideKickParser
  implements ParsePropertiesKeys,
             PrintPropertiesKeys
{
  /* Z extension (dialect). */
  private String extension_;
  private Markup markup_;
  private WffHighlight wffHighlight_= new WffHighlight();

  public CztParser(String extension, Markup markup)
  {
    super(extension + (markup == Markup.UNICODE ? "" : "latex"));
    extension_ = extension;
    markup_ = markup;
  }

  public void activate(EditPane editPane)
  {
    super.activate(editPane);
    wffHighlight_.setTextArea(editPane.getTextArea());
    editPane.getTextArea().getPainter().addExtension(wffHighlight_);
  }

  public void deactivate(EditPane editPane)
  {
    super.deactivate(editPane);
    editPane.getTextArea().getPainter().removeExtension(wffHighlight_);
  }

  public Markup getMarkup()
  {
    return markup_;
  }

  public SectionManager getManager()
  {
    SectionManager manager = new SectionManager(extension_);
    setParseProperties(manager);
    return manager;
  }

  public SideKickParsedData parse(Buffer buffer,
                                  DefaultErrorSource errorSource)
  {
    ParsedData data = new ParsedData(buffer.getName());
    try {
      SectionManager manager = getManager();
      final String name = buffer.getPath();
      final String path = new File(name).getParent();
      if (path != null) {
        manager.setProperty("czt.path", path);
      }
      final Source source =
        new StringSource(buffer.getText(0, buffer.getLength()), name);
      source.setEncoding(buffer.getStringProperty("encoding"));
      source.setMarkup(getMarkup());
      manager.put(new Key(name, Source.class), source);
      Spec spec = (Spec) manager.get(new Key(name, Spec.class));
      if (spec.getSect().size() > 0) {
        data.addData(spec, manager, wffHighlight_, buffer);
        if (! buffer.getBooleanProperty("zsidekick.disable-typechecking")) {
          for (Sect sect : spec.getSect()) {
            if (sect instanceof ZSect) {
              manager.get(new Key(((ZSect) sect).getName(),
                                  SectTypeEnvAnn.class));
            }
          }
        }
      }
      try {
        ParseException parseException = (ParseException)
          manager.get(new Key(source.getName(), ParseException.class));
        if (parseException != null) {
          printErrors(parseException.getErrors(), buffer, errorSource);
        }
      }
      catch (CommandException e) {
        // TODO Is ignoring OK?
      }
    }
    catch (CommandException exception) {
      errorSource.clear();
      Throwable cause = exception.getCause();
      if (cause instanceof CztErrorList) {
        List<? extends CztError> errors = ((CztErrorList) cause).getErrors();
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
    catch (Throwable e) {
      errorSource.clear();
      e.printStackTrace();
      String message =
        "Caught " + e.getClass().getName() + ": " + e.getMessage();
      errorSource.addError(ErrorSource.ERROR,
                           buffer.getPath(),
                           0,
                           0,
                           0,
                           message);
    }
    return data;
  }

  protected void printErrors(List<? extends CztError> errors,
                             Buffer buffer,
                             DefaultErrorSource errorSource)
  {
    for (CztError error : errors) {
      int line, startOffset, endOffset;
      if (error.getStart() >= 0 && error.getLength() >= 0) {
        line = buffer.getLineOfOffset(error.getStart());
        startOffset = error.getStart() - buffer.getLineStartOffset(line);
        endOffset = startOffset + error.getLength(); 
      }
      else {
        line = error.getLine();
        startOffset = error.getColumn();
        endOffset = 0;
      }
      if (line < 0 || line >= buffer.getLineCount()) {
        line = buffer.getLineCount() - 1;
      }
      if (startOffset < 0 || startOffset >= buffer.getLineLength(line)) {
        startOffset = 0;
      }
      if (endOffset < 0 || endOffset >= buffer.getLineLength(line)) {
        endOffset = 0;
      }
      errorSource.addError(ErrorType.ERROR.equals(error.getErrorType()) ?
                             ErrorSource.ERROR : ErrorSource.WARNING,
                           buffer.getPath(),
                           line,
                           startOffset,
                           endOffset,
                           error.getMessage());
    }
  }

  protected void setParseProperties(SectionManager manager)
  {
    String propname = ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS;
    String value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    manager.setProperty(PROP_IGNORE_UNKNOWN_LATEX_COMMANDS, value);
    propname = ZSideKickPlugin.PROP_PRINT_IDS;
    value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    manager.setProperty(PROP_PRINT_NAME_IDS, value);
  }
}

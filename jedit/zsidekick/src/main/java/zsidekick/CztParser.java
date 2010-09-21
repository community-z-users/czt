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
import java.util.List;

import java.util.logging.Level;
import java.util.logging.Logger;
import org.gjt.sp.jedit.*;
import errorlist.*;
import sidekick.*;

import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.oz.TypecheckPropertiesKeys;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;

public class CztParser
  extends SideKickParser
  implements ParsePropertiesKeys,
             PrintPropertiesKeys,
	     TypecheckPropertiesKeys
{
  /* Z extension (dialect). */
  private String extension_;
  private Markup markup_;
  private WffHighlight wffHighlight_= new WffHighlight();
  private boolean debug_ = false;
  private Logger logger_ = CztLogger.getLogger(SectionManager.class);

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

  public SectionManager getManager(Buffer buffer)
  {
    SectionManager manager = new SectionManager(extension_);
    setProperties(manager, buffer);
    return manager;
  }
  
  protected void setFileLogger()
  {
    CztLogger.setFileHandler(logger_, Level.CONFIG, ZSideKickPlugin.DEBUG_LOG_FILENAME);    
  }
    
  public SideKickParsedData parse(Buffer buffer,
                                  DefaultErrorSource errorSource)
  {   
    ParsedData data = new ParsedData(buffer.getName(), getMarkup());    
    try {      
      SectionManager manager = getManager(buffer);
      if (debug_) { setFileLogger(); }
      final String name = buffer.getPath();
      final String path = new File(name).getParent();      
      if (path != null) {
        String oldpath = manager.getProperty("czt.path");
        String localpath = ((oldpath == null || oldpath.isEmpty()) ? path : oldpath + ";" + path);
        assert localpath != null;
        manager.setProperty("czt.path", localpath);
        logger_.config("CZT path as " + localpath);        
      }
      final Source source =
        new StringSource(buffer.getText(0, buffer.getLength()), name);
      source.setEncoding(buffer.getStringProperty("encoding"));
      source.setMarkup(getMarkup());
      manager.put(new Key<Source>(name, Source.class), source);
      Spec spec = manager.get(new Key<Spec>(name, Spec.class));
      logger_.config("Parsing " + source);
      logger_.config("Command for Spec is "+manager.getCommand(Spec.class));      
      if (spec.getSect().size() > 0) {
        data.addData(spec, manager, wffHighlight_, buffer);
        boolean typeChecking = !buffer.getBooleanProperty("zsidekick.disable-typechecking");
        logger_.config("Typechecking? " + typeChecking);        
        if (typeChecking) {
          for (Sect sect : spec.getSect()) {
            if (sect instanceof ZSect) {                            
              logger_.config("Command for SectTypeEnvAnn is "+manager.getCommand(SectTypeEnvAnn.class));              
              // typecheck the section.
              SectTypeEnvAnn ste = manager.get(new Key<SectTypeEnvAnn>(((ZSect) sect).getName(), SectTypeEnvAnn.class));
              logger_.config("Typechecked with results as \n " + ste);
            }
          }
        }
      }
      try {
        ParseException parseException = 
          manager.get(new Key<ParseException>(source.getName(), ParseException.class));
        if (parseException != null) {
          printErrors(parseException.getErrors(), buffer, errorSource);
        }        
      }
      catch (CommandException e) {        
        String message = e.getCause() + getClass().getName();
        logger_.config("Command exception was thrown while printing parser errors: " + message);
        errorSource.addError(ErrorSource.ERROR,
                             buffer.getPath(),
                             0,
                             0,
                             0,
                             message);
      }
    }
    catch (CommandException exception) {      
      errorSource.clear();
      Throwable cause = exception.getCause();
      logger_.config("Command exception was thrown while printing type errors: " + exception.getMessage() + " \t " + cause.getMessage());
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
      logger_.config("Throwable exception raised: " + message);      
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
      DefaultErrorSource.DefaultError jerror =
        new DefaultErrorSource.DefaultError(errorSource,
               ErrorType.ERROR.equals(error.getErrorType()) ?
                                ErrorSource.ERROR : ErrorSource.WARNING,
               buffer.getPath(),
               line,
               startOffset,
               endOffset,
               error.getMessage());
      if (error.getInfo() != null) jerror.addExtraMessage(error.getInfo());
      errorSource.addError(jerror);
    }
  }

  protected void setProperties(SectionManager manager, Buffer buffer)
  {
    String propname = ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS;
    String value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    manager.setProperty(PROP_IGNORE_UNKNOWN_LATEX_COMMANDS, value);

    propname = ZSideKickPlugin.PROP_PRINT_IDS;
    value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    manager.setProperty(PROP_PRINT_NAME_IDS, value);

    propname = ZSideKickPlugin.PROP_RECURSIVE_TYPES;
    value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    manager.setProperty(PROP_TYPECHECK_RECURSIVE_TYPES, value);

    propname = ZSideKickPlugin.PROP_USE_STRONG_TYPING;
    value = jEdit.getBooleanProperty(propname) ? "true" : "false";
    manager.setProperty(PROP_TYPECHECK_USE_STRONG_TYPING, value);

    propname = ZSideKickPlugin.PROP_DEBUG_ZSIDEKICK;
    debug_ = jEdit.getBooleanProperty(propname);
    
    int width = buffer.getIntegerProperty("maxLineLen", 0);
    if (width > 0) {
      manager.setProperty(PROP_TXT_WIDTH, "" + width);
    }
    
    propname = ZSideKickPlugin.PROP_CZTPATH;
    value = jEdit.getProperty(propname);
    if (value != null)
    {
      manager.setProperty(propname, value);
    }
    }
  }

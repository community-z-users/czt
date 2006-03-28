/*
 * SpecialLatexParser.java
 *
 * Created on 15 March 2006, 10:45
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.circus;

import java.io.*;
import java.text.MessageFormat;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.logging.ConsoleHandler;
import java.util.logging.Formatter;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;

import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.AstValidator;
import net.sourceforge.czt.base.util.XmlWriter;
import net.sourceforge.czt.parser.util.LatexMarkupFunction;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.CztLogger;

import net.sourceforge.czt.circus.jaxb.JaxbValidator;
import net.sourceforge.czt.circus.jaxb.JaxbXmlWriter;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;


/**
 * A parser for LaTeX mark-up.  This is a convenience class that
 * composes the {@link LatexScanner} and the {@link Parser}.
 *
 * @see net.sourceforge.czt.parser.z
 */
public class SpecialLatexParser
{
  ZFactory factory_ = new ZFactoryImpl();
  LatexScanner scanner_;
  Parser parser_;

  public SpecialLatexParser(Reader in, SectionInfo sectInfo, Properties properties)
  {
    scanner_ = new LatexScanner(in, sectInfo, properties);
    parser_ = new Parser(scanner_, sectInfo);
  }

  public SpecialLatexParser(Reader in,
                  String filename,
                  SectionInfo sectInfo,
                  Properties properties)
  {
    scanner_ = new LatexScanner(in, sectInfo, properties);
    scanner_.setSource(filename);
    parser_ = new Parser(scanner_, filename, sectInfo);
  }

  /**
   * Converts latex to zml.
   */
  public static void main(String[] args)
  {
    String usage = "Usage: net.sourceforge.czt.parser.circus.SpecialLatexParser"
      + " [ -in <inputfile>] [ -out <outputfile>]";
    try {
      String filename = null;
      Logger logger = CztLogger.getLogger(SpecialLatexParser.class);
      Reader in = new InputStreamReader(System.in);
      OutputStream out = System.out;
      for (int i = 0; i < args.length; i++) {
        if ("-in".equals(args[i])) {
          if (i < args.length) {
            filename = args[++i];
            in = new InputStreamReader(new FileInputStream(filename));
          } else {
            System.err.println(usage);
            return;
          }
        } else if ("-out".equals(args[i])) {
          if (i < args.length) {
            out = new FileOutputStream(args[++i]);
          } else {
            System.err.println(usage);
            return;
          }
        } else {
          System.err.println(usage);
          return;
        }
      }      
      boolean SHOW_TIMESTAMP = true;
      boolean SHOW_RECORDED_MESSAGE = true;
      boolean SHOW_SOURCE_METHOD = false;
      boolean SHOW_DIRECTORY = false;
      boolean SHOW_STACK_TRACE = true;
      SimpleFormatterForCircus sfc = new SimpleFormatterForCircus(
              SHOW_TIMESTAMP, SHOW_RECORDED_MESSAGE, 
              SHOW_SOURCE_METHOD, SHOW_DIRECTORY, SHOW_STACK_TRACE);      
      ConsoleHandler ch = new ConsoleHandler();
      ch.setLevel(Level.ALL);            
      ch.setFormatter(sfc);
      
      /*
      logger = CztLogger.getLogger(Latex2Unicode.class);
      logger.addHandler(ch);
      logger.setLevel(Level.ALL);      
      
      logger = CztLogger.getLogger(KeywordScanner.class);
      logger.addHandler(ch);
      logger.setLevel(Level.ALL);      
      
      logger = CztLogger.getLogger(LatexParser.class);
      logger.addHandler(ch);
      logger.setLevel(Level.ALL);      
      
      logger = CztLogger.getLogger(UnicodeParser.class);
      logger.addHandler(ch);
      logger.setLevel(Level.ALL);      
      */      
      logger = CztLogger.getLogger(Parser.class);
      logger.addHandler(ch);
      logger.setLevel(Level.ALL);         
              
      SectionManager sm = new SectionManager();
      sm.setProperty("czt.path", "D:\\research\\tools\\java\\sourceforge\\czt\\0.4.1\\parser\\lib");
      SpecialLatexParser parser =
        new SpecialLatexParser(in, filename, sm, new Properties());
      Term term = parser.parse();      
      if (term != null) {
          /*
        AstValidator validator = new JaxbValidator();
        if (! validator.validate(term)) {
          String message = "AST is not valid.";
          logger.warning(message);
        }
        XmlWriter xmlWriter = new JaxbXmlWriter();
        xmlWriter.write(term, out);*/
        System.out.println("Parser ok");
      }
      else {
        System.err.println("Parse error");
      }
      out.close();
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

  public Term parse()
    throws ParseException
  {
    try {
      final Symbol parseTree = parser_.parse();
      final Term term = (Term) parseTree.value;
      return term;
    }
    catch (ParseException e) {
      throw e;
    }
    catch (RuntimeException e) {
      throw e;
    }
    catch (Exception e) {
      e.printStackTrace();
      throw new CztException("This should never happen", e);
    }
  }
  
  public static class SimpleFormatterForCircus extends Formatter {

    Date dat = new Date();
    private final static String format = "{0,date} {0,time}";
    private MessageFormat formatter;

    private Object args[] = new Object[1];

    private boolean fShowTimeStamp = true;
    private boolean fShowRecordedMessage = true;
    private boolean fShowSourceMethod = true;
    private boolean fShowDirectory = true;
    private boolean fShowStackTrace = true;
    
    // Line separator string.  This is the value of the line.separator
    // property at the moment that the SimpleFormatter was created.
    private String lineSeparator = (String) java.security.AccessController.doPrivileged(
               new sun.security.action.GetPropertyAction("line.separator"));

    public SimpleFormatterForCircus(boolean showTimeStamp, boolean showRecordedMessage, 
            boolean showSourceMethod, boolean showDirectory, boolean showStackTrace) {
        fShowTimeStamp = showTimeStamp;
        fShowRecordedMessage = showRecordedMessage;
        fShowSourceMethod = showSourceMethod;
        fShowDirectory = showDirectory;
        fShowStackTrace = showStackTrace;
    }
    
    /**
     * Format the given LogRecord.
     * @param record the log record to be formatted.
     * @return a formatted log record
     */
    public synchronized String format(LogRecord record) {
	StringBuffer sb = new StringBuffer();
	if (fShowTimeStamp) {
            // Minimize memory allocations here.
            dat.setTime(record.getMillis());
            args[0] = dat;
            StringBuffer text = new StringBuffer();
            if (formatter == null) {
                formatter = new MessageFormat(format);
            }
            formatter.format(args, text, null);
            sb.append(text);
            sb.append(" ");
        }
        if (fShowSourceMethod) {
            if (record.getSourceClassName() != null) {	
                sb.append(record.getSourceClassName());
            } else {
                sb.append(record.getLoggerName());
            }
            if (record.getSourceMethodName() != null) {	
                sb.append(" ");
                sb.append(record.getSourceMethodName());
            }
            sb.append(lineSeparator);
        }
        if (fShowRecordedMessage) {
            String message = formatMessage(record);
            sb.append(record.getLevel().getLocalizedName());
            sb.append(": ");
            sb.append(message);
            sb.append(lineSeparator);
        }
        if (fShowStackTrace) {
            if (record.getThrown() != null) {
                try {
                    StringWriter sw = new StringWriter();
                    PrintWriter pw = new PrintWriter(sw);
                    record.getThrown().printStackTrace(pw);
                    pw.close();
                    sb.append(sw.toString());
                } catch (Exception ex) {
                }
            }
        }
	return sb.toString();
    }
}
}


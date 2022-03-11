
/*
ParseErrorLogging.java
 *
Created on 05 February 2007, 15:21
 *
To change this template, choose Tools | Template Manager
and open the template in the editor.
 */
package net.sourceforge.czt.parser.circus;

//~--- non-JDK imports --------------------------------------------------------

import net.sourceforge.czt.parser.circus.SpecialLatexParser
    .SimpleFormatterForCircus;
import net.sourceforge.czt.util.CztLogger;

//~--- JDK imports ------------------------------------------------------------

import java.io.IOException;

import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Filter;
import java.util.logging.Formatter;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;

//~--- classes ----------------------------------------------------------------

/**
 *
 * @author leo
 */
public class ParseErrorLogging {
    public final static boolean SHOW_TIMESTAMP        = true;
    public final static boolean SHOW_STACK_TRACE      = true;
    public final static boolean SHOW_SOURCE_METHOD    = false;
    public final static boolean SHOW_RECORDED_MESSAGE = true;
    public final static boolean SHOW_DIRECTORY        = false;

    //~--- fields -------------------------------------------------------------

    private final ConsoleHandler           consoleHandler_;
    private Level                          logLevel_;
    private Logger                         logger_;
    private final Filter                   nameFilter_;
    private final SimpleFormatterForCircus sfc_;

    //~--- constructors -------------------------------------------------------

    public ParseErrorLogging() {
        this(Parser.class, Level.ALL);
    }

    /** Creates a new instance of ParseErrorLogging
     * @param parserCls
     * @param logLevel
     */
    public ParseErrorLogging(Class<?> parserCls, Level logLevel) {
        sfc_ = new SimpleFormatterForCircus(SHOW_TIMESTAMP,
                SHOW_RECORDED_MESSAGE, SHOW_SOURCE_METHOD, SHOW_DIRECTORY,
                SHOW_STACK_TRACE);
        nameFilter_     = new NameFilter();
        consoleHandler_ = createConsoleHandler(nameFilter_, sfc_);
        setLogLevel(logLevel);
        setLogger(parserCls);

        /*
         * logger_ = CztLogger.getLogger(KeywordScanner.class);
         * logger_ = CztLogger.getLogger(Latex2Unicode.class);
         * logger_ = CztLogger.getLogger(LatexMarkupParser.class);
         * logger_ = CztLogger.getLogger(LatexParser.class);
         * logger_ = CztLogger.getLogger(Parser.class);
         * logger_ = CztLogger.getLogger(net.sourceforge.czt.print.circus.Unicode2Latex.class);
         * logger_ = CztLogger.getLogger(UnicodeParser.class);
         */
    }

    //~--- methods ------------------------------------------------------------

    private ConsoleHandler createConsoleHandler(Filter nf, Formatter f) {
        assert (nf != null) && (f != null);

        ConsoleHandler ch = new ConsoleHandler();

        ch.setLevel(Level.ALL);
        ch.setFilter(nf);
        ch.setFormatter(f);

        return ch;
    }

    private FileHandler createFileHandler(String fileName, Filter nf,
            Formatter f) {
        assert (fileName != null) && (nf != null) && (f != null);

        FileHandler fh = null;

        try {
            fh = new FileHandler(fileName + ".log");
            fh.setLevel(Level.ALL);
            fh.setFilter(nf);
            fh.setFormatter(f);
        } catch (IOException e) {}

        return fh;
    }

    //~--- set methods --------------------------------------------------------

    public final void setLogLevel(Level logLevel) {
        assert logLevel != null;
        logLevel_ = logLevel;
    }

    public final void setLogger(Class<?> parserCls) {
        assert parserCls != null;
        logger_ = CztLogger.getLogger(parserCls);
        logger_.setLevel(logLevel_);
        logger_.addHandler(consoleHandler_);
        logger_.addHandler(createFileHandler(parserCls.getName(), nameFilter_,
                sfc_));

        /*
         * System.out.println("Logger has " + logger_.getHandlers().length + " handlers as:");
         * for(Handler h : logger_.getHandlers()) {
         * System.out.println(h.getClass().getName());
         * }
         */
    }

    //~--- inner classes ------------------------------------------------------

    public static class NameFilter implements Filter {
        @Override
        public boolean isLoggable(LogRecord record) {
            String message = record.getMessage();

            // If the mssage have "c:....\/..." remove the path
            int cidx     = message.toUpperCase().indexOf("\"C:");
            int slashidx = message.lastIndexOf('/');

            slashidx = (slashidx == -1)
                       ? message.lastIndexOf('\\')
                       : -1;

            int quoteidx = message.lastIndexOf("\",");

            if ((cidx != -1) && (slashidx != -1) && (quoteidx != -1)
                    && (cidx < slashidx) && (slashidx < quoteidx)
                    && (quoteidx < message.length())) {
                String msg =

                // Next token is (..... in
                message.substring(0, cidx) +

                // filename.tex
                message.substring(slashidx + 1, quoteidx) +

                // ,  .....).
                message.substring(quoteidx + 1);

                record.setMessage(msg);
            }

            return true;
        }
    }
}
/*
 * CZT2ZEves.java
 *
 * Created on 15 September 2005, 09:56
 */

package net.sourceforge.czt.zeves;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.URL;
import java.net.UnknownHostException;
import java.rmi.UnmarshalException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Properties;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.SourceLocator;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.zeves.TypeCheckUtils;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;


/**
 *
 * @author leo
 */
public class CZT2ZEves {

    public static final String DEFAULT_ADDRESS = "127.0.0.1";
    public static final String DEFAULT_PORT    = "6789";
    private static final boolean DEBUG = false;

    /** Creates a new instance of CZT2ZEves */
    public CZT2ZEves() {
    }
    
    public static void main(String[] args) throws CommandException, FileNotFoundException, ParseException, UnmarshalException, IOException {
        if (args.length >= 1) {
            if (args.length > 1 && args[0].startsWith("-print")) {
                List<String> result = runPrinter(args[1], args[0].equals("-printAll"), DEBUG);
                if (DEBUG) { System.out.println(result.size() + " Z/EVES command(s) created:\n"); }
                for(String s : result) {
                    System.out.println(s);
                }
            } else if (args[0].equals("-run")) {
                String address = null;
                String server = null;
                Integer port = null;
                if (args.length > 1)
                  server = args[1];
                else
                {
                  Properties zevesp = new Properties();
                  String path = System.getProperty("user.dir", ".");
                  try
                  {   
                    String filename = path + "/zeves.properties";
                    FileInputStream fis = new FileInputStream(new File(filename));
                    try {
                      zevesp.load(fis);
                    } finally {
                      fis.close();
                    }
                  } catch (IOException e)
                  {        
                    //URL url = CZT2ZEves.class.getResource("net/sourceforge/czt/zeves/zeves.properties");
                    URL url = CZT2ZEves.class.getResource("./zeves.properties");
                    if (url != null) {
                      InputStream inputStream = url.openStream();
                      try {
                        zevesp.load(inputStream);
                      } finally {
                        inputStream.close();
                      }
                    } else
                      throw e;
                  }
                  server = zevesp.getProperty("ZEVES_EXECUTABLE");
                  address = zevesp.getProperty("ZEVES_ADDRESS", DEFAULT_ADDRESS);
                  port = Integer.valueOf(zevesp.getProperty("ZEVES_PORT", DEFAULT_PORT));
                }
                if (args.length > 3)
                  port = Integer.valueOf(args[3]);
                if (args.length > 2)
                  address = args[2];
                assert server != null && address != null && port != null;
                runZEves(server, address, port);
            } else
                System.out.println("Usage: '-print filename.tex', '-run' with properties file, or -run server addr port'");
        } else
            System.out.println("Usage: '-print filename.tex', '-run' with properties file, or '-run server addr port'");
    }
    
    public static List<String> runPrinter(String filename, boolean printNarrParaAsComment, boolean debug)
    throws CommandException, FileNotFoundException, ParseException, UnmarshalException, IOException
    {
        SectionManager manager = new SectionManager(Dialect.ZEVES);
        List<String> result;
        Source source = new FileSource(filename);
        File file = new File(filename);
        String sourceName = SourceLocator.getSourceName(file.getName());
        while (sourceName.lastIndexOf(".") != -1)
          sourceName = sourceName.substring(0, sourceName.lastIndexOf("."));
        SourceLocator.addCZTPathFor(file, manager);
        manager.put(new Key<Source>(sourceName, Source.class), source);
        Spec term = manager.get(new Key<Spec>(sourceName, Spec.class));//ParseUtils.parse(new FileSource(filename), manager);
        List<? extends ErrorAnn> errors = TypeCheckUtils.typecheck(term, manager);
        Iterator<? extends ErrorAnn> it = errors.iterator();
        int foundWarnings = 0;
        while (it.hasNext())
        {
          if (it.next().getErrorType().equals(ErrorType.WARNING))
          {
            foundWarnings++;
            it.remove();
          }
        }
        if (debug && foundWarnings != 0)
        {
          System.out.println("Found " + foundWarnings + " warnings. They are being ignored.");
        }
        if (errors.isEmpty())
        {
            result = specToZEvesXML(term, manager, printNarrParaAsComment);
        } else {
            result = new ArrayList<String>(errors.size()+1);
            result.add("ERRORS");
            System.out.println("We expect a well-typed specification for Z/EVES translation.");
            System.out.println(errors.size() + " error(s) found:");
            for(ErrorAnn ea : errors) 
            {
                assert ea.getErrorType().equals(ErrorType.ERROR);
                result.add(ea.toString());
            }            
        }      
        return result;
    }
    
    public static void runZEves(String server, String address, int port) throws IOException {
        ZEvesServer zEvesServer = new ZEvesServer(server, port);
        zEvesServer.start();


        ZEvesApi api = new ZEvesApi(address, port);
        boolean connected = api.tryConnecting(3);//3 retries

        if (!connected)
          zEvesServer.stop();
        else
        {

        }

        api.disconnect();
        zEvesServer.stop();

        Socket zevesSocket = null;
        PrintWriter out = null;
        BufferedReader in = null;
        BufferedReader stdIn = null;
        try {
          try {
              zevesSocket = new Socket(address, Integer.valueOf(port));
              out = new PrintWriter(zevesSocket.getOutputStream(), true);
              in = new BufferedReader(new InputStreamReader(zevesSocket.getInputStream()));
          } catch (UnknownHostException e) {
              System.err.println("Don't know about host: " + address + " at port " + port);
              System.exit(1);
          } catch (IOException e) {
              System.err.println("Could not get I/O for the connection to: " + address + " at port " + port);
              System.exit(1);
          }
          stdIn = new BufferedReader(new InputStreamReader(System.in));
          System.out.print("zevesClient>");
          String userInput = stdIn.readLine();
          while (userInput != null) {
              out.println(userInput);
              StringBuilder response = new StringBuilder();
              String zevesIn = in.readLine();
              while (zevesIn != null && (zevesIn.equals("</zoutput>") || zevesIn.equals("</zerrort>"))) {
                  response.append(zevesIn);
                  zevesIn = in.readLine();
              }
              System.out.println("zevesClient>\n\t" + response.toString());
              System.out.print("zevesClient>");
              userInput = stdIn.readLine();
          }
        } finally {
          if (out != null) { out.close(); }
          if (in != null) { in.close(); }
          if (stdIn != null) { stdIn.close(); }
          if (zevesSocket != null) { zevesSocket.close(); }
        }
    }
    
    private static final CZT2ZEvesPrinter sZEvesPrinter = new CZT2ZEvesPrinter(null/*...*/);
    
    /**
     * Prints the given term in Z/EVES XML format, provided it is a paragraph, predicate, declaration, or expression.
     * Although typeannotations are not needed for translation, we assume the given terms are well-typed.
     * This assumption can be weakened provided one implements a Z/EVES XML output to CZT AST parser.
     */
    public static String termToZEvesXML(Term term, SectionInfo si, boolean printNarrParaAsComment) {
        return sZEvesPrinter.print(term, si, printNarrParaAsComment);
    }
    
    /**
     * Prints all the contenmts of the given specification and its sections a list of Z/EVES
     * strings to be sent through the Z/EVES server one by one.
     * Although typeannotations are not needed for translation, we assume the given terms are well-typed.
     * This assumption can be weakened provided one implements a Z/EVES XML output to CZT AST parser.
     */
    public static List<String> specToZEvesXML(Spec term, SectionInfo si, boolean printNarrParaAsComment) {
        return sZEvesPrinter.printSpec(term, si, printNarrParaAsComment);
    }
}
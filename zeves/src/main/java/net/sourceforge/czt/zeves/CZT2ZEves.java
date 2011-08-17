/*
 * CZT2ZEves.java
 *
 * Created on 15 September 2005, 09:56
 */

package net.sourceforge.czt.zeves;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.UnknownHostException;
import java.rmi.UnmarshalException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
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
    
    /** Creates a new instance of CZT2ZEves */
    public CZT2ZEves() {
    }
    
    public static void main(String[] args) throws CommandException, FileNotFoundException, ParseException, UnmarshalException, IOException {
        if (args.length > 1) {
            if (args[0].equals("-print")) {
                List<String> result = runPrinter(args[1]);
                System.out.println(result.size() + " Z/Eves command(s) created:\n");
                for(String s : result) {
                    System.out.println(s);
                }
            } else if (args[0].equals("-run")) {
                String address = args[1];
                String port = args[2];
                runZEvesServer(address, port);
            } else
                System.out.println("Usage: '-print filename.tex', or '-run addr port'");
        } else
            System.out.println("Usage: '-print filename.tex', or '-run addr port'");
    }
    
    public static List<String> runPrinter(String filename)
    throws CommandException, FileNotFoundException, ParseException, UnmarshalException, IOException
    {
        SectionManager manager = new SectionManager("zeves");
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
        if (foundWarnings != 0)
        {
          System.out.println("Found " + foundWarnings + " warnings. They are being ignored.");
        }
        if (errors.isEmpty())
        {
            result = specToZEvesXML(term, manager);            
        } else {
            result = new ArrayList<String>();
            result.add("ERRORS");
            System.out.println("We expect a well-typed specification for Z/Eves translation.");
            System.out.println(errors.size() + " error(s) found:");
            for(ErrorAnn ea : errors) 
            {
                assert ea.getErrorType().equals(ErrorType.ERROR);
                result.add(ea.toString());
            }            
        }      
        return result;
    }
    
    public static void runZEvesServer(String address, String port) throws IOException {
        Socket zevesSocket = null;
        PrintWriter out = null;
        BufferedReader in = null;
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
        BufferedReader stdIn = new BufferedReader(new InputStreamReader(System.in));
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
        out.close();
        in.close();
        stdIn.close();
        zevesSocket.close();
    }
    
    private static final CZT2ZEvesPrinter sZEvesPrinter = new CZT2ZEvesPrinter(null/*...*/);
    
    /**
     * Prints the given term in Z/Eves XML format, provided it is a paragraph, predicate, declaration, or expression.
     * Although typeannotations are not needed for translation, we assume the given terms are well-typed.
     * This assumption can be weakened provided one implements a Z/Eves XML output to CZT AST parser.
     */
    public static String termToZEvesXML(Term term, SectionInfo si) {
        return sZEvesPrinter.print(term, si);
    }
    
    /**
     * Prints all the contenmts of the given specification and its sections a list of Z/Eves
     * strings to be sent through the Z/Eves server one by one.
     * Although typeannotations are not needed for translation, we assume the given terms are well-typed.
     * This assumption can be weakened provided one implements a Z/Eves XML output to CZT AST parser.
     */
    public static List<String> specToZEvesXML(Spec term, SectionInfo si) {
        return sZEvesPrinter.printSpec(term, si);
    }
}
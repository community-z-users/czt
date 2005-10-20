/*
 * CZT2ZEves.java
 *
 * Created on 15 September 2005, 09:56
 */

package net.sourceforge.czt.zeves;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.UnknownHostException;

/**
 *
 * @author leo
 */
public class CZT2ZEves {
    
    /** Creates a new instance of CZT2ZEves */
    public CZT2ZEves() {
    }
    
    public static void main(String[] args) throws IOException {

        assert args.length >= 2;
        Socket zevesSocket = null;
        PrintWriter out = null;
        BufferedReader in = null;

        try {
            zevesSocket = new Socket(args[0], Integer.valueOf(args[1]));
            out = new PrintWriter(zevesSocket.getOutputStream(), true);
            in = new BufferedReader(new InputStreamReader(zevesSocket.getInputStream()));
        } catch (UnknownHostException e) {
            System.err.println("Don't know about host: " + args[0]);
            System.exit(1);
        } catch (IOException e) {
            System.err.println("Couldn't get I/O for the connection to: " + args[0]);
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
}
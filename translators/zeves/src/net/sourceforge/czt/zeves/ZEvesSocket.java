/*
 * ZEvesSocket.java
 *
 * Created on 13 October 2005, 09:40
 */

package net.sourceforge.czt.zeves;

import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.UnknownHostException;
import java.text.MessageFormat;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;

/**
 *
 * @author leo
 */
public class ZEvesSocket {
    
    private boolean fConnected;
    private boolean fAutoFlushZEvesOut;
    private boolean fNeedsReconnection;
    
    private int fPort;
    private String fHost;
    private Socket fZEvesServer;
    private PrintWriter fZEvesOut;
    private BufferedReader fStdIn;
    private BufferedReader fZEvesIn;
    
    public static final int ZEVES_SERVER_PORT = 6789;
    
    public static final int EXITCODE_UNKNOWN_HOST = 1;
    
    public ZEvesSocket() {
        this(null);
    }
            
    /** Creates a new instance of ZEvesEvaluator */
    public ZEvesSocket(SectionInfo info) {
        fStdIn = null;
        fZEvesIn = null;
        fZEvesOut = null;
        fZEvesServer = null;        
        fStdIn = null;
        fConnected = false;
        fHost = null;
        fPort = ZEVES_SERVER_PORT;
        fAutoFlushZEvesOut = true;
        fNeedsReconnection = false;                
    }
    
    private String getHostInfo() {
        return MessageFormat.format("\"{0}\"@{1}.", String.valueOf(fHost), String.valueOf(fPort));
    }
    
    protected void finalize() throws Throwable {
        close();        
    }    
    
    protected void connect() throws ZEvesServerConnectionException {        
        try {
            fZEvesServer = new Socket(fHost, fPort);            
        } catch (UnknownHostException e) {
            throw new ZEvesServerConnectionException("Unknown host " + String.valueOf(fHost) + 
                    " while trying to connect to the Z/Eves server.", e);            
        } catch (IOException f) {
            throw new ZEvesServerConnectionException("Could not connect to the Z/Eves server socket for host " + 
                    String.valueOf(fHost) + " at port " + fPort + ". Please check whether the Z/Eves server is" +
                    "on-line (i.e. Z/Eves started with the \"-api\" command line switch).", f);                        
        }
        try {
            try {
                fZEvesOut = new PrintWriter(fZEvesServer.getOutputStream(), fAutoFlushZEvesOut);            
            } catch (IOException e) {
                fZEvesServer.close();
                throw new ZEvesServerConnectionException("Could not open the output stream of the Z/Eves server " +
                        "socket connection to host " + getHostInfo(), e);                        
            }
            try {
                fZEvesIn = new BufferedReader(new InputStreamReader(fZEvesServer.getInputStream()));
            } catch (IOException e) {
                fZEvesServer.close();
                throw new ZEvesServerConnectionException("Could not open the input stream of the Z/Eves server " +
                        "socket connection to host " + getHostInfo(), e);                        
            }                    
        } catch (IOException f) {
            throw new ZEvesServerConnectionException("Could not close the Z/Eves server socket connection after failure " +
                    "to acquire its I/O stream to host " + getHostInfo(), f);                        
        }
	fStdIn = new BufferedReader(new InputStreamReader(System.in));
        fConnected = true;        	
    }    
    
    protected void close() throws ZEvesServerConnectionException {
        if (fConnected) {
            try {
                fStdIn.close();
                fZEvesIn.close();
                fZEvesOut.close();		
                fZEvesServer.close();        
            } catch (IOException e) {
                throw new ZEvesServerConnectionException("An I/O error occurred while trying to close the Z/Eves server socket " +
                        "connection and underlying buffers to host \"" + String.valueOf(fHost) + "\" at port " + fPort + ".", e);
            }
        }
    }
    
    protected void reconnect() throws ZEvesServerConnectionException {
        close();
        connect();
    }

    protected void processCommand() {
//        System.out.print("zevesClient>");
//	String userInput = stdIn.readLine();
//	while (userInput != null) {            
//	    out.println(userInput);                        
//            StringBuilder response = new StringBuilder();           
//            String zevesIn = in.readLine();
//            while (zevesIn != null && (zevesIn.equals("</zoutput>") || zevesIn.equals("</zerrort>"))) {
//                response.append(zevesIn);
//                zevesIn = in.readLine();
//            }
//	    System.out.println("zevesClient>\n\t" + response.toString());
//            System.out.print("zevesClient>");            
//            userInput = stdIn.readLine();
//	}
    }
    
    public String setHost(String host) {
        String old = fHost;
        fHost = host;
        return old;
    }
    
    public String getHost() {
        return fHost;
    }
    
    public int setPort(int port) {
        int old = fPort;
        fPort = port;
        return old;
    }
    
    public int getPort() {
        return fPort;
    }
    
    public boolean getAutoFlushZEvesOut() {
        return fAutoFlushZEvesOut;
    }
    
    public boolean toogleAutoFlushZEvesOut() {
        fAutoFlushZEvesOut = !fAutoFlushZEvesOut;
        fNeedsReconnection = true;
        return fAutoFlushZEvesOut;
    }
}

/*
 * ZEvesSocket.java
 *
 * Created on 13 October 2005, 09:40
 */

package net.sourceforge.czt.zeves;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.UnknownHostException;
import java.text.MessageFormat;
import java.util.Arrays;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;
import net.sourceforge.czt.zeves.ZEvesServerConnectionException;

/**
 * This class encapsulates a Java Socket that connects with the underlying Z/EVES server.
 * It allows one to connect to the server and perform specific command or run proof scripts.
 * The usage is as follows:
 * <ul>
 *       <li>1 Create a ZEvesSocket</li>
 *       <li>2 Set the address and port if the Z/EVES server is not on localhost:6789</li> 
 *       <li>3 Set the context as the section info and the section to load or the standard_toolkit by default</li>
 *       <li>4 Now it is possible to connect to the server and load the default context.</li>
 * </ul>
 * @author leo
 * @deprecated use {@link ZEvesApi}
 * @see ZEvesApi
 */
@Deprecated
public class ZEvesSocket {

	class ZEvesResponse { ZEvesResponse(String foo) {} // dummy
	}
	
//    private boolean fConnected;
    private boolean fAutoFlushZEvesOut;
//    private boolean fNeedsReconnection;
    
    private int fPort;
    private String fHost;
    private Socket fZEvesServer;
    private PrintWriter fZEvesOut;
    private BufferedReader fStdIn;
    private BufferedReader fZEvesIn;
    
    private ZSect fZSect;    
//    private ZEvesResponse fResponse;
    private SectionInfo fSectInfo;
    private final CZT2ZEvesPrinter fPrinter;    
    
    public static final int DEFAULT_ZEVES_SERVER_PORT = 6789;
    public static final String DEFAULT_ZEVES_HOST_ADDRESS = "127.0.0.1";        
    public static final boolean DEFAULT_AUTOFLUSH_ZEVES_OUT = true;
    
    public ZEvesSocket() {
        this(DEFAULT_AUTOFLUSH_ZEVES_OUT);
    }
            
    /** Creates a new instance of ZEvesEvaluator */
    public ZEvesSocket(boolean autoFlushZEvesOut) {                
        clearReferences();
        fZSect = null;
        fSectInfo = null;
        fPrinter = new CZT2ZEvesPrinter(null);
        fAutoFlushZEvesOut = autoFlushZEvesOut;    
        fHost = DEFAULT_ZEVES_HOST_ADDRESS;//InetAddress.getLocalHost();
        fPort = DEFAULT_ZEVES_SERVER_PORT;        
    }
    
    protected String getHostInfo() {
        return MessageFormat.format("\"{0}\"@{1}.", String.valueOf(fHost), String.valueOf(fPort));
    }
    
    private void clearReferences() {
        fStdIn = null;
        fZEvesIn = null;
        fZEvesOut = null;
        fZEvesServer = null;            
//        fResponse = null;
    }
    
    protected void finalize() throws Throwable {
        if (isConnected())
            close();        
    }        
    
    /**
     * Called upon (re)connection. It must has a loaded context prior to execution 
     * otherwise a ZEvesServerConnectionException is thrown.
     */
    public void loadContext() throws ZEvesServerConnectionException {
        if (getContext() != null) {
            List<String> zSectContext = fPrinter.printZSect(fZSect);
            for(String cmd : zSectContext) {
                processCommand(cmd);                
            }
        }
    }
    
    private boolean isQuitCommand(String cmd) {
        return cmd != null && (cmd.equals("<cmd name=\"quit\"></cmd>") || cmd.equals("<cmd name=\"quit\"/>"));
    }
    
    public ZEvesResponse processCommand(String cmd) throws ZEvesServerConnectionException {
        if (!isConnected())
            throw new ZEvesServerConnectionException("Cannot process a Z/EVES command. Connect to the Z/EVES server first.");
        fZEvesOut.println(cmd);        
        ZEvesResponse result;
        // Z/EVES does return </zoutput> rather than <zouput/> upon quitting!
        if (!isQuitCommand(cmd)) {
            StringBuilder response = new StringBuilder("");
            try {
                String zevesIn = fZEvesIn.readLine();                
                response.append(zevesIn);            
            } catch(IOException e) {
                throw new ZEvesServerConnectionException("An I/O exception happened while trying to read the output from the Z/EVES server. See cause for details.", e);
            }
            result = new ZEvesResponse(response.toString());
        } else {
            result = new ZEvesResponse("<zoutput></zoutput>");
        }
        return result;
    }    
    
    public String setHost(String host) throws ZEvesServerConnectionException {
        if (fHost.equals(host))
            return host;
        else {                        
            if (host == null)
                throw new NullPointerException("Invalid (null) host name.");
            String old = fHost;
            fHost = host;
            if (isConnected())
                reconnect();
            return old;
        }
    }
    
    public String getHost() {
        return fHost;
    }
    
    public int setPort(int port) throws ZEvesServerConnectionException {
        if (fPort == port) 
            return port;
        else {
            int old = fPort;
            fPort = port;
            if (isConnected())
                reconnect();
            return old;
        }
    }
    
    public int getPort() {
        return fPort;
    }
    
    public boolean getAutoFlushZEvesOut() {
        return fAutoFlushZEvesOut;
    }
    
    public boolean hasContext() {
        return fSectInfo != null && fZSect != null;
    }
    
    public SectionInfo getContext() throws ZEvesServerConnectionException {
        if (fSectInfo != null)            
            throw new ZEvesServerConnectionException("Invalid section context for Z/EVES socket");
        return fSectInfo;
    }
    
    public ZSect getZSect() throws ZEvesServerConnectionException {
        if (!hasContext())
            throw new ZEvesServerConnectionException("Cannot retrieve Z section due to an invalid section context for Z/EVES socket");
        return fZSect;
    }
    
    public CZT2ZEvesPrinter getZPrinter() {
        return fPrinter;
    }
        
    public void setContext(SectionInfo info) throws ZEvesServerConnectionException {
        setContext("standard_toolkit", info);
    }
    
    public void setContext(String sectName, SectionInfo info) throws ZEvesServerConnectionException {
        fZSect = null;
        fSectInfo = info;
        fPrinter.setSectionInfo(info);
        if (fSectInfo != null) {
            try {
                fZSect = fSectInfo.get(new Key<ZSect>(sectName, ZSect.class));
            } catch(CommandException e) {
                throw new ZEvesServerConnectionException("Could not retrieve Z section named " + sectName + 
                        "withing the given context. See cause for details.", e);
            }
            if (isConnected()) {
                reconnect();                    
            }
        }
    }
    
    public boolean isConnected() {
        boolean result = fZEvesServer != null && fZEvesIn != null && fZEvesOut != null && fStdIn != null;
        if (result) {
            result = fZEvesServer.isBound(); /*&& fZEvesIn.ready() && fStdIn.ready()*/
        }
        return result;
    }
    
    public void close() throws ZEvesServerConnectionException {
        if (!isConnected())
            throw new ZEvesServerConnectionException("Connection with Z/EVES server has not yet been established.",
                    new IllegalStateException("Cannot close a connection that has not yet been openned. Try to connect first."));        
        try {
            // try closing nicely...
            try {
                processCommand("<cmd name=\"quit\"></cmd>");
            } catch(ZEvesServerConnectionException f) {
                // ignore problems and carry on forcing the closure then.
            }
            fStdIn.close();
            fZEvesIn.close();
            fZEvesOut.close();		
            fZEvesServer.close();
            clearReferences();
        } catch (IOException e) {
            clearReferences();
            throw new ZEvesServerConnectionException("An I/O error occurred while trying to close the Z/EVES server socket " +
                    "connection and underlying buffers to host \"" + String.valueOf(fHost) + "\" at port " + fPort + ".", e);
        }        
    }
    
    public void connect() throws ZEvesServerConnectionException {        
        if (isConnected())
            throw new ZEvesServerConnectionException("Evaluator already connected with Z/EVES server.", 
                    new IllegalStateException("Evaluator already connected. Try closing and reconnecting instead."));
        try {
            fZEvesServer = new Socket(fHost, fPort);            
        } catch (UnknownHostException e) {
            throw new ZEvesServerConnectionException("Unknown host " + String.valueOf(fHost) + 
                    " while trying to connect to the Z/EVES server.", e);            
        } catch (IOException f) {
            throw new ZEvesServerConnectionException("Could not connect to the Z/EVES server socket for host " + 
                    String.valueOf(fHost) + " at port " + fPort + ". Please check whether the Z/EVES server is" +
                    "on-line (i.e. Z/EVES started with the \"-api\" command line switch).", f);                        
        }
        try {
            try {
                fZEvesOut = new PrintWriter(fZEvesServer.getOutputStream(), fAutoFlushZEvesOut);            
            } catch (IOException e) {
                fZEvesServer.close();
                throw new ZEvesServerConnectionException("Could not open the output stream of the Z/EVES server " +
                        "socket connection to host " + getHostInfo(), e);                        
            }
            try {
                fZEvesIn = new BufferedReader(new InputStreamReader(fZEvesServer.getInputStream()));
            } catch (IOException e) {
                fZEvesServer.close();
                throw new ZEvesServerConnectionException("Could not open the input stream of the Z/EVES server " +
                        "socket connection to host " + getHostInfo(), e);                        
            }                    
        } catch (IOException f) {
            throw new ZEvesServerConnectionException("Could not close the Z/EVES server socket connection after failure " +
                    "to acquire its I/O stream to host " + getHostInfo(), f);                        
        }
	fStdIn = new BufferedReader(new InputStreamReader(System.in));
        /*loadContext();*/
    }
    
    public void reconnect() throws ZEvesServerConnectionException {
        close();
        connect();
        loadContext();
    }
    
    public String toString() {        
        return "Z/EVES server " + (isConnected() ? "connected" : "disconnected") + "(" + getHostInfo() + ").";
    }
    
    public List<String> translate(Term term) throws ZEvesIncompatibleASTException {
        List<String> result;
        if (term instanceof Spec)
            result = fPrinter.printSpec((Spec)term);
        else if (term instanceof ZSect)
            result = fPrinter.printZSect((ZSect)term);
        else
            result = Arrays.asList(fPrinter.print(term));        
        return result;
    }
}

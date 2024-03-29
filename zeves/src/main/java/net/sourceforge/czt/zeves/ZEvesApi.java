
package net.sourceforge.czt.zeves;

import java.io.*;
import net.sourceforge.czt.util.CztLogger;
import java.net.ConnectException;
import java.net.Socket;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import javax.xml.bind.JAXBException;
import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.response.form.ZEvesNumber;
import net.sourceforge.czt.zeves.response.form.ZEvesResponseString;
import net.sourceforge.czt.zeves.response.para.ZEvesTheorem;
import net.sourceforge.czt.zeves.response.ZEvesError;
import net.sourceforge.czt.zeves.response.ZEvesOutput;
import net.sourceforge.czt.zeves.response.ZEvesResponseReader;

import static net.sourceforge.czt.zeves.z.ZEvesXMLPatterns.ZEVES_COMMAND;

/**
 * This class is provides calls to Z/EVES XML-based API, where communication is
 * done via sockets. It allows one to connect to the Z/EVES server (e.g. running
 * on localhost:6789 by default) and perform specific commands or run proof
 * scripts.
 * 
 * Z/EVES responses are translated into Java objects, which are returned to the
 * caller. This class provides synchronization on writing/reading to the socket,
 * so can be used in a parallel execution.
 * 
 * Use available class methods to perform commands or send the preformatted XML
 * commands via {@link #send(String)}.
 * 
 * @author Andrius Velykis
 */
public class ZEvesApi
{

  public enum ZEvesTheoremType {
    /**
     * Proof obligation, either generated by Z/EVES or a theorem in the
     * specification
     */
    GOAL,

    /**
     * Axiom, generated by Z/EVES for various data types
     */
    AXIOM
  }

  /**
   * A lock to synchronize writing commands, e.g. we should be able to send
   * "abort" while another thread is waiting for response from Z/EVES and
   * therefore holding the main synchronized lock (on
   * {@link #processCommand(String)}).
   */
  private final Object writeLock = new Object();

  private final String zEvesServerAddress;

  private final int port;

  private Socket zEvesSocket = null;

  private PrintWriter zEvesOut = null;

  private BufferedReader zEvesIn = null;
  
  private BufferedWriter debugLog_ = null;
  
  private int commandsSent_ = 0;

  /**
   * Per-thread storage for response XML reader, which is not thread-safe
   */
  private final ThreadLocal<ZEvesResponseReader> responseReader = new ThreadLocal<ZEvesResponseReader>();

  public ZEvesApi(String zEvesServerAddress, int port)
  {
    super();

    this.zEvesServerAddress = zEvesServerAddress;
    this.port = port;
    commandsSent_ = 0;
  }

  public String getServerAddress()
  {
    return zEvesServerAddress;
  }

  public int getPort()
  {
    return port;
  }

  public void connect() throws ConnectException, IOException
  {

    zEvesSocket = new Socket(zEvesServerAddress, Integer.valueOf(port));
    // keep alive, otherwise closes and Z/EVES dies (?)
    zEvesSocket.setKeepAlive(true);

    try {
      zEvesOut = new PrintWriter(zEvesSocket.getOutputStream(), true);
      zEvesIn = new BufferedReader(new InputStreamReader(zEvesSocket.getInputStream()));
      File file = new File("./zevesapi-debug.log");
      debugLog_ = new BufferedWriter(new FileWriter(file));
    }
    catch (IOException e) {
      close();
      throw e;
    }
    commandsSent_ = 0;
  }

  public void disconnect() throws IOException
  {
    if (isConnected()) {
      try {
        synchronized (writeLock) {
          // quit command does not produce output, so just send it
          zEvesOut.println(MessageFormat.format(ZEVES_COMMAND, "quit", ""));
          zEvesOut.flush();
          debugLog_.flush();
        }
      }
      catch (Exception ex) {
        // ignore and just close afterwards
      }
    }

    close();
  }

  public boolean connectRetry(int retries) throws IOException
  {
    assert retries > 0;
    int tries = 0;
    while (tries < retries) {
      try {
        connect();
      }
      catch (ConnectException e) {

        // cannot connect (socket not yet available), retry after 1 second
        try {
          Thread.sleep(1000);
        }
        catch (InterruptedException e1) {
        }

        tries++;
        continue;
      }

      // connected successfully
      return true;
    }

    return false;
  }

  public boolean tryConnecting(int retries) throws IOException
  {
    if (!isConnected()) {
      return connectRetry(retries);
    }
    return true;
  }

  public void close() throws IOException
  {

    if (zEvesIn != null) {
      zEvesIn.close();
      zEvesIn = null;
    }

    if (zEvesOut != null) {
      zEvesOut.close();
      zEvesOut = null;
    }

    if (zEvesSocket != null) {
      zEvesSocket.close();
      zEvesSocket = null;
    }
    
    if (debugLog_ != null)
    {
      debugLog_.close();
      debugLog_ = null;
    }
  }

  public boolean isConnected()
  {
    return zEvesSocket != null && zEvesOut != null && zEvesIn != null && zEvesSocket.isBound();
  }

  /**
   * Synchronize for multi-thread access
   * 
   * @param cmd
   * @return
   * @throws ZEvesException
   */
  private synchronized String processCommand(String cmd) throws ZEvesException
  {

    /*
     * TODO escape comments? E.g. try parsing the XML and check if it
     * contains non-comments. This is a problem, because if a comment is
     * sent, Z/EVES does not reply at all
     */

    checkConnected();

    synchronized (writeLock) {
      zEvesOut.println(cmd);
      zEvesOut.flush();
    }

    try {
      debugLog_.flush();
      return readZEvesResponse();
    }
    catch (IOException e) {
      throw new ZEvesException("I/O problems reading Z/EVES response: " + e.getMessage(), e);
    }
  }

  private String readZEvesResponse() throws IOException
  {
    StringBuilder response = new StringBuilder();

    String responseLine;
    do {

      responseLine = zEvesIn.readLine();

      if (responseLine == null) {
        break;
      }

      response.append(responseLine);

    }
    while (!responseLine.endsWith("</zoutput>") && !responseLine.endsWith("</zerror>")
        && !responseLine.endsWith("<zoutput/>") && !responseLine.endsWith("<zerror/>"));

    return response.toString();
  }

  private void checkConnected() throws ZEvesException
  {
    if (!isConnected()) {
      throw new ZEvesException("Z/EVES theorem prover is not connected.");
    }
  }
  
  /**
   * Sends a command to the server, formatted as specified in Z/EVES XML API
   * requirements.
   * 
   * @param command
   *            formatted Z/EVES XML command
   * @return result as Java object
   * @throws ZEvesException
   *             if command produced an error (zerror) or communication failed
   */
  public ZEvesOutput send(String command) throws ZEvesException
  {
    
    // escape custom unicode characters in the command
    command = ZEvesResponseReader.escapeUnicode(command);

    long startTime = System.currentTimeMillis();
    debug("Sending to Z/EVES: " + command);

    String resultStr = processCommand(command);

    long zevesTime = (System.currentTimeMillis() - startTime); 
    debug("Received result: " + resultStr);

    if (resultStr.isEmpty()) {
      throw new ZEvesException("No response received from Z/EVES.");
    }

    Object result;
    try {
      result = getResponseReader().readXml(resultStr);
    }
    catch (Exception e) {
      String msg = e.getMessage();
      if (msg == null) {
        // check cause
        Throwable cause = e.getCause();
        if (cause != null) {
          msg = cause.getMessage();
        }
      }
      throw new ZEvesException("Problems parsing Z/EVES response XML: " + msg, e,
          "Z/EVES XML response: " + resultStr + "\n\n" +
          "Command sent to Z/EVES: " + command);
    }

    ZEvesOutput output = checkError(result, command);
    //debug("Processed result: " + output.toString());

    commandsSent_++;
    long proofProcessing = ((System.currentTimeMillis() - startTime) - zevesTime); 
    debug("Proof execution  time (" + commandsSent_ + ") = " + zevesTime + "; " + (zevesTime/1000) + "ms");
    debug("Proof processing time (" + commandsSent_ + ") = " + proofProcessing + "; " + (proofProcessing/1000) + "ms");

    return output;
  }

  /**
   * The creation of ZEvesResponseReader is somewhat expensive, however it is
   * not thread safe, so using a ThreadLocal variable to store one reader per
   * thread.
   * 
   * @return
   * @throws JAXBException
   * @throws ParserConfigurationException
   * @throws SAXException
   */
  private ZEvesResponseReader getResponseReader() throws JAXBException,
      ParserConfigurationException, SAXException
  {

    ZEvesResponseReader reader = this.responseReader.get();
    if (reader == null) {
      reader = ZEvesResponseReader.createReader();
      this.responseReader.set(reader);
    }

    return reader;
  }

  private ZEvesOutput checkError(Object result, String commandSent) throws ZEvesException
  {
    if (result instanceof ZEvesError) {
      throw new ZEvesException((ZEvesError) result, "Command sent to Z/EVES: " + commandSent);
    }

    return (ZEvesOutput) result;
  }

  /**
   * Sends an abort command to stop executing current command. This can be
   * done asynchronously, while waiting for reply from Z/EVES. The executing
   * command still produces an output, even if it was aborted.
   */
  public void sendAbort()
  {

    if (!isConnected()) {
      return;
    }

    synchronized (writeLock) {
      // abort command does not produce output, so just send it
      zEvesOut.println(MessageFormat.format(ZEVES_COMMAND, "abort", ""));
      zEvesOut.flush();
    }
  }

  /**
   * Sends the indicated command to the server, passing arguments as command
   * contents.
   * 
   * @param cmdName
   *            Z/EVES XML command name
   * @param args
   *            arguments to be passed as command contents. They will be
   *            separated by white-space.
   * @return result as Java object
   * @throws ZEvesException
   *             if command produced an error (zerror) or communication failed
   */
  public ZEvesOutput sendCommand(String cmdName, String... args) throws ZEvesException
  {
    String command = MessageFormat.format(ZEVES_COMMAND, cmdName, concat(Arrays.asList(args), " "));
    return send(command);
  }

  @SuppressWarnings("unchecked")
  private <T> T sendCommand(String cmdName, Class<? extends T> resultType, String... args)
      throws ZEvesException
  {

    ZEvesOutput output = sendCommand(cmdName, args);

    if (resultType == null) {
      // no reply expected
      return null;
    }

    if (resultType == Integer.class) {
      return (T) getInteger(output, output.getFirstResult());
    }

    if (resultType == String.class) {
      return (T) getString(output, output.getFirstResult());
    }

    if (resultType == Boolean.class) {
      return (T) getBoolean(output, output.getFirstResult());
    }

    if (resultType == ZEvesOutput.class) {
      T val = (T) output;
      return val;
    }

    throw new ZEvesException("Unsupported Z/EVES response type: " + resultType.getClass().getName());
  }

  private Integer getInteger(ZEvesOutput output, Object result) throws ZEvesException
  {

    if (result == null) {
      throw new ZEvesException("Invalid integer result received from Z/EVES. " + output.toString());
    }

    String valStr = ((ZEvesNumber) result).getValue();

    try {
      return Integer.valueOf(valStr);
    }
    catch (NumberFormatException e) {
      throw new ZEvesException("Cannot parse the number in Z/EVES result: " + e.getMessage(), e);
    }
  }

  private String getString(ZEvesOutput output, Object result)
  {

    if (result == null) {
      CztLogger.getLogger(getClass()).warning(
          "Null string result received from Z/EVES. " + output.toString());
      return null;
    }

    if (result instanceof ZEvesName) {
      return ((ZEvesName) result).getIdent();
    }

    return ((ZEvesResponseString) result).getValue();
  }

  private Boolean getBoolean(ZEvesOutput output, Object result) throws ZEvesException
  {

    if (result == null) {
      throw new ZEvesException("Invalid boolean result received from Z/EVES. " + output.toString());
    }

    String valStr = ((ZEvesName) result).getIdent();
    return Boolean.valueOf(valStr);
  }

  private static String concat(Collection<?> list, String delimiter)
  {

    StringBuilder sb = new StringBuilder();

    String delim = "";
    for (Object i : list) {
      sb.append(delim).append(String.valueOf(i));
      delim = delimiter;
    }

    return sb.toString();
  }

  public int getHistoryLength() throws ZEvesException
  {
    return sendCommand("get-history-length", Integer.class);
  }

  public Object getHistoryElement(int paragraphNumber) throws ZEvesException
  {

    ZEvesOutput output = sendCommand("get-history-element", String.valueOf(paragraphNumber));
    return output.getFirstResult();
  }

  public Map<String, ZEvesTheoremType> getTheoremNames(int paragraphNumber) throws ZEvesException
  {

    ZEvesOutput output = sendCommand("get-theorem-names", String.valueOf(paragraphNumber));

    Map<String, ZEvesTheoremType> theoremNames = new LinkedHashMap<String, ZEvesTheoremType>();

    List<?> results = output.getResults();
    for (int index = 0; index < results.size() - 1; index += 2) {

      // theoremName and isGoal/Axiom comes in pairs
      String theoremName = getString(output, results.get(index));

      // axiom otherwise
      Boolean isGoal = getBoolean(output, results.get(index + 1));
      ZEvesTheoremType type = isGoal ? ZEvesTheoremType.GOAL : ZEvesTheoremType.AXIOM;

      theoremNames.put(theoremName, type);
    }

    return theoremNames;
  }

  /**
   * Queries Z/EVES for theorem contents.
   * 
   * @param theoremName
   *            name of theorem
   * @return Theorem definition as represented in Z/EVES, or null if the 
   *         theorem does not exist in Z/EVES
   * @throws ZEvesException
   *             if there are communications errors or Z/EVES errors
   */
  public ZEvesTheorem getTheorem(String theoremName) throws ZEvesException
  {

    ZEvesOutput output = sendCommand("get-theorem", theoremName);
    return (ZEvesTheorem) output.getFirstResult();
  }
  
  /**
   * Queries Z/EVES for the source paragraph (submitted by the user) introducing
   * the given name.
   * 
   * @param name
   *            name of Z/EVES construct
   * @return source paragraph, as counted in Z/EVES, that introduces the given
   *         name, or -1 if the name is unknown (or the name was introduced in the
   *         mathematical toolkit)
   * @throws ZEvesException
   *             if there are communications errors or Z/EVES errors
   */
  public int getNameSource(String name) throws ZEvesException
  {
    ZEvesOutput output = sendCommand("get-name-source", name);

    if (output != null && output.isEmpty()) {
      return -1;
    }
    
    return getInteger(output, output.getFirstResult());
  }
  
  public int getTheoremOrigin(String theoremName) throws ZEvesException
  {
    return sendCommand("get-theorem-origin", Integer.class, theoremName);
  }
  
  public List<String> getRulesMatchingPredicate(String goalName, int stepNumber, String predicate)
      throws ZEvesException
  {

    return getRulesMatchingTerm("get-rules-matching-predicate", goalName, stepNumber, predicate);
  }

  public List<String> getRulesMatchingExpression(String goalName, int stepNumber, String expr)
      throws ZEvesException
  {

    return getRulesMatchingTerm("get-rules-matching-expression", goalName, stepNumber, expr);
  }

  private List<String> getRulesMatchingTerm(String commandName, String goalName, int stepNumber,
      String term) throws ZEvesException
  {

    ZEvesOutput output = sendCommand(commandName, goalName, String.valueOf(stepNumber), term);
    List<String> rules = new ArrayList<String>(output.getResults().size());
    for (Object res : output.getResults()) {
      if (res instanceof ZEvesName) {
        rules.add(((ZEvesName) res).getIdent());
      }
    }

    return rules;
  }

  public String getCurrentGoalName() throws ZEvesException
  {
    return sendCommand("get-current-goal-name", String.class);
  }

  public boolean getGoalProvedState(String goalName) throws ZEvesException
  {
    return sendCommand("get-goal-proved-state", Boolean.class, goalName);
  }

  public int getGoalProofLength(String goalName) throws ZEvesException
  {
    return sendCommand("get-goal-proof-length", Integer.class, goalName);
  }

  public ZEvesOutput getGoalProofStep(String goalName, int stepNumber) throws ZEvesException
  {
    return sendCommand("get-goal-proof-step", goalName, String.valueOf(stepNumber));
  }

  public void reset() throws ZEvesException
  {
    sendCommand("reset");
  }

  public void undoBackTo(int paragraphNumber) throws ZEvesException
  {
    sendCommand("undo-back-to", String.valueOf(paragraphNumber));
  }

  public void undoBackThrough(int paragraphNumber) throws ZEvesException
  {

    // will use "back to" with one paragraph less
    paragraphNumber--;
    if (paragraphNumber < 1) {
      paragraphNumber = 1;
    }

    undoBackTo(paragraphNumber);
  }

  public void setCurrentGoalName(String goalName) throws ZEvesException
  {
    sendCommand("set-current-goal-name", goalName);
  }

  public ZEvesOutput sendProofCommand(String command) throws ZEvesException
  {
    return sendCommand("proof-command", command);
  }

  public void back() throws ZEvesException
  {
    sendProofCommand("back");
  }

  public void back(int numberOfSteps) throws ZEvesException
  {
    sendProofCommand("back " + String.valueOf(numberOfSteps));
  }

  public void retry() throws ZEvesException
  {
    sendProofCommand("retry");
  }

  private void debug(String msg)
  {
    System.out.println(msg);
    if (debugLog_ != null)
    {
      try
      {
        debugLog_.write(msg);
      }
      catch (IOException ex)
      {
        System.err.println("Could not log last msg due to an I/O error");
      }
    }
  }
}

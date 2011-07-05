package net.sourceforge.czt.zeves;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ConnectException;
import java.net.Socket;
import java.text.MessageFormat;
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
import net.sourceforge.czt.zeves.response.form.ZEvesString;
import net.sourceforge.czt.zeves.response.para.ZEvesTheorem;
import net.sourceforge.czt.zeves.response.ZEvesError;
import net.sourceforge.czt.zeves.response.ZEvesOutput;
import net.sourceforge.czt.zeves.response.ZEvesResponseReader;

import static net.sourceforge.czt.zeves.util.ZEvesXMLPatterns.ZEVES_COMMAND;

/**
 * This class is provides calls to Z/Eves XML-based API, where communication is
 * done via sockets. It allows one to connect to the Z/Eves server (e.g. running
 * on localhost:6789 by default) and perform specific commands or run proof
 * scripts.
 * 
 * Z/Eves responses are translated into Java objects, which are returned to the
 * caller. This class provides synchronization on writing/reading to the socket,
 * so can be used in a parallel execution.
 * 
 * Use available class methods to perform commands or send the preformatted XML
 * commands via {@link #send(String)}.
 * 
 * @author Andrius Velykis
 */
public class ZEvesApi {

	public enum ZEvesTheoremType {
		/**
		 * Proof obligation, either generated by Z/Eves or a theorem in the
		 * specification
		 */
		GOAL,
		
		/**
		 * Axiom, generated by Z/Eves for various data types
		 */
		AXIOM
	}

	/**
	 * A lock to synchronize writing commands, e.g. we should be able to send
	 * "abort" while another thread is waiting for response from Z/Eves and
	 * therefore holding the main synchronized lock (on
	 * {@link #processCommand(String)}).
	 */
	private final Object writeLock = new Object();

	private final String zEvesServerAddress;
	private final int port;

	private Socket zEvesSocket = null;
	private PrintWriter zEvesOut = null;
	private BufferedReader zEvesIn = null;

	/**
	 * Per-thread storage for response XML reader, which is not thread-safe
	 */
	private final ThreadLocal<ZEvesResponseReader> responseReader = 
			new ThreadLocal<ZEvesResponseReader>();

	
	public ZEvesApi(String zEvesServerAddress, int port) {
		super();

		this.zEvesServerAddress = zEvesServerAddress;
		this.port = port;
	}

	public String getServerAddress() {
		return zEvesServerAddress;
	}

	public int getPort() {
		return port;
	}

	public void connect() throws ConnectException, IOException {

		zEvesSocket = new Socket(zEvesServerAddress, Integer.valueOf(port));
		// keep alive, otherwise closes and Z/Eves dies (?)
		zEvesSocket.setKeepAlive(true);

		try {
			zEvesOut = new PrintWriter(zEvesSocket.getOutputStream(), true);
			zEvesIn = new BufferedReader(new InputStreamReader(zEvesSocket.getInputStream()));
		} catch (IOException e) {
			close();
			throw e;
		}
	}

	public void disconnect() throws IOException {
		if (isConnected()) {
			try {
				synchronized (writeLock) {
					// quit command does not produce output, so just send it
					zEvesOut.println(MessageFormat.format(ZEVES_COMMAND, "quit", ""));
					zEvesOut.flush();
				}
			} catch (Exception ex) {
				// ignore and just close afterwards
			}
		}

		close();
	}

	public void close() throws IOException {

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
	}

	public boolean isConnected() {
		return zEvesSocket != null && zEvesOut != null && zEvesIn != null && zEvesSocket.isBound();
	}

	/**
	 * Synchronize for multi-thread access
	 * 
	 * @param cmd
	 * @return
	 * @throws ZEvesException
	 */
	private synchronized String processCommand(String cmd) throws ZEvesException {

		/*
		 * TODO escape comments? E.g. try parsing the XML and check if it
		 * contains non-comments. This is a problem, because if a comment is
		 * sent, Z/Eves does not reply at all
		 */

		checkConnected();

		synchronized (writeLock) {
			zEvesOut.println(cmd);
		}

		try {
			return readZEvesResponse();
		} catch (IOException e) {
			throw new ZEvesException("I/O problems reading Z/Eves response: " + e.getMessage(), e);
		}
	}

	private String readZEvesResponse() throws IOException {
		StringBuilder response = new StringBuilder();

		String responseLine;
		do {

			responseLine = zEvesIn.readLine();

			if (responseLine == null) {
				break;
			}

			response.append(responseLine);

		} while (!responseLine.endsWith("</zoutput>") && !responseLine.endsWith("</zerror>")
				&& !responseLine.endsWith("<zoutput/>") && !responseLine.endsWith("<zerror/>"));

		return response.toString();
	}

	private void checkConnected() throws ZEvesException {
		if (!isConnected()) {
			throw new ZEvesException("Z/Eves theorem prover is not connected.");
		}
	}

	/**
	 * Sends a command to the server, formatted as specified in Z/Eves XML API
	 * requirements.
	 * 
	 * @param command
	 *            formatted Z/Eves XML command
	 * @return result as Java object
	 * @throws ZEvesException
	 *             if command produced an error (zerror) or communication failed
	 */
	public ZEvesOutput send(String command) throws ZEvesException {

		debug("Sending to Z/Eves: " + command);

		String resultStr = processCommand(command);

		debug("Received result: " + resultStr);

		Object result;
		try {
			result = getResponseReader().readXml(resultStr);
		} catch (Exception e) {
			throw new ZEvesException("Problems parsing Z/Eves response XML: " + e.getMessage(), e);
		}

		ZEvesOutput output = checkError(result);
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
			ParserConfigurationException, SAXException {

		ZEvesResponseReader reader = this.responseReader.get();
		if (reader == null) {
			reader = ZEvesResponseReader.createReader();
			this.responseReader.set(reader);
		}

		return reader;
	}

	private ZEvesOutput checkError(Object result) throws ZEvesException {
		if (result instanceof ZEvesError) {
			throw new ZEvesException((ZEvesError) result);
		}

		return (ZEvesOutput) result;
	}

	/**
	 * Sends an abort command to stop executing current command. This can be
	 * done asynchronously, while waiting for reply from Z/Eves. The executing
	 * command still produces an output, even if it was aborted.
	 */
	public void sendAbort() {

		if (!isConnected()) {
			return;
		}

		synchronized (writeLock) {
			// abort command does not produce output, so just send it
			zEvesOut.println(MessageFormat.format(ZEVES_COMMAND, "abort", ""));
			zEvesOut.flush();
		}
	}

	private ZEvesOutput sendCommand(String cmdName, String... args) throws ZEvesException {
		String command = MessageFormat.format(ZEVES_COMMAND, cmdName, concat(Arrays.asList(args), " "));
		return send(command);
	}

	@SuppressWarnings("unchecked")
	private <T> T sendCommand(String cmdName, Class<? extends T> resultType, String... args)
			throws ZEvesException {

		ZEvesOutput output = sendCommand(cmdName, args);

		if (resultType == null) {
			// no reply expected
			return null;
		}

		if (resultType == Integer.class) {
			return (T) getInteger(output.getFirstResult());
		}

		if (resultType == String.class) {
			return (T) getString(output.getFirstResult());
		}

		if (resultType == Boolean.class) {
			return (T) getBoolean(output.getFirstResult());
		}

		if (resultType == ZEvesOutput.class) {
			T val = (T) output;
			return val;
		}

		throw new ZEvesException("Unsupported Z/Eves response type: "
				+ resultType.getClass().getName());
	}

	private Integer getInteger(Object result) throws ZEvesException {

		if (result == null) {
			throw new ZEvesException("Invalid result received from Z/Eves.");
		}

		String valStr = ((ZEvesNumber) result).getValue();

		try {
			return Integer.valueOf(valStr);
		} catch (NumberFormatException e) {
			throw new ZEvesException(
					"Cannot parse the number in Z/Eves result: " + e.getMessage(), e);
		}
	}

	private String getString(Object result) {

		if (result == null) {
			return null;
		}

		if (result instanceof ZEvesName) {
			return ((ZEvesName) result).getIdent();
		}

		return ((ZEvesString) result).getValue();
	}

	private Boolean getBoolean(Object result) throws ZEvesException {

		if (result == null) {
			throw new ZEvesException("Invalid result received from Z/Eves.");
		}

		String valStr = ((ZEvesName) result).getIdent();
		return Boolean.valueOf(valStr);
	}

	private static String concat(Collection<?> list, String delimiter) {

		StringBuilder sb = new StringBuilder();

		String delim = "";
		for (Object i : list) {
			sb.append(delim).append(String.valueOf(i));
			delim = delimiter;
		}

		return sb.toString();
	}

	public int getHistoryLength() throws ZEvesException {
		return sendCommand("get-history-length", Integer.class);
	}

	public Object getHistoryElement(int paragraphNumber) throws ZEvesException {

		ZEvesOutput output = sendCommand("get-history-element", String.valueOf(paragraphNumber));
		return output.getFirstResult();
	}

	public Map<String, ZEvesTheoremType> getTheoremNames(int paragraphNumber) 
			throws ZEvesException {
		
		ZEvesOutput output = sendCommand("get-theorem-names", String.valueOf(paragraphNumber));

		Map<String, ZEvesTheoremType> theoremNames = new LinkedHashMap<String, ZEvesTheoremType>();

		List<?> results = output.getResults();
		for (int index = 0; index < results.size() - 1; index += 2) {

			// theoremName and isGoal/Axiom comes in pairs
			String theoremName = getString(results.get(index));

			// axiom otherwise
			Boolean isGoal = getBoolean(results.get(index + 1));
			ZEvesTheoremType type = isGoal ? ZEvesTheoremType.GOAL : ZEvesTheoremType.AXIOM;

			theoremNames.put(theoremName, type);
		}

		return theoremNames;
	}

	public ZEvesTheorem getTheorem(String theoremName) throws ZEvesException {

		ZEvesOutput output = sendCommand("get-theorem", theoremName);
		return (ZEvesTheorem) output.getFirstResult();
	}

	public String getCurrentGoalName() throws ZEvesException {
		return sendCommand("get-current-goal-name", String.class);
	}

	public boolean getGoalProvedState(String goalName) throws ZEvesException {
		return sendCommand("get-goal-proved-state", Boolean.class, goalName);
	}

	public int getGoalProofLength(String goalName) throws ZEvesException {
		return sendCommand("get-goal-proof-length", Integer.class, goalName);
	}

	public ZEvesOutput getGoalProofStep(String goalName, int stepNumber) throws ZEvesException {
		return sendCommand("get-goal-proof-step", goalName, String.valueOf(stepNumber));
	}

	public void reset() throws ZEvesException {
		sendCommand("reset");
	}

	public void undoBackTo(int paragraphNumber) throws ZEvesException {
		sendCommand("undo-back-to", String.valueOf(paragraphNumber));
	}

	public void setCurrentGoalName(String goalName) throws ZEvesException {
		sendCommand("set-current-goal-name", goalName);
	}

	private void debug(String msg) {
//		System.out.println(msg);
	}
}

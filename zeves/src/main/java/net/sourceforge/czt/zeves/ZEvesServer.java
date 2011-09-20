
package net.sourceforge.czt.zeves;

import java.io.IOException;

/**
 * The class for Z/Eves server process management. It launches the given Z/Eves
 * executable in an API mode. The class is aware of when the process is closed
 * externally.
 * 
 * @author Andrius Velykis
 */
public class ZEvesServer
{

  private final String zEvesExecCommand;

  private final int port;

  private Process process;

  public ZEvesServer(String zEvesExecCommand, int port)
  {
    super();
    this.zEvesExecCommand = zEvesExecCommand;
    this.port = port;
  }

  public void start() throws IOException
  {

    assert process == null;

    String fullZEvesCommand = zEvesExecCommand + " -- -api -port " + String.valueOf(port);

    System.out.println("Starting Z/Eves server with command: " + fullZEvesCommand);

    process = Runtime.getRuntime().exec(fullZEvesCommand);

    // wait for the process to die in another thread
    Thread exitWaiter = new Thread(new ProcessExitWaiter());
    exitWaiter.start();
  }

  public void stop()
  {

    if (process == null) {
      return;
    }

    process.destroy();
  }

  public boolean isRunning()
  {
    return process != null;
  }


  /**
   * Waits for the Z/Eves server process to terminate.
   * 
   * TODO Extended to notify users or restart the server.
   * 
   * @author Andrius Velykis
   */
  private class ProcessExitWaiter implements Runnable
  {
    public void run()
    {

      while (!Thread.interrupted()) {
        try {

          process.waitFor();
          process = null;

          System.out.println("Z/Eves server process has terminated.");

          Thread.currentThread().interrupt();
          return;

        }
        catch (InterruptedException ex) {
          ex.printStackTrace();
        }
      }
    }
  }

}

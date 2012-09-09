package net.sourceforge.czt.gnast.maven;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import net.sourceforge.czt.gnast.Gnast;
import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;

/**
 * @goal generate
 *
 * @author Petra Malik
 */
public class Main
  extends AbstractMojo 
{
  /**
   * @parameter expression="${project.build.directory}/generated-sources/gnast"
   * @required
   */
  private String outputDirectory;

  /**
   * @parameter expression="gnastdir"
   */
  private String gnastdir = "gnast";
  
  /**
   * @parameter
   */
  private boolean addAstFinaliser;
  
  /**
   * @parameter
   */
  private boolean gnastVerbose;
  
  /**
   * @parameter
   */
  private String sourceDirectory;
  
  /**
   * @parameter
   */
  private String namespace;

  /**
   * @parameter expression="${project}"
   * @required
   */
  private MavenProject project;

  @Override
  public void execute()
    throws MojoExecutionException 
  {
    File outputDir = new File(outputDirectory);
    if (outputDir.exists())
    {
      getLog().info( "AST has already been generated" );
    }
    else {
      final String message = "Generating AST ...\n" +
        "NOTE: This may take some time " +
        "(about 5 minutes on a 2GHz Pentium).\n" +
        "GnAST parameters = " + 
                        "\n\t-d " + outputDirectory +
                        "\n\t-t " + gnastdir +
                        "\n\t-s " + sourceDirectory +
                        "\n\t-n " + namespace +
                        (gnastVerbose ? "\n\t-vvv" : "") +
                        (addAstFinaliser ? "\n\t-f" : "") + "\n";
      getLog().info(message);
      ArrayList<String> args = new ArrayList<String>(Arrays.asList("-d", outputDirectory, "-t", gnastdir,
          "-s", sourceDirectory, "-n", namespace));
      if (addAstFinaliser)
      {
        args.add("-f");
      }
      if (gnastVerbose)
      {
        args.add("-vvv");
      }
      Gnast.main(args.toArray(new String[0]));
    }
    if (project != null )
    {
      project.addCompileSourceRoot(outputDirectory);
    }
  }
}

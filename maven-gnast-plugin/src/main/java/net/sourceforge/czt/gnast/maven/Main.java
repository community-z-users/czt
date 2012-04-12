package net.sourceforge.czt.gnast.maven;

import java.io.File;
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
  
  // false by default? yes
  /**
   * @parameter
   */
  private boolean addAstFinialiser;

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
        "(about 5 minutes on a 2GHz Pentium).";
      getLog().info(message);
      if (addAstFinialiser)
      {
        String[] args = { "-d", outputDirectory, "-b", gnastdir, "-f" };
        Gnast.main(args);
      } 
      else
      {
        String[] args = { "-d", outputDirectory, "-b", gnastdir };
        Gnast.main(args);
      }
    }
    if (project != null )
    {
      project.addCompileSourceRoot(outputDirectory);
    }
  }
}

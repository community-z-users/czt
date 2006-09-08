package net.sourceforge.czt.gnast.maven;

import java.io.File;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;

import net.sourceforge.czt.gnast.Gnast;

/**
 * @goal generate
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
   * @parameter expression="${project}"
   * @required
   */
  private MavenProject project;

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
      String[] args = { "-d", outputDirectory, "-b", gnastdir };
      Gnast.main(args);
    }
    if (project != null )
    {
      project.addCompileSourceRoot(outputDirectory);
    }
  }
}

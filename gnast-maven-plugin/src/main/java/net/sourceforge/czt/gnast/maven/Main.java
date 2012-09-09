package net.sourceforge.czt.gnast.maven;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;

import net.sourceforge.czt.gnast.Gnast;
import net.sourceforge.czt.gnast.Gnast.GnastBuilder;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;

/**
 * @goal generate
 *
 * @author Petra Malik
 * @author Andrius Velykis
 */
public class Main
  extends AbstractMojo 
{
  /**
   * @parameter expression="${project.build.directory}/generated-sources/gnast"
   */
  private File outputDirectory;

  /**
   * @parameter alias="templateDirectory"
   */
  private List<File> additionalTemplates = new ArrayList<File>();
  
  /**
   * @parameter
   */
  private Boolean addAstFinaliser;
  
  /**
   * @parameter
   */
  private boolean verbose;
  
  /**
   * The directory where all ZML schema files are located.
   * TODO better resolution? E.g. something similar to resources plugin? 
   * 
   * @parameter
   * @required
   */
  private File sourceDirectory;
  
  /**
   * @parameter
   * @required
   */
  private String targetNamespace;

  /**
   * @parameter expression="${project}"
   * @required
   */
  private MavenProject project;

  @Override
  public void execute() throws MojoExecutionException
  {
    getLog().info("Generating AST for " + targetNamespace + ". This may take some time.");

    GnastBuilder config = new GnastBuilder()
        .templates(additionalTemplates)
        .source(sourceDirectory)
        .namespace(targetNamespace);

    if (outputDirectory != null) {
      config = config.destination(outputDirectory);
    }

    if (addAstFinaliser != null) {
      config = config.finalizers(addAstFinaliser.booleanValue());
    }

    if (verbose) {
      config = config.verbosity(Level.FINER);
    }

    // create the generator and launch it
    Gnast gnast = config.create();
    gnast.generate();

    if (project != null) {
      project.addCompileSourceRoot(outputDirectory.getPath());
    }
  }
}

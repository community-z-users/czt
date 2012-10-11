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
import org.sonatype.plexus.build.incremental.BuildContext;

/**
 * @goal generate
 *
 * @author Petra Malik
 * @author Andrius Velykis
 */
public class GnastGenerateMojo
  extends AbstractMojo 
{
  /**
   * @parameter expression="${project.build.directory}/generated-sources/gnast"
   */
  private File outputDirectory;

  /**
   * @parameter alias="templateDirectory"
   * @required
   */
  private List<File> templates = new ArrayList<File>();
  
  /**
   * @parameter
   */
  private File mappingFile;
  
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
  
  /** 
   * Injected by Maven
   * @component
   */
  private BuildContext buildContext;

  @Override
  public void execute() throws MojoExecutionException
  {
    getLog().info("Generating AST for " + targetNamespace + ". This may take some time.");
    
    if (project != null) {
      project.addCompileSourceRoot(outputDirectory.getPath());
    }

    GnastBuilder config = new GnastBuilder()
        .templates(templates)
        .source(sourceDirectory)
        .namespace(targetNamespace);

    if (outputDirectory != null) {
      config = config.destination(outputDirectory);
    }
    
    if (mappingFile != null) {
      config = config.mapping(mappingFile);
    }

    if (addAstFinaliser != null) {
      config = config.finalizers(addAstFinaliser.booleanValue());
    }

    if (verbose) {
      config = config.verbosity(Level.FINER);
    }
    
    if (buildContext != null) {
      config = config.buildContext(buildContext);
    }

    // create the generator and launch it
    try {
      
      Gnast gnast = config.create();
      gnast.generate();
      
    } catch (Exception ex) {
      // catch any exceptions and report as Maven ones
      throw new MojoExecutionException("GnAST code generation failed", ex);
    }

  }
}


package net.sourceforge.czt.m2e.parser.internal;

import java.io.File;
import java.util.Set;

import org.apache.maven.plugin.MojoExecution;
import org.codehaus.plexus.util.Scanner;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.m2e.core.MavenPlugin;
import org.eclipse.m2e.core.embedder.IMaven;
import org.eclipse.m2e.core.project.configurator.MojoExecutionBuildParticipant;
import org.sonatype.plexus.build.incremental.BuildContext;

/**
 * @author Andrius Velykis
 */
public class ParserSrcBuildParticipant extends MojoExecutionBuildParticipant
{

  private static final String TEMPLATE_DIR_PROP = "templateDirectory";

  private static final String CUP_DIR_PROP = "cupOutputDirectory";
  private static final String JFLEX_DIR_PROP = "jflexOutputDirectory";

  public ParserSrcBuildParticipant(MojoExecution execution)
  {
    super(execution, true);
  }

  @Override
  public Set<IProject> build(int kind, IProgressMonitor monitor) throws Exception
  {
    IMaven maven = MavenPlugin.getMaven();
    BuildContext buildContext = getBuildContext();

    if (!canRunBuild(maven, buildContext)) {
      return null;
    }

    // execute mojo
    Set<IProject> result = super.build(kind, monitor);

    // tell m2e builder to refresh generated files
    refreshDir(maven, buildContext, "outputDirectory");
    refreshDir(maven, buildContext, CUP_DIR_PROP);
    refreshDir(maven, buildContext, JFLEX_DIR_PROP);

    return result;

  }
  
  private boolean canRunBuild(IMaven maven, BuildContext buildContext) throws CoreException {
    // check if any of the parser template source files changed
    File source = maven.getMojoParameterValue(getSession(), getMojoExecution(), TEMPLATE_DIR_PROP,
        File.class);
    
    if (source.exists()) {
      // source exists - scan it for changes
      Scanner ds = buildContext.newScanner(source); // delta or full scanner
      ds.scan();
      String[] includedFiles = ds.getIncludedFiles();
      // check if there are changed files
      return includedFiles != null && includedFiles.length > 0;
    } else {
      // plugin templates will be used (packed). Since they will never change, we allow this build
      // through for non-incremental builds
      return !buildContext.isIncremental();
    }
  }

  private void refreshDir(IMaven maven, BuildContext buildContext, String dirProp)
      throws CoreException
  {
    File generated = maven.getMojoParameterValue(getSession(), getMojoExecution(), dirProp,
        File.class);
    if (generated != null) {
      buildContext.refresh(generated);
    }
  }

}

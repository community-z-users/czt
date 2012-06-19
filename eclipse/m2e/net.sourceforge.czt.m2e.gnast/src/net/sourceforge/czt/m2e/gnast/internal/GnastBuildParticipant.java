
package net.sourceforge.czt.m2e.gnast.internal;

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
public class GnastBuildParticipant extends MojoExecutionBuildParticipant
{

  private static final String GENERATE_GOAL = "generate";
  
  private static final String GENERATE_SOURCE_PROP = "gnastdir";
  private static final String GENERATE_SOURCE_SUBDIR = "src/vm";
  
  private static final String RULECODEGEN_SOURCE_PROP = "velocimacroDirectory";
  

  public GnastBuildParticipant(MojoExecution execution)
  {
    super(execution, true);
  }

  @Override
  public Set<IProject> build(int kind, IProgressMonitor monitor) throws Exception
  {
    IMaven maven = MavenPlugin.getMaven();
    BuildContext buildContext = getBuildContext();

    // check if any of the gnast source files changed
    File source = getSourceDir(maven);
    Scanner ds = buildContext.newScanner(source); // delta or full scanner
    ds.scan();
    String[] includedFiles = ds.getIncludedFiles();
    if (includedFiles == null || includedFiles.length <= 0) {
      return null;
    }

    // execute mojo
    Set<IProject> result = super.build(kind, monitor);

    // tell m2e builder to refresh generated files
    File generated = maven.getMojoParameterValue(getSession(), getMojoExecution(), "outputDirectory", File.class);
    if (generated != null) {
      buildContext.refresh(generated);
    }

    return result;

  }

  private File getSourceDir(IMaven maven) throws CoreException
  {

    MojoExecution execution = getMojoExecution();

    if (isGenerateGoal(execution)) {
      File source = maven.getMojoParameterValue(getSession(), execution, GENERATE_SOURCE_PROP,
          File.class);
      // actually need a subdir for gnast:generate
      return new File(source, GENERATE_SOURCE_SUBDIR);
    }
    else {
      return maven.getMojoParameterValue(getSession(), execution, RULECODEGEN_SOURCE_PROP,
          File.class);
    }
  }

  private static boolean isGenerateGoal(MojoExecution execution)
  {
    return GENERATE_GOAL.equals(execution.getGoal());
  }
}


package net.sourceforge.czt.m2e.parser.internal;

import java.io.File;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.maven.plugin.MojoExecution;
import org.codehaus.plexus.util.Scanner;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
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
    refreshDir(maven, buildContext, "outputDirectory", false, monitor);
    refreshDir(maven, buildContext, CUP_DIR_PROP, true, monitor);
    refreshDir(maven, buildContext, JFLEX_DIR_PROP, true, monitor);

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

  private void refreshDir(IMaven maven, BuildContext buildContext, String dirProp,
      boolean immediate, IProgressMonitor monitor) throws CoreException
  {
    File generated = maven.getMojoParameterValue(getSession(), getMojoExecution(), dirProp,
        File.class);
    if (generated != null) {
      buildContext.refresh(generated);
      
      // Force refresh JFlex and CUP output folders immediately.
      // Currently buildContext.refresh() refreshes folders after all build participants
      // execute, which is too late - JFlex and CUP cannot locate the output folders
      // produced by parser-src in the workspace.
      // As a workaround, force refresh the output folders
      // (methods below copied from org.eclipse.m2e.core.internal.builder.MavenBuilderImpl)
      if (immediate) {
        refreshResources(getMavenProjectFacade().getProject(), generated, monitor);
      }
    }
  }
  
  private void refreshResources(IProject project, File file, IProgressMonitor monitor) throws CoreException {
    IPath path = getProjectRelativePath(project, file);
    if (path == null) {
      System.out.println("Could not get relative path for file: "  + file.getAbsoluteFile());
      return;
    }

    IResource resource;
    if (!file.exists()) {
      resource = project.findMember(path);
    } else if (file.isDirectory()) {
      resource = project.getFolder(path);
    } else {
      resource = project.getFile(path);
    }
    if (resource != null) {
      workaroundBug368376(resource, monitor);
      resource.refreshLocal(IResource.DEPTH_INFINITE, monitor);
    }
  }

  private void workaroundBug368376(IResource resource,
      IProgressMonitor monitor) throws CoreException {
    // refreshing a new file does not automatically refresh enclosing new folders
    // refreshLocal(IResource.DEPTH_ONE) on all out-of-sync parents seems to be the least expansive way to refresh
    // https://bugs.eclipse.org/bugs/show_bug.cgi?id=368376
    List<IContainer> parents = new LinkedList<IContainer>();
    for (IContainer parent = resource.getParent(); parent != null
        && !parent.isSynchronized(IResource.DEPTH_ZERO); parent = parent.getParent()) {
      parents.add(0, parent);
    }
    for (IContainer parent : parents) {
      parent.refreshLocal(IResource.DEPTH_ONE, monitor);
    }
  }

  public static IPath getProjectRelativePath(IProject project, File file) {
    if (project == null || file == null) {
      return null;
    }

    IPath projectPath = project.getLocation();
    if (projectPath == null) {
      return null;
    }

    IPath filePath = new Path(file.getAbsolutePath());
    if (!projectPath.isPrefixOf(filePath)) {
      return null;
    }

    return filePath.removeFirstSegments(projectPath.segmentCount());
  }

}

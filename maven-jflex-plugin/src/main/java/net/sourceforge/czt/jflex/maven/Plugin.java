/*
  Copyright (C) 2006 Petra Malik
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.jflex.maven;

import java.io.*;
import java.util.*;

import JFlex.anttask.JFlexTask;
import org.apache.tools.ant.BuildException;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;

/**
 * @goal generate
 * @phase generate-sources
 * @description Maven JFlex Plugin
 */
public class Plugin
  extends AbstractMojo
{
  /**
   * @parameter expression="${basedir}/src/main/jflex"
   * @required
   */
  private File sourceDirectory;

  /**
   * @parameter expression="${project.build.directory}/generated-sources/jflex"
   * @required
   */
  private String outputDirectory;

  /**
   * @parameter expression="${project}"
   * @required
   */
  private MavenProject project;

  public void execute()
    throws MojoExecutionException
  {
    if (project != null)
    {
      project.addCompileSourceRoot(outputDirectory);
    }
    List<File> files = getFiles();
    getLog().info("Processing " + files.size() + " jflex files");
    for (File file : files) {
      JFlexTask task = new JFlexTask();
      task.setDestdir(new File(outputDirectory));
      getLog().info("Processing " + file.getPath());
      task.setFile(file);
      try {
        task.execute();
      }
      catch (BuildException e) {
        throw new MojoExecutionException("JFlex generation failed", e);
      }
    }
  }

  private List<File> getFiles()
  {
    List<File> fileList = new ArrayList<File>();
    if (sourceDirectory != null) {
      collectFiles(sourceDirectory, fileList);
    }
    return fileList;
  }

  private void collectFiles(File directory, List<File> list)
  {
    File[] content = directory.listFiles();
    if (content == null) return;
    for (File file : content) {
      if (file.isDirectory()) collectFiles(file, list);
      else list.add(file);
    }
  }
}

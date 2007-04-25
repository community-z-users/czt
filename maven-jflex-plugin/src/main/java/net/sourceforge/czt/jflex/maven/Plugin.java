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
    extends AbstractMojo {
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
  throws MojoExecutionException {
    if (project != null) {
      project.addCompileSourceRoot(outputDirectory);
    }
    final String fileSep = System.getProperty("file.separator");
    List<File> files = getFiles();
    getLog().info("JFLEX: Processing " + files.size() + " jflex files");
    for (File file : files) {
      if (file.getName().lastIndexOf(".jflex") != -1) {
        String filename = file.getName().substring(0, file.getName().lastIndexOf(".jflex"));
        getLog().debug("JFLEX: Looking for template for file named " + file.getName() + "(" + file.getPath() + ")");
        String packageName = getPackage(file);
        String destdir = outputDirectory + fileSep + packageName.replace(".", fileSep);
        File destDir = new File(destdir);
        File destFile = new File(destDir, filename + ".java");
        getLog().debug("JFLEX: Checking file dates:\n\t" + new Date(destFile.lastModified()) +
            "= " + destFile + "\n\t" + new Date(file.lastModified()) + "= " +
            file);
        if (destFile.exists() && destFile.lastModified() >= file.lastModified()) {
          getLog().debug("JFLEX: Lexer file is up-to-date.");
        } else {
          JFlexTask task = new JFlexTask();
          task.setDestdir(new File(outputDirectory));
          getLog().info("JFLEX: Processing " + file.getPath());
          task.setFile(file);
          try {
            task.execute();
          } catch (BuildException e) {
            throw new MojoExecutionException("JFlex generation failed", e);
          }
        }        
      } else {
        getLog().warn("JFLEX: Found a file that is not for jflex processing: " + file);
      }
    }
  }
  
  private List<File> getFiles() {
    List<File> fileList = new ArrayList<File>();
    if (sourceDirectory != null) {
      collectFiles(sourceDirectory, fileList);
    }
    return fileList;
  }
  
  private void collectFiles(File directory, List<File> list) {
    File[] content = directory.listFiles();
    if (content == null) return;
    for (File file : content) {
      if (file.isDirectory()) collectFiles(file, list);
      else list.add(file);
    }
  }
  
  private String getPackage(File jflexFile)
    throws MojoExecutionException
  {
    try {
      BufferedReader br = new BufferedReader(new FileReader(jflexFile));
      while (br.ready()){
        String line = br.readLine();
        if (line.startsWith("package") && line.indexOf(";") != -1)
        {
          return line.substring(8, line.indexOf(";")).trim();
        }
      }
      return "";
    } catch (IOException e ) {
      throw new MojoExecutionException("Could not retrieve package name for file " + jflexFile);
    }
  }
}

/*
  Copyright 2003, 2005 Petra Malik
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

package net.sourceforge.czt.gnast;

import java.net.URL;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.sonatype.plexus.build.incremental.BuildContext;

/**
 * <p>Global GnAST properties for a code generation run.</p>
 */
public interface GlobalProperties
{
  /**
   * Returns the name of the project associated with the given
   * namespace.
   *
   * @return the name of the project associated with the namespace
   *         <code>namespace</code>;
   *         <code>null</code> if no project is associated with it.
   */
  Project getProjectName(String namespace);

  /**
   * Properties that should be added to the velocity context.
   *
   * @return should never be <code>null</code>.
   */
  Map<String, ?> getDefaultContext();

  /**
   * <p>Converts a package name into a directory name.</p>
   *
   * <p>Given a package name, this method returns the directory,
   * where files that belong to the given package will be
   * generated into.  It does take care of the destination
   * directory specified by the user.</p>
   *
   * @param packageName a valid package name
   * @return the directory where a file that belongs to the
   *         given package should go into.  The last character
   *         is a file separator so that the file name can just
   *         concatenated.
   */
  String toDirectoryName(String packageName);

  /**
   * <p>Returns a string representing the java file name
   * for the given package and class name.</p>
   *
   * <p>The java file name is the concatenation of the destination
   * directory, the directory name derived by replacing all dots in the
   * package name with the file separator character, and
   * the class name followed by ".java".</p>
   *
   * <p>Note that it is not checked
   * whether the given package and class names are valid.</p>
   *
   * @param packageName    the name of the package.
   * @param className  the name of the class.
   * @return the file name.
   */
  String toFileName(String packageName, String className);

  List<URL> getTemplatePaths();
  
  BuildContext getBuildContext();
  
  Set<String> getChangedFiles();
  
  boolean forceGenerateAll();
  
  /**
   * Resolves the given template file in one of the template directories (checks if it exists).
   * 
   * @param fileName
   * @return
   */
  public String resolvePath(String fileName);
  
}

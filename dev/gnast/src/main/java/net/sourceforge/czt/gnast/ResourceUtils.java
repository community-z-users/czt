/*
  Copyright 2012  Andrius Velykis
  
  This file is part of the CZT project.

  The CZT project is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT.  If not, see <http://www.gnu.org/licenses/>.
*/

package net.sourceforge.czt.gnast;

import java.io.File;
import java.net.URL;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.codehaus.plexus.util.Scanner;
import org.sonatype.plexus.build.incremental.BuildContext;

/**
 * Utilities to resolve resources from URLs and file system, as well as to check for changes.
 * 
 * @author Andrius Velykis
 */
public class ResourceUtils
{
  
  /**
   * Resolves a {@link File} from {@link URL}. Checks if the protocol is `file:`, otherwise returns
   * {@code null}.
   * 
   * @param url  the URL to resolve to File
   * @return File represented by the URL, or {@code null} if the URL is not file-based.
   */
  public static File getFile(URL url) {
    
    if (url == null) {
      return null;
    }
    
    if ("file".equals(url.getProtocol())) {
      return new File(url.getFile());
    }
    
    // for non-files, just return null
    return null;
  }
  
  /**
   * Checks if there are changes to the file within the given {@link BuildContext}.
   * <p>
   * Only checks for changes if the URL is a `file:` one, otherwise reports that there are no
   * changes (e.g. the URL is in a JAR).
   * </p>
   * 
   * @param buildContext  build context to check for file changes
   * @param url  URL representing the file resource
   * @param isDir  whether the URL represents a directory ({@code true} - then its contents are
   *          checked
   *          for changes), or a file ({@code false}).
   * @return a set of file names that have changed (both as file names and fully qualified paths).
   *         If there are no changes (or the URL is not in a file system), an empty set is returned.
   */
  public static Set<String> getURLChanges(BuildContext buildContext, URL url, boolean isDir) {
    // get the url file - may be in JAR!
    File file = getFile(url);
    if (file != null) {
      // file can be resolved as is not in JAR - check for changes
      if (isDir) {
        return getDirChanges(buildContext, file);
      } else {
        return getFileChanges(buildContext, file);
      }
    } else {
      return Collections.emptySet();
    }
  }
  
  private static Set<String> getFileChanges(BuildContext buildContext, File file) {
    
    boolean fileChanged = buildContext.hasDelta(file);
    if (fileChanged) {
      // mark the paths (both full path and just the name) for changes
      Set<String> changes = new HashSet<String>();
      changes.add(file.getPath());
      changes.add(file.getName());
      return changes;
    } else {
      return Collections.emptySet();
    }
  }
  
  private static Set<String> getDirChanges(BuildContext buildContext, File dir) {
    
    Set<String> dirChanges = new HashSet<String>();
    
    Scanner deleteScanner = buildContext.newDeleteScanner(dir);
    deleteScanner.scan();
    dirChanges.addAll(Arrays.asList(deleteScanner.getIncludedFiles()));
    
    Scanner changeScanner = buildContext.newScanner(dir);
    changeScanner.scan();
    dirChanges.addAll(Arrays.asList(changeScanner.getIncludedFiles()));
    
    // also add full paths
    Set<String> dirChangesFullPaths = new HashSet<String>();
    for (String relative : dirChanges) {
      dirChangesFullPaths.add(dir + "/" + relative);
    }
    dirChanges.addAll(dirChangesFullPaths);
    
    return dirChanges;
  }
}

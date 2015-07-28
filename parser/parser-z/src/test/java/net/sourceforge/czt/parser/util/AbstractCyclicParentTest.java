package net.sourceforge.czt.parser.util;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.JarURLConnection;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import org.apache.commons.io.FileUtils;
import org.junit.AfterClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import net.sourceforge.czt.session.UrlSource;

/**
 * <p>
 * An abstract class for cyclic parent test cases. It has references to a directory containing
 * cyclic parent test files, and creates test cases for each of the test files.
 * </p>
 * <p>
 * The test class can be used in other plugins. It will access the test files by extracting
 * the contents of parent .jar to a temporary folder, and executing test cases on them.
 * </p>
 * <p>
 * </p>
 * The test class requires JUnit4 and Apache commons-io libraries.
 * 
 * @author Andrius Velykis
 */
@RunWith(Parameterized.class)
public abstract class AbstractCyclicParentTest
{
  
  private static final String TEST_DIR = "/tests/cyclic/";
  private static final String TEMP_TEST_DIR = "cyclicParentTemp";

  @Parameters
  public static Collection<Object[]> cyclicTestFiles()
  {
    URL testsDir = AbstractCyclicParentTest.class.getResource(TEST_DIR);
    List<UrlSource> testFiles = getTestFiles(testsDir);
    
    List<Object[]> params = new ArrayList<Object[]>();
    
    for (UrlSource testFile : testFiles) {
      params.add(new Object[] {testFile});
    }
    
    return params;
  }
  
  /**
   * Collects all the files from a directory to test.
   * @throws URISyntaxException 
   * @throws MalformedURLException 
   */
  public static List<UrlSource> getTestFiles(URL dirUrl) 
  {
    
    try {
      File dir;
      if ("jar".equals(dirUrl.getProtocol())) {
        // extract the contents into a temp dir
        dir = extractFilesToTemp(dirUrl);
      } else {
        // will throw an exception if URL is wrong
        dir = new File(dirUrl.toURI());
      }
      
      File[] files = dir.listFiles();
      List<UrlSource> sources = new ArrayList<UrlSource>();
      if (files != null)
      {
	      for (File file : files) {
	        URL url = file.toURI().toURL();
	        sources.add(new UrlSource(url));
	      }
      }
      else
      {
    	  throw new IOException("Couldn't get list of files for directory " + dir.getName());
      }
      return sources;
    } catch (IOException | URISyntaxException ex) {
      throw new RuntimeException("Cannot resolve test files for URL " + dirUrl + "\n" + ex.getMessage(), ex);
    }
  }
  
  private static File extractFilesToTemp(URL dirURL) throws IOException
  {
    // allocate a temp location to extract .jar contents with test files
    File destination = new File(FileUtils.getTempDirectory(), TEMP_TEST_DIR);
    FileUtils.forceMkdir(destination);
    FileUtils.cleanDirectory(destination);
    destination.deleteOnExit();
    
    copyJarResourcesRecursively(destination, (JarURLConnection) dirURL.openConnection());

    return destination;
  }
  
  /*
   * Adapted from http://stackoverflow.com/questions/1386809/copy-a-directory-from-a-jar-file
   */
  private static void copyJarResourcesRecursively(File destination, JarURLConnection jarConnection)
      throws IOException
  {
    JarFile jarFile = jarConnection.getJarFile();
    for (JarEntry entry : Collections.list(jarFile.entries())) {
      if (entry.getName().startsWith(jarConnection.getEntryName())) {
        String fileName = entry.getName().substring(jarConnection.getEntryName().length());
        File file = new File(destination, fileName);
        file.deleteOnExit();
        
        if (!entry.isDirectory()) {
          InputStream entryInputStream = null;
          try {
            entryInputStream = jarFile.getInputStream(entry);
            FileUtils.copyInputStreamToFile(entryInputStream, file);
          }
          finally {
        	  if (entryInputStream != null) { entryInputStream.close(); }
          }
        }
        else {
          // create inner folders
          FileUtils.forceMkdir(file);
        }
      }
    }
  }
  
  @AfterClass
  public static void cleanupTemp() throws IOException {
      // File destination = new File(FileUtils.getTempDirectory(), TEMP_TEST_DIR);
      //FileUtils.deleteDirectory(destination);
  }
  
  private final UrlSource source;

  public AbstractCyclicParentTest(UrlSource source)
  {
    super();
    this.source = source;
  }
  
  protected UrlSource getSource() {
    return source;
  }
}

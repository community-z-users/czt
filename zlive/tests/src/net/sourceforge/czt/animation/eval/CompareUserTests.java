package net.sourceforge.czt.animation.eval;

import java.util.*;
import java.io.*;
import java.net.URL;


/** This program compares two versions of usertest results, to show
the number of tests gained or lost from first to the second version*/

public class CompareUserTests
{
  private static String versionDirectoryName1,versionDirectoryName2;
  private static ArrayList passedTests1,passedTests2;
  private static ArrayList gainedTests,lostTests;
  private static FileOutputStream outStream;
  private static PrintStream out;
  
  protected static URL getTestExample(String name) {
    Object stupid = new CompareUserTests();
    URL result = stupid.getClass().getResource("/tests/z/" + name);
    if (result == null) {
      throw new RuntimeException("Cannot find filename " + name);
    }
    return result;
  }
  
  private static void writetoOutputFile(String fileType)
  {
    Reader inStream;
    BufferedReader in;
    try {
      URL fileName = getTestExample("animate_"+fileType.toLowerCase()+".tex");
      inStream = new InputStreamReader(fileName.openStream());
      in = new BufferedReader(inStream);
      int lostCounter = 0;
      int gainedCounter = 0;
      out.println("animate_"+fileType.toLowerCase()+".tex");
      int counter = 1;
      String temp;
      if (gainedTests.size()>0){
        do {
          temp = in.readLine();
          if(temp!=null) {
            if(((Integer)gainedTests.get(gainedCounter)).intValue() == counter) {
              out.println("+ Line "+(counter)+": "+temp);
              gainedCounter++;
            }
            counter++;
          }
        } while((temp!=null) && (gainedCounter<gainedTests.size()));
      }
      
      in.close();
      counter = 1;
      inStream = new InputStreamReader(fileName.openStream());
      in = new BufferedReader(inStream);
      
      if (lostTests.size()>0){
        do {
          temp = in.readLine();
          if(temp!=null) {
            if(((Integer)lostTests.get(lostCounter)).intValue() == counter) {
              out.println("- Line "+(counter)+": "+temp);
              lostCounter++;
            }
            counter++;
          }
        } while((temp!=null) && (lostCounter<lostTests.size()));
      }
    }
    catch (FileNotFoundException e) {System.out.println("File not found : animate_"+fileType.toLowerCase()+".tex");}
    catch (IOException e) {System.out.println("I/O Error : animate_"+fileType.toLowerCase()+".tex");}
  }
  
  private static void sortArrays()
  {
    int passedCounter1 = 0;
    int passedCounter2 = 0;
    int gainedCounter = 0;
    int lostCounter = 0;
    while((passedCounter1<passedTests1.size())&&(passedCounter2<passedTests2.size())) {
      if (((Integer)passedTests1.get(passedCounter1)).intValue() == ((Integer)passedTests2.get(passedCounter2)).intValue()) {
        passedCounter1++;
        passedCounter2++;
      }
      else if (((Integer)passedTests1.get(passedCounter1)).intValue() < ((Integer)passedTests2.get(passedCounter2)).intValue()) {
        lostTests.add(passedTests1.get(passedCounter1));
        passedCounter1++;
      }
      else if (((Integer)passedTests1.get(passedCounter1)).intValue() > ((Integer)passedTests2.get(passedCounter2)).intValue()) {
        gainedTests.add(passedTests2.get(passedCounter2));
        passedCounter2++;
      }
    }
    while(passedCounter1<passedTests1.size())
    {
      lostTests.add(passedTests1.get(passedCounter1));
      passedCounter1++;
    }
    while(passedCounter2<passedTests2.size())
    {
      gainedTests.add(passedTests2.get(passedCounter2));
      passedCounter2++;
    }
    gainedCounter=0;
    lostCounter=0;
  }
  
  
  private static void compareFile(String shortName)
    throws IOException
  {
    String fileName =  "TEST-net.sourceforge.czt.animation.eval.Animate"
	                 +shortName+"Test.txt";
    passedTests1 = readPassedTests(versionDirectoryName1,fileName);
    passedTests2 = readPassedTests(versionDirectoryName2,fileName);
    gainedTests = new ArrayList();
    lostTests = new ArrayList();
    sortArrays();
    writetoOutputFile(shortName);
  }

  /** Reads dir/fileName and returns an array of the tests that passed.
      In fact, the resulting array contains the line numbers (from
      the original .tex file, of the passed tests.
  */
  private static ArrayList readPassedTests(String dir, String fileName)
    throws IOException
  {
    File inputFile = new File(dir,fileName);
    FileReader inStream = new FileReader(inputFile);
    BufferedReader reader = new BufferedReader(inStream);
    ArrayList passed = new ArrayList();
    String line = reader.readLine();
    while (line != null) {
	if (line.startsWith("Passed test:")
         || line.startsWith("Passed undef test:")) {
            if ((line.indexOf("::")) >= 0) {
		String testNum = line.substring(line.lastIndexOf(':')+1);
		out.println("WARNING: Passed test #"+testNum
			    +" has no line number in file "
			    +dir+"/"+fileName);
	    }
	    else {
		// we have a line number
		int colon = line.lastIndexOf(':');
		if (colon < 0)
		    throw new RuntimeException("Bad test output: "+line);
		String lineNum = line.substring(colon+1);
		passed.add(new Integer(lineNum));
	    }
	}
        line = reader.readLine();
    }
    reader.close();
    return passed;
  }

  public static void main (String args[])
  throws IOException
  {
    String versionNumber1,versionNumber2;
    String date1,date2;
    String userdir = System.getProperty("user.dir");
    if(args.length == 4) {
      versionNumber1 = args[0];
      date1 = args[1];
      versionNumber2 = args[2];
      date2 = args[3];
      versionDirectoryName1 = "version" + versionNumber1 + "_" + date1;
      versionDirectoryName2 = "version" + versionNumber2 + "_" + date2;
    }
    else if(args.length == 2) {
      versionDirectoryName1 = args[0];
      versionDirectoryName2 = args[1];
      int temp = versionDirectoryName1.lastIndexOf(File.separator);
      versionNumber1 = versionDirectoryName1.substring(temp+1);
      temp = versionDirectoryName2.lastIndexOf(File.separator);
      versionNumber2 = versionDirectoryName2.substring(temp+1);
    }
    else {
      BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
      System.out.print("Enter the version number for the first file (1,2,3...) : ");
      versionNumber1 = br.readLine();
      System.out.print("Enter date (dd-mm-yyyy) of first file : ");
      date1 = br.readLine();
      System.out.print("Enter the version number for the second file (1,2,3...) : ");
      versionNumber2 = br.readLine();
      System.out.print("Enter date (dd-mm-yyyy) of second file : ");
      date2 = br.readLine();
      versionDirectoryName1 = "version" + versionNumber1 + "_" + date1;
      versionDirectoryName2 = "version" + versionNumber2 + "_" + date2;
    }
    out = System.out;
    out.println("--VERSION "+versionNumber1+" VS VERSION "+versionNumber2+"--");
    
    compareFile("Ints");
    compareFile("Freetypes");
    compareFile("Sets");
    compareFile("Schemas");
    compareFile("Misc");
    compareFile("Relations");
    compareFile("Scope");
    compareFile("Sequences");
  }
}


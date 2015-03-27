package net.sourceforge.czt.animation.eval;

import java.io.*;
import java.net.URL;
import java.util.ArrayList;

/** This program compares two versions of usertest results, to show
 *  the number of tests gained or lost from first to the second version.
 */
public class CompareUserTests
{
  private static String versionDirectoryName1,versionDirectoryName2;
  private static ArrayList<Integer> passedTests1,passedTests2;
  private static ArrayList<Integer> gainedTests,lostTests;
  private static PrintStream out;

  /** Returns the number of lost tests. */
  private static int writetoOutputFile(String fileType)
  {
    Reader inStream;
    BufferedReader in;
    int lostCounter = 0;
    int gainedCounter = 0;
    try {
      URL fileName =
        EvalTest.getTestExample("animate_"+fileType.toLowerCase()+".tex");
      inStream = new InputStreamReader(fileName.openStream());
      in = new BufferedReader(inStream);
      final int p1 = passedTests1.size();
      final int p2 = passedTests2.size();
      final String connector = (p1==p2 ? "==" : "->");
      final String emotion = (p1<p2 ? ":-)" : (p1>p2 ? ":-(" : ""));
      out.format("%-30s  %3d %s %3d %s\n", "animate_"+fileType.toLowerCase()+".tex", 
    		  p1, connector, p2, emotion);
      int counter = 0;
      try {
        if (gainedTests.size()>0){
          String temp;
          do {
            temp = in.readLine();
            if(temp!=null) {
              if(((Integer)gainedTests.get(gainedCounter)).intValue() == counter) {
                out.println("+ Line "+counter+": "+temp);
                gainedCounter++;
              }
              counter++;
            }
          } while((temp!=null) && (gainedCounter<gainedTests.size()));
        }
      } finally {
        in.close();
      }
      counter = 0;
      inStream = new InputStreamReader(fileName.openStream());
      in = new BufferedReader(inStream);

      try {
        if (lostTests.size()>0){
          String temp;
          do {
            temp = in.readLine();
            if(temp!=null) {
              if(((Integer)lostTests.get(lostCounter)).intValue() == counter) {
                out.println("- Line "+counter+": "+temp);
                lostCounter++;
              }
              counter++;
            }
          } while((temp!=null) && (lostCounter<lostTests.size()));
        }
      } finally {
        in.close();
      }
    }
    catch (FileNotFoundException e) {System.out.println("File not found : animate_"+fileType.toLowerCase()+".tex");}
    catch (IOException e) {System.out.println("I/O Error : animate_"+fileType.toLowerCase()+".tex");}
    return lostCounter;
  }

  private static void sortArrays()
  {
    int passedCounter1 = 0;
    int passedCounter2 = 0;
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
  }


  /** Returns the number of newly-failing tests. */
  private static int compareFile(String shortName)
    throws IOException
  {
    String fileName =  "TEST-net.sourceforge.czt.animation.eval.Animate"
	                 +shortName+"Test.txt";
    passedTests1 = readPassedTests(versionDirectoryName1,fileName);
    passedTests2 = readPassedTests(versionDirectoryName2,fileName);
    gainedTests = new ArrayList<Integer>();
    lostTests = new ArrayList<Integer>();
    sortArrays();
    return writetoOutputFile(shortName);
  }

  /** Reads dir/fileName and returns an array of the tests that passed.
      In fact, the resulting array contains the line numbers (from
      the original .tex file, of the passed tests.
  */
  private static ArrayList<Integer> readPassedTests(String dir, String fileName)
    throws IOException
  {
    File inputFile = new File(dir,fileName);
    FileReader inStream = new FileReader(inputFile);
    BufferedReader reader = new BufferedReader(inStream);
    try {
      ArrayList<Integer> passed = new ArrayList<Integer>();
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
      return passed;
      
    } finally {
      reader.close();
    }
  }

  public static void main (String args[])
  throws IOException
  {
    //String userdir = System.getProperty("user.dir");
    if(args.length == 2) {
      versionDirectoryName1 = args[0];
      versionDirectoryName2 = args[1];
    }
    else {
      System.out.println("Usage: CompareUserTests oldDirectory newDirectory");
      System.out.println(" note: The two directories must both contain junit output");
      System.out.println("       files with names like TEST-...AnimateIntsTest.txt");
      System.out.println("       newDirectory can equal '.'");
      System.exit(2);
    }
    out = System.out;

    int newFailures = compareFile("Ints")
      + compareFile("Freetypes")
      + compareFile("Sets")
      + compareFile("Schemas")
      + compareFile("Misc")
      + compareFile("Relations")
      + compareFile("Scope")
      + compareFile("Sequences");
    System.exit(newFailures);  // 0 is good, > 0 is bad.
  }
}


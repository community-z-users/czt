package net.sourceforge.czt.animation.eval;

import java.util.*;
import java.io.*;
import java.net.URL;


/** This program compares two versions of usertest results, to show
the number of tests gained or lost from first to the second version*/

public class CompareUserTests
{
  private static File inputFile1,inputFile2;
  private static FileReader inStream1,inStream2;
  private static BufferedReader in1,in2;
  private static ArrayList passedTests1,passedTests2;
  private static ArrayList gainedTests,lostTests;
  private static String versionDirectoryName1,versionDirectoryName2;
  private static String versionNumber1,versionNumber2;
  private static String date1,date2;
  private static String compareFileName;
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
  
  
  private static void compareFile(String fileType)
  {
    String compareFileName;
    File outputFile;
    FileReader inStream;
    BufferedReader in;
    String temp;
    int i=0;
    try {
      inputFile1 = new File(versionDirectoryName1 , "TEST-net.sourceforge.czt.animation.eval.Animate"+fileType+"Test.txt");
      inputFile2 = new File(versionDirectoryName2 , "TEST-net.sourceforge.czt.animation.eval.Animate"+fileType+"Test.txt");
      inStream1 = new FileReader(inputFile1);
      inStream2 = new FileReader(inputFile2);
      in1 = new BufferedReader(inStream1);
      in2 = new BufferedReader(inStream2);
    }
    catch (FileNotFoundException e) {
      System.out.println("File not Found : Animate"+fileType+"Test.txt");
    }
    passedTests1 = new ArrayList();
    passedTests2 = new ArrayList();
    try {
      do {
        temp = in1.readLine();
        if(temp!=null) {
          if(temp.startsWith("Passed test"))
            passedTests1.add(new Integer(temp.substring(25+fileType.length())));
        }
      }while(temp != null);
      
      do {
        temp = in2.readLine();
        if(temp!=null) {
          if(temp.startsWith("Passed test"))
            passedTests2.add(new Integer(temp.substring(25+fileType.length())));
        }
      }while(temp != null);
    }
    catch (IOException e) {System.out.println("I/O Error");}
    gainedTests = new ArrayList();
    lostTests = new ArrayList();
    sortArrays();
    writetoOutputFile(fileType);
  }
  
  public static void main (String args[])
  throws IOException
  {
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
      int temp = args[0].lastIndexOf(File.separator);
      versionNumber1 = args[0].substring(temp);
      temp = args[1].lastIndexOf(File.separator);
      versionNumber2 = args[1].substring(temp);
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
    
    in1.close();
    in2.close();
  }
}


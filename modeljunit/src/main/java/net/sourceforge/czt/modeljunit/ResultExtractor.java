/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit;

import java.io.*;
import java.util.Random;
import java.util.List;
import java.util.ArrayList;
import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;
import net.sourceforge.czt.modeljunit.examples.QuiDonc;

/**
 * This class runs several random and greedyRandom walks
 * and outputs them to a text file
 *
 * @author Pele Douangsavanh
 */
public class ResultExtractor
{
  public static void main(String[] args)
  {
    ResultExtractor r;
    if (args.length > 0)
      r = new ResultExtractor(Integer.parseInt(args[0]));
    else
      r = new ResultExtractor();
    r.run();
  }

  int passes;

  int testLength = 100;

  CoverageHistory metric;
  
  ArrayList<Integer> seeds;

  ArrayList<String> historyRandom;

  ArrayList<String> historyGreedy;

  ArrayList<String> historyAllRound;

  Random rand;

  public ResultExtractor()
  {
    this(3);
  }

  public ResultExtractor(int p)
  {
    passes = p;
    rand = new Random();
    seeds = new ArrayList<Integer>();
    historyRandom = new ArrayList<String>();
    historyGreedy = new ArrayList<String>();
    historyAllRound = new ArrayList<String>();
  }

  /**
   * @return the Random object that is used to generate seeds.
   */
  public Random getRand()
  {
    return rand;
  }

  /**
   * @param rand The Random object that will be used to generate seeds.
   */
  public void setRand(Random rand)
  {
    this.rand = rand;
  }

  /**
   * @return the testLength
   */
  public int getTestLength()
  {
    return testLength;
  }

  /**
   * @param testLength the testLength to set
   */
  public void setTestLength(int testLength)
  {
    this.testLength = testLength;
  }

  protected String generateResults(int seed, Tester tester)
  {
    // model.addListener("verbose");
    tester.reset();
    tester.setRandom(new Random(seed));
    metric.clear();
    tester.generate(testLength);
    return metric.toCSV();
  }

  public void run()
  {
    for (int pass=0; pass < passes; pass++) {
      Model model = new Model(new QuiDonc());
      metric = new CoverageHistory(new TransitionCoverage(), 1);
      model.addListener(metric);
      int seed = rand.nextInt();

      seeds.add(seed);

      // System.out.println("TESTING RANDOM seed="+seed);
      Tester rtester = new RandomTester(model);
      historyRandom.add(generateResults(seed, rtester));

      // System.out.println("TESTING GREEDY seed="+seed);
      Tester gtester = new GreedyTester(model);
      historyGreedy.add(generateResults(seed, gtester));

      Tester atester = new AllRoundTester(model);
      historyAllRound.add(generateResults(seed, atester));
    }
    this.write();
  }

  public void write()
  {
    try {
      File f = new File("ResultExtractorOutput.csv");
      PrintWriter w = new PrintWriter(new FileOutputStream(f));

      System.out.println("Writing to " + f.getAbsolutePath());
      for (int i = 0; i < seeds.size(); i++) {
        w.print("Seed," + seeds.get(i) + ",");
        w.print("Random,");
        w.println(historyRandom.get(i));
        w.print(",,Greedy,");
        w.println(historyGreedy.get(i));
      }
      for (int j = 0; j < seeds.size(); j++) {
        w.print(",,All Round Trips,");
        w.println(historyAllRound.get(j));
      }
      w.close();
    }
    catch (Exception ex) {
      System.err.println("IO error occurance");
      ex.printStackTrace();
    }
  }
}

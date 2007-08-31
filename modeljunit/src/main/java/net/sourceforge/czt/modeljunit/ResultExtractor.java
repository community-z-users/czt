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
*/
public class ResultExtractor 
{
	public static void main(String[] args) 
	{
		ResultExtractor r;
		if(args.length > 0)
			r = new ResultExtractor(Integer.parseInt(args[0]));
		else
			r = new ResultExtractor();
		r.run();
	}

	int passes;
	int currentPass;
	CoverageHistory metric;
	ArrayList<Integer> seeds;
	ArrayList<String> historyRandom;
	ArrayList<String> historyGreedy;
	Random rand;
	
	public ResultExtractor()
	{
		passes = 3;
		currentPass = 0;
		rand = new Random();
		seeds = new ArrayList<Integer>();
		historyRandom = new ArrayList<String>();
		historyGreedy = new ArrayList<String>();
	}
	
	public ResultExtractor(int p)
	{
		passes = p;
		currentPass = 0;
		rand = new Random();
		seeds = new ArrayList<Integer>();
		historyRandom = new ArrayList<String>();
		historyGreedy = new ArrayList<String>();
	}
	
        protected String generateResults(int seed, Tester tester)
        {
                metric = new CoverageHistory(new TransitionCoverage(), 1);
                tester.addCoverageMetric(metric);
                tester.setRandom(new Random(seed));
                tester.generate(100);
                return metric.toCSV();
        }
        
	public void run() {
		while (currentPass != passes)
		{
			int seed = rand.nextInt();
                        Model model = new Model(new QuiDonc());
                        
                        Tester rtester = new RandomTester(model);
			historyRandom.add(generateResults(seed, rtester));
                        
                        Tester gtester = new GreedyTester(model);
                        historyGreedy.add(generateResults(seed, gtester));
			
			seeds.add(seed);
			currentPass++;
		}
		this.write();
	}
	
	public void write() {
		try
		{
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
			w.close();
		}
		catch (Exception ex)
		{
			System.err.println("IO error occurance");
			ex.printStackTrace();
		}
	}
}

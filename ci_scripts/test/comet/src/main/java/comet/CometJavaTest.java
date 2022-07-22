package comet;

// Java Dependencies
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import javax.swing.text.PasswordView;

// Comet Dependencies
import com.smartesting.comet.model.*;
import com.smartesting.comet.api.*; 
import com.smartesting.comet.auth.*;
import com.smartesting.comet.*;

// import static com.google.common.collect.Lists.newArrayList;
// import static com.smartesting.comet.Configuration.getDefaultApiClient;
// import static java.util.stream.IntStream.range;

/**
 * Corejava-z Comet Java Test
 */

public class CometJavaTest {
    private final static String urlService = "https://chiron.comet.smartesting.com";
    private final static String apiKey = "6b3277b2-fbbe-4256-bbf5-7da7fae84eba";
    private final static String prjName = "CZT";

    public static void main(String[] args) {

        // Initialize the client
        ApiClient defaultClient = Configuration.getDefaultApiClient();
        defaultClient.setBasePath(urlService);
  
        // Configure API key authorization: ApiKeyAuth
        ApiKeyAuth ApiKeyAuth = (ApiKeyAuth) defaultClient.getAuthentication("ApiKeyAuth");
        ApiKeyAuth.setApiKey(apiKey);
  
        PrioritizationsApi prioritizationsApi = new PrioritizationsApi(defaultClient);
        ProjectsApi projectsApi = new ProjectsApi(defaultClient);
        TestCyclesApi testCyclesApi = new TestCyclesApi(defaultClient);
        
        // Get prioritisation
        List<TestCycle> prevCycles = CometJavaClient.listCycles(testCyclesApi);
        List<String> tests = new ArrayList<>();
        try {
          TestCycle lastCycle = testCyclesApi.showLastTestCycle(prjName);
          System.out.println("" + lastCycle.getId() + " " + lastCycle.getTests().size());
          if (prevCycles.size() >= 10) {
            Prioritization prioritization = prioritizationsApi.prioritize(prjName, lastCycle.getId());
            tests = prioritization.getTests();
          } else {
            // Return random list order since prioritisation can't be used with < 10 cycles
            System.out.println("There are only " + prevCycles.size() + " test cycles");
            
            // Get tests from last uploaded cycle
            for (Test test : lastCycle.getTests()) {
              System.out.println("Adding Test: " + test.getId());
              tests.add(test.getId());
            }
          }
        } catch (NullPointerException | ApiException e) {
          System.err.println("Problem getting prioritisation");
          System.exit(1);
        }
        // CometJavaClient.showProject(projectsApi);


        // Run tests
        TestsApi testsApi = new TestsApi();
        try {
          Runtime r = Runtime.getRuntime();
          
          for(String id : tests) {
            Process p = r.exec("util/run_test.py " + id);
            BufferedReader b = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String line;
            float duration = 0;
            System.out.print("[INFO] Testing " + id + " : ");
            while ((line = b.readLine()) != null) {
              if (line.contains("Time elapsed")) {
                duration = Float.parseFloat(line.split("Time elapsed: ")[1].split(" sec")[0]);
              }
            }
            b.close();
            p.waitFor();
            TestVerdict verdict = new TestVerdict();
            verdict.id(id);
            if (p.exitValue() == 0) {
              verdict.fail(false);
              verdict.duration(duration); // Inlcude duration only if test passed
              prettyPrint(id, "PASSED");
            } else {
              verdict.fail(true);
              prettyPrint(id, "FAILED");
            }
            testsApi.updateTest(prjName, testCyclesApi.showLastTestCycle(prjName).getId(), verdict);
          }
      } catch (java.lang.InterruptedException | java.io.IOException | ApiException e) {
          System.out.println("Error updating test suite results");
      }
      System.exit(0);
    }

    private static void prettyPrint(String id, String outcome) {
        int length = ("[INFO] Testing " + id + " : ").length();
        String output = "";
        for (int i = length; i < 93; i++) {
          output += " ";
        }
        System.out.println(output + outcome);
    }
}

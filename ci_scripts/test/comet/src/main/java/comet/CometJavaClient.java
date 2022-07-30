package comet;

// Java Dependencies
import java.util.*;
import java.io.*;
import java.time.LocalDateTime; 

// Comet Dependencies
import com.smartesting.comet.model.*;
import com.smartesting.comet.api.*; 
import com.smartesting.comet.auth.*;
import com.smartesting.comet.*;

/**
 * Comet Java Client
 */

public class CometJavaClient {
    private final static String urlService = "https://chiron.comet.smartesting.com";
    private final static String apiKey = "6b3277b2-fbbe-4256-bbf5-7da7fae84eba";
    private final static String prjName = "CZT";


    /** 
     * CZT CometJavaClient
     * TODO: Write comment here
     */

    public static void main(String[] args) {

        // Initialize the client
        ApiClient defaultClient = Configuration.getDefaultApiClient();
        defaultClient.setBasePath(urlService);
  
        // Configure API key authorization: ApiKeyAuth
        ApiKeyAuth ApiKeyAuth = (ApiKeyAuth) defaultClient.getAuthentication("ApiKeyAuth");
        ApiKeyAuth.setApiKey(apiKey);
  
        ProjectsApi projectsApi = new ProjectsApi(defaultClient);

        /*
         * Use coverage data to create test cycle with the following information:
         *  - id: name of test
         *  - classChanged (whether the source class that this test covers changed
         *  - testChanged (whether this class changed)
         */
        System.out.println(prjName + " Comet Java Client");
        Runtime r = Runtime.getRuntime();
        ArrayList<Test> tests = new ArrayList<>();
        try {
            Process p = r.exec("./util/get_tests.py");
            p.waitFor();

            BufferedReader b = new BufferedReader(new InputStreamReader(p.getInputStream()));
            String line;

            while ((line = b.readLine()) != null) {
              String[] tokens = line.split(",");
              Test test = new Test();
              test.setId(tokens[0]);
              test.setClassChanged(tokens[1].equals("True"));
              test.setTestChanged(tokens[1].equals("True"));
              //System.out.println(line);
              tests.add(test);
            }
            b.close();
        } catch (java.lang.InterruptedException | java.io.IOException e) {
            System.err.println("Error collecting test case data");
        }

        /*
         * Add test cycle to comet API
         * - Create project if it doesn't exist and display it's state
         * - Add tests and receive prioritisation
         */
        try {
          final Project project = new Project();
          project.setName(prjName);
          projectsApi.createProject(project);
        } catch (ApiException e) {
          System.out.print("[INFO] " + prjName + " Project aready exists");
        }

        TestCyclesApi testCyclesApi = new TestCyclesApi(defaultClient);
        TestsApi testApi = new TestsApi(defaultClient);
        String testCycleId = LocalDateTime.now().toString();
        try {
          TestCycle testCycle = new TestCycle();
          testCycle.id(testCycleId); 
          testCyclesApi.addTestCycle(prjName, testCycle, false);

          for(Test test : tests) {
            testApi.addTest(prjName, testCycleId, test);
          }
        } catch (ApiException e) {
          printApiException(e);
        }

        /**
         * Get the Prioritisation, run the tests, upload the results
         */
        PrioritizationsApi prioritizationsApi = new PrioritizationsApi(defaultClient);
        List<TestCycle> prevCycles = listCycles(testCyclesApi);
        List<String> prioritisedTests = new ArrayList<>();
        try {
          TestCycle lastCycle = testCyclesApi.showLastTestCycle(prjName);
          System.out.println("" + lastCycle.getId() + " " + lastCycle.getTests().size());
          if (prevCycles.size() >= 10) {
            Prioritization prior = prioritizationsApi.prioritize(prjName, lastCycle.getId());
            prioritisedTests = prior.getTests();
          } else {
            // Return unprioritised list since prioritisation can't be generated with less than
            // ten test cycles.
            System.out.println("There are only " + prevCycles.size() + " test cycles");
            
            // Get tests from last uploaded cycle
            for (Test test : lastCycle.getTests()) {
              prioritisedTests.add(test.getId());
            }
          }
        } catch (NullPointerException | ApiException e) {
          System.out.println(e.toString());
          System.err.println("Problem getting prioritisation");
          System.exit(1);
        }

        // Run tests
        TestsApi testsApi = new TestsApi();
        try {
          r = Runtime.getRuntime();
          
          for(String id : prioritisedTests) {
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

        showProject(projectsApi);
        System.exit(0);
    }


    /** 
     * Utility functions
     */
    public static void showProject(ProjectsApi projectsApi) {
        try {
          Project result = projectsApi.showProject(prjName);
          System.out.println("[INFO] Project State:");
          System.out.println(result);
        } catch (ApiException e) {
          System.out.println("Problem showing up project");
        }
    }

    public static List<TestCycle> listCycles(TestCyclesApi cyclesApi) {
      try {
        List<TestCycle> result = cyclesApi.listTestCycles(prjName);
        return result;
      } catch (ApiException e) {
        System.out.println("Problem showing up project");
        return null;
      }
    }

    public static void removeProject(ProjectsApi projectsApi) {
        try {
          projectsApi.deleteProject(prjName);
          System.out.println("Deleting Project");
        } catch (ApiException e) {
          System.out.println("Problem deleting project");
        }
    }

    private static void prettyPrint(String id, String outcome) {
      int length = ("[INFO] Testing " + id + " : ").length();
      String output = "";
      for (int i = length; i < 93; i++) {
        output += " ";
      }
      System.out.println(output + outcome);
    }

    private static void printApiException(ApiException e) {
      System.err.println("Status code: " + e.getCode());
      System.err.println("Reason: " + e.getResponseBody());
      System.err.println("Response headers: " + e.getResponseHeaders());
    }

}

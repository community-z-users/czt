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
import com.smartesting.comet.model.Feature.TypeEnum;
import static com.google.common.collect.Lists.newArrayList;


/**
 * Comet Java Client
 */

public class CometJavaClient {
    private final static String urlService = "https://chiron.comet.smartesting.com";
    private static String apiKey = "";
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
        ApiKeyAuth.setApiKey(getApiKey());
  
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
              test.put("id", tokens[0]);
              test.put("class_changed", tokens[1].equals("True"));
              test.put("test_changed", tokens[2].equals("True"));
              tests.add(test);
            }
            b.close();
        } catch (java.lang.InterruptedException | java.io.IOException e) {
            System.err.println("Error collecting test case data");
            System.exit(1);
        }

        /*
         * Add test cycle to comet API
         * - Create project if it doesn't exist and display it's state
         * - Add tests and receive prioritisation
         */
        try {
          final Project project = new Project();
          project.setName(prjName);
          project.features(newArrayList(
            new Feature().name("duration").type(TypeEnum.FLOAT).defaultValue("0.0"),
            new Feature().name("class_changed").type(TypeEnum.BOOL).defaultValue("false"),
            new Feature().name("test_changed").type(TypeEnum.BOOL).defaultValue("false")
            ));
          removeProject(projectsApi);
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
          testCycle.tests(tests);
          testCyclesApi.addTestCycle(prjName, testCycle, false);
        } catch (ApiException e) {
          printApiException(e);
          System.exit(1);
        }

        showProject(projectsApi);
        System.exit(0);
        /**
         * Get the Prioritisation, run the tests, upload the results
         */
        PrioritizationsApi prioritizationsApi = new PrioritizationsApi(defaultClient);
        List<TestCycle> prevCycles = listCycles(testCyclesApi);
        List<String> prioritisedTests = new ArrayList<>();
        try {
          TestCycle lastCycle = testCyclesApi.showLastTestCycle(prjName);
          System.out.println("There are currently " + prevCycles.size() + " test cycles");
          System.out.println("" + lastCycle.getId() + " " + lastCycle.getTests().size());
          if (prevCycles.size() >= 10) {
            Prioritization prior = prioritizationsApi.prioritize(prjName, lastCycle.getId());
            prioritisedTests = prior.getTests();
          } else {
            // Return unprioritised list since prioritisation can't be generated with less than
            // ten test cycles.
            // Get tests from last uploaded cycle
            for (Test test : lastCycle.getTests()) {
              prioritisedTests.add((String) test.get(("id")));
            }
          }
        } catch (NullPointerException | ApiException e) {
          System.out.println(e.toString());
          System.err.println("Problem getting prioritisation");
          System.exit(1);
        }


        // Run tests
        TestsApi testsApi = new TestsApi();
        List<TestVerdict> verdicts = new ArrayList<>();
        // System.out.println(testCyclesApi.showLastTestCycle(prjName).getId());
        // System.exit(0);
        boolean allTestsPassed = true;
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
              verdict.put("id", id);
              verdict.put("duration", duration);
              prettyPrint(id, "PASSED");
            } else {
              verdict.put("id", id);
              allTestsPassed = false;
              verdict.put("fail", true);
              prettyPrint(id, "FAILED");
            }
            verdicts.add(verdict);
          }

          testsApi.updateSuite(prjName, testCycleId, verdicts);
        } catch (java.lang.InterruptedException | java.io.IOException | ApiException e) {
            System.out.println("Error updating test suite results");
            System.exit(1);
        }

        showProject(projectsApi);
        if (allTestsPassed) {
          System.exit(0);
        } else {
          System.exit(1);
        }
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
          System.out.println(e);
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

    private static String getApiKey() {
      Runtime r = Runtime.getRuntime();
      try {
          Process p = r.exec("printenv COMET_API_KEY");
          p.waitFor();

          BufferedReader b = new BufferedReader(new InputStreamReader(p.getInputStream()));
          String key = "";
          key = b.readLine(); // First result should be the key
          b.close();
          return key;
      } catch (java.lang.InterruptedException | java.io.IOException e) {
          System.err.println("Error getting API key");
          System.exit(1);
      }
      return "";
    }
}

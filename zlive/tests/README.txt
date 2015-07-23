This directory defines two kinds of tests for ZLive:

1.  unit tests ('ant test')
    These should be run after each change to ZLive, and should 
    normally all pass before changes are committed into CVS.
 
2.  user-level tests ('ant usertest')
    This tries evaluating about 500 Z expressions and predicates,
    which are defined in the ../../parser/tests/z/animate_*.tex files.
    These will not all pass, since not all Z features are handled by ZLive
    yet -- the goal is to measure our progress towards a complete animator.

As we implement more features of Z, and develop better animation
algorithms, more and more of the user-level tests should pass.

The UserTest-Statistics.csv file records our progress statistically.
(It is quite fun to load UserTest-Statistics.csv into a spreadsheet
program like Excel, and graph the progress over time.)

The format of each line is comma-separated fields:
    Date,         the date of the test results
    Change,       a short description of changes made to ZLive
    File1Total,   total number of tests in File1.tex
    File2Passed,  number of those tests (in File1.tex) that passed.
    ...
    ...
    FileNTotal,   total number of tests in FileN.tex
    FileNPassed,  number of those tests (in FileN.tex) that passed.

In addition, the UserTest-Results directory stores the actual junit
output files (TEST-.....Animate*.txt) that correspond to each line
in UserTest-Statistics.csv.

Warning: individual tests are identified just by their line number in
the source animate*.tex file, so it is best to add new tests at the end.
If you do add/delete lines within those files, you should update the
UserTest-Results by copying the new TEST-...Animate*.txt files in there,
so that future comparisons will be meaningful.

After making a change to ZLive, you should:
1.  ant test         (to check that the unit tests all pass)
2.  ant usertest     (to run the user-level tests)
3.  ant compare      (to compare your new usertest output with the previous
                      output stored in the UserTest-Results directory, to see
                      if more user-level tests now pass).
4.  cvs commit src (if all the unit tests pass)

In addition, if your changes cause more of the user-level tests 
to pass, you should add a new line at the end of UserTest-Statistics.csv
as follows:

5.  ant usertest_compare
6.  add a line at the end of UserTest-Statistics.csv (*)
7.  copy all your new TEST-net.sourceforge...Animate*Test.txt files into
       the UserTest-Results directory.
8.  cvs commit tests  (commit the new statistics and results files).

(*) Note that you must do some arithmetic to translate the jUnit output
    for each test into the Total,Passed numbers in the statistics file,
    because JUnit shows the TOTAL number of tests, then the number of 
    FAILURES and ERRORS like this: 
    [junit] Tests run: 214, Failures: 163, Errors: 10, Time elapsed: 0,711 sec
    [junit] TEST net.sourceforge.czt.animation.eval.AnimateSetsTest FAILED
    This means that 41 tests passed (= 214-163-10), so we actually add
    214,41 in the statistics file, under the Sets columns.


Historical note:
   The UserTest-Results directory was added in May 2005, and
   the results of earlier test runs were added to it at that time.
   (Previously, each set of output files was stored in a separate
   directory, which was not very CVS-friendly).
   You can use 'cvs log UserTest-Results/TEST-*SetsTest.txt' to see
   descriptions of all the versions available -- their original dates
   are mentioned in the change descriptions.

   If you want to compare the current ZLive output against one of these
   older results (software archaeology?), you can do 'cvs update -rNN.NN
   UserTest-Results', where NN.NN is the the particular version of the
   results files that you want, then run 'ant compare' as usual.  When
   you do this, the line numbers of newly passing tests (the '+'
   lines) should be accurate, but the line numbers of any lost tests
   (the '-' lines are for tests that used to pass, but now fail) will
   not usually be accurate, unless you use cvs to check out an old
   version of the source .tex files (../../parser/tests/z/animate_*.tex)
   and run 'ant usertest_compare' again.  (And in this case, the '-'
   line numbers should be accurate, but the '+' line numbers may be wrong).



# Z/EVES Eclipse prover IDE

Community Z Tools provide an Eclipse-based IDE and integration with Z/EVES theorem prover. This extends the development of Z specifications in CZT with theorem proving and verification capabilities.

**Z/EVES Eclipse** provides a modern environment to use the Z/EVES theorem prover. It is an alternative to the original Z/EVES UI, which is no longer in development and has issues when used with modern operating systems.

Z/EVES Eclipse brings the Z/EVES theorem prover to a modern IDE and supports all Z/EVES functionality: writing and sending proof commands to the prover, viewing proof output, querying lemmas, section management, etc.

[![Z/EVES Eclipse](images/zeves-full.png)](images/zeves-full.png "Z/EVES Eclipse")


## Getting started

To get started with Z/EVES in Eclipse, use the **zeves** dialect and the Z/EVES perspective, configure and launch the Z/EVES prover, and submit your proof script commands to the prover. The following steps provide slightly more details.

1.  Get Z/EVES Eclipse: it comes together with [CZT IDE][download]. Alternatively, install it from the [CZT update site][download].

2.  [Setup][create-project] your Z/EVES project.

3.  Make sure to select the **zeves** dialect in [Z compiler preferences][dialect-prefs]!

    Otherwise Z/EVES statements (e.g. proof commands) will not be recognised. Reload the open editors after selecting the dialect.

4.  Select the **Z/EVES perspective** via menu: **Window > Open Perspective > Other... > Z/EVES**.

    The Z/EVES views will be opened and arranged - they give a proof-centric view of developing Z specifications.

5.  Configure and launch the Z/EVES prover [launch configuration][launch-config] in **Run > External Tools > External Tools Configurations > Z/EVES**.

6.  Open your Z/EVES specification.

7.  Submit specification contents to the Z/EVES prover using the toolbar buttons ![Submit back](images/submit_back.png)![Submit next](images/submit_next.png)![Submit to point](images/submit_point.png). These submit the next command to the prover, go back one command or submit everything up to the cursor, respectively.

    For your convenience, use keyboard shortcuts for these commands: **Shift + Ctrl + Up/Down/Enter** (use the **Cmd** key instead of Ctrl on Mac OS X).

8.  The submitted commands are highlighted. Use the **Z/EVES Output** view to inspect prover output (e.g. outstanding goals) at the selected command.

9.  Select **Force Unicode** ![Force Unicode](images/utf.png) in the Z/EVES Output view toolbar to show unicode-rendered prover output.

10.  Write new proof commands directly to the specification; or use menus available in the Z/EVES Output view to drive the theorem prover.

11.  Refresh ![Refresh](images/refresh.gif) other Z/EVES views (e.g. **Theorems**) to get the newest information from the prover.

[download]: ../download.html
[create-project]: ../help/getting-started/create-project.html
[dialect-prefs]: ../help/reference/preferences/compiler.html
[launch-config]: help/getting-started/launch-zeves.html


## Features

Z/EVES Eclipse supports all Z/EVES features and provides a convenient integration with other Community Z Tools. Some of the features are listed below:

-   [Z/EVES launch configurations][launch-config]

-   Z/EVES dialect for typesetting Z specifications in Z/EVES style + support for proofs and proof commands.

-   Actions to submit proof commands to Z/EVES either one-by-one, or "everything up to the cursor".

-   Undo when editing: when you edit the document, the Z/EVES prover will be rolled back to the edit point (no need to undo manually).

-   Markers for erroneous Z/EVES commands are displayed in the specification.

-   Asynchronous proof output display: select the command to view its results or outstanding goals in the **Z/EVES Output** view.

-   Support viewing Z/EVES output in Unicode even when developing in Z LaTeX.

-   Select proof commands from the menus in the **Z/EVES Output** view.

-   Context-specific proof commands are available via context menu in the **Z/EVES Output** view.

-   **Section management** (not supported by the original Z/EVES UI!)

    -   Develop your Z/EVES specification using Z sections: all dependencies will be submitted to the prover as well.

    -   Undo the whole section in the **Z/EVES** view.

-   View theorems, axioms and their proof status in the **Theorems** view.

Read more about the CZT and Z/EVES Eclipse features in the documentation.

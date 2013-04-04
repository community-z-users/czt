# Launching Z/EVES

Community Z Tools provides a prover IDE to use with Z/EVES theorem prover. To start proving, you need to select and launch a Z/EVES application. CZT allows multiple such _launch configurations_ to be set up.

The launch configurations can be managed by selecting **Run > External Tools > External Tools Configurations...** or the corresponding toolbar drop-down button ![External tools launch](../images/external-tools-icon.gif):

![Launch configurations toolbar button](../images/zeves-launch-toolbar.png)

_Note: the toolbar and menu items afterwards allow quickly launching the last Z/EVES configuration again._


## Select Z/EVES application

When configuring Z/EVES to launch, you need to indicate where the Z/EVES executable is located and its working directory. When launched, Z/EVES prover will be started and linked with CZT IDE.

![Z/EVES launch configuration](../images/zeves-launch-config.png)

1.  Select **Z/EVES** launch type on the left of the dialog.
2.  Either double-click the selected type or use **New** button to create a new launch configuration (screenshot above).
3.  Select **Z/EVES executable** in the first field:

    -   Windows: Use _\<zeves\>/system/z-eves-pc-windows-lispworks.exe_
    -   Linux: Use _\<zeves\>/system/z-eves.sh_ or equivalent
    -   Mac OS X: Use some script that starts [Wine][wine] with the Windows version of Z/EVES
4.  Select **Working directory** to point to Z/EVES installation directory.
5.  (Optional) You can also change a communications port to use with the Z/EVES prover in **Port**, e.g. if it clashes with some other application.
6.  Click **Run** to launch Z/EVES process.


## Launch Z/EVES

The launch progress is displayed in the bottom-right corner. You can verify whether Z/EVES has been launched successfully in the _Z/EVES_ view (refresh ![Refresh](../images/refresh.gif) it if needed).

![Z/EVES prover status - Z/EVES view](../images/zeves-prover-status.png)

[wine]: http://www.winehq.org

If the connection to Z/EVES fails, a dialog will open with notification. Note that it may take some time to start Z/EVES on Mac OS X, so you can choose to **Retry** there.

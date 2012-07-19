# Create composite p2 repository

[Composite p2 repositories][p2-comp] allow aggregating content from multiple p2
repositories. This way we can include other m2e plugins required to build CZT
in the same repository. Thus the end users do not need to collect all dependencies
manually - they can all be retrieved from the update site.

[p2-comp]: http://wiki.eclipse.org/Equinox/p2/Composite_Repositories_(new)

## Running the script

The `comp-repo.sh` shell script builds (or modifies) a composite p2 repository.
Below is a sample execution that produces the 'latest' composite repository
that contains the CZT m2e update site together with related m2e connector
update sites, which are not part of the m2e marketplace.

The assumption here is that this composite repository is placed under
`http://czt.sourceforge.net/dev/eclipse/updates/latest`
and the actual CZT m2e repository is under
`http://czt.sourceforge.net/dev/eclipse/updates/latest/czt`.


    ./comp-repo.sh <REPO_DIR> --eclipse <ECLIPSE_DIR> \
    --name "CZT m2e Support p2 Composite Repository" \
    add http://czt.sourceforge.net/dev/eclipse/updates/latest/czt \
    add http://objectledge.github.com/maven-extensions/connectors/updates/development \
    add http://nl-mwensveen-m2e-extras.googlecode.com/svn/trunk/p2

See [the blog post][comp-repo-blog] for more details on the script and its arguments.

[comp-repo-blog]: http://eclipsesource.com/blogs/2012/06/11/creating-p2-composite-repositories-on-the-command-line/


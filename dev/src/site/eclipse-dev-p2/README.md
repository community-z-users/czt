# Create composite p2 repository

[Composite p2 repositories][p2-comp] allow aggregating content from multiple p2
repositories. This way we can include other m2e plugins required to build CZT
in the same repository. Thus the end users do not need to collect all dependencies
manually - they can all be retrieved from the update site.

[p2-comp]: http://wiki.eclipse.org/Equinox/p2/Composite_Repositories_(new)


## Running the script

To run the script, use Maven build in /dev subdirectory with the following command:

    mvn generate-sources -P regenerate-p2-repo -N -Declipse.dir=ECLIPSE_DIR


## Running the script standalone

The `comp-repo.sh` shell script builds (or modifies) a composite p2 repository.
Below is a sample execution that produces a composite repository
that contains the m2e connector updates sites required for building CZT,
which are not part of the m2e marketplace.


    ./comp-repo.sh <REPO_DIR> --eclipse <ECLIPSE_DIR> \
    --name "CZT m2e Support" \
    add http://objectledge.github.io/maven-extensions/connectors/updates/development \
    add http://mwensveen-nl.github.io/nl-mwensveen-m2e-extras/p2/release/

See [the blog post][comp-repo-blog] for more details on the script and its arguments.

[comp-repo-blog]: http://eclipsesource.com/blogs/2012/06/11/creating-p2-composite-repositories-on-the-command-line/


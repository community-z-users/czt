#creates the branch
svn cp https://czt.svn.sourceforge.net/svnroot/czt/trunk https://czt.svn.sourceforge.net/svnroot/czt/branches/tsm -m "Branching development version of transactional section manager. Parsing works mostly, except in weird cases, hence the branch. At Revision 8138." 

# switch the main working copy to the branch
svn switch https://czt.svn.sourceforge.net/svnroot/czt/branches/tsm

# double check we are the branch directory
svn info | grep URL

# commit local changes as usual - just check where one is
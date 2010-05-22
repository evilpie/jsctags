* Instead of recursing downward through the directories and building up
  module IDs and package IDs as we go, just search upward for package.json
  files and the libdirs specified on the command line for each file. It'd make
  usage more friendly and bin/jsctags.js simpler.

* Figure out what to do about class construction via mixins. Maybe hash the
  contents of some functions and delegate to native JS code?


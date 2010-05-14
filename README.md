Requirements
------------
* node.js

Directory structure
-------------------

The directory structure is somewhat unusual, in order to work around the
restrictive security policies in modern browsers for `file:` URIs.

* `bin/`: tools runnable from node.js (should be directly executable in Unix)
* `src/`: tools runnable in a browser
* `src/js/`: non-CommonJS-compliant libraries, mostly for the browser tools
* `src/lib/`: CommonJS-compliant libraries


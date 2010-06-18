#!/usr/bin/env node

var argv = process.argv;
var path = require('path');
require.paths.unshift(path.join(path.dirname(argv[1]), "..", "lib",
    "jsctags"));

var ctags = require('ctags'), fs = require('fs'), sys = require('sys');

var tags = new ctags.Tags();
var str = fs.readFileSync(argv[2]);
tags.readString(str);

var result = (argv.length >= 4) ? tags.stem(argv[3]) : tags.tags;
sys.puts(sys.inspect(result));


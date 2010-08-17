// jsctags/typo/servetypes.js

var parse = require('../narcissus/jsparse').parse;
var getTags = require('../narcissus/jscfa').getTags;

// string -> string (representing JSON array)
// s is a string that contains javascript source
function cfa2ToJSON(s) {
  var lines = s.split("\n");
  var ast = parse(s, "js", 1);
  var tags = getTags(ast, "js", lines, {});
  var stags = [];

  tags.forEach(function(t) { stags.push(tagToJSON(t)); });
  return "[" + stags.join() + "]";
}

function tagToJSON(t) {
  var a = [];
  for (var p in t)
    if (t.hasOwnProperty(p))
      a.push("\"" + p + "\" : " + "\"" + t[p] +"\"");
  return "{" + a.join() + "}";
}

exports.cfa2ToJSON = cfa2ToJSON;


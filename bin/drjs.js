#!/usr/bin/env node
/* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is Bespin.
 *
 * The Initial Developer of the Original Code is
 * Mozilla.
 * Portions created by the Initial Developer are Copyright (C) 2009
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Bespin Team (bespin@mozilla.com)
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU General Public License Version 2 or later (the "GPL"), or
 * the GNU Lesser General Public License Version 2.1 or later (the "LGPL"),
 * in which case the provisions of the GPL or the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of either the GPL or the LGPL, and not to allow others to
 * use your version of this file under the terms of the MPL, indicate your
 * decision by deleting the provisions above and replace them with the notice
 * and other provisions required by the GPL or the LGPL. If you do not delete
 * the provisions above, a recipient may use your version of this file under
 * the terms of any one of the MPL, the GPL or the LGPL.
 *
 * ***** END LICENSE BLOCK ***** */

var argv = process.argv;
var path = require('path');
require.paths.unshift(path.join(path.dirname(argv[1]), "..", "lib",
    "jsctags"));

var _ = require('underscore')._;
var http = require('http');
var url = require('url');
var getTags = require('narcissus/jscfa').getTags;
var parse = require('narcissus/jsparse').parse;

http.createServer(function(req, resp) {
  if (url.parse(req.url).pathname !== '/analyze') {
    resp.writeHead(404, "Not Found", { 'Content-type': 'text/plain' });
    resp.end("404 Not Found");
    return;
  }

  var buf = [];
  req.on('data', _(buf.push).bind(buf));
  req.on('end', function() {
      var lines = buf.join("").split("\n");
      try {
        var ast = parse(lines, "js", 1);
        var tags = getTags(ast, "js", lines, {});
        
        resp.writeHead(200, "OK", { 'Content-type': 'application/json' });
        resp.end(JSON.stringify(tags));
      }
      catch (e) {
        throw new Error(lines);
      }
  });
}).listen(8080, "127.0.0.1");


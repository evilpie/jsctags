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
 
var cwd = path.dirname(argv[1]);
var libdir = path.join(cwd, "..", "lib");
 
require.paths.unshift(path.join(libdir, "jsctags"),
                      path.join(libdir, "formidable"));
  
var sys = require('sys');
var _ = require('underscore')._;
var http = require('http');
var url = require('url');
var formidable = require('formidable');
var getTags = require('narcissus/jscfa').getTags;
var parse = require('narcissus/jsparse').parse;

http.createServer(function(req, resp) {
  function error(code, msg) {
    resp.writeHead(code, "Not Found", { 'Content-type': 'text/plain' });  
    resp.end(code + " " + msg);
  }
 
  if (url.parse(req.url).pathname !== '/analyze') {
    error(404, "Not Found");
    return;
  }
 
  if (req.method !== 'POST') {
    error(405, 'Only POST method allowed');
    return;                                        
  }

  // FIXME: prevent formidable from saving files
  var form = new formidable.IncomingForm();
  var src;

  form
    .addListener('error', function(err) {
      error(400, err);
    })
    .addListener('field', function(field, value) {
      if (field === 'src')
        src = value;
    })
    .addListener('end', function() {
      if (!src) {
        error(400, 'No "src" field in POST');
        return;
      }

      // farm the work out to rn.js
      var spawn = require('child_process').spawn;
      var rn = spawn(path.join(cwd, 'rn.js'));

      // on timeout, kill the process and send an error
      setTimeout(function() {
        rn.kill(); // ooh, brutal ;)
        error(500, "Service timed out");
      }, 10000);

      // send the input program to rn.js
      rn.stdin.end(src);

      // forward the output ctags to the response
      var buf = [];
      rn.stdout.on("data", _(buf.push).bind(buf));
      rn.stdout.on("end", function() {
        resp.writeHead(200, "OK", { "Content-type": "application/json" });
        resp.end(buf.join(""));
      });
    });

  form.parse(req);
}).listen(8080, "127.0.0.1");

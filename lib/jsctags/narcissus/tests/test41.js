// unsoundness in Array.prototype.shift
function test(expected) {
  var a = new Array(10, "1");
  a.shift();
  return a[0];
}

test(0); // should be a string

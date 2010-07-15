// unsoundness in Array.prototype.push
function test(expected) {
  var a = new Array();
  a.push(1, 2);
  a[0] = "";
  return a[0];
}

test(""); // doesn't see that a[0] could contain two types.

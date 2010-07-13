// unsoundness due to [] access, doesn't see that o[i] can be a number as well.
function test(expected) {
  function Foo(){}

  var o = new Foo();
  var i = 1;
  o[1] = 123;
  o[i] = "asdf";
  return o[i];
}

test("0");

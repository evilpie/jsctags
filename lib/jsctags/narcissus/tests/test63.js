// evalExp/INDEX: n[0] throws
function test(expected) {
  function t() {throw new Error("asdfaafs");}

  function Foo() {this.foo = 123;}

  try {
    (function(){
      if (123)
        return new Foo();
      else
        t();}())["foo"];
  }
  catch (e) {
    return e.message;
  }
}

test("");

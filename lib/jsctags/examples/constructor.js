var x;

function foo() {
    x = 123;
}

var u = foo();

function Bar(x) {
    this.x = x;
}

var b = (new Bar(4)).x;

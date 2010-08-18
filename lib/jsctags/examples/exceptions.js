function findLargest(a) {
    if (a.length === 0) throw new Error("empty array");
    var max = a[0];
    for (var i = 1, l = a.length; i < l; i++)
        if (a[i] > max)
            max = a[i];
    return max;
}

function foo() {
    var a = [1,2,3];

    try {
        return findLargest(a);
    }
    catch (e) {
        return e.message;
    }
}

foo();

// ==, !=, ===, !==, <, <=, >=, > throw
function test(expected) {
  function t() { throw new Error(); }

  try {
    t() == 321 != "afd" !== t() < false <= true >= t() > -321;
  }
  catch (e) {
    return e.message;
  }
}

test("");

// ==, !=, ===, !==, <, <=, >=, >
function test(expected) {
  return 123 == 321 != "afd" !== true < false <= true >= 0 > -321;
}

test(true);

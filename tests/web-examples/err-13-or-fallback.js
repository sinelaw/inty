function label(n) {
    var name = n || "Guest";
    return name;
}

// Try to call label with a number — the blurb says || requires
// operands to agree.
var r = label(3);

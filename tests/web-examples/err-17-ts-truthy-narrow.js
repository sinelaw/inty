function priceLabel(price) {
    if (price) { return "$" + price; }
    else       { return "free"; }
}

// The blurb claims `+` mixes String and Number and surfaces a bug.
// Try calling priceLabel with a Number.
var lbl = priceLabel(0);

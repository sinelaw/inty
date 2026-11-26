// A record passed where a record with a different member is expected:
// the member whose types differ is named, even when what fails inside it
// isn't a plain mismatch (an array lacks a property the other side reads).
/** type Pane = {title: String, rows: Number[]} */
/** function show(p: {title: String, rows: {size: Number}}) => Number */
function show(p) { return p.rows.size; }
/** const pane: Pane */
const pane = {title: "a", rows: [1, 2]};
show(pane);

// Deeper: the innermost member is named (`view.pane.rows`).
/** type View = {name: String, pane: Pane} */
/** function draw(v: {view: {name: String, pane: {title: String, rows: {size: Number}}}}) => Number */
function draw(v) { return v.view.pane.rows.size; }
/** const w: {view: View} */
const w = {view: {name: "v", pane: pane}};
draw(w);

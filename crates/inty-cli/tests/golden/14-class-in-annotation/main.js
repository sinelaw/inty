// A class whose field is set from an unannotated constructor parameter
// is generic in that field's type: naming it without an argument says
// which field, and that `Box<Number>` names it.
class Box {
  constructor(value) { this.value = value; }
}
/** function current(b: Box) => Number */
function current(b) { return b.value; }

// TypeScript keeps a property narrowed after `!== null` even across a
// call that sets it back to `null`. With full JSDoc types and `--strict`,
// tsc accepts this, and at runtime `session.user` is null.
//
// Inty doesn't narrow a property through a test at all: the property may
// change between the test and the use. Copy it into a `const` and test
// that instead (see nullable.js).

/** type Session = {user: String | Null} */

/** const session: Session */
const session = { user: "ann" };

function logout() { session.user = null; }

if (session.user !== null) {
    logout();
    console.log(session.user.toUpperCase());
    // Inty: 'toUpperCase' not found in String | Null: the value may be null.
}

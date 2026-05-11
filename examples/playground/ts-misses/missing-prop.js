// Object literals produce *closed* rows in inty — what you wrote is
// all that's there. Reading a missing field is a structural error.
//
// In TypeScript without explicit types, this often types as `any`
// (via implicit-any or noImplicitAny=false) and slips through.

function fullName(user) {
    return user.firstName + " " + user.lastName;
}

var name = fullName({ name: "Alice", id: 42 });
//                        ^^^^^^^^^^^^^^^^^^
// Inty: `firstName` not found in `{name: String, id: Number}`.
// TS (.js, no types): silently `any` — caller sees no error.

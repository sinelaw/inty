// Default-import entry point. Run with:
//
//     inty examples/modules/app-default.js
//
// Each `import name from "./mod.js";` binds the module's `export default`
// under whatever local name the importer chooses — `hello` here is the
// function exported as `greet`, and `version` is the bare string from
// `version.js`.

import hello from "./greet.js";
import version from "./version.js";

const banner = `${hello("world")} (v${version})`;
console.log(banner);

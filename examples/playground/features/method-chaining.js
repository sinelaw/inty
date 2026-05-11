// Builder pattern — `return this` produces equi-recursive types.
// The chain types itself, no annotations.

var request = {
    url: "",
    method: "GET",
    setUrl:    function(u) { this.url = u;    return this; },
    setMethod: function(m) { this.method = m; return this; },
    send:      function()  { return this.method + " " + this.url; }
};

var response = request
    .setUrl("/api/users")
    .setMethod("POST")
    .send();

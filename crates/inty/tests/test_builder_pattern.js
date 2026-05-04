// Builder pattern demonstrating equi-recursive types
// Methods return 'this' to enable fluent chaining

function createUserBuilder() {
    return {
        name: "",
        age: 0,
        email: "",

        withName: function(n) {
            this.name = n;
            return this;
        },

        withAge: function(a) {
            this.age = a;
            return this;
        },

        withEmail: function(e) {
            this.email = e;
            return this;
        },

        build: function() {
            return {
                name: this.name,
                age: this.age,
                email: this.email
            };
        }
    };
}

// Fluent chaining: each method returns the builder itself
var user = createUserBuilder()
    .withName("Alice")
    .withAge(30)
    .withEmail("alice@example.com")
    .build();

// Another example: HTTP request builder
var requestBuilder = {
    url: "",
    method: "GET",
    headers: "",

    setUrl: function(u) {
        this.url = u;
        return this;
    },

    setMethod: function(m) {
        this.method = m;
        return this;
    },

    setHeaders: function(h) {
        this.headers = h;
        return this;
    },

    send: function() {
        return this.method + " " + this.url;
    }
};

var response = requestBuilder
    .setUrl("/api/users")
    .setMethod("POST")
    .setHeaders("Content-Type: application/json")
    .send();

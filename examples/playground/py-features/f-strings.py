# F-strings are typed end-to-end. Each interpolation is checked,
# so misspelt names or type errors inside `{ … }` surface here, not
# at runtime.

def greeting(name, count):
    return f"hi {name}, this is message #{count + 1}"

msg = greeting("ada", 0)

# Method calls and arithmetic both work inside the braces.
items = ["apple", "fig"]
header = f"{len(items)} items, starting with {items[0].upper()}"

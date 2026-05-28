# Methods are language-specific. JavaScript array methods don't
# exist on a Python `list`, and JavaScript string methods don't
# exist on a Python `str`. Inty enforces the Python surface.

xs = [1, 2, 3]
xs.push(4)              # JS Array.push — not a Python list method

s = "hello"
c = s.charAt(0)         # JS String.charAt — not a Python str method

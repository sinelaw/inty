# Python `str` methods are typed individually. Each call's result
# flows through the rest of the program with its real type.

s = "Hello, World"

upper = s.upper()                  # String
parts = s.split(", ")              # list[String]
joined = " / ".join(parts)         # String
clean = "  hi  ".strip()           # String
swapped = s.replace("World", "Inty")
yes = s.startswith("Hello")        # Bool
n = len(s)                         # Number

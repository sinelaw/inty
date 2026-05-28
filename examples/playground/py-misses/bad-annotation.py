# A value that contradicts its annotation is a type error. Here the
# variable is annotated `int` but initialised with a String, so inty
# rejects the program.

n: int = "not a number"

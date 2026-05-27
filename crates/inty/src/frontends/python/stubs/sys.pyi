# Built-in `sys` module stub for inty. Members inty can't model precisely
# (the text streams) are exposed opaquely.
argv: list[str]
path: list[str]
version: str
platform: str
maxsize: int
stdin: object
stdout: object
stderr: object
def exit(code: int = ...) -> None: ...
def getsizeof(obj: object) -> int: ...

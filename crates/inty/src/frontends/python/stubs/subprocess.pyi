# Built-in `subprocess` module stub for inty.
class CompletedProcess:
    def __init__(self) -> None: ...
    returncode: int
    stdout: str
    stderr: str

class CalledProcessError:
    def __init__(self) -> None: ...
    returncode: int
    cmd: list[str]

PIPE: int
DEVNULL: int
STDOUT: int
def run(
    cmd: list[str],
    capture_output: bool = ...,
    text: bool = ...,
    check: bool = ...,
    shell: bool = ...,
    cwd: str = ...,
    input: str = ...,
    encoding: str = ...,
    timeout: float = ...,
    stdout: int = ...,
    stderr: int = ...,
    stdin: int = ...,
    env: dict[str, str] = ...,
) -> CompletedProcess: ...
def call(cmd: list[str], shell: bool = ..., cwd: str = ...) -> int: ...
def check_call(cmd: list[str], shell: bool = ..., cwd: str = ...) -> int: ...
def check_output(
    cmd: list[str],
    text: bool = ...,
    shell: bool = ...,
    cwd: str = ...,
    encoding: str = ...,
) -> str: ...

# Built-in `argparse` module stub for inty. Parsed namespaces are dynamic,
# so `parse_args()` returns an opaque value.
class ArgumentParser:
    def __init__(
        self,
        prog: str = ...,
        description: str = ...,
        epilog: str = ...,
        formatter_class: object = ...,
        add_help: bool = ...,
        allow_abbrev: bool = ...,
    ) -> None: ...
    def add_argument(
        self,
        name: str,
        help: str = ...,
        default: object = ...,
        type: object = ...,
        action: str = ...,
        nargs: object = ...,
        dest: str = ...,
        required: bool = ...,
        choices: object = ...,
        metavar: str = ...,
        const: object = ...,
    ) -> None: ...
    def parse_args(self) -> object: ...
    def add_subparsers(self) -> object: ...
    def print_help(self) -> None: ...

# authkit — a non-trivial uv demo project

A small JWT auth/session toolkit, used as a realistic target for type
checkers. It combines several common, non-trivial libraries:

- **pydantic v2** — domain models, validators, computed fields, enums
- **PyJWT** — signing and verifying tokens
- **python-dateutil**, **httpx** — declared deps (the kind a real service pulls in)
- **argparse** — a small CLI front-end

## Layout

```
src/authkit/
  models.py    # pydantic BaseModels, Enum roles, computed fields
  config.py    # settings model + from_env constructor
  tokens.py    # PyJWT encode/decode wrapper
  service.py   # business logic: login, authenticate, role checks
  cli.py       # argparse entry point
  errors.py    # exception hierarchy
tests/
  test_tokens.py
```

## Developer tasks

```sh
make install     # uv sync
make check       # CI: ruff lint + format check + ty type-check + pytest
make typecheck   # ty check
make test        # pytest
make inty        # run inty over src/ the way ty is run (scripts/inty-check.sh)
```

`make check` is the canonical CI gate (`ty`); `make inty` runs the
[inty](../../README.md) checker over the same sources for comparison.

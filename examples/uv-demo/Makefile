# CI-style developer tasks for the authkit demo project.
#
# `make check` is what CI runs: lint + format-check + type-check + tests.
# `make inty` runs the inty type checker over the same sources, the way
# `ty check` is run, for comparison (see scripts/inty-check.sh).

.PHONY: install lint fmt typecheck test check inty clean

install:
	uv sync

lint:
	uv run ruff check src tests

fmt:
	uv run ruff format --check src tests

typecheck:
	uv run ty check

test:
	uv run pytest -q

check: lint fmt typecheck test

inty:
	./scripts/inty-check.sh

clean:
	rm -rf .venv .ruff_cache .pytest_cache

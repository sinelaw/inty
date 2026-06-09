"""Exception hierarchy for the toolkit."""

from __future__ import annotations


class AuthError(Exception):
    """Base class for every error this package raises."""


class InvalidToken(AuthError):
    """The token was malformed, had a bad signature, or failed a claim check."""


class ExpiredToken(InvalidToken):
    """The token's `exp` claim is in the past."""


class PermissionDenied(AuthError):
    """The authenticated principal lacks a required role."""

    def __init__(self, required: str, held: list[str]) -> None:
        self.required = required
        self.held = held
        super().__init__(f"role {required!r} required; principal holds {held!r}")

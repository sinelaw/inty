"""Round-trip tests for the token codec and service."""

from __future__ import annotations

import pytest

from authkit.config import AuthSettings
from authkit.errors import ExpiredToken, PermissionDenied
from authkit.models import Role, User
from authkit.service import AuthService
from authkit.tokens import TokenCodec

SECRET = "test-secret-with-at-least-32-bytes-of-entropy"


def make_service() -> AuthService:
    settings = AuthSettings(secret=SECRET)
    return AuthService(TokenCodec(settings))


def make_user() -> User:
    return User(
        id=7,
        email="ada@example.com",
        display_name="Ada",
        roles=[Role.EDITOR],
    )


def test_round_trip() -> None:
    service = make_service()
    raw = service.login(make_user())
    token = service.authenticate(raw)
    assert token.sub == "7"
    assert Role.EDITOR in token.roles
    assert token.ttl_seconds > 0


def test_expired_token() -> None:
    service = make_service()
    raw = service.login(make_user(), ttl_seconds=-120)
    with pytest.raises(ExpiredToken):
        service.authenticate(raw)


def test_role_enforcement() -> None:
    service = make_service()
    token = service.authenticate(service.login(make_user()))
    service.require_role(token, Role.EDITOR)
    with pytest.raises(PermissionDenied):
        service.require_role(token, Role.ADMIN)

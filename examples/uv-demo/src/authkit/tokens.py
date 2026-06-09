"""JWT encode/decode, wrapping PyJWT."""

from __future__ import annotations

from datetime import UTC, datetime, timedelta
from typing import Any

import jwt
from jwt.exceptions import ExpiredSignatureError, PyJWTError

from authkit.config import AuthSettings
from authkit.errors import ExpiredToken, InvalidToken
from authkit.models import Role, Token, User


class TokenCodec:
    """Encodes `User`s into signed JWTs and decodes them back into `Token`s."""

    def __init__(self, settings: AuthSettings) -> None:
        self.settings = settings

    def issue(self, user: User, *, ttl_seconds: int | None = None) -> str:
        now = datetime.now(UTC)
        ttl = ttl_seconds if ttl_seconds is not None else self.settings.default_ttl_seconds
        expires = now + timedelta(seconds=ttl)
        payload: dict[str, Any] = {
            "sub": str(user.id),
            "email": user.email,
            "roles": [role.value for role in user.roles],
            "iat": int(now.timestamp()),
            "exp": int(expires.timestamp()),
            "iss": self.settings.issuer,
            "aud": self.settings.audience,
        }
        return jwt.encode(payload, self.settings.secret, algorithm=self.settings.algorithm)

    def decode(self, raw: str) -> Token:
        try:
            claims: dict[str, Any] = jwt.decode(
                raw,
                self.settings.secret,
                algorithms=[self.settings.algorithm],
                issuer=self.settings.issuer,
                audience=self.settings.audience,
                leeway=self.settings.leeway_seconds,
            )
        except ExpiredSignatureError as exc:
            raise ExpiredToken(str(exc)) from exc
        except PyJWTError as exc:
            raise InvalidToken(str(exc)) from exc

        roles = [Role(value) for value in claims.get("roles", [])]
        return Token(
            sub=claims["sub"],
            roles=roles,
            issued_at=datetime.fromtimestamp(claims["iat"], tz=UTC),
            expires_at=datetime.fromtimestamp(claims["exp"], tz=UTC),
        )

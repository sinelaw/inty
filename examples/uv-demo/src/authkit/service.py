"""The high-level service tying models, codec and policy together."""

from __future__ import annotations

from collections.abc import Iterable

from authkit.errors import PermissionDenied
from authkit.models import Role, Token, User
from authkit.tokens import TokenCodec


class AuthService:
    """Issues tokens for users and authorizes decoded tokens against roles."""

    def __init__(self, codec: TokenCodec) -> None:
        self.codec = codec
        self._users: dict[str, User] = {}

    def register(self, user: User) -> None:
        self._users[str(user.id)] = user

    def login(self, user: User, *, ttl_seconds: int | None = None) -> str:
        self.register(user)
        return self.codec.issue(user, ttl_seconds=ttl_seconds)

    def authenticate(self, raw: str) -> Token:
        """Decode a raw JWT into validated `Token` claims."""
        return self.codec.decode(raw)

    def require_role(self, token: Token, role: Role) -> None:
        if role not in token.roles:
            held = [r.value for r in token.roles]
            raise PermissionDenied(role.value, held)

    def require_any(self, token: Token, roles: Iterable[Role]) -> Role:
        wanted = list(roles)
        for role in wanted:
            if role in token.roles:
                return role
        held = [r.value for r in token.roles]
        raise PermissionDenied("|".join(r.value for r in wanted), held)

    def whoami(self, raw: str) -> str:
        token = self.authenticate(raw)
        roles = ", ".join(sorted(r.value for r in token.roles)) or "(none)"
        return f"{token.sub} [{roles}]"

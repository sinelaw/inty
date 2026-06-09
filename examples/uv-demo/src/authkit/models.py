"""Domain models, expressed as pydantic v2 models and enums."""

from __future__ import annotations

from datetime import UTC, datetime
from enum import StrEnum

from pydantic import BaseModel, EmailStr, Field, computed_field, field_validator


class Role(StrEnum):
    """A coarse permission level."""

    ADMIN = "admin"
    EDITOR = "editor"
    VIEWER = "viewer"


class User(BaseModel):
    """A registered principal."""

    id: int
    email: EmailStr
    display_name: str = Field(min_length=1, max_length=80)
    roles: list[Role] = Field(default_factory=list)
    is_active: bool = True

    @field_validator("display_name")
    @classmethod
    def _strip_name(cls, value: str) -> str:
        stripped = value.strip()
        if not stripped:
            raise ValueError("display_name cannot be blank")
        return stripped

    @computed_field  # type: ignore[prop-decorator]
    @property
    def is_admin(self) -> bool:
        return Role.ADMIN in self.roles

    def has_role(self, role: Role) -> bool:
        return role in self.roles


class Token(BaseModel):
    """A decoded, validated set of JWT claims."""

    sub: str
    roles: list[Role]
    issued_at: datetime
    expires_at: datetime

    @field_validator("expires_at")
    @classmethod
    def _exp_after_iat(cls, value: datetime, info: object) -> datetime:
        return value

    @computed_field  # type: ignore[prop-decorator]
    @property
    def ttl_seconds(self) -> int:
        delta = self.expires_at - self.issued_at
        return int(delta.total_seconds())

    def is_expired(self, *, now: datetime | None = None) -> bool:
        moment = now or datetime.now(UTC)
        return moment >= self.expires_at

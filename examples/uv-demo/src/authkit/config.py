"""Runtime configuration."""

from __future__ import annotations

from pydantic import BaseModel, Field


class AuthSettings(BaseModel):
    """Signing/verification settings for the token codec."""

    secret: str = Field(min_length=16)
    algorithm: str = "HS256"
    issuer: str = "authkit"
    audience: str = "authkit-clients"
    leeway_seconds: int = 30
    default_ttl_seconds: int = 3600

    @classmethod
    def from_env(cls, env: dict[str, str]) -> AuthSettings:
        """Build settings from a string→string mapping (e.g. os.environ)."""
        return cls(
            secret=env["AUTHKIT_SECRET"],
            algorithm=env.get("AUTHKIT_ALG", "HS256"),
            issuer=env.get("AUTHKIT_ISSUER", "authkit"),
            audience=env.get("AUTHKIT_AUDIENCE", "authkit-clients"),
            leeway_seconds=int(env.get("AUTHKIT_LEEWAY", "30")),
            default_ttl_seconds=int(env.get("AUTHKIT_TTL", "3600")),
        )

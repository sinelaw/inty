"""A tiny argparse CLI exercising the toolkit end-to-end."""

from __future__ import annotations

import argparse
import os
import sys

from authkit.config import AuthSettings
from authkit.errors import AuthError
from authkit.models import Role, User
from authkit.service import AuthService
from authkit.tokens import TokenCodec


def _build_service() -> AuthService:
    settings = AuthSettings.from_env(dict(os.environ))
    return AuthService(TokenCodec(settings))


def cmd_issue(args: argparse.Namespace) -> int:
    service = _build_service()
    user = User(
        id=args.id,
        email=args.email,
        display_name=args.name,
        roles=[Role(r) for r in args.roles],
    )
    token = service.login(user, ttl_seconds=args.ttl)
    print(token)
    return 0


def cmd_whoami(args: argparse.Namespace) -> int:
    service = _build_service()
    try:
        print(service.whoami(args.token))
    except AuthError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="authkit")
    sub = parser.add_subparsers(dest="command", required=True)

    issue = sub.add_parser("issue", help="issue a token for a user")
    issue.add_argument("--id", type=int, required=True)
    issue.add_argument("--email", required=True)
    issue.add_argument("--name", required=True)
    issue.add_argument("--roles", nargs="*", default=[])
    issue.add_argument("--ttl", type=int, default=None)
    issue.set_defaults(func=cmd_issue)

    who = sub.add_parser("whoami", help="decode a token and print its principal")
    who.add_argument("token")
    who.set_defaults(func=cmd_whoami)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())

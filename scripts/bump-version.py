#!/usr/bin/env python3

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import List, Literal

RED = "\033[0;31m"
GREEN = "\033[0;32m"
YELLOW = "\033[1;33m"
BLUE = "\033[0;34m"
NC = "\033[0m"

BumpType = Literal["patch", "minor", "major"]

ROOT_CARGO = Path("Cargo.toml")

# Match the `version = "..."` line under [workspace.package].
WORKSPACE_VERSION_RE = re.compile(
    r'(\[workspace\.package\][^\[]*?\n\s*version\s*=\s*")([^"]+)(")',
    re.DOTALL,
)


def run(cmd: List[str], capture: bool = False, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=capture, text=True, check=check)


def get_current_version() -> str:
    match = WORKSPACE_VERSION_RE.search(ROOT_CARGO.read_text())
    if not match:
        raise ValueError("Could not find version under [workspace.package] in Cargo.toml")
    return match.group(2)


def calculate_new_version(current: str, bump_type: BumpType) -> str:
    major, minor, patch = map(int, current.split("-")[0].split("."))
    if bump_type == "patch":
        patch += 1
    elif bump_type == "minor":
        minor += 1
        patch = 0
    elif bump_type == "major":
        major += 1
        minor = 0
        patch = 0
    return f"{major}.{minor}.{patch}"


def update_workspace_version(new: str) -> None:
    content = ROOT_CARGO.read_text()
    new_content, count = WORKSPACE_VERSION_RE.subn(rf'\g<1>{new}\g<3>', content, count=1)
    if count != 1:
        raise RuntimeError("Failed to update [workspace.package] version")
    ROOT_CARGO.write_text(new_content)


def update_cargo_lock() -> None:
    try:
        run(["cargo", "build", "--quiet"])
    except subprocess.CalledProcessError as e:
        print(f"{YELLOW}Warning:{NC} cargo build returned non-zero (continuing)")
        if e.stderr:
            print(e.stderr)


def tag_exists_at_head(tag: str) -> bool:
    res = run(["git", "rev-parse", f"{tag}^{{commit}}"], capture=True, check=False)
    if res.returncode != 0:
        return False
    head = run(["git", "rev-parse", "HEAD"], capture=True).stdout.strip()
    return res.stdout.strip() == head


def main() -> None:
    parser = argparse.ArgumentParser(description="Bump version, commit, tag, and push.")
    parser.add_argument(
        "bump_type",
        nargs="?",
        default="patch",
        choices=["patch", "minor", "major"],
        help="The type of version bump (default: patch).",
    )
    parser.add_argument(
        "--skip-bump",
        action="store_true",
        help="Skip version bump, just tag and push current version.",
    )
    args = parser.parse_args()
    bump_type: BumpType = args.bump_type
    skip_bump: bool = args.skip_bump

    if not ROOT_CARGO.exists():
        print(f"{RED}Error: run this script from the repo root.{NC}")
        sys.exit(1)

    try:
        current = get_current_version()
    except ValueError as e:
        print(f"{RED}Error: {e}{NC}")
        sys.exit(1)

    new = current if skip_bump else calculate_new_version(current, bump_type)
    tag = f"v{new}"

    print(f"{BLUE}{'Tag and Push (skipping bump)' if skip_bump else f'Version Bump ({bump_type})'}{NC}")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    if skip_bump:
        print(f"Current version: {GREEN}{current}{NC}")
    else:
        print(f"Current version: {YELLOW}{current}{NC}")
        print(f"New version:     {GREEN}{new}{NC}")
    print(f"Tag:             {GREEN}{tag}{NC}")
    print("")
    print("This will:")
    if not skip_bump:
        print("  - Update [workspace.package] version in Cargo.toml")
        print("  - Run `cargo build` to refresh Cargo.lock")
        print("  - Commit the changes")
    print(f"  - Create tag {tag}")
    print("  - Push the current branch and the tag to origin")
    print("")
    print("GitHub Actions will then build, release, and publish to crates.io and npm.")
    print("")

    reply = input("Proceed? (y/N) ").strip().lower()
    if reply != "y":
        print("Aborted.")
        sys.exit(0)

    try:
        if not skip_bump:
            print("")
            print(f"{BLUE}Updating workspace version...{NC}")
            update_workspace_version(new)
            print(f"{GREEN}✓{NC} Cargo.toml updated")

            print(f"{BLUE}Refreshing Cargo.lock...{NC}")
            update_cargo_lock()
            print(f"{GREEN}✓{NC} Cargo.lock updated")

            print(f"{BLUE}Committing...{NC}")
            run(["git", "add", "Cargo.toml", "Cargo.lock"])
            run(["git", "commit", "-m", f"Bump version to {new}"])
            print(f"{GREEN}✓{NC} Committed")

        print(f"{BLUE}Tagging {tag}...{NC}")
        if tag_exists_at_head(tag):
            print(f"{GREEN}✓{NC} Tag {tag} already at HEAD, skipping")
        else:
            run(["git", "tag", tag])
            print(f"{GREEN}✓{NC} Tagged")

        branch = run(["git", "rev-parse", "--abbrev-ref", "HEAD"], capture=True).stdout.strip()
        print(f"{BLUE}Pushing branch {branch} and tag {tag}...{NC}")
        run(["git", "push", "origin", branch])
        run(["git", "push", "origin", tag])
        print(f"{GREEN}✓{NC} Pushed")

        print("")
        print(f"{GREEN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{NC}")
        print(f"{GREEN}✓ {tag} tagged and pushed.{NC}")
        print("")
        print(f"Monitor: {BLUE}https://github.com/sinelaw/minfern/actions{NC}")

    except subprocess.CalledProcessError as e:
        print(f"{RED}Git operation failed: {e}{NC}")
        if e.stderr:
            print(e.stderr)
        sys.exit(1)
    except FileNotFoundError:
        print(f"{RED}Error: 'git' command not found.{NC}")
        sys.exit(1)


if __name__ == "__main__":
    main()

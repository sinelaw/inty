#!/bin/bash
# Deploy inty web app to gh-pages branch
# Usage: ./deploy-gh-pages.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_ROOT"

# Save current branch
CURRENT_BRANCH=$(git branch --show-current)
echo "Current branch: $CURRENT_BRANCH"

# Check for uncommitted changes
if ! git diff-index --quiet HEAD --; then
    echo "Error: You have uncommitted changes. Please commit or stash them first."
    exit 1
fi

# Build the WASM module
echo ""
echo "Building WASM module..."
if ! command -v wasm-pack &> /dev/null; then
    echo "Installing wasm-pack..."
    cargo install wasm-pack
fi
wasm-pack build --target web --out-dir web/pkg --features wasm

# Create a temporary directory for the build artifacts
TEMP_DIR=$(mktemp -d)
echo "Copying build artifacts to $TEMP_DIR..."

cp web/index.html "$TEMP_DIR/"
cp web/styles.css "$TEMP_DIR/"
cp web/app.js "$TEMP_DIR/"
cp -r web/pkg "$TEMP_DIR/"

# Check if gh-pages branch exists
if git show-ref --verify --quiet refs/heads/gh-pages; then
    echo "Switching to gh-pages branch..."
    git checkout gh-pages
else
    echo "Creating gh-pages branch..."
    git checkout --orphan gh-pages
    git rm -rf . 2>/dev/null || true
fi

# Remove old files (except .git)
echo "Cleaning old files..."
find . -maxdepth 1 ! -name '.git' ! -name '.' -exec rm -rf {} +

# Copy new files
echo "Copying new build artifacts..."
cp "$TEMP_DIR/index.html" .
cp "$TEMP_DIR/styles.css" .
cp "$TEMP_DIR/app.js" .
cp -r "$TEMP_DIR/pkg" .

# Remove .gitignore from pkg to include all files
rm -f pkg/.gitignore

# Clean up temp directory
rm -rf "$TEMP_DIR"

# Stage and commit
echo ""
echo "Committing changes..."
git add -A
git commit -m "Deploy inty web app

Built from $CURRENT_BRANCH branch" || echo "No changes to commit"

echo ""
echo "Switching back to $CURRENT_BRANCH..."
git checkout "$CURRENT_BRANCH"

echo ""
echo "Done! The gh-pages branch has been updated."
echo ""
echo "To publish to GitHub Pages, run:"
echo "  git push origin gh-pages"
echo ""
echo "Your site will be available at:"
echo "  https://<username>.github.io/<repo-name>/"

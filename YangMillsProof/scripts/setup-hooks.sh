#!/bin/bash
# Script to set up git hooks for the project

echo "🔧 Setting up git hooks..."

# Get the repository root
REPO_ROOT=$(git rev-parse --show-toplevel)

# Configure git to use our hooks directory
git config core.hooksPath "$REPO_ROOT/.githooks"

# Make all hooks executable
chmod +x "$REPO_ROOT/.githooks"/*

echo "✅ Git hooks configured successfully!"
echo ""
echo "The following hooks are now active:"
echo "  - pre-commit: Prevents commits with new 'sorry' statements"
echo ""
echo "To bypass hooks temporarily (not recommended):"
echo "  git commit --no-verify"
echo ""
echo "To disable hooks:"
echo "  git config --unset core.hooksPath" 
# Git Workflow Guide

This guide explains our branching strategy and commit practices to keep the repository history clean and manageable.

## 🌳 Branch Strategy

We use thematic branches to organize work by type:

### Branch Naming Convention
```
<type>/<description>
```

### Branch Types

#### `math/` - Mathematical Content
For theorem proving, lemma additions, and mathematical corrections.
```bash
git checkout -b math/rg-exact-solution
git checkout -b math/wilson-bound-improvement
```

#### `physics/` - Physics Modeling
For gauge theory implementation, physical constants, and model improvements.
```bash
git checkout -b physics/su3-implementation
git checkout -b physics/centre-projection
```

#### `infra/` - Infrastructure
For CI/CD, build system, testing framework, and tooling.
```bash
git checkout -b infra/numerical-tests
git checkout -b infra/ci-pipeline
```

#### `docs/` - Documentation
For README updates, mathematical exposition, and guides.
```bash
git checkout -b docs/contributing-guide
git checkout -b docs/proof-outline
```

#### `fix/` - Bug Fixes
For fixing errors, resolving sorries, and corrections.
```bash
git checkout -b fix/derivative-calc
git checkout -b fix/interval-bounds
```

## 📝 Commit Guidelines

### Keep Commits Atomic
Each commit should represent one logical change:

❌ **Bad**: Large commit mixing multiple changes
```bash
git commit -m "Fix RG equation, add SU3, update CI, fix typos"
```

✅ **Good**: Separate commits for each change
```bash
git commit -m "fix(RG): Correct derivative calculation in g_exact"
git commit -m "feat(Gauge): Add SU3 matrix operations"
git commit -m "ci: Add numerical verification workflow"
git commit -m "docs: Fix typos in README"
```

### Commit Size Guidelines
- **Small**: < 100 lines changed
- **Medium**: 100-500 lines changed  
- **Large**: > 500 lines changed (consider splitting)

## 🔄 Workflow Example

### Starting New Work
```bash
# 1. Ensure main is up to date
git checkout main
git pull origin main

# 2. Create thematic branch
git checkout -b math/beta-function-improvement

# 3. Make focused changes
# ... edit files ...

# 4. Commit atomically
git add RG/StepScaling.lean
git commit -m "feat(RG): Define beta_one_loop function"

git add RG/StepScaling.lean
git commit -m "fix(RG): Remove artificial b₁*g⁵ = 0 equality"

# 5. Push branch
git push origin math/beta-function-improvement
```

### Splitting Large Changes
If you've made many changes in one branch:

```bash
# 1. Create separate branches for each theme
git checkout -b math/numerical-bounds
git cherry-pick <commit-hash>  # Pick math-related commits

git checkout -b infra/testing
git cherry-pick <commit-hash>  # Pick infrastructure commits

# 2. Clean up original branch
git checkout original-branch
git reset --hard <last-good-commit>
```

## 🎯 PR Strategy

### One Theme Per PR
- **Math PR**: "Improve numerical bounds in RG solution"
- **Physics PR**: "Implement proper SU(3) gauge fields"
- **Infra PR**: "Add CI pipeline for numerical verification"

### PR Size Targets
- **Ideal**: 200-400 lines changed
- **Maximum**: 1000 lines changed
- **If larger**: Split into multiple PRs

## 📊 Branch Lifecycle

```mermaid
graph LR
    A[main] --> B[feature branch]
    B --> C[commits]
    C --> D[PR]
    D --> E[review]
    E --> F[merge to main]
    F --> G[delete branch]
```

### Branch Cleanup
After merging:
```bash
# Delete local branch
git branch -d feature/branch-name

# Delete remote branch
git push origin --delete feature/branch-name

# Prune remote tracking
git remote prune origin
```

## 🚨 Common Pitfalls

### Avoid Mixed Commits
```diff
- git commit -m "Update everything"
+ git commit -m "feat(Wilson): Add plaquette holonomy"
+ git commit -m "test: Add Wilson action tests"
```

### Avoid Long-Lived Branches
- Merge within 1 week when possible
- Rebase frequently: `git rebase main`
- Split large features into incremental PRs

### Avoid Commit Pollution
```diff
- git commit -m "WIP"
- git commit -m "fix"
- git commit -m "more changes"
+ git commit --amend  # Amend previous commit
+ git rebase -i HEAD~3  # Interactive rebase to clean history
```

## 🛠️ Useful Commands

### View Branch Organization
```bash
# List all branches by theme
git branch -a | grep "math/"
git branch -a | grep "physics/"
git branch -a | grep "infra/"

# See branch activity
git for-each-ref --sort=-committerdate refs/heads/ --format='%(committerdate:short) %(refname:short)'
```

### Clean History Before PR
```bash
# Interactive rebase to squash/reorder commits
git rebase -i main

# Update commit messages
git commit --amend

# Force push to update PR (only on feature branches!)
git push --force-with-lease origin feature/branch-name
```

## 📚 Examples from This Project

### Good PR: Mathematical Improvements
- Branch: `math/exact-solution-bounds`
- Commits:
  1. `feat(Numerical): Add precise log and sqrt bounds`
  2. `fix(RG): Tighten c_exact interval to [1.14, 1.20]`
  3. `feat(RG): Prove tight c_product bounds [7.42, 7.68]`
- Size: ~400 lines
- Theme: Focused on numerical accuracy

### Good PR: Infrastructure
- Branch: `infra/ci-numerical`
- Commits:
  1. `feat(Test): Add numerical verification executable`
  2. `ci: Add GitHub Actions workflow`
  3. `docs: Update README with CI badge`
- Size: ~300 lines
- Theme: Testing and automation

## 🎓 Training New Contributors

1. Start with small, focused changes
2. One theorem = one commit
3. Group related theorems in one PR
4. Ask for help splitting large changes

Remember: Clean history helps future mathematicians understand the proof's development! 
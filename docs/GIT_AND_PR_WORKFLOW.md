# Git + GitHub PR workflow (Open Math Lab)

**Remote SoT:** `https://github.com/Paul3435/open-math-lab` (public)  
**Local SoT:** `C:\Users\paulb\Documents\VSCode\open-math-lab`  
**Default branch:** `master` locally; GitHub may use `main` — open PRs with `--base` matching the remote default (`gh repo view --json defaultBranchRef`).  
**Board merge authority:** Paul only (agents open PRs; agents do **not** merge to `master` unless a ticket explicitly says so).

## Why PRs

Paperclip agents produce multi-file sprints. PRs give the board a review surface, CI signal, and a clean history — without agents force-pushing `master`.

## When to open a PR (agents)

Open a PR when **any** of these hold:

1. **Sprint / issue close** — acceptance criteria met (or honest dead-end logged) and you would mark the Paperclip issue `done` or `in_review`.
2. **Coherent work package** — e.g. one attack directory + STATUS/LOG/RESULTS, or Lean install + BUILD_LOG, or catalog hygiene batch.
3. **Board asked for a PR** on the ticket.

Do **not** open a PR for:

- Empty or WIP thrash mid-attack (use the issue comment log instead).
- Secrets, credentials, `.env`, API keys.
- “We solved Millennium problem X” claim packets (use `mathforge claim prepare` + board only).
- Force-push or history rewrite on `master`.

## Branch naming

```text
ope/<id>-<short-slug>          # preferred — ties to Paperclip issue
sprint/<yyyy-mm-dd>-<slug>     # multi-issue sprint bundle
fix/<slug>
chore/<slug>
```

Examples: `ope/13-graceful-caterpillars`, `ope/17-lean-install`, `sprint/2026-07-31-hygiene`.

## Agent procedure (Windows / git-bash)

Work only in the git SoT cwd (not Paperclip managed `_default` alone).

```bash
cd "C:/Users/paulb/Documents/VSCode/open-math-lab"
git fetch origin
git checkout master
git pull origin master

git checkout -b ope/<id>-<slug>

# ... implement ...

# Verify before commit
python test_mathforge.py -v
python bin/mathforge status

git status
git add -A
# Never add: .env, secrets, .lake/, huge binaries

git -c user.name="Paul" -c user.email="paul.borjesson.sesma@gmail.com" commit -m "$(cat <<'EOF'
type(scope): summary for OPE-N

- bullet outcomes
- how to verify
EOF
)"

git push -u origin HEAD

gh pr create --base master --title "OPE-N: short title" --body "$(cat <<'EOF'
## Summary
- What changed (process / code / math artifacts)

## Paperclip
- Issue: OPE-N
- Agent role: Attack Lead | Scout | Formalist | Reviewer | Director

## Math honesty
- Claim status: none | informal | heuristic | Lean-checked (link build log)
- Residual risks: ...

## Test plan
- [ ] `python test_mathforge.py -v`
- [ ] `python bin/mathforge status`
- [ ] (if Lean) `lake build` in `proofs/lean-project` — paste exit code / point at BUILD_LOG

## Board
- [ ] Please review + merge if OK
- [ ] Do **not** treat this PR as external publication of a proof
EOF
)"
```

Then comment the **PR URL** on the Paperclip issue and set issue status appropriately (`in_review` if waiting on board/Reviewer).

## Director responsibilities

At sprint boundaries:

1. Ensure child issues either have a PR or an explicit “no code change” comment.
2. Prefer **one PR per issue** when possible; bundle only when files heavily overlap.
3. Never merge PRs as Director unless board ticket says merge is allowed.
4. Kill crackpot PRs: comment + close recommendation for board.

## Board (Paul)

- Review at https://github.com/Paul3435/open-math-lab/pulls  
- Merge via GitHub UI or `gh pr merge --squash` when satisfied  
- External communication still gated by claim policy

## Auth for agents

Agents use the host `gh` login (`Paul3435`, `repo` scope). If `gh auth status` fails, stop and comment on the issue — do not embed PATs in the repo.

## CI

Lightweight Python tests are defined in `docs/ci/github-actions-test.yml`. Copy to `.github/workflows/test.yml` after the board grants the GitHub token **`workflow`** scope (`gh auth refresh -s workflow`), then commit that path. Full Mathlib `lake build` stays local (OPE-17), not free GitHub runners.

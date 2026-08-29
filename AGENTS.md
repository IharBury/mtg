# Agent instructions

Always pull the latest commits before making any changes.

- Fetch and update the local checkout from the remote first.
- Do not edit files, create a feature branch, or commit from a stale checkout.
- If work starts from `main` (or another base branch), fetch that branch and start from its latest remote commit.

```sh
git fetch origin main
git pull --ff-only origin main
```

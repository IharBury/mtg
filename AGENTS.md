# Agent instructions

Always pull the latest commits before making any changes.

- Fetch and update the local checkout from the remote first.
- Do not edit files, create a feature branch, or commit from a stale checkout.
- If work starts from `main` (or another base branch), fetch that branch and start from its latest remote commit.

```sh
git fetch origin main
git pull --ff-only origin main
```

## Oracle card text source

Use official Gatherer Oracle text as the authoritative source for card definitions and Oracle rulings. When Scryfall does not match Gatherer, use Gatherer.


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

## Documentation

Write documentation so routine code edits do not force mechanical doc updates. This policy applies to living documentation (`docs/`, `README.md`) and to any new sections or phases added to `EVENT_ALIGNMENT_PLAN.md` (leave historical phases in `EVENT_ALIGNMENT_PLAN.md` untouched).

- **No line numbers or line ranges**: Do not cite source line numbers or line ranges in Markdown links (`#L123`, `#L10-L20`) or prose (`File.lean:123`, `L530–694`).
  - Reference code by file path and symbol/declaration name (for example, `` [`evalLayer3`](../Mtg/Engine/Game/Core.lean) `` or `` `evalLayer3` in [`Core.lean`](../Mtg/Engine/Game/Core.lean) ``).
  - Reference sections of other Markdown documents by file path and heading anchor (for example, `` [`EVENT_ALIGNMENT_PLAN.md`](../EVENT_ALIGNMENT_PLAN.md#02-non-goals-for-this-plan) ``).
- **No volatile exact counts**: Do not record exact counts that routinely drift as code or data evolves—such as file or directory line counts, file/module counts, constructor or field counts, `#guard`/test counts, or total catalog/ruling/example counts.
  - State durable design invariants, bounds, or rule-defined quantities instead (for example, "`< 40` constructors vs. Lean 4's `LeanMaxCtorTag = 243`", "the four CR 113.3a–d ability categories", "CR 613 Layers 1–7d", or "all cards in `supportedCatalogCards`").

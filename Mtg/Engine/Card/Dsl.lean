import Mtg.Engine.Card.Dsl.Elements
import Mtg.Engine.Card.Dsl.Compile
import Mtg.Engine.Card.Dsl.Parse

/-!
# Traditional card DSL

A list-shaped definition language for a traditional Magic card: one face,
plus an optional Adventure.

- `Elements`: the clause vocabulary (`.card`, `.textBox`, and the instructions
  inside it).
- `Compile`: functions on those clauses, including `toCardDef`.
- `Parse`: functions that read a printed card back into that clause list,
  including `parseOracleText`.
-/

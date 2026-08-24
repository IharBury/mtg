/-!
# Deterministic RNG

A tiny xorshift64 generator used to shuffle libraries (CR 103.3) without
`IO`, so games are reproducible from a seed.
-/

namespace Mtg.Engine

structure Rng where
  state : UInt64
deriving Repr, Inhabited

namespace Rng

/-- Zero is a fixed point of xorshift, so replace it with an odd constant. -/
def ofSeed (seed : UInt64) : Rng :=
  { state := if seed == 0 then 0x9E3779B97F4A7C15 else seed }

def next (self : Rng) : Rng × UInt64 :=
  let x := self.state ^^^ (self.state <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  ({ state := x }, x)

/-- Fisher–Yates shuffle. Index 0 is the bottom of a library; the last index is the top. -/
def shuffle {α} (self : Rng) (arr : Array α) : Rng × Array α :=
  if arr.size ≤ 1 then
    (self, arr)
  else
    Id.run do
      let mut rng := self
      let mut a := arr
      let n := a.size
      for i in [0:n - 1] do
        let (rng', r) := rng.next
        rng := rng'
        let remaining := n - i
        let j := i + (r.toNat % remaining)
        a := a.swapIfInBounds i j
      return (rng, a)

#guard
  let (rng, a) := (Rng.ofSeed 1).shuffle (Array.range 5)
  a.size == 5 && a.toList.eraseDups.length == 5 && rng.state != 0

end Rng

end Mtg.Engine

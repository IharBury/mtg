/-!
Caches for Oracle text that is folded many times while a card is parsed.

These refs live in their own module so their initializers run on import.
The `parseOracleParts` guards import this module, so these initializers have
already run. An initializer cannot be read from the module that defines it.
-/
namespace Mtg.Engine.OracleParts.Cache

/-- Last results for one normalization helper. The key is the string object. -/
unsafe def cachedAt {α : Type} (slots : IO.Ref (Array (Option (String × α))))
    (s : String) (build : String → α) : α :=
  unsafeBaseIO do
    let arr ← slots.get
    let i := (ptrAddrUnsafe s).toNat % arr.size
    if let some (k, v) := arr[i]! then
      if ptrEq k s then
        return v
    let v := build s
    let arr ← slots.get
    let i := (ptrAddrUnsafe s).toNat % arr.size
    slots.set (arr.set! i (some (s, v)))
    return v

initialize copiedCache : IO.Ref (Array (Option (String × String))) ←
  IO.mkRef (Array.replicate 16 (none : Option (String × String)))

initialize normCache : IO.Ref (Array (Option (String × String))) ←
  IO.mkRef (Array.replicate 32 (none : Option (String × String)))

initialize sentencesCache : IO.Ref (Array (Option (String × List String))) ←
  IO.mkRef (Array.replicate 8 (none : Option (String × List String)))

initialize rulesTextCache : IO.Ref (Array (Option (String × String))) ←
  IO.mkRef (Array.replicate 8 (none : Option (String × String)))

initialize normSentenceCache : IO.Ref (Array (Option (String × String))) ←
  IO.mkRef (Array.replicate 16 (none : Option (String × String)))

initialize normLineCache : IO.Ref (Array (Option (String × String))) ←
  IO.mkRef (Array.replicate 32 (none : Option (String × String)))

end Mtg.Engine.OracleParts.Cache

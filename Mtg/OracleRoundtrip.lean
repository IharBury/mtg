import Mtg.Engine.Card.ParseOracle

/-!
Smoke-check `parseOracleCard` on full printed cards.
-/

open Mtg.Engine

def expect (name : String) (text : String) (ok : CardDef → Bool) : IO Nat := do
  match parseOracleCard text with
  | .error e =>
    IO.println s!"PARSE {name}: {e}"
    return 1
  | .ok c =>
    if ok c then return 0
    else
      IO.println s!"MISMATCH {name}"
      return 1

def main : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let mut fails : Nat := 0
  fails := fails + (← expect "Grizzly Bears"
    "Grizzly Bears\n{1}{G}\nCreature — Bear\n2/2"
    (fun c => c.name == "Grizzly Bears" && c.power == some 2 && c.toughness == some 2 &&
      c.isCreature))
  fails := fails + (← expect "Shock"
    "Shock\n{R}\nInstant\nShock deals 2 damage to any target."
    (fun c => c.spellEffect == some (Effect.dealDamage 2) && c.isInstant))
  fails := fails + (← expect "Mountain"
    "Mountain\nBasic Land — Mountain\n({T}: Add {R}.)"
    (fun c => c.isLand && c.hasSupertype .basic && c.tapAddMana.isEmpty))
  fails := fails + (← expect "Allure of Power"
    "My Precious\n{3}\nLegendary Artifact — Equipment\nEquipped creature has hexproof and can't be blocked.\nEquip—{2}, Pay 2 life.\n//ADV//\nAllure of Power {1}{B}\nInstant — Adventure\nAs an additional cost to cast this spell, sacrifice a creature.\nDraw two cards."
    (fun c =>
      match c.adventure with
      | some a => a.name == "Allure of Power" && a.spellEffect == some (Effect.draw 2) &&
          a.additionalCostSacrificeCreature
      | none => false))
  fails := fails + (← expect "Thanos"
    "Thanos, the Mad Titan\n{R}{W}{B}\nLegendary Creature — Eternal Villain\n4/4\nDeathtouch, lifelink\nPower-up — {C}{W}{U}{B}{R}{G}: Put two +1/+1 counters on Thanos. Choose odd or even. Destroy each other creature with mana value of the chosen quality."
    (fun c => c.activatedAbilities.size == 1 && c.activatedAbilities[0]!.powerUp &&
      c.keywords.deathtouch && c.keywords.lifelink))
  let t1 ← IO.monoMsNow
  IO.println s!"fails {fails} ms {t1 - t0}"
  return if fails == 0 then 0 else 1

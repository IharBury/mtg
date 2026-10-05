import Mtg.Engine.Catalog.RealityFracture
import Mtg.Engine.OracleData

/-!
# Engine behavior for Reality Fracture (FRA) judge rulings (part 3)

Inventory of every FRA judge ruling. Each id is in exactly one list:

- `fraEngineCheckedIds`: checked against game states in the other
  `Mtg.Engine.FraOracleTests*` and `Mtg.Engine.FraCardTests*` modules.
  Rulings that need a card from another set (745, 757, 884) parse it locally
  in `Mtg.Engine.FraOracleTests8`.
- `fraSharedCheckedIds`: comments shared with HOB/HOC or MSH cards, whose
  behavior those suites check. The FRA cards that repeat them are not
  modeled further.

Every FRA card is fully parsed: none keeps a rules line as printed text.

This module imports only the FRA catalog and the ruling table, so the scan
doesn't wait on the gameplay tests.
-/

namespace Mtg.Engine.FraRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog

def fraEngineCheckedIds : List Nat := [
  32, 33, 37, 121, 388, 567, 568, 729, 730, 731, 732, 733, 734, 735, 736,
  737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751,
  752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766,
  767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781,
  782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796,
  797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811,
  812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826,
  827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841,
  842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856,
  857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871,
  872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886,
  887, 888, 889, 890, 891, 892, 893]

def fraSharedCheckedIds : List Nat := [153, 314, 403, 405, 413, 416]

/-- Every FRA ruling id is in exactly one inventory list. -/
def fraInventoryOk : Bool :=
  let all := fraEngineCheckedIds ++ fraSharedCheckedIds
  all.length == uniqueFraOracleRulingCount && all.eraseDups.length == all.length &&
    uniqueFraOracleRulings.all (fun r => all.contains r.id)

#guard fraInventoryOk

/- Shared rulings also apply to a HOB/HOC or MSH card, whose suite checks
them. -/
#guard fraSharedCheckedIds.all (fun i =>
  uniqueOracleRulings.any (fun r =>
    r.id == i && r.sets.any (· == "fra") && r.sets.any (· != "fra")))

/-- The FRA card a Scryfall ruling name refers to. Preparation cards are
named `Creature // Prepare spell`; the catalog uses the creature name. -/
def fraCardNamed? (name : String) : Option CardDef :=
  let base := (name.splitOn " // ").headD name
  realityFractureCards.find? (·.name == base)

/-- True when `c` keeps a rules line as printed text. -/
def keepsPrintedText (c : CardDef) : Bool :=
  c.staticAbilities.any (fun
    | .printed _ => true
    | _ => false) ||
    (match c.prepareFace with
     | some face => !face.extraLines.isEmpty || face.spellEffect.isNone
     | none => false)

/- Every card an FRA-only ruling names is in the FRA catalog, and every
shared ruling names at least one FRA catalog card. -/
#guard uniqueFraOracleRulings.all (fun r =>
  if r.sets.all (· == "fra") then r.cards.all (fun n => (fraCardNamed? n).isSome)
  else r.cards.any (fun n => (fraCardNamed? n).isSome))

/- Every FRA card is fully parsed: no rules line is kept as printed text. -/
#guard realityFractureCards.all (fun c => !keepsPrintedText c)

end Mtg.Engine.FraRulingTests

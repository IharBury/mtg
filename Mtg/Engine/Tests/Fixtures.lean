import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.CardText
import Mtg.Engine.Tests.Turns
import Mtg.Engine.Tests.Mulligans
import Mtg.Engine.Tests.Activation
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Combat
import Mtg.Engine.Tests.Equipment
import Mtg.Engine.Tests.Damage
import Mtg.Engine.Tests.AttackTriggers
import Mtg.Engine.Tests.Adventures
import Mtg.Engine.Tests.CastTriggers
import Mtg.Engine.Tests.Elves
import Mtg.Engine.Tests.Pathmaker
import Mtg.Engine.Tests.Fight
import Mtg.Engine.Tests.Removal
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Cycling
import Mtg.Engine.Tests.Targets
import Mtg.Engine.Tests.Effects
import Mtg.Engine.Tests.Leaving
import Mtg.Engine.Tests.Marvel
import Mtg.Engine.Tests.CatalogSmoke
import Mtg.Engine.Tests.RealityFracture
import Mtg.Engine.Tests.RealityFractureCommander
import Mtg.Engine.Tests.ParseOracle
import Mtg.Engine.Tests.MayCast
import Mtg.Engine.Tests.Draw
import Mtg.Engine.Tests.ReturnToHand
import Mtg.Engine.Tests.Put
import Mtg.Engine.Tests.AddMana
import Mtg.Engine.Tests.Destroy
import Mtg.Engine.Tests.Discard
import Mtg.Engine.Tests.TriggerFight
import Mtg.Engine.Tests.Grant
import Mtg.Engine.Tests.GainLife
import Mtg.Engine.Tests.LoseLife
import Mtg.Engine.Tests.Mill
import Mtg.Engine.Tests.RemoveCounters
import Mtg.Engine.Tests.RevealFromHand
import Mtg.Engine.Tests.RevealLibrary
import Mtg.Engine.Tests.SearchLibrary
import Mtg.Engine.Tests.Tap
import Mtg.Engine.Tests.Lose
import Mtg.Engine.Tests.Cant
import Mtg.Engine.Tests.PutOnLibrary
import Mtg.Engine.Tests.SetBasePT
import Mtg.Engine.Tests.Untap
import Mtg.Engine.Tests.Modes
import Mtg.Engine.Tests.Chapter
import Mtg.Engine.Tests.Count
import Mtg.Engine.Tests.Step
import Mtg.Engine.Tests.Death
import Mtg.Engine.Tests.ThisAttack
import Mtg.Engine.Tests.EnterOrAttack
import Mtg.Engine.Tests.Watch
import Mtg.Engine.Tests.YouAttack
import Mtg.Engine.Tests.Casting
import Mtg.Engine.Tests.Resource
import Mtg.Engine.Tests.Reflexive
import Mtg.Engine.Tests.Pay
import Mtg.Engine.Tests.Sacrifice
import Mtg.Engine.Tests.PutCounters
import Mtg.Engine.Tests.BecomeArtifact
import Mtg.Engine.Tests.BecomePrepared
import Mtg.Engine.Tests.Exile

/-!
# Engine Test Fixtures

Re-exports the `Mtg.Engine.Tests.*` fixture and rule modules without pulling in
the sharded `Mtg.Engine.Tests.Events` suite, allowing `MtgDemo` checks to
elaborate in parallel with `Mtg.Engine.Tests.Events.*`.
-/

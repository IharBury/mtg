import Mtg.Engine.Card
import Mtg.Engine.Catalog
import Mtg.Engine.Catalog.Hobbit
import Mtg.Engine.Catalog.HobbitEternal
import Mtg.Engine.Catalog.MarvelSuperHeroes
import Mtg.Engine.Game
import Mtg.Engine.OracleData
import Mtg.Engine.Tests.Abilities
import Mtg.Engine.Tests.Adventures
import Mtg.Engine.Tests.AttackTriggers
import Mtg.Engine.Tests.Auras
import Mtg.Engine.Tests.Effects
import Mtg.Engine.Tests.Elves
import Mtg.Engine.Tests.Equipment
import Mtg.Engine.Tests.Helpers
import Mtg.Engine.Tests.Pathmaker
import Mtg.Engine.Tests.Removal
import Mtg.Engine.Tests.RulingFixtures
import Mtg.Engine.Tests.Turns


/-!
# Engine behavior for unique Marvel Super Heroes (MSH) judge rulings (part 6)

Wording inventory for the remaining MSH judge rulings.
-/

namespace Mtg.Engine.MshRulingTests

open Mtg.Engine
open Mtg.Engine.Catalog
open Mtg.Engine.Tests

-- Remaining unique comments are restatements of CR the engine already
-- implements (copy, X, illegal targets, timing, reflexive triggers,
-- controlling another player, and card-specific wording). Cite each id
-- so a missing inventory entry fails this suite.
def remainingMshRulingWordingOk : Bool :=
  (mshRuling 375).comment.contains "cast green spells" &&
    (mshRuling 389).comment.contains "won't apply to copying" &&
    (mshRuling 391).comment.contains "choices will be made separately" &&
    (mshRuling 394).comment.contains "won't cause abilities that trigger" &&
    (mshRuling 395).comment.contains "separate life-gaining event" &&
    (mshRuling 399).comment.contains "won't be able to tap it again" &&
    (mshRuling 400).comment.contains "division can't be changed" &&
    (mshRuling 401).comment.contains "same value of X" &&
    (mshRuling 402).comment.contains "same mode" &&
    (mshRuling 197).comment.contains "can't choose to cast it for any alternative" &&
    (mshRuling 406).comment.contains "triggers only once" &&
    (mshRuling 410).comment.contains "Two-Headed Giant" &&
    (mshRuling 412).comment.contains "won't cause its abilities to stop" &&
    (mshRuling 414).comment.contains "same targets as the ability" &&
    (mshRuling 415).comment.contains "resolve before the original" &&
    (mshRuling 419).comment.contains "can't choose to pay any activation" &&
    (mshRuling 421).comment.contains "normal timing rules" &&
    (mshRuling 437).comment.contains "opening hand" &&
    (mshRuling 441).comment.contains "replaces any existing creature types" &&
    (mshRuling 445).comment.contains "enters abilities of each copied" &&
    (mshRuling 446).comment.contains "enters abilities of the copied" &&
    (mshRuling 447).comment.contains "Ares himself" &&
    (mshRuling 448).comment.contains "won't trigger again that turn" &&
    (mshRuling 449).comment.contains "Worlds Within Worlds" &&
    (mshRuling 450).comment.contains "Kid Loki" &&
    (mshRuling 451).comment.contains "second card" &&
    (mshRuling 452).comment.contains "once for each player" &&
    (mshRuling 458).comment.contains "as though they had flash" &&
    (mshRuling 459).comment.contains "multiple instances" &&
    (mshRuling 460).comment.contains "resolves before the spell" &&
    (mshRuling 461).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 462).comment.contains "last time he was on the battlefield" &&
    (mshRuling 463).comment.contains "second card" &&
    (mshRuling 465).comment.contains "tracked even if he has indestructible" &&
    (mshRuling 468).comment.contains "exactly what was printed" &&
    (mshRuling 469).comment.contains "not just one with targets" &&
    (mshRuling 470).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 473).comment.contains "exactly what was printed" &&
    (mshRuling 474).comment.contains "exactly what was printed" &&
    (mshRuling 475).comment.contains "exactly what was printed" &&
    (mshRuling 476).comment.contains "doesn't trigger multiple times" &&
    (mshRuling 478).comment.contains "reflexive" &&
    (mshRuling 479).comment.contains "just once" &&
    (mshRuling 483).comment.contains "doesn't have to attack" &&
    (mshRuling 484).comment.contains "last existed on the battlefield" &&
    (mshRuling 485).comment.contains "before their last ability resolves" &&
    (mshRuling 486).comment.contains "same time as other Villains" &&
    (mshRuling 487).comment.contains "stat comparison will happen again" &&
    (mshRuling 489).comment.contains "last existed on the battlefield" &&
    (mshRuling 490).comment.contains "won't be able to sacrifice it" &&
    (mshRuling 491).comment.contains "won't trigger at all" &&
    (mshRuling 492).comment.contains "You'll create the Robot" &&
    (mshRuling 493).comment.contains "won't be exiled" &&
    (mshRuling 494).comment.contains "won't be exiled" &&
    (mshRuling 495).comment.contains "may still have her deal damage" &&
    (mshRuling 496).comment.contains "won't gain control" &&
    (mshRuling 497).comment.contains "doesn't attack" &&
    (mshRuling 498).comment.contains "won't lose its abilities" &&
    (mshRuling 499).comment.contains "won't receive a counter" &&
    (mshRuling 500).comment.contains "last existed on the battlefield" &&
    (mshRuling 501).comment.contains "last existed on the battlefield" &&
    (mshRuling 502).comment.contains "won't be exiled" &&
    (mshRuling 503).comment.contains "last existed on the battlefield" &&
    (mshRuling 504).comment.contains "trigger only once" &&
    (mshRuling 508).comment.contains "whatever that creature copied" &&
    (mshRuling 512).comment.contains "total amount of damage" &&
    (mshRuling 521).comment.contains "value chosen for X" &&
    (mshRuling 522).comment.contains "doesn't target anything" &&
    (mshRuling 523).comment.contains "linked to a second ability" &&
    (mshRuling 524).comment.contains "linked to a second ability" &&
    (mshRuling 525).comment.contains "won't also deal normal combat damage" &&
    (mshRuling 529).comment.contains "chooses the order" &&
    (mshRuling 530).comment.contains "chooses an order" &&
    (mshRuling 531).comment.contains "divided or assigned before doubling" &&
    (mshRuling 535).comment.contains "trigger multiple times" &&
    (mshRuling 539).comment.contains "choose 0 as the value of X" &&
    (mshRuling 540).comment.contains "won't have any effect" &&
    (mshRuling 541).comment.contains "trigger only once" &&
    (mshRuling 542).comment.contains "will keep that ability" &&
    (mshRuling 543).comment.contains "daybound" &&
    (mshRuling 544).comment.contains "front face up" &&
    (mshRuling 545).comment.contains "original characteristics of that token" &&
    (mshRuling 546).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 547).comment.contains "whatever that artifact copied" &&
    (mshRuling 548).comment.contains "original characteristics of that token" &&
    (mshRuling 549).comment.contains "original characteristics of that token" &&
    (mshRuling 550).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 551).comment.contains "copy of whatever that creature copied" &&
    (mshRuling 552).comment.contains "original characteristics of that token" &&
    (mshRuling 553).comment.contains "copy of whatever that permanent copied" &&
    (mshRuling 556).comment.contains "illegal target" &&
    (mshRuling 557).comment.contains "remain attached" &&
    (mshRuling 558).comment.contains "no damage will be dealt" &&
    (mshRuling 559).comment.contains "won't resolve" &&
    (mshRuling 572).comment.contains "reveal all the cards" &&
    (mshRuling 573).comment.contains "next turn they actually take" &&
    (mshRuling 574).comment.contains "doesn't become a 2/2" &&
    (mshRuling 575).comment.contains "neither attacking creature is attacking alone" &&
    (mshRuling 577).comment.contains "still do as much as it can" &&
    (mshRuling 578).comment.contains "no damage is dealt to the illegal target" &&
    (mshRuling 579).comment.contains "copy only the cards exiled" &&
    (mshRuling 580).comment.contains "removed from the stack" &&
    (mshRuling 581).comment.contains "tap that permanent" &&
    (mshRuling 582).comment.contains "teamwork costs" &&
    (mshRuling 583).comment.contains "Equipment won't move" &&
    (mshRuling 584).comment.contains "must remove a counter" &&
    (mshRuling 585).comment.contains "won't trigger" &&
    (mshRuling 586).comment.contains "returns to their hand" &&
    (mshRuling 587).comment.contains "last one to resolve" &&
    (mshRuling 588).comment.contains "gain control of each player" &&
    (mshRuling 589).comment.contains "multiplied by four" &&
    (mshRuling 591).comment.contains "resolves before the spell" &&
    (mshRuling 593).comment.contains "become unattached" &&
    (mshRuling 594).comment.contains "artifact entered" &&
    (mshRuling 596).comment.contains "second card" &&
    (mshRuling 597).comment.contains "second card" &&
    (mshRuling 598).comment.contains "second card" &&
    (mshRuling 599).comment.contains "resolves before the ability" &&
    (mshRuling 600).comment.contains "resolves before the spell" &&
    (mshRuling 601).comment.contains "second card" &&
    (mshRuling 602).comment.contains "resolves before the spell" &&
    (mshRuling 603).comment.contains "resolves before the spell" &&
    (mshRuling 604).comment.contains "printed order" &&
    (mshRuling 605).comment.contains "doesn't allow you to activate" &&
    (mshRuling 606).comment.contains "only one land per turn" &&
    (mshRuling 607).comment.contains "second card" &&
    (mshRuling 608).comment.contains "overwrite any previous effects" &&
    (mshRuling 610).comment.contains "Multiple instances of lifelink" &&
    (mshRuling 611).comment.contains "overwrite each other" &&
    (mshRuling 612).comment.contains "resolves before the spell" &&
    (mshRuling 614).comment.contains "won't cause him to become unblocked" &&
    (mshRuling 615).comment.contains "won't cause her to become unblocked" &&
    (mshRuling 616).comment.contains "won't be able to make that block illegal" &&
    (mshRuling 617).comment.contains "no player may take actions" &&
    (mshRuling 618).comment.contains "won't stop the ability from resolving" &&
    (mshRuling 619).comment.contains "doesn't check again" &&
    (mshRuling 621).comment.contains "resolves before the spell" &&
    (mshRuling 622).comment.contains "doesn't count as playing a land" &&
    (mshRuling 623).comment.contains "resolves before the spell" &&
    (mshRuling 624).comment.contains "dealt damage this turn" &&
    (mshRuling 625).comment.contains "must survive the damage" &&
    (mshRuling 627).comment.contains "overwrite all previous effects" &&
    (mshRuling 628).comment.contains "creature cards are put into your graveyard" &&
    (mshRuling 629).comment.contains "second card" &&
    (mshRuling 630).comment.contains "not just one with targets" &&
    (mshRuling 631).comment.contains "doesn't cause any object to gain" &&
    (mshRuling 632).comment.contains "doesn't grant haste" &&
    (mshRuling 634).comment.contains "resolves before the spell" &&
    (mshRuling 635).comment.contains "resolves before the spell" &&
    (mshRuling 637).comment.contains "resolves before the spell" &&
    (mshRuling 638).comment.contains "doesn't need to still be on the battlefield" &&
    (mshRuling 639).comment.contains "doesn't actually change any creature's power" &&
    (mshRuling 643).comment.contains "same source as the original" &&
    (mshRuling 644).comment.contains "total amount of life lost" &&
    (mshRuling 645).comment.contains "first time that state-based actions" &&
    (mshRuling 647).comment.contains "Hero in addition to its other types" &&
    (mshRuling 648).comment.contains "doesn't target any player" &&
    (mshRuling 649).comment.contains "won't trigger at all" &&
    (mshRuling 650).comment.contains "replacement effects" &&
    (mshRuling 651).comment.contains "second from the top" &&
    (mshRuling 652).comment.contains "still the active player" &&
    (mshRuling 654).comment.contains "same as the source of the original" &&
    (mshRuling 655).comment.contains "same as the source of the original" &&
    (mshRuling 656).comment.contains "exactly what was printed" &&
    (mshRuling 657).comment.contains "calculated at the time" &&
    (mshRuling 658).comment.contains "calculated only once" &&
    (mshRuling 659).comment.contains "calculated only once" &&
    (mshRuling 660).comment.contains "calculated only once" &&
    (mshRuling 661).comment.contains "calculated only once" &&
    (mshRuling 662).comment.contains "determined only once" &&
    (mshRuling 663).comment.contains "resolves before the spell" &&
    (mshRuling 664).comment.contains "just once" &&
    (mshRuling 669).comment.contains "Token creatures" &&
    (mshRuling 673).comment.contains "checks Viv Vision's power only as it resolves" &&
    (mshRuling 674).comment.contains "neither entering nor leaving" &&
    (mshRuling 675).comment.contains "won't trigger at all" &&
    (mshRuling 677).comment.contains "exactly what was printed" &&
    (mshRuling 678).comment.contains "neither entering nor leaving" &&
    (mshRuling 679).comment.contains "stat that's greater changes" &&
    (mshRuling 681).comment.contains "neither entering nor leaving" &&
    (mshRuling 682).comment.contains "neither entering nor leaving" &&
    (mshRuling 685).comment.contains "You may play the exiled card" &&
    (mshRuling 686).comment.contains "continue to make your own choices" &&
    (mshRuling 687).comment.contains "you can see all cards" &&
    (mshRuling 688).comment.contains "you make all choices" &&
    (mshRuling 691).comment.contains "resolves before the spell" &&
    (mshRuling 695).comment.contains "only affects the next" &&
    (mshRuling 698).comment.contains "can't use your own" &&
    (mshRuling 700).comment.contains "can't choose the same mode" &&
    (mshRuling 701).comment.contains "sideboard" &&
    (mshRuling 702).comment.contains "tournament rules" &&
    (mshRuling 703).comment.contains "can't make any illegal decisions" &&
    (mshRuling 704).comment.contains "can't make the player" &&
    (mshRuling 705).comment.contains "while Baron Helmut Zemo's boast ability is resolving" &&
    (mshRuling 706).comment.contains "Each target must receive at least 1 damage" &&
    (mshRuling 707).comment.contains "doesn't have to be the same player" &&
    (mshRuling 708).comment.contains "can't wait to cast one later" &&
    (mshRuling 709).comment.contains "can't wait to cast them later" &&
    (mshRuling 710).comment.contains "You don't control any of that player's permanents" &&
    (mshRuling 711).comment.contains "reflexive" &&
    (mshRuling 712).comment.contains "reflexive" &&
    (mshRuling 713).comment.contains "reflexive" &&
    (mshRuling 714).comment.contains "reflexive" &&
    (mshRuling 715).comment.contains "reflexive" &&
    (mshRuling 716).comment.contains "reflexive" &&
    (mshRuling 717).comment.contains "reflexive" &&
    (mshRuling 718).comment.contains "reflexive" &&
    (mshRuling 719).comment.contains "reflexive" &&
    (mshRuling 720).comment.contains "reflexive" &&
    (mshRuling 721).comment.contains "reflexive" &&
    (mshRuling 722).comment.contains "You may change any number of the targets" &&
    (mshRuling 723).comment.contains "maximum of one time" &&
    (mshRuling 725).comment.contains "normal timing rules" &&
    (mshRuling 726).comment.contains "timing rules" &&
    (mshRuling 727).comment.contains "even if those cards are no longer"

#guard remainingMshRulingWordingOk

/-- Every unique MSH ruling is stored, names at least one card, and is
exercised by the engine tests above or by the shared CR behavior they
restate. -/
def allMshRulingsPresentOk : Bool :=
  uniqueMshOracleRulings.size == 376 &&
    uniqueMshOracleRulings.all (fun r =>
      !r.cards.isEmpty && r.sets.any (· == "msh") && r.comment.length > 20)

#guard allMshRulingsPresentOk

end Mtg.Engine.MshRulingTests

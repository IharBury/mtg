/-!
# Rules version

The engine follows the *Magic: The Gathering* Comprehensive Rules that are
effective as of 7 August 2026. Citations of the form “CR 105.1” refer to that
document.

The published text is available from Wizards of the Coast:

<https://media.wizards.com/2026/downloads/MagicCompRules%2020260819.txt>
-/

namespace Mtg.Engine.Rules

/-- Calendar date on which this rules version takes effect (CR header). -/
def effectiveDate : String := "2026-08-07"

/-- Publication filename date of the official text we follow. -/
def publicationStamp : String := "20260819"

/-- Official download URL for the Comprehensive Rules text. -/
def sourceUrl : String :=
  "https://media.wizards.com/2026/downloads/MagicCompRules%2020260819.txt"

/-- Human-readable identification of the ruleset. -/
def identification : String :=
  s!"Magic: The Gathering Comprehensive Rules effective {effectiveDate}"

end Mtg.Engine.Rules

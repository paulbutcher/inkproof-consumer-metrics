/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core

namespace Metrics

open Inkproof.Core

/-- Seconds since the Unix epoch. Exposition formats write timestamps and readings as decimals, which
`Rat` holds exactly, and Inkproof.Scale's theorems cover `Rat` but not `Float`. -/
abbrev Time := Rat

abbrev Reading := Rat

/-- The scrapes of one metric, in time order. A scrape that ran but returned no reading is `none`;
a scrape that never ran has no point at all. -/
abbrev Scrapes := Series Time Reading

/-- When two adjacent scrapes must not be joined: they are more than `staleAfter` seconds apart, or
the target restarted after the first and no later than the second. -/
structure GapPolicy where
  staleAfter : Time
  restarts : Array Time

namespace GapPolicy

/-- See `isGap_iff`. -/
def isGap (p : GapPolicy) (a b : Time) : Bool :=
  decide (p.staleAfter < b - a) || p.restarts.any fun r => decide (a < r) && decide (r ≤ b)

/-- The scrapes split wherever `isGap` holds between neighbours, and nowhere else; see
`mem_breaks_segment`. -/
def segment (p : GapPolicy) (s : Scrapes) : Segmented Time Reading :=
  Segmented.splitWhere s p.isGap

end GapPolicy

end Metrics

/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import Metrics.Scrapes

namespace Metrics

open Inkproof.Core Inkproof.Scale

/-- The first, highest, lowest and last reading of a run of scrapes: what a line chart needs to draw
one pixel column. -/
abbrev Summary := First Reading × Maximum Reading × Minimum Reading × Last Reading

/-- A missing reading summarises as nothing at all. -/
def summarise (p : Time × Option Reading) : Summary := (⟨p.2⟩, ⟨p.2⟩, ⟨p.2⟩, ⟨p.2⟩)

/-- One aggregation pyramid per gap-free segment of a metric. -/
abbrev Chart := SegmentedPyramid Time Reading Summary

def chart (p : GapPolicy) (s : Scrapes) : Chart :=
  SegmentedPyramid.build (p.segment s) summarise 8 (by decide)

/-- A column of one segment in screen coordinates, where y grows downwards: so `top` is where the
highest reading is drawn and `bottom` the lowest. -/
structure Extent where
  first : Rat
  top : Rat
  bottom : Rat
  last : Rat
  deriving Repr, BEq

/-- The window drawn: `columns` pixel columns covering times from `start` to `stop`, and `height`
pixel rows covering readings from `low` at the bottom to `high` at the top. -/
structure View where
  start : Time
  stop : Time
  columns : Nat
  low : Reading
  high : Reading
  height : Nat
  deriving Repr

namespace View

def xScale (v : View) : Linear Rat := ⟨v.start, v.stop, 0, v.columns⟩

def yScale (v : View) : Linear Rat := ⟨v.low, v.high, v.height, 0⟩

/-- The time at the left edge of column `c`; column `c` holds the times from here up to, but not
including, the start of column `c + 1`. -/
def columnStart (v : View) (c : Nat) : Time := v.xScale.inv.map c

/-- The summary in screen coordinates, or `none` if it holds no reading. -/
def extent (v : View) : Summary → Option Extent
  | (⟨some f⟩, ⟨some hi⟩, ⟨some lo⟩, ⟨some l⟩) =>
    some ⟨v.yScale.map f, v.yScale.map hi, v.yScale.map lo, v.yScale.map l⟩
  | _ => none

/-- Column `c` of each segment, in segment order: `none` where the segment has no reading there. -/
def column (v : View) (ch : Chart) (c : Nat) : Array (Option Extent) :=
  (ch.query (v.columnStart c) (v.columnStart (c + 1))).map v.extent

def render (v : View) (ch : Chart) : Array (Array (Option Extent)) :=
  (Array.range v.columns).map (v.column ch)

end View

end Metrics

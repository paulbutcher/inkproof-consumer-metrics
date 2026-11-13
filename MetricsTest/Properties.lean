/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Metrics
import InkproofTools.Test.Harness

/-! Generated scrapes, checked against a naive computation over the raw samples that splits
segments and assigns columns itself. -/

namespace MetricsTest.Properties

open Inkproof.Core Metrics InkproofTools.Test

/-- One generated scenario: the raw scrapes, the gap policy, and the window drawn. -/
structure Case where
  points : Array (Time × Option Reading)
  policy : GapPolicy
  start : Time
  stop : Time
  columns : Nat
  height : Nat

instance : Repr GapPolicy := ⟨fun p _ => s!"⟨{reprStr p.staleAfter}, {reprStr p.restarts}⟩"⟩

instance : Repr Case :=
  ⟨fun c _ => s!"points {reprStr c.points}, policy {reprStr c.policy}, window [{reprStr c.start}, \
    {reprStr c.stop}) × {c.columns}, height {c.height}"⟩

def base : Time := 1700000000

/-- Milliseconds as seconds, so timestamps carry the decimals an exposition format gives. -/
def millis (n : Nat) : Time := (n : Rat) / 1000

/-- A reading in `[-50, 150]` with two decimals. -/
def genReading (g : Rng) : Reading × Rng :=
  let (n, g) := g.below 20001
  (((n : Int) - 5000 : Int) / (100 : Rat), g)

/-- Scrapes every 15 s or so with jitter, some never run, some failing for a run of scrapes,
some stalling long enough to be a gap, and occasionally two at the same instant. -/
def genPoints (g : Rng) : Array (Time × Option Reading) × Rng := Id.run do
  let (n, g₀) := g.below 60
  let mut g := g₀
  let mut t := base
  let mut out := #[]
  let mut failing := 0
  for _ in [0:n] do
    let (skipped, g₁) := g.oneIn 6
    let (stall, g₂) := g₁.oneIn 12
    let (same, g₃) := g₂.oneIn 20
    let (jitter, g₄) := g₃.below 4000
    let (startFailing, g₅) := g₄.oneIn 15
    let (runLength, g₆) := g₅.below 6
    let (r, g₇) := genReading g₆
    g := g₇
    t := if same && !out.isEmpty then t else t + 13 + millis jitter + if stall then 60 else 0
    if startFailing then failing := runLength
    if skipped then continue
    if failing > 0 then
      failing := failing - 1
      out := out.push (t, none)
    else
      out := out.push (t, some r)
  return (out, g)

def genCase (g : Rng) : Case × Rng :=
  let (points, g) := genPoints g
  let (nRestarts, g) := g.below 3
  let span : Nat := 1200
  let (restarts, g) := (List.range nRestarts).foldl (fun (acc : Array Time × Rng) _ =>
    let (r, g) := acc.2.below span
    (acc.1.push (base - 30 + r), g)) (#[], g)
  let (lead, g) := g.below 60
  let (len, g) := g.below span
  let (columns, g) := g.below 40
  let (height, g) := g.below 400
  ({ points, policy := ⟨45, restarts⟩, start := base - 30 + lead, stop := base - 30 + lead + 1 + len,
     columns := columns + 1, height := height + 1 }, g)

/-- Low and high readings among the scrapes, widened so the interval is never degenerate. -/
def fitReadings (points : Array (Time × Option Reading)) : Reading × Reading :=
  let rs := points.filterMap (·.2)
  match rs[0]? with
  | none => (0, 1)
  | some r₀ =>
    let lo := rs.foldl min r₀
    let hi := rs.foldl max r₀
    if lo < hi then (lo, hi) else (lo - 1, hi + 1)

def view (c : Case) : View :=
  let (low, high) := fitReadings c.points
  { start := c.start, stop := c.stop, columns := c.columns, low, high, height := c.height }

/-- The segments of the raw points, split directly at each gap. -/
def naiveSegments (p : GapPolicy) (points : Array (Time × Option Reading)) :
    Array (Array (Time × Option Reading)) :=
  points.foldl (init := #[]) fun segs pt =>
    match segs.back? with
    | some seg =>
      match seg.back? with
      | some prev => if p.isGap prev.1 pt.1 then segs.push #[pt] else segs.pop.push (seg.push pt)
      | none => segs.pop.push (seg.push pt)
    | none => #[#[pt]]

/-- The column a time falls in, found from the x-scale rather than from column boundaries. -/
def naiveColumn (v : View) (t : Time) : Int := (v.xScale.map t).floor

def naiveExtent (v : View) (seg : Array (Time × Option Reading)) (c : Nat) : Option Extent :=
  let rs := (seg.filter fun pt => naiveColumn v pt.1 == c).filterMap (·.2)
  match rs[0]?, rs.back? with
  | some f, some l =>
    let y := v.yScale.map
    some ⟨y f, y (rs.foldl max f), y (rs.foldl min f), y l⟩
  | _, _ => none

def scrapes (c : Case) : Except String Scrapes :=
  match Series.ofPoints? c.points with
  | .ok s => .ok s
  | .error e => .error s!"generated scrapes rejected: {reprStr e}"

/-- Checks one scenario against the naive computation and the drawing invariants. -/
def checkCase (c : Case) : Except String Unit := do
  let s ← scrapes c
  let v := view c
  let ch := chart c.policy s
  let segs := naiveSegments c.policy c.points
  check (ch.segmented.numSegments == segs.size)
    s!"{ch.segmented.numSegments} segments, naively {segs.size}"
  for k in [0:segs.size] do
    check ((ch.segmented.segment k).points == segs[k]!) s!"segment {k} differs"
  let cols := v.render ch
  check (cols.size == c.columns) "wrong number of columns"
  for col in [0:cols.size] do
    let got := cols[col]!
    let want := segs.map (naiveExtent v · col)
    check (got == want) s!"column {col}: got {reprStr got}, naively {reprStr want}"
    for e? in got do
      if let some e := e? then
        let h : Rat := c.height
        check (0 ≤ e.top && e.top ≤ e.bottom && e.bottom ≤ h) s!"column {col} out of order or range"
        check (e.top ≤ e.first && e.first ≤ e.bottom && e.top ≤ e.last && e.last ≤ e.bottom)
          s!"column {col}: first or last outside top and bottom"

/-- Larger readings land higher on screen, and the y-scale never inverts their order. -/
def checkOrder (c : Case) : Except String Unit := do
  let v := view c
  let rs := c.points.filterMap (·.2)
  for a in rs do
    for b in rs do
      if a ≤ b then check (v.yScale.map b ≤ v.yScale.map a) s!"{a} ≤ {b} but drawn below it"

def generated : TestCase := .mk "generated scrapes agree with a naive computation" <|
  forAll 300 genCase checkCase

def ordered : TestCase := .mk "mapped readings keep their order" <| forAll 100 genCase checkOrder

def fixed (name : String) (points : Array (Time × Option Reading)) (restarts : Array Time := #[])
    (extra : Case → Except String Unit := fun _ => pure ()) : TestCase :=
  .mk name do
    let c : Case :=
      { points, policy := ⟨45, restarts⟩, start := base - 20, stop := base + 200, columns := 11,
        height := 100 }
    checkCase c
    extra c

def numSegments (c : Case) : Except String Nat := do
  return (chart c.policy (← scrapes c)).segmented.numSegments

def edgeCases : List TestCase := [
  fixed "empty series" #[] (extra := fun c => do
    check ((← numSegments c) == 0) "segments in an empty series"),
  fixed "single sample" #[(base + 5, some 3)],
  fixed "single failed scrape" #[(base + 5, none)],
  fixed "all scrapes failed" ((List.range 10).toArray.map fun (i : Nat) => (base + 15 * (i : Rat), (none : Option Reading)))
    (extra := fun c => do
      let s ← scrapes c
      check ((view c).render (chart c.policy s) |>.all (·.all Option.isNone)) "drew a failed scrape"),
  fixed "failed run inside a segment"
    ((List.range 10).toArray.map fun (i : Nat) => (base + 15 * (i : Rat), if 3 ≤ i ∧ i < 7 then none else some (i : Rat))),
  fixed "stale gap after the first scrape"
    #[(base, some 1), (base + 100, some 2), (base + 115, some 3)] (extra := fun c => do
      check ((← numSegments c) == 2) "first scrape not isolated"),
  fixed "stale gap before the last scrape"
    #[(base, some 1), (base + 15, some 2), (base + 150, some 3)] (extra := fun c => do
      check ((← numSegments c) == 2) "last scrape not isolated"),
  fixed "restart before the first scrape is no gap" #[(base, some 1), (base + 15, some 2)]
    (restarts := #[base - 10]) (extra := fun c => do
      check ((← numSegments c) == 1) "split without a gap"),
  fixed "restart at the last scrape isolates it" #[(base, some 1), (base + 15, some 2)]
    (restarts := #[base + 15]) (extra := fun c => do
      check ((← numSegments c) == 2) "restart ignored"),
  fixed "repeated timestamp" #[(base, some 1), (base, some 5), (base + 15, some 2)]
]

def tests : List TestCase := generated :: ordered :: edgeCases

end MetricsTest.Properties

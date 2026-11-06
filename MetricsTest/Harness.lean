/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace MetricsTest

structure TestCase where
  name : String
  run : Except String Unit

def check (cond : Bool) (msg : String) : Except String Unit :=
  if cond then .ok () else .error msg

/-- A deterministic pseudo-random source (64-bit LCG), so failures reproduce on every platform. -/
structure Rng where
  state : UInt64

namespace Rng

def next (g : Rng) : Rng := ⟨g.state * 6364136223846793005 + 1442695040888963407⟩

/-- A number below `bound`, or `0` when `bound` is `0`. -/
def below (g : Rng) (bound : Nat) : Nat × Rng :=
  let g' := g.next
  ((g'.state >>> 33).toNat % max bound 1, g')

/-- True one time in `n`. -/
def oneIn (g : Rng) (n : Nat) : Bool × Rng :=
  let (k, g) := g.below n
  (k == 0, g)

end Rng

/-- Checks `prop` on `count` generated cases, reporting the first failure with its input. -/
def forAll {γ : Type} [Repr γ] (count : Nat) (gen : Rng → γ × Rng)
    (prop : γ → Except String Unit) (seed : UInt64 := 1) : Except String Unit := do
  let mut g : Rng := ⟨seed⟩
  for _ in [0:count] do
    let (c, g') := gen g
    g := g'
    match prop c with
    | .ok () => pure ()
    | .error msg => throw s!"{msg}\n  input: {reprStr c}"

/-- Runs every case, reports each failure, and returns the process exit code. -/
def runTests (cases : List TestCase) : IO UInt32 := do
  let mut failed := 0
  for c in cases do
    if let .error msg := c.run then
      failed := failed + 1
      IO.eprintln s!"FAIL {c.name}: {msg}"
  IO.println s!"{cases.length - failed}/{cases.length} passed"
  return if failed == 0 then 0 else 1

end MetricsTest

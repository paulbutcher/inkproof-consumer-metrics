/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Proofs
import Inkproof.Scale.Proofs
import Metrics.Chart

/-! What the consumer computes, proved by applying Inkproof.Core's and Inkproof.Scale's published
theorems to its own types, with every hypothesis discharged (VAL-2). -/

namespace Metrics

open Inkproof.Core Inkproof.Scale

namespace GapPolicy

theorem isGap_iff (p : GapPolicy) (a b : Time) :
    p.isGap a b = true ↔ p.staleAfter < b - a ∨ ∃ r ∈ p.restarts, a < r ∧ r ≤ b := by
  simp only [isGap, Bool.or_eq_true, decide_eq_true_eq, Array.any_eq_true', Bool.and_eq_true]

/-- A segment starts at scrape `b` exactly when the policy calls the step from the scrape before it
a gap. -/
theorem mem_breaks_segment (p : GapPolicy) (s : Scrapes) (b : Nat) :
    b ∈ (p.segment s).breaks ↔
      ∃ h : 0 < b ∧ b < s.size,
        p.staleAfter < s.xs[b]'h.2 - s.xs[b - 1]'(by unfold Series.size at h; omega) ∨
          ∃ r ∈ p.restarts, s.xs[b - 1]'(by unfold Series.size at h; omega) < r ∧ r ≤ s.xs[b]'h.2 := by
  simp only [segment, Segmented.mem_breaks_splitWhere, isGap_iff]

end GapPolicy

/-- The scrapes of segment `k` that fall in `[x₀, x₁)`. -/
abbrev inWindow (ch : Chart) (k : Nat) (x₀ x₁ : Time) : Array (Time × Option Reading) :=
  (ch.segmented.segment k).points.filter (Series.inRange x₀ x₁)

theorem query_eq (ch : Chart) (x₀ x₁ : Time) {k : Nat} (hk : k < (ch.query x₀ x₁).size) :
    (ch.query x₀ x₁)[k] = Aggregate.fold ch.measure (inWindow ch k x₀ x₁) :=
  SegmentedPyramid.getElem_query ch x₀ x₁ hk

theorem fold_summarise (xs : Array (Time × Option Reading)) :
    Aggregate.fold summarise xs =
      (Aggregate.fold (fun p => (⟨p.2⟩ : First Reading)) xs,
        Aggregate.fold (fun p => (⟨p.2⟩ : Maximum Reading)) xs,
        Aggregate.fold (fun p => (⟨p.2⟩ : Minimum Reading)) xs,
        Aggregate.fold (fun p => (⟨p.2⟩ : Last Reading)) xs) := by
  unfold summarise
  rw [Aggregate.fold_prod, Aggregate.fold_prod, Aggregate.fold_prod]

/-- What a chart built by `chart` reports for segment `k` and the times `[x₀, x₁)`: the first and
last readings present there, in time order, and the highest and lowest. Nothing from another
segment contributes. -/
theorem query_chart (p : GapPolicy) (s : Scrapes) (x₀ x₁ : Time) {k : Nat}
    (hk : k < ((chart p s).query x₀ x₁).size) :
    let q := ((chart p s).query x₀ x₁)[k]
    let w := (inWindow (chart p s) k x₀ x₁).toList
    q.1.get = w.findSome? (·.2) ∧
      q.2.2.2.get = w.reverse.findSome? (·.2) ∧
      (∀ a, q.2.1.get = some a ↔ (∃ x ∈ w, x.2 = some a) ∧ ∀ x ∈ w, ∀ b, (x : Time × Option Reading).2 = some b → b ≤ a) ∧
      (∀ a, q.2.2.1.get = some a ↔ (∃ x ∈ w, x.2 = some a) ∧ ∀ x ∈ w, ∀ b, (x : Time × Option Reading).2 = some b → a ≤ b) ∧
      (q.2.1.get = none ↔ ∀ x ∈ w, (x : Time × Option Reading).2 = none) := by
  intro q w
  have hq : q = Aggregate.fold summarise (inWindow (chart p s) k x₀ x₁) := query_eq _ _ _ hk
  rw [fold_summarise] at hq
  refine ⟨?_, ?_, fun a => ?_, fun a => ?_, ?_⟩ <;> rw [hq]
  · exact First.fold_get _ _
  · exact Last.fold_get _ _
  · simp only [w, Array.mem_toList_iff]
    exact Maximum.fold_get_eq_some (fun (x : Time × Option Reading) => (⟨x.2⟩ : Maximum Reading)) _ a
  · simp only [w, Array.mem_toList_iff]
    exact Minimum.fold_get_eq_some (fun (x : Time × Option Reading) => (⟨x.2⟩ : Minimum Reading)) _ a
  · simp only [w, Array.mem_toList_iff]
    exact Maximum.fold_get_eq_none (fun (x : Time × Option Reading) => (⟨x.2⟩ : Maximum Reading)) _

namespace View

/-- Time runs left to right across a nonempty window. -/
def Valid (v : View) : Prop := v.start < v.stop ∧ 0 < v.columns ∧ v.low < v.high ∧ 0 < v.height

theorem xScale_increasing {v : View} (hv : v.Valid) :
    v.xScale.domainStart < v.xScale.domainEnd ∧ v.xScale.rangeStart < v.xScale.rangeEnd ∨
      v.xScale.domainEnd < v.xScale.domainStart ∧ v.xScale.rangeEnd < v.xScale.rangeStart := by
  have := hv.2.1
  left; simp only [xScale]; exact ⟨hv.1, by exact_mod_cast this⟩

theorem yScale_decreasing {v : View} (hv : v.Valid) :
    v.yScale.domainStart < v.yScale.domainEnd ∧ v.yScale.rangeEnd < v.yScale.rangeStart ∨
      v.yScale.domainEnd < v.yScale.domainStart ∧ v.yScale.rangeStart < v.yScale.rangeEnd := by
  have := hv.2.2.2
  left; simp only [yScale]; exact ⟨hv.2.2.1, by exact_mod_cast this⟩

theorem columnStart_eq (v : View) (c : Nat) :
    v.columnStart c = v.start + c * (v.stop - v.start) / v.columns := by
  simp [columnStart, Linear.inv_eq, Linear.map_eq, xScale]; grind

/-- A time falls in column `c` exactly when the x-scale maps it into `[c, c + 1)`. -/
theorem inRange_columnStart_iff {v : View} (hv : v.Valid) (c : Nat) (x : Time × Option Reading) :
    Series.inRange (v.columnStart c) (v.columnStart (c + 1)) x = true ↔
      (c : Rat) ≤ v.xScale.map x.1 ∧ v.xScale.map x.1 < c + 1 := by
  have hd : v.xScale.domainStart ≠ v.xScale.domainEnd := Rat.ne_of_lt hv.1
  have hr : v.xScale.rangeStart ≠ v.xScale.rangeEnd := by
    simp only [xScale]; have := hv.2.1; exact Rat.ne_of_lt (by exact_mod_cast this)
  have mono := fun a b => v.xScale.map_le_map_iff_of_increasing (x := a) (y := b) (xScale_increasing hv)
  have back := v.xScale.map_inv_map hd hr
  have h₁ : v.columnStart c ≤ x.1 ↔ (c : Rat) ≤ v.xScale.map x.1 := by
    rw [← mono, columnStart, back]
  have h₂ : v.columnStart (c + 1) ≤ x.1 ↔ ((c + 1 : Nat) : Rat) ≤ v.xScale.map x.1 := by
    rw [← mono, columnStart, back]
  simp only [Series.inRange, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, h₁, h₂, Rat.not_le]
  push_cast
  exact Iff.rfl

/-- A higher reading is drawn higher up, at a smaller screen y. -/
theorem yScale_map_le_iff {v : View} (hv : v.Valid) (a b : Reading) :
    v.yScale.map a ≤ v.yScale.map b ↔ b ≤ a :=
  v.yScale.map_le_map_iff_of_decreasing (yScale_decreasing hv)

/-- A reading between `low` and `high` lands on the screen. -/
theorem yScale_map_mem {v : View} (hv : v.Valid) {r : Reading} (hlo : v.low ≤ r) (hhi : r ≤ v.high) :
    0 ≤ v.yScale.map r ∧ v.yScale.map r ≤ v.height := by
  have hd : v.yScale.domainStart ≠ v.yScale.domainEnd := Rat.ne_of_lt hv.2.2.1
  have top : v.yScale.map v.high = 0 := v.yScale.map_domainEnd hd
  have bottom : v.yScale.map v.low = v.height := v.yScale.map_domainStart
  constructor
  · rw [← top]; exact (yScale_map_le_iff hv _ _).mpr hhi
  · rw [← bottom]; exact (yScale_map_le_iff hv _ _).mpr hlo

theorem extent_eq_some (v : View) (s : Summary) (e : Extent) :
    v.extent s = some e ↔
      ∃ f hi lo l, s = (⟨some f⟩, ⟨some hi⟩, ⟨some lo⟩, ⟨some l⟩) ∧
        e = ⟨v.yScale.map f, v.yScale.map hi, v.yScale.map lo, v.yScale.map l⟩ := by
  obtain ⟨⟨f⟩, ⟨hi⟩, ⟨lo⟩, ⟨l⟩⟩ := s
  cases f <;> cases hi <;> cases lo <;> cases l <;> simp [extent, eq_comm]
  constructor
  · rintro rfl; exact ⟨_, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  · rintro ⟨_, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩; rfl

theorem size_column (v : View) (ch : Chart) (c : Nat) :
    (v.column ch c).size = ch.segmented.numSegments := by
  simp [column, SegmentedPyramid.size_query]

theorem getElem_column (v : View) (ch : Chart) (c : Nat) {k : Nat} (hk : k < (v.column ch c).size) :
    (v.column ch c)[k] =
      v.extent ((ch.query (v.columnStart c) (v.columnStart (c + 1)))[k]'(by simpa [column] using hk)) := by
  simp [column]

theorem size_render (v : View) (ch : Chart) : (v.render ch).size = v.columns := by
  simp [render]

theorem getElem_render (v : View) (ch : Chart) {c : Nat} (hc : c < (v.render ch).size) :
    (v.render ch)[c] = v.column ch c := by
  simp [render]

end View

end Metrics

import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact arithmetic for the Chen–Engel–Glotzer record

All vertex and period coordinates are multiplied by 160, so the numerical
checks are over integers. Coordinates come from arXiv:1001.0586v3,
Definition 2 and Theorem 1. For each pair and bounded shift, a list of ten
nonzero normals suffices: the translated projection intervals are disjoint
or touch at an endpoint. Lean checks each required comparison by reduction.
-/

namespace TetrahedronPacking

/-- Vertices in units of 1/160, ordered as the two positive and then the two
negative tetrahedra of the double dimer. -/
def recordVertex : Fin 4 → Fin 4 → Fin 3 → ℤ :=
  ![![![320, 320, 320], ![320, -160, -160], ![-160, 320, -160], ![-160, -160, 320]],
    ![![-320, -320, -320], ![320, -160, -160], ![-160, 320, -160], ![-160, -160, 320]],
    ![![134, -157, -343], ![134, 323, 137], ![614, -157, 137], ![614, 323, -343]],
    ![![774, 483, 297], ![134, 323, 137], ![614, -157, 137], ![614, 323, -343]]]

/-- The primitive periods `a+b`, `b+c`, `c+a` in the same units. -/
def recordPeriod : Fin 3 → Fin 3 → ℤ :=
  ![![384, 576, 192], ![90, 291, 573], ![576, 36, 360]]

def integerDot (u v : Fin 3 → ℤ) : ℤ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The minimum and maximum vertex projections on an integer axis. -/
def integerProjectionBounds (n : Fin 3 → ℤ) (v : Fin 4 → Fin 3 → ℤ) : ℤ × ℤ :=
  let p := fun j => integerDot n (v j)
  (min (min (p 0) (p 1)) (min (p 2) (p 3)),
    max (max (p 0) (p 1)) (max (p 2) (p 3)))

/-- Check one nonzero axis, allowing equality at projected endpoints.
The offset is the projection of the translation applied to the right piece. -/
def integerSeparates (n : Fin 3 → ℤ) (v w : Fin 4 → Fin 3 → ℤ) (offset : ℤ) : Bool :=
  let (lo₁, hi₁) := integerProjectionBounds n v
  let (lo₂, hi₂) := integerProjectionBounds n w
  decide ((n 0 ≠ 0 ∨ n 1 ≠ 0 ∨ n 2 ≠ 0) ∧
    (hi₁ ≤ lo₂ + offset ∨ hi₂ + offset ≤ lo₁))

private def separates (n : Fin 3 → ℤ) (i j : Fin 4) (x y z : ℤ) : Bool :=
  let offset := x * integerDot n (recordPeriod 0) + y * integerDot n (recordPeriod 1) +
    z * integerDot n (recordPeriod 2)
  integerSeparates n (recordVertex i) (recordVertex j) offset

private def axes : List (Fin 3 → ℤ) :=
  [![1, 1, 1], ![1, -5, 1], ![1, 1, -5], ![5, -1, -1], ![1, 1, -1],
    ![1, -1, -3], ![1, -1, 1], ![1, -1, -1], ![1, 3, -1], ![3, -1, 1]]

example : recordVertex 2 0 2 = -343 ∧ recordVertex 2 0 2 ≠ 343 := by decide
example : recordPeriod 2 1 = 36 ∧ recordPeriod 2 1 ≠ 0 := by decide
example : integerDot ![1, 1, 1] ![1, 2, 3] = 6 ∧
    integerDot ![1, 1, 1] ![1, 2, 3] ≠ 0 := by decide
example : integerProjectionBounds ![1, 1, 1] (recordVertex 0) = (0, 960) := by decide
example : integerProjectionBounds ![1, 1, 1] (recordVertex 0) ≠ (1, 960) := by decide
example : integerSeparates ![1, 1, 1] (recordVertex 0) (recordVertex 1) 0 = true := by decide
example : integerSeparates ![0, 0, 0] (recordVertex 0) (recordVertex 1) 0 = false := by decide
example : separates ![1, 1, 1] 0 1 0 0 0 = true := by decide
example : separates ![1, 1, 1] 0 0 0 0 0 = false := by decide
example : axes.any (fun n => separates n 0 1 0 0 0) = true := by decide
example : axes.any (fun n => separates n 0 0 0 0 0) = false := by decide

theorem integerProjectionBounds_spec (n : Fin 3 → ℤ) (v : Fin 4 → Fin 3 → ℤ) (a : Fin 4) :
    (integerProjectionBounds n v).1 ≤ integerDot n (v a) ∧
    integerDot n (v a) ≤ (integerProjectionBounds n v).2 := by
  fin_cases a <;> simp [integerProjectionBounds, min_le_iff, le_max_iff]

theorem integerSeparates_sound (n : Fin 3 → ℤ) (v w : Fin 4 → Fin 3 → ℤ) (offset : ℤ)
    (h : integerSeparates n v w offset = true) :
    (∃ j, n j ≠ 0) ∧
      ((∀ a b : Fin 4, integerDot n (v a) ≤ integerDot n (w b) + offset) ∨
       (∀ a b : Fin 4, integerDot n (w b) + offset ≤ integerDot n (v a))) := by
  dsimp [integerSeparates] at h
  obtain ⟨hn, hw⟩ := of_decide_eq_true h
  constructor
  · rcases hn with h₀ | h₁ | h₂
    · exact ⟨0, h₀⟩
    · exact ⟨1, h₁⟩
    · exact ⟨2, h₂⟩
  obtain hw | hw := hw
  · left
    intro a b
    exact (integerProjectionBounds_spec n v a).2.trans
      (hw.trans (add_le_add_right (integerProjectionBounds_spec n w b).1 _))
  · right
    intro a b
    exact (add_le_add_right (integerProjectionBounds_spec n w b).2 _).trans
      (hw.trans (integerProjectionBounds_spec n v a).1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem record_bounded_separations (i j : Fin 4) (x y z : Fin 5) :
    (i = j ∧ x = 2 ∧ y = 2 ∧ z = 2) ∨
    axes.any (fun n => separates n i j (x.val - (2 : ℤ)) (y.val - (2 : ℤ))
      (z.val - (2 : ℤ))) = true := by
  revert i j x y z
  decide +kernel

theorem record_integer_separator (i j : Fin 4) (x y z : Fin 5)
    (h : ¬ (i = j ∧ x = 2 ∧ y = 2 ∧ z = 2)) :
    ∃ n, integerSeparates n (recordVertex i) (recordVertex j)
      ((x.val - (2 : ℤ)) * integerDot n (recordPeriod 0) +
       (y.val - (2 : ℤ)) * integerDot n (recordPeriod 1) +
       (z.val - (2 : ℤ)) * integerDot n (recordPeriod 2)) = true := by
  obtain ⟨n, _, hs⟩ := List.any_eq_true.mp ((record_bounded_separations i j x y z).resolve_left h)
  exact ⟨n, hs⟩

theorem record_integer_planes (i j : Fin 4) (x y z : Fin 5)
    (h : ¬ (i = j ∧ x = 2 ∧ y = 2 ∧ z = 2)) :
    ∃ n : Fin 3 → ℤ, 0 < n 0 ∧
      let offset := (x.val - (2 : ℤ)) * integerDot n (recordPeriod 0) +
        (y.val - (2 : ℤ)) * integerDot n (recordPeriod 1) +
        (z.val - (2 : ℤ)) * integerDot n (recordPeriod 2)
      (∀ a b : Fin 4, integerDot n (recordVertex i a) ≤ integerDot n (recordVertex j b) + offset) ∨
      (∀ a b : Fin 4, integerDot n (recordVertex j b) + offset ≤ integerDot n (recordVertex i a)) := by
  obtain ⟨n, hn, hs⟩ := List.any_eq_true.mp ((record_bounded_separations i j x y z).resolve_left h)
  refine ⟨n, ?_, (integerSeparates_sound n (recordVertex i) (recordVertex j) _ hs).2⟩
  simp only [axes, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h <;> subst n <;> decide

theorem record_integer_edge_lengths (i a b : Fin 4) (h : a ≠ b) :
    integerDot (fun t => recordVertex i a t - recordVertex i b t)
      (fun t => recordVertex i a t - recordVertex i b t) = 460800 := by
  revert i a b
  decide

#print axioms record_bounded_separations
#print axioms integerSeparates_sound
#print axioms record_integer_planes
#print axioms record_integer_edge_lengths

end TetrahedronPacking

import TetrahedronPacking.IntegerCertificate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp

/-!
# Exact periodic cell checking

The input consists of integer vertices, a period matrix, a candidate inverse
numerator with positive denominator, and a list of possible separating axes.
The matrix identities certify the inverse. Projecting the vertices by its
integer rows gives pair-specific shift bounds, rounded by integer division.
Every offset in the finite search is computed by the period matrix itself.
-/

namespace TetrahedronPacking

open Set Matrix

structure IntegerCell (m : ℕ) where
  vertices : Fin m → Fin 4 → Fin 3 → ℤ
  periods : Matrix (Fin 3) (Fin 3) ℤ
  inverseNumerator : Matrix (Fin 3) (Fin 3) ℤ
  denominator : ℤ
  axes : List (Fin 3 → ℤ)

namespace IntegerCell

def inverseValid {m : ℕ} (g : IntegerCell m) : Prop :=
  0 < g.denominator ∧
    g.periods * g.inverseNumerator = g.denominator • 1 ∧
    g.inverseNumerator * g.periods = g.denominator • 1

instance {m : ℕ} (g : IntegerCell m) : Decidable g.inverseValid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def shift {m : ℕ} (g : IntegerCell m) (k : Fin 3 → ℤ) (r : Fin 3) : ℤ :=
  integerDot (g.periods r) k

def bounds {m : ℕ} (g : IntegerCell m) (i : Fin m) (r : Fin 3) : ℤ × ℤ :=
  integerProjectionBounds (g.inverseNumerator r) (g.vertices i)

def lower {m : ℕ} (g : IntegerCell m) (i j : Fin m) (r : Fin 3) : ℤ :=
  -(((g.bounds j r).2 - (g.bounds i r).1) / g.denominator)

def upper {m : ℕ} (g : IntegerCell m) (i j : Fin m) (r : Fin 3) : ℤ :=
  ((g.bounds i r).2 - (g.bounds j r).1) / g.denominator

/-- Search precisely the bounded shifts. Only a piece paired with itself at
the zero shift can bypass the projection checks. -/
def checkPair {m : ℕ} (g : IntegerCell m) (i j : Fin m) : Bool :=
  decide (∀ k ∈ integerShiftBox (g.lower i j) (g.upper i j),
    (i = j ∧ k = 0) ∨ g.axes.any (fun n =>
      integerSeparates n (g.vertices i) (g.vertices j) (integerDot n (g.shift k))) = true)

def realPeriods {m : ℕ} (g : IntegerCell m) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (g.periods i j : ℝ)

noncomputable def realInverse {m : ℕ} (g : IntegerCell m) : Matrix (Fin 3) (Fin 3) ℝ :=
  (g.denominator : ℝ)⁻¹ • (Matrix.of fun i j => (g.inverseNumerator i j : ℝ))

private theorem cast_mul_scalar_one (B A : Matrix (Fin 3) (Fin 3) ℤ) (d : ℤ)
    (h : B * A = d • 1) :
    (Matrix.of fun i j => (B i j : ℝ)) * (Matrix.of fun i j => (A i j : ℝ)) =
      (d : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  have hij := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M i j) h
  by_cases he : i = j
  · simp [Matrix.mul_apply, Matrix.one_apply, he] at hij ⊢
    exact_mod_cast hij
  · simp [Matrix.mul_apply, Matrix.one_apply, he] at hij ⊢
    exact_mod_cast hij

private theorem real_inverse_products {m : ℕ} (g : IntegerCell m) (h : g.inverseValid) :
    g.realPeriods * g.realInverse = 1 ∧ g.realInverse * g.realPeriods = 1 := by
  have hd : (g.denominator : ℝ) ≠ 0 := by exact_mod_cast h.1.ne'
  constructor
  · rw [realInverse, Matrix.mul_smul, realPeriods,
      cast_mul_scalar_one _ _ _ h.2.1, smul_smul, inv_mul_cancel₀ hd, one_smul]
  · rw [realInverse, Matrix.smul_mul, realPeriods,
      cast_mul_scalar_one _ _ _ h.2.2, smul_smul, inv_mul_cancel₀ hd, one_smul]

noncomputable def chart {m : ℕ} (g : IntegerCell m) (h : g.inverseValid) :
    (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin'OfInv (real_inverse_products g h).1 (real_inverse_products g h).2

theorem chart_symm_apply {m : ℕ} (g : IntegerCell m) (h : g.inverseValid) (x : Fin 3 → ℝ) :
    (g.chart h).symm x = g.realPeriods *ᵥ x := rfl

private theorem shift_cast {m : ℕ} (g : IntegerCell m) (h : g.inverseValid)
    (k : Fin 3 → ℤ) :
    (g.chart h).symm (fun r => (k r : ℝ)) = (fun r => (g.shift k r : ℝ)) := by
  rw [chart_symm_apply]
  ext r
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, realPeriods, shift, integerDot]

private theorem chart_vertex {m : ℕ} (g : IntegerCell m) (h : g.inverseValid)
    (i : Fin m) (a : Fin 4) (r : Fin 3) :
    g.chart h (fun q => (g.vertices i a q : ℝ)) r =
      (integerDot (g.inverseNumerator r) (g.vertices i a) : ℝ) / (g.denominator : ℝ) := by
  change (g.realInverse *ᵥ fun q => (g.vertices i a q : ℝ)) r = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, realInverse, integerDot, div_eq_mul_inv]
  ring

private theorem rounded_margin (a d : ℤ) (hd : 0 < d) :
    (a : ℝ) / (d : ℝ) < (↑(a / d) : ℝ) + 1 := by
  apply (div_lt_iff₀ (by exact_mod_cast hd)).mpr
  exact_mod_cast Int.lt_ediv_add_one_mul_self a hd

theorem disjoint_of_checkPair {m : ℕ} (g : IntegerCell m) (h : g.inverseValid) (i j : Fin m)
    (hp : g.checkPair i j = true) (k : Fin 3 → ℤ) (hk : i ≠ j ∨ k ≠ 0) :
    Disjoint (interior (convexHull ℝ (range (fun a r => (g.vertices i a r : ℝ)))))
      (interior (convexHull ℝ (range (fun a =>
        (fun r => (g.vertices j a r : ℝ)) + (g.chart h).symm (fun r => (k r : ℝ)))))) := by
  have hd : (0 : ℝ) < g.denominator := by exact_mod_cast h.1
  let lo (i : Fin m) (r : Fin 3) := ((g.bounds i r).1 : ℝ) / (g.denominator : ℝ)
  let hi (i : Fin m) (r : Fin 3) := ((g.bounds i r).2 : ℝ) / (g.denominator : ℝ)
  have hb (i : Fin m) (a : Fin 4) (r : Fin 3) :
      lo i r ≤ g.chart h (fun q => (g.vertices i a q : ℝ)) r ∧
        g.chart h (fun q => (g.vertices i a q : ℝ)) r ≤ hi i r := by
    rw [chart_vertex]
    obtain ⟨hl, hh⟩ := integerProjectionBounds_spec (g.inverseNumerator r) (g.vertices i) a
    exact ⟨div_le_div_of_nonneg_right (by exact_mod_cast hl) hd.le,
      div_le_div_of_nonneg_right (by exact_mod_cast hh) hd.le⟩
  rw [shift_cast]
  apply integer_shift_certificates_of_box (g.chart h) g.shift (shift_cast g h)
    (g.vertices i) (g.vertices j) (fun s => i ≠ j ∨ s ≠ 0)
    (lo i) (hi i) (lo j) (hi j) (g.lower i j) (g.upper i j) (hb i) (hb j) _ _ _ k hk
  · intro r
    have hn := rounded_margin ((g.bounds j r).2 - (g.bounds i r).1) g.denominator h.1
    push_cast at hn
    simp only [lower, Int.cast_neg, lo, hi]
    rw [← sub_div]
    rw [← neg_sub (↑(g.bounds j r).2 : ℝ) (↑(g.bounds i r).1 : ℝ), neg_div]
    simpa only [neg_add, sub_eq_add_neg] using neg_lt_neg hn
  · intro r
    have hn := rounded_margin ((g.bounds i r).2 - (g.bounds j r).1) g.denominator h.1
    simpa only [hi, lo, ← sub_div, upper, Int.cast_sub] using hn
  · intro s hs hn
    obtain he | hsep := (of_decide_eq_true hp) s hs
    · exact (hn.elim (fun hi => hi he.1) (fun hk => hk he.2)).elim
    · obtain ⟨n, _, hh⟩ := List.any_eq_true.mp hsep
      exact ⟨n, hh⟩

#print axioms disjoint_of_checkPair

end IntegerCell
end TetrahedronPacking

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Optimizing the published double-dimer determinant

Chen–Engel–Glotzer, arXiv:1001.0586v3, equations (6), (7) and (11) give the
periods, constraints and volume polynomial used in Lemma 4. We check
the determinant formula from the period coordinates. Geometric
feasibility of the parameter region is outside this algebraic proof.

Write `s = u/2 + 2v`. The constraints give `|s| + |v| ≤ 3/20`.
Bound the product `s*v` by `|s|*|v|`, then complete the square in
`|v|` at fixed `|s| + |v|`. This bounds the determinant from below.
The stated positive optimizer attains it.
-/

namespace TetrahedronPacking

/-- The signed primitive-period determinant in the paper's unscaled coordinates.
It equals the cell volume on the restricted parameter region. -/
noncomputable def doubleDimerVolume (u v : ℝ) : ℝ :=
  (9 / 25) * (117 + 60 * u ^ 2 - 80 * u * v - 80 * v ^ 2)

example : doubleDimerVolume 0 0 = 1053 / 25 ∧ doubleDimerVolume 0 0 ≠ 42039 / 1000 := by
  norm_num [doubleDimerVolume]

theorem published_period_determinant (u v w : ℝ) :
    let a : Fin 3 → ℝ := ![27 / 10 + u, 21 / 20 - v, -3 / 20 + 2 * u + v]
    let b : Fin 3 → ℝ := ![-3 / 10 - u, 51 / 20 + v, 27 / 20 - 2 * u - v]
    let c : Fin 3 → ℝ :=
      ![129 / 160 - u + 2 * v + 2 * w, -237 / 320 + u / 2 - v + 3 * w,
        753 / 320 + u / 2 - v + w]
    (Matrix.of ![a + b, b + c, c + a]).det = doubleDimerVolume u v := by
  dsimp only
  simp [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    doubleDimerVolume]
  ring

theorem double_dimer_volume_lower_bound (u v w : ℝ)
    (hs : |u / 2 + 2 * v| ≤ 33 / 320 + w) (hv : |v| ≤ 3 / 64 - w) :
    42039 / 1000 ≤ doubleDimerVolume u v := by
  let s := u / 2 + 2 * v
  have hsum : |s| + |v| ≤ 3 / 20 := by
    change |s| ≤ 33 / 320 + w at hs
    linarith
  have hsum_nonneg : 0 ≤ |s| + |v| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsum_sq : (|s| + |v|) ^ 2 ≤ (3 / 20 : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hsum hsum hsum_nonneg
      (show 0 ≤ (3 / 20 : ℝ) by norm_num)
  have hprod : s * v ≤ |s| * |v| := by
    simpa only [abs_mul] using le_abs_self (s * v)
  have hq : 60 * u ^ 2 - 80 * u * v - 80 * v ^ 2 =
      2560 * (|v| - (5 / 16) * (|s| + |v|)) ^ 2 -
        10 * (|s| + |v|) ^ 2 + 1120 * (|s| * |v| - s * v) := by
    calc
      _ = 240 * s ^ 2 - 1120 * s * v + 1200 * v ^ 2 := by dsimp [s]; ring
      _ = 240 * |s| ^ 2 - 1120 * s * v + 1200 * |v| ^ 2 := by rw [sq_abs, sq_abs]
      _ = _ := by ring
  have hq_lower : -(9 / 40 : ℝ) ≤ 60 * u ^ 2 - 80 * u * v - 80 * v ^ 2 := by
    rw [hq]
    have hp : 0 ≤ 2560 * (|v| - (5 / 16) * (|s| + |v|)) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have hn : -(9 / 40 : ℝ) ≤ -10 * (|s| + |v|) ^ 2 := by linarith only [hsum_sq]
    have hcross : 0 ≤ 1120 * (|s| * |v| - s * v) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr hprod)
    simpa only [zero_add, add_zero, neg_mul, sub_eq_add_neg] using
      add_le_add (add_le_add hp hn) hcross
  unfold doubleDimerVolume
  linarith only [hq_lower]

theorem double_dimer_density_ratio_upper_bound (u v w : ℝ)
    (hs : |u / 2 + 2 * v| ≤ 33 / 320 + w) (hv : |v| ≤ 3 / 64 - w) :
    36 / doubleDimerVolume u v ≤ 4000 / 4671 := by
  have h := double_dimer_volume_lower_bound u v w hs hv
  have hp : 0 < doubleDimerVolume u v := by linarith
  apply (div_le_iff₀ hp).mpr
  linarith

theorem double_dimer_ratio_attains_bound :
    |(3 / 160 : ℝ) / 2 + 2 * (3 / 64)| ≤ 33 / 320 + 0 ∧
    |(3 / 64 : ℝ)| ≤ 3 / 64 - 0 ∧
    36 / doubleDimerVolume (3 / 160) (3 / 64) = 4000 / 4671 := by
  norm_num [doubleDimerVolume, abs_of_nonneg]

#print axioms double_dimer_volume_lower_bound
#print axioms published_period_determinant
#print axioms double_dimer_density_ratio_upper_bound
#print axioms double_dimer_ratio_attains_bound

end TetrahedronPacking

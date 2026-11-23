import TetrahedronPacking.CellDensity

/-!
# Density screening for regular tetrahedron cells

For edge vectors taken from one vertex, the doubled Gram matrix has
diagonal twice the squared edge length and off-diagonal the squared
edge length. Taking determinants gives twice the squared edge determinant
as the cube of the squared length. All regular pieces therefore have the
same absolute edge determinant. A comparison against the record can use
only the number of pieces, squared length, and period determinant.
-/

namespace TetrahedronPacking.IntegerCell

open Matrix

theorem regular_edge_det_sq {m : ℕ} (g : IntegerCell m) (i : Fin m) (s : ℤ)
    (regular : g.checkRegular s i = true) :
    2 * (g.edgeMatrix i).det ^ 2 = s ^ 3 := by
  have h : 0 < s ∧ (g.edgeMatrix i).det ≠ 0 ∧
      ∀ a b : Fin 4, a ≠ b →
        integerDot (fun r => g.vertices i a r - g.vertices i b r)
          (fun r => g.vertices i a r - g.vertices i b r) = s :=
    of_decide_eq_true regular
  let M := g.edgeMatrix i
  let G : Matrix (Fin 3) (Fin 3) ℤ := !![2*s, s, s; s, 2*s, s; s, s, 2*s]
  have gram : (2 : ℤ) • (Mᵀ * M) = G := by
    have diag (j : Fin 3) : (Mᵀ * M) j j = s := by
      simpa [M, edgeMatrix, Matrix.mul_apply, Fin.sum_univ_three, integerDot] using
        h.2.2 j.succ 0 (Fin.succ_ne_zero j)
    have off (j k : Fin 3) (hne : j ≠ k) : 2 * (Mᵀ * M) j k = s := by
      have hj := diag j
      have hk := diag k
      have hjk := h.2.2 j.succ k.succ (fun he => hne (Fin.succ_injective _ he))
      simp only [M, edgeMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
        Matrix.of_apply] at hj hk ⊢
      simp only [integerDot] at hjk
      linear_combination hj + hk - hjk
    ext j k
    by_cases he : j = k
    · subst k
      simp only [Matrix.smul_apply, smul_eq_mul, diag]
      fin_cases j <;> rfl
    · rw [Matrix.smul_apply, smul_eq_mul, off j k he]
      fin_cases j <;> fin_cases k <;> first | rfl | contradiction
  have hd := congrArg Matrix.det gram
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose] at hd
  simp only [Fintype.card_fin] at hd
  change 2 ^ 3 * (M.det * M.det) = G.det at hd
  have hG : G.det = 4 * s ^ 3 := by
    simp [G, Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    ring
  rw [hG, ← pow_two] at hd
  change 2 * M.det ^ 2 = s ^ 3
  omega

/-- A strict record comparison using only the three quantities needed
before checking periodic overlaps. Zero pieces are allowed and fail
the strict comparison. -/
theorem regular_record_screen {m : ℕ} (g : IntegerCell m) (s : ℤ)
    (regular : ∀ i, g.checkRegular s i = true) :
    4000 * (6 * |g.periods.det|) < 4671 * g.volumeNumerator ↔
      2 * (4000 * (6 * |g.periods.det|)) ^ 2 < 4671 ^ 2 * (m : ℤ) ^ 2 * s ^ 3 := by
  let d := fun i => |(g.edgeMatrix i).det|
  have hd (i) : 2 * d i ^ 2 = s ^ 3 := by
    simpa [d, sq_abs] using g.regular_edge_det_sq i s (regular i)
  have hvol : 2 * g.volumeNumerator ^ 2 = (m : ℤ) ^ 2 * s ^ 3 := by
    by_cases hm : m = 0
    · subst m
      simp [volumeNumerator]
    · let i : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
      have he (j) : d j = d i := by
        have hj := hd j
        have hi := hd i
        have hj0 : 0 ≤ d j := abs_nonneg _
        have hi0 : 0 ≤ d i := abs_nonneg _
        nlinarith [sq_nonneg (d j - d i)]
      have hs : g.volumeNumerator = (m : ℤ) * d i := by
        change (∑ j, d j) = _
        simp [he, Finset.sum_const, nsmul_eq_mul]
      rw [hs]
      linear_combination (m : ℤ) ^ 2 * hd i
  have hleft : 0 ≤ 4000 * (6 * |g.periods.det|) := by positivity
  have hright : 0 ≤ 4671 * g.volumeNumerator :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hsq : (4671 ^ 2 : ℤ) * (m : ℤ) ^ 2 * s ^ 3 =
      2 * (4671 * g.volumeNumerator) ^ 2 := by
    linear_combination -4671 ^ 2 * hvol
  rw [hsq, mul_lt_mul_iff_of_pos_left (by norm_num : (0 : ℤ) < 2)]
  exact (sq_lt_sq₀ hleft hright).symm

#print axioms regular_record_screen

end TetrahedronPacking.IntegerCell

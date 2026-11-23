import TetrahedronPacking.CellChecker
import TetrahedronPacking.PeriodicDensity
import TetrahedronPacking.SimplexVolume
import Mathlib.Analysis.Convex.Topology

/-!
# Density of a checked periodic cell

The full-rank chart supplies the lattice basis. Pair checks cover relative
translations, hence every distinct pair of indexed copies. The density is
the sum of the motif's determinant volumes divided by the period covolume.
-/

namespace TetrahedronPacking.IntegerCell

open Filter MeasureTheory MeasureTheory.Measure Set Matrix
open scoped Pointwise Topology

def realVertex {m : ℕ} (g : IntegerCell m) (i : Fin m) (a : Fin 4) (r : Fin 3) : ℝ :=
  g.vertices i a r

def piece {m : ℕ} (g : IntegerCell m) (i : Fin m) : Set (Fin 3 → ℝ) :=
  convexHull ℝ (range (g.realVertex i))

noncomputable def basis {m : ℕ} (g : IntegerCell m) (h : g.inverseValid) :
    Basis (Fin 3) ℝ (Fin 3 → ℝ) :=
  (Pi.basisFun ℝ (Fin 3)).map (g.chart h).symm

def edgeMatrix {m : ℕ} (g : IntegerCell m) (i : Fin m) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun r j => g.vertices i j.succ r - g.vertices i 0 r

/-- Check regularity of a labelled piece at the common squared edge length. -/
def checkRegular {m : ℕ} (g : IntegerCell m) (squaredLength : ℤ) (i : Fin m) : Bool :=
  decide (0 < squaredLength ∧ (g.edgeMatrix i).det ≠ 0 ∧
    ∀ a b : Fin 4, a ≠ b →
      integerDot (fun r => g.vertices i a r - g.vertices i b r)
        (fun r => g.vertices i a r - g.vertices i b r) = squaredLength)

theorem regular_of_checkRegular {m : ℕ} (g : IntegerCell m) (squaredLength : ℤ) (i : Fin m)
    (h : g.checkRegular squaredLength i = true) :
    0 < squaredLength ∧ (g.edgeMatrix i).det ≠ 0 ∧
      ∀ a b : Fin 4, a ≠ b →
        ∑ r, (g.realVertex i a r - g.realVertex i b r) ^ 2 = (squaredLength : ℝ) := by
  obtain ⟨hp, hd, he⟩ := of_decide_eq_true h
  refine ⟨hp, hd, ?_⟩
  intro a b hab
  have hr := congrArg (fun z : ℤ => (z : ℝ)) (he a b hab)
  simpa [integerDot, realVertex, Fin.sum_univ_three, pow_two] using hr

def volumeNumerator {m : ℕ} (g : IntegerCell m) : ℤ :=
  ∑ i, |(g.edgeMatrix i).det|

theorem piece_volume {m : ℕ} (g : IntegerCell m) (i : Fin m) :
    volume.real (g.piece i) = (|(g.edgeMatrix i).det| : ℤ) / (6 : ℝ) := by
  rw [piece, tetrahedron_volume]
  have hcast : (Matrix.of (fun r (j : Fin 3) =>
      g.realVertex i j.succ r - g.realVertex i 0 r)).det = ((g.edgeMatrix i).det : ℝ) := by
    simp [Matrix.det_fin_three, realVertex, edgeMatrix]
  rw [hcast, Int.cast_abs]

theorem lattice_covolume {m : ℕ} (g : IntegerCell m) (h : g.inverseValid) :
    ZLattice.covolume (Submodule.span ℤ (range (g.basis h))) = (|g.periods.det| : ℤ) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (g.basis h) volume), ZSpan.volume_real_fundamentalDomain]
  have hmat : Matrix.of (g.basis h) = g.realPeriods.transpose := by
    ext i j
    change ((g.chart h).symm ((Pi.basisFun ℝ (Fin 3)) i)) j = g.realPeriods j i
    rw [Pi.basisFun_apply, chart_symm_apply, Matrix.mulVec_single_one]
    rfl
  rw [hmat, Matrix.det_transpose, Int.cast_abs]
  congr 1
  simp [Matrix.det_fin_three, realPeriods]

theorem pairwise_disjoint_of_checks {m : ℕ} (g : IntegerCell m) (h : g.inverseValid)
    (checks : ∀ i j, g.checkPair i j = true) :
    let L := Submodule.span ℤ (range (g.basis h))
    Pairwise fun p q : Fin m × L =>
      Disjoint (interior ((p.2 : Fin 3 → ℝ) +ᵥ g.piece p.1))
        (interior ((q.2 : Fin 3 → ℝ) +ᵥ g.piece q.1)) := by
  let L := Submodule.span ℤ (range (g.basis h))
  have coord (p : L) : ∃ k : Fin 3 → ℤ, (p : Fin 3 → ℝ) =
      (g.chart h).symm (fun r => (k r : ℝ)) := by
    choose k hk using ((g.basis h).mem_span_iff_repr_mem ℤ _).mp p.property
    refine ⟨k, (g.chart h).injective ?_⟩
    ext r
    have hr := (hk r).symm
    change (Pi.basisFun ℝ (Fin 3)).repr (g.chart h (p : Fin 3 → ℝ)) r = (k r : ℝ) at hr
    simpa using hr
  change Pairwise (fun p q : Fin m × L =>
    Disjoint (interior ((p.2 : Fin 3 → ℝ) +ᵥ g.piece p.1))
      (interior ((q.2 : Fin 3 → ℝ) +ᵥ g.piece q.1)))
  intro p q hpq
  obtain ⟨k, hk⟩ := coord p.2
  obtain ⟨l, hl⟩ := coord q.2
  have hne : p.1 ≠ q.1 ∨ l - k ≠ 0 := by
    by_contra! he
    apply hpq
    refine Prod.ext he.1 (Subtype.ext ?_)
    rw [hk, hl, sub_eq_zero.mp he.2]
  have shift_eq : (fun r : Fin 3 => (↑((l - k) r) : ℝ)) =
      (fun r => (l r : ℝ)) - (fun r => (k r : ℝ)) := by
    ext r
    exact Int.cast_sub _ _
  let e := Homeomorph.addRight (p.2 : Fin 3 → ℝ)
  have hdisj := Set.disjoint_image_of_injective e.injective
    (g.disjoint_of_checkPair h p.1 q.1 (checks p.1 q.1) (l - k) hne)
  have translate (i : Fin m) (x : Fin 3 → ℝ) :
      x +ᵥ g.piece i = convexHull ℝ (range fun j => g.realVertex i j + x) := by
    rw [piece, ← convexHull_vadd]
    change convexHull ℝ ((fun y => x + y) '' range (g.realVertex i)) = _
    rw [← range_comp]
    simp only [Function.comp_def, add_comm]
  have e_hull (v : Fin 4 → Fin 3 → ℝ) :
      e '' convexHull ℝ (range v) = convexHull ℝ (range fun a => v a + (p.2 : Fin 3 → ℝ)) := by
    simpa only [← range_comp] using
      AffineMap.image_convexHull (AffineEquiv.vaddConst ℝ (p.2 : Fin 3 → ℝ)).toAffineMap (range v)
  simp only [e.image_interior, e_hull, shift_eq, map_sub] at hdisj
  rw [translate, translate, hl]
  rw [hk] at hdisj ⊢
  simpa only [realVertex, add_assoc, sub_add_cancel] using hdisj

theorem spatial_density_of_checks {m : ℕ} (g : IntegerCell m) (h : g.inverseValid)
    (checks : ∀ i j, g.checkPair i j = true) :
    let L := Submodule.span ℤ (range (g.basis h))
    Tendsto (fun R : ℝ =>
      volume.real ((⋃ p : Fin m × L, (p.2 : Fin 3 → ℝ) +ᵥ g.piece p.1) ∩ Metric.closedBall 0 R) /
        volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R))
      atTop (𝓝 ((g.volumeNumerator : ℝ) / (6 * (|g.periods.det| : ℤ)))) := by
  let L := Submodule.span ℤ (range (g.basis h))
  have hb : Bornology.IsBounded (⋃ i, g.piece i) :=
    Bornology.isBounded_iUnion.mpr fun i => (finite_range _).isCompact_convexHull.isBounded
  obtain ⟨d, hd⟩ := hb.exists_norm_le
  have ht := periodic_convex_density L g.piece d (fun _ => convex_convexHull ℝ _)
    (fun i x hx => hd x (mem_iUnion.mpr ⟨i, hx⟩)) (g.pairwise_disjoint_of_checks h checks)
  rw [g.lattice_covolume h] at ht
  simp only [g.piece_volume, ← Finset.sum_div, ← Int.cast_sum, ← div_div, volumeNumerator] at ht ⊢
  exact ht

#print axioms spatial_density_of_checks
#print axioms regular_of_checkRegular

/-- A checked cell with a strict integer cross-product inequality has
spatial density strictly above the published record. -/
theorem beats_record_of_checks {m : ℕ} (g : IntegerCell m) (h : g.inverseValid)
    (checks : ∀ i j, g.checkPair i j = true)
    (strict : 4000 * (6 * |g.periods.det|) < 4671 * g.volumeNumerator) :
    let L := Submodule.span ℤ (range (g.basis h))
    ∃ ρ : ℝ, 4000 / 4671 < ρ ∧
      Tendsto (fun R : ℝ =>
        volume.real ((⋃ p : Fin m × L, (p.2 : Fin 3 → ℝ) +ᵥ g.piece p.1) ∩ Metric.closedBall 0 R) /
          volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R)) atTop (𝓝 ρ) := by
  refine ⟨_, ?_, g.spatial_density_of_checks h checks⟩
  have hd : 0 < ((|g.periods.det| : ℤ) : ℝ) := by
    rw [← g.lattice_covolume h]
    exact ZLattice.covolume_pos _ volume
  apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 6) hd)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 4671)).mpr
  rw [mul_comm (g.volumeNumerator : ℝ)]
  exact_mod_cast strict

#print axioms beats_record_of_checks

end TetrahedronPacking.IntegerCell

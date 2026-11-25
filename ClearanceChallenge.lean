module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-! # Clearance in the expanded Chen–Engel–Glotzer dimer cell

The columns of the period matrix and the particle centroids are scaled by
1001/1000, with particle shapes fixed. Each perturbed vertex is expressed
in coordinates relative to the actual invertible period basis. Any motif
whose vertices remain within 77892/10^9 in each component of the supplied
rational reference has pairwise disjoint interiors across all copies.
Only the embedded rational data are the inputs to the Lean theorem.
-/

namespace TetrahedronPacking.DimerClearance

open Set

def fractions : Fin 4 → Fin 4 → Fin 3 → ℤ × ℤ := ![
  ![
    ![(1220305, 3022656), (20005, 74217), (380095, 1558557)],
    ![(11905, 365376), (-359965, 519519), (333365, 519519)],
    ![(20853355, 33249216), (-2305, 39963), (-356635, 519519)],
    ![(-1686665, 2557632), (390035, 519519), (23365, 519519)]
  ],
  ![
    ![(-1220305, 3022656), (-20005, 74217), (-380095, 1558557)],
    ![(1076645, 33249216), (-27695, 39963), (999905, 1558557)],
    ![(20846645, 33249216), (-30035, 519519), (-82315, 119889)],
    ![(-21933355, 33249216), (389965, 519519), (6355, 141687)]
  ],
  ![
    ![(1472855, 12090624), (-241753, 296868), (579959, 2078076)],
    ![(720455, 1461504), (307729, 2078076), (-740123, 6234228)],
    ![(-13518595, 132996864), (-77867, 159852), (7539877, 6234228)],
    ![(12123185, 10230528), (-2692271, 2078076), (2979877, 6234228)]
  ],
  ![
    ![(11235295, 12090624), (-81713, 296868), (4780637, 6234228)],
    ![(65588245, 132996864), (23693, 159852), (-739363, 6234228)],
    ![(-13491755, 132996864), (-1011991, 2078076), (580049, 479556)],
    ![(157628245, 132996864), (-2691991, 2078076), (270967, 566748)]
  ]
]

def reference (i : Fin 4) (a : Fin 4) (r : Fin 3) : ℚ :=
  ((fractions i a r).1 : ℚ) / ((fractions i a r).2 : ℚ)

theorem pairwise_disjoint_near_reference (C : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (u : Fin 4 → Fin 4 → Fin 3 → ℝ)
    (hδ : ∀ i a r, |u i a r - (reference i a r : ℝ)| ≤
      (77893 - 1 : ℝ) / 1000000000) :
    let piece (p : Fin 4 × (Fin 3 → ℤ)) :=
      convexHull ℝ (range (fun a => C.symm (u p.1 a) +
        C.symm (fun r => (p.2 r : ℝ))))
    Pairwise fun p q => Disjoint (interior (piece p)) (interior (piece q)) := by
  sorry

end TetrahedronPacking.DimerClearance

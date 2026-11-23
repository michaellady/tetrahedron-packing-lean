module

public import TetrahedronPacking.CellDensity

@[expose] public section

/-!
# Exact cell input

JSON records contain a common coordinate denominator, three period columns
and a motif of tetrahedra. The canonical encoder lets the kernel compare
fixture bytes with the exact data fed to the checker. The checker uses the
integer coordinate numerators as its length units.
-/

namespace TetrahedronPacking

structure CellInput (m : ℕ) where
  coordinateDenominator : ℕ
  periodColumns : Fin 3 → Fin 3 → ℤ
  tetrahedra : Fin m → Fin 4 → Fin 3 → ℤ

namespace CellInput

def canonicalJson {m : ℕ} (input : CellInput m) : String :=
  let brackets := fun parts : List String => "[" ++ ", ".intercalate parts ++ "]"
  let vector := fun v : Fin 3 → ℤ => brackets ((List.finRange 3).map (fun i => toString (v i)))
  let motif := (List.finRange m).map fun i =>
    "    " ++ brackets ((List.finRange 4).map fun j => vector (input.tetrahedra i j))
  "{\n  \"coordinate_denominator\": " ++ toString input.coordinateDenominator ++
    ",\n  \"period_columns\": " ++ brackets ((List.finRange 3).map fun i =>
      vector (input.periodColumns i)) ++
    ",\n  \"tetrahedra\": [\n" ++ ",\n".intercalate motif ++ "\n  ]\n}\n"

/-- Supply an inverse certificate for the row-indexed period matrix and
candidate normals in the same Cartesian frame as the input. -/
def toIntegerCell {m : ℕ} (input : CellInput m)
    (inverse : Matrix (Fin 3) (Fin 3) ℤ) (inverseDenominator : ℤ)
    (axes : List (Fin 3 → ℤ)) : IntegerCell m where
  vertices := input.tetrahedra
  periods := Matrix.of fun r c => input.periodColumns c r
  inverseNumerator := inverse
  denominator := inverseDenominator
  axes := axes

end CellInput
end TetrahedronPacking

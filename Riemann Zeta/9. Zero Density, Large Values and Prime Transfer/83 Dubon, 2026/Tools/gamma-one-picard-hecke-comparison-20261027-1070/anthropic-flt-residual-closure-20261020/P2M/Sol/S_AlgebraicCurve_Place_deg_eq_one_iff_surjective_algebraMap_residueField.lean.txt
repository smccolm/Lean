import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.AlgebraicCurve ModularCurve"

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.deg" namespace Place p2m_export "AlgebraicCurve.Place" "ResidueField deg" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) := by
  unfold Place.deg
  rw [show Function.Surjective (algebraMap K v.ResidueField)
        ↔ Function.Bijective (algebraMap K v.ResidueField) from
      ⟨fun h => ⟨(algebraMap K v.ResidueField).injective, h⟩, fun h => h.2⟩]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.AlgebraicCurve ModularCurve in

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) :=
  AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v

#print axioms solution

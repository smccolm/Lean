import Dubon2026.SourceCurvePowerResidueSum
import Dubon2026.SourceOriginalExactDifferentialResidue
import Dubon2026.SourceOriginalResidueFunctional

/-! DUB-17/18 -> original regular differential dimension -> Riemann--Roch
-> global residue identity. The actual original local residue of df/f is
the normalized order, and every power differential f^n df has zero global
residue. The principal-divisor product formula discharges the logarithmic
case. Arbitrary differentials and the subsequent genus and analytic
cusp-form identification remain required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem original_localResidue_logarithmic
    (v : Place L (modularFunctionFieldOver N L))
    {f : modularFunctionFieldOver N L} (hf : f ≠ 0) :
    (originalCanonicalLocalResidueData N L v).res
      (v.differentialCoeff (D L (modularFunctionFieldOver N L) f) / f) =
        (v.ord f : v.ResidueField) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_original_place_differentials N L v
  haveI := original_place_residue_isAlgebraic N L v
  haveI := original_place_dCoordGenerates N L v
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  exact v.canonicalLocalResidueData_logarithmic
    (original_place_residue_algebraMap_bijective N L v)
    (originalCanonicalLocalResidueData N L v) hf

theorem original_localResidue_power_differential
    (v : Place L (modularFunctionFieldOver N L))
    {f : modularFunctionFieldOver N L} (hf : f ≠ 0) (n : ℤ) :
    (originalCanonicalLocalResidueData N L v).res
      (f ^ n * v.differentialCoeff (D L (modularFunctionFieldOver N L) f)) =
        if n = -1 then (v.ord f : v.ResidueField) else 0 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := finite_original_place_differentials N L v
  haveI := original_place_residue_isAlgebraic N L v
  haveI := original_place_dCoordGenerates N L v
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  exact v.canonicalLocalResidueData_power_differential
    (original_place_residue_algebraMap_bijective N L v)
    (originalCanonicalLocalResidueData N L v) hf n

theorem original_residueSum_power_differential
    {f : modularFunctionFieldOver N L} (hf : f ≠ 0) (n : ℤ) :
    (∑ᶠ v : Place L (modularFunctionFieldOver N L),
      kaehlerResidueTermKFam (originalCanonicalLocalResidueData N L)
        (D L (modularFunctionFieldOver N L) f)
        (diagonalHom L (modularFunctionFieldOver N L) (f ^ n)) v) = 0 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := hasPrincipalDivisors_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L),
      Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] :=
    finite_original_place_differentials N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), Algebra.IsSeparable L v.ResidueField :=
    fun v => by
      haveI := original_place_residue_isAlgebraic N L v
      infer_instance
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI : Nontrivial Ω[modularFunctionFieldOver N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N L)
  exact residueSum_power_differential (K := L) (F := modularFunctionFieldOver N L)
    (originalCanonicalLocalResidueData N L)
    (original_place_residue_algebraMap_bijective N L) hf n

theorem originalResidueFunctional_power_differential
    {f : modularFunctionFieldOver N L}
    (hdf : D L (modularFunctionFieldOver N L) f ≠ 0) (n : ℤ) :
    originalResidueFunctional N L hdf
      ⟨diagonalHom L (modularFunctionFieldOver N L) (f ^ n),
        original_diagonal_mem_adeleSpace N L (f ^ n)⟩ = 0 := by
  have hf : f ≠ 0 := by
    intro hf
    exact hdf (by rw [hf, map_zero])
  exact original_residueSum_power_differential N L hf n

end
end Dubon2026.SourceFunctionField

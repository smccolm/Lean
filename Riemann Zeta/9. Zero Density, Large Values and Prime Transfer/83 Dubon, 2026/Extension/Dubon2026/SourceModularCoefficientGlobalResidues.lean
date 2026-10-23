import Dubon2026.SourceCurveAdjoinGeneratorResidues
import Dubon2026.SourceModularCoefficientGlobalTrace

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> canonical
degree. The actual finite trace transfer and rational-generator residue
theorem prove global residue vanishing on the literal modular coefficient
field in every characteristic. No global residue identity is assumed. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- Global Tate residues against the actual modular j-coordinate sum to zero. -/
theorem coeff_global_tateResidue_j_zero (f : modularFunctionFieldCoeff N K) :
    (∑ᶠ v : Place K (modularFunctionFieldCoeff N K), v.tateResidue f (jCoeff N K)) = 0 := by
  let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
    IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
  letI : Algebra K J := J.toSubalgebra.algebra
  letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
  letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
  letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
  exact (coeff_tateResidue_global_trace N K f
    (IntermediateField.AdjoinSimple.gen K (jCoeff N K))).trans
      (sum_tateResidue_adjoin_generator_eq_zero (jCoeff N K) (transcendental_jCoeff N K)
        (Algebra.trace J (modularFunctionFieldCoeff N K) f))

/-- The canonical residues of every actual global modular differential sum to zero. -/
theorem coeff_global_residue_sum_zero
    (ω : Ω[modularFunctionFieldCoeff N K⁄K]) (f : modularFunctionFieldCoeff N K) :
    (∑ᶠ v : Place K (modularFunctionFieldCoeff N K),
      kaehlerResidueTermKFam (coeffCanonicalLocalResidueData N K) ω
        (diagonalHom K (modularFunctionFieldCoeff N K) f) v) = 0 := by
  haveI : ∀ v : Place K (modularFunctionFieldCoeff N K), v.DCoordGenerates :=
    coeff_place_dCoordGenerates N K
  haveI : Nontrivial Ω[modularFunctionFieldCoeff N K⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_coeff_differentials N K)
  have hmem : ω ∈ Submodule.span (modularFunctionFieldCoeff N K)
      {D K (modularFunctionFieldCoeff N K) (jCoeff N K)} := by
    rw [span_D_jCoeff N K]
    exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  calc
    _ = ∑ᶠ v : Place K (modularFunctionFieldCoeff N K),
        v.tateResidue (f * c) (jCoeff N K) := by
      apply finsum_congr
      intro v
      rw [coeff_tateResidue_eq_canonical_differential N K]
      simp only [kaehlerResidueTermKFam_apply, v.differentialCoeff_smul]
      change Algebra.trace K v.ResidueField ((coeffCanonicalLocalResidueData N K v).res
        (f * (c * v.differentialCoeff (D K (modularFunctionFieldCoeff N K) (jCoeff N K))))) = _
      rw [← mul_assoc]
    _ = 0 := coeff_global_tateResidue_j_zero N K (f * c)

end Dubon2026.SourceFunctionField

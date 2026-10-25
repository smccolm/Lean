import Dubon2026.SourceOriginalArithmeticFieldAction
import Dubon2026.SourceResidueOriginalSpecialization
import Mathlib.RingTheory.Valuation.RamificationGroup

/-! DUB-17/18 -> original Tate/Picard inertia action -> actual modular
reduction equivariance. Native inertia membership gives an integral Laurent
representative of the original arithmetic image with exactly the same residue.
Existing coefficient action and field identification are reused. This is the
function-level input; place/Picard invariance is a further obligation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_reductionModL_smul_eq_self_of_mem_inertiaSubgroupIn. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ

theorem coeffMap_subtype_decomposition
    (A : ValuationSubring Qbar) (d : A.decompositionSubgroup ℚ) (y : LaurentSeries A) :
    coeffMap A.subtype (coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d) y) =
      coeffMap (d.val : Qbar →+* Qbar) (coeffMap A.subtype y) := by
  ext n
  rfl

theorem coeffMap_residue_inertia
    (A : ValuationSubring Qbar) (d : A.decompositionSubgroup ℚ)
    (hd : d ∈ A.inertiaSubgroup ℚ) (y : LaurentSeries A) :
    coeffMap (IsLocalRing.residue A)
        (coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d) y) =
      coeffMap (IsLocalRing.residue A) y := by
  have hπ (a : A) : IsLocalRing.residue A (d • a) = IsLocalRing.residue A a := by
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 := MonoidHom.mem_ker.mp hd
    have h2 := congrArg (fun e : RingAut (IsLocalRing.ResidueField A) =>
      e (IsLocalRing.residue A a)) h1
    simpa using h2
  ext n
  exact hπ (y.coeff n)

theorem original_integral_reduction_inertia
    (N : ℕ) (A : ValuationSubring Qbar) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype)
    (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldOver N Qbar) :
    ∃ y' : LaurentSeries A,
      coeffMap A.subtype y' =
        (originalArithmeticRingAut N τ ⟨coeffMap A.subtype y, hy⟩ : LaurentSeries Qbar) ∧
      coeffMap (IsLocalRing.residue A) y' = coeffMap (IsLocalRing.residue A) y := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hτ
  refine ⟨coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d) y, ?_,
    coeffMap_residue_inertia A d hd y⟩
  exact coeffMap_subtype_decomposition A d y

end
end Dubon2026.SourceFunctionField

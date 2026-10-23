import Dubon2026.SourcePadicIntegerCoefficientMap
import Dubon2026.SourceSpecializationInvariantLattice
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! DUB-17/18 -> primitive residual association -> the stable rank-two
integer lattice. This consumes a spanning specialization of a finite
integral p-adic module and its actual intertwined action. The lattice is
constructed as the integer span of the original integral image. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct ValuativeRel
open Matrix
variable (p : ℕ) [Fact p.Prime]
variable (E : Type) [Field E] [Algebra ℚ_[p] E]
variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

private local instance : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
variable [(ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E)]

private local instance : Algebra ℤ_[p] E := Algebra.compHom E PadicInt.Coe.ringHom
private local instance : IsScalarTower ℤ_[p] ℚ_[p] E :=
  IsScalarTower.of_algebraMap_eq' rfl
private local instance : Algebra ℤ_[p] 𝒪[E] := padicIntegerCoefficientAlgebra p E
private local instance : IsScalarTower ℤ_[p] 𝒪[E] E := padicIntegerCoefficient_scalarTower p E

variable {M G : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M]
variable [Group G]

theorem padicSpecialization_stable_lattice
    (π : ℚ_[p] ⊗[ℤ_[p]] M →ₗ[ℚ_[p]] (Fin 2 → E))
    (hπ : Submodule.span E (Set.range π) = ⊤)
    (η : G →* Module.End ℤ_[p] M) (ρ : G →* GeneralLinearGroup (Fin 2) E)
    (he : ∀ g z, (ρ g).val *ᵥ π z = π ((η g).baseChange ℚ_[p] z)) :
    ∃ L : Submodule 𝒪[E] (Fin 2 → E),
      L = integralImageLattice (S := 𝒪[E]) (scalarExtensionIntegralMap π) ∧
      Submodule.span E (L : Set (Fin 2 → E)) = ⊤ ∧
      Module.Free 𝒪[E] L ∧ Module.Finite 𝒪[E] L ∧ Module.finrank 𝒪[E] L = 2 ∧
      ∀ g v, v ∈ L → (ρ g).val *ᵥ v ∈ L := by
  let L := integralImageLattice (S := 𝒪[E]) (scalarExtensionIntegralMap π)
  obtain ⟨hspan, hfree, hfinite, hrank⟩ := scalarSpecialization_lattice (S := 𝒪[E]) π hπ
  refine ⟨L, rfl, hspan, hfree, hfinite, ?_, ?_⟩
  · simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using hrank
  · intro g
    exact scalarSpecialization_lattice_invariant π
      ((Matrix.mulVecLin (ρ g).val).restrictScalars 𝒪[E]) (η g) (he g)

end
end Dubon2026

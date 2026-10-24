import Dubon2026.SourceCurveDecompositionResidueCharacter
import Dubon2026.SourceCurveWildDifferentCriterion
import Dubon2026.SourceCurveGaloisPlaceCenter

/-! The actual decomposition action and actual residue-unit character
consume the conditional local wild different criterion. Only the fixed-field
order gap, cardinality/order identity and nonzero base differential remain
as geometric inputs. This removes the separate action/character/displacement
certificates on the DUB-17/18 wild genus chain. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential IntermediateField
variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]
variable (v : Place K M)

/-- The actual decomposition automorphisms, restricted to the constant field. -/
def decompositionConstantAction :
    v.toValuationSubring.decompositionSubgroup F →* (M ≃ₐ[K] M) where
  toFun σ := (σ : M ≃ₐ[F] M).restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

theorem decompositionConstantAction_uniformizer_order
    (σ : v.toValuationSubring.decompositionSubgroup F) :
    v.ord (v.decompositionConstantAction σ v.uniformizer) = 1 := by
  have he := (v.mem_decomposition_iff_comapEquiv_eq (σ : M ≃ₐ[F] M)).mp σ.property
  change v.ord ((σ : M ≃ₐ[F] M).restrictScalars K v.uniformizer) = 1
  rw [← v.ord_comapEquiv, he, v.ord_uniformizer]

theorem algebraMap_mem_decomposition_fixedField (x : F) :
    algebraMap F M x ∈ fixedField (v.decompositionConstantAction (F := F)).range := by
  rw [mem_fixedField_iff]
  rintro _ ⟨σ, rfl⟩
  exact (σ : M ≃ₐ[F] M).commutes x

variable [IsAlgClosed K] [FiniteDimensional F M]
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField] [v.DCoordGenerates] [Nontrivial Ω[M⁄K]]

theorem wild_different_bound_of_decomposition_order_gap
    (p : ℕ) [Fact p.Prime] [CharP K p] (x : F)
    [FiniteDimensional K⟮algebraMap F M x⟯ M]
    (hx : v.ord (algebraMap F M x) =
      (Nat.card (v.toValuationSubring.decompositionSubgroup F) : ℤ))
    (hgap : ∀ z ∈ fixedField (v.decompositionConstantAction (F := F)).range,
      v.ord (algebraMap F M x) ∣ v.ord z)
    (hDx : v.coordinateDerivation (algebraMap F M x) ≠ 0)
    (a : ℕ) (ha : p ^ a ∣ Nat.card (v.toValuationSubring.decompositionSubgroup F)) :
    v.ord (algebraMap F M x) - 1 + ((p : ℤ) ^ a - 1) ≤
      v.ordDifferential (D K M (algebraMap F M x)) := by
  classical
  letI : Fintype (v.toValuationSubring.decompositionSubgroup F) := Fintype.ofFinite _
  obtain ⟨χ, hχ⟩ := exists_decomposition_residue_character (F := F) (algebraMap F M x) v
  exact v.wild_different_bound_of_inertia_data p (v.decompositionConstantAction (F := F)) χ
    v.decompositionConstantAction_uniformizer_order (algebraMap F M x)
    (v.algebraMap_mem_decomposition_fixedField x) hx hgap
    (place_residue_bijective_of_finite_coordinate (algebraMap F M x) v).2 hDx hχ a ha

end
end Dubon2026.SourceCurve.Place

import Dubon2026.SourceCurveGaloisParameterOrder

/-! The actual Galois parameter consumer now derives the fixed-field
order gap and cardinality/order identity as well as its inertia character.
The nonzero base differential and local differential instances remain
explicit inputs. Their derivation on the actual auxiliary field is the
last local geometric step before the DUB-17/18 strong wild order bounds. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential IntermediateField
variable {K F M : Type*} [Field K] [IsAlgClosed K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]
variable [FiniteDimensional F M] [IsGalois F M] (v : Place K M)
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField] [v.DCoordGenerates] [Nontrivial Ω[M⁄K]]

theorem wild_different_bound_of_galois_parameter
    (p : ℕ) [Fact p.Prime] [CharP K p] (x : F)
    [FiniteDimensional K⟮algebraMap F M x⟯ M]
    (hx : (v.restrict F).ord x = 1)
    (hDx : v.coordinateDerivation (algebraMap F M x) ≠ 0)
    (a : ℕ) (ha : (p : ℤ) ^ a ∣ v.ord (algebraMap F M x)) :
    v.ord (algebraMap F M x) - 1 + ((p : ℤ) ^ a - 1) ≤
      v.ordDifferential (D K M (algebraMap F M x)) := by
  have htop := place_residue_bijective_of_finite_coordinate (algebraMap F M x) v
  have he := v.galois_parameter_order_eq_decomposition_card htop hx
  have hgap : ∀ z ∈ fixedField (v.decompositionConstantAction (F := F)).range,
      v.ord (algebraMap F M x) ∣ v.ord z := by
    intro z hz
    rw [he]
    exact v.decomposition_fixedField_order_dvd htop hz
  have hpa : p ^ a ∣ Nat.card (v.toValuationSubring.decompositionSubgroup F) := by
    rw [he] at ha
    exact_mod_cast ha
  exact v.wild_different_bound_of_decomposition_order_gap p x he hgap hDx a hpa

end
end Dubon2026.SourceCurve.Place

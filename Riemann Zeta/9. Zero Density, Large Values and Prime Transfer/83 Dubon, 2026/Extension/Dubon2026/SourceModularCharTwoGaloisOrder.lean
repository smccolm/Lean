import Dubon2026.SourceModularCharTwoNormalField
import Dubon2026.SourceNormalFieldCoordinateOrder

/-! DUB-17/18 -> characteristic-two genus/Picard -> wild different bound.
The actual order-twelve inertia sign quotient fixes original modular
embeddings. Existing coordinate fixing-field and normal-place order proofs
provide the finite Galois auxiliary field; full census data is not assumed. -/
namespace Dubon2026.SourceFunctionField
open SourceCurve SourceEllipticDivisionField WeierstrassCurve SourceEllipticCharTwo
open CoefficientPresentation IntermediateField
noncomputable section
attribute [local instance] SourceEllipticCharTwo.charTwoSignSubgroup_normal

theorem exists_char_two_modular_galois_orders_dvd_twelve
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 2] (N : ℕ) (hNK : (N : K) ≠ 0) :
    ∃ M : IntermediateField (RatFunc K) Ω,
      ∃ L : IntermediateField (RatFunc K) M,
        ∃ ι : modularFunctionFieldCoeff N K →ₐ[K] L,
          FiniteDimensional K⟮ι (jCoeff N K)⟯ L ∧
          IsGalois K⟮ι (jCoeff N K)⟯ L ∧
          ∀ v : Place K L, 0 < v.ord (ι (jCoeff N K)) →
            v.ord (ι (jCoeff N K)) ∣ (12 : ℤ) := by
  obtain ⟨M, hfdM, hgalM, L, hfdL, hgalL, ι, hι, w, π, hw, hperm, hfix⟩ :=
    exists_char_two_modular_normal_field K Ω N hNK
  letI := hfdM
  letI := hgalM
  letI := hfdL
  letI := hgalL
  have hc := finite_galois_coordinateField K (M := L)
  refine ⟨M, L, ι, ?_, ?_, ?_⟩
  · rw [hι]
    exact hc.1
  · rw [hι]
    exact hc.2
  · intro v hv
    rw [hι] at hv ⊢
    have hd := Place.normal_coordinate_order_dvd_of_inertia_kernel L w hw π hfix v hv
    simpa only [hperm, Nat.cast_ofNat] using hd

end
end Dubon2026.SourceFunctionField

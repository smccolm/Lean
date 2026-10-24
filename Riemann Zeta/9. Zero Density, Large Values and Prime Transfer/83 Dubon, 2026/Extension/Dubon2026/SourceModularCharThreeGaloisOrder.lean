import Dubon2026.SourceModularCharThreeNormalField
import Dubon2026.SourceNormalFieldCoordinateOrder

/-! The actual characteristic-three modular coefficient field embeds in
a finite Galois extension of its original j-coordinate field whose every
positive j order divides six. All field, place, inertia and embedding
inputs are constructed. This discharges the exact auxiliary-field
obligation for the DUB-17/18 wild different bound at j-order six; the
different bound, exceptional census and genus comparison remain required. -/
namespace Dubon2026.SourceFunctionField
open SourceCurve SourceEllipticDivisionField
open CoefficientPresentation IntermediateField
noncomputable section

theorem exists_char_three_modular_galois_orders_dvd_six
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 3] (N : ℕ) (hNK : (N : K) ≠ 0) :
    ∃ M : IntermediateField (RatFunc K) Ω,
      ∃ L : IntermediateField (RatFunc K) M,
        ∃ ι : modularFunctionFieldCoeff N K →ₐ[K] L,
          FiniteDimensional K⟮ι (jCoeff N K)⟯ L ∧
          IsGalois K⟮ι (jCoeff N K)⟯ L ∧
          ∀ v : Place K L, 0 < v.ord (ι (jCoeff N K)) →
            v.ord (ι (jCoeff N K)) ∣ (6 : ℤ) := by
  obtain ⟨M, hfdM, hgalM, L, hfdL, hgalL, ι, hι, w, π, hw, hperm, hfix⟩ :=
    exists_char_three_modular_normal_field K Ω N hNK
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

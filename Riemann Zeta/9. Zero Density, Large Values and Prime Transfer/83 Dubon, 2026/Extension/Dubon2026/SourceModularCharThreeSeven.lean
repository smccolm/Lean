import Dubon2026.SourceModularCharThreeStrongDifferent

/-! The actual characteristic-three modular order-six/seven theorem.
The finite Galois field, modular embedding and all positive order bounds
are constructed; no auxiliary geometric premises remain. This is a
required local contribution to the DUB-17/18 wild genus comparison.
The exceptional-fiber census and genus assembly remain separate. -/
namespace Dubon2026.SourceFunctionField
open SourceCurve SourceEllipticDivisionField KaehlerDifferential
open CoefficientPresentation IntermediateField
noncomputable section

theorem coeff_place_seven_le_D_j_of_char_three_with_closure
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 3] (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (v : Place K (modularFunctionFieldCoeff N K)) (hv : v.ord (jCoeff N K) = 6) :
    7 ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  obtain ⟨M, hfdM, hgalM, L, hfdL, hgalL, ι, hι, u, π, hu, hperm, hfix⟩ :=
    exists_char_three_modular_normal_field K Ω N hNK
  letI := hfdM
  letI := hgalM
  letI := hfdL
  letI := hgalL
  apply coeff_place_seven_le_D_j_of_char_three_auxiliary K L N ι hι _ v hv
  intro w hw
  simpa only [hperm, Nat.cast_ofNat] using
    Place.normal_coordinate_order_dvd_of_inertia_kernel L u hu π hfix w hw

theorem coeff_place_seven_le_D_j_of_char_three
    (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
    [CharP K 3] (hNK : (N : K) ≠ 0)
    (v : Place K (modularFunctionFieldCoeff N K)) (hv : v.ord (jCoeff N K) = 6) :
    7 ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  classical
  exact coeff_place_seven_le_D_j_of_char_three_with_closure K
    (AlgebraicClosure (RatFunc K)) N hNK v hv

end
end Dubon2026.SourceFunctionField

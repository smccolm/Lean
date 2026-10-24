import Dubon2026.SourceModularCharTwoStrongDifferent

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> wild local bound.
At modular j-order twelve, the constructed auxiliary normal field forces
ramification index one. The existing all-characteristic wild bound at
2^2 gives 12 - 1 + (4 - 1) = 14, which descends for the actual differential.
The weighted census and genus comparison remain separate obligations. -/
namespace Dubon2026.SourceFunctionField
open SourceCurve SourceEllipticDivisionField KaehlerDifferential
open CoefficientPresentation IntermediateField
noncomputable section
attribute [local instance] SourceEllipticCharTwo.charTwoSignSubgroup_normal

theorem coeff_place_fourteen_le_D_j_of_char_two_with_closure
    (K Ω : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [Algebra (RatFunc K) Ω] [Algebra K Ω] [IsScalarTower K (RatFunc K) Ω]
    [Algebra.IsAlgebraic (RatFunc K) Ω] [DecidableEq (RatFunc K)]
    [CharP K 2] (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (v : Place K (modularFunctionFieldCoeff N K)) (hv : v.ord (jCoeff N K) = 12) :
    14 ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  obtain ⟨M, hfdM, hgalM, L, hfdL, hgalL, ι, hι, u, π, hu, hperm, hfix⟩ :=
    exists_char_two_modular_normal_field K Ω N hNK
  letI := hfdM
  letI := hgalM
  letI := hfdL
  letI := hgalL
  apply coeff_place_fourteen_le_D_j_of_char_two_auxiliary K L N ι hι _ v hv
  intro w hw
  simpa only [hperm, Nat.cast_ofNat] using
    Place.normal_coordinate_order_dvd_of_inertia_kernel L u hu π hfix w hw

theorem coeff_place_fourteen_le_D_j_of_char_two
    (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
    [CharP K 2] (hNK : (N : K) ≠ 0)
    (v : Place K (modularFunctionFieldCoeff N K)) (hv : v.ord (jCoeff N K) = 12) :
    14 ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  classical
  exact coeff_place_fourteen_le_D_j_of_char_two_with_closure K
    (AlgebraicClosure (RatFunc K)) N hNK v hv

end
end Dubon2026.SourceFunctionField

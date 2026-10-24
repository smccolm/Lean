import Dubon2026.SourceModularExceptionalFiberCountsFive
import Dubon2026.SourceModularCoefficientTameGenusCriterion

/-! DUB-17/18 -> modular good reduction -> reverse genus. The two
exceptional-fiber counts are derived on the actual coefficient field,
and finite divisor support supplies the finite census required by the
existing Hurwitz criterion. The auxiliary algebraic closure is chosen
internally. Wild characteristics and the remaining good-reduction
comparison are separate obligations. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve SourceLevelProjective SourceEllipticExceptional

theorem coeff_genus_lower_of_five_le (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K]
    (p : ℕ) [CharP K p] (hp : 5 ≤ p) (hNK : (N : K) ≠ 0) :
    genusFormula N ≤ (genusFF K (modularFunctionFieldCoeff N K) : ℚ) := by
  classical
  let Ω := AlgebraicClosure (RatFunc K)
  have hf₀ : {v : Place K (modularFunctionFieldCoeff N K) |
      0 < v.ord (jCoeff N K)}.Finite :=
    (finite_coeff_divisor_support N K (jCoeff N K)).subset fun _ hv => ne_of_gt hv
  have hf₁ : {v : Place K (modularFunctionFieldCoeff N K) |
      0 < v.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) 1728)}.Finite :=
    (finite_coeff_divisor_support N K
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) 1728)).subset
        fun _ hv => ne_of_gt hv
  obtain ⟨h2, h3⟩ := SourceEllipticReduction.isUnit_two_three_of_five_le K K p hp
  have h1728 : (1728 : K) ≠ 0 := by
    have he : (1728 : K) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ h2.ne_zero) (pow_ne_zero _ h3.ne_zero)
  apply coeff_genus_lower_of_exceptional_fiber_counts N K hNK h1728
    hf₀.toFinset hf₁.toFinset (fun v => hf₀.mem_toFinset) (fun v => hf₁.mem_toFinset)
  · have he := (Set.ncard_eq_toFinset_card _ hf₀).symm.trans (Nat.card_coe_set_eq _).symm
    rw [he]
    exact cubic_modular_place_fiber_count K Ω p hp N hNK
  · have he := (Set.ncard_eq_toFinset_card _ hf₁).symm.trans (Nat.card_coe_set_eq _).symm
    rw [he]
    exact quartic_modular_place_fiber_count K Ω p hp N hNK

end
end Dubon2026.SourceFunctionField

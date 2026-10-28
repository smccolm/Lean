import Dubon2026.SourceGammaOneArithmeticDiamondGenerators

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond Galois compatibility. The proved fixed-generator identities and
literal field-generation induction establish commutation of the actual
arithmetic diamond with every original Qbar coefficient automorphism.
No rationality, Galois-equivariance or complex-extension premise remains.
The induced place, Picard and Tate consumers remain to be assembled.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (M : ℕ) [NeZero M] (g : Gamma0 M) (σ : Qbar ≃ₐ[ℚ] Qbar)
local notation "FQ" => functionFieldOver (Gamma1 M) Qbar

theorem arithmeticDiamondHom_arithmetic (x : FQ) :
    arithmeticRingAut (Gamma1 M) σ (arithmeticDiamondHom M g x) =
      arithmeticDiamondHom M g (arithmeticRingAut (Gamma1 M) σ x) := by
  have hm {y : LaurentSeries Qbar} (hy : y ∈ qExpFunctionFieldC Qbar (Gamma1 M)) : y ∈ FQ := by
    rwa [functionFieldOver_eq_qExpFunctionFieldC]
  have H (y : LaurentSeries Qbar) (hy : y ∈ qExpFunctionFieldC Qbar (Gamma1 M)) :
      ∀ hz : y ∈ FQ,
        arithmeticRingAut (Gamma1 M) σ (arithmeticDiamondHom M g ⟨y, hz⟩) =
          arithmeticDiamondHom M g (arithmeticRingAut (Gamma1 M) σ ⟨y, hz⟩) := by
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy =>
        intro hz
        obtain ⟨h1, h2⟩ := arithmeticDiamond_generator_fixed M g σ ⟨y, hz⟩ hy
        rw [h1, h2]
    | algebraMap c =>
        intro hz
        change arithmeticRingAut (Gamma1 M) σ (arithmeticDiamondHom M g (algebraMap Qbar FQ c)) =
          arithmeticDiamondHom M g (arithmeticRingAut (Gamma1 M) σ (algebraMap Qbar FQ c))
        rw [arithmeticDiamondHom_constants, arithmeticRingAut_constants, arithmeticDiamondHom_constants]
    | add y z hy hz ihy ihz =>
        intro hsum
        change arithmeticRingAut (Gamma1 M) σ
          (arithmeticDiamondHom M g (⟨y, hm hy⟩ + ⟨z, hm hz⟩)) =
            arithmeticDiamondHom M g (arithmeticRingAut (Gamma1 M) σ (⟨y, hm hy⟩ + ⟨z, hm hz⟩))
        simp only [map_add, ihy (hm hy), ihz (hm hz)]
    | inv y hy ihy =>
        intro hi
        change arithmeticRingAut (Gamma1 M) σ
          (arithmeticDiamondHom M g (⟨y, hm hy⟩ : FQ)⁻¹) =
            arithmeticDiamondHom M g (arithmeticRingAut (Gamma1 M) σ (⟨y, hm hy⟩ : FQ)⁻¹)
        simp only [map_inv₀, ihy (hm hy)]
    | mul y z hy hz ihy ihz =>
        intro hprod
        change arithmeticRingAut (Gamma1 M) σ
          (arithmeticDiamondHom M g (⟨y, hm hy⟩ * ⟨z, hm hz⟩)) =
            arithmeticDiamondHom M g (arithmeticRingAut (Gamma1 M) σ (⟨y, hm hy⟩ * ⟨z, hm hz⟩))
        simp only [map_mul, ihy (hm hy), ihz (hm hz)]
  exact H x (by simpa only [← functionFieldOver_eq_qExpFunctionFieldC] using x.property) x.property

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField

import Dubon2026.SourceGammaOneOffImageValues

/-! DUB17/18 -> actual Gamma1 torsion surjectivity -> support descent.
Translations of a nonarithmetic j value give infinitely many distinct
actual places. The existing unique-coordinate-value theorem proves
distinctness directly, without an additional evaluation-map construction. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "FC" => functionFieldOver (Gamma1 N) ℂ

theorem translation_orbit_injective (τ : ℂ ≃ₐ[ℚ] ℂ) (W : Place ℂ FC) (t : ℂ)
    (ht : 0 < W.ord (jCoordinateOver (Gamma1 N) ℂ - algebraMap ℂ FC t))
    (hτ : ∀ k : ℕ, (τ ^ k) t = t + k) :
    Function.Injective (fun k : ℕ => arithmeticPlace (Gamma1 N) (τ ^ k) W) := by
  intro i j hij
  dsimp only at hij
  have hi := j_value_arithmetic_pos N (τ ^ i) W ht
  have hj := j_value_arithmetic_pos N (τ ^ j) W ht
  rw [hij, hτ i] at hi
  rw [hτ j] at hj
  let V := arithmeticPlace (Gamma1 N) (τ ^ j) W
  have hm : jCoordinateOver (Gamma1 N) ℂ ∈ V.toValuationSubring := by
    simpa only [sub_add_cancel] using
      add_mem (V.mem_of_ord_nonneg hj.le) (V.algebraMap_mem' (t + j))
  obtain ⟨c, _, huniq⟩ := V.exists_unique_coordinate_value
    (gamma1_place_residue_bijective ℂ N V).surjective
    (transcendental_jCoordinateOver (Gamma1 N) ℂ) hm
  have he : t + (i : ℂ) = t + j := (huniq _ hi).trans (huniq _ hj).symm
  exact_mod_cast add_left_cancel he

omit [NeZero N] in
theorem divisor_pow_fixed (τ : ℂ ≃ₐ[ℚ] ℂ) (A : Divisor ℂ FC)
    (hA : arithmeticDivisorEquiv (Gamma1 N) τ A = A) (k : ℕ) :
    arithmeticDivisorEquiv (Gamma1 N) (τ ^ k) A = A := by
  induction k with
  | zero => rw [pow_zero, arithmeticDivisor_one]
  | succ k ih => rw [pow_succ', arithmeticDivisor_mul, ih, hA]

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField

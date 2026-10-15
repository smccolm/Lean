import Dubon2026.OriginalUnramifiedCyclotomicPowerRoots
import Dubon2026.OriginalCyclotomicPrimeStage

/-! # Arbitrarily large prime-power degrees inside the unchanged arithmetic union

Existing primitive cyclotomic roots and the pinned exact rational degree
formula give actual finite Galois stages of every required prime-power
divisibility. This supplies the arithmetic degree input for the selected
coefficient prime in the restricted-support P-class formation serving
DUB-17. Degree-two invariant maps and their primary surjectivity are not
asserted here.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (Ω : Type) [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The original arithmetic union carries its original rational subfield algebra. -/
local instance primePowerDegreeUnionAlgebra : Algebra ℚ
    (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

include hqa

/-- The unchanged original arithmetic union contains an actual cyclotomic finite Galois stage with the exact prime-power conductor degree. -/
theorem rationalArithmetic_exists_cyclotomic_degree (n : ℕ) :
    ∃ F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
      Module.finrank ℚ F = q ^ n * (q - 1) := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hRoot := originalQUnramifiedUnion_exists_powerRoot (Ω := Ω) a q (n + 1) hqa
  obtain ⟨ζ, hζ⟩ := hRoot
  let F := originalPrimitiveRootStage ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) hζ
  letI : Algebra ℚ F := F.algebra'
  have hF : IsCyclotomicExtension {q ^ (n + 1)} ℚ F :=
    originalPrimitiveRootStage_isCyclotomic ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) hζ
  letI := hF
  refine ⟨F, ?_⟩
  exact (IsCyclotomicExtension.finrank F
    (Polynomial.cyclotomic.irreducible_rat (pow_pos (Fact.out : q.Prime).pos _))).trans
      (Nat.totient_prime_pow_succ (Fact.out : q.Prime) n)

/-- Every power of the selected prime divides the degree of an actual finite Galois stage at the original exceptional support. -/
theorem rationalArithmetic_exists_primePower_degree_dvd (n : ℕ) :
    ∃ F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
      q ^ n ∣ Module.finrank ℚ F := by
  obtain ⟨F, hF⟩ := rationalArithmetic_exists_cyclotomic_degree Ω a q hqa n
  exact ⟨F, hF ▸ dvd_mul_right (q ^ n) (q - 1)⟩

end
end Dubon2026

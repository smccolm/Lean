import Dubon2026.UnramifiedUnionOpenSubgroupCharacters
import Dubon2026.ContinuousRepresentationFiniteQuotient

/-! # Prime-character finiteness for the original arithmetic residual kernel -/

namespace Dubon2026

noncomputable section
open Matrix
open scoped NumberField

variable {Ω ι R : Type*} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]
  [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

/-- The actual kernel of an original continuous arithmetic matrix representation has finitely many continuous prime-order characters. Its openness is derived from the original discrete matrix entries, and its character finiteness is derived for the constructed arithmetic union. -/
theorem originalArithmeticMatrixKernel_prime_characters_finite
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hpa : (p : 𝓞 ℚ) ∣ a) :
    (let U := originalUnramifiedGaloisUnion (Ω := Ω) a
     letI : Algebra ℚ U := U.algebra'
     ∀ (ρ : Gal(U/ℚ) →* GeneralLinearGroup ι R), Continuous ρ →
       Finite (ρ.ker →ₜ* Multiplicative (ZMod p))) := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : Algebra ℚ U := U.algebra'
  dsimp only
  intro ρ hρ
  exact originalQUnramifiedUnion_openSubgroup_prime_characters_finite a ha p hp hpa
    (continuousMatrixRepresentationKernel ρ hρ).toOpenSubgroup

end
end Dubon2026

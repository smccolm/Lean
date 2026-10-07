import Dubon2026.PrincipalPrimeFactors
import Dubon2026.PrincipalRescaledCoefficients

/-! # The actual lower-triangular factors of the principal congruence quotient -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal

/-- The genuine lower-triangular determinant-one subgroup over any commutative ring. -/
def sl2LowerTriangular (R : Type*) [CommRing R] : Subgroup SL(2, R) where
  carrier := {g | g 0 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (a * b) 0 1 = 0
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [ha, hb, mul_zero, zero_mul, add_zero]
  inv_mem' := by
    intro a ha
    change a⁻¹ 0 1 = 0
    rw [SL2_inv_expl]
    simpa using congrArg Neg.neg ha

/-- Being lower triangular is exactly being lower triangular in every actual prime-power factor. -/
theorem sl2PrimeFactors_lower_iff (N : ℕ) [NeZero N] (g : SL(2, ZMod N)) :
    (∀ p : N.primeFactors, sl2PrimeFactorsEquiv N g p ∈
      sl2LowerTriangular (ZMod (p.val ^ N.factorization p.val))) ↔
        g ∈ sl2LowerTriangular (ZMod N) := by
  change (∀ p : N.primeFactors, ZMod.equivPi N (NeZero.ne N) (g 0 1) p = 0) ↔ g 0 1 = 0
  constructor
  · intro h
    apply (ZMod.equivPi N (NeZero.ne N)).injective
    rw [map_zero]
    funext p
    exact h p
  · intro h p
    rw [h, map_zero]
    rfl

/-- The actual integral upper congruence group is precisely the preimage of all local lower groups. -/
theorem principalPrimeFactors_upper_iff (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    (∀ p : N.primeFactors, principalPrimeFactorsEquiv N (QuotientGroup.mk γ) p ∈
      sl2LowerTriangular (ZMod (p.val ^ N.factorization p.val))) ↔ γ ∈ GammaUpper N := by
  exact sl2PrimeFactors_lower_iff N (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ)

/-- Every element of one actual local lower-triangular factor has an integral upper-congruence lift. -/
theorem principalPrimeFactor_lower_lift (N : ℕ) [NeZero N] (p : N.primeFactors)
    (g : sl2LowerTriangular (ZMod (p.val ^ N.factorization p.val))) :
    ∃ γ : SL(2, ℤ), γ ∈ GammaUpper N ∧
      QuotientGroup.mk γ = principalPrimeFactorEmbedding N p g.val := by
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_surjective (principalPrimeFactorEmbedding N p g.val)
  refine ⟨γ, (principalPrimeFactors_upper_iff N γ).mp ?_, hγ⟩
  intro q
  rw [hγ, principalPrimeFactorEmbedding_components]
  by_cases hpq : p = q
  · subst q
    simp
  · simp [Pi.mulSingle_eq_of_ne (Ne.symm hpq)]

/-- The genuine rescaled source form is fixed by every single local lower-triangular group. -/
theorem cuspRescaledPrincipal_local_lower_fixed (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (p : N.primeFactors)
    (g : sl2LowerTriangular (ZMod (p.val ^ N.factorization p.val))) :
    principalCuspRepresentation N k (principalPrimeFactorEmbedding N p g.val)
      (cuspRescaledPrincipal N k f) = cuspRescaledPrincipal N k f := by
  obtain ⟨γ, hγ, hrep⟩ := principalPrimeFactor_lower_lift N p g
  rw [← hrep]
  exact cuspRescaledPrincipal_upper_fixed N k f γ hγ

end
end Dubon2026

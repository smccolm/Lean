import Dubon2026.PrincipalCommonInvariant
import Dubon2026.PrincipalCoprimeProjection

/-! # Actual coprime Fourier projection on the finite slash orbit -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal
attribute [local instance] primeFactorBaseNeZero primeFactorLevelNeZero primeFactorLowerFintype

/-- The actual divisor projector attached to one prime factor of the level. -/
def principalOrbitPrimeProjection (N : ℕ) (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p : N.primeFactors) :
    principalCuspOrbit N k f →ₗ[ℂ] principalCuspOrbit N k f :=
  principalOrbitDivisorProjection (Nat.dvd_of_mem_primeFactors p.property) k f

/-- The actual prime projection complements commute on the genuine orbit. -/
theorem principalOrbitPrimeComplement_commute (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p q : N.primeFactors) :
    Commute (1 - principalOrbitPrimeProjection N k f p) (1 - principalOrbitPrimeProjection N k f q) :=
  (Commute.one_left _).sub_left ((Commute.one_right _).sub_right
    (principalOrbitDivisorProjection_commute _ _ k f))

/-- The literal finite product of prime Fourier projection complements, restricted to the actual orbit. -/
def principalOrbitAvoidProjection (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (s : Finset N.primeFactors) :
    principalCuspOrbit N k f →ₗ[ℂ] principalCuspOrbit N k f :=
  s.noncommProd (fun p => 1 - principalOrbitPrimeProjection N k f p)
    (fun p _ q _ _ => principalOrbitPrimeComplement_commute N k f p q)

/-- A genuine orbit complement erases exactly the divisible Fourier indices. -/
theorem principalOrbitPrimeComplement_coeff (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p : N.primeFactors)
    (v : principalCuspOrbit N k f) (n : ℕ) :
    principalCuspCoefficients ((1 - principalOrbitPrimeProjection N k f p) v).val n =
      if p.val ∣ n then 0 else principalCuspCoefficients v.val n := by
  change principalCuspCoefficientLinear N k n
    (v.val - (principalOrbitPrimeProjection N k f p v).val) = _
  rw [map_sub]
  change principalCuspCoefficients v.val n - principalCuspCoefficients
    (principalOrbitDivisorProjection (Nat.dvd_of_mem_primeFactors p.property) k f v).val n = _
  rw [principalOrbitDivisorProjection_coeff]
  split_ifs <;> simp

/-- Every coefficient of the actual finite orbit product is determined by its prime support. -/
theorem principalOrbitAvoidProjection_coeff (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (s : Finset N.primeFactors)
    (v : principalCuspOrbit N k f) (n : ℕ) :
    principalCuspCoefficients (principalOrbitAvoidProjection N k f s v).val n =
      if ∀ p ∈ s, ¬p.val ∣ n then principalCuspCoefficients v.val n else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [principalOrbitAvoidProjection]
  | insert p s hp ih =>
    unfold principalOrbitAvoidProjection
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hp, Module.End.mul_apply,
      principalOrbitPrimeComplement_coeff]
    change (if p.val ∣ n then 0 else principalCuspCoefficients
      (principalOrbitAvoidProjection N k f s v).val n) = _
    rw [ih]
    by_cases hpn : p.val ∣ n <;> simp [hpn]

/-- Vanishing of the actual coprime coefficients annihilates the entire orbit complement product. -/
theorem principalOrbitAvoidProjection_eq_zero (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (v : principalCuspOrbit N k f)
    (hv : ∀ n, N.Coprime n → principalCuspCoefficients v.val n = 0) :
    principalOrbitAvoidProjection N k f Finset.univ v = 0 := by
  apply Subtype.ext
  apply principalCuspCoefficients_injective N k
  funext n
  rw [principalOrbitAvoidProjection_coeff]
  have hc : (∀ p : N.primeFactors, ¬p.val ∣ n) ↔ N.Coprime n := by
    simpa only [Subtype.forall] using forall_primeFactors_not_dvd_iff N n
  simp only [Finset.mem_univ, forall_const, hc]
  change (if N.Coprime n then principalCuspCoefficients v.val n else 0) =
    principalCuspCoefficientLinear N k n 0
  rw [map_zero]
  by_cases hn : N.Coprime n
  · simpa only [if_pos hn] using hv n hn
  · exact if_neg hn

end
end Dubon2026

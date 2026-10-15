import Dubon2026.RationalPrimeCyclotomicReciprocityRationalUnitAction

/-! # Ramified rational-unit cancellation on the cyclotomic root

The arbitrary rational-unit theorem produces a positive quotient `a / c`
with inverse exponent `b * c`.  Its forward exponent is `a * d`, where `d`
is the inverse of `c`.  The two modular inverse identities show that applying
the ramified action and then the forward quotient action fixes the actual
primitive root.  This is the finite cyclic cancellation needed to assemble
the ramified, away-prime, and real-sign factors in DUB-17's cyclotomic
principal product.
-/

namespace Dubon2026
noncomputable section

open IsDedekindDomain HeightOneSpectrum Metric
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- Every rational unit admits one actual cyclotomic stage on which its
ramified reciprocity action is cancelled by the forward exponent of the
constructed positive quotient. -/
theorem rationalPrimeRationalUnit_exists_reciprocity_root_cancellation
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (q : ℚˣ) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    ∃ (a c : ℕ), 0 < a ∧ 0 < c ∧ ¬p ∣ c ∧
      ∃ ha : ¬p ∣ a, ∃ u : 𝒪[K]ˣ, ∃ hu : u.val = a, ∃ b d : ℕ,
        a.Coprime (p ^ (n + 1)) ∧ b.Coprime (p ^ (n + 1)) ∧
        c.Coprime (p ^ (n + 1)) ∧ d.Coprime (p ^ (n + 1)) ∧
        a * b ≡ 1 [MOD p ^ (n + 1)] ∧
        c * d ≡ 1 [MOD p ^ (n + 1)] ∧
        let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
        letI : IsCyclic Gal(L/K) :=
          rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
        let ζ := rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeRationalUnit p hp q))).toMul ζ = ζ ^ (b * c) ∧
        ((localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeRationalUnit p hp q))).toMul ζ) ^ (a * d) = ζ := by
  dsimp only
  obtain ⟨a, c, ha0, hc0, hc, ha, u, hu, b, d,
      hca, hcb, hcc, hcd, hab, hcdinv, haction⟩ :=
    rationalPrimeRationalUnit_exists_reciprocity_root_action p hp hp2 n q
  refine ⟨a, c, ha0, hc0, hc, ha, u, hu, b, d,
    hca, hcb, hcc, hcd, hab, hcdinv, haction, ?_⟩
  rw [haction, ← pow_mul]
  let ζ := rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha
  have hζ := rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp n a u hu ha
  have hm : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hmod : (b * c) * (a * d) ≡ 1 [MOD p ^ (n + 1)] := by
    simpa only [one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using
      hab.mul hcdinv
  calc
    ζ ^ ((b * c) * (a * d)) = ζ ^ 1 :=
      (hζ.isOfFinOrder hm).pow_eq_pow_iff_modEq.mpr (by
        simpa only [hζ.eq_orderOf] using hmod)
    _ = ζ := pow_one ζ

end
end Dubon2026

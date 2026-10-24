import Dubon2026.SourceCyclicQuotientPrimeArithmetic
import Dubon2026.SourceEllipticPrimeImageBaseChange

/-! The actual composite cyclic quotient, formed by successive least-prime
quotients of the original finite cyclic subgroup and its actual images.
Each target is the intrinsic Velu model and each image uses the specific
degree-two coordinate map or odd ideal norm. Native strong recursion on
the order suffices; behavior on infinite subgroups is unnecessary.
This constructs the object for the all-level polynomial and inertia census
on DUB-17/18. Those conclusions are not asserted by this construction. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticCyclicCount
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- The actual next kernel is the least-prime torsion in the original cyclic subgroup. -/
def cyclicQuotientLeastKernel (W : WeierstrassCurve F) (N : ℕ)
    (hN : (N : F) ≠ 0) (hN1 : N ≠ 1)
    (H : AddSubgroup W.toAffine.Point) (hcyc : IsAddCyclic H) (hcard : Nat.card H = N) :
    {C : AddSubgroup W.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N.minFac} :=
  ⟨cyclicPrimeKernel H N.minFac,
    cyclicPrimeKernel_cyclic_card H hcyc (Nat.minFac_prime hN1).ne_zero
      (cyclicQuotient_prime_arithmetic N hN hN1).2.1
      (hcard.trans (Nat.mul_div_cancel' (Nat.minFac_dvd N)).symm)⟩

/-- The actual elliptic quotient model obtained by all successive canonical prime steps. -/
def cyclicQuotientCurve (N : ℕ) (hN : (N : F) ≠ 0)
    (W : WeierstrassCurve F) [W.IsElliptic]
    (H : AddSubgroup W.toAffine.Point) (hcyc : IsAddCyclic H) (hcard : Nat.card H = N) :
    {V : WeierstrassCurve F // V.IsElliptic} := by
  by_cases hN1 : N = 1
  · exact ⟨W, inferInstance⟩
  · have ha := cyclicQuotient_prime_arithmetic N hN hN1
    letI : Fact N.minFac.Prime := ⟨ha.1⟩
    let C := cyclicQuotientLeastKernel W N hN hN1 H hcyc hcard
    let V := primeAbscissaQuotient W N.minFac C
    letI : V.IsElliptic := primeAbscissaQuotient_isElliptic W N.minFac ha.2.2.2.1 C
    let φ := primeAbscissaHom W N.minFac ha.2.2.2.1 C
    have hs := canonical_cyclic_prime_step W N.minFac (N / N.minFac) ha.2.2.2.1 ha.2.1
      H hcyc (hcard.trans (Nat.mul_div_cancel' (Nat.minFac_dvd N)).symm)
    exact cyclicQuotientCurve (N / N.minFac) ha.2.2.2.2 V (H.map φ) hs.2.2.1 hs.2.2.2.1
termination_by N
decreasing_by exact (cyclicQuotient_prime_arithmetic N hN hN1).2.2.1

/-- Quotienting by the order-one subgroup leaves the literal original curve. -/
theorem cyclicQuotientCurve_one (W : WeierstrassCurve F) [W.IsElliptic]
    (H : AddSubgroup W.toAffine.Point) (hcyc : IsAddCyclic H) (hcard : Nat.card H = 1) :
    (cyclicQuotientCurve (F := F) 1 (by simp) W H hcyc hcard).1 = W := by
  rw [cyclicQuotientCurve]
  rfl

end
end Dubon2026.SourceEllipticVelu

import Dubon2026.SourceEllipticIntrinsicPrimeProduct

/-! Feed the complete original cyclic-kernel census and intrinsic quotient
curves into the proved integral composition identity. The product-level
fiber divides the product of the remaining-level fibers at these actual
quotient j-values. This is the polynomial input to the all-level generic
cyclic-root bijection on the DUB-17/18 inertia-census dependency chain. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial SourceFunctionField SourceFunctionField.IntegralJCoordinate
noncomputable section

/-- The product-level modular fiber is contained, with multiplicity, in the fibers at all actual prime quotients. -/
theorem exists_prime_quotient_fiber_composition
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] (p M : ℕ) [Fact p.Prime] [NeZero M]
    (hp : (p : K) ≠ 0) :
    ∃ e : Fin (p + 1) ≃ {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p},
      relationAtSeed (modularPolynomial (p * M)) W.j ∣
        ∏ i, letI := primeAbscissaQuotient_isElliptic W p hp (e i)
          relationAtSeed (modularPolynomial M) (primeAbscissaQuotient W p (e i)).j := by
  obtain ⟨e, he⟩ := exists_primeAbscissaQuotientProduct W p hp
  refine ⟨e, ?_⟩
  exact modularPolynomial_fiber_dvd_product p M W.j
    (fun i => letI := primeAbscissaQuotient_isElliptic W p hp (e i)
      (primeAbscissaQuotient W p (e i)).j) he

end
end Dubon2026.SourceEllipticVelu

import Dubon2026.SourceEllipticPrimeAbscissaRoot
import Dubon2026.SourceIntegralFiberComposition

/-! Enumerate all original prime cyclic kernels and express the exact
modular fiber as the product of the intrinsic quotient j-values. Reuse the
proved generator census and both original prime products, preserving
multiplicities even at algebraic and CM fibers. This supplies actual
quotient objects to the all-level composition argument, DUB-17/18. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial SourceEllipticCyclicCount
open SourceFunctionField SourceFunctionField.IntegralJCoordinate OddDiscriminant
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

/-- The complete original prime cyclic kernel census gives the exact intrinsic quotient product. -/
theorem exists_primeAbscissaQuotientProduct (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0) :
    ∃ e : Fin (p + 1) ≃ {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p},
      relationAtSeed (modularPolynomial p) W.j =
        ∏ i, letI := primeAbscissaQuotient_isElliptic W p hp (e i)
          X - C (primeAbscissaQuotient W p (e i)).j := by
  have hh := exists_prime_cyclic_generators (K := K) W p hp
  simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] at hh
  obtain ⟨Q, hQ, hinj, hsurj⟩ := hh
  let k : Fin (p + 1) → {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p} :=
    fun i => ⟨AddSubgroup.zmultiples (Q i),
      (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mpr ⟨Q i, rfl⟩,
      (Nat.card_zmultiples (Q i)).trans (hQ i)⟩
  have hk : Function.Bijective k := by
    refine ⟨fun i j he => hinj (congrArg Subtype.val he), ?_⟩
    intro H
    obtain ⟨i, hi⟩ := hsurj H.1 H.2.1 H.2.2
    exact ⟨i, Subtype.ext hi⟩
  let e := Equiv.ofBijective k hk
  have hke (i) : AddSubgroup.zmultiples (Q i) = (e i).1 := rfl
  have hfactor : relationAtSeed (modularPolynomial p) W.j =
      ∏ i, (X - C (primeCyclicRootMap W p hp (e i)).1) := by
    by_cases hp2 : p = 2
    · subst p
      refine (modularPolynomial_two_eq_pointQuotientProduct W hp Q hQ hinj).trans ?_
      apply Finset.prod_congr rfl
      intro i _
      simp only [primeCyclicRootMap, dite_true]
      rw [twoCyclicRootMap_eq_quotient W hp (e i) (hQ i) (hke i)]
    · have hodd : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1 := by
        intro i
        apply (hQ i).trans
        obtain ⟨m, hm⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
        omega
      refine (modularPolynomial_eq_oddQuotientProduct W p hp2 hp Q hodd hinj).trans ?_
      apply Finset.prod_congr rfl
      intro i _
      simp only [primeCyclicRootMap, dif_neg hp2]
      rw [oddPrimeCyclicRootMap_eq_quotient W p hp2 hp (e i) (hodd i) (hke i)]
  refine ⟨e, hfactor.trans ?_⟩
  apply Finset.prod_congr rfl
  intro i _
  rw [primeAbscissaQuotient_j_eq W p hp (e i)]

end
end Dubon2026.SourceEllipticVelu

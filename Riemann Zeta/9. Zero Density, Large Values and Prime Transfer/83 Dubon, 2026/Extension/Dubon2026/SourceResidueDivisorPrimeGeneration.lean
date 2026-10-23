import Dubon2026.SourceResidueTwoPrimeGeneration
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> mixed-divisor generation. The literal two-prime relation
intersection recovers j_d from j_(d/p) and j_(d/q). Roots of unity are obtained
from the coefficient field and the nonzero residue of d, without a root-of-unity
or common-root input. Adapted from the existing local divisor-generation proof. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem residue_divisor_series_mem_of_two_primes
    (K : Type*) [Field K] [IsAlgClosed K] (d p q : ℕ) [NeZero d]
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) (hdK : (d : K) ≠ 0)
    (hpd : p ∣ d) (hqd : q ∣ d) [NeZero (d / p)] [NeZero (d / q)]
    (F : IntermediateField K (LaurentSeries K))
    (h1 : qExpand K (d / p) (jqModC K) ∈ F) (h2 : qExpand K (d / q) (jqModC K) ∈ F) :
    qExpand K d (jqModC K) ∈ F := by
  obtain ⟨m, hm⟩ := ((Nat.coprime_primes hp.out hq.out).mpr hpq).mul_dvd_of_dvd_of_dvd hpd hqd
  haveI : NeZero m := ⟨fun he => NeZero.ne d (by rw [hm, he, mul_zero])⟩
  have hd : d = m * p * q := by rw [hm]; ring
  have hdivp : d / p = m * q := by
    calc
      d / p = (p * (m * q)) / p := by congr 1; rw [hd]; ring
      _ = m * q := Nat.mul_div_cancel_left _ hp.out.pos
  have hdivq : d / q = m * p := by rw [hd, Nat.mul_div_cancel _ hq.out.pos]
  rw [qExpand_congr hdivp (jqModC K)] at h1
  rw [qExpand_congr hdivq (jqModC K)] at h2
  rw [qExpand_congr hd (jqModC K)]
  haveI : NeZero (p : K) := ⟨ne_zero_of_dvd_ne_zero hdK hpd.natCast⟩
  haveI : NeZero (q : K) := ⟨ne_zero_of_dvd_ne_zero hdK hqd.natCast⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K q
  obtain ⟨ζ, hζval⟩ := hz.isUnit hp.out.ne_zero
  obtain ⟨η, hηval⟩ := hw.isUnit hq.out.ne_zero
  exact residue_two_prime_generation K m p q hpq ζ η
    (hζval.symm ▸ hz) (hηval.symm ▸ hw) F h2 h1

end
end Dubon2026.SourceFunctionField

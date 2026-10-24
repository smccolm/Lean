import Dubon2026.SourceEllipticAbscissaQuotient
import Dubon2026.SourceEllipticOddKernelGeometry

/-! The finite abscissa set is intrinsic to the actual cyclic subgroup.
Identify it with every odd-generator half-orbit using the existing exact
kernel-polynomial geometry. Thus the full quotient curve, not only its j,
is independent of that generator. This is the prime-step coefficient input
for composite cyclic quotients in the DUB-17/18 all-level inertia census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticFunctionField
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- The distinct abscissae of all nonzero points in an actual finite subgroup. -/
def cyclicAbscissae (H : AddSubgroup W.toAffine.Point) [Finite H] : Finset F := by
  classical
  letI := Fintype.ofFinite H
  exact (Finset.univ.filter fun P : H => (P : W.toAffine.Point) ≠ 0).image
    fun P : H => (coordsOrZero (P : W.toAffine.Point)).1

theorem mem_cyclicAbscissae (H : AddSubgroup W.toAffine.Point) [Finite H] (x : F) :
    x ∈ cyclicAbscissae W H ↔
      ∃ P : W.toAffine.Point, P ∈ H ∧ P ≠ 0 ∧ (coordsOrZero P).1 = x := by
  simp only [cyclicAbscissae, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨P, hP, hx⟩
    exact ⟨P, P.2, hP, hx⟩
  · rintro ⟨P, hPH, hP, hx⟩
    exact ⟨⟨P, hPH⟩, hP, hx⟩

/-- Every odd-order generator yields the same intrinsic finite kernel abscissae. -/
theorem cyclicAbscissae_eq_oddOrderSummingSet
    (H : AddSubgroup W.toAffine.Point) [Finite H]
    {P : W.toAffine.Point} {n : ℕ} (hP : addOrderOf P = 2 * n + 1)
    (hPH : AddSubgroup.zmultiples P = H) :
    cyclicAbscissae W H = (oddOrderSummingSet W P n).image Prod.fst := by
  ext x
  rw [mem_cyclicAbscissae, Finset.mem_image]
  constructor
  · rintro ⟨R, hRH, hR, hx⟩
    rcases R with _ | ⟨r, s, hrs⟩
    · exact (hR rfl).elim
    · have hr : Affine.Point.some r s hrs ∈ AddSubgroup.zmultiples P := hPH ▸ hRH
      have hz := (eval_oddKernel_eq_zero_iff_mem_zmultiples W hrs hP).mpr hr
      obtain ⟨Q, hQ, hrQ⟩ := (eval_kernelPolynomial_eq_zero_iff _ r).mp hz
      exact ⟨Q, hQ, hrQ.symm.trans hx⟩
  · rintro ⟨Q, hQ, hx⟩
    obtain ⟨k, hk1, hkn, rfl⟩ := mem_oddOrderSummingSet.mp hQ
    refine ⟨k • P, ?_, ?_, hx⟩
    · rw [← hPH]
      exact (AddSubgroup.zmultiples P).nsmul_mem (AddSubgroup.mem_zmultiples P) k
    · intro hz
      have hd : 2 * n + 1 ∣ k := hP ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
      have := Nat.le_of_dvd (by omega) hd
      omega

/-- The literal quotient curve is the intrinsic subgroup-abscissa quotient. -/
theorem oddQuotient_eq_abscissaQuotient
    (H : AddSubgroup W.toAffine.Point) [Finite H]
    {P : W.toAffine.Point} {n : ℕ} (hP : addOrderOf P = 2 * n + 1)
    (hPH : AddSubgroup.zmultiples P = H) :
    veluQuotient W (oddOrderSummingSet W P n) = abscissaQuotient W (cyclicAbscissae W H) := by
  rw [cyclicAbscissae_eq_oddOrderSummingSet W H hP hPH]
  exact (abscissaQuotient_oddOrderSummingSet W hP).symm

/-- Equal odd cyclic kernels give equal literal quotient curves over the original field. -/
theorem oddQuotient_eq_of_zmultiples_eq
    {P Q : W.toAffine.Point} {n m : ℕ}
    (hP : addOrderOf P = 2 * n + 1) (hQ : addOrderOf Q = 2 * m + 1)
    (hPQ : AddSubgroup.zmultiples P = AddSubgroup.zmultiples Q) :
    veluQuotient W (oddOrderSummingSet W P n) =
      veluQuotient W (oddOrderSummingSet W Q m) := by
  haveI : Finite (AddSubgroup.zmultiples P) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zmultiples, hP]
    omega)
  exact (oddQuotient_eq_abscissaQuotient W _ hP rfl).trans
    (oddQuotient_eq_abscissaQuotient W _ hQ hPQ.symm).symm

end
end Dubon2026.SourceEllipticVelu

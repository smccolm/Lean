import Dubon2026.SourceReductionIntegralPolynomials
import Dubon2026.SourceCurveOrders

/-! DUB-17/18 -> original Frobenius/inertia -> actual good reduction ->
genus comparison -> preservation of pole spaces. A literal monic equation with
coefficient degree bounds forces the same pole-order bound after reduction.
Existing actual-place order criteria and the constructed constant reduction
are reused; no genus or place-map conclusion is assumed. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial

section Generic

variable {S E : Type*} [CommSemiring S] [Field E]

theorem eval₂_mem (T : Subring E) (ρ : S →+* E) (hρ : ∀ a, ρ a ∈ T) {y : E} (hy : y ∈ T)
    (q : S[X]) : q.eval₂ ρ y ∈ T := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [eval₂_add]; exact T.add_mem hp hq
  | monomial n a =>
    rw [eval₂_monomial]
    exact T.mul_mem (hρ a) (T.pow_mem hy n)

theorem mul_mem_of_monic (O : ValuationSubring E) (P : E[X]) (hP : P.Monic) (s x : E)
    (hcoeff : ∀ i, P.coeff i * s ^ (P.natDegree - i) ∈ O) (hx : P.eval x = 0) :
    s * x ∈ O := by
  set Q : E[X] := P.scaleRoots s with hQ
  have hQmonic : Q.Monic := (monic_scaleRoots_iff s).mpr hP
  have hQroot : Q.eval (s * x) = 0 := by
    have h := scaleRoots_eval₂_eq_zero (RingHom.id E) (r := x) (s := s) (p := P) hx
    simpa using h
  have hsub : (↑Q.coeffs : Set E) ⊆ O.toSubring := by
    intro c hc
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp (Finset.mem_coe.mp hc)
    rw [hQ, coeff_scaleRoots]
    exact hcoeff n
  set Q' : (O.toSubring)[X] := Q.toSubring O.toSubring hsub with hQ'
  have hQ'monic : Q'.Monic := (monic_toSubring Q O.toSubring hsub).mpr hQmonic
  have hint : IsIntegral O (s * x) := by
    refine ⟨Q', hQ'monic, ?_⟩
    have hmap : Q'.map (algebraMap O E) = Q := map_toSubring Q O.toSubring hsub
    rw [← hmap, eval_map] at hQroot
    exact hQroot
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := E)).mp hint
  rw [← hy]
  exact y.2

end Generic

section Residue

variable {k Fbar : Type*} [Field k] [Field Fbar] [Algebra k Fbar]
variable {S : Type*} [CommRing S] (ρ : S →+* Fbar) (hρ : ∀ w : Place k Fbar, ∀ a, ρ a ∈ w.toValuationSubring)

include hρ in

theorem mul_min_ord_le_ord (y x : Fbar) (m : ℕ) (p : Polynomial (Polynomial S)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (eval₂RingHom ρ y) x = 0) (w : Place k Fbar) :
    (m : ℤ) * min 0 (w.ord y) ≤ w.ord x := by
  set θ : Polynomial S →+* Fbar := eval₂RingHom ρ y with hθ
  set P : Fbar[X] := p.map θ with hP
  have hPmonic : P.Monic := hp.map θ
  have hPdeg : P.natDegree = p.natDegree := hp.natDegree_map θ
  have hProot : P.eval x = 0 := by rw [hP, eval_map]; exact hroot
  have hPcoeff : ∀ i, P.coeff i = (p.coeff i).eval₂ ρ y := fun i => by
    rw [hP, coeff_map, hθ]; rfl
  set O := w.toValuationSubring with hO
  by_cases hy : y ∈ O
  ·
    have hmin : min 0 (w.ord y) = 0 := min_eq_left (Place.ord_nonneg_of_mem w hy)
    rw [hmin, mul_zero]
    have hxO : (1 : Fbar) * x ∈ O := by
      refine mul_mem_of_monic O P hPmonic 1 x (fun i => ?_) hProot
      rw [one_pow, mul_one, hPcoeff]
      exact eval₂_mem O.toSubring ρ (hρ w) hy _
    rw [one_mul] at hxO
    exact Place.ord_nonneg_of_mem w hxO
  ·
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hordy : w.ord y < 0 := lt_of_not_ge (fun h => hy (w.mem_of_ord_nonneg h))
    have hmin : min 0 (w.ord y) = w.ord y := min_eq_right hordy.le
    rw [hmin]
    set g : Fbar := y⁻¹ with hg
    have hgO : g ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    letI : Invertible y := invertibleOfNonzero hy0
    have hinvOf : (⅟y : Fbar) = g := by rw [hg, invOf_eq_inv]

    have hcoeff : ∀ i, P.coeff i * (g ^ m) ^ (P.natDegree - i) ∈ O := by
      intro i
      rw [hPcoeff, hPdeg, ← pow_mul]
      set N := m * (p.natDegree - i) with hN
      have hqN : (p.coeff i).natDegree ≤ N := by
        rw [hN, mul_comm]; exact hdeg i

      have hrefl := eval₂_reflect_mul_pow ρ y N (p.coeff i) hqN
      rw [hinvOf] at hrefl
      have hkey : (p.coeff i).eval₂ ρ y * g ^ N = (reflect N (p.coeff i)).eval₂ ρ g := by
        rw [← hrefl, mul_assoc, ← mul_pow, hg, mul_inv_cancel₀ hy0, one_pow, mul_one]
      rw [hkey]
      exact eval₂_mem O.toSubring ρ (hρ w) hgO _
    have hxO : g ^ m * x ∈ O := mul_mem_of_monic O P hPmonic (g ^ m) x hcoeff hProot

    rcases eq_or_ne x 0 with rfl | hx0
    · simp only [Place.ord_zero]
      have : (m : ℤ) * w.ord y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg m) hordy.le
      exact this
    · have h0 := Place.ord_nonneg_of_mem w hxO
      have hg0 : g ≠ 0 := inv_ne_zero hy0
      rw [w.ord_mul (pow_ne_zero _ hg0) hx0, ← zpow_natCast, w.ord_zpow, hg, w.ord_inv] at h0
      linarith

end Residue


end
end Dubon2026.SourceCurve.RegularProlongation

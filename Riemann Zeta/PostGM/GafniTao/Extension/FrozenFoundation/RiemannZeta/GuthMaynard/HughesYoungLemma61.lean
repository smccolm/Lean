import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import RiemannZeta.GuthMaynard.HughesYoungLocalFactors

open Complex Finset Filter Nat Topology
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young Lemma 6.1

The equation-(106) Euler product is compared with the untwisted zeta-ratio
Euler product.  Since the two products differ only at primes dividing `hk`,
the correction is an exact finite product.  The subsequent source formula
evaluates those finitely many corrections using equations (109)--(118).
-/

/-- The finite set of prime subtypes dividing a natural number. -/
noncomputable def hughesYoungPrimeFactors (n : ℕ) : Finset Nat.Primes :=
  n.primeFactors.attach.map
    ⟨fun p => ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩,
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun r : Nat.Primes => (r : ℕ)) hpq⟩

@[simp]
theorem mem_hughesYoungPrimeFactors {n : ℕ} {p : Nat.Primes} :
    p ∈ hughesYoungPrimeFactors n ↔ (p : ℕ) ∈ n.primeFactors := by
  constructor
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨q, _hq, hpq⟩
    have hpqVal : q.1 = (p : ℕ) :=
      congrArg (fun r : Nat.Primes => (r : ℕ)) hpq
    exact hpqVal ▸ q.2
  · intro hp
    apply Finset.mem_map.mpr
    refine ⟨⟨(p : ℕ), hp⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

/-- A named Euler factor for the Riemann zeta function.  Naming this factor
keeps the quotient-product convergence proof tractable for Lean's elaborator. -/
noncomputable def hughesYoungZetaEulerFactor
    (s : ℂ) (p : Nat.Primes) : ℂ :=
  (1 - (p : ℂ) ^ (-s))⁻¹

/-- The regular local factor whose product is
`ζ(a+b+c) / ζ(a+b)`. -/
noncomputable def hughesYoungRegularLocalFactor
    (a b c : ℂ) (p : Nat.Primes) : ℂ :=
  hughesYoungZetaEulerFactor (a + b + c) p /
    hughesYoungZetaEulerFactor (a + b) p

/-- The actual equation-(106) Euler factor. -/
noncomputable def hughesYoungActualLocalFactor
    (h k : ℕ) (a b c : ℂ) (p : Nat.Primes) : ℂ :=
  ∑' e : ℕ, hughesYoungEquation106Coefficient h k a b c ((p : ℕ) ^ e)

/-- The finite Euler correction supported on primes dividing `hk`. -/
noncomputable def hughesYoungFiniteEulerCorrection
    (h k : ℕ) (a b c : ℂ) : ℂ :=
  (∏ p ∈ hughesYoungPrimeFactors (h * k),
      hughesYoungActualLocalFactor h k a b c p) /
    ∏ p ∈ hughesYoungPrimeFactors (h * k),
      hughesYoungRegularLocalFactor a b c p

/-- The first finite Euler factor displayed in Hughes--Young Lemma 6.1,
for a prime power exactly dividing `h`. -/
noncomputable def hughesYoungLemma61LeftFactor
    (h : ℕ) (a b c : ℂ) (p : Nat.Primes) : ℂ :=
  ((1 - (p : ℂ) ^ (-b)) *
        (1 - (p : ℂ) ^ (-(a + b + c))) +
      (p : ℂ) ^ (-b) * (1 - (p : ℂ) ^ (-a)) *
        (1 - (p : ℂ) ^ (-c)) *
        ((p : ℂ) ^ (-(b + c))) ^ (h.factorization p)) /
    ((1 - (p : ℂ) ^ (-(b + c))) *
      (1 - (p : ℂ) ^ (-(a + b))))

/-- The second finite Euler factor displayed in Hughes--Young Lemma 6.1,
for a prime power exactly dividing `k`. -/
noncomputable def hughesYoungLemma61RightFactor
    (k : ℕ) (a b c : ℂ) (p : Nat.Primes) : ℂ :=
  ((1 - (p : ℂ) ^ (-a)) *
        (1 - (p : ℂ) ^ (-(a + b + c))) +
      (p : ℂ) ^ (-a) * (1 - (p : ℂ) ^ (-b)) *
        (1 - (p : ℂ) ^ (-c)) *
        ((p : ℂ) ^ (-(a + c))) ^ (k.factorization p)) /
    ((1 - (p : ℂ) ^ (-(a + c))) *
      (1 - (p : ℂ) ^ (-(a + b))))

theorem hughesYoungRegularLocalFactor_ne_zero
    {a b c : ℂ} (hA : 1 < (a + b).re)
    (hC : 0 < c.re) (p : Nat.Primes) :
    hughesYoungRegularLocalFactor a b c p ≠ 0 := by
  have hS : 1 < (a + b + c).re := by
    have hA' : 1 < a.re + b.re := by simpa using hA
    simp only [add_re]
    linarith
  exact div_ne_zero
    (inv_ne_zero (Complex.one_sub_prime_cpow_ne_zero p.prop hS))
    (inv_ne_zero (Complex.one_sub_prime_cpow_ne_zero p.prop hA))

/-- The regular local factors have the zeta-ratio product claimed before
the finite corrections in Hughes--Young equation (97). -/
theorem hughesYoungRegularLocalFactor_hasProd
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    HasProd (hughesYoungRegularLocalFactor a b c)
      (riemannZeta (a + b + c) / riemannZeta (a + b)) := by
  have hS : 1 < (a + b + c).re := by
    have hA' : 1 < a.re + b.re := by simpa using hA
    simp only [add_re]
    linarith
  have hsProd : HasProd (hughesYoungZetaEulerFactor (a + b + c))
      (riemannZeta (a + b + c)) := by
    simpa only [hughesYoungZetaEulerFactor] using
      riemannZeta_eulerProduct_hasProd hS
  have haProd : HasProd (hughesYoungZetaEulerFactor (a + b))
      (riemannZeta (a + b)) := by
    simpa only [hughesYoungZetaEulerFactor] using
      riemannZeta_eulerProduct_hasProd hA
  have hsT : Filter.Tendsto
      (fun u : Finset Nat.Primes =>
        ∏ p ∈ u, hughesYoungZetaEulerFactor (a + b + c) p)
      atTop (nhds (riemannZeta (a + b + c))) := hsProd
  have haT : Filter.Tendsto
      (fun u : Finset Nat.Primes =>
        ∏ p ∈ u, hughesYoungZetaEulerFactor (a + b) p)
      atTop (nhds (riemannZeta (a + b))) := haProd
  have ha0 : riemannZeta (a + b) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hA
  have hlim := Filter.Tendsto.div hsT haT ha0
  change Filter.Tendsto
    (fun u : Finset Nat.Primes =>
      ∏ p ∈ u, hughesYoungRegularLocalFactor a b c p)
    atTop (nhds (riemannZeta (a + b + c) / riemannZeta (a + b)))
  refine hlim.congr' ?_
  filter_upwards with u
  exact Finset.prod_div_distrib
    (f := hughesYoungZetaEulerFactor (a + b + c))
    (g := hughesYoungZetaEulerFactor (a + b)) |>.symm

/-- Outside the finite set of twist primes, the actual equation-(106)
factor is exactly the regular zeta-ratio factor. -/
theorem hughesYoungActualLocalFactor_eq_regular_of_not_mem
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re)
    {p : Nat.Primes} (hp : p ∉ hughesYoungPrimeFactors (h * k)) :
    hughesYoungActualLocalFactor h k a b c p =
      hughesYoungRegularLocalFactor a b c p := by
  have hhk0 : h * k ≠ 0 := (Nat.mul_pos hh hk).ne'
  have hpNotProd : ¬ (p : ℕ) ∣ h * k := by
    intro hpDvd
    exact hp (mem_hughesYoungPrimeFactors.mpr
      (Nat.mem_primeFactors.mpr ⟨p.prop, hpDvd, hhk0⟩))
  have hph : ¬ (p : ℕ) ∣ h := fun hph => hpNotProd (dvd_mul_of_dvd_left hph k)
  have hpk : ¬ (p : ℕ) ∣ k := fun hpk => hpNotProd (dvd_mul_of_dvd_right hpk h)
  unfold hughesYoungActualLocalFactor hughesYoungRegularLocalFactor
    hughesYoungZetaEulerFactor
  rw [inv_div_inv]
  exact hughesYoungEquation108_localFactor hh hk p.prop hph hpk hA hC

/-- At a prime dividing `h`, the quotient of the actual equation-(106)
factor by the regular zeta-ratio factor is exactly the first finite factor
in Hughes--Young Lemma 6.1. -/
theorem hughesYoungActual_div_regular_eq_leftFactor
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re)
    {p : Nat.Primes} (hph : (p : ℕ) ∣ h)
    (hr : 1 - (p : ℂ) ^ (-(b + c)) ≠ 0) :
    hughesYoungActualLocalFactor h k a b c p /
        hughesYoungRegularLocalFactor a b c p =
      hughesYoungLemma61LeftFactor h a b c p := by
  have hS : 1 < (a + b + c).re := by
    have hA' : 1 < a.re + b.re := by simpa using hA
    simp only [add_re]
    linarith
  have hq : 1 - (p : ℂ) ^ (-(a + b + c)) ≠ 0 :=
    Complex.one_sub_prime_cpow_ne_zero p.prop hS
  have hab : 1 - (p : ℂ) ^ (-(a + b)) ≠ 0 :=
    Complex.one_sub_prime_cpow_ne_zero p.prop hA
  rw [show hughesYoungActualLocalFactor h k a b c p =
      ((1 - (p : ℂ) ^ (-b)) *
          (1 - (p : ℂ) ^ (-(a + b + c))) +
        (p : ℂ) ^ (-b) * (1 - (p : ℂ) ^ (-a)) *
          (1 - (p : ℂ) ^ (-c)) *
          ((p : ℂ) ^ (-(b + c))) ^ (h.factorization p)) /
        ((1 - (p : ℂ) ^ (-(b + c))) *
          (1 - (p : ℂ) ^ (-(a + b + c)))) by
    exact hughesYoungEquation118_localFactor_left
      hh hk p.prop hhk hph hA hC hr]
  unfold hughesYoungRegularLocalFactor hughesYoungZetaEulerFactor
    hughesYoungLemma61LeftFactor
  field_simp [hr, hq, hab]

/-- Symmetric local quotient identity at a prime dividing `k`. -/
theorem hughesYoungActual_div_regular_eq_rightFactor
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re)
    {p : Nat.Primes} (hpk : (p : ℕ) ∣ k)
    (hr : 1 - (p : ℂ) ^ (-(a + c)) ≠ 0) :
    hughesYoungActualLocalFactor h k a b c p /
        hughesYoungRegularLocalFactor a b c p =
      hughesYoungLemma61RightFactor k a b c p := by
  have hS : 1 < (a + b + c).re := by
    have hA' : 1 < a.re + b.re := by simpa using hA
    simp only [add_re]
    linarith
  have hq : 1 - (p : ℂ) ^ (-(a + b + c)) ≠ 0 :=
    Complex.one_sub_prime_cpow_ne_zero p.prop hS
  have hab : 1 - (p : ℂ) ^ (-(a + b)) ≠ 0 :=
    Complex.one_sub_prime_cpow_ne_zero p.prop hA
  rw [show hughesYoungActualLocalFactor h k a b c p =
      ((1 - (p : ℂ) ^ (-a)) *
          (1 - (p : ℂ) ^ (-(a + b + c))) +
        (p : ℂ) ^ (-a) * (1 - (p : ℂ) ^ (-b)) *
          (1 - (p : ℂ) ^ (-c)) *
          ((p : ℂ) ^ (-(a + c))) ^ (k.factorization p)) /
        ((1 - (p : ℂ) ^ (-(a + c))) *
          (1 - (p : ℂ) ^ (-(a + b + c)))) by
    exact hughesYoungEquation118_localFactor_right
      hh hk p.prop hhk hpk hA hC hr]
  unfold hughesYoungRegularLocalFactor hughesYoungZetaEulerFactor
    hughesYoungLemma61RightFactor
  field_simp [hr, hq, hab]

theorem hughesYoungPrimeFactors_mul
    {h k : ℕ} (hh : h ≠ 0) (hk : k ≠ 0) :
    hughesYoungPrimeFactors (h * k) =
      hughesYoungPrimeFactors h ∪ hughesYoungPrimeFactors k := by
  ext p
  simp only [mem_hughesYoungPrimeFactors, Finset.mem_union]
  rw [Nat.primeFactors_mul hh hk]
  simp

theorem disjoint_hughesYoungPrimeFactors
    {h k : ℕ} (hhk : Nat.Coprime h k) :
    Disjoint (hughesYoungPrimeFactors h) (hughesYoungPrimeFactors k) := by
  rw [Finset.disjoint_left]
  intro p hph hpk
  have hph' : (p : ℕ) ∣ h :=
    Nat.dvd_of_mem_primeFactors (mem_hughesYoungPrimeFactors.mp hph)
  have hpk' : (p : ℕ) ∣ k :=
    Nat.dvd_of_mem_primeFactors (mem_hughesYoungPrimeFactors.mp hpk)
  have hpgcd : (p : ℕ) ∣ Nat.gcd h k := Nat.dvd_gcd hph' hpk'
  have hgcd : Nat.gcd h k = 1 := by
    simpa [Nat.coprime_iff_gcd_eq_one] using hhk
  rw [hgcd] at hpgcd
  exact p.prop.not_dvd_one hpgcd

/-- The finite correction obtained abstractly from the Euler product equals
the two explicit finite products printed in Hughes--Young Lemma 6.1. -/
theorem hughesYoungFiniteEulerCorrection_eq_sourceProducts
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re)
    (hleft : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-(b + c)) ≠ 0)
    (hright : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-(a + c)) ≠ 0) :
    hughesYoungFiniteEulerCorrection h k a b c =
      (∏ p ∈ hughesYoungPrimeFactors h,
        hughesYoungLemma61LeftFactor h a b c p) *
      ∏ p ∈ hughesYoungPrimeFactors k,
        hughesYoungLemma61RightFactor k a b c p := by
  let f : Nat.Primes → ℂ := fun p =>
    hughesYoungActualLocalFactor h k a b c p /
      hughesYoungRegularLocalFactor a b c p
  have hsplit : hughesYoungPrimeFactors (h * k) =
      hughesYoungPrimeFactors h ∪ hughesYoungPrimeFactors k :=
    hughesYoungPrimeFactors_mul hh.ne' hk.ne'
  have hdisjoint : Disjoint (hughesYoungPrimeFactors h)
      (hughesYoungPrimeFactors k) := disjoint_hughesYoungPrimeFactors hhk
  calc
    hughesYoungFiniteEulerCorrection h k a b c =
        ∏ p ∈ hughesYoungPrimeFactors (h * k), f p := by
      unfold hughesYoungFiniteEulerCorrection f
      exact (Finset.prod_div_distrib _ _).symm
    _ = ∏ p ∈ hughesYoungPrimeFactors h ∪ hughesYoungPrimeFactors k,
          f p := by rw [hsplit]
    _ = (∏ p ∈ hughesYoungPrimeFactors h, f p) *
          ∏ p ∈ hughesYoungPrimeFactors k, f p := by
      exact Finset.prod_union hdisjoint
    _ = (∏ p ∈ hughesYoungPrimeFactors h,
          hughesYoungLemma61LeftFactor h a b c p) *
        ∏ p ∈ hughesYoungPrimeFactors k,
          hughesYoungLemma61RightFactor k a b c p := by
      congr 1
      · apply Finset.prod_congr rfl
        intro p hp
        exact hughesYoungActual_div_regular_eq_leftFactor
          hh hk hhk hA hC
          (Nat.dvd_of_mem_primeFactors
            (mem_hughesYoungPrimeFactors.mp hp)) (hleft p hp)
      · apply Finset.prod_congr rfl
        intro p hp
        exact hughesYoungActual_div_regular_eq_rightFactor
          hh hk hhk hA hC
          (Nat.dvd_of_mem_primeFactors
            (mem_hughesYoungPrimeFactors.mp hp)) (hright p hp)

/-- Exact finite-correction form of Hughes--Young Lemma 6.1. -/
theorem hughesYoungLemma61_finiteEulerCorrection
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re) :
    hughesYoungEquation106 h k a b c =
      riemannZeta (1 + c) *
        (riemannZeta (a + b + c) / riemannZeta (a + b)) *
          hughesYoungFiniteEulerCorrection h k a b c := by
  let f : Nat.Primes → ℂ := hughesYoungRegularLocalFactor a b c
  let g : Nat.Primes → ℂ := hughesYoungActualLocalFactor h k a b c
  let S : Finset Nat.Primes := hughesYoungPrimeFactors (h * k)
  have hf : HasProd f
      (riemannZeta (a + b + c) / riemannZeta (a + b)) :=
    hughesYoungRegularLocalFactor_hasProd hA hC
  have hf0 : ∀ p ∈ S, f p ≠ 0 := by
    intro p _hp
    exact hughesYoungRegularLocalFactor_ne_zero hA hC p
  have hfg : ∀ p ∉ S, f p = g p := by
    intro p hp
    exact (hughesYoungActualLocalFactor_eq_regular_of_not_mem
      hh hk hA hC hp).symm
  have hgFromFinite : HasProd g
      ((riemannZeta (a + b + c) / riemannZeta (a + b)) *
        ((∏ p ∈ S, g p) / ∏ p ∈ S, f p)) :=
    hf.congr_cofinite₀ hf0 hfg
  have hgActual : HasProd g
      (∑' n : ℕ, hughesYoungEquation106Coefficient h k a b c n) := by
    exact (hughesYoungEquation106Coefficient_isMultiplicative h k a b c).eulerProduct_hasProd
      (summable_norm_hughesYoungEquation106Coefficient hh hk hA hC)
  have hprod := hgActual.unique hgFromFinite
  rw [hughesYoungEquation106_eq_zeta_mul_eulerProduct hh hk hA hC]
  change riemannZeta (1 + c) * (∏' p : Nat.Primes, g p) = _
  rw [hgActual.tprod_eq, hprod]
  unfold hughesYoungFiniteEulerCorrection S f g
  ring

/-- Hughes--Young Lemma 6.1 in the exact two-product form printed in the
paper, on its initial absolute-convergence region and away from the finitely
many geometric denominators used in the displayed meromorphic formula. -/
theorem hughesYoungLemma61_source
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k)
    {a b c : ℂ} (hA : 1 < (a + b).re) (hC : 0 < c.re)
    (hleft : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-(b + c)) ≠ 0)
    (hright : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-(a + c)) ≠ 0) :
    hughesYoungEquation96 h k a b (1 + c) =
      riemannZeta (1 + c) *
        (riemannZeta (a + b + c) / riemannZeta (a + b)) *
        ((∏ p ∈ hughesYoungPrimeFactors h,
            hughesYoungLemma61LeftFactor h a b c p) *
          ∏ p ∈ hughesYoungPrimeFactors k,
            hughesYoungLemma61RightFactor k a b c p) := by
  rw [hughesYoungEquation105_106 hh hk a b c hA hC]
  rw [hughesYoungLemma61_finiteEulerCorrection hh hk hA hC]
  rw [hughesYoungFiniteEulerCorrection_eq_sourceProducts
    hh hk hhk hA hC hleft hright]

end RiemannZeta.GuthMaynard

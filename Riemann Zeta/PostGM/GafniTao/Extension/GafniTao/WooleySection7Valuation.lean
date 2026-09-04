import GafniTao.WooleySection7Omega
import GafniTao.WooleySection7HardArithmetic
import GafniTao.WooleyPadicSeparation
import GafniTao.WooleyTupleDisplacement

/-!
# The valuation cancellation in Wooley equations (7.10)--(7.12)

The change of equations in Section 7 produces a common factor
`omega * p^d`, where `omega` is prime to the source prime.  This file keeps
the two logically distinct cancellations explicit: `omega` is a unit modulo
every prime power, whereas cancelling `p^d` lowers the modulus by exactly
`d`.  This is the arithmetic loss used in the definition of `B'` in (7.3).
-/

namespace GafniTao

noncomputable section

open Finset Polynomial
open scoped BigOperators

/-- The unit extracted from a separated residue difference stays invertible
modulo every power of the source prime. -/
theorem wooleySection7_unit_isUnit_primePower
    {p L : ℕ} {omega : ℤ}
    (hcop : Nat.Coprime p omega.natAbs) :
    IsUnit (omega : ZMod (p ^ L)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
  simpa using hcop.pow_left L

/-- Exact integer divisibility cancellation underlying the passage from
modulus `p^(d+L)` to modulus `p^L`.  The coprime factor costs no modulus. -/
theorem wooleySection7_primePower_unit_cancel_dvd
    {p d L : ℕ} {omega z : ℤ} (hp : p ≠ 0)
    (hcop : Nat.Coprime p omega.natAbs)
    (hdiv : (p : ℤ) ^ (d + L) ∣ (p : ℤ) ^ d * omega * z) :
    (p : ℤ) ^ L ∣ z := by
  have hpd : (p : ℤ) ^ d ≠ 0 := pow_ne_zero d (by exact_mod_cast hp)
  have hcancel : (p : ℤ) ^ L ∣ omega * z := by
    rw [pow_add, mul_assoc] at hdiv
    exact (Int.mul_dvd_mul_iff_left hpd).mp hdiv
  have hcopInt : IsCoprime ((p : ℤ) ^ L) omega := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop.pow_left L
  exact hcopInt.dvd_of_dvd_mul_left hcancel

/-- ZMod form of the same cancellation.  This is the form used when a
finite Fourier average has converted congruences into vanishing residue
classes. -/
theorem wooleySection7_primePower_unit_cancel_zmod
    {p d L : ℕ} {omega z : ℤ} (hp : p ≠ 0)
    (hcop : Nat.Coprime p omega.natAbs)
    (hzero : (((p : ℤ) ^ d * omega * z : ℤ) :
      ZMod (p ^ (d + L))) = 0) :
    (z : ZMod (p ^ L)) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero ⊢
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hzero ⊢
  exact wooleySection7_primePower_unit_cancel_dvd hp hcop hzero

/-- Cancelling a larger row-dependent power yields every weaker common
modulus.  In Section 7 one takes `e = a*l + (k-r)*gamma` and bounds it by
`r*a + (k-r)*gamma`. -/
theorem wooleySection7_primePower_unit_cancel_to_common
    {p e d M : ℕ} {omega z : ℤ} (hp : p ≠ 0)
    (hcop : Nat.Coprime p omega.natAbs)
    (hed : e ≤ d) (hdM : d ≤ M)
    (hdiv : (p : ℤ) ^ M ∣ (p : ℤ) ^ e * omega * z) :
    (p : ℤ) ^ (M - d) ∣ z := by
  have heM : e ≤ M := hed.trans hdM
  have hrewrite : M = e + (M - e) := (Nat.add_sub_of_le heM).symm
  have hfirst : (p : ℤ) ^ (M - e) ∣ z := by
    apply wooleySection7_primePower_unit_cancel_dvd hp hcop
    rw [← hrewrite]
    exact hdiv
  have hle : M - d ≤ M - e := Nat.sub_le_sub_left hed M
  exact dvd_trans (pow_dvd_pow (p : ℤ) hle) hfirst

/-- Integral tuple displacement, before reduction modulo the Fourier
modulus.  Keeping this integer representative makes exact valuation losses
available to the Section 7 argument. -/
def wooleyIntegerTupleDisplacement {I : Type*}
    (s : ℕ) (value : I → ℤ)
    (xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I) : ℤ :=
  (∑ i, value (xy.1 i)) - ∑ i, value (xy.2 i)

/-- Reduction of the integral displacement is exactly the displacement used
by finite Fourier orthogonality. -/
theorem wooleyIntegerTupleDisplacement_cast
    {I : Type*} (q k s : ℕ)
    (value : I → Fin k → ℤ)
    (xy : WooleyFiniteTuple s I × WooleyFiniteTuple s I) (j : Fin k) :
    (wooleyIntegerTupleDisplacement s (fun x => value x j) xy : ZMod q) =
      wooleyTupleDisplacement q k s
        (fun x l => (value x l : ZMod q)) xy j := by
  simp [wooleyIntegerTupleDisplacement, wooleyTupleDisplacement]

/-- The literal lower-degree system in (7.11). -/
def wooleySection7LowerSystem
    (r p d : ℕ) (Xi : Fin r → Polynomial ℤ) :
    WooleyPolynomialSystem r := fun l =>
  X ^ ((l : ℕ) + 1) + C ((p : ℤ) ^ d) * Xi l

theorem wooleySection7LowerSystem_spaced
    (r p d : ℕ) (Xi : Fin r → Polynomial ℤ) :
    (wooleySection7LowerSystem r p d Xi).Spaced p d := by
  exact ⟨Xi, fun _ => rfl⟩

/-- Exact final cancellation from the transformed congruences following
(7.11) to the common modulus (7.12).  The row `l` loses
`a*(l+1)+(k-r)*gamma`; replacing this by its maximum
`r*a+(k-r)*gamma` gives one common modulus for all equations. -/
theorem wooleySection7_transformed_congruences_imply_7_12
    {I : Type*} {k r p a gamma M R : ℕ} {omega : ℤ}
    (hp : p ≠ 0)
    (hcop : Nat.Coprime p omega.natAbs)
    (hcommon : r * a + (k - r) * gamma ≤ M)
    (Psi : WooleyPolynomialSystem r)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (point : I → ℤ)
    (hscaled : ∀ l : Fin r,
      (p : ℤ) ^ M ∣
        (p : ℤ) ^ (a * ((l : ℕ) + 1) + (k - r) * gamma) *
          omega ^ (k - r) *
          wooleyIntegerTupleDisplacement R
            (fun x => (Psi l).eval (point x)) xy) :
    ∀ l : Fin r,
      wooleyTupleDisplacement
        (p ^ (M - (r * a + (k - r) * gamma))) r R
        (fun x j => (((Psi j).eval (point x) : ℤ) :
          ZMod (p ^ (M - (r * a + (k - r) * gamma))))) xy l = 0 := by
  classical
  intro l
  let d := r * a + (k - r) * gamma
  let e := a * ((l : ℕ) + 1) + (k - r) * gamma
  have hleIndex : (l : ℕ) + 1 ≤ r := l.isLt
  have hed : e ≤ d := by
    dsimp [e, d]
    nlinarith
  have hcopPow : Nat.Coprime p (omega ^ (k - r)).natAbs := by
    simpa only [Int.natAbs_pow] using hcop.pow_right (k - r)
  have hdiv :
      (p : ℤ) ^ (M - d) ∣
        wooleyIntegerTupleDisplacement R
          (fun x => (Psi l).eval (point x)) xy :=
    wooleySection7_primePower_unit_cancel_to_common hp hcopPow hed hcommon
      (hscaled l)
  have hz :
      (wooleyIntegerTupleDisplacement R
          (fun x => (Psi l).eval (point x)) xy :
        ZMod (p ^ (M - d))) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    exact hdiv
  rw [wooleyIntegerTupleDisplacement_cast
    (p ^ (M - d)) r R
    (fun x j => (Psi j).eval (point x)) xy l] at hz
  simpa [d] using hz

/-- Source-parameter specialization of the preceding cancellation: equation
(7.3) identifies the surviving modulus exactly with `B'`, rather than merely
with an unspecified smaller prime power. -/
theorem wooleySection7_transformed_congruences_imply_7_12_source
    {I : Type*} {k r p a b gamma nu R : ℕ} {omega : ℤ}
    (hp : p ≠ 0)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (hcop : Nat.Coprime p omega.natAbs)
    (Psi : WooleyPolynomialSystem r)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (point : I → ℤ)
    (hscaled : ∀ l : Fin r,
      (p : ℤ) ^ ((k - r + 1) * b) ∣
        (p : ℤ) ^ (a * ((l : ℕ) + 1) + (k - r) * gamma) *
          omega ^ (k - r) *
          wooleyIntegerTupleDisplacement R
            (fun x => (Psi l).eval (point x)) xy) :
    ∀ l : Fin r,
      wooleyTupleDisplacement
        (p ^ wooleySection7BPrimeNat k r a b gamma) r R
        (fun x j => (((Psi j).eval (point x) : ℤ) :
          ZMod (p ^ wooleySection7BPrimeNat k r a b gamma))) xy l = 0 := by
  have hsum := wooley_section7_BPrimeNat_add hBPrime
  have hcommon : r * a + (k - r) * gamma ≤ (k - r + 1) * b := by
    omega
  have hresult :=
    wooleySection7_transformed_congruences_imply_7_12
      (k := k) hp hcop hcommon Psi xy point hscaled
  have hsub :
      (k - r + 1) * b - (r * a + (k - r) * gamma) =
        wooleySection7BPrimeNat k r a b gamma := by
    omega
  rw [hsub] at hresult
  intro l
  exact hresult l

#print axioms wooleySection7_unit_isUnit_primePower
#print axioms wooleySection7_primePower_unit_cancel_dvd
#print axioms wooleySection7_primePower_unit_cancel_zmod
#print axioms wooleySection7_primePower_unit_cancel_to_common
#print axioms wooleyIntegerTupleDisplacement_cast
#print axioms wooleySection7LowerSystem_spaced
#print axioms wooleySection7_transformed_congruences_imply_7_12
#print axioms wooleySection7_transformed_congruences_imply_7_12_source

end

end GafniTao

import GafniTao.WooleySection7Transform

/-!
# The hard congruence implication in Wooley Section 7

This file applies the exact polynomial change of equations to ordered tuple
displacements.  It first cancels the column valuations to the common modulus
`p^(M-gamma*k)`, applies the integral inverse matrix, and then cancels the row
valuations to the common modulus in (7.12).  Both losses remain explicit.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleyIntegerTupleDisplacement_add
    {I : Type*} (R : ℕ) (f g : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I) :
    wooleyIntegerTupleDisplacement R (fun x => f x + g x) xy =
      wooleyIntegerTupleDisplacement R f xy +
        wooleyIntegerTupleDisplacement R g xy := by
  simp only [wooleyIntegerTupleDisplacement, Finset.sum_add_distrib]
  ring

theorem wooleyIntegerTupleDisplacement_smul
    {I : Type*} (R : ℕ) (z : ℤ) (f : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I) :
    wooleyIntegerTupleDisplacement R (fun x => z * f x) xy =
      z * wooleyIntegerTupleDisplacement R f xy := by
  simp only [wooleyIntegerTupleDisplacement, ← Finset.mul_sum]
  ring

theorem wooleyIntegerTupleDisplacement_sum
    {I J : Type*} [Fintype J] (R : ℕ) (f : J → I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I) :
    wooleyIntegerTupleDisplacement R (fun x => ∑ j, f j x) xy =
      ∑ j, wooleyIntegerTupleDisplacement R (f j) xy := by
  unfold wooleyIntegerTupleDisplacement
  have hleft :
      (∑ i : Fin R, ∑ j : J, f j (xy.1 i)) =
        ∑ j : J, ∑ i : Fin R, f j (xy.1 i) := Finset.sum_comm
  have hright :
      (∑ i : Fin R, ∑ j : J, f j (xy.2 i)) =
        ∑ j : J, ∑ i : Fin R, f j (xy.2 i) := Finset.sum_comm
  rw [hleft, hright, Finset.sum_sub_distrib]

theorem wooleyIntegerTupleDisplacement_polynomial_add
    {I : Type*} (R : ℕ) (f g : Polynomial ℤ) (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I) :
    wooleyIntegerTupleDisplacement R
        (fun x => (f + g).eval (point x)) xy =
      wooleyIntegerTupleDisplacement R (fun x => f.eval (point x)) xy +
        wooleyIntegerTupleDisplacement R (fun x => g.eval (point x)) xy := by
  simpa only [eval_add] using
    wooleyIntegerTupleDisplacement_add R
      (fun x => f.eval (point x)) (fun x => g.eval (point x)) xy

theorem wooleyIntegerTupleDisplacement_polynomial_C_mul
    {I : Type*} (R : ℕ) (z : ℤ) (f : Polynomial ℤ)
    (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I) :
    wooleyIntegerTupleDisplacement R
        (fun x => (C z * f).eval (point x)) xy =
      z * wooleyIntegerTupleDisplacement R
        (fun x => f.eval (point x)) xy := by
  simpa only [eval_mul, eval_C] using
    wooleyIntegerTupleDisplacement_smul R z
      (fun x => f.eval (point x)) xy

/-- A top-row congruence yields a normalized-column congruence at the weakest
common column modulus. -/
theorem wooleySection7_top_implies_normalized_column
    {I : Type*} {k r p c a gamma M R : ℕ}
    (hp : p ≠ 0) (hrk : r ≤ k) (hgamma : gamma ≤ a)
    (hgammaM : gamma * k ≤ M) (omega h : ℤ)
    (hsep : h = omega * (p : ℤ) ^ gamma)
    (psi : Fin r → Polynomial ℤ) (l : Fin r)
    (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (htop : (p : ℤ) ^ M ∣
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7TranslatedDilatedPolynomial p a h
            (wooleySection7TopSystem k r p c psi l)).eval (point x)) xy) :
    (p : ℤ) ^ (M - gamma * k) ∣
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7ColumnNormalizedPolynomial
            k r p c a gamma omega h psi l).eval (point x)) xy := by
  let j := wooleySection7Node k r l + 1
  let qpoly := wooleySection7ColumnNormalizedPolynomial
    k r p c a gamma omega h psi l
  have hfactor := wooleySection7TranslatedTop_eq_columnFactor_mul
    (p := p) (c := c) (a := a) (gamma := gamma)
    hrk hgamma omega h hsep psi l
  have hdisp :
      wooleyIntegerTupleDisplacement R
          (fun x =>
            (wooleySection7TranslatedDilatedPolynomial p a h
              (wooleySection7TopSystem k r p c psi l)).eval (point x)) xy =
        (p : ℤ) ^ (gamma * j) *
          wooleyIntegerTupleDisplacement R
            (fun x => qpoly.eval (point x)) xy := by
    rw [hfactor]
    exact wooleyIntegerTupleDisplacement_polynomial_C_mul
      R ((p : ℤ) ^ (gamma * j)) qpoly point xy
  have hjk : j ≤ k := wooleySection7Node_succ_le hrk l
  have he : gamma * j ≤ gamma * k := Nat.mul_le_mul_left gamma hjk
  have hdiv : (p : ℤ) ^ M ∣
      (p : ℤ) ^ (gamma * j) * 1 *
        wooleyIntegerTupleDisplacement R
          (fun x => qpoly.eval (point x)) xy := by
    rw [hdisp] at htop
    simpa only [mul_one] using htop
  exact wooleySection7_primePower_unit_cancel_to_common
    hp (by simp) he hgammaM hdiv

/-- Linear combinations used by the inverse matrix preserve the common
normalized-column modulus. -/
theorem wooleySection7_normalized_columns_imply_transformed
    {I : Type*} {k r p c a gamma L R : ℕ}
    (omega h omegaInv : ℤ) (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L))) (i : Fin r)
    (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (hcols : ∀ l : Fin r, (p : ℤ) ^ L ∣
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7ColumnNormalizedPolynomial
            k r p c a gamma omega h psi l).eval (point x)) xy) :
    (p : ℤ) ^ L ∣
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7TransformedPolynomial
            k r p c a gamma L omega h omegaInv psi G i).eval (point x)) xy := by
  let qpoly (l : Fin r) := wooleySection7ColumnNormalizedPolynomial
    k r p c a gamma omega h psi l
  let z (l : Fin r) := wooleyZModMatrixIntLift G i l *
    omegaInv ^ (wooleySection7Node k r l + 1)
  have hsum :
      wooleyIntegerTupleDisplacement R
          (fun x => (∑ l : Fin r, C (z l) * qpoly l).eval (point x)) xy =
        ∑ l : Fin r, z l *
          wooleyIntegerTupleDisplacement R
            (fun x => (qpoly l).eval (point x)) xy := by
    have heval (x : I) :
        (∑ l : Fin r, C (z l) * qpoly l).eval (point x) =
          ∑ l : Fin r, z l * (qpoly l).eval (point x) := by
      simpa only [eval_mul, eval_C] using
        (eval_finsetSum (Finset.univ : Finset (Fin r))
          (fun l => C (z l) * qpoly l) (point x))
    simp_rw [heval]
    rw [wooleyIntegerTupleDisplacement_sum]
    apply Finset.sum_congr rfl
    intro l hl
    exact wooleyIntegerTupleDisplacement_smul R (z l)
      (fun x => (qpoly l).eval (point x)) xy
  have hwhole :
      wooleyIntegerTupleDisplacement R
          (fun x =>
            (wooleySection7TransformedPolynomial
              k r p c a gamma L omega h omegaInv psi G i).eval (point x)) xy =
        omega ^ ((i : ℕ) + 1) *
          ∑ l : Fin r, z l *
            wooleyIntegerTupleDisplacement R
              (fun x => (qpoly l).eval (point x)) xy := by
    unfold wooleySection7TransformedPolynomial
    rw [wooleyIntegerTupleDisplacement_polynomial_C_mul]
    exact congrArg (fun t : ℤ => omega ^ ((i : ℕ) + 1) * t) hsum
  rw [hwhole]
  apply dvd_mul_of_dvd_right
  apply dvd_sum
  intro l hl
  exact dvd_mul_of_dvd_right (hcols l) _

/-- Cancelling the row valuation in a transformed polynomial gives a lower
equation at the common residual modulus.  The `p^L` lift error vanishes
exactly and costs no additional depth. -/
theorem wooleySection7_transformed_implies_lower_displacement
    {I : Type*} {p r a gamma L R : ℕ}
    (hp : p ≠ 0) (hcommon : r * (a - gamma) ≤ L)
    (i : Fin r) (W Psi Error : Polynomial ℤ)
    (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (hWpoly : W =
      C ((p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1))) * Psi +
        C ((p : ℤ) ^ L) * Error)
    (hWdiv : (p : ℤ) ^ L ∣
      wooleyIntegerTupleDisplacement R (fun x => W.eval (point x)) xy) :
    (p : ℤ) ^ (L - r * (a - gamma)) ∣
      wooleyIntegerTupleDisplacement R
        (fun x => Psi.eval (point x)) xy := by
  have hdisp :
      wooleyIntegerTupleDisplacement R (fun x => W.eval (point x)) xy =
        (p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1)) *
            wooleyIntegerTupleDisplacement R
              (fun x => Psi.eval (point x)) xy +
          (p : ℤ) ^ L *
            wooleyIntegerTupleDisplacement R
              (fun x => Error.eval (point x)) xy := by
    rw [hWpoly, wooleyIntegerTupleDisplacement_polynomial_add,
      wooleyIntegerTupleDisplacement_polynomial_C_mul,
      wooleyIntegerTupleDisplacement_polynomial_C_mul]
  have hErrorDiv : (p : ℤ) ^ L ∣
      (p : ℤ) ^ L *
        wooleyIntegerTupleDisplacement R
          (fun x => Error.eval (point x)) xy := dvd_mul_right _ _
  have hrowDiv : (p : ℤ) ^ L ∣
      (p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1)) *
        wooleyIntegerTupleDisplacement R
          (fun x => Psi.eval (point x)) xy := by
    have hsub := dvd_sub hWdiv hErrorDiv
    rw [hdisp] at hsub
    simpa only [add_sub_cancel_right] using hsub
  have hi : (i : ℕ) + 1 ≤ r := i.isLt
  have he : (a - gamma) * ((i : ℕ) + 1) ≤
      r * (a - gamma) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (a - gamma) hi
  have hrowDiv' : (p : ℤ) ^ L ∣
      (p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1)) * 1 *
        wooleyIntegerTupleDisplacement R
          (fun x => Psi.eval (point x)) xy := by
    simpa only [mul_one] using hrowDiv
  exact wooleySection7_primePower_unit_cancel_to_common
    hp (by simp) he hcommon hrowDiv'

/-- Complete algebraic passage from the top congruences (7.10) to a spaced
lower system.  The conclusion records the exact residual depth before the
source arithmetic identifies it with `B'`. -/
theorem wooleySection7_top_congruences_exist_lower_system
    {k r p c a gamma M : ℕ}
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hrk : r ≤ k) (hkp : k < p)
    (hgamma : gamma ≤ a) (hgammaK : gamma * k ≤ a)
    (hgammaM : gamma * k ≤ M)
    (hcommon : r * (a - gamma) ≤ M - gamma * k)
    (omega h : ℤ) (homega : omega ≠ 0)
    (hcop : Nat.Coprime p omega.natAbs)
    (hsep : h = omega * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      ∀ {I : Type*} {R : ℕ} (point : I → ℤ)
          (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I),
        (∀ l : Fin r, (p : ℤ) ^ M ∣
          wooleyIntegerTupleDisplacement R
            (fun x =>
              (wooleySection7TranslatedDilatedPolynomial p a h
                (wooleySection7TopSystem k r p c psi l)).eval (point x)) xy) →
        ∀ i : Fin r, (p : ℤ) ^
            ((M - gamma * k) - r * (a - gamma)) ∣
          wooleyIntegerTupleDisplacement R
            (fun x => (Psi i).eval (point x)) xy := by
  classical
  let L := M - gamma * k
  let Omega := wooleySection7OmegaMatrix (p := p) (c := c)
    hrk h hh psi
  have hOmega : ∀ i l,
      (Omega i l : ZMod p) =
        (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) :
          ZMod p) := by
    intro i l
    exact wooleySection7OmegaMatrix_mod_prime
      (p := p) hc hrk h hh psi i l
  obtain ⟨G, hG⟩ :=
    wooleySection7_sourceMatrix_transpose_exists_leftInverse_primePower
      (L := L) hpPrime hrk hkp Omega hOmega
  obtain ⟨omegaInv, hInv⟩ :=
    wooleySection7_exists_int_unit_inverse (L := L) hcop
  have hG' : G * Matrix.transpose
      (wooleyIntMatrixMod
        (wooleySection7OmegaMatrix (p := p) (c := c)
          hrk h hh psi) (p ^ L)) = 1 := by
    simpa only [Omega] using hG
  choose Xi Error hrow using fun i : Fin r =>
    wooleySection7TransformedPolynomial_exists_lower_equation
      (L := L) hpPrime.ne_zero hrk hgamma hgammaK
        omega h omegaInv homega hsep hh psi G hG' hInv i
  let Psi : WooleyPolynomialSystem r :=
    wooleySection7LowerSystem r p (a - (k - r) * gamma) Xi
  refine ⟨Psi, ?_, ?_⟩
  · exact wooleySection7LowerSystem_spaced
      r p (a - (k - r) * gamma) Xi
  · intro I R point xy htop i
    have hcols : ∀ l : Fin r, (p : ℤ) ^ L ∣
        wooleyIntegerTupleDisplacement R
          (fun x =>
            (wooleySection7ColumnNormalizedPolynomial
              k r p c a gamma omega h psi l).eval (point x)) xy := by
      intro l
      dsimp only [L]
      exact wooleySection7_top_implies_normalized_column
        hpPrime.ne_zero hrk hgamma hgammaM omega h hsep psi l point xy
          (htop l)
    have hWdiv := wooleySection7_normalized_columns_imply_transformed
      omega h omegaInv psi G i point xy hcols
    have hrow' :
        wooleySection7TransformedPolynomial
            k r p c a gamma L omega h omegaInv psi G i =
          C ((p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1))) *
              Psi i +
            C ((p : ℤ) ^ L) * Error i := by
      simpa only [Psi, wooleySection7LowerSystem] using hrow i
    have hresult := wooleySection7_transformed_implies_lower_displacement
      hpPrime.ne_zero (by simpa only [L] using hcommon)
      i (wooleySection7TransformedPolynomial
          k r p c a gamma L omega h omegaInv psi G i)
        (Psi i) (Error i) point xy hrow' hWdiv
    simpa only [L] using hresult

/-- The two-stage column/row cancellation depth is exactly the natural
representative of the signed quantity `B'` from (7.3). -/
theorem wooley_section7_common_depth_eq_BPrimeNat
    {k r a b gamma nu : ℕ} (hrk : r < k)
    (hgamma : gamma ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma) :
    ((((k - r + 1) * b - gamma * k) - r * (a - gamma))) =
      wooleySection7BPrimeNat k r a b gamma := by
  let bp := wooleySection7BPrimeNat k r a b gamma
  let M := (k - r + 1) * b
  have hsum : bp + r * a + (k - r) * gamma = M := by
    simpa only [bp, M] using wooley_section7_BPrimeNat_add hBPrime
  have hgammaR : gamma * r + (a - gamma) * r = a * r := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hgamma]
  have hsplit : gamma * k = gamma * (k - r) + gamma * r := by
    have hkr : (k - r) + r = k := Nat.sub_add_cancel hrk.le
    calc
      gamma * k = gamma * ((k - r) + r) := by rw [hkr]
      _ = _ := Nat.mul_add _ _ _
  have hdecomp :
      M = gamma * k + r * (a - gamma) + bp := by
    rw [hsplit]
    calc
      M = bp + r * a + (k - r) * gamma := hsum.symm
      _ = gamma * (k - r) + gamma * r +
          r * (a - gamma) + bp := by
        rw [Nat.mul_comm (k - r) gamma]
        have hgammaR' : gamma * r + r * (a - gamma) = r * a := by
          simpa [Nat.mul_comm] using hgammaR
        omega
  dsimp only [M, bp] at hdecomp ⊢
  rw [hdecomp]
  omega

/-- Source-parameter form of the hard change of equations: the congruences
(7.10) imply a literal `p^(B')` Vinogradov-type system (7.12). -/
theorem wooleySection7_top_congruences_imply_equation_7_12
    {I : Type*} {k r p c a b gamma nu R : ℕ}
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omega h : ℤ) (homega : omega ≠ 0)
    (hcop : Nat.Coprime p omega.natAbs)
    (hsep : h = omega * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (htop : ∀ l : Fin r, (p : ℤ) ^ ((k - r + 1) * b) ∣
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7TranslatedDilatedPolynomial p a h
            (wooleySection7TopSystem k r p c psi l)).eval (point x)) xy) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      ∀ i : Fin r,
        wooleyTupleDisplacement
          (p ^ wooleySection7BPrimeNat k r a b gamma) r R
          (fun x j => (((Psi j).eval (point x) : ℤ) :
            ZMod (p ^ wooleySection7BPrimeNat k r a b gamma))) xy i = 0 := by
  have hkpos : 1 ≤ k := hr.trans hrk.le
  have hgamma : gamma ≤ a := by
    have hle : gamma ≤ gamma * k := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left gamma hkpos
    exact hle.trans hgammaK
  let M := (k - r + 1) * b
  let bp := wooleySection7BPrimeNat k r a b gamma
  have hdepth := wooley_section7_common_depth_eq_BPrimeNat
    hrk hgamma hBPrime
  have hdecomp : M = gamma * k + r * (a - gamma) + bp := by
    dsimp only [M, bp]
    have hsum := wooley_section7_BPrimeNat_add hBPrime
    have hgammaR : gamma * r + (a - gamma) * r = a * r := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hgamma]
    have hsplit : gamma * k = gamma * (k - r) + gamma * r := by
      have hkr : (k - r) + r = k := Nat.sub_add_cancel hrk.le
      calc
        gamma * k = gamma * ((k - r) + r) := by rw [hkr]
        _ = _ := Nat.mul_add _ _ _
    rw [hsplit]
    calc
      (k - r + 1) * b =
          bp + r * a + (k - r) * gamma := by
        simpa only [bp] using hsum.symm
      _ = gamma * (k - r) + gamma * r +
          r * (a - gamma) + bp := by
        rw [Nat.mul_comm (k - r) gamma]
        have hgammaR' : gamma * r + r * (a - gamma) = r * a := by
          simpa [Nat.mul_comm] using hgammaR
        omega
  have hgammaM : gamma * k ≤ M := by omega
  have hcommon : r * (a - gamma) ≤ M - gamma * k := by omega
  obtain ⟨Psi, hspaced, hdiv⟩ :=
    wooleySection7_top_congruences_exist_lower_system
      hpPrime hc hrk.le hkp hgamma hgammaK hgammaM hcommon
        omega h homega hcop hsep hh psi
  have hdivPoint := hdiv point xy htop
  refine ⟨Psi, hspaced, ?_⟩
  intro i
  have hdiv' : (p : ℤ) ^ bp ∣
      wooleyIntegerTupleDisplacement R
        (fun x => (Psi i).eval (point x)) xy := by
    have hi := hdivPoint i
    dsimp only [M, bp] at hi hdepth ⊢
    rw [hdepth] at hi
    exact hi
  have hz :
      (wooleyIntegerTupleDisplacement R
          (fun x => (Psi i).eval (point x)) xy : ZMod (p ^ bp)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    exact hdiv'
  rw [wooleyIntegerTupleDisplacement_cast
    (p ^ bp) r R (fun x j => (Psi j).eval (point x)) xy i] at hz
  simpa only [bp] using hz

#print axioms wooleyIntegerTupleDisplacement_add
#print axioms wooleyIntegerTupleDisplacement_smul
#print axioms wooleyIntegerTupleDisplacement_sum
#print axioms wooleyIntegerTupleDisplacement_polynomial_add
#print axioms wooleyIntegerTupleDisplacement_polynomial_C_mul
#print axioms wooleySection7_top_implies_normalized_column
#print axioms wooleySection7_normalized_columns_imply_transformed
#print axioms wooleySection7_transformed_implies_lower_displacement
#print axioms wooleySection7_top_congruences_exist_lower_system
#print axioms wooley_section7_common_depth_eq_BPrimeNat
#print axioms wooleySection7_top_congruences_imply_equation_7_12

end

end GafniTao

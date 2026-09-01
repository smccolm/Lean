import GafniTao.FordBinomialTransform
import GafniTao.FordPrimePowerTriangular

/-!
# Ford Section 3: reduction of the source system modulo a prime power

This file supplies the missing source-to-Lemma-2.4 bridge in Ford's proof.
The leading coefficients of a type `(d,T)` integer system are first recovered
as literal integers.  A prime larger than the source degree and avoiding `T`
therefore makes every relevant leading coefficient a unit modulo `p^s`.
-/

open Finset Polynomial

namespace GafniTao

noncomputable section

/-- The literal positive integral leading coefficient of the source polynomial
with index `d+j+1`. -/
def fordSourceLeadingNat (d j m T : ℕ) : ℕ :=
  (d + j + 1).factorial / (j + 1).factorial * (2 ^ m * T)

theorem fordIntegerPolynomialSystem_above_lc
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (j : Fin (k - d)) :
    (ψ.poly (fordAboveIndex hdk j)).leadingCoeff =
      (fordSourceLeadingNat d j ψ.twoMultiplicity T : ℤ) := by
  apply Int.cast_injective (α := ℚ)
  rw [ψ.leadingCoeff_above _ (fordAboveIndex_above hdk j)]
  simp only [fordAboveIndex_val]
  rw [show d + (j : ℕ) + 1 - d = (j : ℕ) + 1 by omega]
  unfold fordSourceLeadingNat
  push_cast
  rw [← Nat.cast_div_charZero (Nat.factorial_dvd_factorial (by omega))]
  norm_cast

theorem fordSourceLeadingNat_not_dvd
    {k d m T p : ℕ} (hp : Nat.Prime p) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (j : Fin (k - d))
    (hpT : ¬p ∣ T) :
    ¬p ∣ fordSourceLeadingNat d j m T := by
  have hdeg : d + (j : ℕ) + 1 ≤ k := by omega
  have hfact : ¬p ∣ (d + (j : ℕ) + 1).factorial := by
    rw [hp.dvd_factorial]
    omega
  have hden : ((j : ℕ) + 1).factorial ∣
      (d + (j : ℕ) + 1).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have hquot : ¬p ∣ (d + (j : ℕ) + 1).factorial /
      ((j : ℕ) + 1).factorial := by
    intro h
    apply hfact
    have hm := dvd_mul_of_dvd_left h ((j : ℕ) + 1).factorial
    rwa [Nat.div_mul_cancel hden] at hm
  have hp2 : ¬p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) h
    omega
  exact hp.not_dvd_mul hquot
    (hp.not_dvd_mul (fun h => hp2 (hp.dvd_of_dvd_pow h)) hpT)

theorem fordIntegerPolynomialSystem_above_lc_isUnit
    {k d T p s : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    (hp : Nat.Prime p) (hs : 0 < s) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (j : Fin (k - d)) :
    IsUnit (((ψ.poly (fordAboveIndex hdk j)).leadingCoeff : ℤ) :
      ZMod (p ^ s)) := by
  rw [fordIntegerPolynomialSystem_above_lc ψ hdk j]
  norm_cast
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hs]
  exact fordSourceLeadingNat_not_dvd hp hk2 hkp hdk j hpT

/-- The nonzero part of a source type `(d,T)` system, reduced modulo `p^s`.
The hypotheses are exactly the elementary prime conditions later supplied by
Ford's selected prime. -/
def fordIntegerSystemAboveModPrimePower
    {k d T p s : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    (hp : Nat.Prime p) (hs : 0 < s) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T) :
    FordPrimePowerTriangularPolynomialSystem p s (k - d) := by
  letI : NeZero (p ^ s) := ⟨pow_ne_zero s hp.ne_zero⟩
  letI : Fact (1 < p ^ s) :=
    ⟨one_lt_pow₀ hp.one_lt hs.ne'⟩
  let f : Fin (k - d) → (ZMod (p ^ s))[X] := fun j =>
    (ψ.poly (fordAboveIndex hdk j)).map (Int.castRingHom (ZMod (p ^ s)))
  refine ⟨f, ?_⟩
  intro j
  have hunit := fordIntegerPolynomialSystem_above_lc_isUnit
    ψ hp hs hk2 hkp hdk hpT j
  constructor
  · unfold f
    rw [natDegree_map_of_leadingCoeff_ne_zero
      (Int.castRingHom (ZMod (p ^ s))) hunit.ne_zero]
    exact ψ.degree_above _ (fordAboveIndex_above hdk j) |>.trans
      (fordAboveIndex_source_degree hdk j)
  · unfold f
    rw [leadingCoeff_map_of_leadingCoeff_ne_zero
      (Int.castRingHom (ZMod (p ^ s))) hunit.ne_zero]
    exact hunit

#print axioms fordIntegerPolynomialSystem_above_lc
#print axioms fordSourceLeadingNat_not_dvd
#print axioms fordIntegerPolynomialSystem_above_lc_isUnit
#print axioms fordIntegerSystemAboveModPrimePower

end

end GafniTao

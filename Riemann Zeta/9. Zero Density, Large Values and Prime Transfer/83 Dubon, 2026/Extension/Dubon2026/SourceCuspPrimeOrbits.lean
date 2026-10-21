import Dubon2026.SourceCuspBoundaryValues
import Dubon2026.HeckeUpperCosets
import Mathlib.GroupTheory.Transfer

/-! DUB-17/18 -> residual Galois association -> the original complex
boundary eigensystem -> the exact full Hecke action on actual cusp values.
The cusp action has one fixed coset and all other orbits of prime length.
This is the specific orbit calculation needed by the full original
transfer sum, with the existing Hecke subgroup and native coset action.
Adapted from the archived Apache-2.0 anthropics/fermats-last-theorem
revision 6e837e75355538c7f80bab5b956861e86c4eacc2, boundary-character proof.
-/
namespace Dubon2026.SourceCuspBoundary
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups
variable {N ℓ : ℕ}

/-- The original upper Hecke subgroup is exactly the integral upper-entry divisibility condition. -/
theorem mem_upper_iff {r : Gamma0 N} :
    r ∈ heckeUpperSubgroup N ℓ ↔ (ℓ : ℤ) ∣ (r : SL(2, ℤ)) 0 1 := by
  change ((r.val 0 1 : ℤ) : ZMod ℓ) = 0 ↔ _
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- The first coordinate of the actual conjugated cusp column. -/
def pOf (δ : SL(2, ℤ)) (r : Gamma0 N) : ℤ := ((r : SL(2, ℤ))⁻¹ * δ) 0 0

/-- The second coordinate of the actual conjugated cusp column. -/
def qOf (δ : SL(2, ℤ)) (r : Gamma0 N) : ℤ := ((r : SL(2, ℤ))⁻¹ * δ) 1 0

/-- The exact first coordinate after original integral inverse conjugation. -/
theorem pOf_eq (δ : SL(2, ℤ)) (r : Gamma0 N) :
    pOf δ r = (r : SL(2, ℤ)) 1 1 * δ 0 0 - (r : SL(2, ℤ)) 0 1 * δ 1 0 := by
  unfold pOf
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The exact second coordinate after original integral inverse conjugation. -/
theorem qOf_eq (δ : SL(2, ℤ)) (r : Gamma0 N) :
    qOf δ r = -(r : SL(2, ℤ)) 1 0 * δ 0 0 + (r : SL(2, ℤ)) 0 0 * δ 1 0 := by
  unfold qOf
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

variable (δ : SL(2, ℤ))

/-- The original cusp translation has the explicit integral unipotent matrix. -/
theorem coe_uOf_eq_unipMat :
    ((uOf N δ : Gamma0 N) : SL(2, ℤ)) = unipMat (δ 0 0) (δ 1 0) N :=
  conj_T_zpow_eq_unipMat δ N

/-- The exact integral matrix of every power of the original cusp element. -/
theorem coe_uOf_pow (n : ℕ) :
    ((uOf N δ ^ n : Gamma0 N) : SL(2, ℤ)) = unipMat (δ 0 0) (δ 1 0) ((N : ℤ) * n) := by
  rw [Subgroup.coe_pow, coe_uOf_eq_unipMat, unipMat_pow]

/-- The exact cusp matrix after original Hecke-coset conjugation. -/
theorem coe_inv_mul_pow_mul (r : Gamma0 N) (n : ℕ) :
    ((r⁻¹ * uOf N δ ^ n * r : Gamma0 N) : SL(2, ℤ)) =
      unipMat (pOf δ r) (qOf δ r) ((N : ℤ) * n) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_uOf_pow, inv_mul_unipMat_mul]
  rfl

/-- A conjugated cusp power lies in the actual Hecke subgroup exactly when its first column satisfies prime divisibility. -/
theorem inv_mul_pow_mul_mem_iff (r : Gamma0 N) (n : ℕ) :
    r⁻¹ * uOf N δ ^ n * r ∈ heckeUpperSubgroup N ℓ ↔ (ℓ : ℤ) ∣ (N : ℤ) * n * pOf δ r * pOf δ r := by
  rw [mem_upper_iff, coe_inv_mul_pow_mul, unipMat_apply_01]

/-- The original cusp action fixes a Hecke coset exactly at the derived divisibility condition. -/
theorem pow_smul_coe_eq_iff (r : Gamma0 N) (n : ℕ) :
    uOf N δ ^ n • ((r : Gamma0 N ⧸ heckeUpperSubgroup N ℓ)) = r ↔
      (ℓ : ℤ) ∣ (N : ℤ) * n * pOf δ r * pOf δ r := by
  rw [← inv_mul_pow_mul_mem_iff δ r n, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
    ← inv_mem_iff, _root_.mul_inv_rev, inv_inv]
  simp only [mul_assoc]

variable (hℓ : ℓ.Prime) (hδ : (ℓ : ℤ) ∣ δ 0 0) (hℓN : ¬ ℓ ∣ N)

include hℓ hδ in
/-- A prime dividing the first primitive cusp coordinate does not divide the second. -/
theorem not_dvd_e : ¬ (ℓ : ℤ) ∣ δ 1 0 := by
  intro he
  have h1 : (ℓ : ℤ) ∣ 1 := by
    obtain ⟨x, y, hxy⟩ := isCoprime_col δ
    rw [← hxy]; exact dvd_add (dvd_mul_of_dvd_right hδ _) (dvd_mul_of_dvd_right he _)
  exact (Nat.prime_iff_prime_int.mp hℓ).not_dvd_one h1

include hℓ hδ in
/-- The fixed cusp orbit is precisely the original upper Hecke subgroup coset. -/
theorem dvd_pOf_iff (r : Gamma0 N) : (ℓ : ℤ) ∣ pOf δ r ↔ r ∈ heckeUpperSubgroup N ℓ := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  rw [mem_upper_iff, pOf_eq]
  constructor
  · intro hp
    have h2 : (ℓ : ℤ) ∣ (r : SL(2, ℤ)) 0 1 * δ 1 0 := by
      have := dvd_sub (dvd_mul_of_dvd_right hδ ((r : SL(2, ℤ)) 1 1)) hp
      rwa [sub_sub_cancel] at this
    exact (hprime.dvd_or_dvd h2).resolve_right (not_dvd_e δ hℓ hδ)
  · intro hr
    exact dvd_sub (dvd_mul_of_dvd_right hδ _) (dvd_mul_of_dvd_left hr _)

include hℓ hδ hℓN in

/-- Every other original Hecke coset has cusp-orbit period exactly the prescribed prime. -/
theorem minimalPeriod_eq (r : Gamma0 N) (hr : r ∉ heckeUpperSubgroup N ℓ) :
    Function.minimalPeriod (uOf N δ • ·) ((r : Gamma0 N ⧸ heckeUpperSubgroup N ℓ)) = ℓ := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp : ¬ (ℓ : ℤ) ∣ pOf δ r := fun h' => hr ((dvd_pOf_iff δ hℓ hδ r).mp h')
  have hNℓ : ¬ (ℓ : ℤ) ∣ (N : ℤ) := fun h => hℓN (Int.natCast_dvd_natCast.mp h)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  apply Function.minimalPeriod_eq_prime
  · rw [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate]
    exact (pow_smul_coe_eq_iff (ℓ := ℓ) δ r ℓ).mpr
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)
  · rw [Function.IsFixedPt]
    intro hfix
    have := (pow_smul_coe_eq_iff (ℓ := ℓ) δ r 1).mp (by simpa using hfix)
    simp only [Nat.cast_one, mul_one] at this
    rcases hprime.dvd_or_dvd this with h1 | h1
    · rcases hprime.dvd_or_dvd h1 with h2 | h2
      · exact hNℓ h2
      · exact hp h2
    · exact hp h1

/-- The actual orbit quotient of the cusp cyclic subgroup on original Hecke cosets. -/
abbrev OrbQ (N : ℕ) (ℓ : ℕ) (u : Gamma0 N) : Type :=
  Quotient (MulAction.orbitRel (Subgroup.zpowers u) (Gamma0 N ⧸ heckeUpperSubgroup N ℓ))

/-- The distinguished cusp orbit containing the actual identity Hecke coset. -/
def orbOne (N : ℕ) (ℓ : ℕ) (u : Gamma0 N) : OrbQ N ℓ u :=
  Quotient.mk _ (((1 : Gamma0 N) : Gamma0 N ⧸ heckeUpperSubgroup N ℓ))

/-- When the cusp element lies in the upper subgroup, its identity orbit is the literal identity coset. -/
theorem orbOne_out (u : Gamma0 N) (huK : u ∈ heckeUpperSubgroup N ℓ) :
    (orbOne N ℓ u).out = (((1 : Gamma0 N) : Gamma0 N ⧸ heckeUpperSubgroup N ℓ)) := by
  have hrel : (orbOne N ℓ u).out ∈ MulAction.orbit (Subgroup.zpowers u)
      (((1 : Gamma0 N) : Gamma0 N ⧸ heckeUpperSubgroup N ℓ)) :=
    MulAction.orbitRel_apply.mp (Quotient.mk_out _)
  obtain ⟨z, hz⟩ := MulAction.mem_orbit_iff.mp hrel
  rw [← hz]
  change ((((z : Gamma0 N) * 1 : Gamma0 N) : Gamma0 N ⧸ heckeUpperSubgroup N ℓ)) = _
  rw [mul_one, QuotientGroup.eq, mul_one]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
  rw [← hk]
  exact inv_mem (Subgroup.zpow_mem _ huK k)

/-- The chosen representative of the distinguished orbit lies in the original Hecke subgroup. -/
theorem orbOne_out_out_mem (u : Gamma0 N) (huK : u ∈ heckeUpperSubgroup N ℓ) :
    (orbOne N ℓ u).out.out ∈ heckeUpperSubgroup N ℓ := by
  have h1 : (((orbOne N ℓ u).out.out : Gamma0 N) : Gamma0 N ⧸ heckeUpperSubgroup N ℓ) =
      ((1 : Gamma0 N) : Gamma0 N ⧸ heckeUpperSubgroup N ℓ) := by
    rw [QuotientGroup.out_eq', orbOne_out u huK]
  have := QuotientGroup.eq.mp h1.symm
  rwa [inv_one, one_mul] at this

/-- Any orbit represented inside the original Hecke subgroup is the distinguished orbit. -/
theorem eq_orbOne_of_mem (u : Gamma0 N) (O : OrbQ N ℓ u)
    (hO : O.out.out ∈ heckeUpperSubgroup N ℓ) : O = orbOne N ℓ u := by
  have h1 : O.out = ((1 : Gamma0 N) : Gamma0 N ⧸ heckeUpperSubgroup N ℓ) := by
    rw [← QuotientGroup.out_eq' O.out]
    symm
    exact QuotientGroup.eq.mpr (by rwa [inv_one, one_mul])
  rw [← Quotient.out_eq O, h1]
  rfl

/-- The distinguished original cusp orbit has exact period one. -/
theorem minimalPeriod_orbOne_out (u : Gamma0 N) (huK : u ∈ heckeUpperSubgroup N ℓ) :
    Function.minimalPeriod (u • ·) (orbOne N ℓ u).out = 1 := by
  rw [orbOne_out u huK, Function.minimalPeriod_eq_one_iff_isFixedPt, Function.IsFixedPt,
    MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
  exact inv_mem huK

include hδ in
/-- Divisibility of the original cusp column puts its translation in the upper Hecke subgroup. -/
theorem uOf_mem_upper : uOf N δ ∈ heckeUpperSubgroup N ℓ := by
  rw [mem_upper_iff, coe_uOf_eq_unipMat, unipMat_apply_01]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hδ _) _


end
end Dubon2026.SourceCuspBoundary

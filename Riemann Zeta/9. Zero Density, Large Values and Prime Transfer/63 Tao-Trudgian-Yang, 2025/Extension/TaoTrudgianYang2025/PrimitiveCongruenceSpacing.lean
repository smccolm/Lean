import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! Primitive congruence-lattice spacing for the arithmetic lemma in
Robert--Sargos (2002). The coefficient primitivity is an actual integer gcd. -/

namespace TaoTrudgianYang2025

theorem primitive_linear_congruence_determinant_dvd
    {a b c u₁ v₁ u₂ v₂ : ℤ}
    (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1)
    (h₁ : c ∣ a*u₁+b*v₁) (h₂ : c ∣ a*u₂+b*v₂) :
    c ∣ u₁*v₂-u₂*v₁ := by
  let D := u₁*v₂-u₂*v₁
  have ha : c ∣ a*D := by
    convert dvd_sub (dvd_mul_of_dvd_left h₁ v₂) (dvd_mul_of_dvd_left h₂ v₁) using 1
    dsimp [D]
    ring
  have hb : c ∣ b*D := by
    convert dvd_sub (dvd_mul_of_dvd_left h₂ u₁) (dvd_mul_of_dvd_left h₁ u₂) using 1
    dsimp [D]
    ring
  have hg : c ∣ (Int.gcd a b : ℤ)*D := by
    rw [Int.gcd_eq_gcd_ab]
    convert dvd_add (dvd_mul_of_dvd_left ha (Int.gcdA a b))
      (dvd_mul_of_dvd_left hb (Int.gcdB a b)) using 1
    ring
  have hlast : c ∣ (Int.gcd (Int.gcd a b : ℤ) c : ℤ)*D := by
    rw [Int.gcd_eq_gcd_ab]
    convert dvd_add (dvd_mul_of_dvd_left hg (Int.gcdA (Int.gcd a b : ℤ) c))
      (dvd_mul_right c (Int.gcdB (Int.gcd a b : ℤ) c*D)) using 1
    ring
  simpa only [hprim,Int.natCast_one,one_mul,D] using hlast

theorem primitive_fraction_coordinates_eq {u₁ v₁ u₂ v₂ : ℤ}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hp₁ : Nat.Coprime u₁.natAbs v₁.natAbs)
    (hp₂ : Nat.Coprime u₂.natAbs v₂.natAbs)
    (h : (u₁:ℝ)/v₁ = (u₂:ℝ)/v₂) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  have hd₁ : (v₁:ℝ) ≠ 0 := by exact_mod_cast hv₁.ne'
  have hd₂ : (v₂:ℝ) ≠ 0 := by exact_mod_cast hv₂.ne'
  have hm : u₁*v₂ = u₂*v₁ := by
    exact_mod_cast (div_eq_div_iff hd₁ hd₂).mp h
  apply Rat.div_int_inj hv₁ hv₂ hp₁ hp₂
  apply (div_eq_div_iff (by exact_mod_cast hv₁.ne') (by exact_mod_cast hv₂.ne')).mpr
  exact_mod_cast hm

theorem primitive_fraction_determinant_ne_zero {u₁ v₁ u₂ v₂ : ℤ}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hp₁ : Nat.Coprime u₁.natAbs v₁.natAbs)
    (hp₂ : Nat.Coprime u₂.natAbs v₂.natAbs)
    (hne : (u₁,v₁) ≠ (u₂,v₂)) :
    u₁*v₂-u₂*v₁ ≠ 0 := by
  intro hz
  have hm : (u₁:ℝ)*(v₂:ℝ) = (u₂:ℝ)*(v₁:ℝ) := by
    exact_mod_cast (sub_eq_zero.mp hz)
  have he := primitive_fraction_coordinates_eq hv₁ hv₂ hp₁ hp₂
    ((div_eq_div_iff (by exact_mod_cast hv₁.ne') (by exact_mod_cast hv₂.ne')).mpr hm)
  exact hne (Prod.ext he.1 he.2)

theorem primitive_linear_congruence_ratio_spacing
    {a b c u₁ v₁ u₂ v₂ : ℤ} {V : ℝ}
    (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1) (hc : 0 < c) (hV : 0 < V)
    (hv₁ : V ≤ (v₁:ℝ)) (hv₂ : V ≤ (v₂:ℝ))
    (hv₁u : (v₁:ℝ) ≤ 2*V) (hv₂u : (v₂:ℝ) ≤ 2*V)
    (hp₁ : Nat.Coprime u₁.natAbs v₁.natAbs)
    (hp₂ : Nat.Coprime u₂.natAbs v₂.natAbs)
    (h₁ : c ∣ a*u₁+b*v₁) (h₂ : c ∣ a*u₂+b*v₂)
    (hne : (u₁,v₁) ≠ (u₂,v₂)) :
    (c:ℝ)/(4*V^2) ≤ |(u₁:ℝ)/v₁-(u₂:ℝ)/v₂| := by
  have hv₁p : 0 < (v₁:ℝ) := hV.trans_le hv₁
  have hv₂p : 0 < (v₂:ℝ) := hV.trans_le hv₂
  have hv₁z : 0 < v₁ := by exact_mod_cast hv₁p
  have hv₂z : 0 < v₂ := by exact_mod_cast hv₂p
  have hdvd := primitive_linear_congruence_determinant_dvd hprim h₁ h₂
  have hneD := primitive_fraction_determinant_ne_zero hv₁z hv₂z hp₁ hp₂ hne
  have hD : c ≤ |u₁*v₂-u₂*v₁| := by
    obtain ⟨t,ht⟩ := hdvd
    have htn : t ≠ 0 := by intro hz; simp [hz] at ht; exact hneD ht
    have ht1 : 1 ≤ |t| := by have htpos := abs_pos.mpr htn; omega
    rw [ht,abs_mul,abs_of_pos hc]
    nlinarith
  have hDr : (c:ℝ) ≤ |((u₁*v₂-u₂*v₁:ℤ):ℝ)| := by exact_mod_cast hD
  have hprod : 0 < (v₁:ℝ)*v₂ := mul_pos hv₁p hv₂p
  have hprodu : (v₁:ℝ)*v₂ ≤ 4*V^2 := by
    have hm := mul_le_mul hv₁u hv₂u hv₂p.le (by positivity : 0 ≤ 2*V)
    nlinarith only [hm]
  have he : (u₁:ℝ)/v₁-(u₂:ℝ)/v₂ =
      ((u₁*v₂-u₂*v₁:ℤ):ℝ)/((v₁:ℝ)*v₂) := by
    push_cast
    field_simp
  rw [he,abs_div,abs_of_pos hprod]
  calc
    _ ≤ (c:ℝ)/((v₁:ℝ)*v₂) :=
      div_le_div_of_nonneg_left (by exact_mod_cast hc.le) hprod hprodu
    _ ≤ _ := div_le_div_of_nonneg_right hDr hprod.le

end TaoTrudgianYang2025

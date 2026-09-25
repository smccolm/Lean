import TaoTrudgianYang2025.PrimitiveTripleGcd

/-! Exact finite counts on a fixed gcd fiber of primitive integer triples. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem primitive_linear_triple_gcd_fiber_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {a b c : ℤ} {g : ℕ} {V α β : ℝ}
    (hcoeff : Int.gcd (Int.gcd a b : ℤ) c = 1) (hc : 0 < c)
    (hg : 0 < g) (hgc : (g:ℤ) ∣ c) (hV : 0 < V) (hαβ : α ≤ β)
    (hgcd : ∀ p ∈ S, Int.gcd p.1 p.2.1 = g)
    (hden : ∀ p ∈ S, V ≤ (p.2.1:ℝ) ∧ (p.2.1:ℝ) ≤ 2*V)
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1)
    (hline : ∀ p ∈ S, a*p.1+b*p.2.1+c*p.2.2 = 0)
    (hratio : ∀ p ∈ S, α ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ β) :
    (S.card:ℝ) ≤ 1+4*V^2*(β-α)/((c:ℝ)*g) := by
  classical
  have hgz : (0:ℤ) < g := by exact_mod_cast hg
  have hgr : (0:ℝ) < g := by exact_mod_cast hg
  have hcr : (0:ℝ) < c := by exact_mod_cast hc
  let f : ℤ × ℤ × ℤ → ℤ × ℤ := fun p => (p.1/g,p.2.1/g)
  let W := S.image f
  have hdu : ∀ p ∈ S, (g:ℤ) ∣ p.1 := by
    intro p hp
    rw [← hgcd p hp]
    exact Int.gcd_dvd_left _ _
  have hdv : ∀ p ∈ S, (g:ℤ) ∣ p.2.1 := by
    intro p hp
    rw [← hgcd p hp]
    exact Int.gcd_dvd_right _ _
  have huc : ∀ p ∈ S, (((f p).1:ℤ):ℝ) = (p.1:ℝ)/g := by
    intro p hp
    apply (eq_div_iff hgr.ne').mpr
    exact_mod_cast Int.ediv_mul_cancel (hdu p hp)
  have hvc : ∀ p ∈ S, (((f p).2:ℤ):ℝ) = (p.2.1:ℝ)/g := by
    intro p hp
    apply (eq_div_iff hgr.ne').mpr
    exact_mod_cast Int.ediv_mul_cancel (hdv p hp)
  have hinj : Set.InjOn f S := by
    intro p hp q hq he
    have heu : p.1 = q.1 := by
      have hh := congrArg (fun t : ℤ × ℤ => t.1*(g:ℤ)) he
      simpa only [f,Int.ediv_mul_cancel (hdu p hp),Int.ediv_mul_cancel (hdu q hq)] using hh
    have hev : p.2.1 = q.2.1 := by
      have hh := congrArg (fun t : ℤ × ℤ => t.2*(g:ℤ)) he
      simpa only [f,Int.ediv_mul_cancel (hdv p hp),Int.ediv_mul_cancel (hdv q hq)] using hh
    have hew : p.2.2 = q.2.2 := by
      have hp' := hline p hp
      have hq' := hline q hq
      rw [heu,hev] at hp'
      nlinarith
    exact Prod.ext heu (Prod.ext hev hew)
  have hm : 0 < c/(g:ℤ) := Int.ediv_pos_of_pos_of_dvd hc hgz.le hgc
  have hmod := primitive_coefficients_of_modulus_dvd hcoeff (Int.ediv_dvd_of_dvd hgc)
  have hWden : ∀ p ∈ W, V/(g:ℝ) ≤ (p.2:ℝ) ∧ (p.2:ℝ) ≤ 2*(V/g) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [hvc q hq]
    constructor
    · exact div_le_div_of_nonneg_right (hden q hq).1 hgr.le
    · simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (hden q hq).2 hgr.le
  have hWprim : ∀ p ∈ W, Nat.Coprime p.1.natAbs p.2.natAbs := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    change Int.gcd (q.1/(g:ℤ)) (q.2.1/(g:ℤ)) = 1
    rw [← hgcd q hq]
    exact Int.gcd_ediv_gcd_ediv_gcd (by rw [hgcd q hq]; exact hg)
  have hWcong : ∀ p ∈ W, (c/(g:ℤ)) ∣ a*p.1+b*p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hv : 0 < q.2.1 := by exact_mod_cast hV.trans_le (hden q hq).1
    have hh := primitive_linear_triple_normalized_congruence hv (hprim q hq) (hline q hq)
    simpa only [hgcd q hq,f] using hh
  have hWratio : ∀ p ∈ W, α ≤ (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 ≤ β := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [huc q hq,hvc q hq,div_div_div_cancel_right₀ hgr.ne']
    exact hratio q hq
  have hb := primitive_congruence_card_le W hmod hm (div_pos hV hgr) hαβ
    hWden hWprim hWcong hWratio
  have hcard : W.card = S.card := Finset.card_image_of_injOn hinj
  have hmc : ((c/(g:ℤ):ℤ):ℝ) = (c:ℝ)/g := by
    apply (eq_div_iff hgr.ne').mpr
    exact_mod_cast Int.ediv_mul_cancel hgc
  rw [hcard,hmc] at hb
  calc
    (S.card:ℝ) ≤ 1+4*(V/(g:ℝ))^2*(β-α)/((c:ℝ)/g) := hb
    _ = 1+4*V^2*(β-α)/((c:ℝ)*g) := by field_simp

end TaoTrudgianYang2025

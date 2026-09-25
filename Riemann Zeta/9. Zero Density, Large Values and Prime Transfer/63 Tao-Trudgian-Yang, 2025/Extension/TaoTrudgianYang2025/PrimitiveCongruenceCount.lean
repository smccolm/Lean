import TaoTrudgianYang2025.PrimitiveCongruenceSpacing
import TaoTrudgianYang2025.AdditiveEnergy

/-! Finite primitive congruence counts from actual rational spacing. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem primitive_congruence_card_le (S : Finset (ℤ × ℤ))
    {a b c : ℤ} {V α β : ℝ}
    (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1) (hc : 0 < c)
    (hV : 0 < V) (hαβ : α ≤ β)
    (hden : ∀ p ∈ S, V ≤ (p.2:ℝ) ∧ (p.2:ℝ) ≤ 2*V)
    (hpair : ∀ p ∈ S, Nat.Coprime p.1.natAbs p.2.natAbs)
    (hcong : ∀ p ∈ S, c ∣ a*p.1+b*p.2)
    (hratio : ∀ p ∈ S, α ≤ (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 ≤ β) :
    (S.card:ℝ) ≤ 1+4*V^2*(β-α)/c := by
  classical
  let ε : ℝ := (c:ℝ)/(4*V^2)
  have hcp : (0:ℝ) < c := by exact_mod_cast hc
  have hε : 0 < ε := div_pos hcp (by positivity)
  let f : ℤ × ℤ → ℝ := fun p => ((p.1:ℝ)/p.2)/ε
  let W := S.image f
  have hinj : Set.InjOn f S := by
    intro p hp q hq he
    have hpe : 0 < p.2 := by exact_mod_cast (hV.trans_le (hden p hp).1)
    have hqe : 0 < q.2 := by exact_mod_cast (hV.trans_le (hden q hq).1)
    have hmul := congrArg (fun x : ℝ => x*ε) he
    dsimp [f] at hmul
    simp only [div_mul_cancel₀ _ hε.ne'] at hmul
    have heq := primitive_fraction_coordinates_eq hpe hqe (hpair p hp) (hpair q hq) hmul
    exact Prod.ext heq.1 heq.2
  have hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x-y| := by
    intro x hx y hy hxy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    have hpq : (p.1,p.2) ≠ (q.1,q.2) := by
      intro he
      apply hxy
      exact congrArg f (Prod.ext (congrArg Prod.fst he) (congrArg Prod.snd he))
    have hs := primitive_linear_congruence_ratio_spacing hprim hc hV
      (hden p hp).1 (hden q hq).1 (hden p hp).2 (hden q hq).2
      (hpair p hp) (hpair q hq) (hcong p hp) (hcong q hq) hpq
    change 1 ≤ |((p.1:ℝ)/p.2)/ε-((q.1:ℝ)/q.2)/ε|
    rw [← sub_div,abs_div,abs_of_pos hε]
    apply (le_div_iff₀ hε).mpr
    simpa only [one_mul,ε] using hs
  have hmem : ∀ x ∈ W, α/ε ≤ x ∧ x ≤ β/ε := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨div_le_div_of_nonneg_right (hratio p hp).1 hε.le,
      div_le_div_of_nonneg_right (hratio p hp).2 hε.le⟩
  have hb := oneSeparated_card_cast_le_interval_length_add_one W hsep
    (sub_nonneg.mpr (div_le_div_of_nonneg_right hαβ hε.le)) hmem
  have hcard : W.card = S.card := Finset.card_image_of_injOn hinj
  rw [hcard] at hb
  calc
    (S.card:ℝ) ≤ β/ε-α/ε+1 := hb
    _ = 1+4*V^2*(β-α)/c := by dsimp [ε]; field_simp; ring

end TaoTrudgianYang2025

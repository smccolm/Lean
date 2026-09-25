import TaoTrudgianYang2025.PrimitiveDivisorGrowth
import TaoTrudgianYang2025.RobertSargosSameSignCount

/-! Uniform epsilon loss for the original fixed-coefficient branch. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_fixed_coeff_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (H Q δ : ℝ),
      0 < n → 0 < H → (n:ℝ) ≤ H → 0 ≤ δ →
      2*(n.divisors.card:ℝ)+
        64*δ*Q^2/(H*(n:ℝ))*(∑ g ∈ n.divisors, (g:ℝ)) ≤
      C*H^ε*(1+δ*Q^2/H) := by
  obtain ⟨D,hD,hdiv⟩ := RiemannZeta.GuthMaynard.divisorCountBound_native ε hε
  refine ⟨64*D,by positivity,?_⟩
  intro n H Q δ hn hH hnH hδ
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have ht : (n.divisors.card:ℝ) ≤ D*H^ε :=
    (hdiv n hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hnp.le hnH hε.le) hD.le)
  have hτ : (0:ℝ) ≤ n.divisors.card := by positivity
  have hX : 0 ≤ δ*Q^2/H := by positivity
  calc
    _ ≤ 2*(n.divisors.card:ℝ)+
        64*δ*Q^2/(H*(n:ℝ))*((n:ℝ)*(n.divisors.card:ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_divisors_cast_le_mul_card n)
        (by positivity : 0 ≤ 64*δ*Q^2/(H*(n:ℝ))))
    _ = (n.divisors.card:ℝ)*(2+64*(δ*Q^2/H)) := by field_simp
    _ ≤ (n.divisors.card:ℝ)*(64*(1+δ*Q^2/H)) :=
      mul_le_mul_of_nonneg_left (by linarith) hτ
    _ ≤ (D*H^ε)*(64*(1+δ*Q^2/H)) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    _ = _ := by ring

theorem exists_robertSargos_fixed_coeff_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (ℤ × ℤ × ℤ)) (r h₁ h₂ : ℤ) (H Q δ : ℝ),
      Int.gcd (Int.gcd r h₁ : ℤ) h₂ = 1 → r ≠ 0 →
      0 < H → 0 < Q → 0 ≤ δ →
      |(r:ℝ)| ≤ H/2 → H ≤ (h₁:ℝ) → H ≤ (h₂:ℝ) →
      (∀ p ∈ S, |(p.2.1:ℝ)| ∈ Set.Icc Q (2*Q)) →
      (∀ p ∈ S, Q ≤ |(p.1:ℝ)|) →
      (∀ p ∈ S, 0 < p.2.1*p.1) →
      (∀ p ∈ S, Int.gcd (Int.gcd p.2.2 p.2.1 : ℤ) p.1 = 1) →
      (∀ p ∈ S, r*p.2.2+h₁*p.2.1-h₂*p.1 = 0) →
      (∀ p ∈ S, |robertSargosReduced r p.2.1 p.1 h₁ h₂ p.2.2| ≤ δ*H*Q^2) →
      (S.card:ℝ) ≤ C*H^ε*(1+δ*Q^2/H) := by
  obtain ⟨C,hC,hdiv⟩ := exists_robertSargos_fixed_coeff_divisor_bound ε hε
  refine ⟨C,hC,?_⟩
  intro S r h₁ h₂ H Q δ hc hr hH hQ hδ hrH hh₁ hh₂ hq₁ hq₂ hs hp hl hn
  have hrc : (r.natAbs:ℝ) = |(r:ℝ)| := by
    simpa only [Int.cast_natCast,Int.cast_abs] using
      congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs r)
  have hrH' : (r.natAbs:ℝ) ≤ H := by rw [hrc]; linarith
  have hb := robertSargos_primitive_fixed_coeff_card_le S hc hr hH hQ hδ hrH
    hh₁ hh₂ hq₁ hq₂ hs hp hl hn
  rw [← hrc] at hb
  exact hb.trans (hdiv r.natAbs H Q δ (Int.natAbs_pos.mpr hr) hH hrH' hδ)

end TaoTrudgianYang2025

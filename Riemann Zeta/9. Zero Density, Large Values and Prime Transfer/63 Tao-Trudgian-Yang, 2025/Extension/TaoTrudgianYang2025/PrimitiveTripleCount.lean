import TaoTrudgianYang2025.PrimitiveTripleGcdFiber

/-! Robert--Sargos (2002), Lemma 5: the actual primitive-triple count,
with explicit divisor sums and constant four. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem primitive_linear_triple_card_le_divisor_sum
    (S : Finset (ℤ × ℤ × ℤ)) {a b : ℤ} {c : ℕ} {V α β : ℝ}
    (hcoeff : Int.gcd (Int.gcd a b : ℤ) c = 1) (hc : 0 < c)
    (hV : 0 < V) (hαβ : α ≤ β)
    (hden : ∀ p ∈ S, V ≤ (p.2.1:ℝ) ∧ (p.2.1:ℝ) ≤ 2*V)
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1)
    (hline : ∀ p ∈ S, a*p.1+b*p.2.1+(c:ℤ)*p.2.2 = 0)
    (hratio : ∀ p ∈ S, α ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ β) :
    (S.card:ℝ) ≤ ∑ g ∈ c.divisors, (1+4*V^2*(β-α)/((c:ℝ)*g)) := by
  classical
  let f : ℤ × ℤ × ℤ → ℕ := fun p => Int.gcd p.1 p.2.1
  have hmaps : Set.MapsTo f S c.divisors := by
    intro p hp
    apply Nat.mem_divisors.mpr
    refine ⟨?_,hc.ne'⟩
    exact Int.natCast_dvd_natCast.mp (primitive_linear_triple_gcd_dvd
      (hprim p hp) (hline p hp))
  have hcard : S.card = ∑ g ∈ c.divisors, (S.filter (fun p => f p = g)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (S.card:ℝ) = ∑ g ∈ c.divisors, ((S.filter (fun p => f p = g)).card:ℝ) := by
      exact_mod_cast hcard
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro g hg
      have hgc : (g:ℤ) ∣ (c:ℤ) := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_divisors hg)
      have hb := primitive_linear_triple_gcd_fiber_card_le
        (S.filter (fun p => f p = g)) hcoeff (by exact_mod_cast hc)
        (Nat.pos_of_mem_divisors hg) hgc hV hαβ
        (fun p hp => (Finset.mem_filter.mp hp).2)
        (fun p hp => hden p (Finset.mem_filter.mp hp).1)
        (fun p hp => hprim p (Finset.mem_filter.mp hp).1)
        (fun p hp => hline p (Finset.mem_filter.mp hp).1)
        (fun p hp => hratio p (Finset.mem_filter.mp hp).1)
      simpa only [Int.cast_natCast] using hb

theorem primitive_divisor_bound_identity {c : ℕ} (hc : 0 < c) (K : ℝ) :
    (∑ g ∈ c.divisors, (1+K/((c:ℝ)*g))) =
      (c.divisors.card:ℝ)+K/(c:ℝ)^2*(∑ g ∈ c.divisors, (g:ℝ)) := by
  have hcr : (0:ℝ) < c := by exact_mod_cast hc
  calc
    _ = ∑ g ∈ c.divisors, (1+K/(c:ℝ)^2*(c/g:ℕ)) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hgr : (0:ℝ) < g := by exact_mod_cast Nat.pos_of_mem_divisors hg
      have he : ((c/g:ℕ):ℝ)*(g:ℝ) = c := by
        exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hg)
      congr 1
      field_simp
      nlinarith only [congrArg (fun x : ℝ => K*x) he]
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Nat.sum_div_divisors]
      simp

theorem primitive_linear_triple_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {a b : ℤ} {c : ℕ} {V α β : ℝ}
    (hcoeff : Int.gcd (Int.gcd a b : ℤ) c = 1) (hc : 0 < c)
    (hV : 0 < V) (hαβ : α ≤ β)
    (hden : ∀ p ∈ S, V ≤ (p.2.1:ℝ) ∧ (p.2.1:ℝ) ≤ 2*V)
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.1 p.2.1 : ℤ) p.2.2 = 1)
    (hline : ∀ p ∈ S, a*p.1+b*p.2.1+(c:ℤ)*p.2.2 = 0)
    (hratio : ∀ p ∈ S, α ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ β) :
    (S.card:ℝ) ≤ (c.divisors.card:ℝ)+
      4*V^2*(β-α)/(c:ℝ)^2*(∑ g ∈ c.divisors, (g:ℝ)) := by
  have hb := primitive_linear_triple_card_le_divisor_sum S hcoeff hc hV hαβ
    hden hprim hline hratio
  rwa [primitive_divisor_bound_identity hc] at hb

end TaoTrudgianYang2025

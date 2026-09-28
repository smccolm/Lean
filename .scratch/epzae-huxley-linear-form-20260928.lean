import TaoTrudgianYang2025
import TaoTrudgianYang2025.HuxleyLinearForms
import TaoTrudgianYang2025.HuxleyLinearForms

#print axioms TaoTrudgianYang2025.HuxleyLinearForm.small_denominator_integer_identity
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.card_mul_le_of_dvd
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.small_denominator_branch
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.exists_reduced_approximation
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fixed_residual_separated
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fixed_residual_card_bound
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.large_denominator_branch
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.linear_form_dichotomy
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.linear_form_dichotomy_round
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.maximal_denominator_determinant_injective
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.determinant_alpha_near
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.determinant_beta_near
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.exists_right_neighbor
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.exists_left_neighbor
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.mem_fareySector_iff
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_exists_unit_determinant
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.card_le_two_mul_nonzero_abs_card_add_one
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.small_error_integer_of_unit_determinant
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_determinant_bound
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_small_error_bounds
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_one_one_two
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.printed_exact_integrality_counterexample

namespace HuxleyLinearFormRegression

open TaoTrudgianYang2025.HuxleyLinearForm

example
    (S : Finset ℕ) {N : ℕ} {α δ : ℝ}
    (hne : S.Nonempty) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ N)
    (hnear : ∀ n ∈ S, |(n:ℝ)*α-(round ((n:ℝ)*α):ℤ)| ≤ δ) :
    (S.card:ℝ) ≤ 12*δ*N ∨
      ∃ q : ℕ, 0 < q ∧ (q:ℝ) ≤ (N:ℝ)/S.card ∧
        |(q:ℝ)*α-(round ((q:ℝ)*α):ℤ)| ≤ δ/S.card ∧
        ∀ n ∈ S, q ∣ n :=
  linear_form_dichotomy_round S hne hN hδ hS hnear

example {m₀ n₀ : ℤ}
    (hn₀ : 0 < n₀) (hcop : IsCoprime m₀ n₀) :
    ∃ a b : ℤ, 1 ≤ b ∧ b ≤ n₀ ∧ IsCoprime a b ∧
      m₀*b-n₀*a = -1 ∧
      ∀ m n : ℤ, 1 ≤ n → n ≤ n₀ → m₀*n < n₀*m → a*n ≤ m*b :=
  exists_right_neighbor hn₀ hcop

example {N : ℕ} {l μ : ℝ} {p : ℤ × ℤ}
    (hl : 0 < l) (hμ : 0 ≤ μ) :
    p ∈ fareySector N l μ ↔ 1 ≤ p.2 ∧ p.2 ≤ N ∧
      IsCoprime p.1 p.2 ∧ l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ μ*p.2 :=
  mem_fareySector_iff hl hμ

example
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hsmall : (μ*(N:ℝ))*δ ≤ 1/(96*B))
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card ∧
    |β-(round β:ℤ)| ≤ 8*(μ*(N:ℝ))*δ/(fareySector N l μ).card :=
  fareySector_small_error_bounds hl hμ hB hδ hR hsmall hnear

example : fareySector 1 1 2 = {(1,1),(2,1)} :=
  fareySector_one_one_two

example :
    max (((2:ℝ)-1)*1^2/1) 2 ≤ ((fareySector 1 1 2).card:ℝ) ∧
    (2:ℝ)*1*(1/1000) ≤ 1/(96*1) ∧
    (∀ p ∈ fareySector 1 1 2,
      ∃ b : ℤ, |(p.1:ℝ)*(1/2000)+(p.2:ℝ)*0-b| ≤ 1/1000) ∧
    ¬∃ k : ℤ, (1/2000:ℝ)=k :=
  printed_exact_integrality_counterexample

end HuxleyLinearFormRegression

namespace HuxleySectorContinuation

open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyLinearForm

/-- Exact numerator count on one genuine denominator fiber of (2.3).
This is an elementary upper bound, not the missing Farey density lower bound. -/
theorem denominator_fiber_card
    {N : ℕ} {l μ : ℝ} (hl : 0 < l) (hlμ : l ≤ μ)
    {n : ℤ} (hn : 0 ≤ n) :
    (((fareySector N l μ).filter (fun p => p.2=n)).card:ℝ) ≤ (μ-l)*(n:ℝ)+1 := by
  classical
  let T := (fareySector N l μ).filter (fun p => p.2=n)
  let A := T.image Prod.fst
  have hcard : A.card=T.card := Finset.card_image_of_injOn (by
    intro p hp q hq he
    exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm))
  have hμ : 0 ≤ μ := hl.le.trans hlμ
  have hnR : (0:ℝ) ≤ n := by exact_mod_cast hn
  have hrad : 0 ≤ (μ-l)*(n:ℝ)/2 := by positivity
  have hnear : ∀ m ∈ A, |(m:ℝ)-(l+μ)*(n:ℝ)/2| ≤ (μ-l)*(n:ℝ)/2 := by
    intro m hm
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hpS,hpn⟩ := Finset.mem_filter.mp hp
    obtain ⟨_hpn,_hpN,_hc,hlower,hupper⟩ := (mem_fareySector_iff hl hμ).mp hpS
    rw [hpn] at hlower hupper
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have h := integer_card_le_of_abs_sub_le A hrad hnear
  rw [hcard] at h
  change (T.card:ℝ) ≤ _
  linarith

#print axioms denominator_fiber_card

end HuxleySectorContinuation

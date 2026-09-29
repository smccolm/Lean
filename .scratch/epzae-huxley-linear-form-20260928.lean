import TaoTrudgianYang2025
import TaoTrudgianYang2025.HuxleyLinearForms
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Order.Preorder.Finite

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

#print axioms TaoTrudgianYang2025.HuxleyLinearForm.denominator_fiber_card
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_card_le
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.large_sector_width
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.prime_coprime_consecutive
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.large_sector_consecutive_numerators
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_consecutive_numerators
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.large_sector_alpha_bound
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_denominator_card_lower
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_denominator_common_divisor
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_card_le_twice_rectangle
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.sector_beta_bound
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_bounded_density_dichotomy
#print axioms TaoTrudgianYang2025.HuxleyLinearForm.fareySector_integer_labels

namespace HuxleyFareyDensity

open TaoTrudgianYang2025

theorem sum_nonunit_inverse_square_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 2 N, 1/(d:ℝ)^2) ≤ 3/4 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.sum_nonunit_inverse_square_le N

#print axioms sum_nonunit_inverse_square_le

/-- A uniform positive proportion of the actual integer square is primitive.
This supplies the mean totient input for the alternate density route. -/
theorem coprime_square_card_lower (N : ℕ) :
    (N:ℝ)^2/4 ≤
      ((((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
        (fun p => Nat.Coprime p.1 p.2)).card:ℝ) := by
  classical
  let A := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  let G := A.filter (fun p => Nat.Coprime p.1 p.2)
  let F := A.filter (fun p => ¬Nat.Coprime p.1 p.2)
  let U : ℕ → Finset (ℕ × ℕ) := fun d =>
    ((Finset.Icc 1 (N/d)) ×ˢ (Finset.Icc 1 (N/d))).image
      (fun p => (d*p.1,d*p.2))
  have hcover : F ⊆ (Finset.Icc 2 N).biUnion U := by
    intro p hp
    obtain ⟨hpA,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpA
    obtain ⟨hp₁pos,hp₁N⟩ := Finset.mem_Icc.mp hp₁
    obtain ⟨hp₂pos,hp₂N⟩ := Finset.mem_Icc.mp hp₂
    let d := Nat.gcd p.1 p.2
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left p.2 hp₁pos
    have hdne : d ≠ 1 := hbad
    have hdN : d ≤ N := (Nat.gcd_le_left p.2 hp₁pos).trans hp₁N
    have hd₁ : d ∣ p.1 := Nat.gcd_dvd_left _ _
    have hd₂ : d ∣ p.2 := Nat.gcd_dvd_right _ _
    apply Finset.mem_biUnion.mpr
    refine ⟨d,Finset.mem_Icc.mpr ⟨by omega,hdN⟩,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(p.1/d,p.2/d),Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp₁pos hd₁) hdpos,
        Nat.div_le_div_right hp₁N⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hp₂pos hd₂) hdpos,
        Nat.div_le_div_right hp₂N⟩
    · exact Prod.ext (Nat.mul_div_cancel' hd₁) (Nat.mul_div_cancel' hd₂)
  have hU (d : ℕ) : (U d).card ≤ (N/d)^2 := by
    have h := Finset.card_image_le (s := (Finset.Icc 1 (N/d)) ×ˢ (Finset.Icc 1 (N/d)))
      (f := fun p : ℕ × ℕ => (d*p.1,d*p.2))
    simpa only [U,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel,pow_two] using h
  have hF : F.card ≤ ∑ d ∈ Finset.Icc 2 N, (N/d)^2 := by
    calc
      _ ≤ _ := Finset.card_le_card hcover
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun d _ => hU d)
  have hFR : (F.card:ℝ) ≤ (3/4:ℝ)*(N:ℝ)^2 := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 2 N, (((N/d)^2:ℕ):ℝ) := by exact_mod_cast hF
      _ ≤ ∑ d ∈ Finset.Icc 2 N, ((N:ℝ)/(d:ℝ))^2 := by
        apply Finset.sum_le_sum
        intro d _hd
        rw [Nat.cast_pow]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) Nat.cast_div_le _
      _ = (N:ℝ)^2 * ∑ d ∈ Finset.Icc 2 N, 1/(d:ℝ)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _hd
        rw [div_pow]
        ring
      _ ≤ (N:ℝ)^2*(3/4) := mul_le_mul_of_nonneg_left (sum_nonunit_inverse_square_le N) (sq_nonneg _)
      _ = _ := by ring
  have htotal : G.card+F.card=N^2 := by
    have h := Finset.card_filter_add_card_filter_not (s := A) (fun p => Nat.Coprime p.1 p.2)
    simpa only [A,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel,pow_two] using h
  have htotalR : (G.card:ℝ)+(F.card:ℝ)=(N:ℝ)^2 := by exact_mod_cast htotal
  change (N:ℝ)^2/4 ≤ (G.card:ℝ)
  linarith

#print axioms coprime_square_card_lower

theorem sum_totient_lower (N : ℕ) :
    (N:ℝ)^2/8 ≤ ∑ n ∈ Finset.Icc 1 N, (n.totient:ℝ) := by
  classical
  let A := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  let G := A.filter (fun p => Nat.Coprime p.1 p.2)
  let C : ℕ → Finset ℕ := fun n => (Finset.Icc 1 n).filter (Nat.Coprime n)
  let U : ℕ → Finset (ℕ × ℕ) := fun n =>
    ((C n).image (fun m => (m,n))) ∪ ((C n).image (fun m => (n,m)))
  have hC (n : ℕ) : (C n).card=n.totient := by
    have h := Nat.filter_coprime_Ico_eq_totient n 1
    have hI : Finset.Ico 1 (1+n) = Finset.Icc 1 n := by
      ext m
      simp only [Finset.mem_Ico,Finset.mem_Icc]
      omega
    rwa [hI] at h
  have hU (n : ℕ) : (U n).card ≤ 2*n.totient := by
    calc
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ (C n).card+(C n).card := add_le_add Finset.card_image_le Finset.card_image_le
      _ = _ := by rw [hC]; omega
  have hcover : G ⊆ (Finset.Icc 1 N).biUnion U := by
    intro p hp
    obtain ⟨hpA,hcop⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpA
    by_cases hle : p.1 ≤ p.2
    · apply Finset.mem_biUnion.mpr
      refine ⟨p.2,hp₂,Finset.mem_union_left _ ?_⟩
      exact Finset.mem_image.mpr ⟨p.1,Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp₁).1,hle⟩,hcop.symm⟩,rfl⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨p.1,hp₁,Finset.mem_union_right _ ?_⟩
      exact Finset.mem_image.mpr ⟨p.2,Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp₂).1,by omega⟩,hcop⟩,rfl⟩
  have hupper : G.card ≤ ∑ n ∈ Finset.Icc 1 N, 2*n.totient :=
    (Finset.card_le_card hcover).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun n _ => hU n)))
  have hupperR : (G.card:ℝ) ≤ 2*∑ n ∈ Finset.Icc 1 N, (n.totient:ℝ) := by
    have h : (G.card:ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, (2:ℝ)*(n.totient:ℝ) := by
      exact_mod_cast hupper
    rwa [← Finset.mul_sum] at h
  have hlower := coprime_square_card_lower N
  change (N:ℝ)^2/4 ≤ (G.card:ℝ) at hlower
  linarith

#print axioms sum_totient_lower

theorem moebius_coprime_indicator {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (∑ d ∈ n.divisors, if d ∣ m then (ArithmeticFunction.moebius d:ℝ) else 0) =
      if Nat.Coprime n m then 1 else 0 := by
  classical
  have hg : n.gcd m ≠ 0 := (Nat.gcd_pos_of_pos_left m hn).ne'
  have hset : n.divisors.filter (fun d => d ∣ m) = (n.gcd m).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdn,_⟩,hdm⟩
      exact ⟨⟨hdn,hdm⟩,hg⟩
    · rintro ⟨⟨hdn,hdm⟩,_⟩
      exact ⟨⟨hdn,hn.ne'⟩,hdm⟩
  rw [← Finset.sum_filter,hset]
  have hμ : (∑ d ∈ (n.gcd m).divisors, ArithmeticFunction.moebius d) =
      if n.gcd m=1 then (1:ℤ) else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  have hcast := congrArg (fun z : ℤ => (z:ℝ)) hμ
  simpa only [Int.cast_sum,Int.cast_ite,Int.cast_one,Int.cast_zero,Nat.Coprime] using hcast

theorem moebius_totient_weight {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)*(n/d:ℕ)) = (n.totient:ℝ) := by
  have hsum : ∀ k : ℕ, 0 < k → (∑ d ∈ k.divisors, (d.totient:ℝ))=(k:ℝ) := by
    intro k _hk
    exact_mod_cast Nat.sum_totient k
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hsum n hn
  rw [Nat.sum_divisorsAntidiagonal (fun d e => (ArithmeticFunction.moebius d:ℝ)*(e:ℝ))] at h
  exact h

#print axioms moebius_coprime_indicator
#print axioms moebius_totient_weight

theorem coprime_prefix_moebius {n : ℕ} (hn : 0 < n) (X : ℕ) :
    (((Finset.Ioc 0 X).filter (Nat.Coprime n)).card:ℝ) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)*(X/d:ℕ) := by
  classical
  calc
    _ = ∑ m ∈ Finset.Ioc 0 X, if Nat.Coprime n m then (1:ℝ) else 0 := by
      simp only [Finset.card_filter,Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      split_ifs <;> norm_num
    _ = ∑ m ∈ Finset.Ioc 0 X, ∑ d ∈ n.divisors,
        if d ∣ m then (ArithmeticFunction.moebius d:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact (moebius_coprime_indicator hn m).symm
    _ = ∑ d ∈ n.divisors, ∑ m ∈ Finset.Ioc 0 X,
        if d ∣ m then (ArithmeticFunction.moebius d:ℝ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,
        Nat.Ioc_filter_dvd_card_eq_div,mul_comm]

theorem moebius_totient_normalized {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)/(d:ℝ)) =
      (n.totient:ℝ)/(n:ℝ) := by
  have h := moebius_totient_weight hn
  have h' : (n:ℝ)*(∑ d ∈ n.divisors, (ArithmeticFunction.moebius d:ℝ)/(d:ℝ)) =
      (n.totient:ℝ) := by
    rw [Finset.mul_sum]
    convert h using 1
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
    ring
  apply (eq_div_iff (by positivity : (n:ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using h'

#print axioms coprime_prefix_moebius
#print axioms moebius_totient_normalized

theorem coprime_prefix_error {n : ℕ} (hn : 0 < n) (X : ℕ) :
    |(((Finset.Ioc 0 X).filter (Nat.Coprime n)).card:ℝ)-
      (X:ℝ)*((n.totient:ℝ)/(n:ℝ))| ≤ n.divisors.card := by
  classical
  rw [coprime_prefix_moebius hn X,← moebius_totient_normalized hn,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ n.divisors,
        |(ArithmeticFunction.moebius d:ℝ)*(X/d:ℕ)-
          (X:ℝ)*((ArithmeticFunction.moebius d:ℝ)/(d:ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro d _hd
      have he : (ArithmeticFunction.moebius d:ℝ)*(X/d:ℕ)-
          (X:ℝ)*((ArithmeticFunction.moebius d:ℝ)/(d:ℝ)) =
          (ArithmeticFunction.moebius d:ℝ)*(((X/d:ℕ):ℝ)-(X:ℝ)/(d:ℝ)) := by ring
      rw [he,abs_mul]
      have hμ : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hfloor : |((X/d:ℕ):ℝ)-(X:ℝ)/(d:ℝ)| ≤ 1 := by
        have hlo := Nat.floor_le (show (0:ℝ) ≤ (X:ℝ)/(d:ℝ) by positivity)
        have hhi := Nat.lt_floor_add_one ((X:ℝ)/(d:ℝ))
        rw [Nat.floor_div_eq_div] at hlo hhi
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      simpa only [one_mul] using mul_le_mul hμ hfloor (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    _ = _ := by simp

#print axioms coprime_prefix_error

/-- An actual half-open real interval, with explicit arithmetic discrepancy.
This statement retains the divisor error instead of postulating density. -/
theorem coprime_interval_lower {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (b-a)*((n.totient:ℝ)/(n:ℝ)) ≤
      (((Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (Nat.Coprime n)).card:ℝ)+3*n.divisors.card := by
  classical
  let L := ⌊a⌋₊
  let U := ⌊b⌋₊
  let C : ℕ → Finset ℕ := fun X => (Finset.Ioc 0 X).filter (Nat.Coprime n)
  let T := (Finset.Ioc L U).filter (Nat.Coprime n)
  have hLU : L ≤ U := Nat.floor_mono hab
  have hpart : C U=C L ∪ T := by
    ext m
    simp only [C,T,Finset.mem_filter,Finset.mem_Ioc,Finset.mem_union]
    omega
  have hdis : Disjoint (C L) T := by
    apply Finset.disjoint_left.mpr
    intro m hm ht
    have h₁ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1
    have h₂ := Finset.mem_Ioc.mp (Finset.mem_filter.mp ht).1
    omega
  have hcounts : ((C U).card:ℝ)=((C L).card:ℝ)+(T.card:ℝ) := by
    rw [hpart,Finset.card_union_of_disjoint hdis,Nat.cast_add]
  let γ : ℝ := (n.totient:ℝ)/(n:ℝ)
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hγ1 : γ ≤ 1 := (div_le_one (by positivity : (0:ℝ) < n)).mpr
    (by exact_mod_cast Nat.totient_le n)
  have hfloor : b-a ≤ (U:ℝ)-(L:ℝ)+1 := by
    have hL := Nat.floor_le ha
    have hU := Nat.lt_floor_add_one b
    change (L:ℝ) ≤ a at hL
    change b < (U:ℝ)+1 at hU
    linarith
  have hscale := mul_le_mul_of_nonneg_right hfloor hγ0
  have hlo := (abs_le.mp (coprime_prefix_error hn L)).2
  have hup := (abs_le.mp (coprime_prefix_error hn U)).1
  change (C L).card-(L:ℝ)*γ ≤ (n.divisors.card:ℝ) at hlo
  change -(n.divisors.card:ℝ) ≤ (C U).card-(U:ℝ)*γ at hup
  have hdiv : (1:ℝ) ≤ n.divisors.card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hn.ne'⟩)
  change (b-a)*γ ≤ (T.card:ℝ)+3*n.divisors.card
  nlinarith only [hcounts,hγ1,hscale,hlo,hup,hdiv]

#print axioms coprime_interval_lower

/-- Möbius inversion gives a density bound for the complete geometric sector,
with an explicit logarithmic discrepancy. It is not the sharper printed
constant-error estimate used in Huxley's Lemma 2.3. -/
theorem fareySector_card_lower_log (N : ℕ) {l μ : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) :
    (μ-l)*(N:ℝ)^2/8 ≤
      ((HuxleyLinearForm.fareySector N l μ).card:ℝ)+3*(N:ℝ)*(1+Real.log N) := by
  classical
  let C : ℕ → Finset ℕ := fun n =>
    (Finset.Ioc ⌊l*(n:ℝ)⌋₊ ⌊μ*(n:ℝ)⌋₊).filter (Nat.Coprime n)
  let U : ℕ → Finset (ℤ × ℤ) := fun n => (C n).image (fun m : ℕ => ((m:ℤ),(n:ℤ)))
  have hcard (n : ℕ) : (U n).card=(C n).card := by
    apply Finset.card_image_of_injective
    intro m k h
    exact Int.ofNat_inj.mp (congrArg Prod.fst h)
  have hdis : (↑(Finset.Icc 1 N):Set ℕ).PairwiseDisjoint U := by
    intro n _hn k _hk hnk
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨a,_ha,ha⟩ := Finset.mem_image.mp hp
    obtain ⟨b,_hb,hb⟩ := Finset.mem_image.mp hq
    exact hnk (Int.ofNat_inj.mp (congrArg Prod.snd (ha.trans hb.symm)))
  have hsub : (Finset.Icc 1 N).biUnion U ⊆ HuxleyLinearForm.fareySector N l μ := by
    intro p hp
    obtain ⟨n,hn,hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hmI,hcop⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmL,hmU⟩ := Finset.mem_Ioc.mp hmI
    obtain ⟨hn1,hnN⟩ := Finset.mem_Icc.mp hn
    apply (HuxleyLinearForm.mem_fareySector_iff hl (hl.le.trans hlμ)).mpr
    refine ⟨by dsimp; exact_mod_cast hn1,by dsimp; exact_mod_cast hnN,hcop.symm.isCoprime,?_,?_⟩
    · simpa only [Int.cast_natCast] using (Nat.lt_of_floor_lt hmL).le
    · have hu := Nat.floor_le (mul_nonneg (hl.le.trans hlμ) (Nat.cast_nonneg n))
      have hmU' : (m:ℝ) ≤ ⌊μ*(n:ℝ)⌋₊ := by exact_mod_cast hmU
      simpa only [Int.cast_natCast] using hmU'.trans hu
  have hsumCard : (∑ n ∈ Finset.Icc 1 N, ((C n).card:ℝ)) ≤
      (HuxleyLinearForm.fareySector N l μ).card := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdis] at hc
    simp only [hcard] at hc
    exact_mod_cast hc
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (μ-l)*(n.totient:ℝ) ≤ ((C n).card:ℝ)+3*n.divisors.card := by
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have he := coprime_interval_lower hn0
      (show (0:ℝ) ≤ l*(n:ℝ) by positivity)
      (mul_le_mul_of_nonneg_right hlμ (Nat.cast_nonneg n))
    have hid : (μ*(n:ℝ)-l*(n:ℝ))*((n.totient:ℝ)/(n:ℝ)) =
        (μ-l)*(n.totient:ℝ) := by
      field_simp [ne_of_gt (show (0:ℝ) < n by exact_mod_cast hn0)]
    rw [hid] at he
    exact he
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have htot := mul_le_mul_of_nonneg_left (sum_totient_lower N) (sub_nonneg.mpr hlμ)
  have hdiv := AtkinsonPrintedSource.sum_divisorCard_le_log N
  have hI : Finset.Ioc 0 N=Finset.Icc 1 N := by ext n; simp; omega
  rw [hI] at hdiv
  nlinarith only [hsum,htot,hdiv,hsumCard]

#print axioms fareySector_card_lower_log

end HuxleyFareyDensity

namespace HuxleySectorRegression

open TaoTrudgianYang2025.HuxleyLinearForm

example (N : ℕ) {l μ : ℝ} (hl : 0 < l) (hlμ : l ≤ μ) :
    ((fareySector N l μ).card:ℝ) ≤ (μ-l)*(N:ℝ)*((N:ℝ)+1)/2+(N:ℝ) :=
  fareySector_card_le N hl hlμ

example {N : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : 16*(N:ℝ) ≤ (fareySector N l μ).card) :
    ∃ m n : ℤ, (m,n) ∈ fareySector N l μ ∧ (m+1,n) ∈ fareySector N l μ :=
  sector_consecutive_numerators hl hlμ hN hR

example {N : ℕ} {l μ B : ℝ}
    (hl : 0 < l) (hlμ : l ≤ μ) (hN : 0 < N)
    (hR : (N:ℝ) ≤ (fareySector N l μ).card)
    (hdensity : (μ-l)*(N:ℝ)^2 ≤ B*(fareySector N l μ).card) :
    (N:ℝ) ≤ (B+1)*((fareySector N l μ).image Prod.snd).card :=
  sector_denominator_card_lower hl hlμ hN hR hdensity

example {N q : ℕ} {l μ : ℝ}
    (hl : 0 < l) (hμ : 0 ≤ μ) (hR : 2 ≤ (fareySector N l μ).card)
    (hdvd : ∀ p ∈ fareySector N l μ, q ∣ p.2.natAbs) : q=1 :=
  sector_denominator_common_divisor hl hμ hR hdvd

example {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((fareySector N l μ).card:ℝ) ≤ 1536*B*δ*(μ*(N:ℝ))*(N:ℝ) ∨
      (|α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(fareySector N l μ).card ∧
       |β-(round β:ℤ)| ≤ 20*B*(μ*(N:ℝ))*δ/(fareySector N l μ).card) :=
  fareySector_bounded_density_dichotomy hl hμ hB hδ hR hnear

example {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hlarge : 1536*B*δ*(μ*(N:ℝ))*(N:ℝ) < (fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ∀ p ∈ fareySector N l μ, ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*(round α)+p.2*(round β) :=
  fareySector_integer_labels hl hμ hB hδ hR hlarge hnear

end HuxleySectorRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalBranch_hasDerivAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalBranch_linear_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalBranch_second
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_linear_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_homogeneous_linearization
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_second
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_curvature_of_cubic_ratio
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_taylor_of_cubic_ratio
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_homogeneous_taylor_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_nonlinear_integer_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.affine_ratio_coordinate_difference
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.cubic_ratio_gap
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.determinant_bound_of_cubic_ratios
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_small_deriv_of_two_values
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.four_point_curvature
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_cubic_ratio_abs_eq
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_four_point_cubic_ratio
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCoordinate_difference
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCoordinate_gap_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_eight_point_determinant
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.point_gap_of_minorArcCoordinate_gap
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.scaled_minorArcCoordinate_abs
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_long_block_determinant

namespace HuxleyRationalPhaseRegression

open TaoTrudgianYang2025.HuxleyRationalPhase

example {μ r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    iteratedDeriv 2 (rationalBranch μ r s) x = 2/(3*μ*(r*x+s)^3) :=
  rationalBranch_second hμ hr hx

example
    {N : ℕ} {l v B ν r s ν₁ r₁ s₁ x₀ d ε α β δ : ℝ}
    (hl : 0 < l) (hv : 1 ≤ v) (hlv : l ≤ v) (hB : 1 ≤ B) (hx₀ : x₀ ∈ Set.Icc l v)
    (hν : ν ≠ 0) (hr : r ≠ 0) (hν₁ : 0 < ν₁) (hr₁ : r₁ ≠ 0) (hd : 0 < d) (hδ : 0 ≤ δ)
    (hden : ∀ y ∈ Set.Icc l v, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l v, d ≤ r₁*y+s₁)
    (hratio : ∀ y ∈ Set.Icc l v, |ν₁*(r₁*y+s₁)^3/(ν*(r*y+s)^3)-1| ≤ ε)
    (hR : max ((v-l)*(N:ℝ)^2/B) 2 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v).card)
    (hnear : ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-
        (p.2:ℝ)*rationalPhase ν r s ν₁ r₁ s₁ ((p.1:ℝ)/(p.2:ℝ))-b| ≤ δ) :
    let g := rationalPhase ν r s ν₁ r₁ s₁
    let η := δ+(N:ℝ)*ε*(v-l)^2/(3*ν₁*d^3)
    1536*B*η*(v*(N:ℝ))*(N:ℝ) <
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v).card →
    ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v, ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ))-b| ≤ δ →
      b=p.1*(round (α-deriv g x₀))+p.2*(round (β-g x₀+x₀*deriv g x₀)) :=
  sector_nonlinear_integer_labels hl hv hlv hB hx₀ hν hr hν₁ hr₁ hd hδ hden hden₁ hratio hR hnear

example
    {μ r s μ₁ r₁ s₁ a b c d h E D₁ A B : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hh : 0 < h) (hab : h ≤ b-a) (hbc : h ≤ c-b) (hcd : h ≤ d-c)
    (hden : ∀ x ∈ Set.Icc a d, r*x+s ≠ 0)
    (hden₁ : ∀ x ∈ Set.Icc a d, r₁*x+s₁ ≠ 0)
    (hD₁ : ∀ x ∈ Set.Icc a d, |r₁*x+s₁| ≤ D₁)
    (ha : |A*a+B-rationalPhase μ r s μ₁ r₁ s₁ a| ≤ E)
    (hb : |A*b+B-rationalPhase μ r s μ₁ r₁ s₁ b| ≤ E)
    (hc : |A*c+B-rationalPhase μ r s μ₁ r₁ s₁ c| ≤ E)
    (hd : |A*d+B-rationalPhase μ r s μ₁ r₁ s₁ d| ≤ E) :
    ∃ z ∈ Set.Ioo a d,
      |μ₁*(r₁*z+s₁)^3/(μ*(r*z+s)^3)-1| ≤ 6*|μ₁| * D₁^3*E/h^2 :=
  rationalPhase_four_point_cubic_ratio hμ hr hμ₁ hr₁ hh hab hbc hcd hden hden₁ hD₁ ha hb hc hd

example
    {μ r s μ₁ r₁ s₁ h E D D₁ q A B : ℝ} (x : Fin 8 → ℝ)
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hh : 0 < h) (hD : 0 < D) (hq : 0 < q)
    (hgap : ∀ i : Fin 7, h ≤ x i.succ-x i.castSucc)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc (x 0) (x 7), r₁*y+s₁ ≠ 0)
    (hbound : ∀ y ∈ Set.Icc (x 0) (x 7), |r*y+s| ≤ D)
    (hbound₁ : ∀ y ∈ Set.Icc (x 0) (x 7), |r₁*y+s₁| ≤ D₁)
    (hratio : ∀ y ∈ Set.Icc (x 0) (x 7), q ≤ (r₁*y+s₁)/(r*y+s))
    (hres : ∀ i : Fin 8, |A*x i+B-rationalPhase μ r s μ₁ r₁ s₁ (x i)| ≤ E) :
    |r*s₁-s*r₁| ≤ 4*|μ| * D^2*D₁^3*E/(q^2*h^3) :=
  rationalPhase_eight_point_determinant x hμ hr hμ₁ hr₁ hh hD hq hgap hden hden₁ hbound hbound₁ hratio hres

example {μ r s a b : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ha : r*a+s ≠ 0) (hb : r*b+s ≠ 0) :
    minorArcCoordinate μ r s b-minorArcCoordinate μ r s a =
      -(b-a)/(3*μ*(r*b+s)*(r*a+s)) :=
  minorArcCoordinate_difference hμ hr ha hb

example
    {μ r s μ₁ r₁ s₁ d L N R K Kμ A B : ℝ} (x : Fin 8 → ℝ)
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hd : 0 < d) (hL : 0 < L) (hN : 0 < N) (hR : 0 < R)
    (hK : 0 ≤ K) (hscale : 1 ≤ Kμ*|μ| * N*R^2)
    (hmono : StrictMono x)
    (hgap : ∀ i : Fin 7, L*N ≤
      |minorArcCoordinate μ r s (x i.succ)-minorArcCoordinate μ r s (x i.castSucc)|)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), d ≤ |r*y+s| ∧ |r*y+s| ≤ 2*d)
    (hden₁ : ∀ y ∈ Set.Icc (x 0) (x 7), r₁*y+s₁ ≠ 0)
    (hbound₁ : ∀ y ∈ Set.Icc (x 0) (x 7), |r₁*y+s₁| ≤ 4*d)
    (hratio : ∀ y ∈ Set.Icc (x 0) (x 7), (1:ℝ)/2 ≤ (r₁*y+s₁)/(r*y+s))
    (hres : ∀ i : Fin 8, |A*x i+B-rationalPhase μ r s μ₁ r₁ s₁ (x i)| ≤
      K*R^2/|r*minorArcCoordinate μ r s (x i)|) :
    |r*s₁-s*r₁| ≤ 1024*K*Kμ*R^4/(L^3*N^2) :=
  rationalPhase_long_block_determinant x hμ hr hμ₁ hr₁ hd hL hN hR hK hscale hmono hgap hden hden₁ hbound₁ hratio hres

end HuxleyRationalPhaseRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.affine_ratio_mem_endpoint_interval
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.cubic_ratio_bound_between
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_eight_point_third_condition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_long_block_third_condition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.ratio_relative_perturbation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.cubic_ratio_parameter_perturbation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.cubicTaylorCoefficient_relative_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_cubicCoefficient_relative_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubicCoefficient_relative_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubic_ratio_transfer
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_first_order_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_curvature_coordinate_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCoordinate_taylor_entry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_minorArcCoordinate_taylor_entry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_round_error
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_round_error
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_rounded_halfCurvature_center
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_minorArcCoordinate_entry

namespace HuxleyPhysicalEntryRegression

open TaoTrudgianYang2025.HuxleyRationalPhase

example {μ r s μ₁ r₁ s₁ d L N R K J A B : ℝ} (x : Fin 8 → ℝ)
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hd : 0 < d) (hL : 0 < L) (hN : 0 < N) (hR : 0 < R)
    (hK : 0 ≤ K) (hJ : |μ₁| ≤ J*|μ|) (hmono : StrictMono x)
    (hgap : ∀ i : Fin 7, L*N ≤
      |minorArcCoordinate μ r s (x i.succ)-minorArcCoordinate μ r s (x i.castSucc)|)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), d ≤ r*y+s ∧ r*y+s ≤ 2*d)
    (hden₁ : ∀ y ∈ Set.Icc (x 0) (x 7), r₁*y+s₁ ≠ 0)
    (hbound₁ : ∀ y ∈ Set.Icc (x 0) (x 7), |r₁*y+s₁| ≤ 4*d)
    (hres : ∀ i : Fin 8, |A*x i+B-rationalPhase μ r s μ₁ r₁ s₁ (x i)| ≤
      K*R^2/|r*minorArcCoordinate μ r s (x i)|) :
    ∀ z ∈ Set.Icc (x 3) (x 4),
      |μ₁*(r₁*z+s₁)^3/(μ*(r*z+s)^3)-1| ≤ 256*J*K*R^2/(L^2*N^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_long_block_third_condition μ r s μ₁ r₁ s₁ d L N R K J A B x hμ hr hμ₁ hr₁ hd hL hN hR hK hJ hmono hgap hden hden₁ hbound₁ hres

example {σ δ T M A W a b a₁ b₁ H p q ε : ℝ} {F F₁ : ℝ → ℝ} (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hF₁ : Expdb.IsApproximateModelPhaseFunction F₁ σ 3 δ)
    (hT : T ≠ 0) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W)
    (ha₁ : a₁ ∈ Set.Ioo 0 W) (hb₁ : b₁ ∈ Set.Ioo 0 W)
    (hH : |b-a| ≤ H) (hH₁ : |b₁-a₁| ≤ H) (hq : q ≠ 0) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let f₁ := TaoTrudgianYang2025.heathBrownPhysicalPhase F₁ T M A 1
    let η := (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*H/
      (TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
    η ≤ 1/2 →
    |(iteratedDeriv 3 f₁ a₁/6)*p^3/((iteratedDeriv 3 f a/6)*q^3)-1| ≤ ε →
    |(iteratedDeriv 3 f₁ b₁/6)*p^3/((iteratedDeriv 3 f b/6)*q^3)-1| ≤ 3*ε+4*η :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubic_ratio_transfer σ δ T M A W a b a₁ b₁ H p q ε F F₁ hσ hδ hF hF₁ hT hM hA hW ha hb ha₁ hb₁ hH hH₁ hq

example {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U) :
    |iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
      3*(iteratedDeriv 3 f a/6)*(b-a)| ≤ U*|b-a|^2/4 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_first_order_remainder f a b U hf hfourth

example {μ e r v s u t : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0)
    (hdet : v*r-e*s=1) :
    (e*u+v*t)/(r*u+s*t)-e/r = 3*μ*minorArcCoordinate μ r s (u/t) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_curvature_coordinate_identity μ e r v s u t hμ hr ht hq hdet

example {σ δ T M A W a b e r v s u t δ₀ δ₁ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W)
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f a/2 = e/r+δ₀ →
    iteratedDeriv 2 f b/2 = (e*u+v*t)/(r*u+s*t)+δ₁ →
    |(b-a)-minorArcCoordinate (iteratedDeriv 3 f a/6) r s (u/t)-
      (δ₁-δ₀)/(3*(iteratedDeriv 3 f a/6))| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|b-a|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_minorArcCoordinate_taylor_entry σ δ T M A W a b e r v s u t δ₀ δ₁ F hσ hδ hF hT hM hA hW ha hb hr ht hq hdet

example {f : ℝ → ℝ} {W x U : ℝ}
    (hx : x ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hf : ∀ y ∈ Set.Ioo 0 W, ContDiffAt ℝ 3 f y)
    (hthird : ∀ y ∈ Set.Ioo 0 W, |iteratedDeriv 3 f y| ≤ U) :
    (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-iteratedDeriv 2 f x/2| ≤ U/4 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_round_error f W x U hx hf hthird

example {σ δ T M A W l v q : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hl : l ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hv : v ∈ Set.Ioo (1/2:ℝ) (W-1/2)) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    q ∈ Set.uIcc (iteratedDeriv 2 f l/2) (iteratedDeriv 2 f v/2) →
    ∃ x ∈ Set.uIcc l v, iteratedDeriv 2 f x/2=q ∧
      (round x:ℝ) ∈ Set.Ioo 0 W ∧
      |iteratedDeriv 2 f (round x)/2-q| ≤
        T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_rounded_halfCurvature_center σ δ T M A W l v q F hσ hF hT hM hA hW hl hv

example {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let n := (round x₁:ℝ)-(round x₀:ℝ)
    let μ := iteratedDeriv 3 f (round x₀)/6
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |n-minorArcCoordinate μ r s (u/t)| ≤
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
        TaoTrudgianYang2025.modelPhaseThirdLower σ+
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|n|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_minorArcCoordinate_entry σ δ T M A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hA hW hx₀ hx₁ hr ht hq hdet

end HuxleyPhysicalEntryRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_halfCurvature_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_firstDerivative_halfCurvature_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_firstDerivative_residual
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_firstDerivative_residual_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_firstDerivative_integer_label
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.corrected_nonlinear_residual_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_corrected_nonlinear_residual_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_corrected_nonlinear_residual_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.coordinate_error_quadratic_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.corrected_residual_source_scale_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_corrected_residual_le_fourth_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_linearization_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_linearization
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rounded_linearization_pair_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_fourth_condition_nonlinear
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.nonlinearResidualConstant_nonneg
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_cubicCoefficient_pos
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_integer_labels

namespace HuxleyResidualRegression

open TaoTrudgianYang2025.HuxleyRationalPhase

example
    {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 4 f y)
    (hfourth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 4 f y| ≤ U) :
    |iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2)| ≤ 5*U*|b-a|^3/12 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_halfCurvature_remainder f a b U hf hfourth

example
    {e r v s u t n : ℤ} {d₀ d₁ : ℝ}
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let q : ℝ := r*u+s*t
    let c := round ((r:ℝ)*d₀)
    let θ := (r:ℝ)*d₀-c
    let γ := q*(d₁-d₀-2*(e:ℝ)*n/r-(n:ℝ)*t/(r*q))
    let H := ((c:ℝ)*s-n)*t/r+θ*q/r+γ
    round (q*d₁) = c*u+2*n*(e*u+v*t)+round H ∧
      q*d₁-round (q*d₁) = H-round H :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_firstDerivative_integer_label e r v s u t n d₀ d₁ hr hq hdet

example
    {μ r s u t n δ E : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(E+2*δ*n+3*μ*n^2-n*t/(r*q))
    γ-n*t/r-t/r*(2*δ/(3*μ)-G) = q*(E+(n-G)*(3*μ*(n-G)+2*δ)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.corrected_nonlinear_residual_identity μ r s u t n δ E hμ hr ht hq

example {A B C₂ C₃ n M N R T : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hn : 0 ≤ n) (hM : 1 ≤ M) (hnM : n ≤ M) (hN : 0 < N)
    (hR : 1 ≤ R) (hT : 0 < T) (hscale : T*N*R^2=M^3) (hcube : n^3 ≤ M*R^2) :
    let K := A*(A+1)+(2*A+1)*B+B^2
    (T/M^3)*(C₃*n^3/(6*M)+C₂/2*(A+B*n^2/M)*(A+B*n^2/M+1)) ≤
      (C₃/3+C₂*K)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.corrected_residual_source_scale_budget A B C₂ C₃ n M N R T hA hB hC₂ hC₃ hn hM hnM hN hR hT hscale hcube

example
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let δ₀ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |n|^3 ≤ M*R^2 →
    |γ-n*t/r-t/r*(2*δ₀/(3*μ)-G)| ≤ nonlinearResidualConstant σ δ*|q|/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_corrected_residual_le_fourth_scale σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R A W x₀ x₁ : ℝ} {e r v s u t : ℤ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let a := round x₀
    let b := round x₁
    let n := b-a
    let q : ℝ := r*u+s*t
    let j := round ((r:ℝ)*iteratedDeriv 1 f a)*u+2*n*(e*u+v*t)
    iteratedDeriv 2 f x₀/2=(e:ℝ)/r →
    iteratedDeriv 2 f x₁/2=((e:ℝ)*u+v*t)/q →
    |(n:ℝ)|^3 ≤ M*R^2 →
    |q*iteratedDeriv 1 f b-j-roundedMinorArcLinearForm f x₀ e r s u t| ≤
      nonlinearResidualConstant σ δ*|q|/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_linearization σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R Δ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun i => round (x₁ i)
    let n := fun i => b i-a i
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let z := fun i => q i*iteratedDeriv 1 (f i) (b i)
    let j := fun i => round ((r i:ℝ)*d₀ i)*u+2*n i*(e i*u+v i*t)
    let h := (round (z 0)-j 0)-(round (z 1)-j 1)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)|^3 ≤ M*R^2) →
    |(z 0-round (z 0))-(z 1-round (z 1))| ≤ Δ →
    |(θ 0-θ 1)*u+(β₀ 0-β₀ 1)*t-
      (t:ℝ)*rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1) ((u:ℝ)/t)-h| ≤
      Δ+nonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_fourth_condition_nonlinear σ δ T M N R Δ u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {K : ℕ} {σ δ T M N R Δ Q l w B y₀ d ε : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℤ × ℤ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hd : 0 < d) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q) :
    let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun p i => round (x₁ p i)
    let n := fun p i => b p i-a i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let z := fun p i => q p i*iteratedDeriv 1 (f i) (b p i)
    let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+2*n p i*(e i*p.1+v i*p.2)
    let h := fun p => (round (z p 0)-j p 0)-(round (z p 1)-j p 1)
    let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
    let η := η₀+(K:ℝ)*ε*(w-l)^2/(3*μ 1*d^3)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i, x₁ p i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ p ∈ S, ∀ i, r i*p.1+s i*p.2 ≠ 0) →
    (∀ p ∈ S, ∀ i, iteratedDeriv 2 (f i) (x₁ p i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n p i:ℝ)|^3 ≤ M*R^2) →
    (∀ p ∈ S, |(z p 0-round (z p 0))-(z p 1-round (z p 1))| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    (∀ y ∈ Set.Icc l w, (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.Icc l w, d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.Icc l w, |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ε) →
    max ((w-l)*(K:ℝ)^2/B) 2 ≤ S.card →
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, h p=p.1*round (α-deriv g y₀)+p.2*round (β-g y₀+y₀*deriv g y₀) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_integer_labels K σ δ T M N R Δ Q l w B y₀ d ε F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hr hdet hl hw hlw hB hy₀ hd hΔ hQ

end HuxleyResidualRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sum_nonunit_inverse_square_le
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.affine_positive_between
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_curvature_targets
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rounded_displacement_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_centres
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_denominator_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_constructed_sector_nonlinear
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.coprime_rectangle_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.isCoprime_unimodular_image
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_image_injective
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_rectangle_fareySector_interior_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_rectangle_fareySector_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_cone_fareySector_interior_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_cone_fareySector_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_interval_determinant_split
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.interval_filter_split_card
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_interior_filter_eq
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_interval_fareySector_interior_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_separation_scaled
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_rational_near_anchor
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_rational_inner_endpoints
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_card_lower_of_rational_anchor
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_card_lower_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_source_density_gate
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_nonlinear_integer_labels_source_density

namespace HuxleyDensityRegression

open TaoTrudgianYang2025.HuxleyRationalPhase

example {K : ℕ}
    {σ δ T M A W l w L U x₀ H R : ℝ} {F : ℝ → ℝ} {e r v s : ℤ}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : 0 < (r:ℝ)*l+s) (hdenw : 0 < (r:ℝ)*w+s)
    (hLdist : |L-x₀| ≤ H) (hUdist : |U-x₀| ≤ H) (hcube : (H+1)^3 ≤ M*R^2) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let I := Set.uIcc (iteratedDeriv 2 f L/2) (iteratedDeriv 2 f U/2)
    ((e:ℝ)*l+v)/((r:ℝ)*l+s) ∈ I →
    ((e:ℝ)*w+v)/((r:ℝ)*w+s) ∈ I →
    ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w,
      0 < (r:ℝ)*p.1+s*p.2 ∧ ∃ x ∈ Set.uIcc L U,
        x ∈ Set.Ioo (1/2:ℝ) (W-1/2) ∧
        iteratedDeriv 2 f x/2=((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∧
        (round x:ℝ) ∈ Set.Ioo 0 W ∧
        |(round x:ℝ)-(round x₀:ℝ)|^3 ≤ M*R^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_centres K σ δ T M A W l w L U x₀ H R F e r v s hσ hF hT hM hA hW hL hU hl hlw hdenl hdenw hLdist hUdist hcube

example {K : ℕ} {l w : ℝ} {r s : ℤ}
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : 0 < (r:ℝ)*l+s) (hdenw : 0 < (r:ℝ)*w+s)
    {p : ℤ × ℤ} (hp : p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w) :
    |(r:ℝ)*p.1+s*p.2| ≤ (K:ℝ)*max ((r:ℝ)*l+s) ((r:ℝ)*w+s) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_denominator_bound K l w r s hl hlw hdenl hdenw p hp

example
    {K : ℕ} {σ δ T M N R Δ l w H : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ L U : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hL : ∀ i, L i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hU : ∀ i, U i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hlw : l ≤ w)
    (hdenl : ∀ i, 0 < (r i:ℝ)*l+s i) (hdenw : ∀ i, 0 < (r i:ℝ)*w+s i)
    (hLdist : ∀ i, |L i-x₀ i| ≤ H) (hUdist : ∀ i, |U i-x₀ i| ≤ H)
    (hcube : (H+1)^3 ≤ M*R^2) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let D := fun i => max ((r i:ℝ)*l+s i) ((r i:ℝ)*w+s i)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, ((e i:ℝ)*l+v i)/((r i:ℝ)*l+s i) ∈
      Set.uIcc (iteratedDeriv 2 (f i) (L i)/2) (iteratedDeriv 2 (f i) (U i)/2)) →
    (∀ i, ((e i:ℝ)*w+v i)/((r i:ℝ)*w+s i) ∈
      Set.uIcc (iteratedDeriv 2 (f i) (L i)/2) (iteratedDeriv 2 (f i) (U i)/2)) →
    ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w,
      ∃ x : Fin 2 → ℝ,
        (∀ i, x i ∈ Set.uIcc (L i) (U i)) ∧
        (∀ i, iteratedDeriv 2 (f i) (x i)/2=((e i:ℝ)*p.1+v i*p.2)/((r i:ℝ)*p.1+s i*p.2)) ∧
        let q := fun i => (r i:ℝ)*p.1+s i*p.2
        let z := fun i => q i*iteratedDeriv 1 (f i) (round (x i))
        let j := fun i => round ((r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i)))*p.1+
          2*(round (x i)-round (x₀ i))*(e i*p.1+v i*p.2)
        |(z 0-round (z 0))-(z 1-round (z 1))| ≤ Δ →
        |roundedMinorArcLinearForm (f 0) (x₀ 0) (e 0) (r 0) (s 0) p.1 p.2-
          roundedMinorArcLinearForm (f 1) (x₀ 1) (e 1) (r 1) (s 1) p.1 p.2-
          ((round (z 0)-j 0)-(round (z 1)-j 1):ℤ)| ≤
          Δ+nonlinearResidualConstant σ δ*(K:ℝ)*(D 0+D 1)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_constructed_sector_nonlinear K σ δ T M N R Δ l w H F A W x₀ L U e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hL hU hr hdet hl hlw hdenl hdenw hLdist hUdist hcube

example (M N : ℕ) :
    (M:ℝ)*N/4 ≤
      ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)).filter
        (fun p => Nat.Coprime p.1 p.2)).card:ℝ) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.coprime_rectangle_card_lower M N

example
    {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hdet : a*d-b*c=1) (hc : 0 < c) (hd : 0 < d)
    (hcK : 4*c ≤ (K:ℤ)) (hdK : 4*d ≤ (K:ℤ))
    (hl : 0 < l) (hlw : l ≤ w)
    (ha : l*(c:ℝ) ≤ a ∧ (a:ℝ) ≤ w*c)
    (hb : l*(d:ℝ) ≤ b ∧ (b:ℝ) ≤ w*d) :
    (K:ℝ)^2/(64*(c:ℝ)*d) ≤ ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
      (fun p => b*p.2 < d*p.1 ∧ c*p.1 < a*p.2)).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_cone_fareySector_interior_card_lower K a b c d l w hdet hc hd hcK hdK hl hlw ha hb

example {a b c d : ℤ}
    (hc : 0 < c) (hd : 0 < d) (ha : IsCoprime a c) (hb : IsCoprime b d)
    (hdet : 1 < a*d-b*c) :
    ∃ m n : ℤ, 0 < n ∧ n ≤ max c d ∧ IsCoprime m n ∧
      0 < a*n-m*c ∧ a*n-m*c < a*d-b*c ∧
      0 < m*d-b*n ∧ m*d-b*n < a*d-b*c :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rational_interval_determinant_split a b c d hc hd ha hb hdet

example
    {K : ℕ} {a b c d : ℤ} {l w : ℝ}
    (hc : 0 < c) (hd : 0 < d) (ha : IsCoprime a c) (hb : IsCoprime b d)
    (hdet : 0 < a*d-b*c) (hcK : 4*c ≤ (K:ℤ)) (hdK : 4*d ≤ (K:ℤ))
    (hl : 0 < l) (hlw : l ≤ w)
    (hsa : l ≤ (a:ℝ)/c ∧ (a:ℝ)/c ≤ w)
    (hsb : l ≤ (b:ℝ)/d ∧ (b:ℝ)/d ≤ w) :
    ((a:ℝ)/c-(b:ℝ)/d)*(K:ℝ)^2/64 ≤
      ((TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).filter
        (fun p => (b:ℝ)/d < (p.1:ℝ)/p.2 ∧ (p.1:ℝ)/p.2 < (a:ℝ)/c)).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rational_interval_fareySector_interior_card_lower K a b c d l w hc hd ha hb hdet hcK hdK hl hlw hsa hsb

example {H : ℕ} {x Δ : ℝ} {r : ℚ}
    (hΔ : 0 < Δ) (hH : 16*r.den ≤ H)
    (hscale : 8 ≤ Δ*(H:ℝ)*r.den) (hx : |x-(r:ℝ)| ≤ Δ) :
    ∃ q : ℚ, q.den ≤ H ∧ |x-(q:ℝ)| ≤ Δ/8 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.exists_rational_near_anchor H x Δ r hΔ hH hscale hx

example {H : ℕ} {l w : ℝ} {r : ℚ}
    (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hH : 16*r.den ≤ H) (hscale : 8 ≤ (w-l)*(H:ℝ)*r.den) :
    ∃ a b : ℚ, a.den ≤ H ∧ b.den ≤ H ∧
      w-(w-l)/4 ≤ (a:ℝ) ∧ (a:ℝ) ≤ w ∧
      l ≤ (b:ℝ) ∧ (b:ℝ) ≤ l+(w-l)/4 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.exists_rational_inner_endpoints H l w r hlw hr hH hscale

example
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    (w-l)*(K:ℝ)^2/128 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_card_lower_source_scale K l w r hl hlw hr hden hscale

example
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hl : 0 < l) (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    max ((w-l)*(K:ℝ)^2/128:ℝ) 2 ≤
      (TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_source_density_gate K l w r hl hlw hr hden hscale

example
    {N : ℕ} {l v ν r s ν₁ r₁ s₁ x₀ d ε α β δ : ℝ} {a₀ : ℚ}
    (hl : 0 < l) (hv : 1 ≤ v) (hlv : l < v) (hx₀ : x₀ ∈ Set.Icc l v)
    (ha₀ : (a₀:ℝ) ∈ Set.Icc l v) (hcut : 64*a₀.den ≤ N)
    (hscale : 64 ≤ (v-l)*(N:ℝ)*a₀.den)
    (hν : ν ≠ 0) (hr : r ≠ 0) (hν₁ : 0 < ν₁) (hr₁ : r₁ ≠ 0) (hd : 0 < d) (hδ : 0 ≤ δ)
    (hden : ∀ y ∈ Set.Icc l v, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l v, d ≤ r₁*y+s₁)
    (hratio : ∀ y ∈ Set.Icc l v, |ν₁*(r₁*y+s₁)^3/(ν*(r*y+s)^3)-1| ≤ ε)
    (hnear : ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-
        (p.2:ℝ)*rationalPhase ν r s ν₁ r₁ s₁ ((p.1:ℝ)/(p.2:ℝ))-b| ≤ δ)
    (hbudget : 196608*(δ+(N:ℝ)*ε*(v-l)^2/(3*ν₁*d^3))*v < (v-l)/128) :
    let g := rationalPhase ν r s ν₁ r₁ s₁
    ∀ p ∈ TaoTrudgianYang2025.HuxleyLinearForm.fareySector N l v, ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/(p.2:ℝ))-b| ≤ δ →
      b=p.1*round (α-deriv g x₀)+p.2*round (β-g x₀+x₀*deriv g x₀) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.sector_nonlinear_integer_labels_source_density N l v ν r s ν₁ r₁ s₁ x₀ d ε α β δ a₀ hl hv hlv hx₀ ha₀ hcut hscale hν hr hν₁ hr₁ hd hδ hden hden₁ hratio hnear hbudget

end HuxleyDensityRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.mem_rationalInterval_iff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalInterval_card_eq
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalInterval_card_lower_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_growth
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_width
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rational_curvature_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rational_curvature_count_real
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareyCurvatureCoordinates_card
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.mem_fareyCurvatureCoordinates_iff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareyCurvatureCoordinates_positive
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_curvature_count

namespace HuxleySignedCurvatureRegression

open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example {K : ℕ} {l w : ℝ} {p : ℤ × ℤ}
    (hlw : l ≤ w) :
    p ∈ rationalInterval K l w ↔ 1 ≤ p.2 ∧ p.2 ≤ K ∧
      IsCoprime p.1 p.2 ∧ l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ w*p.2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.mem_rationalInterval_iff K l w p hlw

example (K : ℕ) (l w : ℝ) :
    (rationalInterval K l w).card =
      (HuxleyLinearForm.fareySector K (l+(⌈1-l⌉:ℤ)) (w+(⌈1-l⌉:ℤ))).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalInterval_card_eq K l w

example
    {K : ℕ} {l w : ℝ} {r : ℚ}
    (hlw : l < w) (hr : (r:ℝ) ∈ Set.Icc l w)
    (hden : 64*r.den ≤ K) (hscale : 64 ≤ (w-l)*(K:ℝ)*r.den) :
    (w-l)*(K:ℝ)^2/128 ≤ (rationalInterval K l w).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalInterval_card_lower_source_scale K l w r hlw hr hden hscale

example
    {σ δ T M A W x y : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo 0 W) (hy : y ∈ Set.Ioo 0 W) (hxy : x ≤ y) :
    let f := heathBrownPhysicalPhase F T M A 1
    modelPhaseThirdLower σ*T/(2*M^3)*(y-x) ≤
      iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_growth σ δ T M A W x y F hσ hδ hF hT hM hA hW hx hy hxy

example
    {σ δ T M A W L U R : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo 0 W) (hU : U ∈ Set.Ioo 0 W) (hLU : L ≤ U)
    (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3) :
    let f := heathBrownPhysicalPhase F T M A 1
    modelPhaseThirdLower σ/(2*R^2) ≤
      iteratedDeriv 2 f U/2-iteratedDeriv 2 f L/2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_width σ δ T M A W L U R F hσ hδ hF hT hM hA hW hL hU hLU hR hscale

example
    {K : ℕ} {σ δ T M A W L U R : ℝ} {F : ℝ → ℝ} {r : ℚ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hLU : L < U) (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3)
    (hcut : 64*r.den ≤ K) (hmajor : 128*R^2 ≤ modelPhaseThirdLower σ*(K:ℝ)*r.den) :
    let f := heathBrownPhysicalPhase F T M A 1
    let l := iteratedDeriv 2 f L/2
    let w := iteratedDeriv 2 f U/2
    let S := rationalInterval K l w
    (r:ℝ) ∈ Set.Icc l w →
    modelPhaseThirdLower σ*(K:ℝ)^2/(256*R^2) ≤ S.card ∧
      ∀ p ∈ S, ∃ x ∈ Set.Icc L U, iteratedDeriv 2 f x/2=(p.1:ℝ)/p.2 ∧
        (round x:ℝ) ∈ Set.Ioo 0 W ∧
        |iteratedDeriv 2 f (round x)/2-(p.1:ℝ)/p.2| ≤
          T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rational_curvature_count K σ δ T M A W L U R F r hσ hδ hF hT hM hA hW hL hU hLU hR hscale hcut hmajor

example
    {σ δ T M A W L U R Q : ℝ} {F : ℝ → ℝ} {r : ℚ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hLU : L < U) (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3)
    (hcut : 128*(r.den:ℝ) ≤ Q) (hmajor : 256*R^2 ≤ modelPhaseThirdLower σ*Q*r.den) :
    let f := heathBrownPhysicalPhase F T M A 1
    let l := iteratedDeriv 2 f L/2
    let w := iteratedDeriv 2 f U/2
    let S := rationalInterval ⌊Q⌋₊ l w
    (r:ℝ) ∈ Set.Icc l w →
    modelPhaseThirdLower σ*Q^2/(1024*R^2) ≤ S.card ∧
      ∀ p ∈ S, 1 ≤ p.2 ∧ (p.2:ℝ) < 2*Q ∧ IsCoprime p.1 p.2 ∧
        ∃ x ∈ Set.Icc L U, iteratedDeriv 2 f x/2=(p.1:ℝ)/p.2 ∧
          (round x:ℝ) ∈ Set.Ioo 0 W ∧
          |iteratedDeriv 2 f (round x)/2-(p.1:ℝ)/p.2| ≤
            T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rational_curvature_count_real σ δ T M A W L U R Q F r hσ hδ hF hT hM hA hW hL hU hLU hR hscale hcut hmajor

example {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    (hdet : v*r-e*s=1) :
    (fareyCurvatureCoordinates K l w e r v s).card=(rationalInterval K l w).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareyCurvatureCoordinates_card K l w e r v s hdet

example {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    {p : ℤ × ℤ} (hlw : l ≤ w) (hdet : v*r-e*s=1) :
    p ∈ fareyCurvatureCoordinates K l w e r v s ↔
      1 ≤ r*p.1+s*p.2 ∧ r*p.1+s*p.2 ≤ K ∧ IsCoprime p.1 p.2 ∧
        l*((r*p.1+s*p.2:ℤ):ℝ) ≤ (e*p.1+v*p.2:ℤ) ∧
        ((e*p.1+v*p.2:ℤ):ℝ) ≤ w*((r*p.1+s*p.2:ℤ):ℝ) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.mem_fareyCurvatureCoordinates_iff K l w e r v s p hlw hdet

example {K : ℕ} {l w : ℝ} {e r v s : ℤ}
    {p : ℤ × ℤ} (hlw : l ≤ w) (hr : 0 < r) (hs : 0 < s)
    (hl : (e:ℝ)/r < l) (hw : w < (v:ℝ)/s)
    (hp : p ∈ fareyCurvatureCoordinates K l w e r v s) : 0 < p.1 ∧ 0 < p.2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareyCurvatureCoordinates_positive K l w e r v s p hlw hr hs hl hw hp

example
    {σ δ T M A W L U R Q : ℝ} {F : ℝ → ℝ} {a₀ : ℚ} {e r v s : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hLU : L < U) (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3)
    (hcut : 128*(a₀.den:ℝ) ≤ Q) (hmajor : 256*R^2 ≤ modelPhaseThirdLower σ*Q*a₀.den)
    (hdet : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let l := iteratedDeriv 2 f L/2
    let w := iteratedDeriv 2 f U/2
    let S := fareyCurvatureCoordinates ⌊Q⌋₊ l w e r v s
    (a₀:ℝ) ∈ Set.Icc l w → (e:ℝ)/r < l → w < (v:ℝ)/s →
    modelPhaseThirdLower σ*Q^2/(1024*R^2) ≤ S.card ∧
      ∀ p ∈ S, 0 < p.1 ∧ 0 < p.2 ∧ IsCoprime p.1 p.2 ∧
        1 ≤ r*p.1+s*p.2 ∧ ((r*p.1+s*p.2:ℤ):ℝ) < 2*Q ∧
        ∃ x ∈ Set.Icc L U,
          iteratedDeriv 2 f x/2=((e*p.1+v*p.2:ℤ):ℝ)/((r*p.1+s*p.2:ℤ):ℝ) ∧
          (round x:ℝ) ∈ Set.Ioo 0 W ∧
          |iteratedDeriv 2 f (round x)/2-
            ((e*p.1+v*p.2:ℤ):ℝ)/((r*p.1+s*p.2:ℤ):ℝ)| ≤
            T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_curvature_count σ δ T M A W L U R Q F a₀ e r v s hσ hδ hF hT hM hA hW hL hU hLU hR hscale hcut hmajor hdet hr hs

end HuxleySignedCurvatureRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_minorArcCoordinate_growth
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_eight_window_points
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_difference
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_mem_interval
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_rational_anchor
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.completeSector_density_from_curvature
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_complete_sector_entry

namespace HuxleyGeometryRegression

open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ δ T M A W x y μ e r v s : ℝ} {F : ℝ → ℝ} (u t : Fin 2 → ℝ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo 0 W) (hy : y ∈ Set.Ioo 0 W) (hxy : x ≤ y)
    (hμ : 0 < μ) (hr : r ≠ 0) (ht : ∀ i, t i ≠ 0)
    (hq : ∀ i, r*u i+s*t i ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f x/2=(e*u 0+v*t 0)/(r*u 0+s*t 0) →
    iteratedDeriv 2 f y/2=(e*u 1+v*t 1)/(r*u 1+s*t 1) →
    modelPhaseThirdLower σ*T/(6*μ*M^3)*(y-x) ≤
      minorArcCoordinate μ r s (u 1/t 1)-minorArcCoordinate μ r s (u 0/t 0) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_minorArcCoordinate_growth σ δ T M A W x y μ e r v s F u t hσ hδ hF hT hM hA hW hx hy hxy hμ hr ht hq hdet

example
    {σ δ T M A W R Q μ H : ℝ} {F : ℝ → ℝ} {e r v s : ℤ}
    (L U : Fin 8 → ℝ) (a₀ : Fin 8 → ℚ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : ∀ i, L i ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hU : ∀ i, U i ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hLU : ∀ i, L i < U i) (hR : 0 < R)
    (hscale : ∀ i, T*(U i-L i)*R^2=M^3)
    (hcut : ∀ i, 128*((a₀ i).den:ℝ) ≤ Q)
    (hmajor : ∀ i, 256*R^2 ≤ modelPhaseThirdLower σ*Q*(a₀ i).den)
    (hdet : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s)
    (hμ : 0 < μ) (hH : 0 < H) (hgap : ∀ i : Fin 7, H ≤ L i.succ-U i.castSucc) :
    let f := heathBrownPhysicalPhase F T M A 1
    let l := fun i => iteratedDeriv 2 f (L i)/2
    let w := fun i => iteratedDeriv 2 f (U i)/2
    let S := fun i => fareyCurvatureCoordinates ⌊Q⌋₊ (l i) (w i) e r v s
    (∀ i, (a₀ i:ℝ) ∈ Set.Icc (l i) (w i)) →
    (∀ i, (e:ℝ)/r < l i) → (∀ i, w i < (v:ℝ)/s) →
    ∃ (p : Fin 8 → ℤ × ℤ) (x : Fin 8 → ℝ),
      (∀ i, p i ∈ S i ∧ x i ∈ Set.Icc (L i) (U i) ∧
        iteratedDeriv 2 f (x i)/2=
          ((e*(p i).1+v*(p i).2:ℤ):ℝ)/((r*(p i).1+s*(p i).2:ℤ):ℝ) ∧
        (round (x i):ℝ) ∈ Set.Ioo 0 W ∧
        |iteratedDeriv 2 f (round (x i))/2-
          ((e*(p i).1+v*(p i).2:ℤ):ℝ)/((r*(p i).1+s*(p i).2:ℤ):ℝ)| ≤
          T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3)) ∧
      StrictAnti (fun i => ((p i).1:ℝ)/(p i).2) ∧
      ∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*H ≤
        minorArcCoordinate μ r s (((p i.succ).1:ℝ)/(p i.succ).2)-
        minorArcCoordinate μ r s (((p i.castSucc).1:ℝ)/(p i.castSucc).2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_eight_window_points σ δ T M A W R Q μ H F e r v s L U a₀ hσ hδ hF hT hM hA hW hL hU hLU hR hscale hcut hmajor hdet hr hs hμ hH hgap

example {e r v s x y : ℝ}
    (hdet : v*r-e*s=1) (hx : r*x-e ≠ 0) (hy : r*y-e ≠ 0) :
    (v-s*x)/(r*x-e)-(v-s*y)/(r*y-e)=(y-x)/((r*x-e)*(r*y-e)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_difference e r v s x y hdet hx hy

example {e r v s l w x : ℝ}
    (hdet : v*r-e*s=1) (hr : 0 < r) (hl : 0 < r*l-e)
    (hx : x ∈ Set.Icc l w) :
    (v-s*x)/(r*x-e) ∈ Set.Icc ((v-s*w)/(r*w-e)) ((v-s*l)/(r*l-e)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_mem_interval e r v s l w x hdet hr hl hx

example {e r v s : ℤ} {a : ℚ}
    (hdet : v*r-e*s=1) (hpos : 0 < r*a.num-e*a.den) :
    let b : ℚ := ((v*a.den-s*a.num:ℤ):ℚ)/((r*a.num-e*a.den:ℤ):ℚ)
    (b.den:ℤ)=r*a.num-e*a.den ∧
      (b:ℝ)=((v:ℝ)-s*(a:ℝ))/((r:ℝ)*(a:ℝ)-e) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_rational_anchor e r v s a hdet hpos

example
    {e r v s : ℤ} {a : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s)
    (hlw : l < w) (hl : (e:ℝ)/r < l) (hw : w < (v:ℝ)/s)
    (ha : (a:ℝ) ∈ Set.Icc l w)
    (hdyad : (r:ℝ)*w-e ≤ 2*((r:ℝ)*l-e))
    (hcut : 256*(a.den:ℝ) ≤ Q) (hscale : 256 ≤ (w-l)*Q*a.den) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊Q*((r:ℝ)*l-e)⌋₊
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ (HuxleyLinearForm.fareySector K α β).card ∧
      ∀ p ∈ HuxleyLinearForm.fareySector K α β,
        0 < (r:ℝ)*p.1+s*p.2 ∧ (r:ℝ)*p.1+s*p.2 ≤ Q ∧
        ((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∈ Set.Icc l w :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.completeSector_density_from_curvature e r v s a l w Q hdet hr hs hlw hl hw ha hdyad hcut hscale

example
    {σ δ T M A W L U R Q : ℝ} {F : ℝ → ℝ} {a : ℚ} {e r v s : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hLU : L < U) (hR : 0 < R) (hscale : T*(U-L)*R^2=M^3)
    (hcut : 256*(a.den:ℝ) ≤ Q) (hmajor : 512*R^2 ≤ modelPhaseThirdLower σ*Q*a.den)
    (hdet : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let l := iteratedDeriv 2 f L/2
    let w := iteratedDeriv 2 f U/2
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊Q*((r:ℝ)*l-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    (a:ℝ) ∈ Set.Icc l w → (e:ℝ)/r < l → w < (v:ℝ)/s →
    (r:ℝ)*w-e ≤ 2*((r:ℝ)*l-e) →
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ S.card ∧
      ∀ p ∈ S, 0 < (r:ℝ)*p.1+s*p.2 ∧ (r:ℝ)*p.1+s*p.2 ≤ Q ∧
        ∃ x ∈ Set.Icc L U,
          iteratedDeriv 2 f x/2=((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∧
          (round x:ℝ) ∈ Set.Ioo 0 W ∧
          |iteratedDeriv 2 f (round x)/2-((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2)| ≤
            T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_complete_sector_entry σ δ T M A W L U R Q F a e r v s hσ hδ hF hT hM hA hW hL hU hLU hR hscale hcut hmajor hdet hr hs

end HuxleyGeometryRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_eight_block_indices
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_consecutive_window_points
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubicCoefficient_bounds
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubicCoefficient_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_consecutive_window_points_uniform
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_consecutive_window_long_block
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCenterLabels_card_le
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.mem_minorArcCenterLabels_iff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_compatible_center_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCenterLabels_family_card_le
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.linearization_pair_bound_with_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_two_choice_nonlinear

namespace HuxleyBlockBoundaryRegression

open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example {B : ℕ} (hB : 32 ≤ B) :
    ∃ j : Fin 8 → Fin B, StrictMono j ∧
      ∀ i : Fin 7, (B:ℝ)/16 ≤ ((j i.succ).val:ℝ)-(j i.castSucc).val-1 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.exists_eight_block_indices B hB

example
    {B : ℕ} {σ δ T M A W R Q μ Z N : ℝ} {F : ℝ → ℝ} {e r v s : ℤ}
    (a₀ : Fin B → ℚ) (hB : 32 ≤ B)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hN : 0 < N) (hZ : (1/2:ℝ) < Z) (hZW : Z+(B:ℝ)*N < W-1/2)
    (hR : 0 < R) (hscale : T*N*R^2=M^3)
    (hcut : ∀ i, 128*((a₀ i).den:ℝ) ≤ Q)
    (hmajor : ∀ i, 256*R^2 ≤ modelPhaseThirdLower σ*Q*(a₀ i).den)
    (hdet : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s) (hμ : 0 < μ) :
    let f := heathBrownPhysicalPhase F T M A 1
    let L := fun i : Fin B => Z+(i.val:ℝ)*N
    let U := fun i : Fin B => L i+N
    let l := fun i => iteratedDeriv 2 f (L i)/2
    let w := fun i => iteratedDeriv 2 f (U i)/2
    let S := fun i => fareyCurvatureCoordinates ⌊Q⌋₊ (l i) (w i) e r v s
    (∀ i, (a₀ i:ℝ) ∈ Set.Icc (l i) (w i)) →
    (∀ i, (e:ℝ)/r < l i) → (∀ i, w i < (v:ℝ)/s) →
    ∃ j : Fin 8 → Fin B, StrictMono j ∧
      ∃ (p : Fin 8 → ℤ × ℤ) (x : Fin 8 → ℝ),
        (∀ i, p i ∈ S (j i) ∧ x i ∈ Set.Icc (L (j i)) (U (j i)) ∧
          iteratedDeriv 2 f (x i)/2=
            ((e*(p i).1+v*(p i).2:ℤ):ℝ)/((r*(p i).1+s*(p i).2:ℤ):ℝ) ∧
          (round (x i):ℝ) ∈ Set.Ioo 0 W ∧
          |iteratedDeriv 2 f (round (x i))/2-
            ((e*(p i).1+v*(p i).2:ℤ):ℝ)/((r*(p i).1+s*(p i).2:ℤ):ℝ)| ≤
            T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3)) ∧
        StrictAnti (fun i => ((p i).1:ℝ)/(p i).2) ∧
        ∀ i : Fin 7, modelPhaseThirdLower σ*T/(96*μ*M^3)*(B:ℝ)*N ≤
          minorArcCoordinate μ r s (((p i.succ).1:ℝ)/(p i.succ).2)-
          minorArcCoordinate μ r s (((p i.castSucc).1:ℝ)/(p i.castSucc).2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_consecutive_window_points B σ δ T M A W R Q μ Z N F e r v s a₀ hB hσ hδ hF hT hM hA hW hN hZ hZW hR hscale hcut hmajor hdet hr hs hμ

example
    {σ δ T M A W z : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hz : z ∈ Set.Ioo 0 W) :
    let μ := iteratedDeriv 3 (heathBrownPhysicalPhase F T M A 1) z/6
    modelPhaseThirdLower σ*T/(6*M^3) ≤ μ ∧
      μ ≤ (σ*(σ+1)+1)*T/(6*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubicCoefficient_bounds σ δ T M A W z F hσ hδ hF hT hM hA hW hz

example
    {σ δ T M A W z N R : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hz : z ∈ Set.Ioo 0 W) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) :
    let μ := iteratedDeriv 3 (heathBrownPhysicalPhase F T M A 1) z/6
    0 < μ ∧ 1 ≤ (6/modelPhaseThirdLower σ)*μ*N*R^2 ∧
      modelPhaseThirdLower σ/(16*(σ*(σ+1)+1)) ≤ modelPhaseThirdLower σ*T/(96*μ*M^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_cubicCoefficient_source_scale σ δ T M A W z N R F hσ hδ hF hT hM hA hW hz hN hR hscale

example
    {B : ℕ} {σ δ T M A W R Q z Z N : ℝ} {F : ℝ → ℝ} {e r v s : ℤ}
    (a₀ : Fin B → ℚ) (hB : 32 ≤ B)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hN : 0 < N) (hZ : (1/2:ℝ) < Z) (hZW : Z+(B:ℝ)*N < W-1/2)
    (hR : 0 < R) (hscale : T*N*R^2=M^3)
    (hcut : ∀ i, 128*((a₀ i).den:ℝ) ≤ Q)
    (hmajor : ∀ i, 256*R^2 ≤ modelPhaseThirdLower σ*Q*(a₀ i).den)
    (hdet : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s) (hz : z ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := iteratedDeriv 3 f z/6
    let L := fun i : Fin B => Z+(i.val:ℝ)*N
    let U := fun i : Fin B => L i+N
    let l := fun i => iteratedDeriv 2 f (L i)/2
    let w := fun i => iteratedDeriv 2 f (U i)/2
    let S := fun i => fareyCurvatureCoordinates ⌊Q⌋₊ (l i) (w i) e r v s
    (∀ i, (a₀ i:ℝ) ∈ Set.Icc (l i) (w i)) →
    (∀ i, (e:ℝ)/r < l i) → (∀ i, w i < (v:ℝ)/s) →
    1 ≤ (6/modelPhaseThirdLower σ)*μ*N*R^2 ∧
    ∃ j : Fin 8 → Fin B, StrictMono j ∧
      ∃ (p : Fin 8 → ℤ × ℤ) (x : Fin 8 → ℝ),
        (∀ i, p i ∈ S (j i) ∧ x i ∈ Set.Icc (L (j i)) (U (j i)) ∧
          iteratedDeriv 2 f (x i)/2=
            ((e*(p i).1+v*(p i).2:ℤ):ℝ)/((r*(p i).1+s*(p i).2:ℤ):ℝ) ∧
          (round (x i):ℝ) ∈ Set.Ioo 0 W ∧
          |iteratedDeriv 2 f (round (x i))/2-
            ((e*(p i).1+v*(p i).2:ℤ):ℝ)/((r*(p i).1+s*(p i).2:ℤ):ℝ)| ≤
            T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3)) ∧
        StrictAnti (fun i => ((p i).1:ℝ)/(p i).2) ∧
        ∀ i : Fin 7, modelPhaseThirdLower σ/(16*(σ*(σ+1)+1))*(B:ℝ)*N ≤
          minorArcCoordinate μ r s (((p i.succ).1:ℝ)/(p i.succ).2)-
          minorArcCoordinate μ r s (((p i.castSucc).1:ℝ)/(p i.castSucc).2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_consecutive_window_points_uniform B σ δ T M A W R Q z Z N F e r v s a₀ hB hσ hδ hF hT hM hA hW hN hZ hZW hR hscale hcut hmajor hdet hr hs hz

example
    {B : ℕ} {σ δ T M A W R Q z Z N μ₁ r₁ s₁ d K C D ya yb : ℝ} {F : ℝ → ℝ} {e r v s : ℤ}
    (a₀ : Fin B → ℚ) (hB : 32 ≤ B)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hN : 0 < N) (hZ : (1/2:ℝ) < Z) (hZW : Z+(B:ℝ)*N < W-1/2)
    (hR : 0 < R) (hscale : T*N*R^2=M^3)
    (hcut : ∀ i, 128*((a₀ i).den:ℝ) ≤ Q)
    (hmajor : ∀ i, 256*R^2 ≤ modelPhaseThirdLower σ*Q*(a₀ i).den)
    (hdet : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s) (hz : z ∈ Set.Ioo 0 W)
    (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0) (hd : 0 < d) (hK : 0 ≤ K) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := iteratedDeriv 3 f z/6
    let L := fun i : Fin B => Z+(i.val:ℝ)*N
    let U := fun i : Fin B => L i+N
    let l := fun i => iteratedDeriv 2 f (L i)/2
    let w := fun i => iteratedDeriv 2 f (U i)/2
    let S := fun i => fareyCurvatureCoordinates ⌊Q⌋₊ (l i) (w i) e r v s
    (∀ i, (a₀ i:ℝ) ∈ Set.Icc (l i) (w i)) →
    (∀ i, (e:ℝ)/r < l i) → (∀ i, w i < (v:ℝ)/s) →
    (∀ i, ∀ p ∈ S i, ((p.1:ℝ)/p.2) ∈ Set.Icc ya yb) →
    (∀ y ∈ Set.Icc ya yb, d ≤ (r:ℝ)*y+s ∧ (r:ℝ)*y+s ≤ 2*d) →
    (∀ y ∈ Set.Icc ya yb, r₁*y+s₁ ≠ 0) →
    (∀ y ∈ Set.Icc ya yb, |r₁*y+s₁| ≤ 4*d) →
    (∀ y ∈ Set.Icc ya yb, (1:ℝ)/2 ≤ (r₁*y+s₁)/((r:ℝ)*y+s)) →
    (∀ i, ∀ p ∈ S i,
      |C*((p.1:ℝ)/p.2)+D-rationalPhase μ r s μ₁ r₁ s₁ ((p.1:ℝ)/p.2)| ≤
        K*R^2/|(r:ℝ)*minorArcCoordinate μ r s ((p.1:ℝ)/p.2)|) →
    |(r:ℝ)*s₁-s*r₁| ≤ 1024*K*(6/modelPhaseThirdLower σ)*R^4/
      ((modelPhaseThirdLower σ/(16*(σ*(σ+1)+1))*(B:ℝ))^3*N^2) ∧
      ∃ a b : ℝ, ya ≤ a ∧ a < b ∧ b ≤ yb ∧
        (modelPhaseThirdLower σ/(16*(σ*(σ+1)+1))*(B:ℝ))*N ≤
          |minorArcCoordinate μ r s b-minorArcCoordinate μ r s a| ∧
        ∀ q ∈ Set.Icc a b,
          |μ₁*(r₁*q+s₁)^3/(μ*((r:ℝ)*q+s)^3)-1| ≤
            256*(|μ₁|/μ)*K*R^2/
              ((modelPhaseThirdLower σ/(16*(σ*(σ+1)+1))*(B:ℝ))^2*N^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_consecutive_window_long_block B σ δ T M A W R Q z Z N μ₁ r₁ s₁ d K C D ya yb F e r v s a₀ hB hσ hδ hF hT hM hA hW hN hZ hZW hR hscale hcut hmajor hdet hr hs hz hμ₁ hr₁ hd hK

example (x ε : ℝ) :
    (minorArcCenterLabels x ε).card ≤ 2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCenterLabels_card_le x ε

example {x ε : ℝ} {n : ℤ} (hε : ε < 1/2) :
    n ∈ minorArcCenterLabels x ε ↔ |x-n| ≤ 1/2+ε :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.mem_minorArcCenterLabels_iff x ε n hε

example {x y ε : ℝ}
    (hε : ε < 1/2) (hnear : |(x-y)-round (x-y)| ≤ ε) :
    ∃ c ∈ minorArcCenterLabels x ε, ∃ d ∈ minorArcCenterLabels y ε,
      c=round x ∧ |(x-c)-(y-d)| ≤ ε :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.exists_compatible_center_labels x y ε hε hnear

example {ι : Type*} (S : Finset ι) (z : ι → ℝ) (ε : ℝ) :
    (S.sigma (fun i => minorArcCenterLabels (z i) ε)).card ≤ 2*S.card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCenterLabels_family_card_le ι S z ε

example {z z₁ L L₁ E E₁ Δ : ℝ} {j j₁ c c₁ : ℤ}
    (hL : |z-j-L| ≤ E) (hL₁ : |z₁-j₁-L₁| ≤ E₁)
    (hfourth : |(z-c)-(z₁-c₁)| ≤ Δ) :
    |(L-L₁)-((c-j)-(c₁-j₁):ℤ)| ≤ Δ+E+E₁ :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.linearization_pair_bound_with_labels z z₁ L L₁ E E₁ Δ j j₁ c c₁ hL hL₁ hfourth

example
    {σ δ T M N R Δ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hΔ : Δ < 1/2)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let z := fun i => q i*iteratedDeriv 1 (f i) (round (x₁ i))
    let j := fun i => round ((r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i)))*u+
      2*n i*(e i*u+v i*t)
    let L := fun i => roundedMinorArcLinearForm (f i) (x₀ i) (e i) (r i) (s i) u t
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)|^3 ≤ M*R^2) →
    |(z 0-z 1)-round (z 0-z 1)| ≤ Δ →
    ∃ c ∈ minorArcCenterLabels (z 0) Δ, ∃ c₁ ∈ minorArcCenterLabels (z 1) Δ,
      c=round (z 0) ∧ |(z 0-c)-(z 1-c₁)| ≤ Δ ∧
      |(L 0-L 1)-((c-j 0)-(c₁-j 1):ℤ)| ≤
        Δ+nonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_two_choice_nonlinear σ δ T M N R Δ u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hΔ hscale hA hW hx₀ hx₁ hr ht hq hdet

end HuxleyBlockBoundaryRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_modular_inverse
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_modular_label_expansion
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_second_condition_cancellation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.actual_derivative_second_condition_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.centered_modular_integer_shift
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.actual_derivative_second_condition_centered
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.common_label_modular_reduction
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.actual_derivative_pair_second_condition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.small_real_of_centered_perturbation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.second_condition_error_difference
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.second_condition_error_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_second_condition_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_derivative_coordinate
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_second_condition_derivative_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.second_condition_taylor_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_second_condition_derivative_bound

namespace HuxleySecondConditionRegression
open TaoTrudgianYang2025.HuxleyRationalPhase

example {e r v s u t tb ub : ℤ}
    (hdet : v*r-e*s=1) (hbez : t*tb+u*ub=1) :
    (e*u+v*t)*(r*tb-s*ub) =
      (r*u+s*t)*(e*tb-v*ub)+1 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_modular_inverse e r v s u t tb ub hdet hbez

example {e r v s u t tb ub n c h : ℤ}
    (hdet : v*r-e*s=1) (hbez : t*tb+u*ub=1) :
    (r*tb-s*ub)*(c*u+2*n*(e*u+v*t)+h) =
      (r*u+s*t)*(c*tb+2*n*(e*tb-v*ub))+
        (2*n-c*s)+(r*tb-s*ub)*h :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_modular_label_expansion e r v s u t tb ub n c h hdet hbez

example
    {r s u t tb ub n c θ γ η h : ℝ}
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0)
    (hbez : t*tb+u*ub=1)
    (hH : (c*s-n)*t/r+θ*(r*u+s*t)/r+γ=h+η) :
    (2*n-c*s)/(r*u+s*t)+(r*tb-s*ub)*h/(r*u+s*t) =
      n/(r*u+s*t)+θ/t-ub*h/t+r*(γ-η)/(t*(r*u+s*t)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_second_condition_cancellation r s u t tb ub n c θ γ η h hr ht hq hbez hH

example
    {e r v s u t tb ub n cnew : ℤ} {d₀ d₁ : ℝ}
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0)
    (hdet : v*r-e*s=1) (hbez : t*tb+u*ub=1) :
    let q : ℝ := r*u+s*t
    let c := round ((r:ℝ)*d₀)
    let θ := (r:ℝ)*d₀-c
    let η := q*d₁-cnew
    let h := cnew-(c*u+2*n*(e*u+v*t))
    let γ := q*(d₁-d₀-2*(e:ℝ)*n/r-(n:ℝ)*t/(r*q))
    ((r*tb-s*ub:ℤ):ℝ)*cnew/q =
      ((c*tb+2*n*(e*tb-v*ub):ℤ):ℝ)+
      ((n:ℝ)/q+θ/t-(ub:ℝ)*h/t+(r:ℝ)*(γ-η)/(t*q)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.actual_derivative_second_condition_identity e r v s u t tb ub n cnew d₀ d₁ hr ht hq hdet hbez

example {x y : ℝ} {k : ℤ}
    (h : x=(k:ℝ)+y) :
    x-round x=y-round y :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.centered_modular_integer_shift x y k h

example
    {e r v s u t tb ub n cnew : ℤ} {d₀ d₁ : ℝ}
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0)
    (hdet : v*r-e*s=1) (hbez : t*tb+u*ub=1) :
    let q : ℝ := r*u+s*t
    let c := round ((r:ℝ)*d₀)
    let θ := (r:ℝ)*d₀-c
    let η := q*d₁-cnew
    let h := cnew-(c*u+2*n*(e*u+v*t))
    let γ := q*(d₁-d₀-2*(e:ℝ)*n/r-(n:ℝ)*t/(r*q))
    let X := ((r*tb-s*ub:ℤ):ℝ)*cnew/q
    let Y := (n:ℝ)/q+θ/t-(ub:ℝ)*h/t+(r:ℝ)*(γ-η)/(t*q)
    X-round X=Y-round Y :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.actual_derivative_second_condition_centered e r v s u t tb ub n cnew d₀ d₁ hr ht hq hdet hbez

example {t u tb ub h h₁ a b : ℤ}
    (ht : t ≠ 0) (hbez : t*tb+u*ub=1)
    (hlabel : h-h₁=a*u+b*t) :
    -(ub:ℝ)*((h:ℝ)-h₁)/t =
      -(a:ℝ)/t+((a*tb-b*ub:ℤ):ℝ) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.common_label_modular_reduction t u tb ub h h₁ a b ht hbez hlabel

example
    {e r v s n cnew : Fin 2 → ℤ} {d₀ d₁ : Fin 2 → ℝ}
    {u t tb ub a b : ℤ}
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0)
    (hdet : ∀ i, v i*r i-e i*s i=1) (hbez : t*tb+u*ub=1) :
    let q := fun i => (r i:ℝ)*u+s i*t
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let η := fun i => q i*d₁ i-cnew i
    let h := fun i => cnew i-(c i*u+2*n i*(e i*u+v i*t))
    let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
      (n i:ℝ)*t/(r i*q i))
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew i/q i
    let E := fun i => (r i:ℝ)*(γ i-η i)/(t*q i)
    let Y := (n 0:ℝ)/q 0-(n 1:ℝ)/q 1+(θ 0-θ 1-a)/t+E 0-E 1
    h 0-h 1=a*u+b*t →
      (X 0-X 1)-round (X 0-X 1)=Y-round Y :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.actual_derivative_pair_second_condition e r v s n cnew d₀ d₁ u t tb ub a b hr ht hq hdet hbez

example {x E Δ B : ℝ}
    (hx : |x| < 1/2) (hc : |(x+E)-round (x+E)| ≤ Δ) (hE : |E| ≤ B) :
    |x| ≤ Δ+B :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.small_real_of_centered_perturbation x E Δ B hx hc hE

example
    {r s r₁ s₁ u t γ γ₁ η η₁ : ℝ}
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hq₁ : r₁*u+s₁*t ≠ 0) :
    let q := r*u+s*t
    let q₁ := r₁*u+s₁*t
    r*(γ-η)/(t*q)-r₁*(γ₁-η₁)/(t*q₁) =
      r*γ/(t*q)-r₁*γ₁/(t*q₁)+
      η*(r₁*s-r*s₁)/(q*q₁)+r₁*(η₁-η)/(t*q₁) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.second_condition_error_difference r s r₁ s₁ u t γ γ₁ η η₁ ht hq hq₁

example
    {r s r₁ s₁ u t γ γ₁ η η₁ D D₁ ε Δ : ℝ}
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hq₁ : r₁*u+s₁*t ≠ 0)
    (hγ : |γ| ≤ |r*u+s*t| * D) (hγ₁ : |γ₁| ≤ |r₁*u+s₁*t| * D₁)
    (hη : |η| ≤ 1/2+ε) (hfourth : |η₁-η| ≤ Δ) :
    let q := r*u+s*t
    let q₁ := r₁*u+s₁*t
    |r*(γ-η)/(t*q)-r₁*(γ₁-η₁)/(t*q₁)| ≤
      (|r| * D+|r₁| * D₁)/|t|+
      (1/2+ε)*|r₁*s-r*s₁|/(|q| * |q₁|)+|r₁| * Δ/(|t| * |q₁|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.second_condition_error_bound r s r₁ s₁ u t γ γ₁ η η₁ D D₁ ε Δ ht hq hq₁ hγ hγ₁ hη hfourth

example
    {σ δ T M Δ₂ Δ₄ ε : ℝ} {u t tb ub a b : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ}
    {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 ≤ σ) (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hε : ε < 1/2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let η := fun i => q i*d₁ i-cnew i
    let h := fun i => cnew i-(c i*u+2*n i*(e i*u+v i*t))
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew i/q i
    let Z := (n 0:ℝ)/q 0-(n 1:ℝ)/q 1+(θ 0-θ 1-a)/t
    let D := fun i =>
      T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|(n i:ℝ)|/(2*M^3)+
      5*T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^3/(12*M^4)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    cnew 0 ∈ minorArcCenterLabels (q 0*d₁ 0) ε →
    |η 1-η 0| ≤ Δ₄ →
    h 0-h 1=a*u+b*t →
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    |Z| < 1/2 →
    |Z| ≤ Δ₂+(|(r 0:ℝ)| * D 0+|(r 1:ℝ)| * D 1)/|(t:ℝ)|+
      (1/2+ε)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q 0| * |q 1|)+
      |(r 1:ℝ)| * Δ₄/(|(t:ℝ)| * |q 1|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_second_condition_bound σ δ T M Δ₂ Δ₄ ε u t tb ub a b F A W x₀ x₁ e r v s cnew hσ hF hT hM hε hA hW hx₀ hx₁ hr ht hq hdet hbez

example
    {μ r s μ₁ r₁ s₁ u t : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hq₁ : r₁*u+s₁*t ≠ 0) :
    deriv (rationalPhase μ r s μ₁ r₁ s₁) (u/t)/t =
      -minorArcCoordinate μ r s (u/t)/(r*u+s*t)+
        minorArcCoordinate μ₁ r₁ s₁ (u/t)/(r₁*u+s₁*t) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_derivative_coordinate μ r s μ₁ r₁ s₁ u t hμ hμ₁ hr hr₁ ht hq hq₁

example
    {μ r s μ₁ r₁ s₁ u t n n₁ α A A₁ B : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hq₁ : r₁*u+s₁*t ≠ 0)
    (hn : |n-minorArcCoordinate μ r s (u/t)| ≤ A)
    (hn₁ : |n₁-minorArcCoordinate μ₁ r₁ s₁ (u/t)| ≤ A₁)
    (hsecond : |n/(r*u+s*t)-n₁/(r₁*u+s₁*t)+α/t| ≤ B) :
    |α-deriv (rationalPhase μ r s μ₁ r₁ s₁) (u/t)| ≤
      |t| * (B+A/|r*u+s*t|+A₁/|r₁*u+s₁*t|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_second_condition_derivative_bound μ r s μ₁ r₁ s₁ u t n n₁ α A A₁ B hμ hμ₁ hr hr₁ ht hq hq₁ hn hn₁ hsecond

example {T M N R C₂ C₃ n : ℝ}
    (hM : M ≠ 0) (hN : N ≠ 0) (hR : R ≠ 0) (hscale : T*N*R^2=M^3) :
    T*C₂*n/(2*M^3)+5*T*C₃*n^3/(12*M^4) =
      C₂*n/(2*N*R^2)+5*C₃*n^3/(12*M*N*R^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.second_condition_taylor_source_scale T M N R C₂ C₃ n hM hN hR hscale

example
    {σ δ T M N R Δ₂ Δ₄ ε : ℝ} {u t tb ub a b : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ}
    {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1) (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hε : ε < 1/2)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let η := fun i => q i*d₁ i-cnew i
    let h := fun i => cnew i-(c i*u+2*n i*(e i*u+v i*t))
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew i/q i
    let Z := (n 0:ℝ)/q 0-(n 1:ℝ)/q 1+(θ 0-θ 1-a)/t
    let D := fun i =>
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|(n i:ℝ)|/(2*N*R^2)+
      5*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^3/(12*M*N*R^2)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let V := fun i => (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
      TaoTrudgianYang2025.modelPhaseThirdLower σ+
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    cnew 0 ∈ minorArcCenterLabels (q 0*d₁ 0) ε →
    |η 1-η 0| ≤ Δ₄ →
    h 0-h 1=a*u+b*t →
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    |Z| < 1/2 →
    |θ 0-θ 1-a-deriv (rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)) ((u:ℝ)/t)| ≤
      |(t:ℝ)| * (Δ₂+(|(r 0:ℝ)| * D 0+|(r 1:ℝ)| * D 1)/|(t:ℝ)|+
      (1/2+ε)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q 0| * |q 1|)+
      |(r 1:ℝ)| * Δ₄/(|(t:ℝ)| * |q 1|)+V 0/|q 0|+V 1/|q 1|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_second_condition_derivative_bound σ δ T M N R Δ₂ Δ₄ ε u t tb ub a b F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hN hR hε hscale hA hW hx₀ hx₁ hr ht hq hdet hbez

end HuxleySecondConditionRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalBranch_base_normal_form
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_bound_from_base_coincidences
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_base_difference_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCoordinate_div_eq_branch
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_base_coincidence_difference_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.actual_derivative_base_centered_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_base_coincidence_near_integer
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_base_coincidence_two_choice_nonlinear
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.short_block_taylor_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.short_block_coordinate_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.short_block_phase_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.short_block_fourth_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_fourth
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_two_choice_nonlinear

namespace HuxleyBaseCoincidenceRegression
open TaoTrudgianYang2025.HuxleyRationalPhase

example {μ r s x : ℝ} (hr : r ≠ 0) :
    rationalBranch μ r s x=1/(3*(μ*r^3)*(x+s/r)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalBranch_base_normal_form μ r s x hr

example
    {μ r s μ₁ r₁ s₁ x ε η : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : x+s/r ≠ 0)
    (hthird : |μ₁*r₁^3/(μ*r^3)-1| ≤ ε) (hε : ε ≤ 1/2)
    (hfirst : |s₁/r₁-s/r| ≤ η*|x+s/r|) (hη : η ≤ 1/2) :
    |rationalPhase μ r s μ₁ r₁ s₁ x| ≤
      (12*ε+4*η)*|rationalBranch μ r s x| :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_bound_from_base_coincidences μ r s μ₁ r₁ s₁ x ε η hμ hμ₁ hr hr₁ hx hthird hε hfirst hη

example
    {r s r₁ s₁ u t n n₁ c c₁ θ θ₁ γ γ₁ G G₁ b : ℝ}
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) :
    let H := (c*s-n)*t/r+θ*(r*u+s*t)/r+γ
    let H₁ := (c₁*s₁-n₁)*t/r₁+θ₁*(r₁*u+s₁*t)/r₁+γ₁
    H-H₁-b*t =
      (c*s/r-c₁*s₁/r₁-b)*t-(G/r-G₁/r₁)*t+
      (θ-θ₁)*(r*u+s*t)/r+θ₁*t*(s/r-s₁/r₁)+
      γ-γ₁-(n-G)*t/r+(n₁-G₁)*t/r₁ :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_base_difference_identity r s r₁ s₁ u t n n₁ c c₁ θ θ₁ γ γ₁ G G₁ b hr hr₁

example (μ r s x : ℝ) :
    minorArcCoordinate μ r s x/r=rationalBranch μ r s x :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCoordinate_div_eq_branch μ r s x

example
    {μ r s μ₁ r₁ s₁ u t n n₁ c c₁ θ θ₁ γ γ₁ b
      ε η D₁ D₂ D₄ A A₁ V V₁ : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : u/t+s/r ≠ 0)
    (hthird : |μ₁*r₁^3/(μ*r^3)-1| ≤ ε) (hε : ε ≤ 1/2)
    (hfirstRelative : |s₁/r₁-s/r| ≤ η*|u/t+s/r|) (hη : η ≤ 1/2)
    (hfirst : |s/r-s₁/r₁| ≤ D₁)
    (hsecond : |c*s/r-c₁*s₁/r₁-b| ≤ D₂)
    (hfourth : |θ-θ₁| ≤ D₄) (hcenter : |θ₁| ≤ 1/2)
    (hcoord : |n-minorArcCoordinate μ r s (u/t)| ≤ A)
    (hcoord₁ : |n₁-minorArcCoordinate μ₁ r₁ s₁ (u/t)| ≤ A₁)
    (hγ : |γ| ≤ V) (hγ₁ : |γ₁| ≤ V₁) :
    let H := (c*s-n)*t/r+θ*(r*u+s*t)/r+γ
    let H₁ := (c₁*s₁-n₁)*t/r₁+θ₁*(r₁*u+s₁*t)/r₁+γ₁
    |H-H₁-b*t| ≤
      D₂*|t|+(12*ε+4*η)*|rationalBranch μ r s (u/t)| * |t|+
      D₄*|(r*u+s*t)/r|+(1/2:ℝ)*|t| * D₁+
      V+V₁+A*|t/r|+A₁*|t/r₁| :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_base_coincidence_difference_bound μ r s μ₁ r₁ s₁ u t n n₁ c c₁ θ θ₁ γ γ₁ b ε η D₁ D₂ D₄ A A₁ V V₁ hμ hμ₁ hr hr₁ hx hthird hε hfirstRelative hη hfirst hsecond hfourth hcenter hcoord hcoord₁ hγ hγ₁

example
    {e r v s n : Fin 2 → ℤ} {d₀ d₁ : Fin 2 → ℝ} {u t b : ℤ}
    (hr : ∀ i, r i ≠ 0) (hq : ∀ i, r i*u+s i*t ≠ 0)
    (hdet : ∀ i, v i*r i-e i*s i=1) :
    let q := fun i => (r i:ℝ)*u+s i*t
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
      (n i:ℝ)*t/(r i*q i))
    let H := fun i => ((c i:ℝ)*s i-n i)*t/r i+θ i*q i/r i+γ i
    let z := fun i => q i*d₁ i
    |(z 0-z 1)-round (z 0-z 1)| ≤ |H 0-H 1-(b:ℝ)*t| :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.actual_derivative_base_centered_bound e r v s n d₀ d₁ u t b hr hq hdet

example
    {σ δ T M N R ε η D₂ D₄ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hε : ε ≤ 1/2) (hη : η ≤ 1/2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let U := (u:ℝ)/t+(s 0:ℝ)/r 0
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let D := fun i =>
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|(n i:ℝ)|/(2*N*R^2)+
      5*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^3/(12*M*N*R^2)
    let V := fun i => (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
      TaoTrudgianYang2025.modelPhaseThirdLower σ+
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
    let z := fun i => q i*d₁ i
    let Λ := D₂*|(t:ℝ)|+
      (12*ε+4*η)*|rationalBranch (μ 0) (r 0) (s 0) ((u:ℝ)/t)| * |(t:ℝ)|+
      D₄*|q 0/r 0|+(1/2:ℝ)*|(t:ℝ)| * (η*|U|)+
      |q 0| * D 0+|q 1| * D 1+V 0*|(t:ℝ)/r 0|+V 1*|(t:ℝ)/r 1|
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ ε →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ η*|U| →
    |C-round C| ≤ D₂ →
    |θ 0-θ 1| ≤ D₄ →
    |(z 0-z 1)-round (z 0-z 1)| ≤ Λ :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_base_coincidence_near_integer σ δ T M N R ε η D₂ D₄ u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hε hη hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R ε η D₂ D₄ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hε : ε ≤ 1/2) (hη : η ≤ 1/2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let U := (u:ℝ)/t+(s 0:ℝ)/r 0
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let D := fun i =>
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|(n i:ℝ)|/(2*N*R^2)+
      5*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^3/(12*M*N*R^2)
    let V := fun i => (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
      TaoTrudgianYang2025.modelPhaseThirdLower σ+
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
    let z := fun i => q i*d₁ i
    let Λ := D₂*|(t:ℝ)|+
      (12*ε+4*η)*|rationalBranch (μ 0) (r 0) (s 0) ((u:ℝ)/t)| * |(t:ℝ)|+
      D₄*|q 0/r 0|+(1/2:ℝ)*|(t:ℝ)| * (η*|U|)+
      |q 0| * D 0+|q 1| * D 1+V 0*|(t:ℝ)/r 0|+V 1*|(t:ℝ)/r 1|
    let j := fun i => c i*u+2*n i*(e i*u+v i*t)
    let L := fun i => roundedMinorArcLinearForm (f i) (x₀ i) (e i) (r i) (s i) u t
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ ε →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ η*|U| →
    |C-round C| ≤ D₂ →
    |θ 0-θ 1| ≤ D₄ →
    (∀ i, |(n i:ℝ)|^3 ≤ M*R^2) →
    Λ < 1/2 →
    ∃ cnew ∈ minorArcCenterLabels (z 0) Λ, ∃ cnew₁ ∈ minorArcCenterLabels (z 1) Λ,
      cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Λ ∧
      |(L 0-L 1)-((cnew-j 0)-(cnew₁-j 1):ℤ)| ≤
        Λ+nonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_base_coincidence_two_choice_nonlinear σ δ T M N R ε η D₂ D₄ u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hε hη hA hW hx₀ hx₁ hr ht hq hdet

example {C₂ C₃ n M N R : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hn : 0 ≤ n)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hnN : n ≤ N) (hNR : N ≤ R^2) (hcube : N^3 ≤ M*R^2) :
    C₂*n/(2*N*R^2)+5*C₃*n^3/(12*M*N*R^2) ≤ (C₂/2+5*C₃/12)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.short_block_taylor_budget C₂ C₃ n M N R hC₂ hC₃ hn hM hN hR hnN hNR hcube

example {C₂ C₃ κ n M N R Q L : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hκ : 0 < κ) (hn : 0 ≤ n)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 ≤ Q)
    (hnN : n ≤ N) (hNR : N ≤ R^2) (hcube : N^3 ≤ M*R^2)
    (hLQ : L ≤ Q/R^2) :
    L*(C₂/κ+C₃*n^2/(2*κ*M)) ≤ (C₂/κ+C₃/(2*κ))*Q/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.short_block_coordinate_budget C₂ C₃ κ n M N R Q L hC₂ hC₃ hκ hn hM hN hR hQ hnN hNR hcube hLQ

example {C₂ C₃ κ n M N R Q L G : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hκ : 0 < κ) (hn : 0 ≤ n)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hnN : n ≤ N) (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hLQ : L ≤ Q/R^2)
    (hG : |G| ≤ n+(C₂/κ+C₃*n^2/(2*κ*M))) :
    (R^2/N^2)*L*|G| ≤ (1+C₂/κ+C₃/(2*κ))*Q/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.short_block_phase_budget C₂ C₃ κ n M N R Q L G hC₂ hC₃ hκ hn hM hN hR hQ hL hnN hNR hRN hcube hLQ hG

example
    {C₂ C₃ κ M N R Q K n n₁ r r₁ t q q₁ G : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hκ : 0 < κ)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hn : 0 ≤ n) (hn₁ : 0 ≤ n₁) (hnN : n ≤ N) (hn₁N : n₁ ≤ N)
    (hr : 0 < r) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hq₁ : 0 ≤ q₁) (hqQ : q ≤ Q) (hq₁Q : q₁ ≤ Q)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hminr : R^2/N ≤ r) (hgeom : t/r ≤ Q/R^2) (hgeom₁ : t/r₁ ≤ Q/R^2)
    (hG : |G| ≤ n+(C₂/κ+C₃*n^2/(2*κ*M))) :
    let D := fun z => C₂*z/(2*N*R^2)+5*C₃*z^3/(12*M*N*R^2)
    let V := fun z => C₂/κ+C₃*z^2/(2*κ*M)
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    (K*R^2/(r*N))*t+(16*K*R^2/N^2)*|G/r| * t+
      (K*r/N)*(q/r)+(K*R^2/(2*N^2))*(q/r)+
      q*D n+q₁*D n₁+V n*(t/r)+V n₁*(t/r₁) ≤
        (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.short_block_fourth_budget C₂ C₃ κ M N R Q K n n₁ r r₁ t q q₁ G hC₂ hC₃ hκ hM hN hR hQ hK hn hn₁ hnN hn₁N hr ht hq hq₁ hqQ hq₁Q hNR hRN hcube hminr hgeom hgeom₁ hG

example
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, (t:ℝ)/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    |(z 0-z 1)-round (z 0-z 1)| ≤ (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_fourth σ δ T M N R Q K u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hA hW hx₀ hx₁ hr ht hdet

example
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    let Δ := (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N
    let j := fun i => c i*u+2*n i*(e i*u+v i*t)
    let L := fun i => roundedMinorArcLinearForm (f i) (x₀ i) (e i) (r i) (s i) u t
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, (t:ℝ)/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    Δ < 1/2 →
    ∃ cnew ∈ minorArcCenterLabels (z 0) Δ, ∃ cnew₁ ∈ minorArcCenterLabels (z 1) Δ,
      cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
      |(L 0-L 1)-((cnew-j 0)-(cnew₁-j 1):ℤ)| ≤
        Δ+nonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_two_choice_nonlinear σ δ T M N R Q K u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hA hW hx₀ hx₁ hr ht hdet

end HuxleyBaseCoincidenceRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.cube_near_one
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.product_cube_near_one
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.affine_denominator_ratio_near_one
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fixed_cubic_ratio_from_base_coincidences
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_third
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_base_residual_difference_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_residual_difference
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_compatible_labels_with_common_difference
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_common_labels


namespace HuxleyThirdLabelRegression
open TaoTrudgianYang2025.HuxleyRationalPhase

example {x η : ℝ} (hx : |x-1| ≤ η) (hη : η ≤ 1/2) :
    |x^3-1| ≤ 7*η :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.cube_near_one x η hx hη

example {a x ε η : ℝ}
    (ha : |a-1| ≤ ε) (hx : |x-1| ≤ η) (hη : η ≤ 1/2) :
    |a*x^3-1| ≤ 4*ε+7*η :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.product_cube_near_one a x ε η ha hx hη

example
    {r r₁ s s₁ u t N R K : ℝ}
    (hr : 0 < r) (hr₁ : r₁ ≠ 0) (ht : 0 < t) (hN : 0 < N)
    (hR : 0 < R) (hK : 0 ≤ K) (hq : 0 < r*u+s*t)
    (hgeom : t/r ≤ (r*u+s*t)/R^2)
    (hfirst : |s₁/r₁-s/r| ≤ K*R^4/(r^2*N^2)) :
    |((r₁*u+s₁*t)/r₁)/((r*u+s*t)/r)-1| ≤ K*R^2/N^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.affine_denominator_ratio_near_one r r₁ s s₁ u t N R K hr hr₁ ht hN hR hK hq hgeom hfirst

example
    {μ μ₁ r r₁ s s₁ u t N R K : ℝ}
    (hμ : μ ≠ 0) (hr : 0 < r) (hr₁ : r₁ ≠ 0)
    (ht : 0 < t) (hN : 0 < N) (hR : 0 < R) (hK : 0 ≤ K)
    (hq : 0 < r*u+s*t) (hgeom : t/r ≤ (r*u+s*t)/R^2)
    (hfirst : |s₁/r₁-s/r| ≤ K*R^4/(r^2*N^2))
    (hthird : |μ₁*r₁^3/(μ*r^3)-1| ≤ K*R^2/N^2)
    (hsmall : K*R^2/N^2 ≤ 1/2) :
    |μ₁*(r₁*u+s₁*t)^3/(μ*(r*u+s*t)^3)-1| ≤ 11*K*R^2/N^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fixed_cubic_ratio_from_base_coincidences μ μ₁ r r₁ s s₁ u t N R K hμ hr hr₁ ht hN hR hK hq hgeom hfirst hthird hsmall

example
    {σ δ T M N R K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {r s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : 0 < t) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 3 (f i) (round (x₁ i))/6
    let C := (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)/
      TaoTrudgianYang2025.modelPhaseThirdLower σ
    (∀ i, |(n i:ℝ)| ≤ N) →
    0 < q 0 →
    (t:ℝ)/r 0 ≤ q 0/R^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    C*(R^2/N^2) ≤ 1/2 →
    |ν 1*(q 1)^3/(ν 0*(q 0)^3)-1| ≤ (33*K+4*C)*R^2/N^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_third σ δ T M N R K u t F A W x₀ x₁ r s hσ hδ hF hT hM hN hR hK hsmall hcube hA hW hx₀ hx₁ hr ht

example
    {σ δ T M N R ε η D₂ D₄ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hε : ε ≤ 1/2) (hη : η ≤ 1/2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let U := (u:ℝ)/t+(s 0:ℝ)/r 0
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let D := fun i =>
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|(n i:ℝ)|/(2*N*R^2)+
      5*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^3/(12*M*N*R^2)
    let V := fun i => (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
      TaoTrudgianYang2025.modelPhaseThirdLower σ+
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
    let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
      (n i:ℝ)*t/(r i*q i))
    let H := fun i => ((c i:ℝ)*s i-n i)*t/r i+θ i*q i/r i+γ i
    let Λ := D₂*|(t:ℝ)|+
      (12*ε+4*η)*|rationalBranch (μ 0) (r 0) (s 0) ((u:ℝ)/t)| * |(t:ℝ)|+
      D₄*|q 0/r 0|+(1/2:ℝ)*|(t:ℝ)| * (η*|U|)+
      |q 0| * D 0+|q 1| * D 1+V 0*|(t:ℝ)/r 0|+V 1*|(t:ℝ)/r 1|
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ ε →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ η*|U| →
    |C-round C| ≤ D₂ →
    |θ 0-θ 1| ≤ D₄ →
    |H 0-H 1-(round C:ℝ)*t| ≤ Λ :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_base_residual_difference_bound σ δ T M N R ε η D₂ D₄ u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hε hη hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
      (n i:ℝ)*t/(r i*q i))
    let H := fun i => ((c i:ℝ)*s i-n i)*t/r i+θ i*q i/r i+γ i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, (t:ℝ)/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    |H 0-H 1-(round C:ℝ)*t| ≤ (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_residual_difference σ δ T M N R Q K u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hA hW hx₀ hx₁ hr ht hdet

example
    {z₀ z₁ H₀ H₁ Δ : ℝ} {j₀ j₁ b t : ℤ}
    (hz₀ : z₀=(j₀:ℝ)+H₀) (hz₁ : z₁=(j₁:ℝ)+H₁)
    (hres : |H₀-H₁-(b:ℝ)*t| ≤ Δ) (hΔ : Δ < 1/2) :
    ∃ c ∈ minorArcCenterLabels z₀ Δ, ∃ c₁ ∈ minorArcCenterLabels z₁ Δ,
      c=round z₀ ∧ |(z₀-c)-(z₁-c₁)| ≤ Δ ∧ (c-j₀)-(c₁-j₁)=b*t :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.exists_compatible_labels_with_common_difference z₀ z₁ H₀ H₁ Δ j₀ j₁ b t hz₀ hz₁ hres hΔ

example
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    let j := fun i => c i*u+2*n i*(e i*u+v i*t)
    let Δ := (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, (t:ℝ)/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    Δ < 1/2 →
    ∃ cnew ∈ minorArcCenterLabels (z 0) Δ, ∃ cnew₁ ∈ minorArcCenterLabels (z 1) Δ,
      cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
      (cnew-j 0)-(cnew₁-j 1)=round C*t :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_common_labels σ δ T M N R Q K u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hA hW hx₀ hx₁ hr ht hdet

end HuxleyThirdLabelRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_displacement_upper
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.short_second_cancellation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_product_square_near_one
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.coordinate_quotient_difference_from_base
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.short_block_coordinate_error_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.short_block_numerator_difference_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.short_second_source_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_second_with_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_second
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_base_denominator_ratio
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_modular_inverse_difference
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.short_first_source_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_first
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_four_conditions


namespace HuxleyFourConditionsRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo 0 W) (hx₁ : x₁ ∈ Set.Ioo 0 W)
    (hr : 0 < r) (ht : 0 < t) (hq : 0 < r*u+s*t) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |(round x₁:ℝ)-(round x₀:ℝ)| ≤
      1+2*N*R^2*t/(modelPhaseThirdLower σ*r*(r*u+s*t)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_displacement_upper σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {r r₁ s s₁ u t n n₁ c c₁ θ θ₁ γ γ₁ η η₁ b : ℝ}
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (ht : t ≠ 0)
    (hq : r*u+s*t ≠ 0) (hq₁ : r₁*u+s₁*t ≠ 0) :
    let q := r*u+s*t
    let q₁ := r₁*u+s₁*t
    let H := (c*s-n)*t/r+θ*q/r+γ
    let H₁ := (c₁*s₁-n₁)*t/r₁+θ₁*q₁/r₁+γ₁
    H-η-(H₁-η₁)=b*t →
    n/q-n₁/q₁+(θ-θ₁)/t+r*(γ-η)/(t*q)-r₁*(γ₁-η₁)/(t*q₁) =
      2*(n/q-n₁/q₁)-(r/q)*(c*s/r-c₁*s₁/r₁-b)+
        (r*s₁-r₁*s)/(q*q₁)*(-n₁*t/r₁+θ₁*q₁/r₁+γ₁-η₁) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.short_second_cancellation r r₁ s s₁ u t n n₁ c c₁ θ θ₁ γ γ₁ η η₁ b hr hr₁ ht hq hq₁

example {a x ε η : ℝ}
    (ha : |a-1| ≤ ε) (hε : ε ≤ 1/2)
    (hx : |x-1| ≤ η) (hη : η ≤ 1/2) :
    |1-(a*x^2)⁻¹| ≤ 24*ε+24*η :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_product_square_near_one a x ε η ha hε hx hη

example
    {μ μ₁ r r₁ s s₁ u t N R K : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : 0 < r) (hr₁ : r₁ ≠ 0)
    (ht : 0 < t) (hN : 0 < N) (hR : 0 < R) (hK : 0 ≤ K)
    (hq : 0 < r*u+s*t) (hq₁ : r₁*u+s₁*t ≠ 0)
    (hgeom : t/r ≤ (r*u+s*t)/R^2)
    (hfirst : |s₁/r₁-s/r| ≤ K*R^4/(r^2*N^2))
    (hthird : |μ₁*r₁^3/(μ*r^3)-1| ≤ K*R^2/N^2)
    (hsmall : K*R^2/N^2 ≤ 1/2) :
    |minorArcCoordinate μ r s (u/t)/(r*u+s*t)-
      minorArcCoordinate μ₁ r₁ s₁ (u/t)/(r₁*u+s₁*t)| ≤
      (48*K*R^2/N^2)*|minorArcCoordinate μ r s (u/t)/(r*u+s*t)| :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.coordinate_quotient_difference_from_base μ μ₁ r r₁ s s₁ u t N R K hμ hμ₁ hr hr₁ ht hN hR hK hq hq₁ hgeom hfirst hthird hsmall

example {C₂ C₃ κ M N R n : ℝ}
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hκ : 0 < κ)
    (hM : 0 < M) (hN : 0 < N) (hn : 0 ≤ n) (hnN : n ≤ N)
    (hNR : N ≤ R^2) (hcube : N^3 ≤ M*R^2) :
    C₂/κ+C₃*n^2/(2*κ*M) ≤ (C₂/κ+C₃/(2*κ))*R^2/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.short_block_coordinate_error_budget C₂ C₃ κ M N R n hC₂ hC₃ hκ hM hN hn hnN hNR hcube

example
    {n n₁ G G₁ q q₁ N R Q K Cc : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hK : 0 ≤ K) (hCc : 0 ≤ Cc) (hRN : R ≤ N)
    (hq : Q/2 ≤ q) (hq₁ : Q/2 ≤ q₁) (hn : |n| ≤ N)
    (hcoord : |n-G| ≤ Cc*R^2/N) (hcoord₁ : |n₁-G₁| ≤ Cc*R^2/N)
    (hphase : |G/q-G₁/q₁| ≤ (48*K*R^2/N^2)*|G/q|) :
    |n/q-n₁/q₁| ≤ (96*K*(1+Cc)+4*Cc)*R^2/(N*Q) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.short_block_numerator_difference_budget n n₁ G G₁ q q₁ N R Q K Cc hN hR hQ hK hCc hRN hq hq₁ hn hcoord hcoord₁ hphase

example
    {r r₁ s s₁ t q q₁ n n₁ C b θ₁ γ₁ η₁ N R Q K Ct A : ℝ}
    (hr : 0 < r) (hr₁ : 0 < r₁) (ht : 0 ≤ t)
    (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q) (hK : 0 ≤ K)
    (hminr : R^2/N ≤ r) (hr₁Q : r₁ ≤ Q)
    (hq : Q/2 ≤ q) (hq₁ : Q/2 ≤ q₁) (hgeom : t/r ≤ q/R^2)
    (hfirst : |s₁/r₁-s/r| ≤ K*R^4/(r^2*N^2))
    (hsecond : |C-b| ≤ K*R^2/(r*N))
    (hn : |n/q-n₁/q₁| ≤ A*R^2/(N*Q))
    (hn₁ : |n₁| ≤ N) (hθ : |θ₁| ≤ 1/2) (hγ : |γ₁| ≤ Ct) (hη : |η₁| ≤ 1) :
    |2*(n/q-n₁/q₁)-(r/q)*(C-b)+
      (r*s₁-r₁*s)/(q*q₁)*(-n₁*t/r₁+θ₁*q₁/r₁+γ₁-η₁)| ≤
      (2*A+9*K+4*K*Ct)*R^2/(N*Q) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.short_second_source_budget r r₁ s s₁ t q q₁ n n₁ C b θ₁ γ₁ η₁ N R Q K Ct A hr hr₁ ht hN hR hQ hK hminr hr₁Q hq hq₁ hgeom hfirst hsecond hn hn₁ hθ hγ hη

example
    {σ δ T M N R Q K : ℝ} {u t tb ub : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3) (hK : 0 ≤ K) (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2) (hQN : Q ≤ N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let η := fun i => q i*d₁ i-cnew i
    let h := fun i => cnew i-(c i*u+2*n i*(e i*u+v i*t))
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew i/q i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, Q/2 ≤ q i ∧ q i ≤ Q) →
    (t:ℝ)/r 0 ≤ q 0/R^2 →
    R^2/N ≤ (r 0:ℝ) →
    (r 1:ℝ) ≤ Q →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    h 0-h 1=round C*t →
    |η 1| ≤ 1 →
    |(X 0-X 1)-round (X 0-X 1)| ≤
      (201*K+192*K*Cc+8*Cc+4*K*Ct)*R^2/(N*Q) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_second_with_labels σ δ T M N R Q K u t tb ub F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hN hR hQ hscale hK hsmall hNR hRN hcube hQN hA hW hx₀ hx₁ hr ht hdet hbez

example
    {σ δ T M N R Q K : ℝ} {u t tb ub : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 < Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2) (hQN : Q ≤ N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    let j := fun i => c i*u+2*n i*(e i*u+v i*t)
    let Δ := (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N
    let X := fun (i : Fin 2) (cnew : ℤ) => ((r i*tb-s i*ub:ℤ):ℝ)*cnew/q i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, Q/2 ≤ q i ∧ q i ≤ Q) →
    (∀ i, (t:ℝ)/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    (r 1:ℝ) ≤ Q →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    Δ < 1/2 →
    ∃ cnew ∈ minorArcCenterLabels (z 0) Δ, ∃ cnew₁ ∈ minorArcCenterLabels (z 1) Δ,
      cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
      (cnew-j 0)-(cnew₁-j 1)=round C*t ∧
      |(X 0 cnew-X 1 cnew₁)-round (X 0 cnew-X 1 cnew₁)| ≤
        (201*K+192*K*Cc+8*Cc+4*K*Ct)*R^2/(N*Q) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_second σ δ T M N R Q K u t tb ub F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hQN hA hW hx₀ hx₁ hr ht hdet hbez

example
    {σ δ T M : ℝ} {F : Fin 2 → ℝ → ℝ} {A W x : Fin 2 → ℝ} {r : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ i, x i ∈ Set.Ioo 0 (W i)) (hr : ∀ i, 0 < r i) :
    let μ := fun i => iteratedDeriv 3 (heathBrownPhysicalPhase (F i) T M (A i) 1) (x i)/6
    |μ 1*(r 1)^3/(μ 0*(r 0)^3)-1| ≤ 1/2 →
    r 1 ≤ (1+3*(σ*(σ+1)+1)/(2*modelPhaseThirdLower σ))*r 0 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_base_denominator_ratio σ δ T M F A W x r hσ hδ hF hT hM hA hW hx hr

example
    {r r₁ s s₁ u t tb ub : ℝ}
    (hq : r*u+s*t ≠ 0) (hq₁ : r₁*u+s₁*t ≠ 0) (hbez : t*tb+u*ub=1) :
    (r*tb-s*ub)/(r*u+s*t)-(r₁*tb-s₁*ub)/(r₁*u+s₁*t) =
      (r*s₁-r₁*s)/((r*u+s*t)*(r₁*u+s₁*t)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_modular_inverse_difference r r₁ s s₁ u t tb ub hq hq₁ hbez

example
    {r r₁ s s₁ u t tb ub N R Q K B : ℝ}
    (hr : 0 < r) (hr₁ : 0 < r₁) (hN : 0 < N) (hQ : 0 < Q)
    (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hq : Q/2 ≤ r*u+s*t) (hq₁ : Q/2 ≤ r₁*u+s₁*t)
    (hbez : t*tb+u*ub=1) (hratio : r₁ ≤ B*r)
    (hfirst : |s₁/r₁-s/r| ≤ K*R^4/(r^2*N^2)) :
    |(r*tb-s*ub)/(r*u+s*t)-(r₁*tb-s₁*ub)/(r₁*u+s₁*t)| ≤
      4*K*B*R^4/(N^2*Q^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.short_first_source_bound r r₁ s s₁ u t tb ub N R Q K B hr hr₁ hN hQ hK hB hq hq₁ hbez hratio hfirst

example
    {σ δ T M N R Q K : ℝ} {u t tb ub : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x : Fin 2 → ℝ} {r s : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hQ : 0 < Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ i, x i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (hbez : t*tb+u*ub=1) :
    let μ := fun i => iteratedDeriv 3 (heathBrownPhysicalPhase (F i) T M (A i) 1) (round (x i))/6
    let q := fun i => (r i:ℝ)*u+s i*t
    let inverse := fun i => r i*tb-s i*ub
    let B := 1+3*(σ*(σ+1)+1)/(2*modelPhaseThirdLower σ)
    (∀ i, Q/2 ≤ q i) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |(inverse 0:ℝ)/q 0-(inverse 1:ℝ)/q 1| ≤ 4*K*B*R^4/(N^2*Q^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_first σ δ T M N R Q K u t tb ub F A W x r s hσ hδ hF hT hM hN hQ hK hsmall hA hW hx hr hbez

example
    {σ δ T M N R Q K : ℝ} {u t tb ub : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 < Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2) (hQN : Q ≤ N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    let j := fun i => c i*u+2*n i*(e i*u+v i*t)
    let Δ := (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N
    let X := fun (i : Fin 2) (cnew : ℤ) => ((r i*tb-s i*ub:ℤ):ℝ)*cnew/q i
    let inverse := fun i => r i*tb-s i*ub
    let ν := fun i => iteratedDeriv 3 (f i) (round (x₁ i))/6
    let B := 1+3*(σ*(σ+1)+1)/(2*κ)
    let Cv := C₃/κ
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, Q/2 ≤ q i ∧ q i ≤ Q) →
    (∀ i, (t:ℝ)/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    (r 1:ℝ) ≤ Q →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    Cv*(R^2/N^2) ≤ 1/2 →
    Δ < 1/2 →
    ∃ cnew ∈ minorArcCenterLabels (z 0) Δ, ∃ cnew₁ ∈ minorArcCenterLabels (z 1) Δ,
      cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
      (cnew-j 0)-(cnew₁-j 1)=round C*t ∧
      |(X 0 cnew-X 1 cnew₁)-round (X 0 cnew-X 1 cnew₁)| ≤
        (201*K+192*K*Cc+8*Cc+4*K*Ct)*R^2/(N*Q) ∧
      |(inverse 0:ℝ)/q 0-(inverse 1:ℝ)/q 1| ≤ 4*K*B*R^4/(N^2*Q^2) ∧
      |ν 1*(q 1)^3/(ν 0*(q 0)^3)-1| ≤ (33*K+4*Cv)*R^2/N^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_four_conditions σ δ T M N R Q K u t tb ub F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hQN hA hW hx₀ hx₁ hr ht hdet hbez

end HuxleyFourConditionsRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_lipschitz
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_window_geometry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_window_four_conditions
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_short_window_geometry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_short_window_four_conditions

namespace HuxleyWindowGeometryRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ δ T M A W x y : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x ∈ Set.Ioo 0 W) (hy : y ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    |iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2| ≤
      (σ*(σ+1)+1)*T/(2*M^3)*|y-x| :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_halfCurvature_lipschitz σ δ T M A W x y F hσ hδ hF hT hM hA hW hx hy

example
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo 0 W) (hx₁ : x₁ ∈ Set.Ioo 0 W)
    (hr : 0 < r) (ht : 0 < t) (hq : 0 < r*u+s*t) (hdet : v*r-e*s=1)
    (hwidth : |x₁-x₀| ≤ N-1)
    (hphasewidth : (σ*(σ+1)+1)*|x₁-x₀| ≤ 2*N) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |(round x₁:ℝ)-(round x₀:ℝ)| ≤ N ∧ t/r ≤ (r*u+s*t)/R^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_window_geometry σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet hwidth hphasewidth

example
    {σ δ T M N R Q K : ℝ} {u t tb ub : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 < Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2) (hQN : Q ≤ N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    let j := fun i => c i*u+2*n i*(e i*u+v i*t)
    let Δ := (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N
    let X := fun (i : Fin 2) (cnew : ℤ) => ((r i*tb-s i*ub:ℤ):ℝ)*cnew/q i
    let inverse := fun i => r i*tb-s i*ub
    let ν := fun i => iteratedDeriv 3 (f i) (round (x₁ i))/6
    let B := 1+3*(σ*(σ+1)+1)/(2*κ)
    let Cv := C₃/κ
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |x₁ i-x₀ i| ≤ N-1) →
    (∀ i, (σ*(σ+1)+1)*|x₁ i-x₀ i| ≤ 2*N) →
    (∀ i, Q/2 ≤ q i ∧ q i ≤ Q) →
    R^2/N ≤ (r 0:ℝ) →
    (r 1:ℝ) ≤ Q →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    Cv*(R^2/N^2) ≤ 1/2 →
    Δ < 1/2 →
    ∃ cnew ∈ minorArcCenterLabels (z 0) Δ, ∃ cnew₁ ∈ minorArcCenterLabels (z 1) Δ,
      cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
      (cnew-j 0)-(cnew₁-j 1)=round C*t ∧
      |(X 0 cnew-X 1 cnew₁)-round (X 0 cnew-X 1 cnew₁)| ≤
        (201*K+192*K*Cc+8*Cc+4*K*Ct)*R^2/(N*Q) ∧
      |(inverse 0:ℝ)/q 0-(inverse 1:ℝ)/q 1| ≤ 4*K*B*R^4/(N^2*Q^2) ∧
      |ν 1*(q 1)^3/(ν 0*(q 0)^3)-1| ≤ (33*K+4*Cv)*R^2/N^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_window_four_conditions σ δ T M N R Q K u t tb ub F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hQN hA hW hx₀ hx₁ hr ht hdet hbez

example
    {σ δ T M N R A W L U x₀ H e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hLdist : |L-x₀| ≤ H) (hUdist : |U-x₀| ≤ H)
    (hwidth : H ≤ N-1) (hphasewidth : (σ*(σ+1)+1)*H ≤ 2*N)
    (hr : 0 < r) (ht : 0 < t) (hq : 0 < r*u+s*t) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f x₀/2=e/r →
    (e*u+v*t)/(r*u+s*t) ∈ Set.uIcc (iteratedDeriv 2 f L/2) (iteratedDeriv 2 f U/2) →
    ∃ x ∈ Set.uIcc L U, x ∈ Set.Ioo (1/2:ℝ) (W-1/2) ∧
      iteratedDeriv 2 f x/2=(e*u+v*t)/(r*u+s*t) ∧ |x-x₀| ≤ H ∧
      |(round x:ℝ)-(round x₀:ℝ)| ≤ N ∧ t/r ≤ (r*u+s*t)/R^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_short_window_geometry σ δ T M N R A W L U x₀ H e r v s u t F hσ hδ hF hT hM hN hR hscale hA hW hx₀ hL hU hLdist hUdist hwidth hphasewidth hr ht hq hdet

example
    {σ δ T M N R Q K : ℝ} {u t tb ub : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ L U H : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 < Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2) (hQN : Q ≤ N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hL : ∀ i, L i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hU : ∀ i, U i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hLdist : ∀ i, |L i-x₀ i| ≤ H i) (hUdist : ∀ i, |U i-x₀ i| ≤ H i)
    (hwidth : ∀ i, H i ≤ N-1)
    (hphasewidth : ∀ i, (σ*(σ+1)+1)*H i ≤ 2*N)
    (hr : ∀ i, 0 < r i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N
    let X := fun (i : Fin 2) (cnew : ℤ) => ((r i*tb-s i*ub:ℤ):ℝ)*cnew/q i
    let inverse := fun i => r i*tb-s i*ub
    let B := 1+3*(σ*(σ+1)+1)/(2*κ)
    let Cv := C₃/κ
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, ((e i:ℝ)*u+v i*t)/q i ∈
      Set.uIcc (iteratedDeriv 2 (f i) (L i)/2) (iteratedDeriv 2 (f i) (U i)/2)) →
    (∀ i, Q/2 ≤ q i ∧ q i ≤ Q) →
    R^2/N ≤ (r 0:ℝ) →
    (r 1:ℝ) ≤ Q →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    Cv*(R^2/N^2) ≤ 1/2 →
    Δ < 1/2 →
    ∃ x₁ : Fin 2 → ℝ, (∀ i, x₁ i ∈ Set.uIcc (L i) (U i)) ∧
      (∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) ∧
      (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) ∧
    let n := fun i => round (x₁ i)-round (x₀ i)
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let z := fun i => q i*d₁ i
    let j := fun i => c i*u+2*n i*(e i*u+v i*t)
    let ν := fun i => iteratedDeriv 3 (f i) (round (x₁ i))/6
    ∃ cnew ∈ minorArcCenterLabels (z 0) Δ, ∃ cnew₁ ∈ minorArcCenterLabels (z 1) Δ,
      cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
      (cnew-j 0)-(cnew₁-j 1)=round C*t ∧
      |(X 0 cnew-X 1 cnew₁)-round (X 0 cnew-X 1 cnew₁)| ≤
        (201*K+192*K*Cc+8*Cc+4*K*Ct)*R^2/(N*Q) ∧
      |(inverse 0:ℝ)/q 0-(inverse 1:ℝ)/q 1| ≤ 4*K*B*R^4/(N^2*Q^2) ∧
      |ν 1*(q 1)^3/(ν 0*(q 0)^3)-1| ≤ (33*K+4*Cv)*R^2/N^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_short_window_four_conditions σ δ T M N R Q K u t tb ub F A W x₀ L U H e r v s hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hQN hA hW hx₀ hL hU hLdist hUdist hwidth hphasewidth hr ht hdet hbez

end HuxleyWindowGeometryRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_forward_window_curvature_coverage
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_forward_window_cutoff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_forward_window_four_conditions

namespace HuxleyForwardWindowRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ δ T M N R A W x₀ H e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo 0 W) (hxH : x₀+H ∈ Set.Ioo 0 W)
    (hH : 0 ≤ H) (hr : 0 < r) (ht : 0 < t) (hq : 0 < r*u+s*t)
    (hdet : v*r-e*s=1)
    (hcut : 2*N*R^2*t ≤ modelPhaseThirdLower σ*H*r*(r*u+s*t)) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f x₀/2=e/r →
    (e*u+v*t)/(r*u+s*t) ∈
      Set.Icc (iteratedDeriv 2 f x₀/2) (iteratedDeriv 2 f (x₀+H)/2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_forward_window_curvature_coverage σ δ T M N R A W x₀ H e r v s u t F hσ hδ hF hT hM hN hR hscale hA hW hx₀ hxH hH hr ht hq hdet hcut

example
    {κ H N R r s u t : ℝ}
    (hκ : 0 < κ) (hH : 0 < H) (hN : 0 < N) (hR : 0 < R)
    (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 < t)
    (hu : 2*N*R^2/(κ*H*r^2)*t ≤ u) :
    0 < r*u+s*t ∧ 2*N*R^2*t ≤ κ*H*r*(r*u+s*t) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.farey_forward_window_cutoff κ H N R r s u t hκ hH hN hR hr hs ht hu

example
    {σ δ T M N R Q K : ℝ} {u t tb ub : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ H : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 < Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2) (hQN : Q ≤ N)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hH : ∀ i, 0 < H i)
    (hxH : ∀ i, x₀ i+H i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hwidth : ∀ i, H i ≤ N-1)
    (hphasewidth : ∀ i, (σ*(σ+1)+1)*H i ≤ 2*N)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 ≤ s i) (ht : 0 < t) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N
    let X := fun (i : Fin 2) (cnew : ℤ) => ((r i*tb-s i*ub:ℤ):ℝ)*cnew/q i
    let inverse := fun i => r i*tb-s i*ub
    let B := 1+3*(σ*(σ+1)+1)/(2*κ)
    let Cv := C₃/κ
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, 2*N*R^2/(κ*H i*(r i:ℝ)^2)*(t:ℝ) ≤ u) →
    (∀ i, Q/2 ≤ q i ∧ q i ≤ Q) →
    R^2/N ≤ (r 0:ℝ) →
    (r 1:ℝ) ≤ Q →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    Cv*(R^2/N^2) ≤ 1/2 →
    Δ < 1/2 →
    ∃ x₁ : Fin 2 → ℝ, (∀ i, x₁ i ∈ Set.uIcc (x₀ i) (x₀ i+H i)) ∧
      (∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) ∧
      (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) ∧
    let n := fun i => round (x₁ i)-round (x₀ i)
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let z := fun i => q i*d₁ i
    let j := fun i => c i*u+2*n i*(e i*u+v i*t)
    let ν := fun i => iteratedDeriv 3 (f i) (round (x₁ i))/6
    ∃ cnew ∈ minorArcCenterLabels (z 0) Δ, ∃ cnew₁ ∈ minorArcCenterLabels (z 1) Δ,
      cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
      (cnew-j 0)-(cnew₁-j 1)=round C*t ∧
      |(X 0 cnew-X 1 cnew₁)-round (X 0 cnew-X 1 cnew₁)| ≤
        (201*K+192*K*Cc+8*Cc+4*K*Ct)*R^2/(N*Q) ∧
      |(inverse 0:ℝ)/q 0-(inverse 1:ℝ)/q 1| ≤ 4*K*B*R^4/(N^2*Q^2) ∧
      |ν 1*(q 1)^3/(ν 0*(q 0)^3)-1| ≤ (33*K+4*Cv)*R^2/N^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_forward_window_four_conditions σ δ T M N R Q K u t tb ub F A W x₀ H e r v s hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hQN hA hW hx₀ hH hxH hwidth hphasewidth hr hs ht hdet hbez

end HuxleyForwardWindowRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_derivative_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_second_condition_no_wrap_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_second_condition_no_wrap
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_second_condition_derivative_from_sector_geometry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_second_condition_consumer
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.long_block_coordinate_error_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_no_wrap_scalar_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_second_condition_source_scales

namespace HuxleyNoWrapRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example
    {μ r s μ₁ r₁ s₁ x x₀ d ε : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : 0 < μ₁) (hr₁ : r₁ ≠ 0) (hd : 0 < d)
    (hden : ∀ y ∈ Set.uIcc x₀ x, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.uIcc x₀ x, d ≤ r₁*y+s₁)
    (hratio : ∀ y ∈ Set.uIcc x₀ x, |μ₁*(r₁*y+s₁)^3/(μ*(r*y+s)^3)-1| ≤ ε) :
    |deriv (rationalPhase μ r s μ₁ r₁ s₁) x-
      deriv (rationalPhase μ r s μ₁ r₁ s₁) x₀| ≤ 2*ε*|x-x₀|/(3*μ₁*d^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_derivative_variation μ r s μ₁ r₁ s₁ x x₀ d ε hμ hr hμ₁ hr₁ hd hden hden₁ hratio

example
    {μ r s μ₁ r₁ s₁ u t x₀ d ε n n₁ α A A₁ : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : 0 < μ₁) (hr₁ : r₁ ≠ 0)
    (ht : 0 < t) (hq : 0 < r*u+s*t) (hq₁ : 0 < r₁*u+s₁*t) (hd : 0 < d)
    (hden : ∀ y ∈ Set.uIcc x₀ (u/t), r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.uIcc x₀ (u/t), d ≤ r₁*y+s₁)
    (hratio : ∀ y ∈ Set.uIcc x₀ (u/t), |μ₁*(r₁*y+s₁)^3/(μ*(r*y+s)^3)-1| ≤ ε)
    (hn : |n-minorArcCoordinate μ r s (u/t)| ≤ A)
    (hn₁ : |n₁-minorArcCoordinate μ₁ r₁ s₁ (u/t)| ≤ A₁) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let a := round (α-deriv g x₀)
    |n/(r*u+s*t)-n₁/(r₁*u+s₁*t)+(α-a)/t| ≤
      (1/2+2*ε*|u/t-x₀|/(3*μ₁*d^3))/t+A/(r*u+s*t)+A₁/(r₁*u+s₁*t) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_second_condition_no_wrap_budget μ r s μ₁ r₁ s₁ u t x₀ d ε n n₁ α A A₁ hμ hr hμ₁ hr₁ ht hq hq₁ hd hden hden₁ hratio hn hn₁

example
    {σ δ T M y₀ d ξ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hd : 0 < d)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : 0 < t)
    (hq : ∀ i, 0 < (r i:ℝ)*u+s i*t) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let θ := fun i => (r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i))-
      round ((r i:ℝ)*iteratedDeriv 1 (f i) (round (x₀ i)))
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let a := round (θ 0-θ 1-deriv g y₀)
    let V := fun i => (modelPhaseJetCoefficient σ 2+δ)/modelPhaseThirdLower σ+
      (modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^2/(2*modelPhaseThirdLower σ*M)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ y ∈ Set.uIcc y₀ ((u:ℝ)/t), (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.uIcc y₀ ((u:ℝ)/t), d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.uIcc y₀ ((u:ℝ)/t),
      |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ξ) →
    (1/2+2*ξ*|(u:ℝ)/t-y₀|/(3*μ 1*d^3))/(t:ℝ)+V 0/q 0+V 1/q 1 < 1/2 →
    |(n 0:ℝ)/q 0-(n 1:ℝ)/q 1+(θ 0-θ 1-a)/t| < 1/2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_second_condition_no_wrap σ δ T M y₀ d ξ u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hd hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R Δ₂ Δ₄ ε y₀ d ξ : ℝ} {u t tb ub b : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ}
    {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1) (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hε : ε < 1/2) (hd : 0 < d)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : 0 < t)
    (hq : ∀ i, 0 < (r i:ℝ)*u+s i*t) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let η := fun i => q i*d₁ i-cnew i
    let h := fun i => cnew i-(c i*u+2*n i*(e i*u+v i*t))
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew i/q i
    let D := fun i =>
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|(n i:ℝ)|/(2*N*R^2)+
      5*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^3/(12*M*N*R^2)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let a := round (θ 0-θ 1-deriv (rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)) y₀)
    let V := fun i => (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)/
      TaoTrudgianYang2025.modelPhaseThirdLower σ+
      (TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ)*|(n i:ℝ)|^2/
        (2*TaoTrudgianYang2025.modelPhaseThirdLower σ*M)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    cnew 0 ∈ minorArcCenterLabels (q 0*d₁ 0) ε →
    |η 1-η 0| ≤ Δ₄ →
    h 0-h 1=a*u+b*t →
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    (∀ y ∈ Set.uIcc y₀ ((u:ℝ)/t), (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.uIcc y₀ ((u:ℝ)/t), d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.uIcc y₀ ((u:ℝ)/t),
      |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ξ) →
    (1/2+2*ξ*|(u:ℝ)/t-y₀|/(3*μ 1*d^3))/(t:ℝ)+V 0/q 0+V 1/q 1 < 1/2 →
    |θ 0-θ 1-a-deriv (rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)) ((u:ℝ)/t)| ≤
      |(t:ℝ)| * (Δ₂+(|(r 0:ℝ)| * D 0+|(r 1:ℝ)| * D 1)/|(t:ℝ)|+
      (1/2+ε)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q 0| * |q 1|)+
      |(r 1:ℝ)| * Δ₄/(|(t:ℝ)| * |q 1|)+V 0/|q 0|+V 1/|q 1|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_second_condition_derivative_from_sector_geometry σ δ T M N R Δ₂ Δ₄ ε y₀ d ξ u t tb ub b F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hN hR hε hd hscale hA hW hx₀ hx₁ hr ht hq hdet hbez

example
    {K : ℕ} {σ δ T M N R Δ Δ₂ Q l w B y₀ d ε : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℤ × ℤ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hd : 0 < d) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q) :
    let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun p i => round (x₁ p i)
    let n := fun p i => b p i-a i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let α := θ 0-θ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let z := fun p i => q p i*iteratedDeriv 1 (f i) (b p i)
    let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
    let η := η₀+(K:ℝ)*ε*(w-l)^2/(3*μ 1*d^3)
    let D := fun p i =>
      (modelPhaseJetCoefficient σ 2+δ)*|(n p i:ℝ)|/(2*N*R^2)+
      5*(modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^3/(12*M*N*R^2)
    let V := fun p i => (modelPhaseJetCoefficient σ 2+δ)/modelPhaseThirdLower σ+
      (modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^2/(2*modelPhaseThirdLower σ*M)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i, x₁ p i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ p ∈ S, ∀ i, 0 < (r i:ℝ)*p.1+s i*p.2) →
    (∀ p ∈ S, ∀ i, iteratedDeriv 2 (f i) (x₁ p i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n p i:ℝ)|^3 ≤ M*R^2) →
    (∀ p ∈ S, |(z p 0-round (z p 0))-(z p 1-round (z p 1))| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    (∀ y ∈ Set.Icc l w, (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.Icc l w, d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.Icc l w, |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ε) →
    max ((w-l)*(K:ℝ)^2/B) 2 ≤ S.card →
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, ∀ tb ub : ℤ, p.2*tb+p.1*ub=1 →
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*round (z p i)/q p i
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    (1/2+2*ε*|(p.1:ℝ)/p.2-y₀|/(3*μ 1*d^3))/(p.2:ℝ)+V p 0/q p 0+V p 1/q p 1 < 1/2 →
    |α-round (α-deriv g y₀)-deriv g ((p.1:ℝ)/p.2)| ≤
      |(p.2:ℝ)| * (Δ₂+(|(r 0:ℝ)| * D p 0+|(r 1:ℝ)| * D p 1)/|(p.2:ℝ)|+
      (1/2)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q p 0| * |q p 1|)+
      |(r 1:ℝ)| * Δ/(|(p.2:ℝ)| * |q p 1|)+V p 0/|q p 0|+V p 1/|q p 1|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_second_condition_consumer K σ δ T M N R Δ Δ₂ Q l w B y₀ d ε F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hr hdet hl hw hlw hB hy₀ hd hΔ hQ

example
    {n N M R C₂ C₃ κ : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hκ : 0 < κ)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hNR : N ≤ R^2) (hcube : N^3 ≤ M*R^2) (hncube : |n|^3 ≤ M*R^2) :
    C₂/κ+C₃*|n|^2/(2*κ*M) ≤ (C₂/κ+C₃/(2*κ))*R^2/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.long_block_coordinate_error_budget n N M R C₂ C₃ κ hN hM hκ hC₂ hC₃ hNR hcube hncube

example
    {t ξ L μ d V V₁ q q₁ : ℝ}
    (ht : 4 ≤ t) (hμ : 0 < μ) (hd : 0 < d)
    (hq : 0 < q) (hq₁ : 0 < q₁)
    (hvar : 16*ξ*L ≤ 3*μ*d^3*t)
    (hV : 16*V ≤ q) (hV₁ : 16*V₁ ≤ q₁) :
    (1/2+2*ξ*L/(3*μ*d^3))/t+V/q+V₁/q₁ < 1/2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.sector_no_wrap_scalar_budget t ξ L μ d V V₁ q q₁ ht hμ hd hq hq₁ hvar hV hV₁

example
    {K : ℕ} {σ δ T M N R Δ Δ₂ Q l w B y₀ d ε : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℤ × ℤ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNR : N ≤ R^2) (hNcube : N^3 ≤ M*R^2)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hd : 0 < d) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q) :
    let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun p i => round (x₁ p i)
    let n := fun p i => b p i-a i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let α := θ 0-θ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let z := fun p i => q p i*iteratedDeriv 1 (f i) (b p i)
    let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
    let η := η₀+(K:ℝ)*ε*(w-l)^2/(3*μ 1*d^3)
    let D := fun p i =>
      (modelPhaseJetCoefficient σ 2+δ)*|(n p i:ℝ)|/(2*N*R^2)+
      5*(modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^3/(12*M*N*R^2)
    let V := fun p i => (modelPhaseJetCoefficient σ 2+δ)/modelPhaseThirdLower σ+
      (modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^2/(2*modelPhaseThirdLower σ*M)
    let κ := modelPhaseThirdLower σ
    let Cc := (modelPhaseJetCoefficient σ 2+δ)/κ+(modelPhaseJetCoefficient σ 3+δ)/(2*κ)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i, x₁ p i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ p ∈ S, ∀ i, 0 < (r i:ℝ)*p.1+s i*p.2) →
    (∀ p ∈ S, ∀ i, iteratedDeriv 2 (f i) (x₁ p i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n p i:ℝ)|^3 ≤ M*R^2) →
    (∀ p ∈ S, |(z p 0-round (z p 0))-(z p 1-round (z p 1))| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    (∀ y ∈ Set.Icc l w, (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.Icc l w, d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.Icc l w, |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ε) →
    max ((w-l)*(K:ℝ)^2/B) 2 ≤ S.card →
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, ∀ tb ub : ℤ, p.2*tb+p.1*ub=1 →
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*round (z p i)/q p i
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    (4:ℤ) ≤ p.2 →
    (∀ i, 16*Cc*R^2/N ≤ q p i) →
    32*ε*(w-l)*N*R^2 ≤ κ*d^3*(p.2:ℝ) →
    |α-round (α-deriv g y₀)-deriv g ((p.1:ℝ)/p.2)| ≤
      |(p.2:ℝ)| * (Δ₂+(|(r 0:ℝ)| * D p 0+|(r 1:ℝ)| * D p 1)/|(p.2:ℝ)|+
      (1/2)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q p 0| * |q p 1|)+
      |(r 1:ℝ)| * Δ/(|(p.2:ℝ)| * |q p 1|)+V p 0/|q p 0|+V p 1/|q p 1|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_second_condition_source_scales K σ δ T M N R Δ Δ₂ Q l w B y₀ d ε F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hNR hNcube hscale hA hW hx₀ hr hdet hl hw hlw hB hy₀ hd hΔ hQ

end HuxleyNoWrapRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_fourth_condition_nonlinear_with_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_integer_labels_with_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_sector_two_choice_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_second_condition_consumer_with_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_second_condition_source_scales_with_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_constructed_two_choice_sector_second
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_curvature_zero_iff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_curvature_zero_unique
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_quadratic_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_halfCurvature_quartic_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_remainders
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_quartic_coordinate
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_quartic_firstDerivative_residual
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_cubicCoefficient_remainder

namespace HuxleyDoubledQuarticRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ δ T M N R Δ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun i => round (x₁ i)
    let n := fun i => b i-a i
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let z := fun i => q i*iteratedDeriv 1 (f i) (b i)
    let j := fun i => round ((r i:ℝ)*d₀ i)*u+2*n i*(e i*u+v i*t)
    let h := (cnew 0-j 0)-(cnew 1-j 1)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)|^3 ≤ M*R^2) →
    |(z 0-cnew 0)-(z 1-cnew 1)| ≤ Δ →
    |(θ 0-θ 1)*u+(β₀ 0-β₀ 1)*t-
      (t:ℝ)*rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1) ((u:ℝ)/t)-h| ≤
      Δ+nonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_fourth_condition_nonlinear_with_labels σ δ T M N R Δ u t F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {K : ℕ} {σ δ T M N R Δ Q l w B y₀ d ε : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℤ × ℤ → Fin 2 → ℝ} {cnew : ℤ × ℤ → Fin 2 → ℤ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hd : 0 < d) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q) :
    let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun p i => round (x₁ p i)
    let n := fun p i => b p i-a i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let z := fun p i => q p i*iteratedDeriv 1 (f i) (b p i)
    let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+2*n p i*(e i*p.1+v i*p.2)
    let h := fun p => (cnew p 0-j p 0)-(cnew p 1-j p 1)
    let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
    let η := η₀+(K:ℝ)*ε*(w-l)^2/(3*μ 1*d^3)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i, x₁ p i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ p ∈ S, ∀ i, r i*p.1+s i*p.2 ≠ 0) →
    (∀ p ∈ S, ∀ i, iteratedDeriv 2 (f i) (x₁ p i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n p i:ℝ)|^3 ≤ M*R^2) →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    (∀ y ∈ Set.Icc l w, (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.Icc l w, d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.Icc l w, |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ε) →
    max ((w-l)*(K:ℝ)^2/B) 2 ≤ S.card →
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, h p=p.1*round (α-deriv g y₀)+p.2*round (β-g y₀+y₀*deriv g y₀) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_integer_labels_with_labels K σ δ T M N R Δ Q l w B y₀ d ε F A W x₀ x₁ cnew e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hr hdet hl hw hlw hB hy₀ hd hΔ hQ

example
    {K : ℕ} {σ δ T M N R Δ Q l w B y₀ d ε : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℤ × ℤ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hd : 0 < d) (hΔ : 0 ≤ Δ) (hsmall : Δ < 1/2) (hQ : 0 ≤ Q) :
    let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun p i => round (x₁ p i)
    let n := fun p i => b p i-a i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let z := fun p i => q p i*iteratedDeriv 1 (f i) (b p i)
    let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+2*n p i*(e i*p.1+v i*p.2)
    let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
    let η := η₀+(K:ℝ)*ε*(w-l)^2/(3*μ 1*d^3)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i, x₁ p i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ p ∈ S, ∀ i, r i*p.1+s i*p.2 ≠ 0) →
    (∀ p ∈ S, ∀ i, iteratedDeriv 2 (f i) (x₁ p i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n p i:ℝ)|^3 ≤ M*R^2) →
    (∀ p ∈ S, |(z p 0-z p 1)-round (z p 0-z p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    (∀ y ∈ Set.Icc l w, (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.Icc l w, d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.Icc l w, |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ε) →
    max ((w-l)*(K:ℝ)^2/B) 2 ≤ S.card →
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∃ cnew : ℤ × ℤ → Fin 2 → ℤ, ∀ p ∈ S,
      (∀ i, cnew p i ∈ minorArcCenterLabels (z p i) Δ) ∧ cnew p 0=round (z p 0) ∧
      |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ ∧
      (cnew p 0-j p 0)-(cnew p 1-j p 1)=
        p.1*round (α-deriv g y₀)+p.2*round (β-g y₀+y₀*deriv g y₀) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_exists_sector_two_choice_labels K σ δ T M N R Δ Q l w B y₀ d ε F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hr hdet hl hw hlw hB hy₀ hd hΔ hsmall hQ

example
    {K : ℕ} {σ δ T M N R Δ Δ₂ Q l w B y₀ d ε ρ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℤ × ℤ → Fin 2 → ℝ} {cnew : ℤ × ℤ → Fin 2 → ℤ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hd : 0 < d) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q) (hρ : ρ < 1/2) :
    let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun p i => round (x₁ p i)
    let n := fun p i => b p i-a i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let α := θ 0-θ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let z := fun p i => q p i*iteratedDeriv 1 (f i) (b p i)
    let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
    let η := η₀+(K:ℝ)*ε*(w-l)^2/(3*μ 1*d^3)
    let D := fun p i =>
      (modelPhaseJetCoefficient σ 2+δ)*|(n p i:ℝ)|/(2*N*R^2)+
      5*(modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^3/(12*M*N*R^2)
    let V := fun p i => (modelPhaseJetCoefficient σ 2+δ)/modelPhaseThirdLower σ+
      (modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^2/(2*modelPhaseThirdLower σ*M)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i, x₁ p i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ p ∈ S, ∀ i, 0 < (r i:ℝ)*p.1+s i*p.2) →
    (∀ p ∈ S, ∀ i, iteratedDeriv 2 (f i) (x₁ p i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n p i:ℝ)|^3 ≤ M*R^2) →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, cnew p 0 ∈ minorArcCenterLabels (z p 0) ρ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    (∀ y ∈ Set.Icc l w, (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.Icc l w, d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.Icc l w, |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ε) →
    max ((w-l)*(K:ℝ)^2/B) 2 ≤ S.card →
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, ∀ tb ub : ℤ, p.2*tb+p.1*ub=1 →
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew p i/q p i
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    (1/2+2*ε*|(p.1:ℝ)/p.2-y₀|/(3*μ 1*d^3))/(p.2:ℝ)+V p 0/q p 0+V p 1/q p 1 < 1/2 →
    |α-round (α-deriv g y₀)-deriv g ((p.1:ℝ)/p.2)| ≤
      |(p.2:ℝ)| * (Δ₂+(|(r 0:ℝ)| * D p 0+|(r 1:ℝ)| * D p 1)/|(p.2:ℝ)|+
      (1/2+ρ)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q p 0| * |q p 1|)+
      |(r 1:ℝ)| * Δ/(|(p.2:ℝ)| * |q p 1|)+V p 0/|q p 0|+V p 1/|q p 1|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_second_condition_consumer_with_labels K σ δ T M N R Δ Δ₂ Q l w B y₀ d ε ρ F A W x₀ x₁ cnew e r v s hσ hδ hF hT hM hN hR hscale hA hW hx₀ hr hdet hl hw hlw hB hy₀ hd hΔ hQ hρ

example
    {K : ℕ} {σ δ T M N R Δ Δ₂ Q l w B y₀ d ε ρ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℤ × ℤ → Fin 2 → ℝ} {cnew : ℤ × ℤ → Fin 2 → ℤ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNR : N ≤ R^2) (hNcube : N^3 ≤ M*R^2)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hd : 0 < d) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q) (hρ : ρ < 1/2) :
    let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun p i => round (x₁ p i)
    let n := fun p i => b p i-a i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let α := θ 0-θ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let z := fun p i => q p i*iteratedDeriv 1 (f i) (b p i)
    let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
    let η := η₀+(K:ℝ)*ε*(w-l)^2/(3*μ 1*d^3)
    let D := fun p i =>
      (modelPhaseJetCoefficient σ 2+δ)*|(n p i:ℝ)|/(2*N*R^2)+
      5*(modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^3/(12*M*N*R^2)
    let V := fun p i => (modelPhaseJetCoefficient σ 2+δ)/modelPhaseThirdLower σ+
      (modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^2/(2*modelPhaseThirdLower σ*M)
    let κ := modelPhaseThirdLower σ
    let Cc := (modelPhaseJetCoefficient σ 2+δ)/κ+(modelPhaseJetCoefficient σ 3+δ)/(2*κ)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i, x₁ p i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ p ∈ S, ∀ i, 0 < (r i:ℝ)*p.1+s i*p.2) →
    (∀ p ∈ S, ∀ i, iteratedDeriv 2 (f i) (x₁ p i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n p i:ℝ)|^3 ≤ M*R^2) →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, cnew p 0 ∈ minorArcCenterLabels (z p 0) ρ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    (∀ y ∈ Set.Icc l w, (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.Icc l w, d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.Icc l w, |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ε) →
    max ((w-l)*(K:ℝ)^2/B) 2 ≤ S.card →
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, ∀ tb ub : ℤ, p.2*tb+p.1*ub=1 →
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew p i/q p i
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    (4:ℤ) ≤ p.2 →
    (∀ i, 16*Cc*R^2/N ≤ q p i) →
    32*ε*(w-l)*N*R^2 ≤ κ*d^3*(p.2:ℝ) →
    |α-round (α-deriv g y₀)-deriv g ((p.1:ℝ)/p.2)| ≤
      |(p.2:ℝ)| * (Δ₂+(|(r 0:ℝ)| * D p 0+|(r 1:ℝ)| * D p 1)/|(p.2:ℝ)|+
      (1/2+ρ)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q p 0| * |q p 1|)+
      |(r 1:ℝ)| * Δ/(|(p.2:ℝ)| * |q p 1|)+V p 0/|q p 0|+V p 1/|q p 1|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_sector_second_condition_source_scales_with_labels K σ δ T M N R Δ Δ₂ Q l w B y₀ d ε ρ F A W x₀ x₁ cnew e r v s hσ hδ hF hT hM hN hR hNR hNcube hscale hA hW hx₀ hr hdet hl hw hlw hB hy₀ hd hΔ hQ hρ

example
    {K : ℕ} {σ δ T M N R Δ Δ₂ Q l w B y₀ d ε : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℤ × ℤ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNR : N ≤ R^2) (hNcube : N^3 ≤ M*R^2)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hd : 0 < d) (hΔ : 0 ≤ Δ) (hsmall : Δ < 1/2) (hQ : 0 ≤ Q) :
    let S := TaoTrudgianYang2025.HuxleyLinearForm.fareySector K l w
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun p i => round (x₁ p i)
    let n := fun p i => b p i-a i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let z := fun p i => q p i*iteratedDeriv 1 (f i) (b p i)
    let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+2*n p i*(e i*p.1+v i*p.2)
    let η₀ := Δ+nonlinearResidualConstant σ δ*Q/N
    let η := η₀+(K:ℝ)*ε*(w-l)^2/(3*μ 1*d^3)
    let κ := modelPhaseThirdLower σ
    let Cc := (modelPhaseJetCoefficient σ 2+δ)/κ+(modelPhaseJetCoefficient σ 3+δ)/(2*κ)
    let D := fun p i =>
      (modelPhaseJetCoefficient σ 2+δ)*|(n p i:ℝ)|/(2*N*R^2)+
      5*(modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^3/(12*M*N*R^2)
    let V := fun p i => (modelPhaseJetCoefficient σ 2+δ)/κ+
      (modelPhaseJetCoefficient σ 3+δ)*|(n p i:ℝ)|^2/(2*κ*M)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i, x₁ p i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ p ∈ S, ∀ i, 0 < (r i:ℝ)*p.1+s i*p.2) →
    (∀ p ∈ S, ∀ i, iteratedDeriv 2 (f i) (x₁ p i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n p i:ℝ)|^3 ≤ M*R^2) →
    (∀ p ∈ S, |(z p 0-z p 1)-round (z p 0-z p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    (∀ y ∈ Set.Icc l w, (r 0:ℝ)*y+s 0 ≠ 0) →
    (∀ y ∈ Set.Icc l w, d ≤ (r 1:ℝ)*y+s 1) →
    (∀ y ∈ Set.Icc l w, |μ 1*((r 1:ℝ)*y+s 1)^3/(μ 0*((r 0:ℝ)*y+s 0)^3)-1| ≤ ε) →
    max ((w-l)*(K:ℝ)^2/B) 2 ≤ S.card →
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∃ cnew : ℤ × ℤ → Fin 2 → ℤ, ∀ p ∈ S,
      (∀ i, cnew p i ∈ minorArcCenterLabels (z p i) Δ) ∧ cnew p 0=round (z p 0) ∧
      |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ ∧
      (cnew p 0-j p 0)-(cnew p 1-j p 1)=
        p.1*round (α-deriv g y₀)+p.2*round (β-g y₀+y₀*deriv g y₀) ∧
      ∀ tb ub : ℤ, p.2*tb+p.1*ub=1 →
      let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew p i/q p i
      |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
      (4:ℤ) ≤ p.2 →
      (∀ i, 16*Cc*R^2/N ≤ q p i) →
      32*ε*(w-l)*N*R^2 ≤ κ*d^3*(p.2:ℝ) →
      |α-round (α-deriv g y₀)-deriv g ((p.1:ℝ)/p.2)| ≤
        |(p.2:ℝ)| * (Δ₂+(|(r 0:ℝ)| * D p 0+|(r 1:ℝ)| * D p 1)/|(p.2:ℝ)|+
        (1/2+Δ)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q p 0| * |q p 1|)+
        |(r 1:ℝ)| * Δ/(|(p.2:ℝ)| * |q p 1|)+V p 0/|q p 0|+V p 1/|q p 1|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_constructed_two_choice_sector_second K σ δ T M N R Δ Δ₂ Q l w B y₀ d ε F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hNR hNcube hscale hA hW hx₀ hr hdet hl hw hlw hB hy₀ hd hΔ hsmall hQ

example
    {μ r s μ₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x=0 ↔
      μ₁*(r₁*x+s₁)^3=μ*(r*x+s)^3 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_curvature_zero_iff μ r s μ₁ r₁ s₁ x hμ hr hμ₁ hr₁ hx hx₁

example
    {μ r s μ₁ r₁ s₁ x y : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hdet : r₁*s-r*s₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0)
    (hy : r*y+s ≠ 0) (hy₁ : r₁*y+s₁ ≠ 0)
    (hzero : iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x=0)
    (hzero₁ : iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) y=0) : x=y :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.rationalPhase_curvature_zero_unique μ r s μ₁ r₁ s₁ x y hμ hr hμ₁ hr₁ hdet hx hx₁ hy hy₁ hzero hzero₁

example
    {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 5 f y)
    (hfifth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 5 f y| ≤ U) :
    |iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-
      3*(iteratedDeriv 3 f a/6)*(b-a)-6*(iteratedDeriv 4 f a/24)*(b-a)^2| ≤
      U*|b-a|^3/12 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.halfCurvature_quadratic_remainder f a b U hf hfifth

example
    {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 5 f y)
    (hfifth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 5 f y| ≤ U) :
    |iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2)+
      2*(iteratedDeriv 4 f a/24)*(b-a)^3| ≤ U*|b-a|^4/8 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_halfCurvature_quartic_remainder f a b U hf hfifth

example
    {σ δ T M A W a b : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := iteratedDeriv 3 f a/6
    let ν := iteratedDeriv 4 f a/24
    |iteratedDeriv 2 f b/2-iteratedDeriv 2 f a/2-3*μ*(b-a)-6*ν*(b-a)^2| ≤
      T*(modelPhaseJetCoefficient σ 4+δ)*|b-a|^3/(12*M^5) ∧
    |iteratedDeriv 1 f b-iteratedDeriv 1 f a-
      (b-a)*(iteratedDeriv 2 f a/2+iteratedDeriv 2 f b/2)+2*ν*(b-a)^3| ≤
      T*(modelPhaseJetCoefficient σ 4+δ)*|b-a|^4/(8*M^5) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_remainders σ δ T M A W a b F hσ hF hT hM hA hW ha hb

example
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let n := (round x₁:ℝ)-(round x₀:ℝ)
    let μ := iteratedDeriv 3 f (round x₀)/6
    let ν := iteratedDeriv 4 f (round x₀)/24
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |n+2*ν/μ*n^2-minorArcCoordinate μ r s (u/t)| ≤
      (modelPhaseJetCoefficient σ 2+δ)/modelPhaseThirdLower σ+
      (modelPhaseJetCoefficient σ 4+δ)*|n|^3/(6*modelPhaseThirdLower σ*M^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_quartic_coordinate σ δ T M A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := TaoTrudgianYang2025.heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let q := r*u+s*t
    let ν := iteratedDeriv 4 f a/24
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q)+2*ν*n^3)| ≤
      |q| * (T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ)*|n|/(2*M^3)+
        T*(TaoTrudgianYang2025.modelPhaseJetCoefficient σ 4+δ)*|n|^4/(8*M^5)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_quartic_firstDerivative_residual σ δ T M A W x₀ x₁ e r v s u t F hσ hF hT hM hA hW hx₀ hx₁ hr hq hdet

example
    {σ δ T M A W a b : ℝ} {F : ℝ → ℝ} (hσ : 0 ≤ σ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    |iteratedDeriv 3 f b/6-iteratedDeriv 3 f a/6-
      4*(iteratedDeriv 4 f a/24)*(b-a)| ≤
      T*(modelPhaseJetCoefficient σ 4+δ)*|b-a|^2/(12*M^5) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_cubicCoefficient_remainder σ δ T M A W a b F hσ hF hT hM hA hW ha hb

end HuxleyDoubledQuarticRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_hasDerivAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_second
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_second
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_derivative_coordinate
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coordinate_replacement
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_cubic_ratio_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_quartic_rational_coordinate
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_corrected_nonlinear_residual_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_quartic_corrected_nonlinear_residual_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.coordinate_cube_difference_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_nonlinear_residual_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_residual_source_scale_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_residual_le_fourth_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_rounded_linearization
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_fourth_condition_nonlinear_with_labels

namespace HuxleyQuarticPhaseRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example {μ ν r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    HasDerivAt (quarticBranch μ ν r s) (-8*ν/(27*μ^3*r^2*(r*x+s)^3)) x :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_hasDerivAt μ ν r s x hμ hr hx

example {μ ν r s x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hx : r*x+s ≠ 0) :
    iteratedDeriv 2 (quarticBranch μ ν r s) x =
      8*ν/(9*μ^3*r*(r*x+s)^4) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_second μ ν r s x hμ hr hx

example {μ ν r s μ₁ ν₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x =
      8*ν/(9*μ^3*r*(r*x+s)^4)-8*ν₁/(9*μ₁^3*r₁*(r₁*x+s₁)^4) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_second μ ν r s μ₁ ν₁ r₁ s₁ x hμ hr hμ₁ hr₁ hx hx₁

example
    {μ ν r s μ₁ ν₁ r₁ s₁ u t : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hq₁ : r₁*u+s₁*t ≠ 0) :
    3/(4*t)*deriv (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) (u/t) =
      -(2*ν/μ)*(minorArcCoordinate μ r s (u/t))^2/(r*u+s*t)+
        (2*ν₁/μ₁)*(minorArcCoordinate μ₁ r₁ s₁ (u/t))^2/(r₁*u+s₁*t) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_derivative_coordinate μ ν r s μ₁ ν₁ r₁ s₁ u t hμ hμ₁ hr hr₁ ht hq hq₁

example {n G a A B : ℝ}
    (hn : |n-G| ≤ A) (hq : |n+a*n^2-G| ≤ B) :
    |n+a*G^2-G| ≤ B+|a| * A*(2*|n|+A) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coordinate_replacement n G a A B hn hq

example
    {σ δ T M A W z : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hz : z ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := iteratedDeriv 3 f z/6
    let ν := iteratedDeriv 4 f z/24
    |2*ν/μ| ≤ (modelPhaseJetCoefficient σ 3+δ)/(2*modelPhaseThirdLower σ*M) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_cubic_ratio_bound σ δ T M A W z F hσ hδ hF hT hM hA hW hz

example
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let n := (round x₁:ℝ)-(round x₀:ℝ)
    let μ := iteratedDeriv 3 f (round x₀)/6
    let ν := iteratedDeriv 4 f (round x₀)/24
    let G := minorArcCoordinate μ r s (u/t)
    let κ := modelPhaseThirdLower σ
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let C₄ := modelPhaseJetCoefficient σ 4+δ
    let V := C₂/κ+C₃*|n|^2/(2*κ*M)
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |n+2*ν/μ*G^2-G| ≤ C₂/κ+C₄*|n|^3/(6*κ*M^2)+
      C₃/(2*κ*M)*V*(2*|n|+V) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_rounded_quartic_rational_coordinate σ δ T M A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hA hW hx₀ hx₁ hr ht hq hdet

example
    {μ ν r s u t n δ E : ℝ} (hμ : μ ≠ 0) (hr : r ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(E+2*δ*n+3*μ*n^2+4*ν*n^3-n*t/(r*q))
    γ-n*t/r-t/r*(2*δ/(3*μ)-G)-t*quarticBranch μ ν r s (u/t) =
      q*(E+(n-G)*(3*μ*(n-G)+2*δ)+4*ν*(n^3-G^3)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_corrected_nonlinear_residual_identity μ ν r s u t n δ E hμ hr ht hq

example
    {f : ℝ → ℝ} {a b U e r s u t : ℝ}
    (hf : ∀ y ∈ Set.uIcc a b, ContDiffAt ℝ 5 f y)
    (hfifth : ∀ y ∈ Set.uIcc a b, |iteratedDeriv 5 f y| ≤ U)
    (hμ : iteratedDeriv 3 f a/6 ≠ 0) (hr : r ≠ 0)
    (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let ν := iteratedDeriv 4 f a/24
    let δ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    |γ-n*t/r-t/r*(2*δ/(3*μ)-G)-t*quarticBranch μ ν r s (u/t)| ≤
      |q| * (U*|n|^4/24+|n-G| * (3*|μ| * |n-G|+2*|δ|)+
        4*|ν| * |n^3-G^3|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.firstDerivative_quartic_corrected_nonlinear_residual_bound f a b U e r s u t hf hfifth hμ hr ht hq

example {n G D : ℝ} (hn : |n-G| ≤ D) :
    |n^3-G^3| ≤ D*(3*|n|^2+3*|n| * D+D^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.coordinate_cube_difference_bound n G D hn

example
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let ν := iteratedDeriv 4 f a/24
    let δ₀ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let C₄ := modelPhaseJetCoefficient σ 4+δ
    let κ := modelPhaseThirdLower σ
    let D := C₂/κ+C₃*|n|^2/(2*κ*M)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |γ-n*t/r-t/r*(2*δ₀/(3*μ)-G)-t*quarticBranch μ ν r s (u/t)| ≤
      |q| * (T/M^3) * (C₄*|n|^4/(24*M^2)+C₂/2*D*(D+1)+
        C₃/(6*M)*D*(3*|n|^2+3*|n| * D+D^2)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_nonlinear_residual_bound σ δ T M A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hA hW hx₀ hx₁ hr ht hq hdet

example
    {A B C₂ C₃ C₄ n M N R T : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄)
    (hn : 0 ≤ n) (hM : 0 < M) (hnM : n ≤ M) (hN : 0 < N)
    (hR : 1 ≤ R) (hRM : R ≤ M) (hT : 0 < T)
    (hscale : T*N*R^2=M^3) (hsquare : n^2 ≤ M*R) :
    let K := A+B
    let D := A+B*n^2/M
    (T/M^3)*(C₄*n^4/(24*M^2)+C₂/2*D*(D+1)+
      C₃/(6*M)*D*(3*n^2+3*n*D+D^2)) ≤
      (C₄/24+C₂/2*K*(K+1)+C₃/6*(3*K+3*K^2+K^3))/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_residual_source_scale_budget A B C₂ C₃ C₄ n M N R T hA hB hC₂ hC₃ hC₄ hn hM hnM hN hR hRM hT hscale hsquare

example
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let ν := iteratedDeriv 4 f a/24
    let δ₀ := iteratedDeriv 2 f a/2-e/r
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |n|^2 ≤ M*R →
    |γ-n*t/r-t/r*(2*δ₀/(3*μ)-G)-t*quarticBranch μ ν r s (u/t)| ≤ quarticNonlinearResidualConstant σ δ*|q|/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_residual_le_fourth_scale σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R A W x₀ x₁ : ℝ} {e r v s u t : ℤ} {F : ℝ → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a := round x₀
    let b := round x₁
    let n := b-a
    let q : ℝ := r*u+s*t
    let j := round ((r:ℝ)*iteratedDeriv 1 f a)*u+2*n*(e*u+v*t)
    iteratedDeriv 2 f x₀/2=(e:ℝ)/r →
    iteratedDeriv 2 f x₁/2=((e:ℝ)*u+v*t)/q →
    |(n:ℝ)|^2 ≤ M*R →
    |q*iteratedDeriv 1 f b-j-roundedMinorArcQuarticLinearForm f x₀ e r s u t| ≤
      quarticNonlinearResidualConstant σ δ*|q|/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_rounded_linearization σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R Δ : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun i => round (x₁ i)
    let n := fun i => b i-a i
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let z := fun i => q i*iteratedDeriv 1 (f i) (b i)
    let j := fun i => round ((r i:ℝ)*d₀ i)*u+2*n i*(e i*u+v i*t)
    let h := (cnew 0-j 0)-(cnew 1-j 1)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)|^2 ≤ M*R) →
    |(z 0-cnew 0)-(z 1-cnew 1)| ≤ Δ →
    |(θ 0-θ 1)*u+(β₀ 0-β₀ 1)*t-
      (t:ℝ)*rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1) ((u:ℝ)/t)+
      (t:ℝ)*quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1) ((u:ℝ)/t)-h| ≤
      Δ+quarticNonlinearResidualConstant σ δ*(|q 0|+|q 1|)/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_fourth_condition_nonlinear_with_labels σ δ T M N R Δ u t F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀ hx₁ hr ht hq hdet

end HuxleyQuarticPhaseRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_linear_remainder_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_reciprocal_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_reciprocal_coordinate_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_curvature_transfer
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_curvature_of_reciprocal_errors
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_third_condition_curvature
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_curvature_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_taylor_source_scale

namespace HuxleyQuarticReciprocalRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example {x y d : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    |x/y-1+d/x| ≤ x/y*((d/x)^2+(|d/x|+1)*|(y-x-d)/x|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_linear_remainder_bound x y d hx hy

example
    {σ δ T M A W a b : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (ha : a ∈ Set.Ioo 0 W) (hb : b ∈ Set.Ioo 0 W) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := iteratedDeriv 3 f a/6
    let μ₁ := iteratedDeriv 3 f b/6
    let ν := iteratedDeriv 4 f a/24
    let n := b-a
    let κ := modelPhaseThirdLower σ
    let L := (modelPhaseJetCoefficient σ 3+δ)/κ
    let V := (modelPhaseJetCoefficient σ 4+δ)/(2*κ)
    |μ/μ₁-1+4*ν*n/μ| ≤ ((σ*(σ+1)+1)/κ)*(L^2+(L+1)*V)*|n|^2/M^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_reciprocal_remainder σ δ T M A W a b F hσ hδ hF hT hM hA hW ha hb

example
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNscale : N^2 ≤ M*R) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let μ₁ := iteratedDeriv 3 f b/6
    let ν := iteratedDeriv 4 f a/24
    let G := minorArcCoordinate μ r s (u/t)
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |n|^2 ≤ M*R →
    |μ/μ₁-1+4*ν*G/μ| ≤ quarticReciprocalConstant σ δ*R^2/N^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_reciprocal_coordinate_source_scale σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hNscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {μ ν μnew r s x ε : ℝ}
    (hμ : 0 < μ) (hμnew : μnew ≠ 0) (hr : r ≠ 0) (hx : 0 < r*x+s)
    (he : |μ/μnew-1+4*ν*minorArcCoordinate μ r s x/μ| ≤ ε) :
    |iteratedDeriv 2 (rationalBranch μ r s) x-
        iteratedDeriv 2 (quarticBranch μ ν r s) x-2/(3*μnew*(r*x+s)^3)| ≤
      (2/(3*μ*(r*x+s)^3))*ε :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_curvature_transfer μ ν μnew r s x ε hμ hμnew hr hx he

example
    {μ ν μnew r s μ₁ ν₁ μnew₁ r₁ s₁ x ε ε₁ Δ : ℝ}
    (hμ : 0 < μ) (hμ₁ : 0 < μ₁) (hμnew : 0 < μnew) (hμnew₁ : 0 < μnew₁)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hx : 0 < r*x+s) (hx₁ : 0 < r₁*x+s₁)
    (he : |μ/μnew-1+4*ν*minorArcCoordinate μ r s x/μ| ≤ ε)
    (he₁ : |μ₁/μnew₁-1+4*ν₁*minorArcCoordinate μ₁ r₁ s₁ x/μ₁| ≤ ε₁)
    (hthird : |μnew₁*(r₁*x+s₁)^3/(μnew*(r*x+s)^3)-1| ≤ Δ) :
    |iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
        iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x| ≤
      2*Δ/(3*μnew₁*(r₁*x+s₁)^3)+
        2*ε/(3*μ*(r*x+s)^3)+2*ε₁/(3*μ₁*(r₁*x+s₁)^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_curvature_of_reciprocal_errors μ ν μnew r s μ₁ ν₁ μnew₁ r₁ s₁ x ε ε₁ Δ hμ hμ₁ hμnew hμnew₁ hr hr₁ hx hx₁ he he₁ hthird

example
    {σ δ T M N R Δ u t : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ e r v s : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNscale : N^2 ≤ M*R) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : 0 < t) (hq : ∀ i, 0 < r i*u+s i*t)
    (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => (round (x₀ i):ℝ)
    let b := fun i => (round (x₁ i):ℝ)
    let n := fun i => b i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun i => iteratedDeriv 3 (f i) (b i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun i => r i*u+s i*t
    let d := fun i => r i*(u/t)+s i
    let E := quarticReciprocalConstant σ δ*R^2/N^2
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(e i*u+v i*t)/q i) →
    (∀ i, |n i|^2 ≤ M*R) →
    |μnew 1*(q 1)^3/(μnew 0*(q 0)^3)-1| ≤ Δ →
    |iteratedDeriv 2 (rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)) (u/t)-
        iteratedDeriv 2 (quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)) (u/t)| ≤
      2*Δ/(3*μnew 1*(d 1)^3)+2*E/(3*μ 0*(d 0)^3)+2*E/(3*μ 1*(d 1)^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_third_condition_curvature σ δ T M N R Δ u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hNscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R B dmin u t : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ e r v s : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3) (hB : 0 ≤ B) (hdmin : 0 < dmin) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : 0 < t) (hq : ∀ i, 0 < r i*u+s i*t)
    (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => (round (x₀ i):ℝ)
    let b := fun i => (round (x₁ i):ℝ)
    let n := fun i => b i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun i => iteratedDeriv 3 (f i) (b i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun i => r i*u+s i*t
    let d := fun i => r i*(u/t)+s i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(e i*u+v i*t)/q i) →
    (∀ i, |n i|^2 ≤ M*R) →
    (∀ i, dmin ≤ d i) →
    |μnew 1*(q 1)^3/(μnew 0*(q 0)^3)-1| ≤ B*R^2/N^2 →
    |iteratedDeriv 2 (rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)) (u/t)-
        iteratedDeriv 2 (quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)) (u/t)| ≤
      (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_curvature_source_scale σ δ T M N R B dmin u t F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hNscale hscale hB hdmin hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R B dmin y₀ y₁ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.uIcc y₀ y₁, ∀ i, x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.uIcc y₀ y₁, ∀ i, dmin ≤ r i*y+s i) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => (round (x₀ i):ℝ)
    let b := fun y i => (round (x₁ y i):ℝ)
    let n := fun y i => b y i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (b y i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let d := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun y => g y-h y
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.uIcc y₀ y₁, ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/d y i) →
    (∀ y ∈ Set.uIcc y₀ y₁, ∀ i, |n y i|^2 ≤ M*R) →
    (∀ y ∈ Set.uIcc y₀ y₁,
      |μnew y 1*(d y 1)^3/(μnew y 0*(d y 0)^3)-1| ≤ B*R^2/N^2) →
    |φ y₁-φ y₀-deriv φ y₀*(y₁-y₀)| ≤
      (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4*|y₁-y₀|^2/(N*dmin^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_taylor_source_scale σ δ T M N R B dmin y₀ y₁ F A W x₀ e r v s x₁ hσ hδ hF hT hM hN hR hNscale hscale hB hdmin hA hW hx₀ hx₁ hr hdet hden

end HuxleyQuarticReciprocalRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_integer_labels_of_taylor_remainders
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_sector_integer_labels
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureNumerator_degree
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureNumerator_eval
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureBoundaryPolynomial_degree
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureBoundaryPolynomial_eval
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureBoundaryPolynomial_isRoot_iff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureBoundaryRoots_card
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.mem_quarticCurvatureBoundaryRoots_iff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_curvature_boundary_dichotomy
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.finite_boundary_rank_interval
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.continuous_band_constant_on_boundary_rank
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_curvature_band_rank_partition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.finiteBoundaryCell_ordConnected
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_curvature_band_finite_interval_partition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_taylor_on_boundary_cell
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_taylor_on_boundary_cell
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_quartic_boundary_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_quartic_band_count_le_cells

namespace HuxleyQuarticRegionRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase Polynomial
open scoped Classical

example
    {K : ℕ} {l w B y₀ α β δ C : ℝ} {g : ℝ → ℝ} {H : ℤ × ℤ → ℤ}
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hcard : max ((w-l)*(K:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector K l w).card)
    (htaylor : ∀ p ∈ HuxleyLinearForm.fareySector K l w,
      |g ((p.1:ℝ)/p.2)-g y₀-deriv g y₀*((p.1:ℝ)/p.2-y₀)| ≤
        C*|((p.1:ℝ)/p.2)-y₀|^2)
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector K l w,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/p.2)-H p| ≤ δ) :
    let η := δ+(K:ℝ)*C*(w-l)^2
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < (HuxleyLinearForm.fareySector K l w).card →
    ∀ p ∈ HuxleyLinearForm.fareySector K l w,
      H p=p.1*round (α-deriv g y₀)+p.2*round (β-g y₀+y₀*deriv g y₀) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.sector_integer_labels_of_taylor_remainders K l w B y₀ α β δ C g H hl hw hlw hB hy₀ hδ hC hcard htaylor hnear

example
    {K : ℕ} {σ δ T M N R B dmin l w Bd y₀ Δ Q : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    {cnew : ℤ × ℤ → Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc l w, ∀ i, x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hBd : 1 ≤ Bd) (hy₀ : y₀ ∈ Set.Icc l w)
    (hden : ∀ y ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*y+s i) :
    let S := HuxleyLinearForm.fareySector K l w
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun y i => round (x₁ y i)
    let n := fun y i => b y i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (b y i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let d := fun y i => (r i:ℝ)*y+s i
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun y => g y-h y
    let z := fun (p : ℤ × ℤ) i => q p i*iteratedDeriv 1 (f i) (b ((p.1:ℝ)/p.2) i)
    let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+
      2*n ((p.1:ℝ)/p.2) i*(e i*p.1+v i*p.2)
    let H := fun p => (cnew p 0-j p 0)-(cnew p 1-j p 1)
    let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
    let η := D+(K:ℝ)*C*(w-l)^2
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ y ∈ Set.Icc l w, ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=((e i:ℝ)*y+v i)/d y i) →
    (∀ y ∈ Set.Icc l w, ∀ i, |(n y i:ℝ)|^2 ≤ M*R) →
    (∀ y ∈ Set.Icc l w, |μnew y 1*(d y 1)^3/(μnew y 0*(d y 0)^3)-1| ≤ B*R^2/N^2) →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    max ((w-l)*(K:ℝ)^2/Bd) 2 ≤ S.card →
    1536*Bd*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, H p=p.1*round (α-deriv φ y₀)+p.2*round (β-φ y₀+y₀*deriv φ y₀) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_sector_integer_labels K σ δ T M N R B dmin l w Bd y₀ Δ Q F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hN hR hRM hNscale hscale hB hdmin hΔ hQ hA hW hx₀ hx₁ hr hdet hl hw hlw hBd hy₀ hden

example (μ ν r s μ₁ ν₁ r₁ s₁ : ℝ) :
    (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).natDegree ≤ 5 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureNumerator_degree μ ν r s μ₁ ν₁ r₁ s₁

example
    {μ ν r s μ₁ ν₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x =
      (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).eval x/
        ((r*x+s)^4*(r₁*x+s₁)^4) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureNumerator_eval μ ν r s μ₁ ν₁ r₁ s₁ x hμ hμ₁ hr hr₁ hx hx₁

example
    (μ ν r s μ₁ ν₁ r₁ s₁ c : ℝ) :
    (quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ c).natDegree ≤ 8 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureBoundaryPolynomial_degree μ ν r s μ₁ ν₁ r₁ s₁ c

example
    {μ ν r s μ₁ ν₁ r₁ s₁ c x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    (quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ c).eval x =
      ((r*x+s)^4*(r₁*x+s₁)^4)*
        (iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
          iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x-c) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureBoundaryPolynomial_eval μ ν r s μ₁ ν₁ r₁ s₁ c x hμ hμ₁ hr hr₁ hx hx₁

example
    {μ ν r s μ₁ ν₁ r₁ s₁ c x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    (quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ c).IsRoot x ↔
      iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
        iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x=c :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureBoundaryPolynomial_isRoot_iff μ ν r s μ₁ ν₁ r₁ s₁ c x hμ hμ₁ hr hr₁ hx hx₁

example
    (μ ν r s μ₁ ν₁ r₁ s₁ U : ℝ) :
    (quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U).card ≤ 16 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticCurvatureBoundaryRoots_card μ ν r s μ₁ ν₁ r₁ s₁ U

example
    {μ ν r s μ₁ ν₁ r₁ s₁ U x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hp : quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ U ≠ 0)
    (hm : quarticCurvatureBoundaryPolynomial μ ν r s μ₁ ν₁ r₁ s₁ (-U) ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    x ∈ quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U ↔
      (iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
        iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x=U) ∨
      (iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
        iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x= -U) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.mem_quarticCurvatureBoundaryRoots_iff μ ν r s μ₁ ν₁ r₁ s₁ U x hμ hμ₁ hr hr₁ hp hm hx hx₁

example
    {μ ν r s μ₁ ν₁ r₁ s₁ U : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) :
    let F := fun x => iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x
    (∀ x, r*x+s ≠ 0 → r₁*x+s₁ ≠ 0 → F x=U) ∨
    (∀ x, r*x+s ≠ 0 → r₁*x+s₁ ≠ 0 → F x= -U) ∨
    ∃ S : Finset ℝ, S.card ≤ 16 ∧
      ∀ x, r*x+s ≠ 0 → r₁*x+s₁ ≠ 0 → (x ∈ S ↔ F x=U ∨ F x= -U) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_curvature_boundary_dichotomy μ ν r s μ₁ ν₁ r₁ s₁ U hμ hμ₁ hr hr₁

example {S : Finset ℝ} {x y : ℝ}
    (hx : x ∉ S) (hy : y ∉ S)
    (heq : (S.filter (fun z => z<x)).card=(S.filter (fun z => z<y)).card) :
    ∀ z ∈ Set.uIcc x y, z ∉ S :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.finite_boundary_rank_interval S x y hx hy heq

example
    {f : ℝ → ℝ} {S : Finset ℝ} {x y U : ℝ}
    (hf : ContinuousOn f (Set.uIcc x y))
    (hboundary : ∀ z ∈ Set.uIcc x y, |f z|=U → z ∈ S)
    (hx : x ∉ S) (hy : y ∉ S)
    (heq : (S.filter (fun z => z<x)).card=(S.filter (fun z => z<y)).card) :
    (|f x| ≤ U ↔ |f y| ≤ U) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.continuous_band_constant_on_boundary_rank f S x y U hf hboundary hx hy heq

example
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ x ∈ Set.Icc l w, r*x+s ≠ 0)
    (hden₁ : ∀ x ∈ Set.Icc l w, r₁*x+s₁ ≠ 0) :
    let F := fun x => iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x
    let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    S.card ≤ 16 ∧
      ∀ x ∈ Set.Icc l w, ∀ y ∈ Set.Icc l w, x ∉ S → y ∉ S →
        (S.filter (fun z => z<x)).card=(S.filter (fun z => z<y)).card →
        (|F x| ≤ U ↔ |F y| ≤ U) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_curvature_band_rank_partition μ ν r s μ₁ ν₁ r₁ s₁ U l w hμ hμ₁ hr hr₁ hden hden₁

example (S : Finset ℝ) (l w : ℝ) (k : ℕ) :
    Set.OrdConnected (finiteBoundaryCell S l w k) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.finiteBoundaryCell_ordConnected S l w k

example
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ x ∈ Set.Icc l w, r*x+s ≠ 0)
    (hden₁ : ∀ x ∈ Set.Icc l w, r₁*x+s₁ ≠ 0) :
    let F := fun x => iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x
    let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    S.card ≤ 16 ∧
      (∀ k : Fin 17, Set.OrdConnected (finiteBoundaryCell S l w k)) ∧
      (∀ x ∈ Set.Icc l w, x ∈ S ∨ ∃ k : Fin 17, x ∈ finiteBoundaryCell S l w k) ∧
      (∀ k : Fin 17, ∀ x ∈ finiteBoundaryCell S l w k,
        ∀ y ∈ finiteBoundaryCell S l w k, |F x| ≤ U ↔ |F y| ≤ U) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_curvature_band_finite_interval_partition μ ν r s μ₁ ν₁ r₁ s₁ U l w hμ hμ₁ hr hr₁ hden hden₁

example
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ y ∈ Set.Icc l w, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l w, r₁*y+s₁ ≠ 0) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun y => g y-h y
    let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀ ∈ finiteBoundaryCell S l w k →
    x ∈ finiteBoundaryCell S l w k →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    |φ x-φ x₀-deriv φ x₀*(x-x₀)| ≤ U*|x-x₀|^2/2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_taylor_on_boundary_cell μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x k hμ hμ₁ hr hr₁ hden hden₁

example
    {σ δ T M N R B dmin u t l w y : ℝ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ e r v s : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : 0 < t)
    (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z ∈ Set.Icc l w, ∀ i, dmin ≤ r i*z+s i) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => (round (x₀ i):ℝ)
    let b := fun i => (round (x₁ i):ℝ)
    let n := fun i => b i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun i => iteratedDeriv 3 (f i) (b i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun i => r i*u+s i*t
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let S := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    u/t ∈ finiteBoundaryCell S l w k →
    y ∈ finiteBoundaryCell S l w k →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(e i*u+v i*t)/q i) →
    (∀ i, |n i|^2 ≤ M*R) →
    |μnew 1*(q 1)^3/(μnew 0*(q 0)^3)-1| ≤ B*R^2/N^2 →
    |φ y-φ (u/t)-deriv φ (u/t)*(y-u/t)| ≤ U*|y-u/t|^2/2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_taylor_on_boundary_cell σ δ T M N R B dmin u t l w y k F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hNscale hscale hB hdmin hA hW hx₀ hx₁ hr ht hdet hden

example
    {K : ℕ} {l w : ℝ} (hl : 0 < l) (hw : 0 ≤ w)
    (μ ν r s μ₁ ν₁ r₁ s₁ U : ℝ) :
    ((HuxleyLinearForm.fareySector K l w).filter (fun p =>
      (p.1:ℝ)/p.2 ∈ quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U)).card ≤ 16 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_quartic_boundary_count K l w hl hw μ ν r s μ₁ ν₁ r₁ s₁ U

example
    {K : ℕ} {l w : ℝ} (hl : 0 < l) (hw : 0 ≤ w)
    {μ ν r s μ₁ ν₁ r₁ s₁ U : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ x ∈ Set.Icc l w, r*x+s ≠ 0)
    (hden₁ : ∀ x ∈ Set.Icc l w, r₁*x+s₁ ≠ 0) :
    let S := HuxleyLinearForm.fareySector K l w
    let B := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    let F := fun x => iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x
    (S.filter (fun p => |F ((p.1:ℝ)/p.2)| ≤ U)).card ≤ 16+
      ∑ k : Fin 17, (S.filter (fun p : ℤ × ℤ =>
        (p.1:ℝ)/p.2 ∈ finiteBoundaryCell B l w k ∧ |F ((p.1:ℝ)/p.2)| ≤ U)).card :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_quartic_band_count_le_cells K l w hl hw μ ν r s μ₁ ν₁ r₁ s₁ U hμ hμ₁ hr hr₁ hden hden₁

end HuxleyQuarticRegionRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_second_condition_residual_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_second_condition_residual_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_branch_remainder
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_condition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_derivative_variation_on_boundary_cell
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_no_wrap_on_boundary_cell
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_condition_on_cell

namespace HuxleyQuarticSecondRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example
    {μ ν r s u t n γ : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    n/q+r*γ/(t*q)-
        (-deriv (rationalBranch μ r s) (u/t)+deriv (quarticBranch μ ν r s) (u/t))/t =
      (n+(2*ν/μ)*G^2-G)/q+r/(t*q)*(γ+2*ν*q*n^3)-
        2*ν*r/t*(n^3-G^3) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_second_condition_residual_identity μ ν r s u t n γ hμ hr ht hq

example
    {μ ν r s u t n γ A V D : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) :
    let q := r*u+s*t
    let G := minorArcCoordinate μ r s (u/t)
    |n-G| ≤ A →
    |n+(2*ν/μ)*G^2-G| ≤ V →
    |γ+2*ν*q*n^3| ≤ |q| * D →
    |n/q+r*γ/(t*q)-
        (-deriv (rationalBranch μ r s) (u/t)+deriv (quarticBranch μ ν r s) (u/t))/t| ≤
      V/|q|+|r| * D/|t|+2*|ν*r/t| * A*(3*|n|^2+3*|n| * A+A^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticBranch_second_condition_residual_bound μ ν r s u t n γ A V D hμ hr ht hq

example
    {σ δ T M A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : r ≠ 0) (ht : t ≠ 0) (hq : r*u+s*t ≠ 0) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let ν := iteratedDeriv 4 f a/24
    let q := r*u+s*t
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    let κ := modelPhaseThirdLower σ
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let C₄ := modelPhaseJetCoefficient σ 4+δ
    let D := C₂/κ+C₃*|n|^2/(2*κ*M)
    let V := C₂/κ+C₄*|n|^3/(6*κ*M^2)+C₃/(2*κ*M)*D*(2*|n|+D)
    let E := T*C₂*|n|/(2*M^3)+T*C₄*|n|^4/(8*M^5)
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    |n/q+r*γ/(t*q)-
        (-deriv (rationalBranch μ r s) (u/t)+deriv (quarticBranch μ ν r s) (u/t))/t| ≤
      V/|q|+|r| * E/|t|+2*|ν*r/t| * D*(3*|n|^2+3*|n| * D+D^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_branch_remainder σ δ T M A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M Δ₂ Δ₄ ε : ℝ} {u t tb ub a b : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ}
    {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hε : ε < 1/2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let η := fun i => q i*d₁ i-cnew i
    let j := fun i => cnew i-(c i*u+2*n i*(e i*u+v i*t))
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew i/q i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let Z := (θ 0-θ 1-a-deriv g ((u:ℝ)/t)+deriv h ((u:ℝ)/t))/(t:ℝ)
    let κ := modelPhaseThirdLower σ
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let C₄ := modelPhaseJetCoefficient σ 4+δ
    let D := fun i => C₂/κ+C₃*|(n i:ℝ)|^2/(2*κ*M)
    let V := fun i => C₂/κ+C₄*|(n i:ℝ)|^3/(6*κ*M^2)+
      C₃/(2*κ*M)*D i*(2*|(n i:ℝ)|+D i)
    let E := fun i => T*C₂*|(n i:ℝ)|/(2*M^3)+T*C₄*|(n i:ℝ)|^4/(8*M^5)
    let B := fun i => V i/|q i|+|(r i:ℝ)| * E i/|(t:ℝ)|+
      2*|ν i*r i/(t:ℝ)| * D i*(3*|(n i:ℝ)|^2+3*|(n i:ℝ)| * D i+(D i)^2)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    cnew 0 ∈ minorArcCenterLabels (q 0*d₁ 0) ε →
    |η 1-η 0| ≤ Δ₄ →
    j 0-j 1=a*u+b*t →
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    |Z| < 1/2 →
    |θ 0-θ 1-a-deriv g ((u:ℝ)/t)+deriv h ((u:ℝ)/t)| ≤
      |(t:ℝ)| * (Δ₂+B 0+B 1+
        (1/2+ε)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q 0| * |q 1|)+
        |(r 1:ℝ)| * Δ₄/(|(t:ℝ)| * |q 1|)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_condition σ δ T M Δ₂ Δ₄ ε u t tb ub a b F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hε hA hW hx₀ hx₁ hr ht hq hdet hbez

example
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ y ∈ Set.Icc l w, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l w, r₁*y+s₁ ≠ 0) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun y => g y-h y
    let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀ ∈ finiteBoundaryCell S l w k →
    x ∈ finiteBoundaryCell S l w k →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    |deriv φ x-deriv φ x₀| ≤ U*|x-x₀| :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_derivative_variation_on_boundary_cell μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x k hμ hμ₁ hr hr₁ hden hden₁

example
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x α t : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ y ∈ Set.Icc l w, r*y+s ≠ 0)
    (hden₁ : ∀ y ∈ Set.Icc l w, r₁*y+s₁ ≠ 0)
    (ht : 4 ≤ t) (hwidth : 8*U*(w-l) ≤ t) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun y => g y-h y
    let S := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀ ∈ finiteBoundaryCell S l w k →
    x ∈ finiteBoundaryCell S l w k →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    |(α-round (α-deriv φ x₀)-deriv φ x)/t| < 1/2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_no_wrap_on_boundary_cell μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x α t k hμ hμ₁ hr hr₁ hden hden₁ ht hwidth

example
    {σ δ T M N R Bc dmin l w y₀ Δ₂ Δ₄ ε : ℝ} {k : Fin 17} {u t tb ub a b : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ}
    {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hε : ε < 1/2)
    (hN : 0 < N) (hR : 1 ≤ R) (hNscale : N^2 ≤ M*R)
    (hscale : T*N*R^2=M^3) (hBc : 0 ≤ Bc) (hdmin : 0 < dmin)
    (ht4 : (4:ℝ) ≤ t)
    (hden : ∀ z ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*z+s i)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (ht : t ≠ 0)
    (hq : ∀ i, r i*u+s i*t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let η := fun i => q i*d₁ i-cnew i
    let j := fun i => cnew i-(c i*u+2*n i*(e i*u+v i*t))
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew i/q i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let κ := modelPhaseThirdLower σ
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let C₄ := modelPhaseJetCoefficient σ 4+δ
    let D := fun i => C₂/κ+C₃*|(n i:ℝ)|^2/(2*κ*M)
    let V := fun i => C₂/κ+C₄*|(n i:ℝ)|^3/(6*κ*M^2)+
      C₃/(2*κ*M)*D i*(2*|(n i:ℝ)|+D i)
    let E := fun i => T*C₂*|(n i:ℝ)|/(2*M^3)+T*C₄*|(n i:ℝ)|^4/(8*M^5)
    let B := fun i => V i/|q i|+|(r i:ℝ)| * E i/|(t:ℝ)|+
      2*|ν i*r i/(t:ℝ)| * D i*(3*|(n i:ℝ)|^2+3*|(n i:ℝ)| * D i+(D i)^2)
    let μnew := fun i => iteratedDeriv 3 (f i) (round (x₁ i))/6
    let φ := fun z => g z-h z
    let U := (4/κ)*(Bc+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let S := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    cnew 0 ∈ minorArcCenterLabels (q 0*d₁ 0) ε →
    |η 1-η 0| ≤ Δ₄ →
    j 0-j 1=a*u+b*t →
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    (∀ i, |(n i:ℝ)|^2 ≤ M*R) →
    |μnew 1*(q 1)^3/(μnew 0*(q 0)^3)-1| ≤ Bc*R^2/N^2 →
    ((u:ℝ)/t) ∈ finiteBoundaryCell S l w k →
    y₀ ∈ finiteBoundaryCell S l w k →
    a=round (θ 0-θ 1-deriv φ y₀) →
    8*U*(w-l) ≤ (t:ℝ) →
    |θ 0-θ 1-a-deriv g ((u:ℝ)/t)+deriv h ((u:ℝ)/t)| ≤
      |(t:ℝ)| * (Δ₂+B 0+B 1+
        (1/2+ε)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q 0| * |q 1|)+
        |(r 1:ℝ)| * Δ₄/(|(t:ℝ)| * |q 1|)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_condition_on_cell σ δ T M N R Bc dmin l w y₀ Δ₂ Δ₄ ε k u t tb ub a b F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hε hN hR hNscale hscale hBc hdmin ht4 hden hA hW hx₀ hx₁ hr ht hq hdet hbez

end HuxleyQuarticSecondRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_far_inverse_farey_factor
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coordinate_error_source_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_second_remainder_source_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_branch_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_condition_source_scale

namespace HuxleyQuarticScaleRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : 0 < r) (ht : 0 < t) (hq : 0 < r*u+s*t) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let n := (round x₁:ℝ)-(round x₀:ℝ)
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    2 ≤ n →
    (r/t)*n ≤ 4*N*R^2/(modelPhaseThirdLower σ*(r*u+s*t)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_far_inverse_farey_factor σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {n N M R C₂ C₃ C₄ κ : ℝ}
    (hn : 0 ≤ n) (hN : 0 < N) (hM : 0 < M) (hR : 1 ≤ R)
    (hRM : R ≤ M) (hNscale : N^2 ≤ M*R) (hNR : N ≤ R^2)
    (hnsquare : n^2 ≤ M*R) (hκ : 0 < κ)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) :
    let K := C₂/κ+C₃/(2*κ)
    let D := C₂/κ+C₃*n^2/(2*κ*M)
    C₂/κ+C₄*n^3/(6*κ*M^2)+C₃/(2*κ*M)*D*(2*n+D) ≤
      (C₂/κ+C₄/(6*κ)+C₃/(2*κ)*K*(2+K))*R^2/N :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coordinate_error_source_budget n N M R C₂ C₃ C₄ κ hn hN hM hR hRM hNscale hNR hnsquare hκ hC₂ hC₃ hC₄

example
    {n N M R C₂ C₃ C₄ κ q w ν : ℝ}
    (hn : 1 ≤ n) (hN : 0 < N) (hM : 0 < M) (hR : 1 ≤ R)
    (hRM : R ≤ M) (hNscale : N^2 ≤ M*R) (hNR : N ≤ R^2)
    (hnsquare : n^2 ≤ M*R) (hκ : 0 < κ) (hq : 0 < q) (hw : 0 ≤ w)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄)
    (hfar : w*n ≤ 4*N*R^2/(κ*q))
    (hν : |ν| ≤ C₃/(24*M*N*R^2)) :
    let K := C₂/κ+C₃/(2*κ)
    let D := C₂/κ+C₃*n^2/(2*κ*M)
    let V := C₂/κ+C₄*n^3/(6*κ*M^2)+C₃/(2*κ*M)*D*(2*n+D)
    let E := C₂*n/(2*N*R^2)+C₄*n^4/(8*M^2*N*R^2)
    let C := C₂/κ+C₄/(6*κ)+C₃/(2*κ)*K*(2+K)+
      2*C₂/κ+C₄/(2*κ)+C₃/(3*κ)*(3*K+3*K^2+K^3)
    V/q+w*E+2*|ν| * w*D*(3*n^2+3*n*D+D^2) ≤ C*R^2/(N*q) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_second_remainder_source_budget n N M R C₂ C₃ C₄ κ q w ν hn hN hM hR hRM hNscale hNR hnsquare hκ hq hw hC₂ hC₃ hC₄ hfar hν

example
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hRM : R ≤ M) (hNscale : N^2 ≤ M*R) (hNR : N ≤ R^2)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo (1/2:ℝ) (W-1/2)) (hx₁ : x₁ ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hr : 0 < r) (ht : 0 < t) (hq : 0 < r*u+s*t) (hdet : v*r-e*s=1) :
    let f := heathBrownPhysicalPhase F T M A 1
    let a : ℝ := round x₀
    let b : ℝ := round x₁
    let n := b-a
    let μ := iteratedDeriv 3 f a/6
    let ν := iteratedDeriv 4 f a/24
    let q := r*u+s*t
    let γ := q*(iteratedDeriv 1 f b-iteratedDeriv 1 f a-2*e*n/r-n*t/(r*q))
    let κ := modelPhaseThirdLower σ
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let C₄ := modelPhaseJetCoefficient σ 4+δ
    let D := C₂/κ+C₃*|n|^2/(2*κ*M)
    let V := C₂/κ+C₄*|n|^3/(6*κ*M^2)+C₃/(2*κ*M)*D*(2*|n|+D)
    let E := T*C₂*|n|/(2*M^3)+T*C₄*|n|^4/(8*M^5)
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/q →
    2 ≤ n → n^2 ≤ M*R →
    (V/|q|+|r| * E/|t|+2*|ν*r/t| * D*(3*|n|^2+3*|n| * D+D^2) ≤
      quarticSecondResidualConstant σ δ*R^2/(N*q)) ∧
    |n/q+r*γ/(t*q)-
        (-deriv (rationalBranch μ r s) (u/t)+deriv (quarticBranch μ ν r s) (u/t))/t| ≤
      quarticSecondResidualConstant σ δ*R^2/(N*q) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_branch_source_scale σ δ T M N R A W x₀ x₁ e r v s u t F hσ hδ hF hT hM hN hR hRM hNscale hNR hscale hA hW hx₀ hx₁ hr ht hq hdet

example
    {σ δ T M N R Q Bc dmin l w y₀ Δ₂ Δ₄ ε : ℝ} {k : Fin 17} {u t tb ub a b : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ}
    {e r v s cnew : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hε : ε < 1/2)
    (hQ : 0 < Q) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M) (hNR : N ≤ R^2) (hNscale : N^2 ≤ M*R)
    (hscale : T*N*R^2=M^3) (hBc : 0 ≤ Bc) (hdmin : 0 < dmin)
    (ht4 : (4:ℝ) ≤ t)
    (hden : ∀ z ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*z+s i)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i)
    (hqband : ∀ i, Q ≤ (r i:ℝ)*u+s i*t) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hbez : t*tb+u*ub=1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let η := fun i => q i*d₁ i-cnew i
    let j := fun i => cnew i-(c i*u+2*n i*(e i*u+v i*t))
    let X := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew i/q i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let κ := modelPhaseThirdLower σ
    let μnew := fun i => iteratedDeriv 3 (f i) (round (x₁ i))/6
    let φ := fun z => g z-h z
    let U := (4/κ)*(Bc+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let S := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    cnew 0 ∈ minorArcCenterLabels (q 0*d₁ 0) ε →
    |η 1-η 0| ≤ Δ₄ →
    j 0-j 1=a*u+b*t →
    |(X 0-X 1)-round (X 0-X 1)| ≤ Δ₂ →
    (∀ i, 2 ≤ (n i:ℝ)) →
    (∀ i, |(n i:ℝ)|^2 ≤ M*R) →
    |μnew 1*(q 1)^3/(μnew 0*(q 0)^3)-1| ≤ Bc*R^2/N^2 →
    ((u:ℝ)/t) ∈ finiteBoundaryCell S l w k →
    y₀ ∈ finiteBoundaryCell S l w k →
    a=round (θ 0-θ 1-deriv φ y₀) →
    8*U*(w-l) ≤ (t:ℝ) →
    |θ 0-θ 1-a-deriv g ((u:ℝ)/t)+deriv h ((u:ℝ)/t)| ≤
      |(t:ℝ)| * (Δ₂+2*quarticSecondResidualConstant σ δ*R^2/(N*Q)+
        (1/2+ε)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q 0| * |q 1|)+
        |(r 1:ℝ)| * Δ₄/(|(t:ℝ)| * |q 1|)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_second_condition_source_scale σ δ T M N R Q Bc dmin l w y₀ Δ₂ Δ₄ ε k u t tb ub a b F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hε hQ hN hR hRM hNR hNscale hscale hBc hdmin ht4 hden hA hW hx₀ hx₁ hr hqband hdet hbez

end HuxleyQuarticScaleRegression


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_sector_integer_labels_on_cell
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_constructed_quartic_sector_second
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_boundary_cell_eq_sector
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_four_point_curvature
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_cubic_ratio_of_curvature
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_four_point_third_condition

namespace HuxleyQuarticSampledSectorRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped Classical

example
    {K : ℕ} {σ δ T M N R B dmin l w Bd Δ Q : ℝ}
    {p₀ : ℤ × ℤ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    {cnew : ℤ × ℤ → Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ p ∈ HuxleyLinearForm.fareySector K l w, ∀ i,
      x₁ ((p.1:ℝ)/p.2) i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hBd : 1 ≤ Bd) (hp₀ : p₀ ∈ HuxleyLinearForm.fareySector K l w)
    (hden : ∀ y ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*y+s i) :
    let S := HuxleyLinearForm.fareySector K l w
    let y₀ := (p₀.1:ℝ)/p₀.2
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun y i => round (x₁ y i)
    let n := fun y i => b y i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (b y i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun y => g y-h y
    let z := fun (p : ℤ × ℤ) i => q p i*iteratedDeriv 1 (f i) (b ((p.1:ℝ)/p.2) i)
    let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+
      2*n ((p.1:ℝ)/p.2) i*(e i*p.1+v i*p.2)
    let H := fun p => (cnew p 0-j p 0)-(cnew p 1-j p 1)
    let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
    let η := D+(K:ℝ)*C*(w-l)^2
    let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    l ∈ finiteBoundaryCell Z l w k →
    w ∈ finiteBoundaryCell Z l w k →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i,
      iteratedDeriv 2 (f i) (x₁ ((p.1:ℝ)/p.2) i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n ((p.1:ℝ)/p.2) i:ℝ)|^2 ≤ M*R) →
    |μnew y₀ 1*(q p₀ 1)^3/(μnew y₀ 0*(q p₀ 0)^3)-1| ≤ B*R^2/N^2 →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    max ((w-l)*(K:ℝ)^2/Bd) 2 ≤ S.card →
    1536*Bd*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, H p=p.1*round (α-deriv φ y₀)+p.2*round (β-φ y₀+y₀*deriv φ y₀) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_sector_integer_labels_on_cell K σ δ T M N R B dmin l w Bd Δ Q p₀ k F A W x₀ x₁ e r v s cnew hσ hδ hF hT hM hN hR hRM hNscale hscale hB hdmin hΔ hQ hA hW hx₀ hx₁ hr hdet hl hw hlw hBd hp₀ hden

example
    {K : ℕ} {σ δ T M N R B dmin l w Δ Δ₂ Q Qlo : ℝ}
    {anchor : ℚ}
    {p₀ : ℤ × ℤ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hNR : N ≤ R^2) (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin) (hΔ : 0 ≤ Δ) (hsmall : Δ < 1/2) (hQ : 0 ≤ Q) (hQlo : 0 < Qlo)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ p ∈ HuxleyLinearForm.fareySector K l w, ∀ i,
      x₁ ((p.1:ℝ)/p.2) i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l < w) (hp₀ : p₀ ∈ HuxleyLinearForm.fareySector K l w)
    (hden : ∀ y ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*y+s i)
    (hanchor : (anchor:ℝ) ∈ Set.Icc l w) (hcut : 64*anchor.den ≤ K)
    (hwidthscale : 64 ≤ (w-l)*(K:ℝ)*anchor.den) :
    let S := HuxleyLinearForm.fareySector K l w
    let y₀ := (p₀.1:ℝ)/p₀.2
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun y i => round (x₁ y i)
    let n := fun y i => b y i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (b y i)/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun y => g y-h y
    let z := fun (p : ℤ × ℤ) i => q p i*iteratedDeriv 1 (f i) (b ((p.1:ℝ)/p.2) i)
    let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+
      2*n ((p.1:ℝ)/p.2) i*(e i*p.1+v i*p.2)
    let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
    let η := D+(K:ℝ)*C*(w-l)^2
    let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    l ∈ finiteBoundaryCell Z l w k →
    w ∈ finiteBoundaryCell Z l w k →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ p ∈ S, ∀ i,
      iteratedDeriv 2 (f i) (x₁ ((p.1:ℝ)/p.2) i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n ((p.1:ℝ)/p.2) i:ℝ)|^2 ≤ M*R) →
    |μnew y₀ 1*(q p₀ 1)^3/(μnew y₀ 0*(q p₀ 0)^3)-1| ≤ B*R^2/N^2 →
    (∀ p ∈ S, |(z p 0-z p 1)-round (z p 0-z p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    196608*η*w < (w-l)/128 →
    ∃ cnew : ℤ × ℤ → Fin 2 → ℤ, ∀ p ∈ S,
      (∀ i, cnew p i ∈ minorArcCenterLabels (z p i) Δ) ∧
      cnew p 0=round (z p 0) ∧
      |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ ∧
      (cnew p 0-j p 0)-(cnew p 1-j p 1)=
        p.1*round (α-deriv φ y₀)+p.2*round (β-φ y₀+y₀*deriv φ y₀) ∧
      ∀ tb ub : ℤ, p.2*tb+p.1*ub=1 →
      let V := fun i => ((r i*tb-s i*ub:ℤ):ℝ)*cnew p i/q p i
      |(V 0-V 1)-round (V 0-V 1)| ≤ Δ₂ →
      (4:ℝ) ≤ p.2 →
      (∀ i, Qlo ≤ q p i) →
      (∀ i, 2 ≤ (n ((p.1:ℝ)/p.2) i:ℝ)) →
      |μnew ((p.1:ℝ)/p.2) 1*(q p 1)^3/
        (μnew ((p.1:ℝ)/p.2) 0*(q p 0)^3)-1| ≤ B*R^2/N^2 →
      8*U*(w-l) ≤ (p.2:ℝ) →
      |α-round (α-deriv φ y₀)-deriv g ((p.1:ℝ)/p.2)+
        deriv h ((p.1:ℝ)/p.2)| ≤
        |(p.2:ℝ)| * (Δ₂+2*quarticSecondResidualConstant σ δ*R^2/(N*Qlo)+
          (1/2+Δ)*|(r 1:ℝ)*s 0-r 0*s 1|/(|q p 0| * |q p 1|)+
          |(r 1:ℝ)| * Δ/(|(p.2:ℝ)| * |q p 1|)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_constructed_quartic_sector_second K σ δ T M N R B dmin l w Δ Δ₂ Q Qlo anchor p₀ k F A W x₀ x₁ e r v s hσ hδ hF hT hM hN hR hRM hNR hNscale hscale hB hdmin hΔ hsmall hQ hQlo hA hW hx₀ hx₁ hr hdet hl hw hlw hp₀ hden hanchor hcut hwidthscale

example
    {K k : ℕ} {l w : ℝ} {Z : Finset ℝ}
    (hl : 0 < l) (hlw : l ≤ w)
    (hne : ((HuxleyLinearForm.fareySector K l w).filter
      (fun p => (p.1:ℝ)/p.2 ∈ finiteBoundaryCell Z l w k)).Nonempty) :
    ∃ l' w' : ℝ, l ≤ l' ∧ l' ≤ w' ∧ w' ≤ w ∧
      l' ∈ finiteBoundaryCell Z l' w' k ∧
      w' ∈ finiteBoundaryCell Z l' w' k ∧
      (HuxleyLinearForm.fareySector K l w).filter
        (fun p => (p.1:ℝ)/p.2 ∈ finiteBoundaryCell Z l w k) =
        HuxleyLinearForm.fareySector K l' w' :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_boundary_cell_eq_sector K k l w Z hl hlw hne

example
    {μ ν r s μ₁ ν₁ r₁ s₁ a b c d h E A B : ℝ}
    (hμ : μ ≠ 0) (hr : r ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (hh : 0 < h) (hab : h ≤ b-a) (hbc : h ≤ c-b) (hcd : h ≤ d-c)
    (hden : ∀ x ∈ Set.Icc a d, r*x+s ≠ 0)
    (hden₁ : ∀ x ∈ Set.Icc a d, r₁*x+s₁ ≠ 0) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let H := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    (∀ x ∈ ({a,b,c,d} : Finset ℝ), |A*x+B-g x+H x| ≤ E) →
    ∃ z ∈ Set.Ioo a d,
      |iteratedDeriv 2 g z-iteratedDeriv 2 H z| ≤ 4*E/h^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_four_point_curvature μ ν r s μ₁ ν₁ r₁ s₁ a b c d h E A B hμ hr hμ₁ hr₁ hh hab hbc hcd hden hden₁

example
    {μ ν μnew r s μ₁ ν₁ μnew₁ r₁ s₁ x ε ε₁ D : ℝ}
    (hμ : 0 < μ) (hμ₁ : 0 < μ₁) (hμnew : 0 < μnew) (hμnew₁ : 0 < μnew₁)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hx : 0 < r*x+s) (hx₁ : 0 < r₁*x+s₁)
    (he : |μ/μnew-1+4*ν*minorArcCoordinate μ r s x/μ| ≤ ε)
    (he₁ : |μ₁/μnew₁-1+4*ν₁*minorArcCoordinate μ₁ r₁ s₁ x/μ₁| ≤ ε₁)
    (hcurv : |iteratedDeriv 2 (rationalPhase μ r s μ₁ r₁ s₁) x-
      iteratedDeriv 2 (quarticPhase μ ν r s μ₁ ν₁ r₁ s₁) x| ≤ D) :
    |μnew₁*(r₁*x+s₁)^3/(μnew*(r*x+s)^3)-1| ≤
      (3*μnew₁*(r₁*x+s₁)^3/2)*
        (D+2*ε/(3*μ*(r*x+s)^3)+2*ε₁/(3*μ₁*(r₁*x+s₁)^3)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quarticPhase_cubic_ratio_of_curvature μ ν μnew r s μ₁ ν₁ μnew₁ r₁ s₁ x ε ε₁ D hμ hμ₁ hμnew hμnew₁ hr hr₁ hx hx₁ he he₁ hcurv

example
    {σ δ T M N R L a b c d h E α β : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc a d, ∀ i, x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc a d, ∀ i, 0 < r i*y+s i)
    (hh : 0 < h) (hab : h ≤ b-a) (hbc : h ≤ c-b) (hcd : h ≤ d-c) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let ε := quarticReciprocalConstant σ δ*R^2/(L*N)^2
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc a d, ∀ i, iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc a d, ∀ i, |n y i|^2 ≤ M*R) →
    (∀ y ∈ ({a,b,c,d} : Finset ℝ), |α*y+β-g y+H y| ≤ E) →
    ∃ z ∈ Set.Ioo a d,
      |μnew z 1*(D z 1)^3/(μnew z 0*(D z 0)^3)-1| ≤
        (3*μnew z 1*(D z 1)^3/2)*
          (4*E/h^2+2*ε/(3*μ 0*(D z 0)^3)+2*ε/(3*μ 1*(D z 1)^3)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_four_point_third_condition σ δ T M N R L a b c d h E α β F A W x₀ e r v s x₁ hσ hδ hF hT hM hN hR hL hNL hA hW hx₀ hx₁ hr hdet hden hh hab hbc hcd

end HuxleyQuarticSampledSectorRegression

-- Installed quartic uniform estimates: audit and exact-type regression only.
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_four_point_third_source_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_long_block_third_condition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.ratio_relative_perturbation_of_inverse_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_two_long_block_witnesses
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.determinant_bound_of_varying_cubic_ratios
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_long_block_determinant
namespace HuxleyQuarticUniformRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped Classical

namespace HuxleyQuarticLongBlockRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped Classical

example
    {μ₀ μ₁ μnew d₀ d₁ d K L N R Γ C : ℝ}
    (hμ₀ : 0 < μ₀) (hμ₁ : 0 < μ₁)
    (hd : 0 < d) (hL : 0 < L) (hN : 0 < N)
    (hK : 0 ≤ K) (hΓ : 0 ≤ Γ) (hC : 0 ≤ C)
    (hd₀ : d ≤ d₀) (hd₁ : d ≤ d₁) (hD₁ : d₁ ≤ 2*d)
    (hcoef₀ : μnew ≤ Γ*μ₀) (hcoef₁ : μnew ≤ Γ*μ₁) :
    (3*μnew*d₁^3/2)*
      (4*(6*K*μ₀*R^2*d)/(3*μ₀*d^2*L*N)^2+
        2*(C*R^2/(L*N)^2)/(3*μ₀*d₀^3)+
        2*(C*R^2/(L*N)^2)/(3*μ₁*d₁^3)) ≤
      Γ*(32*K+9*C)*R^2/(L^2*N^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.quartic_four_point_third_source_budget μ₀ μ₁ μnew d₀ d₁ d K L N R Γ C hμ₀ hμ₁ hd hL hN hK hΓ hC hd₀ hd₁ hD₁ hcoef₀ hcoef₁

example
    {σ δ T M N R L d K α β : ℝ} (x : Fin 4 → ℝ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 3), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 3), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 3), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 3), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 3), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 3, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 4, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    ∃ z ∈ Set.Ioo (x 0) (x 3),
      |μnew z 1*(D z 1)^3/(μnew z 0*(D z 0)^3)-1| ≤
        ((σ*(σ+1)+1)/modelPhaseThirdLower σ)*
          (32*K+9*quarticReciprocalConstant σ δ)*R^2/(L^2*N^2) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_long_block_third_condition σ δ T M N R L d K α β x F A W x₀ e r v s x₁ hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono

example
    {a u v ε η Γ : ℝ} (hv : 0 < v) (hΓ : 0 ≤ Γ)
    (ha : |a-1| ≤ ε) (hu : |u-1| ≤ η) (hvv : |v-1| ≤ η)
    (hub : |u| ≤ Γ) (hvinv : 1/v ≤ Γ) :
    |a*u/v-1| ≤ Γ^2*ε+2*Γ*η :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.ratio_relative_perturbation_of_inverse_bound a u v ε η Γ hv hΓ ha hu hvv hub hvinv

example
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    ∃ z₀ ∈ Set.Ioo (x 0) (x 3), ∃ z₁ ∈ Set.Ioo (x 4) (x 7),
      L*N/4 ≤ |G z₁-G z₀| ∧
      (∀ z ∈ ({z₀,z₁} : Finset ℝ),
        |μnew z 1*(D z 1)^3/(μnew z 0*(D z 0)^3)-1| ≤
          ((σ*(σ+1)+1)/modelPhaseThirdLower σ)*
            (32*K+9*quarticReciprocalConstant σ δ)*R^2/(L^2*N^2)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_two_long_block_witnesses σ δ T M N R L d K α β x F A W x₀ e r v s x₁ hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono

example
    {μbase μa μa₁ μb μb₁ r s r₁ s₁ z₀ z₁ Γ ε η q H : ℝ}
    (hbase : 0 < μbase) (ha : 0 < μa) (ha₁ : 0 < μa₁)
    (hb : 0 < μb) (hb₁ : 0 < μb₁) (hr : r ≠ 0)
    (hΓ : 0 < Γ) (hq : 0 < q) (hH : 0 < H)
    (hz₀ : r*z₀+s ≠ 0) (hz₁ : r*z₁+s ≠ 0)
    (hden₀ : q ≤ (r₁*z₀+s₁)/(r*z₀+s))
    (hden₁ : q ≤ (r₁*z₁+s₁)/(r*z₁+s))
    (hthird₀ : |μa₁*(r₁*z₀+s₁)^3/(μa*(r*z₀+s)^3)-1| ≤ ε)
    (hthird₁ : |μb₁*(r₁*z₁+s₁)^3/(μb*(r*z₁+s)^3)-1| ≤ ε)
    (hvar : |μa/μb-1| ≤ η) (hvar₁ : |μa₁/μb₁-1| ≤ η)
    (hcoef : μa ≤ Γ*μbase)
    (hcoef₁ : μa₁ ≤ Γ*μb₁) (hinverse : μb ≤ Γ*μa)
    (hgap : H ≤ |minorArcCoordinate μbase r s z₁-minorArcCoordinate μbase r s z₀|) :
    |r*s₁-s*r₁| ≤
      2*Γ*((1+Γ^2)*ε+2*Γ*η)/(9*μa₁*q^2*H) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.determinant_bound_of_varying_cubic_ratios μbase μa μa₁ μb μb₁ r s r₁ s₁ z₀ z₁ Γ ε η q H hbase ha ha₁ hb hb₁ hr hΓ hq hH hz₀ hz₁ hden₀ hden₁ hthird₀ hthird₁ hvar hvar₁ hcoef hcoef₁ hinverse hgap

example
    {σ δ T M N R L d K Kw α β : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K) (hKw : 0 ≤ Kw)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x)
    (hwindow : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ z ∈ Set.Icc (x 0) (x 7), ∀ i,
      |(round (x₁ y i):ℝ)-(round (x₁ z i):ℝ)| ≤ Kw*L*N) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    |r 0*s 1-s 0*r 1| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C*R^4/(L^3*N^2)+
        2*Γ*(modelPhaseJetCoefficient σ 3+δ)*Kw*N*R^2/(κ*M)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_long_block_determinant σ δ T M N R L d K Kw α β x F A W x₀ e r v s x₁ hσ hδ hF hT hM hN hR hL hNL hd hK hKw hscale hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hwindow

end HuxleyQuarticLongBlockRegression

end HuxleyQuarticUniformRegression

namespace HuxleyQuarticWindowScratch
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped Classical

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_interval_root_family
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_consecutive_window_determinant
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_fixed_matrix_scalar_count

example
    {σ δ T M A W l w L U x₀ H e r v s : ℝ} {F : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hL : L ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hU : U ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hdenl : 0 < r*l+s) (hdenw : 0 < r*w+s)
    (hLdist : |L-x₀| ≤ H) (hUdist : |U-x₀| ≤ H) :
    let f := heathBrownPhysicalPhase F T M A 1
    let I := Set.uIcc (iteratedDeriv 2 f L/2) (iteratedDeriv 2 f U/2)
    (e*l+v)/(r*l+s) ∈ I → (e*w+v)/(r*w+s) ∈ I →
    ∃ ρ : ℝ → ℝ,
      (∀ y ∈ Set.Icc l w, ρ y ∈ Set.uIcc L U ∧
        ρ y ∈ Set.Ioo (1/2:ℝ) (W-1/2) ∧
        iteratedDeriv 2 f (ρ y)/2=(e*y+v)/(r*y+s) ∧
        (round (ρ y):ℝ) ∈ Set.Ioo 0 W ∧
        |(round (ρ y):ℝ)-(round x₀:ℝ)| ≤ H+1) ∧
      (∀ y ∈ Set.Icc l w, ∀ z ∈ Set.Icc l w,
        |(round (ρ y):ℝ)-(round (ρ z):ℝ)| ≤ |U-L|+1) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_interval_root_family σ δ T M A W l w L U x₀ H e r v s F hσ hF hT hM hA hW hL hU hdenl hdenw hLdist hUdist

example
    {B : ℕ} {σ δ T M N R Q Z d K Kw α β ya yb : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ V₀ V₁ H : Fin 2 → ℝ}
    {e r v s : Fin 2 → ℤ}
    (a₀ : Fin B → ℚ) (hB : 32 ≤ B)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hscale : T*N*R^2=M^3) (hd : 0 < d) (hK : 0 ≤ K) (hKw : 0 ≤ Kw)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hV₀ : ∀ i, V₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hV₁ : ∀ i, V₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hV₀dist : ∀ i, |V₀ i-x₀ i| ≤ H i)
    (hV₁dist : ∀ i, |V₁ i-x₀ i| ≤ H i)
    (hsquare : ∀ i, (H i+1)^2 ≤ M*R)
    (hZ : (1/2:ℝ) < Z) (hZW : Z+(B:ℝ)*N < W 0-1/2)
    (hcut : ∀ i, 128*((a₀ i).den:ℝ) ≤ Q)
    (hmajor : ∀ i, 256*R^2 ≤ modelPhaseThirdLower σ*Q*(a₀ i).den)
    (hr : ∀ i, r i ≠ 0) (hr₀ : 0 < r 0) (hs₀ : 0 < s 0)
    (hdet : ∀ i, v i*r i-e i*s i=1)
    (hdena : ∀ i, d ≤ (r i:ℝ)*ya+s i ∧ (r i:ℝ)*ya+s i ≤ 2*d)
    (hdenb : ∀ i, d ≤ (r i:ℝ)*yb+s i ∧ (r i:ℝ)*yb+s i ≤ 2*d) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let Hq := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    let Lw := fun j : Fin B => Z+(j.val:ℝ)*N
    let Uw := fun j : Fin B => Lw j+N
    let l := fun j => iteratedDeriv 2 (f 0) (Lw j)/2
    let w := fun j => iteratedDeriv 2 (f 0) (Uw j)/2
    let S := fun j => fareyCurvatureCoordinates ⌊Q⌋₊ (l j) (w j) (e 0) (r 0) (v 0) (s 0)
    let L := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1))*(B:ℝ)
    (L*N)^2 ≤ M*R →
    (∀ i, |V₁ i-V₀ i|+1 ≤ Kw*L*N) →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, ((e i:ℝ)*ya+v i)/((r i:ℝ)*ya+s i) ∈
      Set.uIcc (iteratedDeriv 2 (f i) (V₀ i)/2) (iteratedDeriv 2 (f i) (V₁ i)/2)) →
    (∀ i, ((e i:ℝ)*yb+v i)/((r i:ℝ)*yb+s i) ∈
      Set.uIcc (iteratedDeriv 2 (f i) (V₀ i)/2) (iteratedDeriv 2 (f i) (V₁ i)/2)) →
    (∀ j, (a₀ j:ℝ) ∈ Set.Icc (l j) (w j)) →
    (∀ j, (e 0:ℝ)/r 0 < l j) → (∀ j, w j < (v 0:ℝ)/s 0) →
    (∀ j, ∀ p ∈ S j, (p.1:ℝ)/p.2 ∈ Set.Icc ya yb) →
    (∀ j, ∀ p ∈ S j,
      |α*((p.1:ℝ)/p.2)+β-g ((p.1:ℝ)/p.2)+Hq ((p.1:ℝ)/p.2)| ≤
        K*R^2/|(r 0:ℝ)*G ((p.1:ℝ)/p.2)|) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    |(r 0:ℝ)*s 1-s 0*r 1| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C*R^4/(L^3*N^2)+
        2*Γ*(modelPhaseJetCoefficient σ 3+δ)*Kw*N*R^2/(κ*M)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_consecutive_window_determinant B σ δ T M N R Q Z d K Kw α β ya yb F A W x₀ V₀ V₁ H e r v s a₀ hB hσ hδ hF hT hM hN hR hscale hd hK hKw hA hW hx₀ hV₀ hV₁ hV₀dist hV₁dist hsquare hZ hZW hcut hmajor hr hr₀ hs₀ hdet hdena hdenb

example
    (S : Finset ℚ) (x y : ℚ → ℝ) (Q : ℕ) (a b c d : ℤ)
    {σ δ T M A W Δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hΔ : 0 ≤ Δ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hscale : 16*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ (modelPhaseThirdLower σ)^2*T)
    (hx : ∀ p ∈ S, x p ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hy : ∀ p ∈ S, y p ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hq : ∀ p ∈ S, p.den ≤ Q) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := fun z => iteratedDeriv 3 f (round z)/6
    let t := fun p : ℚ => (c:ℝ)*(p:ℝ)+d
    (∀ p ∈ S, iteratedDeriv 2 f (x p)/2=(p:ℝ)) →
    (∀ p ∈ S, ((a:ℝ)*(p:ℝ)+b)/t p=iteratedDeriv 2 f (y p)/2) →
    (∀ p ∈ S, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p ∈ S, |μ (y p)*(t p)^3/μ (x p)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (S.card:ℝ) ≤ 1+8*(σ*(σ+1)+1)*(Γ^2*Δ+2*Γ*η)*(Q:ℝ)^2/(|(c:ℝ)| *κ) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_fixed_matrix_scalar_count S x y Q a b c d σ δ T M A W Δ F hσ hδ hδ0 hF hT hM hA hW hΔ hdet hc hscale hx hy hq


-- Installed amplitude-normalized count: audits and exact-type regressions.
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.scaled_C4_nontriangular_resonance_compression
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.scaled_C4_rational_matrix_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_large_entry_matrix_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_large_entry_labelled_count

example
    (f : ℝ → ℝ) {A B L E xl xr yl yr : ℝ}
    (a b c d : ℤ) (hdet : a*d-b*c=1) (hc : c ≠ 0) (hL : 0 < L)
    (hf : ∀ z ∈ Set.Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z ∈ Set.Ioo A B, L ≤ iteratedDeriv 3 f z)
    (hfour : ∀ z ∈ Set.Ioo A B, |iteratedDeriv 4 f z| ≤ |(c:ℝ)| *L^2/16)
    (hxl : xl ∈ Set.Ioo A B) (hxr : xr ∈ Set.Ioo A B)
    (hyl : yl ∈ Set.Ioo A B) (hyr : yr ∈ Set.Ioo A B) :
    let h := fun z => iteratedDeriv 2 f z/2
    let t := fun z => (c:ℝ)*z+d
    h xl ≤ h xr →
    ((a:ℝ)*h xl+b)/t (h xl)=h yl →
    ((a:ℝ)*h xr+b)/t (h xr)=h yr →
    ((1:ℝ)/2 ≤ t (h xl) ∧ t (h xl) ≤ 2) →
    ((1:ℝ)/2 ≤ t (h xr) ∧ t (h xr) ≤ 2) →
    |(iteratedDeriv 3 f yl/6)*t (h xl)^3-iteratedDeriv 3 f xl/6| ≤ E →
    |(iteratedDeriv 3 f yr/6)*t (h xr)^3-iteratedDeriv 3 f xr/6| ≤ E →
    h xr-h xl ≤ 48*E/(|(c:ℝ)| *L) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.scaled_C4_nontriangular_resonance_compression f A B L E xl xr yl yr a b c d hdet hc hL hf hthree hfour hxl hxr hyl hyr

example
    (S : Finset ℚ) (f : ℝ → ℝ) (x y : ℚ → ℝ) (Q : ℕ)
    {A B L E : ℝ} (a b c d : ℤ)
    (hdet : a*d-b*c=1) (hc : c ≠ 0) (hL : 0 < L) (hE : 0 ≤ E)
    (hf : ∀ z ∈ Set.Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z ∈ Set.Ioo A B, L ≤ iteratedDeriv 3 f z)
    (hfour : ∀ z ∈ Set.Ioo A B, |iteratedDeriv 4 f z| ≤ |(c:ℝ)| *L^2/16)
    (hx : ∀ p ∈ S, x p ∈ Set.Ioo A B) (hy : ∀ p ∈ S, y p ∈ Set.Ioo A B)
    (hq : ∀ p ∈ S, p.den ≤ Q) :
    let h := fun z => iteratedDeriv 2 f z/2
    let t := fun p : ℚ => (c:ℝ)*(p:ℝ)+d
    (∀ p ∈ S, h (x p)=(p:ℝ)) →
    (∀ p ∈ S, ((a:ℝ)*(p:ℝ)+b)/t p=h (y p)) →
    (∀ p ∈ S, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p ∈ S, |(iteratedDeriv 3 f (y p)/6)*(t p)^3-
      iteratedDeriv 3 f (x p)/6| ≤ E) →
    (S.card:ℝ) ≤ 1+48*E*(Q:ℝ)^2/(|(c:ℝ)| *L) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.scaled_C4_rational_matrix_count S f x y Q A B L E a b c d hdet hc hL hE hf hthree hfour hx hy hq

example
    (S : Finset ℚ) (x y : ℚ → ℝ) (Q : ℕ) (a b c d : ℤ)
    {σ δ T M A W Δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hΔ : 0 ≤ Δ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hscale : 16*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(c:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hx : ∀ p ∈ S, x p ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hy : ∀ p ∈ S, y p ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hq : ∀ p ∈ S, p.den ≤ Q) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := fun z => iteratedDeriv 3 f (round z)/6
    let t := fun p : ℚ => (c:ℝ)*(p:ℝ)+d
    (∀ p ∈ S, iteratedDeriv 2 f (x p)/2=(p:ℝ)) →
    (∀ p ∈ S, ((a:ℝ)*(p:ℝ)+b)/t p=iteratedDeriv 2 f (y p)/2) →
    (∀ p ∈ S, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p ∈ S, |μ (y p)*(t p)^3/μ (x p)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (S.card:ℝ) ≤ 1+8*(σ*(σ+1)+1)*(Γ^2*Δ+2*Γ*η)*(Q:ℝ)^2/(|(c:ℝ)| *κ) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_large_entry_matrix_count S x y Q a b c d σ δ T M A W Δ F hσ hδ hδ0 hF hT hM hA hW hΔ hdet hc hscale hx hy hq

example
    (S : Finset ℚ) (x y : ℚ → ℝ) (Q : ℕ) (a b c d : ℤ)
    {σ δ T M A W Δ ε : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hΔ : 0 ≤ Δ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hscale : 16*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(c:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hx : ∀ p ∈ S, x p ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hy : ∀ p ∈ S, y p ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hq : ∀ p ∈ S, p.den ≤ Q) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := fun z => iteratedDeriv 3 f (round z)/6
    let t := fun p : ℚ => (c:ℝ)*(p:ℝ)+d
    (∀ p ∈ S, iteratedDeriv 2 f (x p)/2=(p:ℝ)) →
    (∀ p ∈ S, ((a:ℝ)*(p:ℝ)+b)/t p=iteratedDeriv 2 f (y p)/2) →
    (∀ p ∈ S, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p ∈ S, |μ (y p)*(t p)^3/μ (x p)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    let z := fun p : ℚ => (p.den:ℝ)*iteratedDeriv 1 f (round (x p))
    let z₁ := fun p : ℚ => ((c:ℝ)*p.num+d*p.den)*iteratedDeriv 1 f (round (y p))
    ((S.sigma (fun p =>
      (minorArcCenterLabels (z p) ε).product (minorArcCenterLabels (z₁ p) ε))).card:ℝ) ≤
      4*(1+8*(σ*(σ+1)+1)*(Γ^2*Δ+2*Γ*η)*(Q:ℝ)^2/(|(c:ℝ)| *κ)) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_large_entry_labelled_count S x y Q a b c d σ δ T M A W Δ ε F hσ hδ hδ0 hF hT hM hA hW hΔ hdet hc hscale hx hy hq


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.scaled_C4_block_matrix_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_large_entry_block_count
example
    (S : Finset ℤ) (f : ℝ → ℝ) (x y : ℤ → ℝ)
    {A B L E N Z : ℝ} (a b c d : ℤ)
    (hdet : a*d-b*c=1) (hc : c ≠ 0) (hL : 0 < L) (hE : 0 ≤ E) (hN : 0 < N)
    (hf : ∀ z ∈ Set.Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z ∈ Set.Ioo A B, L ≤ iteratedDeriv 3 f z)
    (hfour : ∀ z ∈ Set.Ioo A B, |iteratedDeriv 4 f z| ≤ |(c:ℝ)| *L^2/16)
    (hx : ∀ k ∈ S, x k ∈ Set.Ioo A B) (hy : ∀ k ∈ S, y k ∈ Set.Ioo A B)
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ x k ∧ x k ≤ Z+((k:ℝ)+1)*N) :
    let h := fun z => iteratedDeriv 2 f z/2
    let t := fun z => (c:ℝ)*z+d
    (∀ k ∈ S, ((a:ℝ)*h (x k)+b)/t (h (x k))=h (y k)) →
    (∀ k ∈ S, (1:ℝ)/2 ≤ t (h (x k)) ∧ t (h (x k)) ≤ 2) →
    (∀ k ∈ S, |(iteratedDeriv 3 f (y k)/6)*(t (h (x k)))^3-
      iteratedDeriv 3 f (x k)/6| ≤ E) →
    (S.card:ℝ) ≤ 2+96*E/(|(c:ℝ)| *L^2*N) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.scaled_C4_block_matrix_count S f x y A B L E N Z a b c d hdet hc hL hE hN hf hthree hfour hx hy hwindow

example
    (S : Finset ℤ) (x y : ℤ → ℝ) (a b c d : ℤ)
    {σ δ T M A W Δ N R Z : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hphase : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hΔ : 0 ≤ Δ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hscale : 16*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(c:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hx : ∀ p ∈ S, x p ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hy : ∀ p ∈ S, y p ∈ Set.Ioo (1/2:ℝ) (W-1/2))
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ x k ∧ x k ≤ Z+((k:ℝ)+1)*N) :
    let f := heathBrownPhysicalPhase F T M A 1
    let μ := fun z => iteratedDeriv 3 f (round z)/6
    let t := fun p : ℤ => (c:ℝ)*(iteratedDeriv 2 f (x p)/2)+d
    (∀ p ∈ S, ((a:ℝ)*(iteratedDeriv 2 f (x p)/2)+b)/t p=iteratedDeriv 2 f (y p)/2) →
    (∀ p ∈ S, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p ∈ S, |μ (y p)*(t p)^3/μ (x p)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (S.card:ℝ) ≤ 2+16*(σ*(σ+1)+1)*(Γ^2*Δ+2*Γ*η)*R^2/(κ^2*|(c:ℝ)|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_large_entry_block_count S x y a b c d σ δ T M A W Δ N R Z F hσ hδ hδ0 hF hT hM hN hphase hA hW hΔ hdet hc hscale hx hy hwindow

open Set
open scoped ContDiff

#print axioms TaoTrudgianYang2025.bourgain_paired_C4_nontriangular_resonance_compression

example
    (f f₁ : ℝ → ℝ) {A B A₁ B₁ L E xl xr yl yr : ℝ}
    (a b c d : ℤ) (hdet : a*d-b*c=1) (hc : c ≠ 0) (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x)
    (hfour : ∀ x∈Ioo A B, |iteratedDeriv 4 f x| ≤ L^2/16)
    (hf₁ : ∀ x∈Ioo A₁ B₁, ContDiffAt ℝ 4 f₁ x)
    (hthree₁ : ∀ x∈Ioo A₁ B₁, L ≤ iteratedDeriv 3 f₁ x)
    (hfour₁ : ∀ x∈Ioo A₁ B₁, |iteratedDeriv 4 f₁ x| ≤ L^2/16)
    (hxl : xl∈Ioo A B) (hxr : xr∈Ioo A B)
    (hyl : yl∈Ioo A₁ B₁) (hyr : yr∈Ioo A₁ B₁) :
    let h := fun x => iteratedDeriv 2 f x/2
    let h₁ := fun x => iteratedDeriv 2 f₁ x/2
    let t := fun v => (c:ℝ)*v+d
    h xl ≤ h xr →
    ((a:ℝ)*h xl+b)/t (h xl)=h₁ yl →
    ((a:ℝ)*h xr+b)/t (h xr)=h₁ yr →
    ((1:ℝ)/2 ≤ t (h xl) ∧ t (h xl) ≤ 2) →
    ((1:ℝ)/2 ≤ t (h xr) ∧ t (h xr) ≤ 2) →
    |(iteratedDeriv 3 f₁ yl/6)*t (h xl)^3-iteratedDeriv 3 f xl/6| ≤ E →
    |(iteratedDeriv 3 f₁ yr/6)*t (h xr)^3-iteratedDeriv 3 f xr/6| ≤ E →
    h xr-h xl ≤ 48*E/(|(c:ℝ)| *L) :=
  @TaoTrudgianYang2025.bourgain_paired_C4_nontriangular_resonance_compression f f₁ A B A₁ B₁ L E xl xr yl yr a b c d hdet hc hL hf hthree hfour hf₁ hthree₁ hfour₁ hxl hxr hyl hyr

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.scaled_paired_C4_nontriangular_resonance_compression
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.scaled_paired_C4_block_matrix_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_paired_large_entry_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_paired_long_block_constraint

example
    (f f₁ : ℝ → ℝ) {A B A₁ B₁ L E xl xr yl yr : ℝ}
    (a b c d : ℤ) (hdet : a*d-b*c=1) (hc : c ≠ 0) (hL : 0 < L)
    (hf : ∀ z ∈ Set.Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z ∈ Set.Ioo A B, L ≤ iteratedDeriv 3 f z)
    (hfour : ∀ z ∈ Set.Ioo A B, |iteratedDeriv 4 f z| ≤ |(c:ℝ)| *L^2/16)
    (hf₁ : ∀ z ∈ Set.Ioo A₁ B₁, ContDiffAt ℝ 4 f₁ z)
    (hthree₁ : ∀ z ∈ Set.Ioo A₁ B₁, L ≤ iteratedDeriv 3 f₁ z)
    (hfour₁ : ∀ z ∈ Set.Ioo A₁ B₁, |iteratedDeriv 4 f₁ z| ≤ |(c:ℝ)| *L^2/16)
    (hxl : xl ∈ Set.Ioo A B) (hxr : xr ∈ Set.Ioo A B)
    (hyl : yl ∈ Set.Ioo A₁ B₁) (hyr : yr ∈ Set.Ioo A₁ B₁) :
    let h := fun z => iteratedDeriv 2 f z/2
    let h₁ := fun z => iteratedDeriv 2 f₁ z/2
    let t := fun z => (c:ℝ)*z+d
    h xl ≤ h xr →
    ((a:ℝ)*h xl+b)/t (h xl)=h₁ yl →
    ((a:ℝ)*h xr+b)/t (h xr)=h₁ yr →
    ((1:ℝ)/2 ≤ t (h xl) ∧ t (h xl) ≤ 2) →
    ((1:ℝ)/2 ≤ t (h xr) ∧ t (h xr) ≤ 2) →
    |(iteratedDeriv 3 f₁ yl/6)*t (h xl)^3-iteratedDeriv 3 f xl/6| ≤ E →
    |(iteratedDeriv 3 f₁ yr/6)*t (h xr)^3-iteratedDeriv 3 f xr/6| ≤ E →
    h xr-h xl ≤ 48*E/(|(c:ℝ)| *L) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.scaled_paired_C4_nontriangular_resonance_compression f f₁ A B A₁ B₁ L E xl xr yl yr a b c d hdet hc hL hf hthree hfour hf₁ hthree₁ hfour₁ hxl hxr hyl hyr

example
    (S : Finset ℤ) (f f₁ : ℝ → ℝ) (x y : ℤ → ℝ)
    {A B A₁ B₁ L E N Z : ℝ} (a b c d : ℤ)
    (hdet : a*d-b*c=1) (hc : c ≠ 0) (hL : 0 < L) (hE : 0 ≤ E) (hN : 0 < N)
    (hf : ∀ z ∈ Set.Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z ∈ Set.Ioo A B, L ≤ iteratedDeriv 3 f z)
    (hfour : ∀ z ∈ Set.Ioo A B, |iteratedDeriv 4 f z| ≤ |(c:ℝ)| *L^2/16)
    (hf₁ : ∀ z ∈ Set.Ioo A₁ B₁, ContDiffAt ℝ 4 f₁ z)
    (hthree₁ : ∀ z ∈ Set.Ioo A₁ B₁, L ≤ iteratedDeriv 3 f₁ z)
    (hfour₁ : ∀ z ∈ Set.Ioo A₁ B₁, |iteratedDeriv 4 f₁ z| ≤ |(c:ℝ)| *L^2/16)
    (hx : ∀ k ∈ S, x k ∈ Set.Ioo A B) (hy : ∀ k ∈ S, y k ∈ Set.Ioo A₁ B₁)
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ x k ∧ x k ≤ Z+((k:ℝ)+1)*N) :
    let h := fun z => iteratedDeriv 2 f z/2
    let h₁ := fun z => iteratedDeriv 2 f₁ z/2
    let t := fun z => (c:ℝ)*z+d
    (∀ k ∈ S, ((a:ℝ)*h (x k)+b)/t (h (x k))=h₁ (y k)) →
    (∀ k ∈ S, (1:ℝ)/2 ≤ t (h (x k)) ∧ t (h (x k)) ≤ 2) →
    (∀ k ∈ S, |(iteratedDeriv 3 f₁ (y k)/6)*(t (h (x k)))^3-
      iteratedDeriv 3 f (x k)/6| ≤ E) →
    (S.card:ℝ) ≤ 2+96*E/(|(c:ℝ)| *L^2*N) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.scaled_paired_C4_block_matrix_count S f f₁ x y A B A₁ B₁ L E N Z a b c d hdet hc hL hE hN hf hthree hfour hf₁ hthree₁ hfour₁ hx hy hwindow

example
    (S : Finset ℤ) (x y : ℤ → ℝ) (a b c d : ℤ)
    {σ δ T M Δ N R Z : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T) (hM : 0 < M) (hN : 0 < N)
    (hphase : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hΔ : 0 ≤ Δ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hscale : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(c:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hx : ∀ p ∈ S, x p ∈ Set.Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ p ∈ S, y p ∈ Set.Ioo (1/2:ℝ) (W 1-1/2))
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ x k ∧ x k ≤ Z+((k:ℝ)+1)*N) :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let μ := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun p : ℤ => (c:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+d
    (∀ p ∈ S, ((a:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+b)/t p=
      iteratedDeriv 2 (f 1) (y p)/2) →
    (∀ p ∈ S, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p ∈ S, |μ 1 (y p)*(t p)^3/μ 0 (x p)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (S.card:ℝ) ≤ 2+32*(σ*(σ+1)+1)*(Γ^2*Δ+2*Γ*η)*R^2/(κ^2*|(c:ℝ)|) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_paired_large_entry_block_count S x y a b c d σ δ T M Δ N R Z τ A W F hσ hδ hδ0 hF hT hτ hM hN hphase hA hW hΔ hdet hc hscale hx hy hwindow

example
    (S : Finset ℤ) (x y : ℤ → ℝ) (a b c d : ℤ)
    {σ δ T M D ℓ N R Z : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T) (hM : 0 < M) (hN : 0 < N)
    (hphase : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hD : 0 ≤ D) (hℓ : 4 ≤ ℓ) (hR : 1 ≤ R)
    (hcut : (ℓ*N)^2 ≤ M*R^2) (hcard : ℓ ≤ (S.card:ℝ)) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*N*R^2 ≤ |(c:ℝ)| *(modelPhaseThirdLower σ)^2*M)
    (hx : ∀ p ∈ S, x p ∈ Set.Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ p ∈ S, y p ∈ Set.Ioo (1/2:ℝ) (W 1-1/2))
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ x k ∧ x k ≤ Z+((k:ℝ)+1)*N) :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let μ := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun p : ℤ => (c:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+d
    (∀ p ∈ S, ((a:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+b)/t p=
      iteratedDeriv 2 (f 1) (y p)/2) →
    (∀ p ∈ S, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p ∈ S, |μ 1 (y p)*(t p)^3/μ 0 (x p)-1| ≤ D*R^2/(ℓ^2*N^2)) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    κ^2*|(c:ℝ)| *ℓ^3*N^2 ≤
      64*(σ*(σ+1)+1)*(Γ^2*D+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_paired_long_block_constraint S x y a b c d σ δ T M D ℓ N R Z τ A W F hσ hδ hδ0 hF hT hτ hM hN hphase hA hW hD hℓ hR hcut hcard hdet hc hlarge hx hy hwindow


open Filter
open scoped Topology

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_hasDerivAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_vertical_profile_hasDerivAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_parameter_compression
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_parameter_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_constructed_parameter_count

example
    (H : ℝ → ℝ → ℝ) (ρ : ℝ → ℝ) {z hy hx : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I) (hx0 : hx ≠ 0)
    (hH : HasStrictFDerivAt (fun p : ℝ × ℝ => H p.1 p.2)
      (hy • ContinuousLinearMap.fst ℝ ℝ ℝ + hx • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (z,ρ z))
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H w (ρ w)=H z (ρ z))
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (H w) I) :
    HasDerivAt ρ (-hy/hx) z :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_hasDerivAt H ρ z hy hx I hI hbase hx0 hH hroot huniq

example
    (H : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ) {z : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 2 H (z,ρ z))
    (hx0 : fderiv ℝ H (z,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w,ρ w)=H (z,ρ z))
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun u => H (w,u)) I) :
    let G := fun p => fderiv ℝ H p (0,1)
    let B := fun p => fderiv ℝ H p (1,0)
    HasDerivAt (fun w => G (w,ρ w))
      (G (z,ρ z)*deriv (fun u => B (z,u)/G (z,u)) (ρ z)) z :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_vertical_profile_hasDerivAt H ρ z I hI hbase hH hx0 hroot huniq

example
    (H : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ)
    {a b A B s t q L K E : ℝ}
    (hL : 0 < L) (hK : 0 < K) (hst : s ≤ t)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hH : ∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, ContDiffAt ℝ 2 H (y,x))
    (hroot : ∀ y ∈ Set.Ioo a b, ρ y ∈ Set.Ioo A B ∧ H (y,ρ y)=q) :
    let G := fun p => fderiv ℝ H p (0,1)
    let Z := fun p => fderiv ℝ H p (1,0)
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, L ≤ |G (y,x)|) →
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B,
      K ≤ |deriv (fun u => Z (y,u)/G (y,u)) x|) →
    |G (t,ρ t)-G (s,ρ s)| ≤ E →
    t-s ≤ E/(L*K) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_parameter_compression H ρ a b A B s t q L K E hL hK hst hs ht hH hroot

example
    (S : Finset ℝ) (H : ℝ × ℝ → ℝ) (ρ : ℝ → ℝ)
    {a b A B q L K E J g : ℝ}
    (hL : 0 < L) (hK : 0 < K) (hE : 0 ≤ E) (hJ : 0 < J)
    (hS : ∀ y ∈ S, y ∈ Set.Ioo a b)
    (hsep : ∀ y ∈ S, ∀ w ∈ S, y ≠ w → 1 ≤ J*|y-w|)
    (hH : ∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, ContDiffAt ℝ 2 H (y,x))
    (hroot : ∀ y ∈ Set.Ioo a b, ρ y ∈ Set.Ioo A B ∧ H (y,ρ y)=q) :
    let G := fun p => fderiv ℝ H p (0,1)
    let Z := fun p => fderiv ℝ H p (1,0)
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, L ≤ |G (y,x)|) →
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B,
      K ≤ |deriv (fun u => Z (y,u)/G (y,u)) x|) →
    (∀ y ∈ S, |G (y,ρ y)-g| ≤ E) →
    (S.card:ℝ) ≤ 1+2*E*J/(L*K) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_parameter_count S H ρ a b A B q L K E J g hL hK hE hJ hS hsep hH hroot

example
    (S : Finset ℝ) (H : ℝ × ℝ → ℝ)
    {a b A B A₀ B₀ q L K Δ J g : ℝ}
    (hL : 0 < L) (hK : 0 < K) (hΔ : 0 ≤ Δ) (hJ : 0 < J) (hg : g ≠ 0)
    (hAB : A₀ ≤ B₀) (hA₀ : A < A₀) (hB₀ : B₀ < B)
    (hS : ∀ y ∈ S, y ∈ Set.Ioo a b)
    (hsep : ∀ y ∈ S, ∀ w ∈ S, y ≠ w → 1 ≤ J*|y-w|)
    (hH : ∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, ContDiffAt ℝ 2 H (y,x))
    (hcover : ∀ y ∈ Set.Ioo a b, H (y,A₀) ≤ q ∧ q ≤ H (y,B₀)) :
    let ρ := fun y => Function.invFunOn (fun x => H (y,x)) (Set.Ioo A B) q
    let G := fun p => fderiv ℝ H p (0,1)
    let Z := fun p => fderiv ℝ H p (1,0)
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B, L ≤ |G (y,x)|) →
    (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B,
      K ≤ |deriv (fun u => Z (y,u)/G (y,u)) x|) →
    (∀ y ∈ S, |G (y,ρ y)/g-1| ≤ Δ) →
    (S.card:ℝ) ≤ 1+2*|g| *Δ*J/(L*K) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.curvature_fiber_constructed_parameter_count S H a b A B A₀ B₀ q L K Δ J g hL hK hΔ hJ hg hAB hA₀ hB₀ hS hsep hH hcover


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.difference_logarithmic_ratio_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_difference_mixed_nondegeneracy
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.difference_curvature_mixed_jets
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_difference_curvature_parameter_count

namespace HuxleyActualDifferenceRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open Set Filter
open scoped ContDiff Topology Classical

example
    (f : ℝ → ℝ) {x z η y l c U V : ℝ}
    (hη : 0 < η) (hy : 1 ≤ y) (hy' : y ≤ 2) (hz : z=x+η*y)
    (hl : 0 < l) (hc : 0 < c) (hU : 0 < U) (hV : 0 < V)
    (hf : ∀ w ∈ Set.Icc x z, ContDiffAt ℝ 2 f w)
    (hvalue : ∀ w ∈ Set.Icc x z, l ≤ |f w| ∧ |f w| ≤ V)
    (hder : ∀ w ∈ Set.Icc x z, c ≤ |deriv f w| ∧ |deriv f w| ≤ U)
    (hdet : ∀ w ∈ Set.Icc x z, c ≤ |f w*iteratedDeriv 2 f w-(deriv f w)^2|) :
    f x-f z ≠ 0 ∧ c*(z-x) ≤ |f x-f z| ∧
    l^2*c/(2*U^2*V^2) ≤
      |η*(f z*deriv f x-deriv f z*f x)/(f x-f z)^2| :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.difference_logarithmic_ratio_lower f x z η y l c U V hη hy hy' hz hl hc hU hV hf hvalue hder hdet

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ F : ℝ → ℝ, Expdb.IsApproximateModelPhaseFunction F σ 5 δ →
      ∀ η y x : ℝ, 0 < η → 1 ≤ y → y ≤ 2 →
        x ∈ Set.Ioo (1:ℝ) 2 → x+η*y < 2 →
      ∀ r : ℕ, 3 ≤ r → r ≤ 4 →
        K ≤ |(iteratedDeriv r F x-iteratedDeriv r F (x+η*y))/(σ*η)| ∧
        K ≤ |η*(iteratedDeriv r F (x+η*y)*iteratedDeriv (r+1) F x-
          iteratedDeriv (r+1) F (x+η*y)*iteratedDeriv r F x)/
          (iteratedDeriv r F x-iteratedDeriv r F (x+η*y))^2| :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_difference_mixed_nondegeneracy σ hσ

example
    (f : ℝ → ℝ) {σ η y x : ℝ}
    (hσ : σ ≠ 0) (hη : η ≠ 0)
    (hx : ContDiffAt ℝ 2 f x) (hz : ContDiffAt ℝ 2 f (x+η*y))
    (hd : deriv f x-deriv f (x+η*y) ≠ 0) :
    let H := fun p : ℝ × ℝ => (f p.2-f (p.2+η*p.1))/(σ*η)
    let G := fun p => fderiv ℝ H p (0,1)
    let Z := fun p => fderiv ℝ H p (1,0)
    ContDiffAt ℝ 2 H (y,x) ∧
    G (y,x)=(deriv f x-deriv f (x+η*y))/(σ*η) ∧
    Z (y,x)= -deriv f (x+η*y)/σ ∧
    deriv (fun u => Z (y,u)/G (y,u)) x =
      η*(deriv f (x+η*y)*iteratedDeriv 2 f x-
        iteratedDeriv 2 f (x+η*y)*deriv f x)/
        (deriv f x-deriv f (x+η*y))^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.difference_curvature_mixed_jets f σ η y x hσ hη hx hz hd

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ F : ℝ → ℝ, Expdb.IsApproximateModelPhaseFunction F σ 5 δ →
      ∀ η A B A₀ B₀ q Δ J g : ℝ,
      ∀ S : Finset ℝ,
      0 < η → 1 ≤ A → B+2*η ≤ 2 →
      A₀ ≤ B₀ → A < A₀ → B₀ < B →
      0 ≤ Δ → 0 < J → g ≠ 0 →
      (∀ y ∈ S, y ∈ Set.Ioo (1:ℝ) 2) →
      (∀ y ∈ S, ∀ w ∈ S, y ≠ w → 1 ≤ J*|y-w|) →
      let H := fun p : ℝ × ℝ =>
        (iteratedDeriv 2 F p.2-iteratedDeriv 2 F (p.2+η*p.1))/(σ*η)
      let G := fun p => fderiv ℝ H p (0,1)
      let ρ := fun y => Function.invFunOn (fun x => H (y,x)) (Set.Ioo A B) q
      (∀ y ∈ Set.Ioo (1:ℝ) 2, H (y,A₀) ≤ q ∧ q ≤ H (y,B₀)) →
      (∀ y ∈ S, |G (y,ρ y)/g-1| ≤ Δ) →
      (∀ y ∈ Set.Ioo (1:ℝ) 2, ∀ x ∈ Set.Ioo A B,
        iteratedDeriv 2 (fun u => (F u-F (u+η*y))/(σ*η)) x=H (y,x) ∧
        G (y,x)=(iteratedDeriv 3 F x-iteratedDeriv 3 F (x+η*y))/(σ*η)) ∧
      (S.card:ℝ) ≤ 1+2*|g| *Δ*J/K^2 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_difference_curvature_parameter_count σ hσ

end HuxleyActualDifferenceRegression

#print axioms TaoTrudgianYang2025.HuxleyModel.reference_tests_positive
#print axioms TaoTrudgianYang2025.HuxleyModel.exists_uniform_test_lower_positive_compact
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_buffered_extension_uniform
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.buffered_phase_sharp_sum_comparison
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_sharp_transport
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_source_tests
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_curvature_entry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_difference_parameter_count


namespace HuxleyEnlargedSourceRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase TaoTrudgianYang2025.HuxleyModel
open Set Filter
open scoped ContDiff Topology Classical

example {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) (i : Fin 7) :
    tests (fun j : Fin 4 => iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x) i ≠ 0 :=
  @TaoTrudgianYang2025.HuxleyModel.reference_tests_positive σ x hσ hx i

example
    {σ a b : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ x ∈ Set.Icc a b, ∀ v : Fin 4 → ℝ,
        (∀ j, |v j-iteratedDeriv (j.val+2) (Expdb.modelPhase σ) x| ≤ δ) →
        ∀ j, c ≤ |tests v j| :=
  @TaoTrudgianYang2025.HuxleyModel.exists_uniform_test_lower_positive_compact σ a b hσ ha hab

example (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ δ h : ℝ) (F : ℝ → ℝ),
      0 ≤ δ → 0 < h → h < 1/4 →
      Expdb.IsApproximateModelPhaseFunction F σ (Q+1) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Set.Icc (1+2*h) (2-2*h), Fext x=F x) ∧
        (∀ x ∈ Set.Icc (1/2:ℝ) 3, ∀ n ≤ Q,
          |iteratedDeriv (n+1) Fext x-iteratedDeriv n (Expdb.modelPhase σ) x| ≤ C*δ) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_buffered_extension_uniform Q

example
    (F Fext : ℝ → ℝ) {N h : ℝ} (hN : 0 < N) (hh : 0 < h)
    (hagrees : ∀ x ∈ Set.Icc (1+2*h) (2-2*h), Fext x=F x)
    (T : ℝ) (a b : ℕ) (ha : N ≤ (a:ℝ)) (hb : (b:ℝ) ≤ 2*N) :
    ‖Expdb.exponentialSumAt F T N a b-Expdb.exponentialSumAt Fext T N a b‖ ≤ 16*N*h+4 :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.buffered_phase_sharp_sum_comparison F Fext N h hN hh hagrees T a b ha hb

example (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ δ N : ℝ) (F : ℝ → ℝ),
      0 ≤ δ → 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ (Q+1) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Set.Icc (1/2:ℝ) 3, ∀ n ≤ Q,
          |iteratedDeriv (n+1) Fext x-iteratedDeriv n (Expdb.modelPhase σ) x| ≤ C*δ) ∧
        (∀ (T : ℝ) (a b : ℕ), N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N a b-Expdb.exponentialSumAt Fext T N a b‖ ≤ 6) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_sharp_transport Q

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ c U : ℝ, 0 < δ ∧ 0 < c ∧ 0 < U ∧
      ∀ (N : ℝ) (F : ℝ → ℝ), 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Set.Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ U) ∧
        (∀ x ∈ Set.Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ (T : ℝ) (a b : ℕ), N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N a b-Expdb.exponentialSumAt Fext T N a b‖ ≤ 6) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_source_tests σ hσ

example
    (F : ℝ → ℝ) {σ c U η x y : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Set.Icc (3/4:ℝ) (9/4)) (hy : y ∈ Set.Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Set.Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Set.Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (r : ℕ) (hr : 3 ≤ r) (hr' : r ≤ 4) :
    let H := fun p : ℝ × ℝ =>
      (iteratedDeriv (r-1) F p.2-iteratedDeriv (r-1) F (p.2+η*p.1))/(σ*η)
    let G := fun p => fderiv ℝ H p (0,1)
    let Z := fun p => fderiv ℝ H p (1,0)
    iteratedDeriv (r-1) (fun u => (F u-F (u+η*y))/(σ*η)) x=H (y,x) ∧
    ContDiffAt ℝ 2 H (y,x) ∧
    G (y,x)=(iteratedDeriv r F x-iteratedDeriv r F (x+η*y))/(σ*η) ∧
    c/(2*σ) ≤ |G (y,x)| ∧
    c^2*c/(6*U^4) ≤ |deriv (fun u => Z (y,u)/G (y,u)) x| :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_curvature_entry F σ c U η x y hσ hc hU hη hηmax hx hy hf hbound htests r hr hr'

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ L K : ℝ, 0 < δ ∧ 0 < L ∧ 0 < K ∧
      ∀ (N : ℝ) (F : ℝ → ℝ), 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ (T : ℝ) (a b : ℕ), N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N a b-Expdb.exponentialSumAt Fext T N a b‖ ≤ 6) ∧
        ∀ η a b A B A₀ B₀ q Δ J g : ℝ, ∀ S : Finset ℝ,
        0 < η → η ≤ 1/8 → 1/2 ≤ a → b ≤ 3 → 3/4 ≤ A → B ≤ 9/4 →
        A₀ ≤ B₀ → A < A₀ → B₀ < B → 0 ≤ Δ → 0 < J → g ≠ 0 →
        (∀ y ∈ S, y ∈ Set.Ioo a b) →
        (∀ y ∈ S, ∀ w ∈ S, y ≠ w → 1 ≤ J*|y-w|) →
        let H := fun p : ℝ × ℝ =>
          (iteratedDeriv 2 Fext p.2-iteratedDeriv 2 Fext (p.2+η*p.1))/(σ*η)
        let G := fun p => fderiv ℝ H p (0,1)
        let ρ := fun y => Function.invFunOn (fun x => H (y,x)) (Set.Ioo A B) q
        (∀ y ∈ Set.Ioo a b, H (y,A₀) ≤ q ∧ q ≤ H (y,B₀)) →
        (∀ y ∈ S, |G (y,ρ y)/g-1| ≤ Δ) →
        (∀ y ∈ Set.Ioo a b, ∀ x ∈ Set.Ioo A B,
          iteratedDeriv 2 (fun u => (Fext u-Fext (u+η*y))/(σ*η)) x=H (y,x)) ∧
        (S.card:ℝ) ≤ 1+2*|g| *Δ*J/(L*K) :=
  @TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_difference_parameter_count σ hσ

end HuxleyEnlargedSourceRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_mixed_derivative
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_mixed_upper
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_spatial_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_curvature_directions
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_source_ratio
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_case_one_entry

namespace HuxleyCaseOneSourceRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open Set Filter
open scoped ContDiff Topology Classical

example
    (F : ℝ → ℝ) {σ η x y : ℝ}
    (hσ : σ ≠ 0) (hη : 0 < η) (hx : 0 < x) (hy : 0 < y)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (r s : ℕ) (hs : 0 < s) :
    iteratedDeriv r (fun u => iteratedDeriv s
      (fun v => (F u-F (u+η*v))/(σ*η)) y) x =
      -(η^(s-1)/σ)*iteratedDeriv (r+s) F (x+η*y) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_mixed_derivative F hσ hη hx hy hf r s hs

example
    (F : ℝ → ℝ) {σ U η x y : ℝ}
    (hσ : 0 < σ) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (r s : ℕ) (hs : s ≤ 2) (hrs : r+s ≤ 6) :
    |iteratedDeriv r (fun u => iteratedDeriv s
      (fun v => (F u-F (u+η*v))/(σ*η)) y) x| ≤ 3*U/σ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_mixed_upper F hσ hU hη hηmax hx hy hf hbound r s hs hrs

example
    (F : ℝ → ℝ) {σ c η x y : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (r : ℕ) (hr : 2 ≤ r) (hr' : r ≤ 4) :
    c/(2*σ) ≤ |iteratedDeriv r (fun u => (F u-F (u+η*y))/(σ*η)) x| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_spatial_lower F hσ hc hη hηmax hx hy hf htests r hr hr'

example
    (F : ℝ → ℝ) {σ η x y : ℝ}
    (hx : 0 < x) (hz : 0 < x+η*y)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w) (r : ℕ) :
    let H := fun p : ℝ × ℝ =>
      (iteratedDeriv r F p.2-iteratedDeriv r F (p.2+η*p.1))/(σ*η)
    ContDiffAt ℝ ∞ H (y,x) ∧
    fderiv ℝ H (y,x) (0,1) =
      (iteratedDeriv (r+1) F x-iteratedDeriv (r+1) F (x+η*y))/(σ*η) ∧
    fderiv ℝ H (y,x) (1,0) =
      -η*iteratedDeriv (r+1) F (x+η*y)/(σ*η) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_curvature_directions F (σ:=σ) hx hz hf r

example
    (F : ℝ → ℝ) {σ c U η x y : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (r : ℕ) (hr : 3 ≤ r) (hr' : r ≤ 4) :
    c^2*c/(6*U^4) ≤ |deriv (fun u =>
      iteratedDeriv (r-1) (fun t => deriv (fun v => (F t-F (t+η*v))/(σ*η)) y) u /
      iteratedDeriv r (fun t => (F t-F (t+η*y))/(σ*η)) u) x| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_source_ratio F hσ hc hU hη hηmax hx hy hf hbound htests r hr hr'

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ C₁ C₂ : ℝ, 0 < δ ∧ 1 ≤ C₁ ∧ 0 < C₂ ∧
      ∀ (N : ℝ) (F : ℝ → ℝ), 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ (T : ℝ) (a b : ℕ), N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N a b-Expdb.exponentialSumAt Fext T N a b‖ ≤ 6) ∧
        ∀ η : ℝ, 0 < η → η ≤ 1/8 →
        let P := fun p : ℝ × ℝ => (Fext p.2-Fext (p.2+η*(p.1+1)))/(σ*η)
        ∀ x ∈ Icc (3/4:ℝ) (9/4), ∀ y ∈ Icc (0:ℝ) 1,
        ContDiffAt ℝ ∞ P (y,x) ∧
        (∀ r s : ℕ, 2 ≤ r → s ≤ 2 → r+s ≤ 6 →
          |iteratedDeriv r (fun u => iteratedDeriv s (fun v => P (v,u)) y) x| ≤ C₁) ∧
        (∀ r : ℕ, 2 ≤ r → r ≤ 4 →
          1/C₁ ≤ |iteratedDeriv r (fun u => P (y,u)) x|) ∧
        (∀ r : ℕ, 3 ≤ r → r ≤ 4 →
          C₂ ≤ |deriv (fun u =>
            iteratedDeriv (r-1) (fun t => deriv (fun v => P (v,t)) y) u /
            iteratedDeriv r (fun t => P (y,t)) u) x|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_case_one_entry hσ

end HuxleyCaseOneSourceRegression

#print axioms TaoTrudgianYang2025.HuxleyModel.caseTwoTests
#print axioms TaoTrudgianYang2025.HuxleyModel.caseTwoTests_scaled
#print axioms TaoTrudgianYang2025.HuxleyModel.continuous_caseTwoTests
#print axioms TaoTrudgianYang2025.HuxleyModel.caseTwoTests_uniform_stability
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_jet_small_shift
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_case_two_tests
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_both_cases_entry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.difference_family_dyadic_parameter_geometry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sourceShiftCorrelation_difference_family_sum

namespace HuxleyBothCasesSourceRegression
open TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase TaoTrudgianYang2025.HuxleyModel
open Set Filter Metric
open scoped ContDiff Topology Classical FourierTransform BigOperators

example (v : Fin 4 → ℝ) (y σ : ℝ) :
    caseTwoTests ![-y/σ*v 0,-y/σ*v 1,-y/σ*v 2,-y/σ*v 3,
      -1/σ*v 0,-1/σ*v 1,-1/σ*v 2] =
      ![y^2/σ^2*HuxleyModel.tests v 5,-y^3/σ^4*HuxleyModel.tests v 6] :=
  TaoTrudgianYang2025.HuxleyModel.caseTwoTests_scaled v y σ

example (j : Fin 2) :
    Continuous (fun w : Fin 7 → ℝ => caseTwoTests w j) :=
  TaoTrudgianYang2025.HuxleyModel.continuous_caseTwoTests j

example {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) :
    ∃ ε d : ℝ, 0 < ε ∧ 0 < d ∧
      ∀ (v : Fin 4 → ℝ) (y : ℝ),
      (∀ i, |v i| ≤ U) → c ≤ |HuxleyModel.tests v 5| → c ≤ |HuxleyModel.tests v 6| →
      y ∈ Icc (1:ℝ) 2 → ∀ w : Fin 7 → ℝ,
      (∀ i, |w i- ![-y/σ*v 0,-y/σ*v 1,-y/σ*v 2,-y/σ*v 3,
        -1/σ*v 0,-1/σ*v 1,-1/σ*v 2] i| ≤ ε) →
      ∀ j, d ≤ |caseTwoTests w j| :=
  TaoTrudgianYang2025.HuxleyModel.caseTwoTests_uniform_stability (U:=U) hσ hc

example
    (F : ℝ → ℝ) {σ U η x y : ℝ}
    (hσ : 0 < σ) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (r : ℕ) (hr : r ≤ 5) :
    |iteratedDeriv r (fun u => (F u-F (u+η*y))/(σ*η)) x+
      y/σ*iteratedDeriv (r+1) F x| ≤ 4*U*η/σ ∧
    |iteratedDeriv r (fun u => deriv (fun v => (F u-F (u+η*v))/(σ*η)) y) x+
      1/σ*iteratedDeriv (r+1) F x| ≤ 2*U*η/σ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_jet_small_shift F hσ hU hη hηmax hx hy hf hbound r hr

example {σ c U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ d : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < d ∧
      ∀ F : ℝ → ℝ,
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ x ∈ Icc (3/4:ℝ) (9/4), ∀ y ∈ Icc (1:ℝ) 2,
      let D := fun r => iteratedDeriv r (fun u => (F u-F (u+η*y))/(σ*η)) x
      let B := fun r => iteratedDeriv r
        (fun u => deriv (fun v => (F u-F (u+η*v))/(σ*η)) y) x
      ∀ j, d ≤ |caseTwoTests ![D 2,D 3,D 4,D 5,B 2,B 3,B 4] j| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_jets_difference_case_two_tests hσ hc hU

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ η₀ C₁ C₂ d : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧
      1 ≤ C₁ ∧ 0 < C₂ ∧ 0 < d ∧
      ∀ (N : ℝ) (F : ℝ → ℝ), 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ (T : ℝ) (a b : ℕ), N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N a b-Expdb.exponentialSumAt Fext T N a b‖ ≤ 6) ∧
        ∀ η : ℝ, 0 < η → η ≤ η₀ →
        let P := fun p : ℝ × ℝ => (Fext p.2-Fext (p.2+η*(p.1+1)))/(σ*η)
        ∀ x ∈ Icc (3/4:ℝ) (9/4), ∀ y ∈ Icc (0:ℝ) 1,
        ContDiffAt ℝ ∞ P (y,x) ∧
        (∀ r s : ℕ, 2 ≤ r → s ≤ 2 → r+s ≤ 6 →
          |iteratedDeriv r (fun u => iteratedDeriv s (fun v => P (v,u)) y) x| ≤ C₁) ∧
        (∀ r : ℕ, 2 ≤ r → r ≤ 4 →
          1/C₁ ≤ |iteratedDeriv r (fun u => P (y,u)) x|) ∧
        (∀ r : ℕ, 3 ≤ r → r ≤ 4 →
          C₂ ≤ |deriv (fun u =>
            iteratedDeriv (r-1) (fun t => deriv (fun v => P (v,t)) y) u /
            iteratedDeriv r (fun t => P (y,t)) u) x|) ∧
        (let D := fun r => iteratedDeriv r (fun u => P (y,u)) x
         let B := fun r => iteratedDeriv r (fun u => deriv (fun v => P (v,u)) y) x
         d ≤ |3*(D 3)^2-D 2*D 4| ∧
         d ≤ |Matrix.det ![![3*(D 3)^2+4*D 2*D 4,3*D 2*D 3,(D 2)^2],
           ![D 5,D 4,D 3],![B 4,B 3,B 2]]|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_both_cases_entry hσ

example {H : ℝ} (hH : 0 < H) :
    (∀ r : ℕ, H ≤ (r:ℝ) → (r:ℝ) ≤ 2*H → (r:ℝ)/H-1 ∈ Icc (0:ℝ) 1) ∧
    (∀ r s : ℕ, r ≠ s →
      1 ≤ H*|(r:ℝ)/H-1-((s:ℝ)/H-1)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.difference_family_dyadic_parameter_geometry hH

example
    (F : ℝ → ℝ) {σ T N H : ℝ} (hσ : σ ≠ 0) (hN : N ≠ 0) (hH : H ≠ 0)
    (a L r : ℕ) (hrL : r ≤ L) :
    let P := fun p : ℝ × ℝ => (F p.2-F (p.2+(H/N)*(p.1+1)))/(σ*(H/N))
    sourceShiftCorrelation F T N a L r =
      starRingEnd ℂ (Expdb.exponentialSumAt (fun x => P ((r:ℝ)/H-1,x))
        (σ*T*H/N) N a (a+(L-r))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.sourceShiftCorrelation_difference_family_sum F hσ hN hH a L r hrL

example (w : Fin 7 → ℝ) :
    caseTwoTests w = ![3*(w 1)^2-w 0*w 2,
      Matrix.det ![![3*(w 1)^2+4*w 0*w 2,3*w 0*w 1,(w 0)^2],
        ![w 3,w 2,w 1],![w 6,w 5,w 4]]] := rfl

end HuxleyBothCasesSourceRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_hasFDerivAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_root_hasFDerivAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_hasFDerivAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_jacobian
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_inverse_profile_jacobian_lower

namespace HuxleyInverseProfileRegression

open TaoTrudgianYang2025.HuxleyRationalPhase Filter Set
open scoped Topology ContDiff

example
    (H : (ℝ × ℝ) → ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {hx : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I) (hx0 : hx ≠ 0)
    (hH : HasStrictFDerivAt (fun p : (ℝ × ℝ) × ℝ => H p.1 p.2)
      (L.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+
        hx • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (z,ρ z))
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H w (ρ w)=H z (ρ z))
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (H w) I) :
    HasFDerivAt ρ (-(hx⁻¹ • L)) z :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_hasFDerivAt H ρ hI hbase hx0 hH hroot huniq

example
    (H : ℝ × ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 1 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    HasFDerivAt ρ
      ((-fderiv ℝ H (z.1,ρ z) (1,0)/fderiv ℝ H (z.1,ρ z) (0,1)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        (1/fderiv ℝ H (z.1,ρ z) (0,1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_root_hasFDerivAt H ρ hI hbase hH hx0 hroot huniq

example
    (H : ℝ × ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 2 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let B := fderiv ℝ H p (1,0)
    let K := fderiv ℝ G p (0,1)
    let Z := fderiv ℝ G p (1,0)
    HasFDerivAt (fun w => G (w.1,ρ w))
      ((Z-K*B/G p) • ContinuousLinearMap.fst ℝ ℝ ℝ+
        (K/G p) • ContinuousLinearMap.snd ℝ ℝ ℝ) z :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_hasFDerivAt H ρ hI hbase hH hx0 hroot huniq

example
    (H : ℝ × ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hxx0 : fderiv ℝ (fun v => fderiv ℝ H v (0,1)) (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let q := fun w => fderiv ℝ g w (0,1)
    fderiv ℝ g z (0,1)*fderiv ℝ q z (1,0)-
        fderiv ℝ q z (0,1)*fderiv ℝ g z (1,0) =
      (K p/G p)^2*deriv (fun x => Z (z.1,x)/K (z.1,x)) (ρ z) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_jacobian H ρ hI hbase hH hx0 hxx0 hroot huniq

example
    (F : ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {σ c U η : ℝ} {z : ℝ × ℝ} {I : Set ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : ρ z ∈ Icc (3/4:ℝ) (9/4)) (hy : z.1 ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let G := fun v => fderiv ℝ H v (0,1)
    let g := fun w => G (w.1,ρ w)
    let q := fun w => fderiv ℝ g w (0,1)
    (c/(6*U))^2*(c^2*c/(6*U^4)) ≤
      |fderiv ℝ g z (0,1)*fderiv ℝ q z (1,0)-
        fderiv ℝ q z (0,1)*fderiv ℝ g z (1,0)| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_inverse_profile_jacobian_lower F ρ hσ hc hU hη hηmax hx hy hf hbound htests hI hbase hroot huniq

end HuxleyInverseProfileRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.planar_profile_quantitative_separation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.triangular_profile_interval_compression
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.scalar_surface_contDiffAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_root_contDiffAt
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_profile_compression

namespace HuxleyTriangularProfileRegression

open TaoTrudgianYang2025.HuxleyRationalPhase Filter Set
open scoped Topology ContDiff

example
    (Φ : ℝ × ℝ → ℝ × ℝ) {S : Set (ℝ × ℝ)} {p q : ℝ × ℝ}
    {κ M ε : ℝ} (hM : 0 ≤ M)
    (hsmall : 4*M*ε ≤ κ)
    (hS : Convex ℝ S) (hp : p ∈ S) (hq : q ∈ S)
    (hΦ : ∀ w ∈ S, DifferentiableAt ℝ Φ w)
    (hvar : ∀ w ∈ S, ‖fderiv ℝ Φ w-fderiv ℝ Φ p‖ ≤ ε)
    (hcol₁ : ‖fderiv ℝ Φ p (1,0)‖ ≤ M)
    (hcol₂ : ‖fderiv ℝ Φ p (0,1)‖ ≤ M)
    (hdet : κ ≤ |(fderiv ℝ Φ p (1,0)).1*(fderiv ℝ Φ p (0,1)).2-
      (fderiv ℝ Φ p (0,1)).1*(fderiv ℝ Φ p (1,0)).2|) :
    κ*‖q-p‖ ≤ 4*M*‖Φ q-Φ p‖ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.planar_profile_quantitative_separation Φ hM hsmall hS hp hq hΦ hvar hcol₁ hcol₂ hdet

example
    (f : ℝ × ℝ → ℝ) {S : Set (ℝ × ℝ)}
    {ya yb b l r κ M ε δ : ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M) (hsmall : 4*M*ε ≤ κ)
    (hlr : l < r) (hlen : r-l ≤ 2)
    (hS : Convex ℝ S)
    (hF : ∀ w ∈ S, ContDiffAt ℝ 2 f w)
    (hpoints : ∀ t ∈ Icc l r, (ya,t) ∈ S ∧ (yb,t+b) ∈ S)
    (hnear : ∀ t ∈ Icc l r, |f (yb,t+b)-f (ya,t)| ≤ δ) :
    let Φ := fun w => (f w,fderiv ℝ f w (0,1))
    (∀ p ∈ S, ∀ w ∈ S, ‖fderiv ℝ Φ w-fderiv ℝ Φ p‖ ≤ ε) →
    (∀ p ∈ S, ‖fderiv ℝ Φ p (1,0)‖ ≤ M ∧ ‖fderiv ℝ Φ p (0,1)‖ ≤ M) →
    (∀ p ∈ S, κ ≤ |(fderiv ℝ Φ p (1,0)).1*(fderiv ℝ Φ p (0,1)).2-
      (fderiv ℝ Φ p (0,1)).1*(fderiv ℝ Φ p (1,0)).2|) →
    κ*|b| *(r-l) ≤ 8*M*δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.triangular_profile_interval_compression f hκ hM hsmall hlr hlen hS hF hpoints hnear

example
    (F : (ℝ × ℝ) × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {n : ℕ∞ω} {z : ℝ × ℝ} {I : Set ℝ}
    (hn : n ≠ 0) (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hF : ContDiffAt ℝ n F (z,ρ z))
    (hx : fderiv ℝ F (z,ρ z) ((0,0),1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ F (w,ρ w)=F (z,ρ z))
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => F (w,x)) I) :
    ContDiffAt ℝ n ρ z :=
  TaoTrudgianYang2025.HuxleyRationalPhase.scalar_surface_contDiffAt F ρ hn hI hbase hF hx hroot huniq

example
    (H : ℝ × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {n : ℕ∞ω} {z : ℝ × ℝ} {I : Set ℝ}
    (hn : n ≠ 0) (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ n H (z.1,ρ z))
    (hx : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    ContDiffAt ℝ n ρ z :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_root_contDiffAt H ρ hn hI hbase hH hx hroot huniq

example
    (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {σ c U η ya yb b l r M ε δ : ℝ} {I : Set ℝ} {S : Set (ℝ × ℝ)}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hS : IsOpen S) (hconv : Convex ℝ S)
    (hrange : ∀ w ∈ S, ρ w ∈ Icc (3/4:ℝ) (9/4) ∧ w.1 ∈ Icc (1/2:ℝ) 3)
    (hroot : ∀ w ∈ S, ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ w ∈ S, Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I)
    (hlr : l < r) (hlen : r-l ≤ 2)
    (hpoints : ∀ t ∈ Icc l r, (ya,t) ∈ S ∧ (yb,t+b) ∈ S)
    (hM : 0 ≤ M) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
    4*M*ε ≤ κ →
    (∀ p ∈ S, ∀ w ∈ S, ‖fderiv ℝ Φ w-fderiv ℝ Φ p‖ ≤ ε) →
    (∀ p ∈ S, ‖fderiv ℝ Φ p (1,0)‖ ≤ M ∧ ‖fderiv ℝ Φ p (0,1)‖ ≤ M) →
    (∀ t ∈ Icc l r, |g (yb,t+b)-g (ya,t)| ≤ δ) →
    κ*|b| *(r-l) ≤ 8*M*δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_profile_compression F ρ hσ hc hU hη hηmax hf hbound htests hI hS hconv hrange hroot huniq hlr hlen hpoints hM

end HuxleyTriangularProfileRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_derivative_matrix
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_columns_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_inverse_profile_columns_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_compression_from_variation

namespace HuxleyUniformProfileColumnsRegression

open TaoTrudgianYang2025.HuxleyRationalPhase Filter Set
open scoped Topology ContDiff

example
    (H : ℝ × ℝ → ℝ) (ρ : (ℝ × ℝ) → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let q := fun w => fderiv ℝ g w (0,1)
    fderiv ℝ (fun w => (g w,q w)) z (1,0) =
      (Z p-K p*fderiv ℝ H p (1,0)/G p,
       (fderiv ℝ K p (1,0)*G p-K p*Z p)/G p^2-
        fderiv ℝ H p (1,0)*(fderiv ℝ K p (0,1)*G p-K p^2)/G p^3) ∧
    fderiv ℝ (fun w => (g w,q w)) z (0,1) =
      (K p/G p,(fderiv ℝ K p (0,1)*G p-K p^2)/G p^3) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_derivative_matrix H ρ hI hbase hH hx0 hroot huniq

example
    (H : ℝ × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    |fderiv ℝ H p (1,0)| ≤ R →
    |G p| ≤ R → |K p| ≤ R → |Z p| ≤ R →
    |fderiv ℝ K p (0,1)| ≤ R → |fderiv ℝ K p (1,0)| ≤ R →
    |(G p)⁻¹| ≤ R →
    ‖fderiv ℝ Φ z (1,0)‖ ≤ 4*R^6 ∧ ‖fderiv ℝ Φ z (0,1)‖ ≤ 4*R^6 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_columns_bound H ρ hR hI hbase hH hx0 hroot huniq

example
    (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {σ c U η : ℝ} {z : ℝ × ℝ} {I : Set ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : ρ z ∈ Icc (3/4:ℝ) (9/4)) (hy : z.1 ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    let R := max 1 (max (3*U/σ) (2*σ/c))
    ‖fderiv ℝ Φ z (1,0)‖ ≤ 4*R^6 ∧ ‖fderiv ℝ Φ z (0,1)‖ ≤ 4*R^6 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_inverse_profile_columns_bound F ρ hσ hc hU hη hηmax hx hy hf hbound htests hI hbase hroot huniq

example
    (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {σ c U η ya yb b l r δ : ℝ} {I : Set ℝ} {S : Set (ℝ × ℝ)}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hS : IsOpen S) (hconv : Convex ℝ S)
    (hrange : ∀ w ∈ S, ρ w ∈ Icc (3/4:ℝ) (9/4) ∧ w.1 ∈ Icc (1/2:ℝ) 3)
    (hroot : ∀ w ∈ S, ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ w ∈ S, Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I)
    (hlr : l < r) (hlen : r-l ≤ 2)
    (hpoints : ∀ t ∈ Icc l r, (ya,t) ∈ S ∧ (yb,t+b) ∈ S)
    :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    let R := max 1 (max (3*U/σ) (2*σ/c))
    let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
    (∀ p ∈ S, ∀ w ∈ S, ‖fderiv ℝ Φ w-fderiv ℝ Φ p‖ ≤ κ/(16*R^6)) →
    (∀ t ∈ Icc l r, |g (yb,t+b)-g (ya,t)| ≤ δ) →
    κ*|b| *(r-l) ≤ 32*R^6*δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_compression_from_variation F ρ hσ hc hU hη hηmax hf hbound htests hI hS hconv hrange hroot huniq hlr hlen hpoints

end HuxleyUniformProfileColumnsRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.contDiff_profileDerivativeColumns
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.profileDerivativeColumns_uniform_derivative_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_columns_polynomial
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.profile_columns_uniform_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_profile_jet_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_profile_chart_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_profile_uniform_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_compression_on_small_region
namespace HuxleyUniformProfileVariationRegression

open scoped Topology

open TaoTrudgianYang2025.HuxleyRationalPhase

example : ContDiff ℝ ∞ profileDerivativeColumns :=
  TaoTrudgianYang2025.HuxleyRationalPhase.contDiff_profileDerivativeColumns

example (R : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ w : Fin 7 → ℝ, (∀ i, |w i| ≤ R) →
      ‖fderiv ℝ profileDerivativeColumns w‖ ≤ D :=
  TaoTrudgianYang2025.HuxleyRationalPhase.profileDerivativeColumns_uniform_derivative_bound R

example
    (H : ℝ × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ z))
    (hx0 : fderiv ℝ H (z.1,ρ z) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ z)
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    (fderiv ℝ Φ z (1,0),fderiv ℝ Φ z (0,1)) =
      profileDerivativeColumns ![fderiv ℝ H p (1,0),G p,K p,Z p,
        fderiv ℝ K p (0,1),fderiv ℝ K p (1,0),(G p)⁻¹] :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_profile_columns_polynomial H ρ hI hbase hH hx0 hroot huniq

example (R : ℝ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (Φ : ℝ × ℝ → ℝ × ℝ) (J : ℝ × ℝ → Fin 7 → ℝ)
        (S : Set (ℝ × ℝ)) (p q : ℝ × ℝ) (B : ℝ),
      Convex ℝ S → p ∈ S → q ∈ S →
      (∀ w ∈ S, ∀ i, |J w i| ≤ R) →
      (∀ w ∈ S, DifferentiableAt ℝ J w) →
      (∀ w ∈ S, ‖fderiv ℝ J w‖ ≤ B) →
      (∀ w ∈ S, (fderiv ℝ Φ w (1,0),fderiv ℝ Φ w (0,1))=
        profileDerivativeColumns (J w)) →
      ‖fderiv ℝ Φ q-fderiv ℝ Φ p‖ ≤ 2*D*B*‖q-p‖ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.profile_columns_uniform_variation R

example
    (F : ℝ → ℝ) {σ c U η x y : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let R := max 1 (max (3*U/σ) (2*σ/c))
    DifferentiableAt ℝ (differenceProfileJet F σ η) (y,x) ∧
    (∀ i, |differenceProfileJet F σ η (y,x) i| ≤ R) ∧
    ‖fderiv ℝ (differenceProfileJet F σ η) (y,x)‖ ≤ 2*R^3 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_profile_jet_bound F hσ hc hU hη hηmax hx hy hf hbound htests

example
    (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {σ c U η : ℝ} {z : ℝ × ℝ} {I : Set ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : ρ z ∈ Icc (3/4:ℝ) (9/4)) (hy : z.1 ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hbase : ρ z ∈ I)
    (hroot : ∀ᶠ w in 𝓝 z, ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ᶠ w in 𝓝 z, Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
    let Φ := fun w => (g w,fderiv ℝ g w (0,1))
    let W := fun w => differenceProfileJet F σ η (w.1,ρ w)
    let R := max 1 (max (3*U/σ) (2*σ/c))
    DifferentiableAt ℝ W z ∧ (∀ i, |W z i| ≤ R) ∧
    ‖fderiv ℝ W z‖ ≤ 6*R^5 ∧
    (fderiv ℝ Φ z (1,0),fderiv ℝ Φ z (0,1))=profileDerivativeColumns (W z) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_profile_chart_bound F ρ hσ hc hU hη hηmax hx hy hf hbound htests hI hbase hroot huniq

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ) (η : ℝ) (I : Set ℝ) (S : Set (ℝ × ℝ)),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      IsOpen I → IsOpen S → Convex ℝ S →
      (∀ w ∈ S, ρ w ∈ Icc (3/4:ℝ) (9/4) ∧ w.1 ∈ Icc (1/2:ℝ) 3) →
      (∀ w ∈ S, ρ w ∈ I ∧
        (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2) →
      (∀ w ∈ S, Set.InjOn
        (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let Φ := fun w => (g w,fderiv ℝ g w (0,1))
      ∀ p ∈ S, ∀ q ∈ S, ‖fderiv ℝ Φ q-fderiv ℝ Φ p‖ ≤ L*‖q-p‖ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_profile_uniform_variation hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ d : ℝ, 0 < d ∧
      ∀ (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ) (η : ℝ) (I : Set ℝ) (S : Set (ℝ × ℝ))
        (ya yb b l r δ : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      IsOpen I → IsOpen S → Convex ℝ S →
      (∀ w ∈ S, ρ w ∈ Icc (3/4:ℝ) (9/4) ∧ w.1 ∈ Icc (1/2:ℝ) 3) →
      (∀ w ∈ S, ρ w ∈ I ∧
        (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2) →
      (∀ w ∈ S, Set.InjOn
        (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) →
      (∀ p ∈ S, ∀ q ∈ S, ‖q-p‖ ≤ d) →
      l < r → r-l ≤ 2 →
      (∀ t ∈ Icc l r, (ya,t) ∈ S ∧ (yb,t+b) ∈ S) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let R := max 1 (max (3*U/σ) (2*σ/c))
      let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
      (∀ t ∈ Icc l r, |g (yb,t+b)-g (ya,t)| ≤ δ) →
      κ*|b| *(r-l) ≤ 32*R^6*δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_compression_on_small_region hσ hc hU

end HuxleyUniformProfileVariationRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_uniform_root_chart
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.triangular_profile_endpoint_compression
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_endpoint_compression
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_local_triangular_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_near_triangular_count
namespace HuxleyConstructedTriangularCountRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ : ℝ),
      0 < η → η ≤ 1/8 → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      ∀ w : ℝ × ℝ, ‖w-(y₀,H (y₀,x₀))‖ < r →
        ρ w ∈ Ioo (3/4:ℝ) (9/4) ∧ w.1 ∈ Icc (1/2:ℝ) 3 ∧
        H (w.1,ρ w)=w.2 ∧ Set.InjOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_uniform_root_chart hσ hc hU

example
    (f : ℝ × ℝ → ℝ) {S : Set (ℝ × ℝ)}
    {ya yb b l r κ M ε δ : ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M) (hsmall : 8*M*ε ≤ κ)
    (hlr : l < r) (hlen : r-l ≤ 2)
    (hS : Convex ℝ S)
    (hF : ∀ w ∈ S, ContDiffAt ℝ 2 f w)
    (hpoints : ∀ t ∈ Icc l r, (ya,t) ∈ S ∧ (yb,t+b) ∈ S)
    (hleft : |f (yb,l+b)-f (ya,l)| ≤ δ)
    (hright : |f (yb,r+b)-f (ya,r)| ≤ δ) :
    let Φ := fun w => (f w,fderiv ℝ f w (0,1))
    (∀ p ∈ S, ∀ w ∈ S, ‖fderiv ℝ Φ w-fderiv ℝ Φ p‖ ≤ ε) →
    (∀ p ∈ S, ‖fderiv ℝ Φ p (1,0)‖ ≤ M ∧ ‖fderiv ℝ Φ p (0,1)‖ ≤ M) →
    (∀ p ∈ S, κ ≤ |(fderiv ℝ Φ p (1,0)).1*(fderiv ℝ Φ p (0,1)).2-
      (fderiv ℝ Φ p (0,1)).1*(fderiv ℝ Φ p (1,0)).2|) →
    κ*‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ 16*M*δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.triangular_profile_endpoint_compression f hκ hM hsmall hlr hlen hS hF hpoints hleft hright

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ),
      0 < η → η ≤ 1/8 → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let z₀ := (y₀,H (y₀,x₀))
      let R := max 1 (max (3*U/σ) (2*σ/c))
      let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
      l < r → r-l ≤ 2 →
      (∀ t ∈ Icc l r, ‖((ya,t):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t+b):ℝ × ℝ)-z₀‖ < a) →
      |g (yb,l+b)-g (ya,l)| ≤ δ → |g (yb,r+b)-g (ya,r)| ≤ δ →
      κ*‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ 64*R^6*δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_endpoint_compression hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b δ J : ℝ) (S : Finset ℝ),
      0 < η → η ≤ 1/8 → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 < J → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ J*|s-t|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let z₀ := (y₀,H (y₀,x₀))
      let R := max 1 (max (3*U/σ) (2*σ/c))
      let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
      (∀ t ∈ S, ‖((ya,t):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t+b):ℝ × ℝ)-z₀‖ < a) →
      (∀ t ∈ S, |g (yb,t+b)-g (ya,t)| ≤ δ) →
      (S.card:ℝ) ≤ 1+64*R^6*δ*J/(κ*‖((yb-ya,b):ℝ × ℝ)‖) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_local_triangular_count hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ e K : ℝ, 0 < e ∧ 0 < K ∧
      ∀ (F : ℝ → ℝ) (η ya yb b δ J : ℝ) (S : Finset ℝ),
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 < J → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 →
      ‖((yb-ya,b):ℝ × ℝ)‖ < e →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ J*|s-t|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let R := max 1 (max (3*U/σ) (2*σ/c))
      let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
      (∀ t ∈ S, ∃ x ∈ Icc (1:ℝ) 2, H (ya,x)=t) →
      (∀ t ∈ S, |g (yb,t+b)-g (ya,t)| ≤ δ) →
      (S.card:ℝ) ≤ K*(1+64*R^6*δ*J/(κ*‖((yb-ya,b):ℝ × ℝ)‖)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_near_triangular_count hσ hc hU

end HuxleyConstructedTriangularCountRegression

private theorem interval_abs_derivative_lower
    (f f' : ℝ → ℝ) {a b x y L : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hlower : ∀ t ∈ Icc a b, L ≤ |f' t|) :
    L*|y-x| ≤ |f y-f x| := by
  have hordered s t (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      L*(t-s) ≤ |f t-f s| := by
    rcases hst.eq_or_lt with he | hlt
    · subst t
      simp
    have hsub : Icc s t ⊆ Icc a b := fun v hv => ⟨hs.1.trans hv.1,hv.2.trans ht.2⟩
    obtain ⟨v,hv,he⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun w hw => (hd w (hsub hw)).continuousAt.continuousWithinAt)
      (fun w hw => hd w (hsub ⟨hw.1.le,hw.2.le⟩))
    have hb := hlower v (hsub ⟨hv.1.le,hv.2.le⟩)
    rw [he,abs_div,abs_of_pos (sub_pos.mpr hlt)] at hb
    exact (le_div_iff₀ (sub_pos.mpr hlt)).mp hb
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hordered x y hx hy hxy
  · rw [abs_sub_comm y x,abs_sub_comm (f y) (f x)]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hyx)] using hordered y x hy hx hyx

#print axioms interval_abs_derivative_lower

namespace HuxleyAllTranslationsCountRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example
    (F : ℝ → ℝ) {σ c U η x y u : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Ioo (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hroot : (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*y))/(σ*η)=u) :
    Function.invFunOn
      (fun t => (iteratedDeriv 2 F t-iteratedDeriv 2 F (t+η*y))/(σ*η))
      (Ioo (3/4:ℝ) (9/4)) u=x :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_curvature_inverse_eq F hσ hc hU hη hηmax hx hy hf hbound htests hroot

example
    (F : ℝ → ℝ) {σ c U η xa xb ya yb : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hxa : xa ∈ Icc (1:ℝ) 2) (hxb : xb ∈ Icc (1:ℝ) 2)
    (hya : ya ∈ Icc (1:ℝ) 2) (hyb : yb ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let G := fun v : ℝ × ℝ =>
      (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
    let R := max 1 (max (3*U/σ) (2*σ/c))
    |H (yb,xb)-H (ya,xa)| ≤
      R^2*|G (yb,xb)-G (ya,xa)|+(R^3+R)*|yb-ya| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_curvature_translation_bound F hσ hc hU hη hηmax hxa hxb hya hyb hf hbound htests

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb b δ J : ℝ) (S : Finset ℝ) (xa xb : ℝ → ℝ),
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 < J → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ J*|s-t|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      (∀ t ∈ S, xa t ∈ Icc (1:ℝ) 2 ∧ xb t ∈ Icc (1:ℝ) 2 ∧
        H (ya,xa t)=t ∧ H (yb,xb t)=t+b) →
      (∀ t ∈ S, |G (yb,xb t)-G (ya,xa t)| ≤ δ) →
      (S.card:ℝ) ≤ C*(1+δ*J/‖((yb-ya,b):ℝ × ℝ)‖) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_count hσ hc hU

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c U a C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < U ∧ 0 < a ∧ 0 < C ∧
      ∀ (N : ℝ) (F : ℝ → ℝ), 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ 7 ε →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ U) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ (T : ℝ) (m n : ℕ), N ≤ (m:ℝ) → (n:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N m n-Expdb.exponentialSumAt Fext T N m n‖ ≤ 6) ∧
        (∀ (η ya yb b δ J : ℝ) (S : Finset ℝ) (xa xb : ℝ → ℝ),
          0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
          0 < J → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
          (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ J*|s-t|) →
          let H := fun v : ℝ × ℝ =>
            (iteratedDeriv 2 Fext v.2-iteratedDeriv 2 Fext (v.2+η*v.1))/(σ*η)
          let G := fun v : ℝ × ℝ =>
            (iteratedDeriv 3 Fext v.2-iteratedDeriv 3 Fext (v.2+η*v.1))/(σ*η)
          (∀ t ∈ S, xa t ∈ Icc (1:ℝ) 2 ∧ xb t ∈ Icc (1:ℝ) 2 ∧
            H (ya,xa t)=t ∧ H (yb,xb t)=t+b) →
          (∀ t ∈ S, |G (yb,xb t)-G (ya,xa t)| ≤ δ) →
          (S.card:ℝ) ≤ C*(1+δ*J/‖((yb-ya,b):ℝ × ℝ)‖)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_triangular_count hσ

end HuxleyAllTranslationsCountRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_curvature_inverse_eq
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_curvature_translation_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_triangular_count


namespace HuxleyPhysicalTriangularCountRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb b δ w Z : ℝ) (S : Finset ℤ) (xa xb : ℤ → ℝ),
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < w → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
      (∀ k ∈ S, Z+(k:ℝ)*w ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*w) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      (∀ k ∈ S, xa k ∈ Icc (1:ℝ) 2 ∧ xb k ∈ Icc (1:ℝ) 2 ∧
        H (yb,xb k)=H (ya,xa k)+b) →
      (∀ k ∈ S, |G (yb,xb k)-G (ya,xa k)| ≤ δ) →
      (S.card:ℝ) ≤ C*(1+(2*σ/c)*δ/(w*‖((yb-ya,b):ℝ × ℝ)‖)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_block_count hσ hc hU

example
    (F : ℝ → ℝ) {σ η y T M x : ℝ} (hM : 0 < M) (hx : 0 < x)
    (hshift : 0 ≤ η*y) (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z) (n : ℕ) :
    iteratedDeriv n (fun z => T*(F (z/M)-F (z/M+η*y))/(σ*η)) x =
      T/M^n*((iteratedDeriv n F (x/M)-iteratedDeriv n F (x/M+η*y))/(σ*η)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_iteratedDeriv F hM hx hshift hf n

example
    (F : ℝ → ℝ) {σ c U η M xa xb ya yb Δ : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hM : 2 ≤ M) (hxa : xa ∈ Icc (1:ℝ) 2) (hxb : xb ∈ Icc (1:ℝ) 2)
    (hya : ya ∈ Icc (1:ℝ) 2) (hyb : yb ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hΔ : 0 ≤ Δ) :
    let G := fun v : ℝ × ℝ =>
      (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
    let R := max 1 (max (3*U/σ) (2*σ/c))
    |G (yb,(round (M*xb):ℝ)/M)/G (ya,(round (M*xa):ℝ)/M)-1| ≤ Δ →
    |G (yb,xb)-G (ya,xa)| ≤ R*(Δ+1/M) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rounded_third_bound F hσ hc hU hη hηmax hM hxa hxb hya hyb hf hbound htests hΔ

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb b Δ T M N Z : ℝ)
        (S : Finset ℤ) (xa xb : ℤ → ℝ),
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ →
      ((yb-ya,2*M^2*b/T):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
      (∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) →
      (∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M)) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ k ∈ S, iteratedDeriv 2 (f yb) (xb k)/2=
        iteratedDeriv 2 (f ya) (xa k)/2+b) →
      (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)-1| ≤ Δ) →
      let R := max 1 (max (3*U/σ) (2*σ/c))
      (S.card:ℝ) ≤ C*(1+(2*σ/c)*R*(Δ+1/M)*M/
        (N*‖((yb-ya,2*M^2*b/T):ℝ × ℝ)‖)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_triangular_block_count hσ hc hU

example
    (S : Finset ℤ) (x : ℤ → ℝ) {M N Z : ℝ} (hM : 0 ≤ M) (hN : 0 < N)
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ x k ∧ x k ≤ Z+((k:ℝ)+1)*N)
    (hpoints : ∀ k ∈ S, x k ∈ Icc M (2*M)) :
    (S.card:ℝ) ≤ 2+M/N :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physical_interval_block_count S x hM hN hwindow hpoints

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c U a C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < U ∧ 0 < a ∧ 0 < C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 2 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ 7 ε →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ U) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        (∀ (η ya yb b Δ T N Z : ℝ) (S : Finset ℤ) (xa xb : ℤ → ℝ),
          0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
          0 < T → 0 < N → 0 ≤ Δ → |yb-ya| < a →
          (∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) →
          (∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M)) →
          let f := fun y z => T*(Fext (z/M)-Fext (z/M+η*y))/(σ*η)
          let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
          (∀ k ∈ S, iteratedDeriv 2 (f yb) (xb k)/2=
            iteratedDeriv 2 (f ya) (xa k)/2+b) →
          (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)-1| ≤ Δ) →
          let R := max 1 (max (3*U/σ) (2*σ/c))
          let d : ℝ × ℝ := (yb-ya,2*M^2*b/T)
          (S.card:ℝ) ≤ if d=0 then 2+M/N else
            C*(1+(2*σ/c)*R*(Δ+1/M)*M/(N*‖d‖))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_physical_triangular_count hσ

end HuxleyPhysicalTriangularCountRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_triangular_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_iteratedDeriv
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rounded_third_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_triangular_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physical_interval_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_physical_triangular_count


namespace HuxleyReciprocalProfileRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C K : ℝ, 0 < a ∧ 0 < C ∧ 0 < K ∧
      ∀ (F : ℝ → ℝ) (η ya yb b D ℓ T M N R Z : ℝ)
        (S : Finset ℤ) (xa xb : ℤ → ℝ),
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ D → 2*C ≤ ℓ → b ≠ 0 →
      T*N*R^2=M^3 → (ℓ*N)^2 ≤ M*R^2 → ℓ ≤ (S.card:ℝ) →
      |yb-ya| < a →
      (∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) →
      (∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M)) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ k ∈ S, iteratedDeriv 2 (f yb) (xb k)/2=
        iteratedDeriv 2 (f ya) (xa k)/2+b) →
      (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)-1| ≤ D*R^2/(ℓ^2*N^2)) →
      |b| *ℓ^3*N^4 ≤ K*(D+1)*M^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_upper_long_block_constraint hσ hc hU

example
    (H G K L B Z T : ℝ) (hH : H ≠ 0) (hG : G ≠ 0) :
    let gy := Z-K*B/G
    let gt := K/G
    let gtt := (L*G-K^2)/G^3
    let gty := (T*G-K*Z)/G^2-B*(L*G-K^2)/G^3
    (gy/H^3)*(6*G/H-4*gt+H*gtt)-
      (3*G/H^2-gt/H)*(3*gy/H^2-gty/H) =
      TaoTrudgianYang2025.HuxleyModel.caseTwoTests ![H,G,K,L,B,Z,T] 1/(H^4*G^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_profile_case_two_jacobian_identity H G K L B Z T hH hG

example
    (g : ℝ × ℝ → ℝ) {z : ℝ × ℝ} (hz : z.2 ≠ 0)
    (hg : ContDiffAt ℝ 2 g (z.1,z.2⁻¹)) :
    let p := (z.1,z.2⁻¹)
    let q := fun w => fderiv ℝ g w (0,1)
    let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
    let Φ := fun w => (k w,fderiv ℝ k w (0,1))
    fderiv ℝ Φ z (1,0)=
      (z.2^3*fderiv ℝ g p (1,0),
        3*z.2^2*fderiv ℝ g p (1,0)-z.2*fderiv ℝ q p (1,0)) ∧
    fderiv ℝ Φ z (0,1)=
      (3*z.2^2*g p-z.2*q p,
        6*z.2*g p-4*q p+fderiv ℝ q p (0,1)/z.2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_profile_derivative_matrix g hz hg

example
    (H : ℝ × ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {z : ℝ × ℝ} {I : Set ℝ} (hz : z.2 ≠ 0)
    (hI : IsOpen I) (hbase : ρ (z.1,z.2⁻¹) ∈ I)
    (hH : ContDiffAt ℝ 3 H (z.1,ρ (z.1,z.2⁻¹)))
    (hx0 : fderiv ℝ H (z.1,ρ (z.1,z.2⁻¹)) (0,1) ≠ 0)
    (hroot : ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), ρ w ∈ I ∧ H (w.1,ρ w)=w.2)
    (huniq : ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), Set.InjOn (fun x => H (w.1,x)) I) :
    let p := (z.1,ρ (z.1,z.2⁻¹))
    let G := fun v => fderiv ℝ H v (0,1)
    let K := fun v => fderiv ℝ G v (0,1)
    let Z := fun v => fderiv ℝ G v (1,0)
    let g := fun w => G (w.1,ρ w)
    let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
    let Φ := fun w => (k w,fderiv ℝ k w (0,1))
    (fderiv ℝ Φ z (1,0)).1*(fderiv ℝ Φ z (0,1)).2-
      (fderiv ℝ Φ z (0,1)).1*(fderiv ℝ Φ z (1,0)).2 =
      TaoTrudgianYang2025.HuxleyModel.caseTwoTests
        ![H p,G p,K p,fderiv ℝ K p (0,1),
          fderiv ℝ H p (1,0),Z p,fderiv ℝ K p (1,0)] 1/
        ((H p)^4*(G p)^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_reciprocal_profile_jacobian H ρ hz hI hbase hH hx0 hroot huniq

end HuxleyReciprocalProfileRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_upper_long_block_constraint
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_profile_case_two_jacobian_identity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_profile_derivative_matrix
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_surface_reciprocal_profile_jacobian

namespace HuxleyConstructedReciprocalRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ κ : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < κ ∧
      ∀ (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ) (η : ℝ)
        (z : ℝ × ℝ) (I : Set ℝ),
      0 < η → η ≤ η₀ → z.2 ≠ 0 →
      ρ (z.1,z.2⁻¹) ∈ Icc (3/4:ℝ) (9/4) → z.1 ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      IsOpen I → ρ (z.1,z.2⁻¹) ∈ I →
      (∀ᶠ w in 𝓝 (z.1,z.2⁻¹), ρ w ∈ I ∧
        (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2) →
      (∀ᶠ w in 𝓝 (z.1,z.2⁻¹), Set.InjOn
        (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      let Φ := fun w => (k w,fderiv ℝ k w (0,1))
      κ ≤ |(fderiv ℝ Φ z (1,0)).1*(fderiv ℝ Φ z (0,1)).2-
        (fderiv ℝ Φ z (0,1)).1*(fderiv ℝ Φ z (1,0)).2| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_profile_jacobian_lower hσ hc hU

example {A a u : ℝ}
    (hA : 0 < A) (ha : a ≠ 0) (haA : |a| ≤ A)
    (hu : |u-a⁻¹| < 1/(2*A)) :
    u ≠ 0 ∧ |u⁻¹-a| ≤ 2*A^2*|u-a⁻¹| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_coordinate_local_bound hA ha haA hu

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ s : ℝ, 0 < s ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ : ℝ),
      0 < η → η ≤ 1/8 → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      ∀ w : ℝ × ℝ, ‖w-(y₀,(H (y₀,x₀))⁻¹)‖ < s →
        w.2 ≠ 0 ∧ ρ (w.1,w.2⁻¹) ∈ Ioo (3/4:ℝ) (9/4) ∧
        w.1 ∈ Icc (1/2:ℝ) 3 ∧ H (w.1,ρ (w.1,w.2⁻¹))=w.2⁻¹ ∧
        (∀ᶠ v in 𝓝 (w.1,w.2⁻¹), ρ v ∈ Ioo (3/4:ℝ) (9/4) ∧
          H (v.1,ρ v)=v.2) ∧
        (∀ᶠ v in 𝓝 (w.1,w.2⁻¹), Set.InjOn
          (fun x => H (v.1,x)) (Ioo (3/4:ℝ) (9/4))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_uniform_reciprocal_root_chart hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ κ s : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < κ ∧ 0 < s ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ : ℝ),
      0 < η → η ≤ η₀ → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      let Φ := fun w => (k w,fderiv ℝ k w (0,1))
      ∀ z : ℝ × ℝ, ‖z-(y₀,(H (y₀,x₀))⁻¹)‖ < s →
        z.1 ∈ Icc (1:ℝ) 2 →
        ContDiffAt ℝ 2 k z ∧
        κ ≤ |(fderiv ℝ Φ z (1,0)).1*(fderiv ℝ Φ z (0,1)).2-
          (fderiv ℝ Φ z (0,1)).1*(fderiv ℝ Φ z (1,0)).2| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_reciprocal_profile hσ hc hU

end HuxleyConstructedReciprocalRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_profile_jacobian_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.reciprocal_coordinate_local_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_uniform_reciprocal_root_chart
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_reciprocal_profile

namespace HuxleyReciprocalCountRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example : ContDiff ℝ ∞ reciprocalProfileColumns :=
  TaoTrudgianYang2025.HuxleyRationalPhase.contDiff_reciprocalProfileColumns

example (R : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ v : (Fin 7 → ℝ) × ℝ × ℝ, ‖v‖ ≤ R →
      ‖reciprocalProfileColumns v‖ ≤ D ∧
      ‖fderiv ℝ reciprocalProfileColumns v‖ ≤ D :=
  TaoTrudgianYang2025.HuxleyRationalPhase.reciprocalProfileColumns_uniform_bound R

example
    (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ)
    {σ c U η : ℝ} {z : ℝ × ℝ} {I : Set ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hz : z.2 ≠ 0)
    (hx : ρ (z.1,z.2⁻¹) ∈ Icc (3/4:ℝ) (9/4)) (hy : z.1 ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hI : IsOpen I) (hbase : ρ (z.1,z.2⁻¹) ∈ I)
    (hroot : ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), ρ w ∈ I ∧
      (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2)
    (huniq : ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), Set.InjOn
      (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
    let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
    let Φ := fun w => (k w,fderiv ℝ k w (0,1))
    let W := fun w => differenceProfileJet F σ η (w.1,ρ w)
    let V := fun w : ℝ × ℝ => (W (w.1,w.2⁻¹),w.2,w.2⁻¹)
    let R := max 1 (max (3*U/σ) (2*σ/c))
    DifferentiableAt ℝ V z ∧ ‖V z‖ ≤ R ∧
    ‖fderiv ℝ V z‖ ≤ 6*R^7 ∧
    (fderiv ℝ Φ z (1,0),fderiv ℝ Φ z (0,1))=reciprocalProfileColumns (V z) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_profile_chart_bound F ρ hσ hc hU hη hηmax hz hx hy hf hbound htests hI hbase hroot huniq

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ D L : ℝ, 0 < D ∧ 0 < L ∧
      ∀ (F : ℝ → ℝ) (ρ : ℝ × ℝ → ℝ) (η : ℝ)
        (I : Set ℝ) (S : Set (ℝ × ℝ)),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      IsOpen I → Convex ℝ S →
      (∀ w ∈ S, w.2 ≠ 0 ∧ ρ (w.1,w.2⁻¹) ∈ Icc (3/4:ℝ) (9/4) ∧
        w.1 ∈ Icc (1/2:ℝ) 3) →
      (∀ z ∈ S, ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), ρ w ∈ I ∧
        (iteratedDeriv 2 F (ρ w)-iteratedDeriv 2 F (ρ w+η*w.1))/(σ*η)=w.2) →
      (∀ z ∈ S, ∀ᶠ w in 𝓝 (z.1,z.2⁻¹), Set.InjOn
        (fun x => (iteratedDeriv 2 F x-iteratedDeriv 2 F (x+η*w.1))/(σ*η)) I) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      let Φ := fun w => (k w,fderiv ℝ k w (0,1))
      (∀ w ∈ S, ‖fderiv ℝ Φ w (1,0)‖ ≤ D ∧ ‖fderiv ℝ Φ w (0,1)‖ ≤ D) ∧
      ∀ p ∈ S, ∀ q ∈ S, ‖fderiv ℝ Φ q-fderiv ℝ Φ p‖ ≤ L*‖q-p‖ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_profile_uniform_variation hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ),
      0 < η → η ≤ η₀ → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      let z₀ := (y₀,(H (y₀,x₀))⁻¹)
      l < r → r-l ≤ 2 →
      (∀ t ∈ Icc l r, ‖((ya,t):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t+b):ℝ × ℝ)-z₀‖ < a) →
      |k (yb,l+b)-k (ya,l)| ≤ δ → |k (yb,r+b)-k (ya,r)| ≤ δ →
      ‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ C*δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_reciprocal_endpoint_compression hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b δ J : ℝ) (S : Finset ℝ),
      0 < η → η ≤ η₀ → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 < J → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ J*|s-t|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      let z₀ := (y₀,(H (y₀,x₀))⁻¹)
      (∀ t ∈ S, ‖((ya,t):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t+b):ℝ × ℝ)-z₀‖ < a) →
      (∀ t ∈ S, |k (yb,t+b)-k (ya,t)| ≤ δ) →
      (S.card:ℝ) ≤ 1+C*δ*J/‖((yb-ya,b):ℝ × ℝ)‖ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_local_reciprocal_count hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ e K C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < e ∧ 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb b δ J : ℝ) (S : Finset ℝ),
      0 < η → η ≤ η₀ → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 < J → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 →
      ‖((yb-ya,b):ℝ × ℝ)‖ < e →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ J*|s-t|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let ρ := fun w : ℝ × ℝ =>
        Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
      let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
      let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
      (∀ t ∈ S, ∃ x ∈ Icc (1:ℝ) 2, (H (ya,x))⁻¹=t) →
      (∀ t ∈ S, |k (yb,t+b)-k (ya,t)| ≤ δ) →
      (S.card:ℝ) ≤ K*(1+C*δ*J/‖((yb-ya,b):ℝ × ℝ)‖) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_near_reciprocal_count hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ κ : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < κ ∧
      ∀ (F : ℝ → ℝ) (η x y : ℝ),
      0 < η → η ≤ η₀ → x ∈ Icc (3/4:ℝ) (9/4) → y ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun t => (iteratedDeriv 2 F t-iteratedDeriv 2 F (t+η*y))/(σ*η)
      let G := fun t => (iteratedDeriv 3 F t-iteratedDeriv 3 F (t+η*y))/(σ*η)
      DifferentiableAt ℝ (fun t => G t/(H t)^3) x ∧
      κ ≤ |deriv (fun t => G t/(H t)^3) x| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_spatial_lower hσ hc hU

end HuxleyReciprocalCountRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.contDiff_reciprocalProfileColumns
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.reciprocalProfileColumns_uniform_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_profile_chart_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_profile_uniform_variation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_reciprocal_endpoint_compression
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_local_reciprocal_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_near_reciprocal_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_spatial_lower

namespace HuxleyReciprocalPhysicalRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example
    (F : ℝ → ℝ) {σ c U η x y : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let G := fun v : ℝ × ℝ =>
      (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
    let P := fun v => G v*((H v)⁻¹)^3
    let R := max 1 (max (3*U/σ) (2*σ/c))
    DifferentiableAt ℝ (fun t => (H (y,t))⁻¹) x ∧
    DifferentiableAt ℝ (fun t => (H (t,x))⁻¹) y ∧
    DifferentiableAt ℝ (fun t => P (t,x)) y ∧
    |deriv (fun t => (H (y,t))⁻¹) x| ≤ R^3 ∧
    |deriv (fun t => (H (t,x))⁻¹) y| ≤ R^3 ∧
    |deriv (fun t => P (t,x)) y| ≤ 4*R^6 ∧
    c/(2*σ*R^2) ≤ |deriv (fun t => (H (y,t))⁻¹) x| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_surface_bounds F hσ hc hU hη hηmax hx hy hf hbound htests

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ A B : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < A ∧ 0 < B ∧
      ∀ (F : ℝ → ℝ) (η xa xb ya yb : ℝ),
      0 < η → η ≤ η₀ →
      xa ∈ Icc (1:ℝ) 2 → xb ∈ Icc (1:ℝ) 2 →
      ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      let P := fun v => G v*((H v)⁻¹)^3
      |(H (yb,xb))⁻¹-(H (ya,xa))⁻¹| ≤
        A*|P (yb,xb)-P (ya,xa)|+B*|yb-ya| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_translation_bound hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb b δ J : ℝ) (S : Finset ℝ) (xa xb : ℝ → ℝ),
      0 < η → η ≤ η₀ → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 < J → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ J*|s-t|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      let P := fun v => G v*((H v)⁻¹)^3
      (∀ t ∈ S, xa t ∈ Icc (1:ℝ) 2 ∧ xb t ∈ Icc (1:ℝ) 2 ∧
        (H (ya,xa t))⁻¹=t ∧ (H (yb,xb t))⁻¹=t+b) →
      (∀ t ∈ S, |P (yb,xb t)-P (ya,xa t)| ≤ δ) →
      (S.card:ℝ) ≤ C*(1+δ*J/‖((yb-ya,b):ℝ × ℝ)‖) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_count hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb b δ w Z : ℝ) (S : Finset ℤ) (xa xb : ℤ → ℝ),
      0 < η → η ≤ η₀ → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < w → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
      (∀ k ∈ S, Z+(k:ℝ)*w ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*w) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      let P := fun v => G v*((H v)⁻¹)^3
      let R := max 1 (max (3*U/σ) (2*σ/c))
      (∀ k ∈ S, xa k ∈ Icc (1:ℝ) 2 ∧ xb k ∈ Icc (1:ℝ) 2 ∧
        (H (yb,xb k))⁻¹=(H (ya,xa k))⁻¹+b) →
      (∀ k ∈ S, |P (yb,xb k)-P (ya,xa k)| ≤ δ) →
      (S.card:ℝ) ≤ C*(1+(2*σ*R^2/c)*δ/(w*‖((yb-ya,b):ℝ × ℝ)‖)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_block_count hσ hc hU

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c U η₀ a C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < U ∧
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (N : ℝ) (F : ℝ → ℝ), 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ 7 ε →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ U) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ (T : ℝ) (m n : ℕ), N ≤ (m:ℝ) → (n:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N m n-Expdb.exponentialSumAt Fext T N m n‖ ≤ 6) ∧
        (∀ (η ya yb b δ w Z : ℝ) (S : Finset ℤ) (xa xb : ℤ → ℝ),
      0 < η → η ≤ η₀ → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      0 < w → 0 ≤ δ → ((yb-ya,b):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
      (∀ k ∈ S, Z+(k:ℝ)*w ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*w) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 Fext v.2-iteratedDeriv 2 Fext (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 Fext v.2-iteratedDeriv 3 Fext (v.2+η*v.1))/(σ*η)
      let P := fun v => G v*((H v)⁻¹)^3
      let R := max 1 (max (3*U/σ) (2*σ/c))
      (∀ k ∈ S, xa k ∈ Icc (1:ℝ) 2 ∧ xb k ∈ Icc (1:ℝ) 2 ∧
        (H (yb,xb k))⁻¹=(H (ya,xa k))⁻¹+b) →
      (∀ k ∈ S, |P (yb,xb k)-P (ya,xa k)| ≤ δ) →
      (S.card:ℝ) ≤ C*(1+(2*σ*R^2/c)*δ/(w*‖((yb-ya,b):ℝ × ℝ)‖))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_reciprocal_block_count hσ

example
    (F : ℝ → ℝ) {σ c U η M xa xb ya yb Δ q : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hM : 2 ≤ M) (hxa : xa ∈ Icc (1:ℝ) 2) (hxb : xb ∈ Icc (1:ℝ) 2)
    (hya : ya ∈ Icc (1:ℝ) 2) (hyb : yb ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hΔ : 0 ≤ Δ) :
    let G := fun v : ℝ × ℝ =>
      (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
    let R := max 1 (max (3*U/σ) (2*σ/c))
    |G (yb,(round (M*xb):ℝ)/M)/G (ya,(round (M*xa):ℝ)/M)*q-1| ≤ Δ →
    |G (yb,xb)*q-G (ya,xa)| ≤ R*(Δ+(|q|+1)/(2*M)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rounded_weighted_third_bound F hσ hc hU hη hηmax hM hxa hxb hya hyb hf hbound htests hΔ

example
    (F : ℝ → ℝ) {σ c U η M xa xb ya yb Δ : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hM : 2 ≤ M) (hxa : xa ∈ Icc (1:ℝ) 2) (hxb : xb ∈ Icc (1:ℝ) 2)
    (hya : ya ∈ Icc (1:ℝ) 2) (hyb : yb ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hΔ : 0 ≤ Δ) :
    let H := fun v : ℝ × ℝ =>
      (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
    let G := fun v : ℝ × ℝ =>
      (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
    let P := fun v => G v*((H v)⁻¹)^3
    let R := max 1 (max (3*U/σ) (2*σ/c))
    let q := (H (ya,xa)/H (yb,xb))^3
    |G (yb,(round (M*xb):ℝ)/M)/G (ya,(round (M*xa):ℝ)/M)*q-1| ≤ Δ →
    |P (yb,xb)-P (ya,xa)| ≤ R^10*(Δ+1/M) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rounded_reciprocal_profile_bound F hσ hc hU hη hηmax hM hxa hxb hya hyb hf hbound htests hΔ

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb γ Δ T M N Z : ℝ)
        (S : Finset ℤ) (xa xb : ℤ → ℝ),
      0 < η → η ≤ η₀ → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ →
      ((yb-ya,T*γ/(2*M^2)):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
      (∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) →
      (∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M)) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let h := fun y z => iteratedDeriv 2 (f y) z/2
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ k ∈ S, h yb (xb k)=h ya (xa k)/(γ*h ya (xa k)+1)) →
      (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)*(γ*h ya (xa k)+1)^3-1| ≤ Δ) →
      let R := max 1 (max (3*U/σ) (2*σ/c))
      (S.card:ℝ) ≤ C*(1+(2*σ/c)*R^12*(Δ+1/M)*M/
        (N*‖((yb-ya,T*γ/(2*M^2)):ℝ × ℝ)‖)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_lower_block_count hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C K : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧ 0 < K ∧
      ∀ (F : ℝ → ℝ) (η ya yb γ D ℓ T M N R Z : ℝ)
        (S : Finset ℤ) (xa xb : ℤ → ℝ),
      0 < η → η ≤ η₀ → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ D → 2*C ≤ ℓ → γ ≠ 0 →
      T*N*R^2=M^3 → (ℓ*N)^2 ≤ M*R^2 → ℓ ≤ (S.card:ℝ) →
      |yb-ya| < a →
      (∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) →
      (∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M)) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let h := fun y z => iteratedDeriv 2 (f y) z/2
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ k ∈ S, h yb (xb k)=h ya (xa k)/(γ*h ya (xa k)+1)) →
      (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)*(γ*h ya (xa k)+1)^3-1| ≤
        D*R^2/(ℓ^2*N^2)) →
      |γ| *ℓ^3*N^2 ≤ K*(D+1)*R^4 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_lower_long_block_constraint hσ hc hU

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c U η₀ a C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < U ∧
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 2 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ 7 ε →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ U) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        (∀ (η ya yb γ Δ T N Z : ℝ) (S : Finset ℤ) (xa xb : ℤ → ℝ),
          0 < η → η ≤ η₀ → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
          0 < T → 0 < N → 0 ≤ Δ → |yb-ya| < a →
          (∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) →
          (∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M)) →
          let f := fun y z => T*(Fext (z/M)-Fext (z/M+η*y))/(σ*η)
          let h := fun y z => iteratedDeriv 2 (f y) z/2
          let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
          (∀ k ∈ S, h yb (xb k)=h ya (xa k)/(γ*h ya (xa k)+1)) →
          (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)*(γ*h ya (xa k)+1)^3-1| ≤ Δ) →
          let R := max 1 (max (3*U/σ) (2*σ/c))
          let d : ℝ × ℝ := (yb-ya,T*γ/(2*M^2))
          (S.card:ℝ) ≤ if d=0 then 2+M/N else
            C*(1+(2*σ/c)*R^12*(Δ+1/M)*M/(N*‖d‖))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_physical_lower_count hσ

end HuxleyReciprocalPhysicalRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_surface_bounds
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_translation_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_reciprocal_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rounded_weighted_third_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rounded_reciprocal_profile_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_lower_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_lower_long_block_constraint
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_physical_lower_count


namespace HuxleyDifferencePairedRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example
    (F : ℝ → ℝ) {σ c η x y : ℝ}
    (hσ : 0 < σ) (hη : 0 < η) (hηmax : η ≤ 1/8) (hc : 0 < c)
    (hx : x ∈ Icc (3/4:ℝ) (9/4)) (hy : y ∈ Icc (1/2:ℝ) 3)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    c/(2*σ) ≤ (iteratedDeriv 3 F x-iteratedDeriv 3 F (x+η*y))/(σ*η) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_third_signed_lower F hσ hη hηmax hc hx hy hf hnegative

example
    (F : ℝ → ℝ) (S : Finset ℤ) (xa xb : ℤ → ℝ) (a b c d : ℤ)
    {σ κ₀ U η ya yb Δ T M N R Z : ℝ}
    (hσ : 0 < σ) (hc₀ : 0 < κ₀) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hya : ya ∈ Icc (1:ℝ) 2) (hyb : yb ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      κ₀ ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hnegative : ∀ z ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F z ≤ -κ₀)
    (hT : 0 < T) (hM : 2 ≤ M) (hN : 0 < N) (hΔ : 0 ≤ Δ)
    (hphase : T*N*R^2=M^3) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hlarge : 16*(3*U/σ)*M^2 ≤ |(c:ℝ)| *(κ₀/(2*σ))^2*T)
    (hpoints : ∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M))
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) :
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let t := fun k => (c:ℝ)*h ya (xa k)+d
    (∀ k ∈ S, ((a:ℝ)*h ya (xa k)+b)/t k=h yb (xb k)) →
    (∀ k ∈ S, (1:ℝ)/2 ≤ t k ∧ t k ≤ 2) →
    (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)*(t k)^3-1| ≤ Δ) →
    let B := max 1 (max (3*U/σ) (2*σ/κ₀))
    (S.card:ℝ) ≤ 2+16*B*(Δ+5/M)*R^2/((κ₀/(2*σ))^2*|(c:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_paired_large_entry_block_count F S xa xb a b c d hσ hc₀ hU hη hηmax hya hyb hf hbound htests hnegative hT hM hN hΔ hphase hdet hc hlarge hpoints hwindow

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ c U : ℝ, 0 < δ ∧ 0 < c ∧ 0 < U ∧
      ∀ (N : ℝ) (F : ℝ → ℝ), 1 ≤ N →
      Expdb.IsApproximateModelPhaseFunction F σ 7 δ →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ U) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -c) ∧
        (∀ (T : ℝ) (a b : ℕ), N ≤ (a:ℝ) → (b:ℝ) ≤ 2*N →
          ‖Expdb.exponentialSumAt F T N a b-Expdb.exponentialSumAt Fext T N a b‖ ≤ 6) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_signed_source_tests hσ

example
    (F : ℝ → ℝ) (S : Finset ℤ) (xa xb : ℤ → ℝ) (a b c d : ℤ)
    {σ κ₀ U η ya yb D ℓ T M N R Z : ℝ}
    (hσ : 0 < σ) (hc₀ : 0 < κ₀) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hya : ya ∈ Icc (1:ℝ) 2) (hyb : yb ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      κ₀ ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hnegative : ∀ z ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F z ≤ -κ₀)
    (hT : 0 < T) (hM : 2 ≤ M) (hN : 0 < N) (hD : 0 ≤ D)
    (hℓ : 4 ≤ ℓ) (hcut : (ℓ*N)^2 ≤ M*R^2) (hcard : ℓ ≤ (S.card:ℝ))
    (hphase : T*N*R^2=M^3) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hlarge : 16*(3*U/σ)*N*R^2 ≤ |(c:ℝ)| *(κ₀/(2*σ))^2*M)
    (hpoints : ∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M))
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) :
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let t := fun k => (c:ℝ)*h ya (xa k)+d
    (∀ k ∈ S, ((a:ℝ)*h ya (xa k)+b)/t k=h yb (xb k)) →
    (∀ k ∈ S, (1:ℝ)/2 ≤ t k ∧ t k ≤ 2) →
    (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)*(t k)^3-1| ≤ D*R^2/(ℓ^2*N^2)) →
    let B := max 1 (max (3*U/σ) (2*σ/κ₀))
    (κ₀/(2*σ))^2*|(c:ℝ)| *ℓ^3*N^2 ≤ 32*B*(D+5)*R^4 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_paired_long_block_constraint F S xa xb a b c d hσ hc₀ hU hη hηmax hya hyb hf hbound htests hnegative hT hM hN hD hℓ hcut hcard hphase hdet hc hlarge hpoints hwindow

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε κ₀ U : ℝ, 0 < ε ∧ 0 < κ₀ ∧ 0 < U ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 2 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ 7 ε →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ U) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          κ₀ ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -κ₀) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        (∀ (S : Finset ℤ) (xa xb : ℤ → ℝ) (a b c d : ℤ)
          (η ya yb Δ T N R Z : ℝ),
          0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
          0 < T → 0 < N → 0 ≤ Δ → T*N*R^2=M^3 → a*d-b*c=1 → c ≠ 0 →
          16*(3*U/σ)*M^2 ≤ |(c:ℝ)| *(κ₀/(2*σ))^2*T →
          (∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M)) →
          (∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) →
          let f := fun y z => T*(Fext (z/M)-Fext (z/M+η*y))/(σ*η)
          let h := fun y z => iteratedDeriv 2 (f y) z/2
          let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
          let t := fun k => (c:ℝ)*h ya (xa k)+d
          (∀ k ∈ S, ((a:ℝ)*h ya (xa k)+b)/t k=h yb (xb k)) →
          (∀ k ∈ S, (1:ℝ)/2 ≤ t k ∧ t k ≤ 2) →
          (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)*(t k)^3-1| ≤ Δ) →
          let B := max 1 (max (3*U/σ) (2*σ/κ₀))
          (S.card:ℝ) ≤ 2+16*B*(Δ+5/M)*R^2/((κ₀/(2*σ))^2*|(c:ℝ)|)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_paired_large_entry_count hσ

end HuxleyDifferencePairedRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_third_signed_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_paired_large_entry_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_signed_source_tests
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_paired_long_block_constraint
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_paired_large_entry_count


namespace HuxleyConstructedParameterScaleRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η x₀ y₀ E J g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
      0 < η → η ≤ 1/8 → x₀ ∈ Icc (1:ℝ) 2 → y₀ ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 ≤ E → 0 < J →
      (∀ y ∈ S, y ∈ Icc (1:ℝ) 2 ∧ |y-y₀| < a ∧ x y ∈ Icc (1:ℝ) 2) →
      (∀ y ∈ S, ∀ z ∈ S, y ≠ z → 1 ≤ J*|y-z|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      (∀ y ∈ S, H (y,x y)=H (y₀,x₀)) →
      (∀ y ∈ S, |G (y,x y)-g| ≤ E) →
      (S.card:ℝ) ≤ 1+C*E*J :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_local_parameter_count hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η E J q g : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 ≤ E → 0 < J →
      (∀ y ∈ S, y ∈ Icc (1:ℝ) 2 ∧ x y ∈ Icc (1:ℝ) 2) →
      (∀ y ∈ S, ∀ z ∈ S, y ≠ z → 1 ≤ J*|y-z|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      (∀ y ∈ S, H (y,x y)=q) →
      (∀ y ∈ S, |G (y,x y)-g| ≤ E) →
      (S.card:ℝ) ≤ K*(1+C*E*J) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_parameter_count hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya xa Δ J q t T M : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 < T → 2 ≤ M → 0 ≤ Δ → 0 < J → t ∈ Icc (1/2:ℝ) 2 →
      xa ∈ Icc M (2*M) →
      (∀ y ∈ S, y ∈ Icc (1:ℝ) 2 ∧ x y ∈ Icc M (2*M)) →
      (∀ y ∈ S, ∀ z ∈ S, y ≠ z → 1 ≤ J*|y-z|) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ y ∈ S, iteratedDeriv 2 (f y) (x y)/2=q) →
      (∀ y ∈ S, |μ y (x y)/μ ya xa*t^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (S.card:ℝ) ≤ K*(1+8*C*B*(Δ+5/M)*J) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_parameter_count hσ hc hU

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c U K C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < U ∧ 0 < K ∧ 0 < C ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 2 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ 7 ε →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ U) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -c) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        (∀ (η ya xa Δ J q t T : ℝ) (S : Finset ℝ) (x : ℝ → ℝ),
          0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 →
          0 < T → 0 ≤ Δ → 0 < J → t ∈ Icc (1/2:ℝ) 2 →
          xa ∈ Icc M (2*M) →
          (∀ y ∈ S, y ∈ Icc (1:ℝ) 2 ∧ x y ∈ Icc M (2*M)) →
          (∀ y ∈ S, ∀ z ∈ S, y ≠ z → 1 ≤ J*|y-z|) →
          let f := fun y z => T*(Fext (z/M)-Fext (z/M+η*y))/(σ*η)
          let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
          (∀ y ∈ S, iteratedDeriv 2 (f y) (x y)/2=q) →
          (∀ y ∈ S, |μ y (x y)/μ ya xa*t^3-1| ≤ Δ) →
          let B := max 1 (max (3*U/σ) (2*σ/c))
          (S.card:ℝ) ≤ K*(1+8*C*B*(Δ+5/M)*J)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_physical_parameter_count hσ

example
    {M N R Q B : ℝ} (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hB : 1 ≤ B)
    (hlarge : 2*B ≤ (N/Q)^((2:ℝ)/3)) (hscale : N^5 ≤ M*R^4) :
    ∃ U : ℕ, 1 ≤ U ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      B^3*(U:ℝ)^3*N^3 ≤ M*R^2 ∧
      B*(U:ℝ)*Q ≤ N ∧
      B^2*(U:ℝ)^3*R^2 ≤ N^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_reference_block_length hM hN hR hRQ hQN hB hlarge hscale

example
    {M N R Q B : ℝ} (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hB : 1 ≤ B)
    (hlarge : 2*B ≤ (N/Q)^((2:ℝ)/3)) (hscale : N^5 ≤ M*R^4) :
    ∃ U : ℕ, 1 ≤ U ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      ∀ r G : ℝ, 0 < r → 0 ≤ G → R^2 ≤ r^2*(U:ℝ) →
        G ≤ B*(U:ℝ)*N →
        G^3 ≤ M*R^2 ∧ G*Q ≤ N^2 ∧ G*R^2 ≤ r*N^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_reference_block_length_physical_budgets hM hN hR hRQ hQN hB hlarge hscale

end HuxleyConstructedParameterScaleRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_local_parameter_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_parameter_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_parameter_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_physical_parameter_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_reference_block_length
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_reference_block_length_physical_budgets

namespace HuxleyReusedMatrixEnumerationRegression

example
    (S : Finset (Fin 4 → ℤ)) {c : ℤ} {X : ℝ} (hc : c ≠ 0) (hX : 0 ≤ X)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hgamma : ∀ M∈S, M 2=c)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(c:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(c:ℝ)| *X+2) :
    (S.card:ℝ) ≤ (2*|(c:ℝ)| *X+5)*(2*X+5) :=
  TaoTrudgianYang2025.bourgain_fixed_gamma_matrix_count S hc hX hdet hgamma ha hd

example
    (S : Finset (Fin 4 → ℤ)) {X Gamma W : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma) (hW : 0 ≤ W)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hc : ∀ M∈S, M 2 ≠ 0 ∧ |(M 2:ℝ)| ≤ Gamma)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(M 2:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(M 2:ℝ)| *X+2) :
    ∑ M∈S,(1+W/|(M 2:ℝ)|) ≤ (2*Gamma+1)*(2*X+5)^2*(Gamma+W) :=
  TaoTrudgianYang2025.bourgain_resonance_matrix_weight_sum S hX hGamma hW hdet hc ha hd

example {a b c d x y X : ℝ}
    (hdet : a*d-b*c=1) (htl : (1:ℝ)/2 ≤ c*x+d) (htu : c*x+d ≤ 2)
    (hmap : (a*x+b)/(c*x+d)=y) (hx : |x| ≤ X) (hy : |y| ≤ X) :
    |a| ≤ |c| *X+2 ∧ |d| ≤ |c| *X+2 :=
  TaoTrudgianYang2025.bourgain_mobius_entry_bounds hdet htl htu hmap hx hy

end HuxleyReusedMatrixEnumerationRegression

#print axioms TaoTrudgianYang2025.bourgain_fixed_gamma_matrix_count
#print axioms TaoTrudgianYang2025.bourgain_resonance_matrix_weight_sum
#print axioms TaoTrudgianYang2025.bourgain_mobius_entry_bounds

namespace HuxleyPairedMatrixSumRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example
    (F : ℝ → ℝ) (S : Finset (Fin 4 → ℤ))
    (blocks : (Fin 4 → ℤ) → Finset ℤ)
    (xa xb : (Fin 4 → ℤ) → ℤ → ℝ)
    (ya yb Z : (Fin 4 → ℤ) → ℝ)
    {σ κ₀ U η Δ T M N R Gamma : ℝ}
    (hσ : 0 < σ) (hc₀ : 0 < κ₀) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hya : ∀ A ∈ S, ya A ∈ Icc (1:ℝ) 2)
    (hyb : ∀ A ∈ S, yb A ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      κ₀ ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hnegative : ∀ z ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F z ≤ -κ₀)
    (hT : 0 < T) (hM : 2 ≤ M) (hN : 0 < N) (hΔ : 0 ≤ Δ)
    (hGamma : 0 ≤ Gamma) (hphase : T*N*R^2=M^3)
    (hdet : ∀ A ∈ S, A 0*A 3-A 1*A 2=1)
    (hc : ∀ A ∈ S, A 2 ≠ 0 ∧ |(A 2:ℝ)| ≤ Gamma)
    (hlarge : ∀ A ∈ S, 16*(3*U/σ)*M^2 ≤ |(A 2:ℝ)| *(κ₀/(2*σ))^2*T)
    (hoccupied : ∀ A ∈ S, (blocks A).Nonempty)
    (hpoints : ∀ A ∈ S, ∀ k ∈ blocks A,
      xa A k ∈ Icc M (2*M) ∧ xb A k ∈ Icc M (2*M))
    (hwindow : ∀ A ∈ S, ∀ k ∈ blocks A,
      Z A+(k:ℝ)*N ≤ xa A k ∧ xa A k ≤ Z A+((k:ℝ)+1)*N) :
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let t := fun (A : Fin 4 → ℤ) k => (A 2:ℝ)*h (ya A) (xa A k)+A 3
    (∀ A ∈ S, ∀ k ∈ blocks A,
      ((A 0:ℝ)*h (ya A) (xa A k)+A 1)/t A k=h (yb A) (xb A k)) →
    (∀ A ∈ S, ∀ k ∈ blocks A, (1:ℝ)/2 ≤ t A k ∧ t A k ≤ 2) →
    (∀ A ∈ S, ∀ k ∈ blocks A,
      |μ (yb A) (xb A k)/μ (ya A) (xa A k)*(t A k)^3-1| ≤ Δ) →
    let B := max 1 (max (3*U/σ) (2*σ/κ₀))
    let curvatureScale := 3*U*T/(2*σ*M^2)
    let W := 8*B*(Δ+5/M)*R^2/(κ₀/(2*σ))^2
    ∑ A ∈ S, ((blocks A).card:ℝ) ≤
      2*(2*Gamma+1)*(2*curvatureScale+5)^2*(Gamma+W) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_paired_matrix_block_sum F S blocks xa xb ya yb Z hσ hc₀ hU hη hηmax hya hyb hf hbound htests hnegative
    hT hM hN hΔ hGamma hphase hdet hc hlarge hoccupied hpoints hwindow

example
    (F : ℝ → ℝ) (S : Finset (Fin 4 → ℤ))
    (blocks : (Fin 4 → ℤ) → Finset ℤ)
    (xa xb : (Fin 4 → ℤ) → ℤ → ℝ)
    (ya yb Z : (Fin 4 → ℤ) → ℝ)
    {σ κ₀ U η D ℓ T M N R : ℝ}
    (hσ : 0 < σ) (hc₀ : 0 < κ₀) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hya : ∀ A ∈ S, ya A ∈ Icc (1:ℝ) 2)
    (hyb : ∀ A ∈ S, yb A ∈ Icc (1:ℝ) 2)
    (hf : ∀ z, 0 < z → ContDiffAt ℝ ∞ F z)
    (hbound : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F z| ≤ U)
    (htests : ∀ z ∈ Icc (1/2:ℝ) 3, ∀ j,
      κ₀ ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F z) j|)
    (hnegative : ∀ z ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F z ≤ -κ₀)
    (hT : 0 < T) (hM : 2 ≤ M) (hN : 0 < N) (hD : 0 ≤ D)
    (hℓ : 4 ≤ ℓ) (hcut : (ℓ*N)^2 ≤ M*R^2)
    (hphase : T*N*R^2=M^3)
    (hdet : ∀ A ∈ S, A 0*A 3-A 1*A 2=1)
    (hc : ∀ A ∈ S, A 2 ≠ 0)
    (hlarge : ∀ A ∈ S, 16*(3*U/σ)*N*R^2 ≤ |(A 2:ℝ)| *(κ₀/(2*σ))^2*M)
    (hcard : ∀ A ∈ S, ℓ ≤ ((blocks A).card:ℝ))
    (hpoints : ∀ A ∈ S, ∀ k ∈ blocks A,
      xa A k ∈ Icc M (2*M) ∧ xb A k ∈ Icc M (2*M))
    (hwindow : ∀ A ∈ S, ∀ k ∈ blocks A,
      Z A+(k:ℝ)*N ≤ xa A k ∧ xa A k ≤ Z A+((k:ℝ)+1)*N) :
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let t := fun (A : Fin 4 → ℤ) k => (A 2:ℝ)*h (ya A) (xa A k)+A 3
    (∀ A ∈ S, ∀ k ∈ blocks A,
      ((A 0:ℝ)*h (ya A) (xa A k)+A 1)/t A k=h (yb A) (xb A k)) →
    (∀ A ∈ S, ∀ k ∈ blocks A, (1:ℝ)/2 ≤ t A k ∧ t A k ≤ 2) →
    (∀ A ∈ S, ∀ k ∈ blocks A,
      |μ (yb A) (xb A k)/μ (ya A) (xa A k)*(t A k)^3-1| ≤ D*R^2/(ℓ^2*N^2)) →
    let B := max 1 (max (3*U/σ) (2*σ/κ₀))
    let curvatureScale := 3*U*T/(2*σ*M^2)
    let Gamma := 32*B*(D+5)*R^4/((κ₀/(2*σ))^2*ℓ^3*N^2)
    ∑ A ∈ S, ((blocks A).card:ℝ) ≤
      3*ℓ*Gamma^2*(2*curvatureScale+5)^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_paired_long_matrix_block_sum F S blocks xa xb ya yb Z hσ hc₀ hU hη hηmax hya hyb hf hbound htests hnegative
    hT hM hN hD hℓ hcut hphase hdet hc hlarge hcard hpoints hwindow

example
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε κ₀ U : ℝ, 0 < ε ∧ 0 < κ₀ ∧ 0 < U ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 2 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ 7 ε →
      ∃ Fext : ℝ → ℝ,
        (∀ x, 0 < x → ContDiffAt ℝ ∞ Fext x) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ U) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          κ₀ ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -κ₀) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        (∀ (S : Finset (Fin 4 → ℤ)) (blocks : (Fin 4 → ℤ) → Finset ℤ)
          (xa xb : (Fin 4 → ℤ) → ℤ → ℝ) (ya yb Z : (Fin 4 → ℤ) → ℝ)
          (η D ℓ T N R : ℝ),
          0 < η → η ≤ 1/8 →
          (∀ A ∈ S, ya A ∈ Icc (1:ℝ) 2) → (∀ A ∈ S, yb A ∈ Icc (1:ℝ) 2) →
          0 < T → 0 < N → 0 ≤ D → 4 ≤ ℓ → (ℓ*N)^2 ≤ M*R^2 →
          T*N*R^2=M^3 →
          (∀ A ∈ S, A 0*A 3-A 1*A 2=1) → (∀ A ∈ S, A 2 ≠ 0) →
          (∀ A ∈ S, 16*(3*U/σ)*N*R^2 ≤ |(A 2:ℝ)| *(κ₀/(2*σ))^2*M) →
          (∀ A ∈ S, ℓ ≤ ((blocks A).card:ℝ)) →
          (∀ A ∈ S, ∀ k ∈ blocks A,
            xa A k ∈ Icc M (2*M) ∧ xb A k ∈ Icc M (2*M)) →
          (∀ A ∈ S, ∀ k ∈ blocks A,
            Z A+(k:ℝ)*N ≤ xa A k ∧ xa A k ≤ Z A+((k:ℝ)+1)*N) →
          let f := fun y z => T*(Fext (z/M)-Fext (z/M+η*y))/(σ*η)
          let h := fun y z => iteratedDeriv 2 (f y) z/2
          let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
          let t := fun (A : Fin 4 → ℤ) k => (A 2:ℝ)*h (ya A) (xa A k)+A 3
          (∀ A ∈ S, ∀ k ∈ blocks A,
            ((A 0:ℝ)*h (ya A) (xa A k)+A 1)/t A k=h (yb A) (xb A k)) →
          (∀ A ∈ S, ∀ k ∈ blocks A, (1:ℝ)/2 ≤ t A k ∧ t A k ≤ 2) →
          (∀ A ∈ S, ∀ k ∈ blocks A,
            |μ (yb A) (xb A k)/μ (ya A) (xa A k)*(t A k)^3-1| ≤ D*R^2/(ℓ^2*N^2)) →
          let B := max 1 (max (3*U/σ) (2*σ/κ₀))
          let curvatureScale := 3*U*T/(2*σ*M^2)
          let Gamma := 32*B*(D+5)*R^4/((κ₀/(2*σ))^2*ℓ^3*N^2)
          ∑ A ∈ S, ((blocks A).card:ℝ) ≤
            3*ℓ*Gamma^2*(2*curvatureScale+5)^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_long_matrix_block_sum hσ

end HuxleyPairedMatrixSumRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_paired_matrix_block_sum
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_paired_long_matrix_block_sum
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_long_matrix_block_sum

namespace HuxleyReferenceRefinementRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example {a b H : ℤ}
    (hb : 0 < b) (hbH : b ≤ H) (hcop : IsCoprime a b) :
    ∃ c d : ℤ, 1 ≤ d ∧ d ≤ H ∧ H < b+d ∧ IsCoprime c d ∧
      c*b-a*d=1 ∧
      ∀ m n : ℤ, 1 ≤ n → n ≤ H → a*n < b*m → c*n ≤ m*d :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_right_neighbor_at_order hb hbH hcop

example {H : ℤ} (hH : 1 ≤ H)
    {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    ∃ a b c d : ℤ, 1 ≤ b ∧ b ≤ H ∧ 1 ≤ d ∧ d ≤ H ∧ H < b+d ∧
      IsCoprime a b ∧ IsCoprime c d ∧ c*b-a*d=1 ∧
      (a:ℝ)/b ≤ x ∧ x < (c:ℝ)/d :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_farey_bracket_unit hH hx

example {H : ℤ} (hH : 1 ≤ H) (x : ℝ) :
    ∃ a b c d : ℤ, 1 ≤ b ∧ b ≤ H ∧ 1 ≤ d ∧ d ≤ H ∧ H < b+d ∧
      IsCoprime a b ∧ IsCoprime c d ∧ c*b-a*d=1 ∧
      (a:ℝ)/b ≤ x ∧ x < (c:ℝ)/d ∧
      (c:ℝ)/d-(a:ℝ)/b=1/((b:ℝ)*d) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_farey_bracket hH x

example
    (A seed : Set ℝ) (ε : NNReal) (hA : A.Finite)
    (hseed : seed ⊆ A) (hsep : Metric.IsSeparated ε seed) :
    ∃ S : Set ℝ, seed ⊆ S ∧ S ⊆ A ∧ S.Finite ∧
      Metric.IsSeparated ε S ∧ Metric.IsCover ε A S :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_seeded_separated_reference_cover A seed ε hA hseed hsep

example {e r f s : ℤ} {δ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hdet : f*r-e*s=1)
    (hδ : 0 < δ) (hscale : 1 ≤ δ*(r:ℝ)^2) :
    ∃ K : ℕ,
      (∀ n : ℕ, n ≤ K →
        IsCoprime (e+f*(n:ℤ)) (r+s*(n:ℤ)) ∧ r ≤ r+s*(n:ℤ)) ∧
      ∀ x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s),
        ∃ n ≤ K, |x-((e:ℝ)+f*n)/((r:ℝ)+s*n)| ≤ δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_mediant_reference_cover hr hs hdet hδ hscale

example {e r f s : ℤ} {δ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hdet : f*r-e*s=1)
    (hδ : 0 < δ) (hscale : 1 ≤ δ*(r:ℝ)^2)
    (hlong : δ < (f:ℝ)/s-(e:ℝ)/r) :
    ∃ S : Finset ℝ, (e:ℝ)/r ∈ S ∧ (f:ℝ)/s ∈ S ∧
      (∀ x ∈ S, x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s)) ∧
      (∀ x ∈ S, x ≠ (f:ℝ)/s →
        ∃ n : ℕ, x=((e:ℝ)+f*n)/((r:ℝ)+s*n) ∧
          IsCoprime (e+f*(n:ℤ)) (r+s*(n:ℤ)) ∧ r ≤ r+s*(n:ℤ)) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/4 < |x-y|) ∧
      (∀ x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s), ∃ y ∈ S, |x-y| ≤ 5*δ/4) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y →
        (∀ z ∈ S, ¬ (x < z ∧ z < y)) →
        δ/4 < y-x ∧ y-x ≤ 5*δ/2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_separated_mediant_reference_cover hr hs hdet hδ hscale hlong

example {e r f s : ℤ} {δ : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hdet : f*r-e*s=1)
    (hδ : 0 < δ) (hscale : 1 ≤ δ*(s:ℝ)^2)
    (hlong : δ < (f:ℝ)/s-(e:ℝ)/r) :
    ∃ S : Finset ℝ, (e:ℝ)/r ∈ S ∧ (f:ℝ)/s ∈ S ∧
      (∀ x ∈ S, x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s)) ∧
      (∀ x ∈ S, x ≠ (e:ℝ)/r →
        ∃ n : ℕ, x=((f:ℝ)+e*n)/((s:ℝ)+r*n) ∧
          IsCoprime (f+e*(n:ℤ)) (s+r*(n:ℤ)) ∧ s ≤ s+r*(n:ℤ)) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/4 < |x-y|) ∧
      (∀ x ∈ Icc ((e:ℝ)/r) ((f:ℝ)/s), ∃ y ∈ S, |x-y| ≤ 5*δ/4) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y →
        (∀ z ∈ S, ¬ (x < z ∧ z < y)) →
        δ/4 < y-x ∧ y-x ≤ 5*δ/2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_separated_reflected_mediant_reference_cover hr hs hdet hδ hscale hlong

example {a b c d : ℤ} {δ : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hdet : c*b-a*d=1) (hδ : 0 < δ)
    (hscale : 1 ≤ δ*((max b d:ℤ):ℝ)^2)
    (hgap : δ/4 ≤ (c:ℝ)/d-(a:ℝ)/b) :
    ∃ S : Finset ℝ, (a:ℝ)/b ∈ S ∧ (c:ℝ)/d ∈ S ∧
      (∀ x ∈ S, x ∈ Icc ((a:ℝ)/b) ((c:ℝ)/d)) ∧
      (∀ x ∈ S, x ≠ (a:ℝ)/b → x ≠ (c:ℝ)/d →
        ∃ m n u v : ℤ, x=(m:ℝ)/n ∧ IsCoprime m n ∧ max b d ≤ n ∧
          ((u=a ∧ v=b) ∨ (u=c ∧ v=d)) ∧ |m*v-u*n|=1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/4 ≤ |x-y|) ∧
      (∀ x ∈ Icc ((a:ℝ)/b) ((c:ℝ)/d), ∃ y ∈ S, |x-y| ≤ 5*δ/4) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y →
        (∀ z ∈ S, ¬ (x < z ∧ z < y)) →
        δ/4 ≤ y-x ∧ y-x ≤ 5*δ/2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_farey_reference_refinement hb hd hdet hδ hscale hgap

example {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ∃ H : ℤ, 2 ≤ H ∧
      ∀ b d : ℤ, 0 < b → b ≤ H → 0 < d → d ≤ H → H < b+d →
        1 ≤ δ*((max b d:ℤ):ℝ)^2 ∧ δ/4 ≤ 1/((b:ℝ)*d) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_source_farey_order hδ hδmax

example {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ∃ H : ℤ, 2 ≤ H ∧ ∀ x : ℝ,
      ∃ a b c d : ℤ, 0 < b ∧ b ≤ H ∧ 0 < d ∧ d ≤ H ∧ H < b+d ∧
        IsCoprime a b ∧ IsCoprime c d ∧ c*b-a*d=1 ∧
        (a:ℝ)/b ≤ x ∧ x < (c:ℝ)/d ∧ 1 ≤ δ*((max b d:ℤ):ℝ)^2 ∧
        ∃ S : Finset ℝ, (a:ℝ)/b ∈ S ∧ (c:ℝ)/d ∈ S ∧
          (∀ z ∈ S, z ∈ Icc ((a:ℝ)/b) ((c:ℝ)/d)) ∧
          (∀ z ∈ S, z ≠ (a:ℝ)/b → z ≠ (c:ℝ)/d →
            ∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ max b d ≤ n ∧
              ((u=a ∧ v=b) ∨ (u=c ∧ v=d)) ∧ |m*v-u*n|=1) ∧
          (∀ z ∈ S, ∀ w ∈ S, z ≠ w → δ/4 ≤ |z-w|) ∧
          (∀ z ∈ Icc ((a:ℝ)/b) ((c:ℝ)/d), ∃ w ∈ S, |z-w| ≤ 5*δ/4) ∧
          (∀ z ∈ S, ∀ w ∈ S, z < w →
            (∀ v ∈ S, ¬ (z < v ∧ v < w)) →
            δ/4 ≤ w-z ∧ w-z ≤ 5*δ/2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_source_reference_refinement hδ hδmax

end HuxleyReferenceRefinementRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_right_neighbor_at_order
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_farey_bracket_unit
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_farey_bracket
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_seeded_separated_reference_cover
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_mediant_reference_cover
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_separated_mediant_reference_cover
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_separated_reflected_mediant_reference_cover
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_farey_reference_refinement
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_source_farey_order
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_source_reference_refinement

namespace HuxleyGlobalUnitReferenceRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example {a b c d m n : ℤ}
    (hb : 0 < b) (hd : 0 < d) (hn : 0 < n) (hdet : c*b-a*d=1)
    (hleft : (a:ℝ)/b < (m:ℝ)/n) (hright : (m:ℝ)/n < (c:ℝ)/d) :
    b+d ≤ n :=
  TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_interval_denominator_lower (a:=a) (b:=b) (c:=c) (d:=d) (m:=m) (n:=n) hb hd hn hdet hleft hright

example {a b c d : ℤ} {x : ℝ}
    (hb : 0 < b) (hd : 0 < d)
    (hdet : c*b-a*d=1) (hx : x ∈ Ico (0:ℝ) 1)
    (hleft : (a:ℝ)/b ≤ x) (hright : x < (c:ℝ)/d) :
    0 ≤ a ∧ c ≤ d :=
  TaoTrudgianYang2025.HuxleyRationalPhase.farey_bracket_unit_bounds (a:=a) (b:=b) (c:=c) (d:=d) (x:=x) hb hd hdet hx hleft hright

example {q r : ℚ} {H : ℤ}
    (hH : 2 ≤ H) (hq : (q.den:ℤ) ≤ H) (hr : (r.den:ℤ) ≤ H) (hne : q ≠ r) :
    1/(H:ℝ)^2 < |(q:ℝ)-(r:ℝ)| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.bounded_denominator_strict_separation (q:=q) (r:=r) (H:=H) hH hq hr hne

example {H : ℤ} (hH : 2 ≤ H) :
    ∃ B : Finset ℝ,
      (∀ x, x ∈ B ↔ ∃ q : ℚ, x=(q:ℝ) ∧ (q.den:ℤ) ≤ H ∧
        (q:ℝ) ∈ Icc (0:ℝ) 1) ∧
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → 1/(H:ℝ)^2 < |x-y|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_finite_farey_seed (H:=H) hH

example {δ : ℝ} {H : ℤ}
    (hδ : 0 < δ) (hH : 2 ≤ H)
    (hscale : ∀ b d : ℤ, 0 < b → b ≤ H → 0 < d → d ≤ H → H < b+d →
      1 ≤ δ*((max b d:ℤ):ℝ)^2 ∧ δ/4 ≤ 1/((b:ℝ)*d))
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    ∃ z ∈ Icc (0:ℝ) 1, |x-z| ≤ 5*δ/4 ∧
      ((∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
       (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
         1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
         (u:ℝ)/v ∈ Icc (0:ℝ) 1 ∧ |m*v-u*n|=1)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_unit_reference_candidate (δ:=δ) (H:=H) hδ hH hscale (x:=x) hx

example {δ : ℝ} {H : ℤ}
    (hδ : 0 < δ) (hH : 2 ≤ H)
    (hscale : ∀ b d : ℤ, 0 < b → b ≤ H → 0 < d → d ≤ H → H < b+d →
      1 ≤ δ*((max b d:ℤ):ℝ)^2 ∧ δ/4 ≤ 1/((b:ℝ)*d)) :
    ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc (0:ℝ) 1 → (q:ℝ) ∈ S) ∧
      (∀ z ∈ S, z ∈ Icc (0:ℝ) 1) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
          (u:ℝ)/v ∈ Icc (0:ℝ) 1 ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/4 < |x-y|) ∧
      (∀ x ∈ Icc (0:ℝ) 1, ∃ y ∈ S, |x-y| ≤ 7*δ/4) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y →
        (∀ z ∈ S, ¬ (x < z ∧ z < y)) →
        δ/4 < y-x ∧ y-x ≤ 7*δ/2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_unit_reference_system (δ:=δ) (H:=H) hδ hH hscale

example (S : Finset ℝ) {δ : ℝ} {H : ℤ}
    (hδ : 0 < δ)
    (hseed : ∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc (0:ℝ) 1 → (q:ℝ) ∈ S)
    (hpoints : ∀ z ∈ S, z ∈ Icc (0:ℝ) 1)
    (hscale : ∀ b d : ℤ, 0 < b → b ≤ H → 0 < d → d ≤ H → H < b+d →
      1 ≤ δ*((max b d:ℤ):ℝ)^2)
    {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d)
    (haS : (a:ℝ)/b ∈ S) (hcS : (c:ℝ)/d ∈ S)
    (hac : (a:ℝ)/b < (c:ℝ)/d)
    (hadj : ∀ z ∈ S, ¬ ((a:ℝ)/b < z ∧ z < (c:ℝ)/d))
    (hbcase : b ≤ H ∨ 1 ≤ δ*(b:ℝ)^2)
    (hdcase : d ≤ H ∨ 1 ≤ δ*(d:ℝ)^2) :
    1 ≤ δ*((max b d:ℤ):ℝ)^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.reference_adjacent_denominator_scale S (δ:=δ) (H:=H) hδ hseed hpoints hscale (a:=a) (b:=b) (c:=c) (d:=d) hb hd haS hcS hac hadj hbcase hdcase

example {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ∃ H : ℤ, 2 ≤ H ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc (0:ℝ) 1 → (q:ℝ) ∈ S) ∧
      (∀ z ∈ S, z ∈ Icc (0:ℝ) 1) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
          (u:ℝ)/v ∈ Icc (0:ℝ) 1 ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/4 < |x-y|) ∧
      (∀ x ∈ Icc (0:ℝ) 1, ∃ y ∈ S, |x-y| ≤ 7*δ/4) ∧
      (∀ x ∈ S, ∀ y ∈ S, x < y →
        (∀ z ∈ S, ¬ (x < z ∧ z < y)) →
        δ/4 < y-x ∧ y-x ≤ 7*δ/2 ∧
        ∃ a b c d : ℤ, x=(a:ℝ)/b ∧ y=(c:ℝ)/d ∧
          IsCoprime a b ∧ IsCoprime c d ∧ 0 < b ∧ 0 < d ∧
          1 ≤ δ*((max b d:ℤ):ℝ)^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_source_unit_reference_system (δ:=δ) hδ hδmax

end HuxleyGlobalUnitReferenceRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.unimodular_interval_denominator_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_bracket_unit_bounds
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.bounded_denominator_strict_separation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_finite_farey_seed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_unit_reference_candidate
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_unit_reference_system
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.reference_adjacent_denominator_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_source_unit_reference_system

namespace HuxleyIntervalScaleRegression

example (S : Finset ℝ) {δ L U : ℝ} {H : ℤ}
    (hδ : 0 < δ)
    (hseed : ∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc L U → (q:ℝ) ∈ S)
    (hpoints : ∀ z ∈ S, z ∈ Icc L U)
    (hscale : ∀ b d : ℤ, 0 < b → b ≤ H → 0 < d → d ≤ H → H < b+d →
      1 ≤ δ*((max b d:ℤ):ℝ)^2)
    {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d)
    (haS : (a:ℝ)/b ∈ S) (hcS : (c:ℝ)/d ∈ S)
    (hac : (a:ℝ)/b < (c:ℝ)/d)
    (hadj : ∀ z ∈ S, ¬ ((a:ℝ)/b < z ∧ z < (c:ℝ)/d))
    (hbcase : b ≤ H ∨ 1 ≤ δ*(b:ℝ)^2)
    (hdcase : d ≤ H ∨ 1 ≤ δ*(d:ℝ)^2) :
    1 ≤ δ*((max b d:ℤ):ℝ)^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.reference_adjacent_denominator_scale S (δ:=δ) (L:=L) (U:=U) (H:=H) hδ hseed hpoints hscale (a:=a) (b:=b) (c:=c) (d:=d) hb hd haS hcS hac hadj hbcase hdcase

end HuxleyIntervalScaleRegression

namespace HuxleyPhysicalReferenceRegression

open scoped Topology
open TaoTrudgianYang2025.HuxleyRationalPhase

example (S : Finset ℝ) {ε : ℝ}
    (hzero : (0:ℝ) ∈ S) (hone : (1:ℝ) ∈ S)
    (hpoints : ∀ z ∈ S, z ∈ Icc (0:ℝ) 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < |x-y|)
    {i j : ℤ} {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hne : (i:ℝ)+x ≠ (j:ℝ)+y) :
    ε < |((i:ℝ)+x)-((j:ℝ)+y)| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.integer_translate_reference_separation S (ε:=ε) hzero hone hpoints hsep (i:=i) (j:=j) (x:=x) (y:=y) hx hy hne

example {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ∃ H : ℤ, 2 ≤ H ∧ ∀ L U : ℤ, L ≤ U →
      ∃ T : Finset ℝ,
        (∀ q : ℚ, (q.den:ℤ) ≤ H →
          (q:ℝ) ∈ Icc (L:ℝ) ((U:ℝ)+1) → (q:ℝ) ∈ T) ∧
        (∀ z ∈ T, z ∈ Icc (L:ℝ) ((U:ℝ)+1)) ∧
        (∀ z ∈ T,
          (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
          (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
            1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
            (u:ℝ)/v ∈ Icc (L:ℝ) ((U:ℝ)+1) ∧ |m*v-u*n|=1)) ∧
        (∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ/4 < |x-y|) ∧
        (∀ x ∈ Icc (L:ℝ) ((U:ℝ)+1), ∃ y ∈ T, |x-y| ≤ 7*δ/4) ∧
        (∀ x ∈ T, ∀ y ∈ T, x < y →
          (∀ z ∈ T, ¬ (x < z ∧ z < y)) →
          δ/4 < y-x ∧ y-x ≤ 7*δ/2 ∧
          ∃ a b c d : ℤ, x=(a:ℝ)/b ∧ y=(c:ℝ)/d ∧
            IsCoprime a b ∧ IsCoprime c d ∧ 0 < b ∧ 0 < d ∧
            1 ≤ δ*((max b d:ℤ):ℝ)^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_source_interval_reference_system (δ:=δ) hδ hδmax

example
    (F : ℝ → ℝ) {σ c η y T M N R U x z : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*N*R^2=M^3)
    (hx : x ∈ Icc M (2*M)) (hz : z ∈ Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    |iteratedDeriv 2 f z/2-iteratedDeriv 2 f x/2| ≤ 7*U/(2*R^2) →
    |z-x| ≤ (14*σ/c)*U*N :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_preimage_width F (σ:=σ) (c:=c) (η:=η) (y:=y) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (x:=x) (z:=z) hσ hc hη hηmax hy hf hnegative hT hM hN hR hphase hx hz

example
    (F : ℝ → ℝ) {σ c J η T M N R U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) (hphase : T*N*R^2=M^3) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ H : ℤ, 2 ≤ H ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*U*N)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_reference_system F (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) hσ hc hJ hη hηmax hf hbound htests hnegative hT hM hN hR hU hUmax hphase

end HuxleyPhysicalReferenceRegression

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.reference_adjacent_denominator_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.integer_translate_reference_separation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_source_interval_reference_system
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_preimage_width
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_reference_system

example
    (S : Finset ℝ) {H a b c d : ℤ} {L U : ℝ}
    (hseed : ∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc L U → (q:ℝ) ∈ S)
    (hb : 0 < b) (hbH : b ≤ H) (hd : 0 < d) (hdH : d ≤ H)
    (hcopb : IsCoprime a b) (hcopd : IsCoprime c d)
    (haI : (a:ℝ)/b ∈ Icc L U) (hcI : (c:ℝ)/d ∈ Icc L U)
    (hac : (a:ℝ)/b < (c:ℝ)/d)
    (hadj : ∀ z ∈ S, ¬ ((a:ℝ)/b < z ∧ z < (c:ℝ)/d)) :
    c*b-a*d=1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.bounded_denominator_adjacent_unimodular S (H:=H) (a:=a) (b:=b) (c:=c) (d:=d) (L:=L) (U:=U) hseed hb hbH hd hdH hcopb hcopd haI hcI hac hadj

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (F : ℝ → ℝ) (η y x T M u : ℝ),
      0 < η → η ≤ 1/8 → y ∈ Icc (1:ℝ) 2 →
      0 < T → 0 < M → x ∈ Icc M (2*M) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let f := fun z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let h := fun z => iteratedDeriv 2 f z/2
      |u-h x| < ε*T/M^2 →
      ∃ z ∈ Ioo (3*M/4) (9*M/4), h z=u ∧
        ∀ w ∈ Ioo (3*M/4) (9*M/4), h w=u → w=z :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_root_neighborhood (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    (S : Finset ℝ) {H a b c d : ℤ} {L U : ℝ}
    (hseed : ∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ) ∈ Icc L U → (q:ℝ) ∈ S)
    (hlabels : ∀ z ∈ S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1))
    (hb : 0 < b) (hd : 0 < d)
    (hcopb : IsCoprime a b) (hcopd : IsCoprime c d)
    (haS : (a:ℝ)/b ∈ S) (hcS : (c:ℝ)/d ∈ S)
    (haI : (a:ℝ)/b ∈ Icc L U) (hcI : (c:ℝ)/d ∈ Icc L U)
    (hac : (a:ℝ)/b < (c:ℝ)/d)
    (hadj : ∀ z ∈ S, ¬ ((a:ℝ)/b < z ∧ z < (c:ℝ)/d)) :
    ∃ e r f s : ℤ, ((e=a ∧ r=b) ∨ (e=c ∧ r=d)) ∧
      r=max b d ∧ IsCoprime e r ∧ 0 < r ∧ 0 < s ∧ s ≤ r ∧ s ≤ H ∧
      (f:ℝ)/s ∈ S ∧ |e*s-f*r|=1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.reference_max_denominator_neighbor S (H:=H) (a:=a) (b:=b) (c:=c) (d:=d) (L:=L) (U:=U) hseed hlabels hb hd hcopb hcopd haS hcS haI hcI hac hadj

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (F : ℝ → ℝ) (η y x T M D : ℝ) (a b p q : ℤ),
      0 < η → η ≤ 1/8 → y ∈ Icc (1:ℝ) 2 →
      0 < T → 0 < M → x ∈ Icc M (2*M) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      0 < b → 0 < q → |a*q-p*b|=1 →
      let f := fun z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let h := fun z => iteratedDeriv 2 f z/2
      |(a:ℝ)/b-h x| ≤ D →
      D+1/((b:ℝ)*q) < ε*T/M^2 →
      ∃ z ∈ Ioo (3*M/4) (9*M/4), h z=(p:ℝ)/q ∧
        ∀ w ∈ Ioo (3*M/4) (9*M/4), h w=(p:ℝ)/q → w=z :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rational_neighbor_preimage (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example (S : Finset ℝ) {l u x : ℝ}
    (hl : l ∈ S) (hu : u ∈ S) (hlx : l ≤ x) (hxu : x ≤ u) (hx : x ∉ S) :
    ∃ a ∈ S, ∃ b ∈ S, a < x ∧ x < b ∧
      ∀ z ∈ S, ¬ (a < z ∧ z < b) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.finite_reference_bracket S (l:=l) (u:=u) (x:=x) hl hu hlx hxu hx

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (F : ℝ → ℝ) (η T M N R U : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 0 < M → 0 < N → 0 < R → 0 < U → U ≤ R^2 →
      T*N*R^2=M^3 →
      7*U/(2*R^2)+Real.sqrt U/R < ε*T/M^2 →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      ∃ H : ℤ, 2 ≤ H ∧ ∃ S : Finset ℝ,
        (∀ z ∈ S, |z| ≤ 3*J*T/(2*σ*M^2)+1) ∧
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → U/(4*R^2) < |a-b|) ∧
        ∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
          h y x ∈ S ∨
          ∃ a ∈ S, ∃ b ∈ S, a < h y x ∧ h y x < b ∧
            (∀ t ∈ S, ¬ (a < t ∧ t < b)) ∧
            U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
            ∃ e r p q : ℤ, ((e:ℝ)/r=a ∨ (e:ℝ)/r=b) ∧
              IsCoprime e r ∧ 0 < r ∧ 0 < q ∧ q ≤ r ∧ q ≤ H ∧
              R^2 ≤ U*(r:ℝ)^2 ∧ (p:ℝ)/q ∈ S ∧ |e*q-p*r|=1 ∧
              (∃ z ∈ Ioo (3*M/4) (9*M/4), h y z=(e:ℝ)/r) ∧
              (∃ w ∈ Ioo (3*M/4) (9*M/4), h y w=(p:ℝ)/q) ∧
              (∀ x₁ ∈ Icc M (2*M), ∀ x₂ ∈ Icc M (2*M),
                h y x₁ ∈ Icc a b → h y x₂ ∈ Icc a b →
                |x₂-x₁| ≤ (14*σ/c)*U*N) ∧
              (∀ (A : Finset ℤ) (z : ℤ → ℝ) (Z : ℝ),
                (∀ k ∈ A, Z+(k:ℝ)*N ≤ z k ∧ z k ≤ Z+((k:ℝ)+1)*N) →
                (∀ k ∈ A, z k ∈ Icc M (2*M) ∧ h y (z k) ∈ Icc a b) →
                (A.card:ℝ) ≤ 2+(14*σ/c)*U) ∧
              (∀ Z : ℝ, a ∈ Icc (h y M) (h y (2*M)) →
                b ∈ Icc (h y M) (h y (2*M)) →
                ∃ x₁ ∈ Icc M (2*M), ∃ x₂ ∈ Icc M (2*M),
                  h y x₁=a ∧ h y x₂=b ∧ ∃ A : Finset ℤ,
                    (∀ k : ℤ, k ∈ A ↔
                      x₁ ≤ Z+(k:ℝ)*N ∧ Z+(k:ℝ)*N ≤ x₂) ∧
                    (∀ k ∈ A, Z+(k:ℝ)*N ∈ Icc M (2*M) ∧
                      h y (Z+(k:ℝ)*N) ∈ Icc a b) ∧
                    (σ/(6*J))*U-1 ≤ (A.card:ℝ) ∧
                    (A.card:ℝ) ≤ (14*σ/c)*U+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_reference_gap (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.bounded_denominator_adjacent_unimodular
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_root_neighborhood
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.reference_max_denominator_neighbor
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rational_neighbor_preimage
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.finite_reference_bracket
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_reference_gap

example
    (S : Finset ℤ) (x : ℤ → ℝ) {N Z C : ℝ} (hN : 0 < N) (hC : 0 ≤ C)
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ x k ∧ x k ≤ Z+((k:ℝ)+1)*N)
    (hwidth : ∀ i ∈ S, ∀ j ∈ S, |x j-x i| ≤ C*N) :
    (S.card:ℝ) ≤ 2+C :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physical_block_count_of_pairwise_width S x (N:=N) (Z:=Z) (C:=C) hN hC hwindow hwidth

example
    {ε T M N R Q B : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hNR : N ≤ R^2)
    (hNM : N^2 ≤ M) (hB : 1 ≤ B) (hBε : 5 < ε*B)
    (hlarge : 2*B ≤ (N/Q)^((2:ℝ)/3))
    (hphase : T*N*R^2=M^3) :
    ∃ U : ℕ, 1 ≤ U ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      (U:ℝ) ≤ R^2 ∧
      B*(U:ℝ)*Q ≤ N ∧ B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      7*(U:ℝ)/(2*R^2)+Real.sqrt (U:ℝ)/R < ε*T/M^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_reference_block_length_enlarged_margin (ε:=ε) (T:=T) (M:=M) (N:=N) (R:=R) (Q:=Q) (B:=B) hM hN hR hRQ hQN hNR hNM hB hBε hlarge hphase

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (F : ℝ → ℝ) (η T M N R Q : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 0 < M → 0 < N → 1 ≤ R → R ≤ Q → Q ≤ N →
      N ≤ R^2 → N^2 ≤ M → 2*B ≤ (N/Q)^((2:ℝ)/3) →
      T*N*R^2=M^3 →
      ∃ U : ℕ, 1 ≤ U ∧
        (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
        (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
        (U:ℝ) ≤ R^2 ∧ B*(U:ℝ)*Q ≤ N ∧ B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      ∃ H : ℤ, 2 ≤ H ∧ ∃ S : Finset ℝ,
        (∀ z ∈ S, |z| ≤ 3*J*T/(2*σ*M^2)+1) ∧
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (U:ℝ)/(4*R^2) < |a-b|) ∧
        ∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
          h y x ∈ S ∨
          ∃ a ∈ S, ∃ b ∈ S, a < h y x ∧ h y x < b ∧
            (∀ t ∈ S, ¬ (a < t ∧ t < b)) ∧
            (U:ℝ)/(4*R^2) < b-a ∧ b-a ≤ 7*(U:ℝ)/(2*R^2) ∧
            ∃ e r p q : ℤ, ((e:ℝ)/r=a ∨ (e:ℝ)/r=b) ∧
              IsCoprime e r ∧ 0 < r ∧ 0 < q ∧ q ≤ r ∧ q ≤ H ∧
              R^2 ≤ (U:ℝ)*(r:ℝ)^2 ∧ (p:ℝ)/q ∈ S ∧ |e*q-p*r|=1 ∧
              (∃ z ∈ Ioo (3*M/4) (9*M/4), h y z=(e:ℝ)/r) ∧
              (∃ w ∈ Ioo (3*M/4) (9*M/4), h y w=(p:ℝ)/q) ∧
              (∀ x₁ ∈ Icc M (2*M), ∀ x₂ ∈ Icc M (2*M),
                h y x₁ ∈ Icc a b → h y x₂ ∈ Icc a b →
                |x₂-x₁| ≤ (14*σ/c)*(U:ℝ)*N) ∧
              (∀ (A : Finset ℤ) (z : ℤ → ℝ) (Z : ℝ),
                (∀ k ∈ A, Z+(k:ℝ)*N ≤ z k ∧ z k ≤ Z+((k:ℝ)+1)*N) →
                (∀ k ∈ A, z k ∈ Icc M (2*M) ∧ h y (z k) ∈ Icc a b) →
                (A.card:ℝ) ≤ 2+(14*σ/c)*(U:ℝ)) ∧
              (∀ Z : ℝ, a ∈ Icc (h y M) (h y (2*M)) →
                b ∈ Icc (h y M) (h y (2*M)) →
                ∃ x₁ ∈ Icc M (2*M), ∃ x₂ ∈ Icc M (2*M),
                  h y x₁=a ∧ h y x₂=b ∧ ∃ A : Finset ℤ,
                    (∀ k : ℤ, k ∈ A ↔
                      x₁ ≤ Z+(k:ℝ)*N ∧ Z+(k:ℝ)*N ≤ x₂) ∧
                    (∀ k ∈ A, Z+(k:ℝ)*N ∈ Icc M (2*M) ∧
                      h y (Z+(k:ℝ)*N) ∈ Icc a b) ∧
                    (σ/(6*J))*(U:ℝ)-1 ≤ (A.card:ℝ) ∧
                    (A.card:ℝ) ≤ (14*σ/c)*(U:ℝ)+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_gap (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    (F : ℝ → ℝ) {σ J η y T M N R U x z : ℝ}
    (hσ : 0 < σ) (hJ : 0 < J) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*N*R^2=M^3)
    (hx : x ∈ Icc (3*M/4) (9*M/4)) (hz : z ∈ Icc (3*M/4) (9*M/4)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    U/(4*R^2) ≤ |iteratedDeriv 2 f z/2-iteratedDeriv 2 f x/2| →
    (σ/(6*J))*U*N ≤ |z-x| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_preimage_width_lower F (σ:=σ) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (x:=x) (z:=z) hσ hJ hη hηmax hy hf hbound hT hM hN hR hphase hx hz

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physical_block_count_of_pairwise_width
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_reference_block_length_enlarged_margin
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_gap
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_preimage_width_lower

open scoped FourierTransform BigOperators

example {N Z x z : ℝ} (hN : 0 < N) (hxz : x ≤ z) :
    ∃ A : Finset ℤ,
      (∀ k : ℤ, k ∈ A ↔ x ≤ Z+(k:ℝ)*N ∧ Z+(k:ℝ)*N ≤ z) ∧
      (z-x)/N-1 ≤ (A.card:ℝ) ∧ (A.card:ℝ) ≤ (z-x)/N+1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physical_grid_interval_card (N:=N) (Z:=Z) (x:=x) (z:=z) hN hxz

example
    (F : ℝ → ℝ) {σ c η y T M : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    StrictMonoOn (fun w => iteratedDeriv 2 f w/2) (Icc (3*M/4) (9*M/4)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_curvature_strictMono F (σ:=σ) (c:=c) (η:=η) (y:=y) (T:=T) (M:=M) hσ hc hη hηmax hy hf hnegative hT hM

example
    (F : ℝ → ℝ) {σ c J η y T M N R U x z Z : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hphase : T*N*R^2=M^3) (hx : x ∈ Icc M (2*M)) (hz : z ∈ Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    U/(4*R^2) ≤ h z-h x → h z-h x ≤ 7*U/(2*R^2) →
    ∃ A : Finset ℤ,
      (∀ k : ℤ, k ∈ A ↔ x ≤ Z+(k:ℝ)*N ∧ Z+(k:ℝ)*N ≤ z) ∧
      (∀ k ∈ A, Z+(k:ℝ)*N ∈ Icc M (2*M) ∧
        h (Z+(k:ℝ)*N) ∈ Icc (h x) (h z)) ∧
      (σ/(6*J))*U-1 ≤ (A.card:ℝ) ∧
      (A.card:ℝ) ≤ (14*σ/c)*U+1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_gap_grid_count F (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (x:=x) (z:=z) (Z:=Z) hσ hc hJ hη hηmax hy hf hbound hnegative hT hM hN hR hU hphase hx hz

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ) (y : ι → ℝ)
      (L : ι → ℤ) (H : ι → ℕ) (N : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i ∈ Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ) ∈ Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      (4*σ/c)*R^2+8*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let lambda := c/(4*σ*(N:ℝ)*R^2)
      let Lambda := 3*J/(2*σ*(N:ℝ)*R^2)
      let z := fun i => (L i:ℝ)-2*(N:ℝ)
      ∃ (a : ι → ℤ) (q : ι → ℕ) (c : ι → ℝ) (m : ι → ℤ),
        (∀ i∈S, 0 < q i ∧ q i ≤ N ∧ IsCoprime (a i) (q i:ℤ) ∧
          |iteratedDeriv 2 (f i) (z i)/2-(a i:ℝ)/(q i:ℝ)| ≤ 1/(((N:ℝ)+1)*q i) ∧
          |c i-z i| ≤ 1/(lambda*((N:ℝ)+1)*q i) ∧
          iteratedDeriv 2 (f i) (c i)/2=(a i:ℝ)/(q i:ℝ) ∧
          |(m i:ℝ)-c i| ≤ 1/2 ∧
          |(m i:ℝ)-z i| ≤ 1/(lambda*((N:ℝ)+1)*q i)+1/2 ∧
          |iteratedDeriv 2 (f i) (m i)/2-(a i:ℝ)/(q i:ℝ)| ≤ Lambda/2) ∧
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let A := fun i => (L i-m i).toNat
      let G := S.filter (fun i => 3 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈G, N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 21*Lambda*(N:ℝ)^3 ≤ K₀ →
      ∃ r : ι → ℤ, (∀ i∈G, (q i:ℤ)∣a i*r i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(r i:ℝ)*b i p/q i,-(r i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
        C*((∑ i∈S.filter (fun i => lambda*(q i:ℝ)^2*N < 3),(H i:ℝ))+
          (1+Real.log K₀)*
          (∑ i∈G, ∑ p : Fin 2,
            (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
            ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
              GafniTao.fordAdditiveCharacter (∑ e,x i p e*
                (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                  Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) e)‖)+
          ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_prescribed_interval_minor_arcs (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physical_grid_interval_card
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_curvature_strictMono
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_gap_grid_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_prescribed_interval_minor_arcs

example
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (F : ℝ → ℝ)
    (k : ι → ℤ) (N Bmul : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hNM : (N:ℝ) ≤ M) (hphase : T*(N:ℝ)*R^2=M^3)
    (hmul : ∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul)
    (hpoints : ∀ i∈S, s+(N:ℝ)*(k i:ℝ) ∈ Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let t := fun i => s+(N:ℝ)*(k i:ℝ)
    let v := fun i => iteratedDeriv 2 f (t i)/2
    let delta := c/(16*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈S, z i∈Ioo (t i-(N:ℝ)/4) (t i+(N:ℝ)/4) ∧
        iteratedDeriv 2 f (z i)/2=(r i:ℝ) ∧
        (r i:ℝ)∈Ioo (v i-delta) (v i+delta) ∧
        ∀ a : ℚ, (a:ℝ)∈Ioo (v i-delta) (v i+delta) → (r i).den ≤ a.den) ∧
      (∀ i∈S, ∀ a∈Icc M (2*M), ∀ b∈Icc M (2*M),
        a+(N:ℝ)/4 ≤ t i → t i ≤ b-(N:ℝ)/4 →
        (r i:ℝ)∈Ioo (iteratedDeriv 2 f a/2) (iteratedDeriv 2 f b/2)) ∧
      ∀ Q : ℕ, 2 ≤ Q →
        let G := S.filter (fun i => Q ≤ (r i).den)
        let D := 16*σ*R^2/(c*(Q:ℝ))
        (G.card:ℝ) ≤ Bmul*(4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_minimal_curvature_arc_count (ι:=ι) S F k N Bmul s (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (R:=R) hσ hc hJ hη hηmax hy hf hbound hnegative hT hM hN hR hNM hphase hmul hpoints

example
    (F : ℝ → ℝ) (N : ℕ) {σ c J η y T M R U x z s : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hU : 0 < U)
    (hNM : (N:ℝ) ≤ M) (hUlarge : 3*J ≤ σ*U)
    (hphase : T*(N:ℝ)*R^2=M^3) (hx : x∈Icc M (2*M)) (hz : z∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(16*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    U/(4*R^2) ≤ h z-h x → h z-h x ≤ 7*U/(2*R^2) →
    ∃ A : Finset ℤ, ∃ (r : ℤ → ℚ) (w : ℤ → ℝ),
      (∀ k : ℤ, k∈A ↔ x+(N:ℝ)/4 ≤ t k ∧ t k ≤ z-(N:ℝ)/4) ∧
      (∀ k∈A, w k∈Ioo x z ∧ h (w k)=(r k:ℝ) ∧
        (r k:ℝ)∈Ioo (h x) (h z) ∧
        (r k:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) ∧
        ∀ a : ℚ, (a:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) → (r k).den ≤ a.den) ∧
      (σ/(6*J))*U-3/2 ≤ (A.card:ℝ) ∧
      (A.card:ℝ) ≤ (14*σ/c)*U+1/2 ∧
      ∀ Q : ℕ, 2 ≤ Q →
        let G := A.filter (fun k => Q ≤ (r k).den)
        let D := 16*σ*R^2/(c*(Q:ℝ))
        (G.card:ℝ) ≤ 4*(Vbound+1)*D^2+D*(2+Real.log (D+1)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_gap_minimal_arcs F N (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (R:=R) (U:=U) (x:=x) (z:=z) (s:=s) hσ hc hJ hη hηmax hy hf hbound hnegative hT hM hN hR hU hNM hUlarge hphase hx hz

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (F : ℝ → ℝ) (N : ℕ) (η T M R Q : ℝ),
      0 < N → 0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 0 < M → 1 ≤ R → R ≤ Q → Q ≤ (N:ℝ) →
      (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      2*B ≤ ((N:ℝ)/Q)^((2:ℝ)/3) →
      6*B*J ≤ σ*((N:ℝ)/Q)^((2:ℝ)/3) →
      T*(N:ℝ)*R^2=M^3 →
      ∃ U : ℕ, 1 ≤ U ∧
        ((N:ℝ)/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
        (U:ℝ) ≤ ((N:ℝ)/Q)^((2:ℝ)/3)/B ∧
        (U:ℝ) ≤ R^2 ∧ B*(U:ℝ)*Q ≤ (N:ℝ) ∧
        B^2*(U:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let delta := c/(16*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ H : ℤ, 2 ≤ H ∧ ∃ S : Finset ℝ,
        (∀ v ∈ S, |v| ≤ 3*J*T/(2*σ*M^2)+1) ∧
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (U:ℝ)/(4*R^2) < |a-b|) ∧
        ∀ y ∈ Icc (1:ℝ) 2, ∀ x∈Icc M (2*M),
          h y x∈S ∨
          ∃ a∈S, ∃ b∈S, a<h y x ∧ h y x<b ∧
            (∀ v∈S, ¬ (a<v ∧ v<b)) ∧
            (U:ℝ)/(4*R^2)<b-a ∧ b-a≤7*(U:ℝ)/(2*R^2) ∧
            ∃ e r₀ p q : ℤ, ((e:ℝ)/r₀=a ∨ (e:ℝ)/r₀=b) ∧
              IsCoprime e r₀ ∧ 0<r₀ ∧ 0<q ∧ q≤r₀ ∧ q≤H ∧
              R^2≤(U:ℝ)*(r₀:ℝ)^2 ∧ (p:ℝ)/q∈S ∧ |e*q-p*r₀|=1 ∧
              (∃ z∈Ioo (3*M/4) (9*M/4), h y z=(e:ℝ)/r₀) ∧
              (∃ z∈Ioo (3*M/4) (9*M/4), h y z=(p:ℝ)/q) ∧
              (∀ s : ℝ, a∈Icc (h y M) (h y (2*M)) →
                b∈Icc (h y M) (h y (2*M)) →
                ∃ x₁∈Icc M (2*M), ∃ x₂∈Icc M (2*M),
                  h y x₁=a ∧ h y x₂=b ∧
                  ∃ A : Finset ℤ, ∃ (r : ℤ→ℚ) (w : ℤ→ℝ),
                    (∀ k : ℤ, k∈A ↔
                      x₁+(N:ℝ)/4 ≤ s+(N:ℝ)*k ∧ s+(N:ℝ)*k ≤ x₂-(N:ℝ)/4) ∧
                    (∀ k∈A, w k∈Ioo x₁ x₂ ∧ h y (w k)=(r k:ℝ) ∧
                      (r k:ℝ)∈Ioo a b ∧
                      (r k:ℝ)∈Ioo (h y (s+(N:ℝ)*k)-delta) (h y (s+(N:ℝ)*k)+delta) ∧
                      ∀ v : ℚ, (v:ℝ)∈Ioo
                        (h y (s+(N:ℝ)*k)-delta) (h y (s+(N:ℝ)*k)+delta) →
                        (r k).den ≤ v.den) ∧
                    (σ/(6*J))*(U:ℝ)-3/2 ≤ (A.card:ℝ) ∧
                    (A.card:ℝ) ≤ (14*σ/c)*(U:ℝ)+1/2 ∧
                    ∀ K : ℕ, 2 ≤ K →
                      let G := A.filter (fun k => K ≤ (r k).den)
                      let D := 16*σ*R^2/(c*(K:ℝ))
                      (G.card:ℝ) ≤ 4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_arcs (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_minimal_curvature_arc_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reference_gap_minimal_arcs
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_arcs


example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (r : ι → ℚ) (z : ι → ℝ)
      (N : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, z i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/4)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/4) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(N:ℝ)^3 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_chosen_arcs_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι) (F : ℝ → ℝ)
      (k : ι → ℤ) (H : ι → ℕ) (N Bmul : ℕ) (s : ℤ) (η y T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, (s:ℝ)+(N:ℝ)*(k i:ℝ)∈Icc M (2*M)) →
      let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let t := fun i => (s:ℝ)+(N:ℝ)*(k i:ℝ)
      let L := fun i => s+(N:ℤ)*k i+2*(N:ℤ)
      let delta := c/(16*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ (r : ι → ℚ) (z : ι → ℝ),
        (∀ i∈S, z i∈Ioo (t i-(N:ℝ)/4) (t i+(N:ℝ)/4) ∧
          iteratedDeriv 2 f (z i)/2=(r i:ℝ) ∧
          (r i:ℝ)∈Ioo (iteratedDeriv 2 f (t i)/2-delta) (iteratedDeriv 2 f (t i)/2+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (iteratedDeriv 2 f (t i)/2-delta)
            (iteratedDeriv 2 f (t i)/2+delta) → (r i).den ≤ a.den) ∧
        (∀ i∈S, ∀ a∈Icc M (2*M), ∀ b∈Icc M (2*M),
          a+(N:ℝ)/4 ≤ t i → t i ≤ b-(N:ℝ)/4 →
          (r i:ℝ)∈Ioo (iteratedDeriv 2 f a/2) (iteratedDeriv 2 f b/2)) ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 16*σ*R^2/(c*(Q:ℝ))
          ((S.filter (fun i => Q ≤ (r i).den)).card:ℝ) ≤
            Bmul*(4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 f (m i)/6
      let ℓ := fun i => deriv f (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_minimal_arcs_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (N : ℕ) (s : ℤ) (H : ℤ → ℕ)
      (η y T M R U x₁ x₂ : ℝ),
      1 ≤ N → (∀ k, H k ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U → x₁∈Icc M (2*M) → x₂∈Icc M (2*M) →
      let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun w => iteratedDeriv 2 f w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(16*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      U/(4*R^2) ≤ h x₂-h x₁ → h x₂-h x₁ ≤ 7*U/(2*R^2) →
      ∃ S : Finset ℤ, ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
        (∀ k : ℤ, k∈S ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈S, z k∈Ioo x₁ x₂ ∧ h (z k)=(r k:ℝ) ∧
          (r k:ℝ)∈Ioo (h x₁) (h x₂) ∧
          (r k:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) → (r k).den ≤ a.den) ∧
        (σ/(6*J))*U-3/2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ (14*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 16*σ*R^2/(c*(Q:ℝ))
          ((S.filter (fun k => Q ≤ (r k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 f (m i)/6
      let ℓ := fun i => deriv f (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_interior_gap_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_chosen_arcs_fourier
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_minimal_arcs_fourier
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_interior_gap_fourier


example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (N : ℕ) (η T M R Q : ℝ),
      0 < N → 0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 0 < M → 1 ≤ R → R ≤ Q → Q ≤ (N:ℝ) →
      (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      2*B ≤ ((N:ℝ)/Q)^((2:ℝ)/3) →
      6*B*J ≤ σ*((N:ℝ)/Q)^((2:ℝ)/3) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      ∃ U : ℕ, 1 ≤ U ∧
        ((N:ℝ)/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
        (U:ℝ) ≤ ((N:ℝ)/Q)^((2:ℝ)/3)/B ∧
        (U:ℝ) ≤ R^2 ∧ B*(U:ℝ)*Q ≤ (N:ℝ) ∧
        B^2*(U:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let delta := c/(16*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ H : ℤ, 2 ≤ H ∧ ∃ S : Finset ℝ,
        (∀ v ∈ S, |v| ≤ 3*J*T/(2*σ*M^2)+1) ∧
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (U:ℝ)/(4*R^2) < |a-b|) ∧
        ∀ y ∈ Icc (1:ℝ) 2, ∀ x∈Icc M (2*M),
          h y x∈S ∨
          ∃ a∈S, ∃ b∈S, a<h y x ∧ h y x<b ∧
            (∀ v∈S, ¬ (a<v ∧ v<b)) ∧
            (U:ℝ)/(4*R^2)<b-a ∧ b-a≤7*(U:ℝ)/(2*R^2) ∧
            ∃ e r₀ p q : ℤ, ((e:ℝ)/r₀=a ∨ (e:ℝ)/r₀=b) ∧
              IsCoprime e r₀ ∧ 0<r₀ ∧ 0<q ∧ q≤r₀ ∧ q≤H ∧
              R^2≤(U:ℝ)*(r₀:ℝ)^2 ∧ (p:ℝ)/q∈S ∧ |e*q-p*r₀|=1 ∧
              (∃ z∈Ioo (3*M/4) (9*M/4), h y z=(e:ℝ)/r₀) ∧
              (∃ z∈Ioo (3*M/4) (9*M/4), h y z=(p:ℝ)/q) ∧
              (∀ (s : ℤ) (Hlen : ℤ → ℕ), (∀ k, Hlen k ≤ N) →
                a∈Icc (h y M) (h y (2*M)) → b∈Icc (h y M) (h y (2*M)) →
                ∃ x₁∈Icc M (2*M), ∃ x₂∈Icc M (2*M),
                  h y x₁=a ∧ h y x₂=b ∧
                let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
                let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      ∃ Agrid : Finset ℤ, ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
        (∀ k : ℤ, k∈Agrid ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈Agrid, z k∈Ioo x₁ x₂ ∧ (h y) (z k)=(r k:ℝ) ∧
          (r k:ℝ)∈Ioo ((h y) x₁) ((h y) x₂) ∧
          (r k:ℝ)∈Ioo ((h y) (t k)-delta) ((h y) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h y) (t k)-delta) ((h y) (t k)+delta) → (r k).den ≤ a.den) ∧
        (σ/(6*J))*(U:ℝ)-3/2 ≤ (Agrid.card:ℝ) ∧ (Agrid.card:ℝ) ≤ (14*σ/c)*(U:ℝ)+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 16*σ*R^2/(c*(Q:ℝ))
          ((Agrid.filter (fun k => Q ≤ (r k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f y) (m i)/6
      let ℓ := fun i => deriv (f y) (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := Agrid.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈Agrid, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Agrid, ‖∑ n∈Finset.Ioc (L i) (L i+Hlen i),(𝐞 ((f y) n):ℂ)‖) ≤
          C*((∑ i∈Agrid.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(Hlen i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2)))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_fourier


example
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℝ) (z : ι → ℝ) (r : ι → ℚ) (v : ι → ℤ)
    (Q K₀ : ℕ) [NeZero K₀] (μ₀ U₀ : ℝ) (hμ₀ : 0 < μ₀)
    (hμbounds : ∀ i∈S, μ₀ ≤ iteratedDeriv 3 (f i) (round (z i))/6 ∧
      iteratedDeriv 3 (f i) (round (z i))/6 ≤ U₀)
    (hlevel : ∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ))
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den)
    (hinv : ∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) :
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ A : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      ∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.source_arc_fourier_cloud_matrices (ι:=ι) S f z r v Q K₀ μ₀ U₀ hμ₀ hμbounds hlevel hden hinv

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.source_arc_fourier_cloud_matrices


example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (r : ι → ℚ) (z : ι → ℝ)
      (N : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, z i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/4)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/4) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_chosen_arcs_band_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_chosen_arcs_band_fourier




example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι) (F : ℝ → ℝ)
      (k : ι → ℤ) (H : ι → ℕ) (N Bmul : ℕ) (s : ℤ) (η y T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, (s:ℝ)+(N:ℝ)*(k i:ℝ)∈Icc M (2*M)) →
      let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let t := fun i => (s:ℝ)+(N:ℝ)*(k i:ℝ)
      let L := fun i => s+(N:ℤ)*k i+2*(N:ℤ)
      let delta := c/(16*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ (r : ι → ℚ) (z : ι → ℝ),
        (∀ i∈S, z i∈Ioo (t i-(N:ℝ)/4) (t i+(N:ℝ)/4) ∧
          iteratedDeriv 2 f (z i)/2=(r i:ℝ) ∧
          (r i:ℝ)∈Ioo (iteratedDeriv 2 f (t i)/2-delta) (iteratedDeriv 2 f (t i)/2+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (iteratedDeriv 2 f (t i)/2-delta)
            (iteratedDeriv 2 f (t i)/2+delta) → (r i).den ≤ a.den) ∧
        (∀ i∈S, ∀ a∈Icc M (2*M), ∀ b∈Icc M (2*M),
          a+(N:ℝ)/4 ≤ t i → t i ≤ b-(N:ℝ)/4 →
          (r i:ℝ)∈Ioo (iteratedDeriv 2 f a/2) (iteratedDeriv 2 f b/2)) ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 16*σ*R^2/(c*(Q:ℝ))
          ((S.filter (fun i => Q ≤ (r i).den)).card:ℝ) ≤
            Bmul*(4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 f (m i)/6
      let ℓ := fun i => deriv f (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_minimal_arcs_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_minimal_arcs_fourier

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (N : ℕ) (s : ℤ) (H : ℤ → ℕ)
      (η y T M R U x₁ x₂ : ℝ),
      1 ≤ N → (∀ k, H k ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U → x₁∈Icc M (2*M) → x₂∈Icc M (2*M) →
      let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun w => iteratedDeriv 2 f w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(16*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      U/(4*R^2) ≤ h x₂-h x₁ → h x₂-h x₁ ≤ 7*U/(2*R^2) →
      ∃ S : Finset ℤ, ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
        (∀ k : ℤ, k∈S ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈S, z k∈Ioo x₁ x₂ ∧ h (z k)=(r k:ℝ) ∧
          (r k:ℝ)∈Ioo (h x₁) (h x₂) ∧
          (r k:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) → (r k).den ≤ a.den) ∧
        (σ/(6*J))*U-3/2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ (14*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 16*σ*R^2/(c*(Q:ℝ))
          ((S.filter (fun k => Q ≤ (r k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 f (m i)/6
      let ℓ := fun i => deriv f (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := S.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_interior_gap_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_interior_gap_fourier

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (N : ℕ) (η T M R Q : ℝ),
      0 < N → 0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 0 < M → 1 ≤ R → R ≤ Q → Q ≤ (N:ℝ) →
      (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      2*B ≤ ((N:ℝ)/Q)^((2:ℝ)/3) →
      6*B*J ≤ σ*((N:ℝ)/Q)^((2:ℝ)/3) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      ∃ U : ℕ, 1 ≤ U ∧
        ((N:ℝ)/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
        (U:ℝ) ≤ ((N:ℝ)/Q)^((2:ℝ)/3)/B ∧
        (U:ℝ) ≤ R^2 ∧ B*(U:ℝ)*Q ≤ (N:ℝ) ∧
        B^2*(U:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let delta := c/(16*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ H : ℤ, 2 ≤ H ∧ ∃ S : Finset ℝ,
        (∀ v ∈ S, |v| ≤ 3*J*T/(2*σ*M^2)+1) ∧
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (U:ℝ)/(4*R^2) < |a-b|) ∧
        ∀ y ∈ Icc (1:ℝ) 2, ∀ x∈Icc M (2*M),
          h y x∈S ∨
          ∃ a∈S, ∃ b∈S, a<h y x ∧ h y x<b ∧
            (∀ v∈S, ¬ (a<v ∧ v<b)) ∧
            (U:ℝ)/(4*R^2)<b-a ∧ b-a≤7*(U:ℝ)/(2*R^2) ∧
            ∃ e r₀ p q : ℤ, ((e:ℝ)/r₀=a ∨ (e:ℝ)/r₀=b) ∧
              IsCoprime e r₀ ∧ 0<r₀ ∧ 0<q ∧ q≤r₀ ∧ q≤H ∧
              R^2≤(U:ℝ)*(r₀:ℝ)^2 ∧ (p:ℝ)/q∈S ∧ |e*q-p*r₀|=1 ∧
              (∃ z∈Ioo (3*M/4) (9*M/4), h y z=(e:ℝ)/r₀) ∧
              (∃ z∈Ioo (3*M/4) (9*M/4), h y z=(p:ℝ)/q) ∧
              (∀ (s : ℤ) (Hlen : ℤ → ℕ), (∀ k, Hlen k ≤ N) →
                a∈Icc (h y M) (h y (2*M)) → b∈Icc (h y M) (h y (2*M)) →
                ∃ x₁∈Icc M (2*M), ∃ x₂∈Icc M (2*M),
                  h y x₁=a ∧ h y x₂=b ∧
                let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
                let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      ∃ Agrid : Finset ℤ, ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
        (∀ k : ℤ, k∈Agrid ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈Agrid, z k∈Ioo x₁ x₂ ∧ (h y) (z k)=(r k:ℝ) ∧
          (r k:ℝ)∈Ioo ((h y) x₁) ((h y) x₂) ∧
          (r k:ℝ)∈Ioo ((h y) (t k)-delta) ((h y) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h y) (t k)-delta) ((h y) (t k)+delta) → (r k).den ≤ a.den) ∧
        (σ/(6*J))*(U:ℝ)-3/2 ≤ (Agrid.card:ℝ) ∧ (Agrid.card:ℝ) ≤ (14*σ/c)*(U:ℝ)+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 16*σ*R^2/(c*(Q:ℝ))
          ((Agrid.filter (fun k => Q ≤ (r k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f y) (m i)/6
      let ℓ := fun i => deriv (f y) (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := Agrid.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈Agrid, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Agrid, ‖∑ n∈Finset.Ioc (L i) (L i+Hlen i),(𝐞 ((f y) n):ℂ)‖) ≤
          C*((∑ i∈Agrid.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(Hlen i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2)))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_fourier


example
    (F : ℝ → ℝ) {σ c J η y z T M N R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 0 < N) (hR : 0 < R)
    (hz : z∈Icc M (2*M)) (hphase : T*N*R^2=M^3) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    c/(12*σ*N*R^2) ≤ iteratedDeriv 3 f (round z)/6 ∧
      iteratedDeriv 3 f (round z)/6 ≤ J/(2*σ*N*R^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rounded_cubic_scales F (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (z:=z) (T:=T) (M:=M) (N:=N) (R:=R) hσ hc hJ hη hηmax hy hf hbound hnegative hM hN hR hz hphase

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rounded_cubic_scales


example
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F : ℝ → ℝ) (y z : ι → ℝ) (r : ι → ℚ) (v : ι → ℤ)
    (Q K₀ : ℕ) [NeZero K₀] {σ c J η T M N R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 0 < N) (hR : 0 < R)
    (hz : ∀ i∈S, z i∈Icc M (2*M)) (hphase : T*N*R^2=M^3) :
    let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c/(12*σ*N*R^2)
    let U₀ := J/(2*σ*N*R^2)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ A : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      ∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_fourier_cloud_matrices (ι:=ι) S F y z r v Q K₀ (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (N:=N) (R:=R) hσ hc hJ hη hηmax hy hf hbound hnegative hM hN hR hz hphase

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_fourier_cloud_matrices

example
    {σ J M N R : ℝ} (hJ : 0 < J) (hσ : 7203*J ≤ σ)
    (hN : 29 ≤ N) (hR : 0 < R) (hRN : R ≤ N)
    (hNR : N ≤ R^2) (hNM : N^2 ≤ M)
    (hquartic : N^10 ≤ M^3*R^7) :
    7*N+2 ≤ M/4 ∧ (3*J/σ)*(6*N+1)^4 ≤ M*N*R^2 ∧
      (3*J/(4*σ))*(6*N+1)^2 ≤ N*R^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_fourier_budgets (σ:=σ) (J:=J) (M:=M) (N:=N) (R:=R) hJ hσ hN hR hRN hNR hNM hquartic

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_fourier_budgets

example
    {σ c J : ℝ} (hσ : 7203*J ≤ σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (N : ℕ) (η T M R Q : ℝ),
      29 ≤ N → 0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 0 < M → 1 ≤ R → R ≤ Q → Q ≤ (N:ℝ) →
      (N:ℝ) ≤ R^2 → (N:ℝ)^2 ≤ M →
      2*B ≤ ((N:ℝ)/Q)^((2:ℝ)/3) →
      6*B*J ≤ σ*((N:ℝ)/Q)^((2:ℝ)/3) →
      T*(N:ℝ)*R^2=M^3 →
      (N:ℝ)^10 ≤ M^3*R^7 →
      ∃ U : ℕ, 1 ≤ U ∧
        ((N:ℝ)/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
        (U:ℝ) ≤ ((N:ℝ)/Q)^((2:ℝ)/3)/B ∧
        (U:ℝ) ≤ R^2 ∧ B*(U:ℝ)*Q ≤ (N:ℝ) ∧
        B^2*(U:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let delta := c/(16*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ H : ℤ, 2 ≤ H ∧ ∃ S : Finset ℝ,
        (∀ v ∈ S, |v| ≤ 3*J*T/(2*σ*M^2)+1) ∧
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (U:ℝ)/(4*R^2) < |a-b|) ∧
        ∀ y ∈ Icc (1:ℝ) 2, ∀ x∈Icc M (2*M),
          h y x∈S ∨
          ∃ a∈S, ∃ b∈S, a<h y x ∧ h y x<b ∧
            (∀ v∈S, ¬ (a<v ∧ v<b)) ∧
            (U:ℝ)/(4*R^2)<b-a ∧ b-a≤7*(U:ℝ)/(2*R^2) ∧
            ∃ e r₀ p q : ℤ, ((e:ℝ)/r₀=a ∨ (e:ℝ)/r₀=b) ∧
              IsCoprime e r₀ ∧ 0<r₀ ∧ 0<q ∧ q≤r₀ ∧ q≤H ∧
              R^2≤(U:ℝ)*(r₀:ℝ)^2 ∧ (p:ℝ)/q∈S ∧ |e*q-p*r₀|=1 ∧
              (∃ z∈Ioo (3*M/4) (9*M/4), h y z=(e:ℝ)/r₀) ∧
              (∃ z∈Ioo (3*M/4) (9*M/4), h y z=(p:ℝ)/q) ∧
              (∀ (s : ℤ) (Hlen : ℤ → ℕ), (∀ k, Hlen k ≤ N) →
                a∈Icc (h y M) (h y (2*M)) → b∈Icc (h y M) (h y (2*M)) →
                ∃ x₁∈Icc M (2*M), ∃ x₂∈Icc M (2*M),
                  h y x₁=a ∧ h y x₂=b ∧
                let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
                let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      ∃ Agrid : Finset ℤ, ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
        (∀ k : ℤ, k∈Agrid ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈Agrid, z k∈Ioo x₁ x₂ ∧ (h y) (z k)=(r k:ℝ) ∧
          (r k:ℝ)∈Ioo ((h y) x₁) ((h y) x₂) ∧
          (r k:ℝ)∈Ioo ((h y) (t k)-delta) ((h y) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h y) (t k)-delta) ((h y) (t k)+delta) → (r k).den ≤ a.den) ∧
        (σ/(6*J))*(U:ℝ)-3/2 ≤ (Agrid.card:ℝ) ∧ (Agrid.card:ℝ) ≤ (14*σ/c)*(U:ℝ)+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 16*σ*R^2/(c*(Q:ℝ))
          ((Agrid.filter (fun k => Q ≤ (r k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f y) (m i)/6
      let ℓ := fun i => deriv (f y) (m i)
      let lambda := c/(12*σ*(N:ℝ)*R^2)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      let G := Agrid.filter (fun i => q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)
      (∀ i∈Agrid, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ Q₀ : ℕ, (∀ i∈G, q i ≤ Q₀) →
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q₀:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Agrid, ‖∑ n∈Finset.Ioc (L i) (L i+Hlen i),(𝐞 ((f y) n):ℂ)‖) ≤
          C*((∑ i∈Agrid.filter (fun i => ¬ (q i ≤ N ∧ 1 ≤ lambda*(q i:ℝ)^2*N)),(Hlen i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2)))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_source_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_selected_reference_source_fourier

example
    (a b c d : ℤ) {h h₁ : ℝ}
    (hdet : a*d-b*c=1)
    (hh : |h| ≤ 1/6) (hh₁ : |h₁| ≤ 1/6)
    (haction : |(c:ℝ)*h| ≤ 1/4)
    (ht : (1:ℝ)/2 ≤ (c:ℝ)*h+d ∧ (c:ℝ)*h+d ≤ 2)
    (hmap : ((a:ℝ)*h+b)/((c:ℝ)*h+d)=h₁) :
    a=1 ∧ b=0 ∧ d=1 ∧ h₁=h/((c:ℝ)*h+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.small_curvature_small_action_lower_triangular a b c d (h:=h) (h₁:=h₁) hdet hh hh₁ haction ht hmap

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.small_curvature_small_action_lower_triangular

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb Δ T M N Z : ℝ) (a₀ b₀ c₀ d₀ : ℤ)
        (S : Finset ℤ) (xa xb : ℤ → ℝ),
      0 < η → η ≤ η₀ → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ →
      a₀*d₀-b₀*c₀=1 →
      (3*U/σ)*T/(2*M^2) ≤ 1/6 →
      |(c₀:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ 1/4 →
      ((yb-ya,T*(c₀:ℝ)/(2*M^2)):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
      (∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) →
      (∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M)) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let h := fun y z => iteratedDeriv 2 (f y) z/2
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ k ∈ S, (1:ℝ)/2 ≤ (c₀:ℝ)*h ya (xa k)+d₀ ∧
        (c₀:ℝ)*h ya (xa k)+d₀ ≤ 2) →
      (∀ k ∈ S, ((a₀:ℝ)*h ya (xa k)+b₀)/((c₀:ℝ)*h ya (xa k)+d₀)=h yb (xb k)) →
      (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)*((c₀:ℝ)*h ya (xa k)+d₀)^3-1| ≤ Δ) →
      let R := max 1 (max (3*U/σ) (2*σ/c))
      (S.card:ℝ) ≤ C*(1+(2*σ/c)*R^12*(Δ+1/M)*M/
        (N*‖((yb-ya,T*(c₀:ℝ)/(2*M^2)):ℝ × ℝ)‖)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_small_action_block_count (σ:=σ) (c:=c) (U:=U) hσ hc hU

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_small_action_block_count

example
    (a b c d : ℤ) {h h₁ : ℝ}
    (hdet : a*d-b*c=1) (hh0 : h ≠ 0) (hh₁0 : h₁ ≠ 0)
    (hh : |1/h| ≤ 1/6) (hh₁ : |1/h₁| ≤ 1/6)
    (haction : |(b:ℝ)/h| ≤ 1/4)
    (ht : (1:ℝ)/2 ≤ (b:ℝ)/h+a ∧ (b:ℝ)/h+a ≤ 2)
    (hmap : ((a:ℝ)*h+b)/((c:ℝ)*h+d)=h₁) :
    a=1 ∧ c=0 ∧ d=1 ∧ h₁=h+b :=
  TaoTrudgianYang2025.HuxleyRationalPhase.large_curvature_small_action_upper_triangular a b c d (h:=h) (h₁:=h₁) hdet hh0 hh₁0 hh hh₁ haction ht hmap

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.large_curvature_small_action_upper_triangular

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb Δ T M N Z : ℝ) (a₀ b₀ c₀ d₀ : ℤ)
        (S : Finset ℤ) (xa xb : ℤ → ℝ),
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ →
      a₀*d₀-b₀*c₀=1 →
      4*σ*M^2/(c*T) ≤ 1/6 →
      |(b₀:ℝ)| * (4*σ*M^2/(c*T)) ≤ 1/4 →
      ((yb-ya,2*M^2*(b₀:ℝ)/T):ℝ × ℝ) ≠ 0 → |yb-ya| < a →
      (∀ k ∈ S, Z+(k:ℝ)*N ≤ xa k ∧ xa k ≤ Z+((k:ℝ)+1)*N) →
      (∀ k ∈ S, xa k ∈ Icc M (2*M) ∧ xb k ∈ Icc M (2*M)) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let h := fun y z => iteratedDeriv 2 (f y) z/2
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ k ∈ S, (1:ℝ)/2 ≤ (b₀:ℝ)/h ya (xa k)+a₀ ∧
        (b₀:ℝ)/h ya (xa k)+a₀ ≤ 2) →
      (∀ k ∈ S, ((a₀:ℝ)*h ya (xa k)+b₀)/((c₀:ℝ)*h ya (xa k)+d₀)=h yb (xb k)) →
      (∀ k ∈ S, |μ yb (xb k)/μ ya (xa k)*((c₀:ℝ)*h ya (xa k)+d₀)^3-1| ≤ Δ) →
      let R := max 1 (max (3*U/σ) (2*σ/c))
      (S.card:ℝ) ≤ C*(1+(2*σ/c)*R*(Δ+1/M)*M/
        (N*‖((yb-ya,2*M^2*(b₀:ℝ)/T):ℝ × ℝ)‖)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_small_action_block_count (σ:=σ) (c:=c) (U:=U) hσ hc hU

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_reciprocal_small_action_block_count

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (A : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (ha hb : ℝ → ℝ) (za zb : ℤ → ℝ) (D : Set ℝ) {N Z : ℝ}
    (hN : 0 < N) (hinj : Set.InjOn hb D)
    (hz : ∀ ij∈P, zb ij.2.1∈D)
    (hspan : ∀ ij∈P, N ≤ Z+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ∧
      Z+(ij.2.1:ℝ)*N+2*N-(round (zb ij.2.1):ℝ) ≤ 3*N)
    (hmap : ∀ ij∈P,
      ((A ij 0:ℝ)*ha (za ij.1.1)+A ij 1)/
        ((A ij 2:ℝ)*ha (za ij.1.1)+A ij 3)=hb (zb ij.2.1)) :
    P.card ≤ 12*(P.image (fun ij => (A ij,ij.1.1))).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_pair_card_le_matrix_blocks P A ha hb za zb D (N:=N) (Z:=Z) hN hinj hz hspan hmap

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.curvature_pair_card_le_matrix_blocks

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (F : ℝ → ℝ) (za zb : ℤ → ℝ) (Alen : ℤ → ℕ) (N : ℕ) (Z : ℤ)
    {σ c η ya yb T M : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hyb : yb∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hz : ∀ ij∈P, zb ij.2.1∈Icc M (2*M))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat ij 0:ℝ)*h ya (za ij.1.1)+Mat ij 1)/
      ((Mat ij 2:ℝ)*h ya (za ij.1.1)+Mat ij 3)=h yb (zb ij.2.1)) →
    P.card ≤ 12*∑ A∈P.image Mat, ((P.filter (fun ij => Mat ij=A)).image (fun ij => ij.1.1)).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_pair_card_le_matrix_blocks P Mat F za zb Alen N Z (σ:=σ) (c:=c) (η:=η) (ya:=ya) (yb:=yb) (T:=T) (M:=M) hσ hc hη hηmax hyb hf hnegative hT hM hN hz hgeometry

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_pair_card_le_matrix_blocks

example
    (I : Finset ℤ) (z : ℤ → ℝ) (Alen : ℤ → ℕ) (N : ℕ) (Z : ℤ) (W : ℝ)
    (hN : 0 < N)
    (hgeometry : ∀ k∈I, N ≤ Alen k ∧ Alen k ≤ 3*N ∧
      round (z k)+(Alen k:ℤ)=Z+(N:ℤ)*k+2*(N:ℤ)) :
    I.card ≤ 5*(I.image (fun k => ⌊(z k-W)/(N:ℝ)⌋)).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.rounded_offset_floor_block_count I z Alen N Z W hN hgeometry

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (F : ℝ → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ) (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ c η ya yb T M : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hyb : yb∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hz : ∀ ij∈P, zb ij.2.1∈Icc M (2*M))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((Mat ij 0:ℝ)*h ya (za ij.1.1)+Mat ij 1)/
      ((Mat ij 2:ℝ)*h ya (za ij.1.1)+Mat ij 3)=h yb (zb ij.2.1)) →
    P.card ≤ 60*∑ A∈P.image Mat,
      ((P.filter (fun ij => Mat ij=A)).image (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_pair_card_le_physical_blocks P Mat F za zb AlenA Alen N Za Z W (σ:=σ) (c:=c) (η:=η) (ya:=ya) (yb:=yb) (T:=T) (M:=M) hσ hc hη hηmax hyb hf hnegative hT hM hN hz hgeometryA hgeometry

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (F : ℝ → ℝ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ)
    (N : ℕ) (Za Zb : ℤ) {σ c U η ya yb Δ T M R Gamma : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hya : ya∈Icc (1:ℝ) 2) (hyb : yb∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 2 ≤ M) (hN : 0 < N)
    (hΔ : 0 ≤ Δ) (hGamma : 0 ≤ Gamma) (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ ij∈P, za ij.1.1∈Icc M (2*M) ∧ zb ij.2.1∈Icc M (2*M))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometryB : ∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ))
    (hdet : ∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1)
    (hgamma : ∀ ij∈P, Mat ij 2 ≠ 0 ∧ |(Mat ij 2:ℝ)| ≤ Gamma)
    (hlarge : ∀ ij∈P, 16*(3*U/σ)*M^2 ≤ |(Mat ij 2:ℝ)| * (c/(2*σ))^2*T) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
    let t := fun ij => (Mat ij 2:ℝ)*h ya (za ij.1.1)+Mat ij 3
    (∀ ij∈P, ((Mat ij 0:ℝ)*h ya (za ij.1.1)+Mat ij 1)/t ij=h yb (zb ij.2.1)) →
    (∀ ij∈P, (1:ℝ)/2 ≤ t ij ∧ t ij ≤ 2) →
    (∀ ij∈P, |μ yb (zb ij.2.1)/μ ya (za ij.1.1)*(t ij)^3-1| ≤ Δ) →
    let B := max 1 (max (3*U/σ) (2*σ/c))
    let Vbound := 3*U*T/(2*σ*M^2)
    let Error := 8*B*(Δ+5/M)*R^2/(c/(2*σ))^2
    (P.card:ℝ) ≤ 120*(2*Gamma+1)*(2*Vbound+5)^2*(Gamma+Error) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_large_entry_pair_count P Mat F za zb AlenA AlenB N Za Zb (σ:=σ) (c:=c) (U:=U) (η:=η) (ya:=ya) (yb:=yb) (Δ:=Δ) (T:=T) (M:=M) (R:=R) (Gamma:=Gamma) hσ hc hU hη hηmax hya hyb hf hbound htests hnegative hT hM hN hΔ hGamma hphase hpoints hgeometryA hgeometryB hdet hgamma hlarge

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (F : ℝ → ℝ) (za zb : ℤ → ℝ) (Alen : ℤ → ℕ) (N : ℕ) (Z : ℤ)
    {σ c η ya yb T M : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hyb : yb∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hz : ∀ ij∈P, zb ij.2.1∈Icc M (2*M))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, h ya (za ij.1.1)=h yb (zb ij.2.1)) →
    P.card ≤ 12*(P.image (fun ij => ij.1.1)).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_identity_pair_count P F za zb Alen N Z (σ:=σ) (c:=c) (η:=η) (ya:=ya) (yb:=yb) (T:=T) (M:=M) hσ hc hη hηmax hyb hf hnegative hT hM hN hz hgeometry

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rounded_offset_floor_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_pair_card_le_physical_blocks
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_large_entry_pair_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_identity_pair_count

example
    (a b c d : ℤ) {x y H L : ℝ}
    (hdet : a*d-b*c=1) (hx0 : x ≠ 0)
    (hx : |x| ≤ H) (hy : |y| ≤ H)
    (haction : |(c:ℝ)| * H ≤ L)
    (hmap : ((a:ℝ)*x+b)/((c:ℝ)*x+d)=y)
    (hden : |((c:ℝ)*x+d)-1| ≤ 1/(8*(L+3)))
    (hnum : |((a:ℝ)*x+b)/x-1| ≤ 1/(8*(L+3))) :
    a+d=2 ∧ (a-1)^2= -b*c :=
  TaoTrudgianYang2025.HuxleyRationalPhase.bounded_action_narrow_ratios_trace_two a b c d (x:=x) (y:=y) (H:=H) (L:=L) hdet hx0 hx hy haction hmap hden hnum

example
    (r s : ℚ) (a b c d : ℤ) {H L : ℝ}
    (hr : r ≠ 0) (hdet : a*d-b*c=1)
    (hrange : |(r:ℝ)| ≤ H) (hsrange : |(s:ℝ)| ≤ H)
    (haction : |(c:ℝ)| * H ≤ L)
    (hmap : ((a:ℝ)*(r:ℝ)+b)/((c:ℝ)*(r:ℝ)+d)=(s:ℝ))
    (hdenom : (c:ℝ)*(r:ℝ)+d=(s.den:ℝ)/r.den)
    (hden : |(s.den:ℝ)/r.den-1| ≤ 1/(8*(L+3)))
    (hnum : |(s.num:ℝ)/r.num-1| ≤ 1/(8*(L+3))) :
    a+d=2 ∧ (a-1)^2= -b*c :=
  TaoTrudgianYang2025.HuxleyRationalPhase.rational_bounded_action_narrow_bands_trace_two r s a b c d (H:=H) (L:=L) hr hdet hrange hsrange haction hmap hdenom hden hnum

example
    (a b c d : ℤ) {x y H : ℝ}
    (hdet : a*d-b*c=1) (hx0 : x ≠ 0)
    (hx : |x| ≤ H) (hy : |y| ≤ H)
    (haction : |(c:ℝ)| * H ≤ 1/2)
    (hmap : ((a:ℝ)*x+b)/((c:ℝ)*x+d)=y)
    (hden : |((c:ℝ)*x+d)-1| ≤ 1/32)
    (hnum : |((a:ℝ)*x+b)/x-1| ≤ 1/32) :
    a=1 ∧ d=1 ∧ (b=0 ∨ c=0) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.narrow_ratios_half_action_triangular a b c d (x:=x) (y:=y) (H:=H) hdet hx0 hx hy haction hmap hden hnum

example
    (S : Finset (Fin 4 → ℤ)) (x y : (Fin 4 → ℤ) → ℝ) {H L : ℝ}
    (hL : 0 ≤ L)
    (hdet : ∀ A∈S, A 0*A 3-A 1*A 2=1)
    (hnontri : ∀ A∈S, A 1 ≠ 0 ∧ A 2 ≠ 0)
    (hpoints : ∀ A∈S, x A ≠ 0 ∧ |x A| ≤ H ∧ |y A| ≤ H)
    (haction : ∀ A∈S, |(A 2:ℝ)| * H ≤ L)
    (hmap : ∀ A∈S, ((A 0:ℝ)*x A+A 1)/((A 2:ℝ)*x A+A 3)=y A)
    (hden : ∀ A∈S, |((A 2:ℝ)*x A+A 3)-1| ≤ 1/(8*(L+3)))
    (hnum : ∀ A∈S, |((A 0:ℝ)*x A+A 1)/x A-1| ≤ 1/(8*(L+3))) :
    (S.card:ℝ) ≤ (2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.bounded_action_narrow_nontriangular_matrix_count S x y (H:=H) (L:=L) hL hdet hnontri hpoints haction hmap hden hnum

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (F : ℝ → ℝ) (za zb : ℤ → ℝ) (Alen : ℤ → ℕ) (N : ℕ) (Z : ℤ)
    {σ c U η ya yb T M L : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hya : ya∈Icc (1:ℝ) 2) (hyb : yb∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hL : 0 ≤ L)
    (hpoints : ∀ ij∈P, za ij.1.1∈Icc M (2*M) ∧ zb ij.2.1∈Icc M (2*M))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ))
    (hdet : ∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1)
    (hnontri : ∀ ij∈P, Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0)
    (haction : ∀ ij∈P, |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let t := fun ij => (Mat ij 2:ℝ)*h ya (za ij.1.1)+Mat ij 3
    (∀ ij∈P, ((Mat ij 0:ℝ)*h ya (za ij.1.1)+Mat ij 1)/t ij=h yb (zb ij.2.1)) →
    (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
    (∀ ij∈P, |((Mat ij 0:ℝ)*h ya (za ij.1.1)+Mat ij 1)/h ya (za ij.1.1)-1| ≤ 1/(8*(L+3))) →
    (P.card:ℝ) ≤ 12*((2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2)*
      ((P.image (fun ij => ij.1.1)).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_bounded_action_nontriangular_pair_count P Mat F za zb Alen N Z (σ:=σ) (c:=c) (U:=U) (η:=η) (ya:=ya) (yb:=yb) (T:=T) (M:=M) (L:=L) hσ hc hU hη hηmax hya hyb hf hbound htests hnegative hT hM hN hL hpoints hgeometry hdet hnontri haction

example
    {σ c U T M γ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hT : 0 < T) (hM : 0 < M) :
    |γ| * ((3*U/σ)*T/(2*M^2)) ≤ 288*(U/c)^2 ∨
      16*(3*U/σ)*M^2 ≤ |γ| * (c/(2*σ))^2*T :=
  TaoTrudgianYang2025.HuxleyRationalPhase.source_action_or_large_entry (σ:=σ) (c:=c) (U:=U) (T:=T) (M:=M) (γ:=γ) hσ hc hU hT hM

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (F : ℝ → ℝ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ)
    (N : ℕ) (Za Zb : ℤ) {σ c U η ya yb Δ T M R Gamma : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hya : ya∈Icc (1:ℝ) 2) (hyb : yb∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 2 ≤ M) (hN : 0 < N)
    (hΔ : 0 ≤ Δ) (hGamma : 0 ≤ Gamma) (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ ij∈P, za ij.1.1∈Icc M (2*M) ∧ zb ij.2.1∈Icc M (2*M))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometryB : ∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ))
    (hdet : ∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1)
    (hnontri : ∀ ij∈P, Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0)
    (hgamma : ∀ ij∈P, |(Mat ij 2:ℝ)| ≤ Gamma) :
    let L := 288*(U/c)^2
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
    let t := fun ij => (Mat ij 2:ℝ)*h ya (za ij.1.1)+Mat ij 3
    (∀ ij∈P, ((Mat ij 0:ℝ)*h ya (za ij.1.1)+Mat ij 1)/t ij=h yb (zb ij.2.1)) →
    (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
    (∀ ij∈P, |((Mat ij 0:ℝ)*h ya (za ij.1.1)+Mat ij 1)/h ya (za ij.1.1)-1| ≤ 1/(8*(L+3))) →
    (∀ ij∈P, |μ yb (zb ij.2.1)/μ ya (za ij.1.1)*(t ij)^3-1| ≤ Δ) →
    let B := max 1 (max (3*U/σ) (2*σ/c))
    let Vbound := 3*U*T/(2*σ*M^2)
    let Error := 8*B*(Δ+5/M)*R^2/(c/(2*σ))^2
    (P.card:ℝ) ≤
      12*((2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2)*((P.image (fun ij => ij.1.1)).card:ℝ)+
      120*(2*Gamma+1)*(2*Vbound+5)^2*(Gamma+Error) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_narrow_nontriangular_pair_count P Mat F za zb AlenA AlenB N Za Zb (σ:=σ) (c:=c) (U:=U) (η:=η) (ya:=ya) (yb:=yb) (Δ:=Δ) (T:=T) (M:=M) (R:=R) (Gamma:=Gamma) hσ hc hU hη hηmax hya hyb hf hbound htests hnegative hT hM hN hΔ hGamma hphase hpoints hgeometryA hgeometryB hdet hnontri hgamma

example (H : ℕ) :
    (∑ h ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0, 1/|(h : ℝ)|) ≤
      2*(3+2*Real.log ((H : ℝ)+1)) :=
  TaoTrudgianYang2025.bourgain_integer_reciprocal_sum H

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.bounded_action_narrow_ratios_trace_two
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_bounded_action_narrow_bands_trace_two
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.narrow_ratios_half_action_triangular
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.bounded_action_narrow_nontriangular_matrix_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_bounded_action_nontriangular_pair_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.source_action_or_large_entry
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_narrow_nontriangular_pair_count
#print axioms TaoTrudgianYang2025.bourgain_integer_reciprocal_sum

example
    (S : Finset ℤ) {D W : ℝ} (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hS : ∀ b∈S, b ≠ 0 ∧ |(b:ℝ)| ≤ D) :
    ∑ b∈S, (1+W/|(b:ℝ)|) ≤ 2*D+1+2*W*(3+2*Real.log (D+2)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.integer_translation_weight_sum S (D:=D) (W:=W) hD hW hS

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb Δ T M N Z D : ℝ)
        (S : Finset ℤ) (blocks : ℤ → Finset ℤ) (xa xb : ℤ → ℤ → ℝ),
      0 < η → η ≤ 1/8 → ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 ≤ D → |yb-ya| < a →
      (∀ b∈S, b ≠ 0 ∧ |(b:ℝ)| ≤ D) →
      (∀ b∈S, ∀ k∈blocks b, Z+(k:ℝ)*N ≤ xa b k ∧ xa b k ≤ Z+((k:ℝ)+1)*N) →
      (∀ b∈S, ∀ k∈blocks b, xa b k∈Icc M (2*M) ∧ xb b k∈Icc M (2*M)) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ b∈S, ∀ k∈blocks b,
        iteratedDeriv 2 (f yb) (xb b k)/2=iteratedDeriv 2 (f ya) (xa b k)/2+b) →
      (∀ b∈S, ∀ k∈blocks b, |μ yb (xb b k)/μ ya (xa b k)-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      let W := (σ/c)*B*(Δ+1/M)*T/(N*M)
      ∑ b∈S, ((blocks b).card:ℝ) ≤ C*(2*D+1+2*W*(3+2*Real.log (D+2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_upper_translation_block_sum (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η ya yb Δ T M N Z D : ℝ)
        (S : Finset ℤ) (blocks : ℤ → Finset ℤ) (xa xb : ℤ → ℤ → ℝ),
      0 < η → η ≤ η₀ → ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
      (∀ v, 0 < v → ContDiffAt ℝ ∞ F v) →
      (∀ v∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F v| ≤ U) →
      (∀ v∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F v) j|) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 ≤ D → |yb-ya| < a →
      (∀ b∈S, b ≠ 0 ∧ |(b:ℝ)| ≤ D) →
      (∀ b∈S, ∀ k∈blocks b, Z+(k:ℝ)*N ≤ xa b k ∧ xa b k ≤ Z+((k:ℝ)+1)*N) →
      (∀ b∈S, ∀ k∈blocks b, xa b k∈Icc M (2*M) ∧ xb b k∈Icc M (2*M)) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let h := fun y z => iteratedDeriv 2 (f y) z/2
      let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
      (∀ b∈S, ∀ k∈blocks b,
        h yb (xb b k)=h ya (xa b k)/((b:ℝ)*h ya (xa b k)+1)) →
      (∀ b∈S, ∀ k∈blocks b, |μ yb (xb b k)/μ ya (xa b k)*((b:ℝ)*h ya (xa b k)+1)^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      let W := (4*σ/c)*B^12*(Δ+1/M)*M^3/(N*T)
      ∑ b∈S, ((blocks b).card:ℝ) ≤ C*(2*D+1+2*W*(3+2*Real.log (D+2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_lower_translation_block_sum (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (tag : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
    (A : ℤ → Fin 4 → ℤ) (hA : Function.Injective A)
    (F : ℝ → ℝ) (za zb : ℤ → ℝ) (AlenA Alen : ℤ → ℕ) (N : ℕ) (Za Z : ℤ) (W : ℝ)
    {σ c η ya yb T M : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hyb : yb∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (hz : ∀ ij∈P, zb ij.2.1∈Icc M (2*M))
    (hgeometryA : ∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ))
    (hgeometry : ∀ ij∈P, N ≤ Alen ij.2.1 ∧ Alen ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(Alen ij.2.1:ℤ)=Z+(N:ℤ)*ij.2.1+2*(N:ℤ)) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ ij∈P, ((A (tag ij) 0:ℝ)*h ya (za ij.1.1)+A (tag ij) 1)/
      ((A (tag ij) 2:ℝ)*h ya (za ij.1.1)+A (tag ij) 3)=h yb (zb ij.2.1)) →
    P.card ≤ 60*∑ b∈P.image tag,
      ((P.filter (fun ij => tag ij=b)).image (fun ij => ⌊(za ij.1.1-W)/(N:ℝ)⌋)).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_tagged_pair_card_le_physical_blocks P tag A hA F za zb AlenA Alen N Za Z W (σ:=σ) (c:=c) (η:=η) (ya:=ya) (yb:=yb) (T:=T) (M:=M) hσ hc hη hηmax hyb hf hnegative hT hM hN hz hgeometryA hgeometry

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
      ∀ (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
        (tag : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
        (F : ℝ → ℝ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ)
        (N : ℕ) (Za Zb : ℤ) (η ya yb Δ T M D : ℝ),
      0 < η → η ≤ 1/8 → ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 ≤ D → |yb-ya| < a →
      (∀ ij∈P, tag ij ≠ 0 ∧ |(tag ij:ℝ)| ≤ D) →
      (∀ ij∈P, za ij.1.1∈Icc M (2*M) ∧ zb ij.2.1∈Icc M (2*M)) →
      (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
        round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
        round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      (∀ ij∈P, h yb (zb ij.2.1)=h ya (za ij.1.1)+tag ij) →
      (∀ ij∈P, |μ yb (zb ij.2.1)/μ ya (za ij.1.1)-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      let W := (σ/c)*B*(Δ+1/M)*T/((N:ℝ)*M)
      (P.card:ℝ) ≤ 60*C*(2*D+1+2*W*(3+2*Real.log (D+2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_upper_translation_pair_count (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
      ∀ (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
        (tag : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℤ)
        (F : ℝ → ℝ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ)
        (N : ℕ) (Za Zb : ℤ) (η ya yb Δ T M D : ℝ),
      0 < η → η ≤ η₀ → ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 ≤ D → |yb-ya| < a →
      (∀ ij∈P, tag ij ≠ 0 ∧ |(tag ij:ℝ)| ≤ D) →
      (∀ ij∈P, za ij.1.1∈Icc M (2*M) ∧ zb ij.2.1∈Icc M (2*M)) →
      (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
        round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
        round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      (∀ ij∈P, h yb (zb ij.2.1)=h ya (za ij.1.1)/((tag ij:ℝ)*h ya (za ij.1.1)+1)) →
      (∀ ij∈P, |μ yb (zb ij.2.1)/μ ya (za ij.1.1)*((tag ij:ℝ)*h ya (za ij.1.1)+1)^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      let W := (4*σ/c)*B^12*(Δ+1/M)*M^3/((N:ℝ)*T)
      (P.card:ℝ) ≤ 60*C*(2*D+1+2*W*(3+2*Real.log (D+2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_lower_translation_pair_count (σ:=σ) (c:=c) (U:=U) hσ hc hU

example {u v Q δ : ℝ}
    (hQ : 0 < Q) (hδ : 0 < δ) (hu : Q ≤ |u|)
    (hbin : ⌊u/(δ*Q)⌋=⌊v/(δ*Q)⌋) :
    |v/u-1| ≤ δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.same_scaled_floor_relative_bound (u:=u) (v:=v) (Q:=Q) (δ:=δ) hQ hδ hu hbin

example
    {ι : Type*} (S : Finset ι) (u : ι → ℝ) {Q δ R : ℝ}
    (hQ : 0 < Q) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hu : ∀ i∈S, |u i| ≤ R*Q) :
    ((S.image (fun i => ⌊u i/(δ*Q)⌋)).card:ℝ) ≤ 2*R/δ+3 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.scaled_floor_image_card (ι:=ι) S u (Q:=Q) (δ:=δ) (R:=R) hQ hδ hR hu

example
    {ι : Type*} (S : Finset ι) (r : ι → ℚ) (Q : ℕ) {lambda U δ : ℝ}
    (hQ : 0 < Q) (hlambda : 0 < lambda) (hU : 0 ≤ U) (hδ : 0 < δ)
    (hcurv : ∀ i∈S, lambda ≤ |(r i:ℝ)| ∧ |(r i:ℝ)| ≤ U)
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) :
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    ((S.image color).card:ℝ) ≤ (4/δ+3)*(4*U/(lambda*δ)+3) ∧
      ∀ i∈S, ∀ j∈S, color i=color j →
        |((r j).den:ℝ)/(r i).den-1| ≤ δ ∧
        |((r j).num:ℝ)/(r i).num-1| ≤ δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.rational_narrow_band_partition (ι:=ι) S r Q (lambda:=lambda) (U:=U) (δ:=δ) hQ hlambda hU hδ hcurv hden

example
    {ι : Type*} (S : Finset ι) (r : ι → ℚ) (Q : ℕ) {lambda U δ : ℝ}
    (hQ : 0 < Q) (hlambda : 0 < lambda) (hU : 0 ≤ U) (hδ : 0 < δ)
    (hcurv : ∀ i∈S, lambda ≤ |(r i:ℝ)| ∧ |(r i:ℝ)| ≤ U)
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) :
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    ((S.image color).card:ℝ) ≤ (4/δ+3)*(4*U/(lambda*δ)+3) ∧
      (∀ i∈S, ∀ j∈S, color i=color j →
        |((r j).den:ℝ)/(r i).den-1| ≤ δ ∧
        |((r j).num:ℝ)/(r i).num-1| ≤ δ) ∧
      ∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
        ((4/δ+3)*(4*U/(lambda*δ)+3))^11*
          ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.rational_narrow_band_twelfth_partition (ι:=ι) S r Q (lambda:=lambda) (U:=U) (δ:=δ) hQ hlambda hU hδ hcurv hden

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.integer_translation_weight_sum
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_upper_translation_block_sum
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_lower_translation_block_sum
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_tagged_pair_card_le_physical_blocks
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_upper_translation_pair_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_lower_translation_pair_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.same_scaled_floor_relative_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.scaled_floor_image_card
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_narrow_band_partition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rational_narrow_band_twelfth_partition

example
    (F : ℝ → ℝ) {σ c U η T M y z : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hT : 0 < T) (hM : 0 < M)
    (hy : y∈Icc (1:ℝ) 2) (hz : z∈Icc M (2*M))
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    c*T/(4*σ*M^2) ≤ |h y z| ∧ |h y z| ≤ (3*U/σ)*T/(2*M^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_half_curvature_source_bounds F (σ:=σ) (c:=c) (U:=U) (η:=η) (T:=T) (M:=M) (y:=y) (z:=z) hσ hc hU hη hηmax hT hM hy hz hf hbound htests

example
    {ι : Type*} (S : Finset ι) (F : ℝ → ℝ)
    (param z : ι → ℝ) (r : ι → ℚ) (Q : ℕ) {σ c U η T M δ : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hT : 0 < T) (hM : 0 < M) (hQ : 0 < Q) (hδ : 0 < δ)
    (hparam : ∀ i∈S, param i∈Icc (1:ℝ) 2)
    (hpoints : ∀ i∈S, z i∈Icc M (2*M))
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    (∀ i∈S, h (param i) (z i)=(r i:ℝ)) →
    let lambda := c*T/(4*σ*M^2)
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(24*U/(c*δ)+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
      (∀ i∈S, ∀ j∈S, color i=color j →
        |((r j).den:ℝ)/(r i).den-1| ≤ δ ∧
        |((r j).num:ℝ)/(r i).num-1| ≤ δ) ∧
      ∀ coeff : ι → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
        ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rational_band_twelfth_partition (ι:=ι) S F param z r Q (σ:=σ) (c:=c) (U:=U) (η:=η) (T:=T) (M:=M) (δ:=δ) hσ hc hU hη hηmax hT hM hQ hδ hparam hpoints hf hbound htests hden

example
    (a b c d : ℤ) {x lambda H δ : ℝ}
    (hlambda : 0 < lambda) (hxlo : lambda ≤ |x|) (hxhi : |x| ≤ H)
    (hδ : 0 ≤ δ) (hδmax : δ < 1)
    (hdet : a*d-b*c=1)
    (hden : |((c:ℝ)*x+d)-1| ≤ δ)
    (hnum : |((a:ℝ)*x+b)/x-1| ≤ δ) :
    (a=1 ∧ b=0 ∧ c=0 ∧ d=1) ∨
    (a=1 ∧ d=1 ∧ c=0 ∧ b≠0 ∧ |(b:ℝ)| ≤ δ*H) ∨
    (a=1 ∧ d=1 ∧ b=0 ∧ c≠0 ∧ |(c:ℝ)| ≤ δ/lambda) ∨
    (b≠0 ∧ c≠0) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.narrow_band_matrix_translation_cases a b c d (x:=x) (lambda:=lambda) (H:=H) (δ:=δ) hlambda hxlo hxhi hδ hδmax hdet hden hnum

example
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F : ℝ → ℝ) (y z : ι → ℝ) (r : ι → ℚ) (v : ι → ℤ)
    (Q K₀ : ℕ) [NeZero K₀] {σ c J η T M N R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hQ : 0 < Q)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 0 < N) (hR : 0 < R)
    (hz : ∀ i∈S, z i∈Icc M (2*M)) (hphase : T*N*R^2=M^3) :
    let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c/(12*σ*N*R^2)
    let U₀ := J/(2*σ*N*R^2)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let L := 288*(J/c)^2
    let δ := 1/(8*(L+3))
    let lambda := c*T/(4*σ*M^2)
    let Hcurv := (3*J/σ)*T/(2*M^2)
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(24*J/(c*δ)+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : ι → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      ∀ ij∈P, color ij.1.1=color ij.2.1 →
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        |t-1| ≤ δ ∧
        |((A ij 0:ℝ)*h ij.1.1+A ij 1)/h ij.1.1-1| ≤ δ ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 2=0 ∧ A ij 1≠0 ∧ |(A ij 1:ℝ)| ≤ δ*Hcurv) ∨
         (A ij 0=1 ∧ A ij 3=1 ∧ A ij 1=0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| ≤ δ/lambda) ∨
         (A ij 1≠0 ∧ A ij 2≠0)) ∧
        (|(A ij 2:ℝ)| * Hcurv ≤ L →
          A ij 0+A ij 3=2 ∧ (A ij 0-1)^2= -A ij 1*A ij 2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_colored_fourier_cloud_matrices (ι:=ι) S F y z r v Q K₀ (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (N:=N) (R:=R) hσ hc hJ hη hηmax hy hf hbound htests hQ hnegative hM hN hR hz hphase

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (S : Finset ((ℝ × ℤ) × Fin 2)) (F : ℝ → ℝ)
        (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ)
        (η ya xa Δ J q t T M : ℝ),
      0 < η → η ≤ 1/8 → ya∈Icc (1:ℝ) 2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → t∈Icc (1/2:ℝ) 2 →
      xa∈Icc M (2*M) →
      (∀ ip∈S, ip.1.1∈Icc (1:ℝ) 2 ∧ z ip.1.1 ip.1.2∈Icc M (2*M)) →
      (∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
        round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
          Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) →
      (∀ ip∈S, ∀ jp∈S, ip.1.1 ≠ jp.1.1 → 1 ≤ J*|ip.1.1-jp.1.1|) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      (∀ ip∈S, h ip.1.1 (z ip.1.1 ip.1.2)=q) →
      (∀ ip∈S, |μ ip.1.1 (z ip.1.1 ip.1.2)/μ ya xa*t^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (S.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_family_fiber_count (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, t ij∈Icc (1/2:ℝ) 2) →
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*
        ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_pair_card_le_matrix_points (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      (∀ ij∈P, h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)=h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*
        ((P.image Prod.fst).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_identity_pair_count (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M L : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → 0 ≤ L →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0) →
      (∀ ij∈P, |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      let B := max 1 (max (3*U/σ) (2*σ/c))
      (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*
        ((2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2)*
        ((P.image Prod.fst).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_bounded_action_pair_count (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    (S : Finset ((ℝ × ℤ) × Fin 2)) (z : ℝ → ℤ → ℝ)
    (Alen : ℝ → ℤ → ℕ) (N : ℕ) (Z : ℝ → ℤ) {M : ℝ}
    (hM : 0 ≤ M) (hN : 0 < N)
    (hpoints : ∀ ip∈S, z ip.1.1 ip.1.2∈Icc M (2*M))
    (hgeometry : ∀ ip∈S, N ≤ Alen ip.1.1 ip.1.2 ∧ Alen ip.1.1 ip.1.2 ≤ 3*N ∧
      round (z ip.1.1 ip.1.2)+(Alen ip.1.1 ip.1.2:ℤ)=
        Z ip.1.1+(N:ℤ)*ip.1.2+2*(N:ℤ)) :
    (S.card:ℝ) ≤ 2*(4+M/(N:ℝ))*((S.image (fun ip => ip.1.1)).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.rounded_offset_family_point_count S z Alen N Z (M:=M) hM hN hpoints hgeometry


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_half_curvature_source_bounds
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_rational_band_twelfth_partition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.narrow_band_matrix_translation_cases
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_colored_fourier_cloud_matrices
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_physical_family_fiber_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_pair_card_le_matrix_points
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_identity_pair_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_bounded_action_pair_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.rounded_offset_family_point_count

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    let L := 288*(U/c)^2
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0) →
      (∀ ij∈P, |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_bounded_action_source_scale (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      (∀ ij∈P, h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)=h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_identity_source_scale (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    let L := 288*(U/c)^2
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L)) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_type_one_source_scale (σ:=σ) (c:=c) (U:=U) hσ hc hU

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (S : Finset (ℝ × ℤ))
        (F : ℝ → ℝ) (z : (ℝ × ℤ) → ℝ) (r : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ)
        (Alen : (ℝ × ℤ) → ℕ) (Z : ℝ → ℤ)
        (Q K₀ N : ℕ) [NeZero K₀] (η T M R Jsep : ℝ),
      (0 < η) →
      (η ≤ 1/8) →
      (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (0 < Q) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      (2 ≤ M) →
      (0 < N) →
      (0 < R) →
      (∀ i∈S, z i∈Icc M (2*M)) →
      (T*(N:ℝ)*R^2=M^3) →
      ((N:ℝ) ≤ M) →
      (0 < Jsep) →
      (Jsep ≤ M) →
      (∀ i∈S, N ≤ Alen i ∧ Alen i ≤ 3*N ∧
      round (z i)+(Alen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
      (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let y := (Prod.fst : (ℝ × ℤ) → ℝ)
    let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
    (∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) →
    (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den) →
    (∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) →
    let μ₀ := c/(12*σ*N*R^2)
    let U₀ := U/(2*σ*N*R^2)
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let L := 288*(U/c)^2
    let δ := 1/(8*(L+3))
    let lambda := c*T/(4*σ*M^2)
    let Hcurv := (3*U/σ)*T/(2*M^2)
    let q₀ := (Q:ℝ)/2
    let p₀ := lambda*(Q:ℝ)/2
    let color := fun i => (⌊((r i).den:ℝ)/(δ*q₀)⌋,⌊((r i).num:ℝ)/(δ*p₀)⌋)
    let Cap := (4/δ+3)*(24*U/(c*δ)+3)
    let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ coeff : (ℝ × ℤ) → ℂ, ‖∑ i∈S,coeff i‖^12 ≤ Cap^11*
      ∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),coeff i‖^12) ∧
    ∃ A : ((((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) → Fin 4 → ℤ,
      (∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t∈Icc (1/2:ℝ) 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤ Δ) ∧
      let E := P.filter (fun ij =>
        color ij.1.1=color ij.2.1 ∧
        ((A ij 0=1 ∧ A ij 1=0 ∧ A ij 2=0 ∧ A ij 3=1) ∨
         (A ij 1≠0 ∧ A ij 2≠0 ∧ |(A ij 2:ℝ)| * Hcurv ≤ L)))
      (E.card:ℝ) ≤ D*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_fourier_cloud_type_one_count (σ:=σ) (c:=c) (U:=U) hσ hc hU


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_bounded_action_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_identity_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_family_type_one_source_scale
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_fourier_cloud_type_one_count

end HuxleyQuarticWindowScratch

import TaoTrudgianYang2025.SargosDProcessGeometry

noncomputable section
namespace TaoTrudgianYang2025

/-- Exact two-parameter balance. This is algebra, not an analytic source
bound; both terms must still be derived for the actual derivative pairs. -/
theorem d_process_free_width_balance {k l α : ℝ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) :
    let d := 2+5*k+3*l
    let h := ((2*k+4*l)*α-l)/d
    let r := 4*α-1-5*h
    5*α-1-5*h-r=α ∧
    (1-2*k+4*l)*α+k-l-(2+3*l)*h+k*r=α ∧
    (4*α+1+2*h)/8 =
      exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α := by
  intro d h r
  have hd : d ≠ 0 := by dsimp only [d]; positivity
  constructor
  · dsimp only [r]; ring
  constructor
  · dsimp only [r,h]
    field_simp
    dsimp only [d]
    ring
  · have he : 5*k+3*l+2=d := by dsimp only [d]; ring
    unfold exponentPairLine sargosDProcessK sargosDProcessL
    rw [he]
    dsimp only [h]
    field_simp
    dsimp only [d]
    ring

theorem d_bourgain_free_width_scales {α : ℝ}
    (hlo : 140/391 ≤ α) (hhi : α ≤ 16/39) :
    let h := (246*α-55)/398
    let r := (362*α-123)/398
    0 < r ∧ r ≤ h ∧ 0 < h ∧ h < α-1/4 ∧
    1-3*α+2*h ≥ 0 ∧ 5*α-1-6*h ≤ α ∧
    4*α-1-3*h < α ∧
    (4*α+1+2*h)/8=18/199+(521/796)*α := by
  dsimp only
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith


#print axioms d_process_free_width_balance
#print axioms d_bourgain_free_width_scales
/-- The original-source trimming losses fit strictly below the D(Bourgain)
target. Strictness at the upper endpoint is needed only for the cubic
width factor, whose endpoint is already covered by the other route. -/
theorem d_bourgain_source_loss_exponents {α : ℝ}
    (hlo : 140/391 ≤ α) (hhi : α < 16/39) :
    let h := (246*α-55)/398
    let β := 18/199+(521/796)*α
    let q := 4*α-1-3*h
    0 < q ∧ q < β ∧ 2*h < β ∧ h < β ∧
      0 < 1-3*α+2*h ∧ 3*α-1-2*h < 0 ∧ α-2*h ≤ α := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [hlo,hhi]

#print axioms d_bourgain_source_loss_exponents

example :
    4*(2/5:ℝ)-1-3*(217/1990)=543/1990 ∧
    2*(217/1990:ℝ)=434/1990 ∧
    (543/1990:ℝ)<701/1990 := by norm_num


-- The target interior scale is exact, not a floating-point fit.
example :
    (246*(2/5:ℝ)-55)/398=217/1990 ∧
    (362*(2/5:ℝ)-123)/398=109/1990 ∧
    18/199+(521/796)*(2/5:ℝ)=701/1990 := by norm_num

-- The closed upper endpoint is precisely where the cubic-width factor
-- changes regime.
example : 1-3*(16/39:ℝ)+2*((246*(16/39:ℝ)-55)/398)=0 := by norm_num

-- The Fourier width is strictly smaller than the Taylor exponent here.
example : (109/1990:ℝ) < 217/1990 := by norm_num

end TaoTrudgianYang2025

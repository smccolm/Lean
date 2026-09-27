import TaoTrudgianYang2025.SargosDProcessGeometry

noncomputable section
namespace TaoTrudgianYang2025

/-- Exact first pruning of the generic D-process domain. A fallthrough
from the already-proved Robert--Sargos and Bourgain beta bounds must
lie strictly between these two physical length scales. -/
theorem sargosD_fallthrough_interval {a b : ℝ}
    (hsecondary : 1/12+2*a/3 ≤ b)
    (hRS : b < (1+9*a)/13)
    (hhigh : 5/12 ≤ a → b < 1/12+2*a/3) :
    1/4 < a ∧ a < 5/12 := by
  constructor
  · linarith only [hsecondary,hRS]
  · by_contra hh
    exact (not_lt_of_ge hsecondary) (hhigh (le_of_not_gt hh))

/-- Denominator-free identities for the remaining exact D-domain
inequalities; these identify the current algebraic terminal blockers. -/
theorem sargosD_physical_scale_numerators {k l a : ℝ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) :
    let d := 2+5*k+3*l
    let h := ((2*k+4*l)*a-l)/d
    let r := 4*a-1-5*h
    d*r=(8*a-2)*(1-l)+(10*a-5)*k ∧
      d*(1-3*a+2*h)=2-6*a+(5-11*a)*k+(1-a)*l ∧
      d*(a-1/4-h)=2*a-1/2+(3*a-5/4)*k+(1/4-a)*l ∧
      d*(h-(4*a-1)/6)=((5-8*a)*k+(12*a-3)*l+2-8*a)/6 := by
  intro d h r
  have hd : d ≠ 0 := by dsimp [d]; positivity
  dsimp [r,h]
  field_simp
  dsimp [d]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- All physical inequalities apart from the curvature product follow
from the Robert--Sargos fallback and the secondary D line alone. -/
theorem sargosD_fallthrough_physical {a b h : ℝ}
    (ha : 1/4 < a) (ha' : a < 5/12)
    (hh : (4*a-1)/6 ≤ h) (hb : b=(4*a+1+2*h)/8)
    (hRS : b < (1+9*a)/13) :
    0<h ∧ h<1 ∧ 0<4*a-1-5*h ∧ 0<4*a-1-3*h ∧
      4*a-1-3*h<a ∧ 4*a-1-3*h<b ∧ 2*h<b ∧ b<a ∧
      1-4*a+4*h<0 ∧ 4*a-1-6*h≤0 ∧
      1-2*a+(4*a-1-3*h)+(4*a-1-5*h)<1 := by
  have hupper : h < (20*a-5)/26 := by linarith only [hb,hRS]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    linarith only [ha,ha',hh,hb,hupper,hRS]

#print axioms sargosD_fallthrough_physical
/-- A rational obstruction to the proposed purely numerical fallback.
This is NOT an exponent pair assertion or a counterexample to Sargos D.
The input lies in the triangle, but the tested P/A/B, Robert--Sargos and
Bourgain lines do not force the necessary positive curvature exponent. -/
example :
    let k : ℝ := 6153/40000
    let l : ℝ := 26153/40000
    let a : ℝ := 2051/5000
    let h := max (((2*k+4*l)*a-l)/(2+5*k+3*l)) ((4*a-1)/6)
    let b := (4*a+1+2*h)/8
    InExponentPairTriangle k l ∧
      b<k+(l-k)*a ∧ b<(k+(l+1)*a)/(2*k+2) ∧
      b<l-1/2+(k-l+1)*a ∧ b<(1+9*a)/13 ∧
      b<13/84+a/2 ∧ b<2/9+a/3 ∧ b<18/199+(521/796)*a ∧
      1-3*a+2*h<0 := by
  norm_num [InExponentPairTriangle]

#print axioms sargosD_fallthrough_interval
#print axioms sargosD_physical_scale_numerators
end TaoTrudgianYang2025

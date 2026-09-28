import TaoTrudgianYang2025.SquareProductCount
import TaoTrudgianYang2025.SargosDProcessGeometry
section UniversalSargosDRegression
open Set Expdb Filter GafniTao TaoTrudgianYang2025 TaoTrudgianYang2025.CubicJointCount
open scoped Topology ContDiff BigOperators NNReal FourierTransform

example {a b : ℝ}
    (hsecondary : 1/12+2*a/3 ≤ b)
    (hRS : b < (1+9*a)/13)
    (hhigh : 5/12 ≤ a → b < 1/12+2*a/3) :
    1/4 < a ∧ a < 5/12 :=
  sargosD_fallthrough_interval hsecondary hRS hhigh

example {a b h : ℝ}
    (ha : 1/4 < a) (ha' : a < 5/12)
    (hh : (4*a-1)/6 ≤ h) (hb : b=(4*a+1+2*h)/8)
    (hRS : b < (1+9*a)/13) :
    0<h ∧ h<1 ∧ 0<4*a-1-5*h ∧ 0<4*a-1-3*h ∧
      4*a-1-3*h<a ∧ 4*a-1-3*h<b ∧ 2*h<b ∧ b<a ∧
      1-4*a+4*h<0 ∧ 4*a-1-6*h≤0 ∧
      1-2*a+(4*a-1-3*h)+(4*a-1-5*h)<1 :=
  sargosD_fallthrough_physical ha ha' hh hb hRS

example
    {k l a b h : ℝ}
    (hk : 0≤k) (hl : 1/2≤l)
    (ha : 1/4<a) (ha' : a<5/12)
    (hh : (4*a-1)/6≤h) (hb : b=(4*a+1+2*h)/8)
    (hD : ((2*k+4*l)*a-l)/(2+5*k+3*l)≤h)
    (hP : b<k+(l-k)*a)
    (hB : b<l-1/2+(k-l+1)*a)
    (hnew : 2/5<a →
      b < max (1/12+2*a/3) (241/1164+425*a/1164)) :
    0<1-3*a+2*h :=
  sargosD_refined_fallthrough_curvature hk hl ha ha' hh hb hD hP hB hnew

example
    {T N : VariableObject ℝ} {α h σ κ₀ η : ℝ}
    (hlo : 1/4<α) (hhi : α<5/12)
    (hsecondary : (4*α-1)/6≤h)
    (hRS : (4*α+1+2*h)/8<(1+9*α)/13)
    (hcurvature : 0<1-3*α+2*h) (hσ : 0<σ)
    (hκ₀ : 0 < κ₀) (hη : 0 < η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let r := 4*α-1-5*h
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let L := fun i => modelPhaseJetLower σ 2*T i/(N i)^3
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, 0 < N i ∧ 2 ≤ H i ∧ 2 ≤ Y i ∧
      ∃ J : ℕ, 1 ≤ Qcut i ∧ Qcut i ≤ (2:ℝ)^J ∧ (J:ℝ)+2 ≤ (T i)^η ∧
        1/(4*(H i:ℝ)^2) ≤ L i/4 ∧
        4*U i*Qcut i*(N i)^2/(σ*T i) ≤ κ₀ ∧
        B i*((H i:ℝ)+1)^4 ≤ 1 :=
  eventually_cubic_generic_parameters hlo hhi hsecondary hRS hcurvature hσ hκ₀ hη hT hTunbounded hNT

example
    {T N : VariableObject ℝ} {k l α h σ η : ℝ}
    (hlo : 1/4<α) (hhi : α<5/12)
    (hsecondary : (4*α-1)/6≤h)
    (hRS : (4*α+1+2*h)/8<(1+9*α)/13)
    (hcurvature : 0<1-3*α+2*h)
    (hopt : (2*k+4*l)*α-l≤h*(2+5*k+3*l))
    (hσ : 0<σ) (hη : 0<η)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) :
    let r := 4*α-1-5*h
    let β := (4*α+1+2*h)/8
    let H := floorRpow T h
    let Y := fun i => (T i)^r
    let lam := fun i => modelPhaseJetLower σ 3*T i/(N i)^4
    let B := fun i => (modelPhaseJetCoefficient σ 3+1)*T i/(N i)^4
    let U := fun i => (modelPhaseJetCoefficient σ 2+1)*T i/(N i)^3
    let Qcut := fun i => 3/(2*lam i*(H i:ℝ)^3)
    ∀ᶠ i in atTop, ∀ J : ℕ, (J:ℝ)+2 ≤ (T i)^η →
      let E := ((J:ℝ)+2)*(U i/(lam i*(H i:ℝ)^2))*
        (1+B i/((lam i)^2*(H i:ℝ)^4)+Qcut i/(H i:ℝ)+Qcut i/Y i+
          (T i/(N i)^2)^(k+η)*(Qcut i)^(l+η)*(Y i)^(k+η)+(N i)^2/T i)
      (N i)^6*(N i+E)*(1+U i*(H i:ℝ)^2)*(H i:ℝ)^η+
          (H i:ℝ)^8+((H i:ℝ)^2+Qcut i+1)^8 ≤
        (15+3^8)*(T i)^(8*β+5*η) :=
  eventually_cubic_generic_cost hlo hhi hsecondary hRS hcurvature hopt hσ hη hT hTunbounded hNT

example
    {k l h : ℝ} {α : ℝ≥0} (hpair : ExponentPair k l)
    (hlo : 1/4<(α:ℝ)) (hhi : (α:ℝ)<5/12)
    (hsecondary : (4*(α:ℝ)-1)/6≤h)
    (hRS : (4*(α:ℝ)+1+2*h)/8<(1+9*(α:ℝ))/13)
    (hcurvature : 0<1-3*(α:ℝ)+2*h)
    (hopt : (2*k+4*l)*(α:ℝ)-l≤h*(2+5*k+3*l)) :
    IsExponentSumBound α ((4*(α:ℝ)+1+2*h)/8) :=
  isExponentSumBound_cubic_generic hpair hlo hhi hsecondary hRS hcurvature hopt

example {k l a : ℝ} (hk : 0≤k) (hl : 0≤l) :
    let h := max (((2*k+4*l)*a-l)/(2+5*k+3*l)) ((4*a-1)/6)
    max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) a)
      (1/12+2*a/3) = (4*a+1+2*h)/8 :=
  sargosD_balanced_scale hk hl

example
    {k l : ℝ} (hpair : ExponentPair k l)
    {α : ℝ≥0} (hhalf : (α:ℝ)≤1/2) :
    exponentSumGrowthExponent α ≤
      max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α)
        (1/12+2*(α:ℝ)/3) :=
  exponentSumGrowthExponent_le_sargosD_half hpair hhalf

example
    {k l : ℝ} (hpair : ExponentPair k l)
    {α : ℝ≥0} (hα : (α:ℝ)≤1) :
    exponentSumGrowthExponent α ≤
      max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α)
        (1/12+2*(α:ℝ)/3) :=
  exponentSumGrowthExponent_le_sargosD hpair hα

example {k l : ℝ}
    (hpair : ExponentPair k l) (hzero : 0≤5*k-3*l+2) (hhalf : 2≤k+3*l) :
    ExponentPair (sargosDProcessK k l) (sargosDProcessL k l) :=
  exponentPair_sargosD hpair hzero hhalf

example {k l : ℝ} (hpair : ExponentPair k l) :
    exponentSumGrowthExponent 0 ≤
      max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) 0) (1/12) := by
  simpa using exponentSumGrowthExponent_le_sargosD (α:=0) hpair (by norm_num)

example {k l : ℝ} (hpair : ExponentPair k l) :
    exponentSumGrowthExponent 1 ≤
      max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) 1) (3/4) := by
  have h := exponentSumGrowthExponent_le_sargosD (α:=1) hpair (by norm_num)
  norm_num at h ⊢
  exact h

example : ExponentPair (18/199) (593/796) := by
  have h := exponentPair_sargosD exponentPair_bourgain (by norm_num) (by norm_num)
  norm_num [sargosDProcessK,sargosDProcessL] at h
  exact h

end UniversalSargosDRegression

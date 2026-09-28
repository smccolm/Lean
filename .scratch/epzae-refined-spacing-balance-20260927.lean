import TaoTrudgianYang2025.SargosDProcessGeometry
noncomputable section
open Set Expdb
open scoped Topology ContDiff BigOperators NNReal
namespace TaoTrudgianYang2025.CubicJointCount

/-- Exact balance for the exponent-pair replacement of the second-spacing
term. This is algebra only; the analytic beta consumer is a separate obligation. -/
theorem refined_spacing_exponent_balance {k l a : ℝ} (hk : 0 ≤ k) :
    let u := 1-3*a
    let z := a+u/2
    let v := a+u
    let w := (k*v+(l-1)*z)/(1+k)
    let c := (7*k+l+4)/(24*(1+k))
    let d := (5*k-l+10)/(24*(1+k))
    w+z=k*v+l*z-k*w ∧
      w+z=((2*k+l)/(1+k))*a+((3*k+l)/(2*(1+k)))*u ∧
      10*a+u/2+(a+3*u/2)+(w+z)=12*(c+d*a) := by
  intro u z v w c d
  have hd : (1+k) ≠ 0 := by positivity
  dsimp only [u,z,v,w,c,d]
  field_simp
  constructor
  · ring
  constructor <;> ring

/-- Physical strict inequalities for the prospective Bourgain-input refinement;
this statement does not assert the beta bound. -/
theorem refined_bourgain_scale_domain {a : ℝ} (ha : 2/5 < a) (hb : a < 3/7) :
    let u := 1-3*a
    let z := a+u/2
    let w := -(3+23*a)/194
    let β := max (1/12+2*a/3) (241/1164+425*a/1164)
    u<0 ∧ w<0 ∧ 2-5*a<0 ∧ 0<a+3*u/2 ∧ z<a ∧ z<β ∧
      2*a-1<0 ∧ 1/4+a/4≤β ∧
      ((13/84:ℝ)*(a+u)+(55/84-1)*z)/(1+13/84)=w ∧
      w+z=(47-60*a)/97 := by
  intro u z w β
  have hβ : 1/12+2*a/3 ≤ β := le_max_left _ _
  dsimp only [u,z,w] at *
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,?_,?_⟩ <;> ring

/-- Uniform physical bound for the refined count before choosing the free
Fourier width. Constants precede all physical parameters. -/
theorem refined_count_physical_majorant
    {l a b u n p q : ℝ} (hl : 0<l) (ha : 0<a) (hb : 0≤b)
    (hu : 0<u) (hn : 0≤n) (hq : 0≤q) :
    ∃ C > (0:ℝ), ∀ P U K η w : ℝ,
      0<P → 0<U → U≤1 → 1≤P*U*Real.sqrt U →
      0≤K → K≤n*(P*U*Real.sqrt U) →
      0≤η → η≤4*Real.sqrt U → 0<w →
      let D := K/(l*U)+1
      (2*η+w)*D+20736*(b*U/P)*U^4/((a*U/P)^2*(l*U)^2)+
        (P*U/u)^p*D^q*w^(-p)+u/(P*U) ≤
      C*(P*U+w*(P*Real.sqrt U)+(P*U)^p*(P*Real.sqrt U)^q*w^(-p)+1/(P*U)) := by
  let d := n/l+1
  let c := 20736*b/(a^2*l^2)
  let e := (1/u)^p*d^q
  let C := 8*d+c+d+e+u
  have hd : 0<d := by dsimp only [d]; positivity
  have hc : 0≤c := by dsimp only [c]; positivity
  have he : 0≤e := by dsimp only [e]; positivity
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro P U K η w hP hU hU1 hscale hK hKhi hη hηhi hw D
  have hs : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  have hPU : 0<P*U := mul_pos hP hU
  have hPS : 1≤P*Real.sqrt U := hscale.trans (by
    calc
      _ ≤ P*1*Real.sqrt U := by gcongr
      _ = _ := by ring)
  have hD : 0<D := by dsimp only [D]; positivity
  have hDu : D≤d*(P*Real.sqrt U) := by
    calc
      _ ≤ (n*(P*U*Real.sqrt U))/(l*U)+P*Real.sqrt U :=
        add_le_add (div_le_div_of_nonneg_right hKhi (by positivity)) hPS
      _ = _ := by dsimp only [d]; field_simp
  have hmain : (2*η+w)*D≤(8*d)*(P*U)+d*(w*(P*Real.sqrt U)) := by
    calc
      _ ≤ (8*Real.sqrt U+w)*(d*(P*Real.sqrt U)) :=
        mul_le_mul (by linarith only [hηhi]) hDu hD.le (by positivity)
      _ = (8*d*P)*(Real.sqrt U)^2+d*(w*(P*Real.sqrt U)) := by ring
      _ = _ := by rw [Real.sq_sqrt hU.le]; ring
  have hcorr : 20736*(b*U/P)*U^4/((a*U/P)^2*(l*U)^2)=c*(P*U) := by
    dsimp only [c]
    field_simp
  have hosc : (P*U/u)^p*D^q*w^(-p) ≤ e*((P*U)^p*(P*Real.sqrt U)^q*w^(-p)) := by
    calc
      _ ≤ (P*U/u)^p*(d*(P*Real.sqrt U))^q*w^(-p) := by gcongr
      _ = _ := by
        rw [show P*U/u=(P*U)*(1/u) by ring,
          Real.mul_rpow hPU.le (by positivity),
          Real.mul_rpow hd.le (by positivity)]
        dsimp only [e]
        ring
  have hC₁ : 8*d+c≤C := by dsimp only [C]; linarith
  have hC₂ : d≤C := by dsimp only [C]; linarith
  have hC₃ : e≤C := by dsimp only [C]; linarith
  have hC₄ : u≤C := by dsimp only [C]; linarith
  calc
    _ ≤ ((8*d)*(P*U)+d*(w*(P*Real.sqrt U)))+c*(P*U)+
        e*((P*U)^p*(P*Real.sqrt U)^q*w^(-p))+u/(P*U) := by
      rw [hcorr]
      exact add_le_add (add_le_add (add_le_add hmain le_rfl) hosc) le_rfl
    _ = (8*d+c)*(P*U)+d*(w*(P*Real.sqrt U))+
        e*((P*U)^p*(P*Real.sqrt U)^q*w^(-p))+u*(1/(P*U)) := by ring
    _ ≤ C*(P*U)+C*(w*(P*Real.sqrt U))+
        C*((P*U)^p*(P*Real.sqrt U)^q*w^(-p))+C*(1/(P*U)) := by gcongr
    _ = _ := by ring

/-- The source error and small-denominator bands fit the first refined
twelfth-moment term when the same lifting scale P*U^2 is small. -/
theorem refined_elementary_twelfth
    {P U Z C Log ε r : ℝ} (hP : 1≤P) (hU : 0<U) (hU1 : U≤1)
    (hZ : 0≤Z) (hC : 0≤C) (hLog : 1≤Log) (hε : 0≤ε)
    (hr : 1/4≤r) (hsmall : P*U^2≤1)
    (hbound : Z≤C*P*U^r*Log^2) :
    Z^12 ≤ C^12*P^ε*Log^24*(P^11*U) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hUquarter : U^r≤U^((1:ℝ)/4) :=
    Real.rpow_le_rpow_of_exponent_ge hU hU1 hr
  have hpower : (U^((1:ℝ)/4))^12=U^3 := by
    rw [←Real.rpow_mul_natCast hU.le]
    norm_num
  have hbase : P^12*U^3≤P^11*U := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤P^11*U by positivity)
    nlinarith only [hh]
  have hPe : 1≤P^ε := Real.one_le_rpow hP hε
  calc
    _ ≤ (C*P*U^((1:ℝ)/4)*Log^2)^12 := by
      apply pow_le_pow_left₀ hZ
      exact hbound.trans (by gcongr)
    _ = C^12*Log^24*(P^12*U^3) := by
      rw [mul_pow,mul_pow,mul_pow,hpower]
      ring
    _ ≤ C^12*Log^24*(P^11*U) := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hPe (show 0≤C^12*Log^24*(P^11*U) by positivity)
      nlinarith only [hh]

end TaoTrudgianYang2025.CubicJointCount

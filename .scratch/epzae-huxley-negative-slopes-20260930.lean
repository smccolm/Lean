import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical

namespace HuxleyNegativeSlopesScratch

/-- Reflect the all-positive-slope rigidity theorem without changing the
original nearest-integer convention. Density rules out the half-integer
tie; no global oddness of rounding and no cutoff at slope -1 is assumed. -/
theorem negative_fareySector_integer_labels_enlarged_rectangle_all_slopes
    {N : ℕ} {l w B α β δ : ℝ}
    (hw : w < 0) (hlw : l ≤ w) (hB : 1 ≤ B) (hδ : 0 ≤ δ) :
    let P := HuxleyLinearForm.fareySector N (-w) (-l)
    let S := P.image (fun p : ℤ × ℤ => (-p.1,p.2))
    max ((w-l)*(N:ℝ)^2/B) 2 ≤ (S.card:ℝ) →
    3840*B*δ*((-l)*(N:ℝ))*(N:ℝ) < (S.card:ℝ) →
    (∀ p∈S, ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) →
    ∀ p : ℤ × ℤ, 0 ≤ -(p.1:ℝ) → -(p.1:ℝ) ≤ 12*((-l)*(N:ℝ)) →
      0 ≤ (p.2:ℝ) → (p.2:ℝ) ≤ 12*(N:ℝ) → ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*round α+p.2*round β := by
  classical
  intro P S hR hlarge hnear
  have hinj : Function.Injective (fun p : ℤ × ℤ => (-p.1,p.2)) := by
    intro p q hpq
    have h₁ := congrArg Prod.fst hpq
    have h₂ := congrArg Prod.snd hpq
    exact Prod.ext (neg_injective h₁) h₂
  have hcard : S.card=P.card := Finset.card_image_of_injective P hinj
  rw [hcard] at hR hlarge
  have hw' : 0 < -w := neg_pos.mpr hw
  have hl' : 0 ≤ -l := by linarith only [hlw,hw]
  have hR' : max (((-l)-(-w))*(N:ℝ)^2/B) 2 ≤ (P.card:ℝ) := by
    have heq : (-l)-(-w)=w-l := by ring
    rw [heq]
    exact hR
  have hnear' : ∀ p∈P, ∃ b : ℤ, |(p.1:ℝ)*(-α)+(p.2:ℝ)*β-b| ≤ δ := by
    intro p hp
    obtain ⟨b,hb⟩ := hnear (-p.1,p.2) (Finset.mem_image_of_mem _ hp)
    refine ⟨b,?_⟩
    simpa only [Int.cast_neg,neg_mul,mul_neg] using hb
  obtain ⟨ha,_hb⟩ :=
    (fareySector_bounded_density_dichotomy_all_slopes
      hw' hB hδ hR' hnear').resolve_left (not_le.mpr hlarge)
  have hPtwo : (2:ℝ) ≤ P.card := (le_max_right _ _).trans hR'
  have hPpos : (0:ℝ) < P.card := lt_of_lt_of_le (by norm_num) hPtwo
  obtain ⟨p₀,hp₀⟩ := Finset.card_pos.mp
    (show 0 < P.card by exact_mod_cast hPpos)
  have hpdata := (HuxleyLinearForm.mem_fareySector_iff hw' hl').mp hp₀
  have ht : (0:ℝ) < p₀.2 := by exact_mod_cast (show 0 < p₀.2 by omega)
  have htN : (p₀.2:ℝ) ≤ N := by exact_mod_cast hpdata.2.1
  have hnum : (0:ℝ) < p₀.1 :=
    (mul_pos hw' ht).trans_le hpdata.2.2.2.1
  have hnumOne : (1:ℝ) ≤ p₀.1 := by
    have hh : (0:ℤ) < p₀.1 := by exact_mod_cast hnum
    exact_mod_cast (show 1 ≤ p₀.1 by omega)
  have hμN : 1 ≤ (-l)*(N:ℝ) :=
    hnumOne.trans (hpdata.2.2.2.2.trans (mul_le_mul_of_nonneg_left htN hl'))
  have hfactor : 54*B ≤ 3840*B*(-l)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hμN (show 0 ≤ 3840*B by positivity)
    nlinarith only [hh,hB]
  have hscaled := mul_le_mul_of_nonneg_right hfactor
    (mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hδ)
  have hsmall : 27*B*(N:ℝ)*δ/(P.card:ℝ) < 1/2 := by
    apply (div_lt_iff₀ hPpos).mpr
    nlinarith only [hlarge,hscaled]
  have hhalf := abs_lt.mp (ha.trans_lt hsmall)
  have hround : round α= -round (-α) := by
    apply round_eq_iff.mpr
    simp only [Int.cast_neg,Set.mem_Ico]
    constructor <;> linarith only [hhalf.1,hhalf.2]
  have hlabels := fareySector_integer_labels_enlarged_rectangle_all_slopes
    hw' hl' hB hδ hR' hlarge hnear'
  intro p hp0 hpM hpt0 hptN b hb
  have hh := hlabels (-p.1,p.2)
    (by simpa only [Int.cast_neg] using hp0)
    (by simpa only [Int.cast_neg] using hpM) hpt0 hptN b
    (by simpa only [Int.cast_neg,neg_mul,mul_neg,neg_neg] using hb)
  change b=(-p.1)*round (-α)+p.2*round β at hh
  rw [hround]
  nlinarith only [hh]

#print axioms negative_fareySector_integer_labels_enlarged_rectangle_all_slopes

private theorem negative_sector_seed_label_of_taylor_remainders_all_slopes
    {K : ℕ} {l w B y₀ α β δ C : ℝ} {g : ℝ → ℝ} {H : ℤ × ℤ → ℤ} {p₀ : ℤ × ℤ} {H₀ : ℤ}
    (hw : w < 0) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hcard : max ((w-l)*(K:ℝ)^2/B) 2 ≤ (((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))).card)
    (htaylor : ∀ p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))),
      |g ((p.1:ℝ)/p.2)-g y₀-deriv g y₀*((p.1:ℝ)/p.2-y₀)| ≤
        C*|((p.1:ℝ)/p.2)-y₀|^2)
    (hnear : ∀ p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))),
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/p.2)-H p| ≤ δ) :
    let η := δ+(K:ℝ)*C*(w-l)^2
    3840*B*η*((-l)*(K:ℝ))*(K:ℝ) < (((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))).card →
    0 ≤ -(p₀.1:ℝ) → -(p₀.1:ℝ) ≤ 12*((-l)*(K:ℝ)) →
    0 < (p₀.2:ℝ) → (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    (p₀.1:ℝ)/p₀.2=y₀ →
    |(p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*g y₀-H₀| ≤ δ →
    H₀=p₀.1*round (α-deriv g y₀)+p₀.2*round (β-g y₀+y₀*deriv g y₀) := by
  let η := δ+(K:ℝ)*C*(w-l)^2
  change _ → _
  intro hlarge
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hlin (p : ℤ × ℤ) (hp : p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))) :
      |(p.1:ℝ)*(α-deriv g y₀)+(p.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H p| ≤ η := by
    obtain ⟨ht,htK,_hc,hlo,hhi⟩ :=
      (mem_negative_fareySector_iff hw hlw).mp hp
    have ht0 : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    have htK' : (p.2:ℝ) ≤ K := by exact_mod_cast htK
    let x : ℝ := (p.1:ℝ)/p.2
    have hx : x ∈ Set.Icc l w :=
      ⟨(le_div_iff₀ ht0).mpr hlo,(div_le_iff₀ ht0).mpr hhi⟩
    have hdist : |x-y₀| ≤ w-l := abs_le.mpr
      ⟨by linarith [hx.1,hy₀.2],by linarith [hx.2,hy₀.1]⟩
    have htay := htaylor p hp
    have hbudget : (p.2:ℝ)*|g x-g y₀-deriv g y₀*(x-y₀)| ≤ (K:ℝ)*C*(w-l)^2 := by
      calc
        _ ≤ (p.2:ℝ)*(C*|x-y₀|^2) := mul_le_mul_of_nonneg_left htay ht0.le
        _ ≤ (K:ℝ)*(C*(w-l)^2) := by gcongr
        _ = _ := by ring
    have hid : (p.1:ℝ)*(α-deriv g y₀)+(p.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H p =
        (p.2:ℝ)*(g x-g y₀-deriv g y₀*(x-y₀))+
        ((p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g x-H p) := by
      dsimp [x]
      field_simp
      ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_pos ht0]
    exact (add_le_add hbudget (hnear p hp)).trans_eq (by dsimp [η]; ring)
  intro hp0 hpu hpt hptK hy hpnear
  have hmul : (p₀.1:ℝ)=y₀*(p₀.2:ℝ) := (div_eq_iff hpt.ne').mp hy
  have hid : (p₀.1:ℝ)*(α-deriv g y₀)+(p₀.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H₀ =
      (p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*g y₀-H₀ := by
    rw [hmul]
    ring
  have hpnear' : |(p₀.1:ℝ)*(α-deriv g y₀)+
      (p₀.2:ℝ)*(β-g y₀+y₀*deriv g y₀)-H₀| ≤ η := by
    rw [hid]
    exact hpnear.trans (le_add_of_nonneg_right (by positivity))
  exact negative_fareySector_integer_labels_enlarged_rectangle_all_slopes hw hlw hB hη hcard hlarge
    (fun q hq => ⟨H q,hlin q hq⟩) p₀ hp0 hpu hpt.le hptK H₀ hpnear'

/-- The original negative-chart physical seed receives the sector's common integer
label and quartic residual even outside the auxiliary cutoff. The seed
Fourth Condition and all auxiliary nonlinear/Taylor bounds are consumed;
neither the common label nor the residual is assumed. -/
private theorem physicalModelPhase_quartic_negative_original_seed_linearization_all_slopes
    {K : ℕ} {σ δ T M N R B dmin l w Bd Δ Q : ℝ}
    {p₀ : ℤ × ℤ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xseed : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    {cnew : ℤ × ℤ → Fin 2 → ℤ} {cseed : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))), ∀ i,
      x₁ ((p.1:ℝ)/p.2) i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hxseed : ∀ i, xseed i∈Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hw : w < 0) (hlw : l ≤ w) (hBd : 1 ≤ Bd) (htseed : 0 < p₀.2)
    (hyseed : (p₀.1:ℝ)/p₀.2∈Set.Icc l w)
    (hden : ∀ y ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*y+s i) :
    let S := ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))
    let y₀ := (p₀.1:ℝ)/p₀.2
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun y i => round (x₁ y i)
    let n := fun y i => b y i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μseed := fun i => iteratedDeriv 3 (f i) (round (xseed i))/6
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
    let zseed := fun i => q p₀ i*iteratedDeriv 1 (f i) (round (xseed i))
    let jseed := fun i => round ((r i:ℝ)*d₀ i)*p₀.1+
      2*(round (xseed i)-a i)*(e i*p₀.1+v i*p₀.2)
    let Hseed := (cseed 0-jseed 0)-(cseed 1-jseed 1)
    let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
    let η := D+(K:ℝ)*C*(w-l)^2
    let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    l ∈ finiteBoundaryCell Z l w k →
    w ∈ finiteBoundaryCell Z l w k →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (xseed i)/2=((e i:ℝ)*p₀.1+v i*p₀.2)/q p₀ i) →
    (∀ i, |(round (xseed i):ℝ)-(a i:ℝ)|^2 ≤ M*R) →
    (∀ p ∈ S, ∀ i,
      iteratedDeriv 2 (f i) (x₁ ((p.1:ℝ)/p.2) i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n ((p.1:ℝ)/p.2) i:ℝ)|^2 ≤ M*R) →
    |μseed 1*(q p₀ 1)^3/(μseed 0*(q p₀ 0)^3)-1| ≤ B*R^2/N^2 →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    max ((w-l)*(K:ℝ)^2/Bd) 2 ≤ S.card →
    3840*Bd*η*((-l)*(K:ℝ))*(K:ℝ) < S.card →
    -(p₀.1:ℝ) ≤ 12*((-l)*(K:ℝ)) →
    (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    |(zseed 0-cseed 0)-(zseed 1-cseed 1)| ≤ Δ →
    |q p₀ 0|+|q p₀ 1| ≤ Q →
    Hseed=p₀.1*round (α-deriv φ y₀)+p₀.2*round (β-φ y₀+y₀*deriv φ y₀) ∧
    |(α-round (α-deriv φ y₀))*y₀+
      (β-round (β-φ y₀+y₀*deriv φ y₀))-φ y₀| ≤ D/(p₀.2:ℝ) := by
  let S := ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))
  let y₀ := (p₀.1:ℝ)/p₀.2
  let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
  let a := fun i => round (x₀ i)
  let b := fun y i => round (x₁ y i)
  let n := fun y i => b y i-a i
  let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
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
  let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+
    2*n ((p.1:ℝ)/p.2) i*(e i*p.1+v i*p.2)
  let H := fun p => (cnew p 0-j p 0)-(cnew p 1-j p 1)
  let zseed := fun i => q p₀ i*iteratedDeriv 1 (f i) (round (xseed i))
  let jseed := fun i => round ((r i:ℝ)*d₀ i)*p₀.1+
    2*(round (xseed i)-a i)*(e i*p₀.1+v i*p₀.2)
  let Hseed := (cseed 0-jseed 0)-(cseed 1-jseed 1)
  let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
  let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
  let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
  let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
    (μ 1) (ν 1) (r 1) (s 1) U
  change _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _
  intro hleft hright hbase hseed hseedsquare hpoint hsquare hthird hfourth hqbound hcard hlarge
    hpu hptK hseedfourth hseedQ
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hr' (i) : (r i:ℝ) ≠ 0 := by exact_mod_cast hr i
  have hdet' (i) : (v i:ℝ)*r i-e i*s i=1 := by exact_mod_cast hdet i
  have hκ := modelPhaseThirdLower_pos hσ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (heathBrownPhysicalPoint_mem_interior hM0 (hA 0) (hW 0)
        (show x₀ 0 ∈ Set.Ioo 0 (W 0) from
          ⟨by linarith [(hx₀ 0).1],by linarith [(hx₀ 0).2]⟩)) 4 le_rfl)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCN : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp [quarticNonlinearResidualConstant]
    positivity
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp [quarticReciprocalConstant]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hgeom (p : ℤ × ℤ) (hp : p ∈ S) :
      (0:ℝ) < p.2 ∧ (p.1:ℝ)/p.2 ∈ Set.Icc l w := by
    obtain ⟨ht,_htK,_hc,hlo,hhi⟩ :=
      (mem_negative_fareySector_iff hw hlw).mp hp
    have ht0 : (0:ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
    exact ⟨ht0,⟨(le_div_iff₀ ht0).mpr hlo,(div_le_iff₀ ht0).mpr hhi⟩⟩
  have hy₀ : y₀ ∈ Set.Icc l w := hyseed
  have ht₀ : (0:ℝ) < p₀.2 := by exact_mod_cast htseed
  have hcell {z : ℝ} (hz : z ∈ Set.Icc l w) :
      z ∈ finiteBoundaryCell Z l w k :=
    (finiteBoundaryCell_ordConnected Z l w k).uIcc_subset hleft hright
      (by simpa only [Set.uIcc_of_le hlw] using hz)
  have htaylor (p : ℤ × ℤ) (hp : p ∈ S) :
      |φ ((p.1:ℝ)/p.2)-φ y₀-deriv φ y₀*((p.1:ℝ)/p.2-y₀)| ≤ C*|((p.1:ℝ)/p.2)-y₀|^2 := by
    have he := physicalModelPhase_quartic_taylor_on_boundary_cell
      (u := (p₀.1:ℝ)) (t := (p₀.2:ℝ)) (y := (p.1:ℝ)/p.2)
      hσ hδ hF hT hM0 hN hR hNscale hscale hB hdmin hA hW hx₀
      hxseed hr' ht₀ hdet' hden
      (hcell hy₀) (hcell (hgeom p hp).2) hbase hseed hseedsquare hthird
    exact he.trans_eq (by dsimp [C,U]; ring)
  have hnear (p : ℤ × ℤ) (hp : p ∈ S) :
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*φ ((p.1:ℝ)/p.2)-H p| ≤ D := by
    let x : ℝ := (p.1:ℝ)/p.2
    have ht0 := (hgeom p hp).1
    have hx := (hgeom p hp).2
    have hpt : p.2 ≠ 0 := by exact_mod_cast ht0.ne'
    have hd (i) : 0 < d x i := hdmin.trans_le (hden x hx i)
    have hqd (i) : q p i=d x i*(p.2:ℝ) := by dsimp [q,d,x]; field_simp
    have hqpos (i) : 0 < q p i := by rw [hqd i]; exact mul_pos (hd i) ht0
    have hqint (i) : r i*p.1+s i*p.2 ≠ 0 := by
      have hh : (0:ℝ) < ((r i*p.1+s i*p.2:ℤ):ℝ) := by
        simpa only [Int.cast_add,Int.cast_mul] using hqpos i
      exact_mod_cast hh.ne'
    have he := physicalModelPhase_quartic_fourth_condition_nonlinear_with_labels
      (cnew := cnew p) hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀
      (hx₁ p hp) hr hpt hqint hdet hbase (hpoint p hp) (hsquare p hp) (hfourth p hp)
    have hid : (p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*φ x-H p =
        (θ 0-θ 1)*p.1+(β₀ 0-β₀ 1)*p.2-(p.2:ℝ)*g x+(p.2:ℝ)*h x-H p := by
      dsimp [α,β,φ]
      ring
    rw [hid]
    apply he.trans
    dsimp only [D]
    gcongr
    exact hqbound p hp
  have hqseedpos (i) : 0 < q p₀ i := by
    have hh : q p₀ i=d y₀ i*(p₀.2:ℝ) := by dsimp only [q,d,y₀]; field_simp
    rw [hh]
    exact mul_pos (hdmin.trans_le (hden y₀ hy₀ i)) ht₀
  have hqseedint (i) : r i*p₀.1+s i*p₀.2 ≠ 0 := by
    have hh : (0:ℝ) < ((r i*p₀.1+s i*p₀.2:ℤ):ℝ) := by
      simpa only [Int.cast_add,Int.cast_mul] using hqseedpos i
    exact_mod_cast hh.ne'
  have hseednear :
      |(p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*φ y₀-Hseed| ≤ D := by
    have he := physicalModelPhase_quartic_fourth_condition_nonlinear_with_labels
      (cnew := cseed) hσ hδ hF hT hM hN hR hRM hscale hA hW hx₀
      hxseed hr htseed.ne' hqseedint hdet hbase hseed
      (fun i => by simpa only [Int.cast_sub] using hseedsquare i) hseedfourth
    have hid : (p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*φ y₀-Hseed =
        (θ 0-θ 1)*p₀.1+(β₀ 0-β₀ 1)*p₀.2-
        (p₀.2:ℝ)*g y₀+(p₀.2:ℝ)*h y₀-Hseed := by
      dsimp only [α,β,φ]; ring
    rw [hid]
    apply he.trans
    dsimp only [D]
    gcongr
  have hp0 : 0 ≤ -(p₀.1:ℝ) := by
    have hh := (div_le_iff₀ ht₀).mp hy₀.2
    have hw0 : w*(p₀.2:ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hw.le ht₀.le
    linarith only [hh,hw0]
  have hlabel := negative_sector_seed_label_of_taylor_remainders_all_slopes
    hw hlw hBd hy₀ hD hC hcard htaylor hnear hlarge
    hp0 hpu ht₀ hptK rfl hseednear
  refine ⟨hlabel,?_⟩
  have hid : (p₀.2:ℝ)*((α-round (α-deriv φ y₀))*y₀+
      (β-round (β-φ y₀+y₀*deriv φ y₀))-φ y₀) =
      (p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*φ y₀-Hseed := by
    rw [hlabel]
    push_cast
    dsimp only [y₀]
    field_simp
    ring
  have hmulabs := congrArg abs hid
  rw [abs_mul,abs_of_pos ht₀] at hmulabs
  apply (le_div_iff₀ ht₀).mpr
  rw [mul_comm]
  exact hmulabs.trans_le hseednear


#print axioms negative_sector_seed_label_of_taylor_remainders_all_slopes
#print axioms physicalModelPhase_quartic_negative_original_seed_linearization_all_slopes

/-- Full negative-slope original-seed residual, retaining the original
physical phases, rounded labels, source Fourier matrix and t-cutoff. -/
private theorem physicalModelPhase_actual_fourier_negative_original_seed_residual_all_slopes
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    (v:ℝ)-s*((rat 0:ℝ)-ε) < 0 →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := (HuxleyLinearForm.fareySector K (-β) (-α)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    3840*128*η*((-α)*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤ D/(pseed.2:ℝ) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ ep rp sp pseed yseed ar μr νr dr δr θr βr ac bc g hq φ
    Ctay D η U Z hMone hRone hRM hNscale hdmin hΔ hrp hxref href hbudget
    hd hleft hright hlarge
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  obtain ⟨hcard,ξ,hξ⟩ := physicalModelPhase_actual_fourier_complete_negative_sector_fourth
    Q K₀ rat vinv parity Mat anchor e r v s hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear hsmall hNR hRN hcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
  let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
  let ap := fun (p : ℤ × ℤ) i => (ep i:ℝ)*p.1+vp i*p.2
  let xp := fun p : ℤ × ℤ => ξ ((p.1:ℝ)/p.2)
  let zp := fun p i => qp p i*deriv (f i) (round (xp p i))
  have hqe (p : ℤ × ℤ) (i : Fin 2) :
      ((![r*p.1+s*p.2,Mat 2*(e*p.1+v*p.2)+Mat 3*(r*p.1+s*p.2)] i:ℤ):ℝ)=qp p i := by
    fin_cases i <;> dsimp only [qp,rp,sp] <;> push_cast <;> ring
  have hae (p : ℤ × ℤ) (i : Fin 2) :
      ((![e*p.1+v*p.2,Mat 0*(e*p.1+v*p.2)+Mat 1*(r*p.1+s*p.2)] i:ℤ):ℝ)=ap p i := by
    fin_cases i <;> dsimp only [ap,ep,vp] <;> push_cast <;> ring
  have hpoints (p) (hp : p∈S) (i) :
      xp p i∈Ioo (1/2:ℝ) (W i-1/2) ∧
      iteratedDeriv 2 (f i) (xp p i)/2=ap p i/qp p i ∧
      |xp p i-x₀ i| ≤ H ∧ 0 < qp p i ∧ qp p i ≤ Q := by
    have hh := (hξ p hp).1 i
    simpa only [hqe,hae] using hh
  have hlabels (p : ℤ × ℤ) : ∃ ci : Fin 2 → ℤ, p∈S →
      (∀ i, ci i∈minorArcCenterLabels (zp p i) Δ) ∧
      |(zp p 0-ci 0)-(zp p 1-ci 1)| ≤ Δ := by
    by_cases hp : p∈S
    · have hh := (hξ p hp).2.2 hΔ
      simp only [hqe] at hh
      obtain ⟨c₀,hc₀,c₁,hc₁,_hrnd,hfour,_⟩ := hh
      refine ⟨![c₀,c₁],fun _ => ⟨?_,hfour⟩⟩
      intro i
      fin_cases i
      · exact hc₀
      · exact hc₁
    · exact ⟨fun _ => 0,fun h => False.elim (hp h)⟩
  choose cnew hcnew using hlabels
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hC₂ : 0 ≤ C₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ : 0 ≤ C₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hΔpos : 0 ≤ Δ := by dsimp only [Δ,Ct,Cc]; positivity
  have hH : 0 < H := by dsimp only [H,C]; positivity
  have hε : 0 < ε := by dsimp only [ε,C]; positivity
  have hlw : l < w' := by dsimp only [l,w']; linarith only [hε]
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hnegβ : β < 0 := div_neg_of_neg_of_pos hnum hdl
  have hαβ : α ≤ β := by
    have hh := inverseFarey_difference hchartR hdl.ne' hdw.ne'
    change β-α=(w'-l)/(((r:ℝ)*l-e)*((r:ℝ)*w'-e)) at hh
    have hp' : 0 ≤ (w'-l)/(((r:ℝ)*l-e)*((r:ℝ)*w'-e)) := by positivity
    linarith only [hh,hp']
  have hqpos i : (0:ℝ) < q i := by exact_mod_cast (rat i).pos
  have hrat i : (rat i:ℝ)=((rat i).num:ℝ)/(q i:ℝ) := Rat.cast_def _
  have hdenR : (Mat 2:ℝ)*(rat 0).num+Mat 3*q 0=q 1 := by
    calc
      _ = ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)*q 0 := by
        rw [hrat]; field_simp [(hqpos 0).ne']
      _ = q 1 := by rw [hMatt]; field_simp [(hqpos 0).ne']
  have hnumR : (Mat 0:ℝ)*(rat 0).num+Mat 1*q 0=(rat 1).num := by
    have hm := hMatmap
    rw [hMatt,hrat 0,hrat 1] at hm
    have hh := (div_eq_iff (div_ne_zero (hqpos 1).ne' (hqpos 0).ne')).mp hm
    field_simp [(hqpos 0).ne',(hqpos 1).ne'] at hh
    nlinarith only [hh]
  have hseedq (i) : qp pseed i=(q i:ℝ) := by
    fin_cases i
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination (q 0:ℝ)*hchartR
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination ((Mat 2:ℝ)*(rat 0).num+Mat 3*q 0)*hchartR+hdenR
  have hseeda (i) : ap pseed i=((rat i).num:ℝ) := by
    fin_cases i
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((rat 0).num:ℝ)*hchartR
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((Mat 0:ℝ)*(rat 0).num+Mat 1*q 0)*hchartR+hnumR
  have hseedroot (i) : iteratedDeriv 2 (f i) (x₀ i)/2=ap pseed i/qp pseed i := by
    rw [hseedq,hseeda,hlevel,hrat]
  have hseedtd : (pseed.2:ℝ)=((r:ℝ)*(rat 0:ℝ)-e)*q 0 := by
    dsimp only [pseed]; push_cast; rw [hrat]; field_simp [(hqpos 0).ne']
  have hseedd : 0 < (r:ℝ)*(rat 0:ℝ)-e := by
    nlinarith only [hdl,hdw]
  have htseed : 0 < pseed.2 := by
    have hh : (0:ℝ) < pseed.2 := by rw [hseedtd]; exact mul_pos hseedd (hqpos 0)
    exact_mod_cast hh
  have hys : yseed=((v:ℝ)-s*(rat 0:ℝ))/((r:ℝ)*(rat 0:ℝ)-e) := by
    dsimp only [yseed,pseed]
    push_cast
    rw [hrat 0]
    field_simp [(hqpos 0).ne']
  have hyseed : yseed∈Icc α β := by
    rw [hys]
    apply inverseFarey_mem_interval_signed hchartR hdl hdw
    exact ⟨by linarith only [hε],by linarith only [hε]⟩
  have hdetp (i) : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hsq (p) (hp : p∈S) (i) :
      |((round (xp p i)-ar i:ℤ):ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (xp p i) (xref i)
    have htri := abs_sub_le (xp p i) (x₀ i) (xref i)
    have hdist := (hpoints p hp i).2.2.1
    have hb : |(round (xp p i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,htri,hdist]
    rw [Int.cast_sub]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  have hseedSq i : |(round (x₀ i):ℝ)-(ar i:ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (x₀ i) (xref i)
    have hb : |(round (x₀ i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,hH]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  obtain ⟨_v,_hv,hthird,_hsecond,_hfirst,hfourth⟩ := physicalModelPhase_actual_fourier_conditions
    Q K₀ rat vinv parity hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear
  have hthird' : |mu 1*(qp pseed 1)^3/(mu 0*(qp pseed 0)^3)-1| ≤ B*R^2/N^2 := by
    simpa only [hseedq] using hthird
  have hqsum p (hp : p∈S) : |qp p 0|+|qp p 1| ≤ 2*(Q:ℝ) := by
    rw [abs_of_pos (hpoints p hp 0).2.2.2.1,abs_of_pos (hpoints p hp 1).2.2.2.1]
    linarith only [(hpoints p hp 0).2.2.2.2,(hpoints p hp 1).2.2.2.2]
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hseedI : (rat 0:ℝ)∈Icc l w' :=
    ⟨by dsimp only [l]; linarith only [hε],
      by dsimp only [w']; linarith only [hε]⟩
  have hrect := inverseFarey_negative_original_seed_enlarged_rectangle
    hchart hdl hdw hnum ha hseedI hdyad hcut
    (show ((rat 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden 0).1)
  have hpu : -(pseed.1:ℝ) ≤ 12*((-α)*(K:ℝ)) := hrect.2.2.2.1
  have hptK : (pseed.2:ℝ) ≤ 12*(K:ℝ) := hrect.2.2.2.2
  have hseedfourth :
      |(qp pseed 0*iteratedDeriv 1 (f 0) (round (x₀ 0))-cround 0)-
       (qp pseed 1*iteratedDeriv 1 (f 1) (round (x₀ 1))-cround 1)| ≤ Δ := by
    simp only [hseedq,iteratedDeriv_one]
    apply hfourth.trans
    have hqQ : (q 0:ℝ) ≤ Q := by exact_mod_cast (hden 0).1
    have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
    have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
    have hcoeff : B ≤ 37*B/2+16*B*Cc+2*Ct+2*Cc := by
      nlinarith only [hB,hCt,hCc,mul_nonneg hB hCc]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqQ hB) hN.le).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (by positivity : (0:ℝ) ≤ Q)) hN.le)
  have hseedQ : |qp pseed 0|+|qp pseed 1| ≤ 2*(Q:ℝ) := by
    rw [hseedq,hseedq,abs_of_pos (hqpos 0),abs_of_pos (hqpos 1)]
    have hq0 : (q 0:ℝ) ≤ Q := by exact_mod_cast (hden 0).1
    have hq1 : (q 1:ℝ) ≤ Q := by exact_mod_cast (hden 1).1
    linarith only [hq0,hq1]
  have hcommon := physicalModelPhase_quartic_negative_original_seed_linearization_all_slopes
    (p₀:=pseed) (x₀:=xref) (xseed:=x₀) (x₁:=ξ) (e:=ep) (r:=rp) (v:=vp) (s:=sp)
    (cnew:=cnew) (cseed:=cround) hσ hδ hF hT hMone hN hRone hRM hNscale hscale
    hB hdmin hΔpos (by positivity : (0:ℝ) ≤ 2*(Q:ℝ))
    hA hW hxref (fun p hp i => (hpoints p hp i).1) hx₀ hrp hdetp
    hnegβ hαβ (by norm_num : (1:ℝ) ≤ 128) htseed hyseed hd
    hleft hright href hseedroot hseedSq
    (fun p hp i => (hpoints p hp i).2.1) hsq hthird'
    (fun p hp => by simpa only [iteratedDeriv_one] using (hcnew p hp).2) hqsum hcard hlarge
    hpu hptK hseedfourth hseedQ
  have hres := hcommon.2
  simp only [iteratedDeriv_one] at hres
  change |(ac-round (ac-deriv φ yseed))*yseed+
    (bc-round (bc-φ yseed+yseed*deriv φ yseed))-φ yseed| ≤ D/(pseed.2:ℝ) at hres
  convert hres using 1
  congr 1
  dsimp only [φ]
  ring

/-- Both measured curvature and raw quartic residual for the actual
original Fourier seed on EVERY strictly negative inverse-Farey interval.
No slope-minus-one restriction, modified label convention or supplied
curvature/residual certificate is used. -/
theorem physicalModelPhase_actual_fourier_original_seed_bounds_all_negative_slopes
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    (v:ℝ)-s*((rat 0:ℝ)-ε) < 0 →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := (HuxleyLinearForm.fareySector K (-β) (-α)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    3840*128*η*((-α)*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      D/(pseed.2:ℝ) := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ ep rp sp pseed yseed ar μr νr dr δr θr βr ac bc g hq φ
    Ctay D η U Z hMone hRone hRM hNscale hdmin hΔ hrp hxref href hbudget
    hd hleft hright hlarge
  have hresult := physicalModelPhase_actual_fourier_negative_original_seed_residual_all_slopes
    Q K₀ rat vinv parity Mat anchor e r v s
    hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv
    hlevel hcolor hnear hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    hMone hRone hRM hNscale hdmin hΔ hrp hxref href hbudget hd hleft hright hlarge
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,C]; positivity
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hseedI : (rat 0:ℝ)∈Icc l w' :=
    ⟨by dsimp only [l]; linarith only [hε],
      by dsimp only [w']; linarith only [hε]⟩
  have hrect := inverseFarey_negative_original_seed_enlarged_rectangle
    hchart hdl hdw hnum ha hseedI hdyad hcut
    (show ((rat 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden 0).1)
  have ht : (0:ℝ) < pseed.2 := hrect.1
  have hyseed : yseed∈Icc α β := hrect.2.1
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  refine ⟨?_,hresult⟩
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
  let ap := fun (p : ℤ × ℤ) i => (ep i:ℝ)*p.1+vp i*p.2
  have hH : 0 < H := by dsimp only [H,C]; positivity
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  have hqpos i : (0:ℝ) < q i := by exact_mod_cast (rat i).pos
  have hrat i : (rat i:ℝ)=((rat i).num:ℝ)/(q i:ℝ) := Rat.cast_def _
  have hdenR : (Mat 2:ℝ)*(rat 0).num+Mat 3*q 0=q 1 := by
    calc
      _ = ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)*q 0 := by
        rw [hrat]; field_simp [(hqpos 0).ne']
      _ = q 1 := by rw [hMatt]; field_simp [(hqpos 0).ne']
  have hnumR : (Mat 0:ℝ)*(rat 0).num+Mat 1*q 0=(rat 1).num := by
    have hm := hMatmap
    rw [hMatt,hrat 0,hrat 1] at hm
    have hh := (div_eq_iff (div_ne_zero (hqpos 1).ne' (hqpos 0).ne')).mp hm
    field_simp [(hqpos 0).ne',(hqpos 1).ne'] at hh
    nlinarith only [hh]
  have hseedq (i) : qp pseed i=(q i:ℝ) := by
    fin_cases i
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination (q 0:ℝ)*hchartR
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination ((Mat 2:ℝ)*(rat 0).num+Mat 3*q 0)*hchartR+hdenR
  have hseeda (i) : ap pseed i=((rat i).num:ℝ) := by
    fin_cases i
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((rat 0).num:ℝ)*hchartR
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((Mat 0:ℝ)*(rat 0).num+Mat 1*q 0)*hchartR+hnumR
  have hseedroot (i) : iteratedDeriv 2 (f i) (x₀ i)/2=ap pseed i/qp pseed i := by
    rw [hseedq,hseeda,hlevel,hrat]
  have hdetp (i) : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hseedSq i : |(round (x₀ i):ℝ)-(ar i:ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (x₀ i) (xref i)
    have hb : |(round (x₀ i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,hH]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  obtain ⟨_v,_hv,hthird,_hsecond,_hfirst,_hfourth⟩ := physicalModelPhase_actual_fourier_conditions
    Q K₀ rat vinv parity hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear
  have hthird' : |mu 1*(qp pseed 1)^3/(mu 0*(qp pseed 0)^3)-1| ≤ B*R^2/N^2 := by
    simpa only [hseedq] using hthird
  exact physicalModelPhase_quartic_curvature_source_scale
    (u:=(pseed.1:ℝ)) (t:=(pseed.2:ℝ)) (x₀:=xref) (x₁:=x₀)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    hσ hδ hF hT hM hN hRone hNscale hscale hB hdmin hA hW hxref hx₀
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast hrp i) ht
    (fun i => by change 0 < qp pseed i; rw [hseedq]; exact hqpos i)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i) href hseedroot hseedSq
    (hd yseed hyseed) hthird'



#print axioms physicalModelPhase_actual_fourier_negative_original_seed_residual_all_slopes
#print axioms physicalModelPhase_actual_fourier_original_seed_bounds_all_negative_slopes

/-- Shared same-reference source consumer for the Section 9 First Condition. -/
private theorem physicalModelPhase_actual_fourier_signed_height_square_span_fixed_reference_first_condition
    (S : Finset ℕ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut : ℝ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcesquare : nSpan^2 ≤ M*R)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, 0 < (v:ℝ)-s*((rat j 0:ℝ)+ε) ∨ (v:ℝ)-s*((rat j 0:ℝ)-ε) < 0) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∀ xref : Fin 2 → ℝ,
      (∀ i, rp i ≠ 0 ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let U := Ccurv*R^4/(N*d^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M := by
  classical
  intro Vheight P₁ P₂ hS f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  intro xref hxr Hspan hdisplacement hspan ar μr νr G Ccurv Ctay D η U Z Kres hbudget hD hΔ
    hdenregion hleft hright hlarge hBsize hGcut Blabels Γ L C Cfirst Csecond
  have hrp i : rp i ≠ 0 := (hxr i).1
  have hxref i : xref i∈Ioo (1/2:ℝ) (W i-1/2) := (hxr i).2.1
  have href i : iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i := (hxr i).2.2
  let p : ℕ → ℤ × ℤ := fun j =>
    (v*(q j 0:ℤ)-s*(rat j 0).num,r*(rat j 0).num-e*(q j 0:ℤ))
  let y := fun j => ((p j).1:ℝ)/(p j).2
  let dr := fun i => deriv (f i) (ar i)
  let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
  let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
  let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
  let ac := θr 0-θr 1
  let bc := βr 0-βr 1
  let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
  let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
  let φ := fun z => g z-hq z
  have hMone : 1 ≤ M := hR.trans hRM
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,Cphys]; positivity
  have hNscale : N^2 ≤ M*R := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg N) (mul_nonneg hM.le hRpos.le)
      (by norm_num : (3:ℕ) ≠ 0)).mp
    have hh := pow_le_pow_left₀ (pow_nonneg hN.le 3) hNcube 2
    have hh' := mul_le_mul_of_nonneg_left hRM (show 0 ≤ M^2*R^3 by positivity)
    nlinarith only [hh,hh']
  have hrect j (hj : j∈S) : 0 < (p j).2 ∧ y j∈Icc (α j) (β j) := by
    have ha : (anchor j:ℝ)∈Icc (lo j) (hi j) := by
      have hh := abs_le.mp (hanchor j hj)
      exact ⟨by dsimp only [lo]; linarith only [hh.1],
        by dsimp only [hi]; linarith only [hh.2]⟩
    have hp : (rat j 0:ℝ)∈Icc (lo j) (hi j) := by
      constructor <;> dsimp only [lo,hi] <;> linarith only [hε]
    rcases hnum j hj with hpos | hneg
    · have hh := inverseFarey_original_seed_enlarged_rectangle_signed
        hchart (hdl j hj) (hdw j hj) hpos ha hp (hdyad j hj) (hcut j hj)
        (show ((rat j 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden j hj 0).1)
      exact ⟨by exact_mod_cast hh.1,hh.2.1⟩
    · have hh := inverseFarey_negative_original_seed_enlarged_rectangle
        hchart (hdl j hj) (hdw j hj) hneg ha hp (hdyad j hj) (hcut j hj)
        (show ((rat j 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden j hj 0).1)
      exact ⟨by exact_mod_cast hh.1,hh.2.1⟩
  have hy j (hj : j∈S) : y j∈finiteBoundaryCell Z l w k :=
    (finiteBoundaryCell_ordConnected Z l w k).out (hleft j hj) (hright j hj) (hrect j hj).2
  have hlocalI j (hj : j∈S) : Icc (α j) (β j) ⊆ Icc l w :=
    fun z hz => ⟨(hleft j hj).1.1.trans hz.1,hz.2.trans (hright j hj).1.2⟩
  have hleft' j (hj : j∈S) : α j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨le_rfl,(hrect j hj).2.1.trans (hrect j hj).2.2⟩,(hleft j hj).2⟩
  have hright' j (hj : j∈S) : β j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨(hrect j hj).2.1.trans (hrect j hj).2.2,le_rfl⟩,(hright j hj).2⟩
  have hsource j (hj : j∈S) :
      |iteratedDeriv 2 g (y j)-iteratedDeriv 2 hq (y j)| ≤ U ∧
      |(ac-round (ac-deriv φ (y j)))*y j+
        (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+hq (y j)| ≤
        D/(p j).2 := by
    have hαβ : α j ≤ β j := (hrect j hj).2.1.trans (hrect j hj).2.2
    rcases hnum j hj with hpos | hneg
    · have hαpos : 0 < α j := div_pos hpos (hdw j hj)
      have hβpos : 0 < β j := hαpos.trans_le hαβ
      have hmax : max |α j| |β j|=β j := by
        rw [abs_of_pos hαpos,abs_of_pos hβpos,max_eq_right hαβ]
      have hlarge' := hlarge j hj
      dsimp only [Saux] at hlarge'
      rw [if_pos hαpos,hmax] at hlarge'
      exact physicalModelPhase_actual_fourier_original_seed_bounds_all_positive_slopes
        Q K₀ (rat j) (vinv j) (parity j) Mat (anchor j) e r v s
        hσ hδ hF hT hM hN hRpos hQ hscale hmesh hA hW (hx j hj)
        (hden j hj) (hinv j hj) (hlevel j hj) (hcolor j hj) (hnear j hj)
        hsmall hNR hRN hNcube hminscale hMatdet (hMatt j hj) (hMatmap j hj) hMatgamma
        hNtwo (hL j hj) (hU j hj) hchart (hdl j hj) (hdw j hj) hpos
        (hdyad j hj) (hanchor j hj) (hcut j hj) (hcount j hj)
        hMone hR hRM hNscale hd hΔ hrp hxref href (hbudget j hj)
        (fun z hz i => (hdenregion z (hlocalI j hj hz) i).1)
        (hleft' j hj) (hright' j hj) hlarge'
    · have hβneg : β j < 0 := div_neg_of_neg_of_pos hneg (hdl j hj)
      have hαneg : α j < 0 := hαβ.trans_lt hβneg
      have hmax : max |α j| |β j|= -α j := by
        rw [abs_of_neg hαneg,abs_of_neg hβneg,max_eq_left (neg_le_neg hαβ)]
      have hlarge' := hlarge j hj
      dsimp only [Saux] at hlarge'
      rw [if_neg (not_lt.mpr hαneg.le),hmax] at hlarge'
      exact physicalModelPhase_actual_fourier_original_seed_bounds_all_negative_slopes
        Q K₀ (rat j) (vinv j) (parity j) Mat (anchor j) e r v s
        hσ hδ hF hT hM hN hRpos hQ hscale hmesh hA hW (hx j hj)
        (hden j hj) (hinv j hj) (hlevel j hj) (hcolor j hj) (hnear j hj)
        hsmall hNR hRN hNcube hminscale hMatdet (hMatt j hj) (hMatmap j hj) hMatgamma
        hNtwo (hL j hj) (hU j hj) hchart (hdl j hj) (hdw j hj) hneg
        (hdyad j hj) (hanchor j hj) (hcut j hj) (hcount j hj)
        hMone hR hRM hNscale hd hΔ hrp hxref href (hbudget j hj)
        (fun z hz i => (hdenregion z (hlocalI j hj hz) i).1)
        (hleft' j hj) (hright' j hj) hlarge'
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hdetp i : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hcoordinates j (hj : j∈S) :
      (∀ i, (rp i:ℝ)*(p j).1+sp i*(p j).2=(q j i:ℝ)) ∧
      (∀ i, iteratedDeriv 2 (f i) (x j i)/2=
        ((ep i:ℝ)*(p j).1+vp i*(p j).2)/((rp i:ℝ)*(p j).1+sp i*(p j).2)) := by
    have hc := farey_matrix_original_seed_coordinates (rat j) Mat e r v s
      hchart (hMatt j hj) (hMatmap j hj)
    refine ⟨fun i => (hc i).1,?_⟩
    intro i
    rw [(hc i).1,(hc i).2,hlevel j hj]
    exact Rat.cast_def _
  have hpoint j (hj : j∈S) i := (hcoordinates j hj).2 i
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]; positivity
  have hCcurv : 0 ≤ Ccurv := by dsimp only [Ccurv]; positivity
  let Cres := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  have hCres : 0 ≤ Cres := by
    dsimp only [Cres,Cc,Ct,C₂,C₃,quarticNonlinearResidualConstant]
    positivity
  have hDeq : D=Cres*(Q:ℝ)/N := by dsimp only [D,Δ,Cres]; ring
  have hD₀ : 0 ≤ D := by
    rw [hDeq]
    exact div_nonneg (mul_nonneg hCres (Nat.cast_nonneg Q)) hN.le
  have hVheight : 0 ≤ Vheight := div_nonneg
    (mul_nonneg hT.le (add_nonneg (modelPhaseJetCoefficient_nonneg σ 1) hδ0))
    (by positivity)
  have hP₂ : 0 < P₂ := add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) hVheight) (abs_nonneg _))
      (Nat.cast_nonneg Q))
  have hpheight j (hj : j∈S) :
      |((p j).1:ℝ)| ≤ P₁ ∧ ((p j).2:ℝ) ≤ P₂ := by
    have hxj : x j 0∈Ioo 0 (W 0) :=
      ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩
    have hh := physicalModelPhase_original_seed_coordinate_heights (rat j 0) Q e r v s
      hσ.le (hF 0) (by norm_num : 1 ≤ 4) hT hM (hA 0) (hW 0)
      hxj (hden j hj 0).1 (hlevel j hj 0)
    exact ⟨hh.1.trans (le_add_of_nonneg_left zero_le_one),
      (le_abs_self _).trans (hh.2.trans (le_add_of_nonneg_left zero_le_one))⟩
  have hpband j (hj : j∈S) :
      (Q:ℝ) ≤ 2*((rp 0:ℝ)*(p j).1+sp 0*(p j).2) := by
    rw [(hcoordinates j hj).1 0]
    exact_mod_cast (hden j hj 0).2
  obtain ⟨j₀,hj₀⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have htransport : (ep 1:ℝ)=(Mat 0:ℝ)*(ep 0)+Mat 1*(rp 0) ∧
      (vp 1:ℝ)=(Mat 0:ℝ)*(vp 0)+Mat 1*(sp 0) ∧
      (rp 1:ℝ)=(Mat 2:ℝ)*(ep 0)+Mat 3*(rp 0) ∧
      (sp 1:ℝ)=(Mat 2:ℝ)*(vp 0)+Mat 3*(sp 0) := by
    simp [ep,vp,rp,sp,Int.cast_add,Int.cast_mul]
  have hbound := physicalModelPhase_signed_height_square_span_first_condition
    (ac:=ac) (bc:=bc) (y₀:=y j₀) (Ccurv:=Ccurv) (Bcut:=Bcut)
    (Cres:=Cres) (Q:=(Q:ℝ)) (D:=D)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    S p x Mat hS hσ hδ hF hT hM hN hR hd hCres hD₀ hD hDeq.le hscale hA hW hxref
    hpheight (fun j hj => (hrect j hj).1) hpband hx hwindow hdisplacement hspan hsourcesquare
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast hrp i)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i)
    hdenregion hcoord hP₂ hCcurv hBcut hBsize hMatdet htransport hGcut
    href hpoint (hy j₀ hj₀) hy (hsource j₀ hj₀).1 (fun j hj => (hsource j hj).2)
  exact hbound


#print axioms physicalModelPhase_actual_fourier_signed_height_square_span_fixed_reference_first_condition

/-- Crossing slope zero costs at most three ACTUAL physical windows.
The near-boundary condition is derived from the inverse Farey endpoints. -/
private theorem physicalModelPhase_zero_crossing_window_count
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε e r v s l w : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M) (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hregion : ∀ z∈Icc l w, 0 < r*z+s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (∀ j∈S, 0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (S.filter (fun j => ¬(0 < α j ∨ β j < 0))).card ≤ 3 := by
  classical
  intro f q α β hcharts hends
  let Z : Finset ℝ := ({0}:Finset ℝ).filter (fun z => z∈Icc l w)
  have hc := physicalModelPhase_farey_boundary_crossing_count S Z x (v:=v)
    hσ hδ hF hT hM hN hR hA hW hphase hsmall hx hwindow
    (fun z hz => hregion z (Finset.mem_filter.mp hz).2) hcharts
  have he : S.filter (fun j => ¬(0 < α j ∨ β j < 0))=
      S.filter (fun j => ∃ z∈Z, z∈Icc (α j) (β j)) := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj,hnot⟩
      have hh := not_or.mp hnot
      have ha : α j ≤ 0 := le_of_not_gt hh.1
      have hb : 0 ≤ β j := le_of_not_gt hh.2
      refine ⟨hj,0,?_,ha,hb⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_singleton_self 0,
        (hends j hj).1.1.trans ha,hb.trans (hends j hj).2.2⟩
    · rintro ⟨hj,z,hz,haz,hzb⟩
      have hz0 : z=0 := Finset.mem_singleton.mp (Finset.mem_filter.mp hz).1
      subst z
      exact ⟨hj,fun hh => hh.elim (not_lt_of_ge haz) (not_lt_of_ge hzb)⟩
  rw [he]
  have hZ : Z.card ≤ 1 := by
    simpa only [Finset.card_singleton] using
      (Finset.card_filter_le (s:=({0}:Finset ℝ)) (p:=fun z => z∈Icc l w))
  exact hc.trans (by omega)

/-- The SAME actual Fourier family and constructed reference supply
the Section 9 two-term First Condition after actual curvature-cell
selection. The accepted physical span is square, not cubic; all source
sector/cutoff and displacement conditions remain explicit. -/
private theorem physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_first_condition
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcesquare : nSpan^2 ≤ M*R)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M := by
 classical
  intro Vheight P₁ P₂ hS f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  obtain ⟨xref,hxr⟩ := physicalModelPhase_actual_matrix_reference_roots_signed
    Q K₀ (rat jref) Mat e r hσ hδ hF₂ hT hM hN hRpos hLref hQ hscale hmesh
    hA hW (hx jref hjref) (hden jref hjref) hMatdet hMatgamma hrefWindow hr
    (hlevel jref hjref) (hMatt jref hjref) (hMatmap jref hjref) hwideL hwideU hrefNear
  refine ⟨xref,hxr,?_⟩
  intro Hspan hdisplacement hspan ar μr G Ccurv Ctay D η Kres hbudget hD hΔ
    hdenregion hends hlarge hBsize hGcut
  let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
  let U := Ccurv*R^4/(N*d^3)
  let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
    (μr 1) (νr 1) (rp 1) (sp 1) U
  have hκp : 0 < κ := modelPhaseThirdLower_pos hσ
  have hchartReal : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hεnonneg : 0 ≤ ε := by dsimp only [ε,Cphys]; positivity
  have hεsmall : 4*ε*R^2 ≤ κ := by
    have hCpos : 0 < Cphys+2 := by dsimp only [Cphys]; positivity
    have heq : 4*ε*R^2=κ/(4*(Cphys+2)) := by
      dsimp only [ε]
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos (by norm_num) hCpos)).mpr
    have hh : 1 ≤ 4*(Cphys+2) := by
      have hp := mul_nonneg hσ.le (add_nonneg hσ.le zero_le_one)
      dsimp only [Cphys]
      linarith only [hp]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hκp.le
  obtain ⟨k,Spre,hSpreS,hSprecard,hcellsPre⟩ :=
    physicalModelPhase_farey_common_cell_selection_signed S Z (fun j => x j 0)
      (ε:=ε) (e:=(e:ℝ)) (r:=(r:ℝ)) (v:=(v:ℝ)) (s:=(s:ℝ))
      hσ hδ (hF₂ 0) hT hM hN hRpos (hA 0) (hW 0) hscale hεsmall hεnonneg
      hchartReal
      (quarticCurvatureBoundaryRoots_card (μr 0) (νr 0) (rp 0) (sp 0)
        (μr 1) (νr 1) (rp 1) (sp 1) U)
      (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
      (fun j hj => by simpa only [mul_comm] using hwindow j hj)
      (fun z hz => by
        have hh := (hdenregion z hz 0).1
        change d ≤ (r:ℝ)*z+s at hh
        exact hd.trans_le hh)
      (by
        intro j hj
        change 0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e ∧
          0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e
        rw [hlevel j hj 0]
        exact ⟨hdl j hj,hdw j hj⟩)
      (by
        intro j hj
        change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈Icc l w ∧
          (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈Icc l w
        rw [hlevel j hj 0]
        exact hends j hj)
  let good := fun j => 0 < α j ∨ β j < 0
  have hbad : (S.filter (fun j => ¬good j)).card ≤ 3 := by
    have hh := physicalModelPhase_zero_crossing_window_count S (fun j => x j 0)
      (ε:=ε) (e:=(e:ℝ)) (r:=(r:ℝ)) (v:=(v:ℝ)) (s:=(s:ℝ))
      (l:=l) (w:=w)
      hσ hδ (hF₂ 0) hT hM hN hRpos (hA 0) (hW 0) hscale hεsmall
      (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
      (fun j hj => by simpa only [mul_comm] using hwindow j hj)
      (fun z hz => by
        have hz' := (hdenregion z hz 0).1
        change d ≤ (r:ℝ)*z+s at hz'
        exact hd.trans_le hz')
      (by
        intro j hj
        change 0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e ∧
          0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e
        rw [hlevel j hj 0]
        exact ⟨hdl j hj,hdw j hj⟩)
      (by
        intro j hj
        change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈Icc l w ∧
          (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈Icc l w
        rw [hlevel j hj 0]
        exact hends j hj)
    convert hh using 1
    congr 1
    apply Finset.filter_congr
    intro j hj
    dsimp only [good,α,β,lo,hi]
    rw [hlevel j hj 0]
  let S₀ := Spre.filter good
  have hS₀S : S₀⊆S := (Finset.filter_subset _ _).trans hSpreS
  have hS₀card : S.card ≤ 99+17*S₀.card := by
    have hb : (Spre.filter (fun j => ¬good j)).card ≤ 3 := by
      apply le_trans (Finset.card_le_card ?_) hbad
      intro j hj
      exact Finset.mem_filter.mpr ⟨hSpreS (Finset.mem_filter.mp hj).1,
        (Finset.mem_filter.mp hj).2⟩
    have he := Finset.card_filter_add_card_filter_not (s:=Spre) good
    change S₀.card+(Spre.filter (fun j => ¬good j)).card=Spre.card at he
    omega
  have hcells j (hj : j∈S₀) := hcellsPre j (Finset.mem_filter.mp hj).1
  have hS₀ : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S₀.card := by
    apply Nat.le_of_mul_le_mul_left (c:=17) _ (by decide)
    apply Nat.le_of_add_le_add_left (a:=99)
    calc
      _ = 99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) := by ring
      _ ≤ _ := hS.trans hS₀card
  have hcells' j (hj : j∈S₀) :
      α j∈finiteBoundaryCell Z l w k ∧ β j∈finiteBoundaryCell Z l w k := by
    have hh := hcells j hj
    change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
        (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈finiteBoundaryCell Z l w k ∧
      (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
        (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈finiteBoundaryCell Z l w k at hh
    rw [hlevel j (hS₀S hj) 0] at hh
    exact hh
  refine ⟨S₀,hS₀S,hS₀card,?_⟩
  intro Blabels Γ L C Cfirst Csecond
  have hx j (hj : j∈S₀) := hx j (hS₀S hj)
  have hwindow j (hj : j∈S₀) := hwindow j (hS₀S hj)
  have hden j (hj : j∈S₀) := hden j (hS₀S hj)
  have hinv j (hj : j∈S₀) := hinv j (hS₀S hj)
  have hlevel j (hj : j∈S₀) := hlevel j (hS₀S hj)
  have hcolor j (hj : j∈S₀) := hcolor j (hS₀S hj)
  have hnear j (hj : j∈S₀) := hnear j (hS₀S hj)
  have hMatt j (hj : j∈S₀) := hMatt j (hS₀S hj)
  have hMatmap j (hj : j∈S₀) := hMatmap j (hS₀S hj)
  have hL j (hj : j∈S₀) := hL j (hS₀S hj)
  have hU j (hj : j∈S₀) := hU j (hS₀S hj)
  have hdl j (hj : j∈S₀) := hdl j (hS₀S hj)
  have hdw j (hj : j∈S₀) := hdw j (hS₀S hj)
  have hnum j (hj : j∈S₀) :
      0 < (v:ℝ)-s*((rat j 0:ℝ)+ε) ∨ (v:ℝ)-s*((rat j 0:ℝ)-ε) < 0 := by
    rcases (Finset.mem_filter.mp hj).2 with hpos | hneg
    · left
      have hh := (lt_div_iff₀ (hdw j hj)).mp hpos
      simpa only [zero_mul] using hh
    · right
      have hh := (div_lt_iff₀ (hdl j hj)).mp hneg
      simpa only [zero_mul] using hh
  have hdyad j (hj : j∈S₀) := hdyad j (hS₀S hj)
  have hanchor j (hj : j∈S₀) := hanchor j (hS₀S hj)
  have hcut j (hj : j∈S₀) := hcut j (hS₀S hj)
  have hcount j (hj : j∈S₀) := hcount j (hS₀S hj)
  have hdisplacement j (hj : j∈S₀) := hdisplacement j (hS₀S hj)
  have hbudget j (hj : j∈S₀) := hbudget j (hS₀S hj)
  have hlarge j (hj : j∈S₀) := hlarge j (hS₀S hj) (Finset.mem_filter.mp hj).2
  have hleft j (hj : j∈S₀) := (hcells' j hj).1
  have hright j (hj : j∈S₀) := (hcells' j hj).2
  exact physicalModelPhase_actual_fourier_signed_height_square_span_fixed_reference_first_condition S₀ Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hd hcoord hBcut
    hS₀ hlevel hcolor hnear hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hdl hdw hnum hdyad
    hanchor hcut hcount xref
    (fun i => ⟨(mul_ne_zero_iff.mp (hxr i).1.ne').1,(hxr i).2.1,(hxr i).2.2.1⟩)
    Hspan hdisplacement hspan hbudget hD hΔ hdenregion hleft hright
    hlarge hBsize hGcut


/-- The square-span First Condition itself controls the whole actual
Fourier family, after an explicit small-entry alternative. This bypasses
transport of an improved Third estimate to intervening occupied points. -/
private theorem physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_family_count
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcesquare : nSpan^2 ≤ M*R)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
 classical
  intro Vheight P₁ P₂ hS
  have hlong := physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_first_condition S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  obtain ⟨xref,hxr,hconsumer⟩ := hlong hS hlevel hcolor hnear
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
  refine ⟨xref,hxr,?_⟩
  intro Hspan hdisplacement hspan ar μr G Ccurv Ctay D η Kres hbudget hD hΔ
    hdenregion hends hsector hBsize hGcut
  obtain ⟨S₀,hS₀S,hS₀card,hfirst⟩ :=
    hconsumer Hspan hdisplacement hspan hbudget hD hΔ hdenregion hends hsector hBsize hGcut
  clear hlong hconsumer
  refine ⟨S₀,hS₀S,hS₀card,?_⟩
  intro Blabels Γ L C Cfirst Csecond Ccount
  by_cases hsmallEntry : |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M
  · exact Or.inl hsmallEntry
  apply Or.inr
  have hS₀ : 32*Blabels ≤ S₀.card := by
    apply Nat.le_of_mul_le_mul_left (c:=17) _ (by decide)
    apply Nat.le_of_add_le_add_left (a:=99)
    calc
      _ = 99+544*Blabels := by ring
      _ ≤ _ := hS.trans hS₀card
  have hBpos : (0:ℝ) < Blabels := by dsimp only [Blabels]; positivity
  have hBnat : 0 < Blabels := by exact_mod_cast hBpos
  have hScard : (0:ℝ) < S₀.card := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 32) hBnat).trans_le hS₀
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hL : 0 < L := mul_pos
    (div_pos hκ (mul_pos (mul_pos (by norm_num) hBpos) hCp)) hScard
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hsecond : 0 ≤ 2*Csecond*N*R^2/M := by
    dsimp only [Csecond]
    positivity
  have hcpos : 0 < |(Mat 2:ℝ)| := hsecond.trans_lt (lt_of_not_ge hsmallEntry)
  change |(Mat 2:ℝ)| ≤ Cfirst*R^4/(L^3*N^2)+Csecond*N*R^2/M at hfirst
  have hsmallTerm : 2*(Csecond*N*R^2/M) < |(Mat 2:ℝ)| := by
    calc
      _ = 2*Csecond*N*R^2/M := by ring
      _ < _ := lt_of_not_ge hsmallEntry
  have hhalf : |(Mat 2:ℝ)|/2 ≤ Cfirst*R^4/(L^3*N^2) := by
    linarith only [hfirst,hsmallTerm]
  have hcube : |(Mat 2:ℝ)| *L^3*N^2 ≤ 2*Cfirst*R^4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < L^3*N^2)).mp hhalf
    nlinarith only [hh]
  have hcellcount : (S₀.card:ℝ) ≤ Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
    apply (le_div_iff₀ (by positivity : 0 < L^2*N^2*|(Mat 2:ℝ)|)).mpr
    have hLrel : (S₀.card:ℝ)=(16*(Blabels:ℝ)*Cphys/κ)*L := by
      dsimp only [L]
      field_simp
    rw [hLrel]
    calc
      _ = (16*(Blabels:ℝ)*Cphys/κ)*(|(Mat 2:ℝ)| *L^3*N^2) := by ring
      _ ≤ (16*(Blabels:ℝ)*Cphys/κ)*(2*Cfirst*R^4) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
      _ = _ := by dsimp only [Ccount]; ring
  have hmass : (S.card:ℝ) ≤ 99+17*(S₀.card:ℝ) := by exact_mod_cast hS₀card
  calc
    _ ≤ 99+17*(S₀.card:ℝ) := hmass
    _ ≤ 99+17*(Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hcellcount (by norm_num))
    _ = _ := by ring


/-- The actual reference-gap family count derives the global physical
displacements, padded square Taylor budgets and source coordinate cutoff
at the SAME selected U and constructed reference under N^10 <= M^3 R^7.
The sector sign is derived after discarding at most three zero-crossing
windows. The original source matrix, selected U, labels and reference are
unchanged. Chart geometry, density and boundary buffers remain explicit. -/
theorem physicalModelPhase_actual_fourier_signed_selected_reference_gap_count
    (Uref : ℕ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d base l w Bcut : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hwideL : ∀ i, x jref i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hreferenceEndpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi)
    (hchartLeft : ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
 classical
  intro Lref
  have hκearly : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hUone : (1:ℝ) ≤ Uref := by exact_mod_cast hUref
  have hUp : (0:ℝ) < Uref := zero_lt_one.trans_le hUone
  have hBtwo : 2 ≤ Bselect := by
    have hp : 0 < 168/modelPhaseThirdLower σ := by positivity
    linarith only [hBselectSize,hp]
  have hBselect : 0 < Bselect := lt_of_lt_of_le (by norm_num) hBtwo
  have hLref : 0 < Lref := by dsimp only [Lref]; positivity
  have hspanMargin :
      2*Lref+56*(Uref:ℝ)/modelPhaseThirdLower σ+2 ≤ Bselect*(Uref:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hBselectSize hUp.le
    have he : (2+168/modelPhaseThirdLower σ)*(Uref:ℝ)=
        2*(Uref:ℝ)+2*Lref+56*(Uref:ℝ)/modelPhaseThirdLower σ := by
      dsimp only [Lref]
      ring
    rw [he] at hh
    linarith only [hh,hUone]
  have hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2 := by
    have hBsq : (4:ℝ) ≤ Bselect^2 := by nlinarith only [hBtwo]
    have hUsq : (1:ℝ) ≤ (Uref:ℝ)^2 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hUone 2
    have hUcube : (Uref:ℝ) ≤ (Uref:ℝ)^3 := by
      have hh := mul_le_mul_of_nonneg_right hUsq hUp.le
      nlinarith only [hh]
    have hscaled : 4*(Uref:ℝ)*R^2 ≤ N^2 := by
      apply le_trans _ hselectedWrap
      calc
        _ ≤ Bselect^2*(Uref:ℝ)*R^2 := by gcongr
        _ ≤ Bselect^2*(Uref:ℝ)^3*R^2 := by gcongr
    have he : modelPhaseThirdLower σ*Lref*R^2=56*(Uref:ℝ)*R^2 := by
      dsimp only [Lref]
      field_simp
    rw [he]
    nlinarith only [hscaled,sq_nonneg N]
  have hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤
      modelPhaseThirdLower σ*Lref/(16*R^2) := by
    have hinside := hfamilyGap jref hjref
    have hdist : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ gapHi-gapLo := by
      rcases hreferenceEndpoint with he | he
      · rw [he,abs_of_nonpos (sub_nonpos.mpr hinside.1)]
        linarith only [hinside.2]
      · rw [he,abs_of_nonneg (sub_nonneg.mpr hinside.2)]
        linarith only [hinside.1]
    apply (hdist.trans hgapWidth).trans
    apply le_of_eq
    dsimp only [Lref]
    field_simp
    ring
  let nSpan := Bselect*(Uref:ℝ)*N
  have hsourcesquare : nSpan^2 ≤ M*R :=
    source_selected_reference_square_span_budget Uref hM hN (zero_lt_one.trans_le hR)
      hRQ hBselect hselectedUpper hscaleTen
  intro Vheight P₁ P₂ hS
  have hlong := physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_family_count S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcesquare hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  obtain ⟨xref,hxr,hconsumer⟩ := hlong hS hlevel hcolor hnear
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hdl hdw hdyad hanchor hcut hcount
  clear hlong
  refine ⟨xref,hxr,?_⟩
  intro Ccurv Ctay D η Kres hD hΔ hdenregion hends hsector hBsize
  let G := minorArcCoordinate (iteratedDeriv 3 (f 0) (round (xref 0))/6) (rp 0) (sp 0)
  have hlw : l ≤ w := (hends jref hjref).1.1.trans (hends jref hjref).1.2
  have hchartLeftPos : 0 < (r:ℝ)*l+s :=
    hd.trans_le (hdenregion l ⟨le_rfl,hlw⟩ 0).1
  have hbase : iteratedDeriv 2 (f 0) (xref 0)/2=(e:ℝ)/r := (hxr 0).2.2.1
  have hGcut : |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) := by
    exact physicalModelPhase_reference_gap_minorArc_cutoff hσ hδ
      (approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl)
      hT hM (hA 0) (hW 0) (hxr 0).2.1 hN (zero_lt_one.trans_le hR)
      (Nat.cast_nonneg Uref) hBselect hBcut hscale hcutMargin
      (by exact_mod_cast hr) hchartLeftPos.ne' (by exact_mod_cast hchart)
      hgapWidth hreferenceDen hselectedWrap hchartLeft hbase
      (by rw [hbase]; exact hreferenceEndpoint)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hpair (j : ℕ) (hj : j∈S) (i : Fin 2) :
      |x j i-x jref i| ≤ 28*(Uref:ℝ)*N/κ := by
    exact physicalModelPhase_actual_matrix_gap_displacement Q (rat jref) (rat j) Mat
      hσ hδ (fun i => approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl)
      hT hM hN (zero_lt_one.trans_le hR) (Nat.cast_nonneg Uref) hA hW
      (fun i => ⟨by linarith only [(hx jref hjref i).1],
        by linarith only [(hx jref hjref i).2]⟩)
      (fun i => ⟨by linarith only [(hx j hj i).1],
        by linarith only [(hx j hj i).2]⟩)
      hscale (hden jref hjref) (hden j hj) hMatdet
      (hMatt jref hjref) (hMatt j hj) (hMatmap jref hjref) (hMatmap j hj)
      hgapWidth (hfamilyGap jref hjref) (hfamilyGap j hj)
      (hlevel jref hjref) (hlevel j hj) i
  let span := (Lref+28*(Uref:ℝ)/κ)*N
  have hspan0 : 0 ≤ span := by dsimp only [span]; positivity
  have hdisplacement (j : ℕ) (hj : j∈S) (i : Fin 2) :
      |x j i-xref i| ≤ span := by
    calc
      _ ≤ |x j i-x jref i|+|x jref i-xref i| := abs_sub_le _ _ _
      _ ≤ 28*(Uref:ℝ)*N/κ+Lref*N := by
        apply add_le_add (hpair j hj i)
        rw [abs_sub_comm]
        exact (hxr i).2.2.2.1
      _ = span := by dsimp only [span]; ring
  have hspanBuffer : 2*span+2*N ≤ nSpan := by
    have hh := mul_le_mul_of_nonneg_right hspanMargin hN.le
    change (2*Lref+56*(Uref:ℝ)/κ+2)*N ≤ nSpan at hh
    have he : (2*Lref+56*(Uref:ℝ)/κ+2)*N=2*span+2*N := by
      dsimp only [span]
      ring
    rwa [he] at hh
  have hspan : 2*span+1 ≤ nSpan := by
    linarith only [hspanBuffer,hNtwo]
  have hHN : H ≤ N := by
    apply (div_le_iff₀ (show 0 < Cphys+2 by dsimp only [Cphys]; positivity)).mpr
    have hh : 1 ≤ Cphys+2 := by
      have hp := mul_nonneg hσ.le (add_nonneg hσ.le zero_le_one)
      dsimp only [Cphys]
      linarith only [hp]
    simpa only [one_mul,mul_one,mul_comm] using mul_le_mul_of_nonneg_right hh hN.le
  have hbudget (j : ℕ) (hj : j∈S) (i : Fin 2) :
      (H+|x j i-xref i|+1)^2 ≤ M*R := by
    have hH0 : 0 ≤ H := by dsimp only [H,Cphys]; positivity
    have hb : H+|x j i-xref i|+1 ≤ nSpan := by
      linarith only [hdisplacement j hj i,hspanBuffer,hHN,hspan0,hNtwo]
    exact (pow_le_pow_left₀ (by positivity) hb 2).trans hsourcesquare
  exact hconsumer (fun _ => span) hdisplacement (fun _ => hspan)
    hbudget hD hΔ hdenregion hends hsector hBsize hGcut


#print axioms physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_first_condition
#print axioms physicalModelPhase_actual_fourier_signed_height_square_span_selected_cell_family_count
#print axioms physicalModelPhase_actual_fourier_signed_selected_reference_gap_count

#print axioms physicalModelPhase_zero_crossing_window_count

example
    {N : ℕ} {l w B α β δ : ℝ}
    (hw : w < 0) (hlw : l ≤ w) (hB : 1 ≤ B) (hδ : 0 ≤ δ) :
    let P := HuxleyLinearForm.fareySector N (-w) (-l)
    let S := P.image (fun p : ℤ × ℤ => (-p.1,p.2))
    max ((w-l)*(N:ℝ)^2/B) 2 ≤ (S.card:ℝ) →
    3840*B*δ*((-l)*(N:ℝ))*(N:ℝ) < (S.card:ℝ) →
    (∀ p∈S, ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) →
    ∀ p : ℤ × ℤ, 0 ≤ -(p.1:ℝ) → -(p.1:ℝ) ≤ 12*((-l)*(N:ℝ)) →
      0 ≤ (p.2:ℝ) → (p.2:ℝ) ≤ 12*(N:ℝ) → ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*round α+p.2*round β :=
  HuxleyNegativeSlopesScratch.negative_fareySector_integer_labels_enlarged_rectangle_all_slopes (N:=N) (l:=l) (w:=w) (B:=B) (α:=α) (β:=β) (δ:=δ) hw hlw hB hδ

example
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    (v:ℝ)-s*((rat 0:ℝ)-ε) < 0 →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := (HuxleyLinearForm.fareySector K (-β) (-α)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    3840*128*η*((-α)*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      D/(pseed.2:ℝ) :=
  HuxleyNegativeSlopesScratch.physicalModelPhase_actual_fourier_original_seed_bounds_all_negative_slopes (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    (Uref : ℕ) {Bselect gapLo gapHi : ℝ}
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d base l w Bcut : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hwideL : ∀ i, x jref i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : R^2 ≤ (r:ℝ)^2*(Uref:ℝ))
    (hgapWidth : gapHi-gapLo ≤ 7*(Uref:ℝ)/(2*R^2))
    (hreferenceEndpoint : (e:ℝ)/r=gapLo ∨ (e:ℝ)/r=gapHi)
    (hchartLeft : ((e:ℝ)*l+v)/((r:ℝ)*l+s)∈Icc gapLo gapHi)
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ j∈S, (rat j 0:ℝ)∈Icc gapLo gapHi) :
    let Lref := 56*(Uref:ℝ)/modelPhaseThirdLower σ
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    99+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => if 0 < α j then HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
      else (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
        (fun p : ℤ × ℤ => (-p.1,p.2))
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, (0 < α j ∨ β j < 0) → 3840*128*η j*((max |α j| |β j|)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 99+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cfirst := 128*Cphys*(Γ^2*C+Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Csecond := 32*(modelPhaseJetCoefficient σ 3+δ)/κ^2
    let Ccount := 32*(Blabels:ℝ)*Cphys*Cfirst/κ
    |(Mat 2:ℝ)| ≤ 2*Csecond*N*R^2/M ∨
      (S.card:ℝ) ≤ 99+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  HuxleyNegativeSlopesScratch.physicalModelPhase_actual_fourier_signed_selected_reference_gap_count Uref (Bselect:=Bselect) (gapLo:=gapLo) (gapHi:=gapHi) S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hinv hchart hr hd hcoord hBcut hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hreferenceEndpoint hchartLeft hRQ hselectedUpper hscaleTen hfamilyGap


end HuxleyNegativeSlopesScratch

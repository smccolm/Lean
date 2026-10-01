import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyTriangularQuarticScratch

/-- Endpoint compression for the actual source roots; the inverse chart
and its derivatives are identified rather than assumed as source data. -/
private theorem positive_difference_actual_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ 1/8 → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let G := fun z : ℝ × ℝ =>
      (iteratedDeriv 3 F z.2-iteratedDeriv 3 F (z.2+η*z.1))/(σ*η)
    let t : Fin 2 → ℝ := ![l,r]
    let z₀ := (y₀,H (y₀,x₀))
    l < r →
    (∀ i, xa i∈Icc (1:ℝ) 2 ∧ xb i∈Icc (1:ℝ) 2 ∧
      H (ya,xa i)=t i ∧ H (yb,xb i)=t i+b) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t i+b):ℝ × ℝ)-z₀‖ < a) →
    (∀ i, |G (yb,xb i)-G (ya,xa i)| ≤ δ) →
    ‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ C*δ := by
  obtain ⟨a₀,ha₀,hcompression⟩ := positive_difference_constructed_endpoint_compression hσ hc hU
  let a := min a₀ (1/2:ℝ)
  let R := max 1 (max (3*U/σ) (2*σ/c))
  let κ := (c/(6*U))^2*(c^2*c/(6*U^4))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  refine ⟨a,64*R^6/κ,lt_min ha₀ (by norm_num),min_le_right _ _,by positivity,?_⟩
  intro F η x₀ y₀ ya yb b l r δ xa xb hη hηmax hx₀ hy₀ hya hyb
    hf hbound htests H G t z₀ hlr hroots hends hnear
  let ρ := fun w : ℝ × ℝ =>
    Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
  let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
  have hxext x (hx : x∈Icc (1:ℝ) 2) : x∈Ioo (3/4:ℝ) (9/4) :=
    ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  have hyext y (hy : y∈Icc (1:ℝ) 2) : y∈Icc (1/2:ℝ) 3 :=
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
  have hGder x y (hx : x∈Icc (1:ℝ) 2) (hy : y∈Icc (1:ℝ) 2) :
      fderiv ℝ H (y,x) (0,1)=G (y,x) := by
    have hxpos : 0 < x := by linarith only [hx.1]
    have hypos : 0 < y := by linarith only [hy.1]
    exact (positive_difference_curvature_directions F (σ:=σ) hxpos
      (add_pos hxpos (mul_pos hη hypos)) hf 2).2.1
  have hcanonical i : |g (yb,t i+b)-g (ya,t i)| ≤ δ := by
    have ha : ρ (ya,t i)=xa i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).1) (hyext _ hya)
      hf hbound htests (hroots i).2.2.1
    have hb : ρ (yb,t i+b)=xb i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).2.1) (hyext _ hyb)
      hf hbound htests (hroots i).2.2.2
    dsimp only [g]
    rw [ha,hb,hGder _ _ (hroots i).1 hya,hGder _ _ (hroots i).2.1 hyb]
    exact hnear i
  have hsegment y β
      (hl : ‖((y,l+β):ℝ × ℝ)-z₀‖ < a)
      (hr : ‖((y,r+β):ℝ × ℝ)-z₀‖ < a)
      u (hu : u∈Icc l r) : ‖((y,u+β):ℝ × ℝ)-z₀‖ < a := by
    change max |y-z₀.1| |l+β-z₀.2| < a at hl
    change max |y-z₀.1| |r+β-z₀.2| < a at hr
    change max |y-z₀.1| |u+β-z₀.2| < a
    refine max_lt_iff.mpr ⟨(max_lt_iff.mp hl).1,abs_lt.mpr ⟨?_,?_⟩⟩
    · linarith only [(abs_lt.mp (max_lt_iff.mp hl).2).1,hu.1]
    · linarith only [(abs_lt.mp (max_lt_iff.mp hr).2).2,hu.2]
  have hpts u (hu : u∈Icc l r) :
      ‖((ya,u):ℝ × ℝ)-z₀‖ < a₀ ∧ ‖((yb,u+b):ℝ × ℝ)-z₀‖ < a₀ := by
    constructor
    · have hh := hsegment ya 0 (by simpa only [t,Matrix.cons_val_zero,add_zero] using (hends 0).1)
        (by simpa only [t,Matrix.cons_val_one,Matrix.head_cons,add_zero] using (hends 1).1) u hu
      have hh' : ‖((ya,u):ℝ × ℝ)-z₀‖ < a := by simpa only [add_zero] using hh
      exact hh'.trans_le (min_le_left _ _)
    · exact (hsegment yb b (hends 0).2 (hends 1).2 u hu).trans_le (min_le_left _ _)
  have hlen : r-l ≤ 2 := by
    have hl := (norm_snd_le (((ya,l):ℝ × ℝ)-z₀)).trans_lt (hends 0).1
    have hr := (norm_snd_le (((ya,r):ℝ × ℝ)-z₀)).trans_lt (hends 1).1
    change |l-z₀.2| < a at hl
    change |r-z₀.2| < a at hr
    have ha : a ≤ 1/2 := min_le_right _ _
    linarith only [(abs_lt.mp hl).1,(abs_lt.mp hr).2,ha]
  have hh := hcompression F η x₀ y₀ ya yb b l r δ hη hηmax hx₀ hy₀
    hf hbound htests hlr hlen hpts (hcanonical 0) (hcanonical 1)
  have hdiv := (le_div_iff₀ hκ).mpr (by nlinarith only [hh] :
    ‖((yb-ya,b):ℝ × ℝ)‖*(r-l)*κ ≤ 64*R^6*δ)
  exact hdiv.trans_eq (by ring)

/-- Physical upper-triangular endpoint compression with the measured
rounded Third Condition. All normalization and rounding losses are derived. -/
private theorem positive_difference_physical_upper_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b Δ T M : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ 1/8 → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 ≤ Δ →
    (∀ i, xa i∈Icc M (2*M) ∧ xb i∈Icc M (2*M)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let u := fun i => iteratedDeriv 2 (f ya) (xa i)/2
    let t := fun i => (2*M^2/T)*u i
    let bnorm := 2*M^2*b/T
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,H (y₀,x₀))
    u 0 < u 1 →
    (∀ i, iteratedDeriv 2 (f yb) (xb i)/2=u i+b) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    4*M^4*|b| *(u 1-u 0) ≤ C*(Δ+1/M)*T^2 := by
  obtain ⟨a,C,ha,hac,hC,hcompression⟩ :=
    positive_difference_actual_endpoint_compression hσ hc hU
  let B := max 1 (max (3*U/σ) (2*σ/c))
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨a,C*B,ha,hac,mul_pos hC hB,?_⟩
  intro F η x₀ y₀ ya yb b Δ T M xa xb hη hηmax hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f μ u t bnorm H z₀ hu hmap hthird hends
  have hMp : 0 < M := by linarith only [hM]
  let G := fun z : ℝ × ℝ =>
    (iteratedDeriv 3 F z.2-iteratedDeriv 3 F (z.2+η*z.1))/(σ*η)
  have hnorm z (hz : z∈Icc M (2*M)) : z/M∈Icc (1:ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hMp).mpr (by simpa using hz.1)
    · exact (div_le_iff₀ hMp).mpr hz.2
  have hpos z (hz : z∈Icc M (2*M)) : 0 < z := hMp.trans_le hz.1
  have hroundpos z (hz : z∈Icc M (2*M)) : (0:ℝ) < round z := by
    have hh := abs_le.mp (abs_sub_round z)
    linarith only [hh.2,hz.1,hM]
  have hd n z y (hz : 0 < z) (hy : y∈Icc (1:ℝ) 2) :
      iteratedDeriv n (f y) z=
        T/M^n*((iteratedDeriv n F (z/M)-iteratedDeriv n F (z/M+η*y))/(σ*η)) :=
    positive_difference_physical_iteratedDeriv F hMp hz
      (mul_nonneg hη.le (by linarith only [hy.1])) hf n
  have hrootA i : H (ya,xa i/M)=t i := by
    dsimp only [t,u]
    rw [hd 2 _ _ (hpos _ (hpoints i).1) hya]
    change H (ya,xa i/M)=(2*M^2/T)*(T/M^2*H (ya,xa i/M)/2)
    field_simp
  have hrootB i : H (yb,xb i/M)=t i+bnorm := by
    have he := congrArg (fun z : ℝ => (2*M^2/T)*z) (hmap i)
    rw [hd 2 _ _ (hpos _ (hpoints i).2) hyb] at he
    change (2*M^2/T)*(T/M^2*H (yb,xb i/M)/2)=(2*M^2/T)*(u i+b) at he
    change H (yb,xb i/M)=(2*M^2/T)*u i+2*M^2*b/T
    field_simp at he ⊢
    nlinarith only [he]
  have hrounded i :
      |G (yb,(round (M*(xb i/M)):ℝ)/M)/
        G (ya,(round (M*(xa i/M)):ℝ)/M)-1| ≤ Δ := by
    have he z : M*(z/M)=z := mul_div_cancel₀ z hMp.ne'
    rw [he,he]
    have ha : μ ya (xa i)=(T/(6*M^3))*G (ya,(round (xa i):ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos _ (hpoints i).1) hya]
      dsimp only [G]
      ring
    have hb : μ yb (xb i)=(T/(6*M^3))*G (yb,(round (xb i):ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos _ (hpoints i).2) hyb]
      dsimp only [G]
      ring
    have hh := hthird i
    rw [ha,hb,mul_div_mul_left _ _ (by positivity : T/(6*M^3) ≠ 0)] at hh
    exact hh
  have hnear i : |G (yb,xb i/M)-G (ya,xa i/M)| ≤ B*(Δ+1/M) :=
    positive_difference_rounded_third_bound F hσ hc hU hη hηmax hM
      (hnorm _ (hpoints i).1) (hnorm _ (hpoints i).2) hya hyb
      hf hbound htests hΔ (hrounded i)
  have ht : t 0 < t 1 := mul_lt_mul_of_pos_left hu (by positivity)
  have htvec (i : Fin 2) : (![t 0,t 1] : Fin 2 → ℝ) i=t i := by fin_cases i <;> rfl
  have hh := hcompression F η x₀ y₀ ya yb bnorm (t 0) (t 1) (B*(Δ+1/M))
    (fun i => xa i/M) (fun i => xb i/M) hη hηmax hx₀ hy₀ hya hyb hf hbound htests ht
    (by intro i; rw [htvec]; exact ⟨hnorm _ (hpoints i).1,hnorm _ (hpoints i).2,hrootA i,hrootB i⟩)
    (by intro i; rw [htvec]; exact hends i)
    hnear
  have hn : 2*M^2*|b|/T ≤ ‖((yb-ya,bnorm):ℝ × ℝ)‖ := by
    have he := norm_snd_le ((yb-ya,bnorm):ℝ × ℝ)
    simpa only [bnorm,Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos hT,
      abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (sq_nonneg M)] using he
  have hm := (mul_le_mul_of_nonneg_right hn (sub_nonneg.mpr ht.le)).trans hh
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg T)
  have he : (2*M^2*|b|/T*(t 1-t 0))*T^2=4*M^4*|b| *(u 1-u 0) := by
    dsimp only [t]
    field_simp
    ring
  rw [he] at hm'
  exact hm'.trans_eq (by ring)

private theorem huxley_upper_endpoint_source_scale
    {κ L R M N T S E C D b g : ℝ}
    (hL : 0 < L) (hR : 1 ≤ R) (hM : 0 < M)
    (hN : 0 < N) (hS : 0 < S)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hNL : (L*N)^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hST : S ≤ E*T) (hlow : κ*L/(8*R^2) ≤ g)
    (hu : 4*M^4*b*g ≤ C*(D*R^2/(L^2*N^2)+1/M)*S^2) :
    κ*b*L^3*N^4 ≤ 2*C*(D+1)*E^2*M^2 := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hNLR : L^2*N^2 ≤ M*R^2 := by
    calc
      _ = (L*N)^2 := by ring
      _ ≤ M*R := hNL
      _ ≤ M*R^2 := mul_le_mul_of_nonneg_left (by nlinarith only [hR] : R ≤ R^2) hM.le
  have hInv : 1/M ≤ R^2/(L^2*N^2) :=
    (div_le_div_iff₀ hM (by positivity)).mpr (by nlinarith only [hNLR])
  have hcost : D*R^2/(L^2*N^2)+1/M ≤ (D+1)*R^2/(L^2*N^2) := by
    calc
      _ ≤ D*R^2/(L^2*N^2)+R^2/(L^2*N^2) := add_le_add le_rfl hInv
      _ = _ := by ring
  have hsquare : S^2 ≤ E^2*T^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hS.le hST 2
  have hupper : 4*M^4*b*g ≤ C*((D+1)*R^2/(L^2*N^2))*(E^2*T^2) :=
    hu.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hcost hC) hsquare (sq_nonneg S) (by positivity))
  have hh := (mul_le_mul_of_nonneg_left hlow
    (by positivity : 0 ≤ 4*M^4*b)).trans hupper
  have heleft : 4*M^4*b*(κ*L/(8*R^2))=κ*b*L*M^4/(2*R^2) := by ring
  have heright : C*((D+1)*R^2/(L^2*N^2))*(E^2*T^2)=
      C*(D+1)*R^2*E^2*T^2/(L^2*N^2) := by ring
  rw [heleft,heright] at hh
  have hcross := (div_le_div_iff₀ (by positivity : 0 < 2*R^2)
    (by positivity : 0 < L^2*N^2)).mp hh
  have hmul := mul_le_mul_of_nonneg_right hcross (sq_nonneg N)
  have hsq : T^2*N^2*R^4=M^6 := by
    have he := congrArg (fun z : ℝ => z^2) hscale
    nlinarith only [he]
  have hright : (C*(D+1)*R^2*E^2*T^2*(2*R^2))*N^2=
      2*C*(D+1)*E^2*M^6 := by
    calc
      _ = 2*C*(D+1)*E^2*(T^2*N^2*R^4) := by ring
      _ = _ := by rw [hsq]
  rw [hright] at hmul
  apply (mul_le_mul_iff_right₀ (pow_pos hM 4)).mp
  convert hmul using 1 <;> ring

/-- The two genuine quartic witnesses discharge the improved Third
Condition for a source-linked upper-triangular difference family.
Only the original endpoint chart geometry and exact physical source identity remain explicit. -/
theorem positive_difference_quartic_upper_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0+b*r 0 ∧ v 1=v 0+b*s 0 ∧ r 1=r 0 ∧ s 1=s 0) →
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
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
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (∀ i, f i=fun z => Src (yp i) ((A i:ℝ)+z)) →
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a) →
    κ*|b| *L^3*N^4 ≤ 2*Csrc*(C+1)*E^2*M^2 := by
  obtain ⟨a,Csrc,ha,_hac,hCsrc,hcompression⟩ :=
    positive_difference_physical_upper_endpoint_compression hσsrc hcsrc hUsrc
  refine ⟨a,Csrc,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb b Tsrc E σ δ T M N R L d K α β x F A W x₀ e r v s x₁
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Src Hsrc center hsource hlocalEnds
  have hxleft : x 0∈Icc (x 0) (x 7) := ⟨le_rfl,hmono.monotone (by decide)⟩
  have hxright : x 7∈Icc (x 0) (x 7) := ⟨hmono.monotone (by decide),le_rfl⟩
  have hcurvOrder u w (hu : u∈Icc (x 0) (x 7)) (hv : w∈Icc (x 0) (x 7))
      (huv : u ≤ w) i :
      iteratedDeriv 2 (f i) (x₁ w i)/2 ≤ iteratedDeriv 2 (f i) (x₁ u i)/2 := by
    apply sub_nonneg.mp
    have hdu : 0 < D u i := hd.trans_le (hden u hu i)
    have hdv : 0 < D w i := hd.trans_le (hden w hv i)
    rw [hpoint u hu i,hpoint w hv i,div_sub_div _ _ hdu.ne' hdv.ne']
    have hnum : (e i*u+v i)*D w i-D u i*(e i*w+v i)=w-u := by
      dsimp only [D]
      linear_combination (w-u)*hdet i
    rw [hnum]
    exact div_nonneg (sub_nonneg.mpr huv) (mul_pos hdu hdv).le
  have hlocal z (hz : z∈Icc (x 0) (x 7)) i :
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a := by
    have hl := hlocalEnds (x 7) (by simp) i
    have hu := hlocalEnds (x 0) (by simp) i
    have hlo := mul_le_mul_of_nonneg_left (hcurvOrder z (x 7) hz hxright hz.2 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    have hhi := mul_le_mul_of_nonneg_left (hcurvOrder (x 0) z hxleft hz hz.1 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ (x 7) i)/2)-center.2| < a at hl
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ (x 0) i)/2)-center.2| < a at hu
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)-center.2| < a
    refine max_lt_iff.mpr ⟨(max_lt_iff.mp hl).1,abs_lt.mpr ⟨?_,?_⟩⟩
    · linarith only [(abs_lt.mp (max_lt_iff.mp hl).2).1,hlo]
    · linarith only [(abs_lt.mp (max_lt_iff.mp hu).2).2,hhi]
  let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
  obtain ⟨z₀,hz₀,z₁,hz₁,hG,hthird⟩ := physicalModelPhase_quartic_two_long_block_witnesses
    x hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet
    hden hdenUpper hmono hbase hpoint hsquare hgap hres
  have hz₀' : z₀∈Icc (x 0) (x 7) :=
    ⟨hz₀.1.le,hz₀.2.le.trans (hmono.monotone (by decide))⟩
  have hz₁' : z₁∈Icc (x 0) (x 7) :=
    ⟨(hmono.monotone (by decide)).trans hz₁.1.le,hz₁.2.le⟩
  have hzorder : z₀ ≤ z₁ := hz₀.2.le.trans
    ((hmono.monotone (by decide : (3:Fin 8) ≤ 4)).trans hz₁.1.le)
  have hdpos z (hz : z∈Icc (x 0) (x 7)) i : 0 < D z i :=
    hd.trans_le (hden z hz i)
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hround := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ 0)
    hT hM (hA 0) (hW 0) (hx₀ 0)
  have hμbounds := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ 0)
    hT hM (hA 0) (hW 0) hround.1
  have hμ : 0 < μ 0 := lt_of_lt_of_le (by positivity) hμbounds.1
  let z : Fin 2 → ℝ := ![z₁,z₀]
  let profile : ℝ → ℝ := fun t => iteratedDeriv 2 (f 0) (x₁ t 0)/2
  have hz p : z p∈Icc (x 0) (x 7) := by
    fin_cases p
    · exact hz₁'
    · exact hz₀'
  have hdiff : profile z₀-profile z₁=(z₁-z₀)/(D z₀ 0*D z₁ 0) := by
    dsimp only [profile]
    rw [hpoint z₀ hz₀' 0,hpoint z₁ hz₁' 0,
      div_sub_div _ _ (hdpos z₀ hz₀' 0).ne' (hdpos z₁ hz₁' 0).ne']
    congr 1
    dsimp only [D]
    linear_combination (z₁-z₀)*hdet 0
  have horder : profile z₁ ≤ profile z₀ := sub_nonneg.mp (by
    rw [hdiff]
    exact div_nonneg (sub_nonneg.mpr hzorder)
      (mul_pos (hdpos z₀ hz₀' 0) (hdpos z₁ hz₁' 0)).le)
  have hGid t (ht : t∈Icc (x 0) (x 7)) : profile t-e 0/r 0=3*μ 0*G t := by
    rw [show profile t=(e 0*t+v 0)/(r 0*t+s 0) from hpoint t ht 0]
    simpa only [mul_one,div_one] using
      (farey_curvature_coordinate_identity (u:=t) (t:=1) hμ.ne' (hr 0)
        one_ne_zero (by simpa only [mul_one] using (hdpos t ht 0).ne') (hdet 0))
  have hdiffG : profile z₀-profile z₁=3*μ 0*(G z₀-G z₁) := by
    linarith only [hGid z₀ hz₀',hGid z₁ hz₁']
  have hGorder : 0 ≤ G z₀-G z₁ := by
    apply (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num : (0:ℝ)<3) hμ)).mp
    rw [← hdiffG]
    exact sub_nonneg.mpr horder
  rw [abs_sub_comm,abs_of_nonneg hGorder] at hG
  have hlo : κ*L/(8*R^2) ≤ profile z₀-profile z₁ := by
    have hmul := mul_le_mul_of_nonneg_left hG
      (mul_pos (by norm_num : (0:ℝ)<3) hμ).le
    calc
      _ = 3*(κ*T/(6*M^3))*(L*N/4) := by
        have hTval : T=M^3/(N*R^2) :=
          (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
        rw [hTval]
        field_simp
        ring_nf
      _ ≤ 3*μ 0*(L*N/4) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hμbounds.1 (by norm_num : (0:ℝ) ≤ 3))
        (by positivity)
      _ ≤ _ := by linarith only [hmul,hdiffG]
  let Δ := C*R^2/(L^2*N^2)
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans (hthird z₀ (by simp))
  have hC : 0 ≤ C := by
    have hh : 0 ≤ C*(R^2/(L^2*N^2)) := by simpa only [Δ,mul_div_assoc] using hΔ
    have hp : 0 < R^2/(L^2*N^2) := by positivity
    nlinarith only [hh,hp]
  have hDsame t : D t 1=D t 0 := by
    dsimp only [D]
    rw [htransport.2.2.1,htransport.2.2.2]
  have hmap t (ht : t∈Icc (x 0) (x 7)) :
      iteratedDeriv 2 (f 1) (x₁ t 1)/2=profile t+b := by
    change _=iteratedDeriv 2 (f 0) (x₁ t 0)/2+b
    rw [hpoint t ht 1,hpoint t ht 0,hDsame]
    rw [htransport.1,htransport.2.1]
    have hd0 : r 0*t+s 0 ≠ 0 := (hdpos t ht 0).ne'
    dsimp only [D]
    field_simp [hd0]
    ring
  have hthird' p : |μnew (z p) 1/μnew (z p) 0-1| ≤ Δ := by
    have hh := hthird (z p) (by fin_cases p <;> simp [z])
    change |μnew (z p) 1*(D (z p) 1)^3/(μnew (z p) 0*(D (z p) 0)^3)-1| ≤ Δ at hh
    rw [hDsame] at hh
    rwa [mul_div_mul_right _ _ (pow_ne_zero 3 (hdpos _ (hz p) 0).ne')] at hh
  have hjet i k t : iteratedDeriv k (f i) t=
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hrounded i t :
      iteratedDeriv 3 (f i) (round t)=
        iteratedDeriv 3 (Src (yp i)) (round ((A i:ℝ)+t)) := by
    rw [hjet,round_intCast_add,Int.cast_add]
  let xa := fun p => (A 0:ℝ)+x₁ (z p) 0
  let xb := fun p => (A 1:ℝ)+x₁ (z p) 1
  have hphysical p : xa p∈Icc M (2*M) ∧ xb p∈Icc M (2*M) := by
    constructor
    · exact ⟨by dsimp only [xa]; linarith only [hA 0,(hx₁ _ (hz p) 0).1],
        by dsimp only [xa]; linarith only [hW 0,(hx₁ _ (hz p) 0).2]⟩
    · exact ⟨by dsimp only [xb]; linarith only [hA 1,(hx₁ _ (hz p) 1).1],
        by dsimp only [xb]; linarith only [hW 1,(hx₁ _ (hz p) 1).2]⟩
  have hua p : iteratedDeriv 2 (Src ya) (xa p)/2=profile (z p) := by
    exact (congrArg (fun u : ℝ => u/2) (hjet 0 2 (x₁ (z p) 0))).symm
  have hub p : iteratedDeriv 2 (Src yb) (xb p)/2=profile (z p)+b := by
    exact (congrArg (fun u : ℝ => u/2) (hjet 1 2 (x₁ (z p) 1))).symm.trans (hmap _ (hz p))
  have hstrict : profile z₁ < profile z₀ := by
    have hp : 0 < κ*L/(8*R^2) := by positivity
    linarith only [hlo,hp]
  have hh := hcompression Fsrc η xcenter ycenter ya yb b Δ Tsrc M xa xb
    hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hΔ hphysical
    (by
      change iteratedDeriv 2 (Src ya) (xa 0)/2 < iteratedDeriv 2 (Src ya) (xa 1)/2
      rw [hua,hua]
      exact hstrict)
    (by
      intro p
      change iteratedDeriv 2 (Src yb) (xb p)/2=iteratedDeriv 2 (Src ya) (xa p)/2+b
      rw [hua,hub])
    (by
      intro p
      have hh := hthird' p
      change |(iteratedDeriv 3 (f 1) (round (x₁ (z p) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (x₁ (z p) 0))/6)-1| ≤ Δ at hh
      rw [hrounded,hrounded] at hh
      exact hh)
    (by
      intro p
      change ‖((ya,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa p)/2)):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa p)/2)+2*M^2*b/Tsrc):ℝ × ℝ)-center‖ < a
      constructor
      · rw [hua]
        exact hlocal _ (hz p) 0
      · have he : (2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa p)/2)+
            2*M^2*b/Tsrc=(2*M^2/Tsrc)*(iteratedDeriv 2 (f 1) (x₁ (z p) 1)/2) := by
          rw [hua,hmap _ (hz p)]
          ring
        rw [he]
        exact hlocal _ (hz p) 1)
  change 4*M^4*|b| *(iteratedDeriv 2 (Src ya) (xa 1)/2-iteratedDeriv 2 (Src ya) (xa 0)/2) ≤
    Csrc*(Δ+1/M)*Tsrc^2 at hh
  rw [hua,hua] at hh
  exact huxley_upper_endpoint_source_scale hL hR hM hN hTsrc hCsrc.le hC
    (abs_nonneg b) hNL hscale hsourceScale hlo hh

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0+b*r 0 ∧ v 1=v 0+b*s 0 ∧ r 1=r 0 ∧ s 1=s 0) →
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
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
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (∀ i, f i=fun z => Src (yp i) ((A i:ℝ)+z)) →
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a) →
    κ*|b| *L^3*N^4 ≤ 2*Csrc*(C+1)*E^2*M^2 :=
  HuxleyTriangularQuarticScratch.positive_difference_quartic_upper_long_block_constraint (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

/-- Source-defined normalized difference phases consume the actual
quartic witnesses and the original endpoint chart geometry. The physical
phase identities and integer-rounded jet correspondence are derived. -/
theorem positive_difference_normalized_quartic_upper_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*(![ya,yb] : Fin 2 → ℝ) i))/(σsrc*η)
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0+b*r 0 ∧ v 1=v 0+b*s 0 ∧ r 1=r 0 ∧ s 1=s 0) →
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
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
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a) →
    κ*|b| *L^3*N^4 ≤ 2*Csrc*(C+1)*E^2*M^2 := by
  obtain ⟨a,Csrc,ha,hCsrc,hcore⟩ :=
    positive_difference_quartic_upper_long_block_constraint hσsrc hcsrc hUsrc
  refine ⟨a,Csrc,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb b Tsrc E σ δ T M N R L d K α β x A W x₀ e r v s x₁
    F hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Hsrc center hlocalEnds
  let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
  have hsource i : f i=fun z => Src (yp i) ((A i:ℝ)+z) := by
    funext z
    dsimp only [f,heathBrownPhysicalPhase,F,Src,yp]
    field_simp
  exact hcore Fsrc η xcenter ycenter ya yb b Tsrc E x (F:=F) A
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hbase hpoint hsquare hgap hres hsource hlocalEnds


example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    {σ δ T M N R L d K α β : ℝ} (x : Fin 8 → ℝ)
    (A : Fin 2 → ℤ) {W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ},
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*(![ya,yb] : Fin 2 → ℝ) i))/(σsrc*η)
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 < d) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, r i ≠ 0) →
    (∀ i, v i*r i-e i*s i=1) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d) →
    (StrictMono x) →
    (T*N*R^2=M^3) →
    (e 1=e 0+b*r 0 ∧ v 1=v 0+b*s 0 ∧ r 1=r 0 ∧ s 1=s 0) →
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
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
    let yp : Fin 2 → ℝ := ![ya,yb]
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (x₁ z i)/2)):ℝ × ℝ)-center‖ < a) →
    κ*|b| *L^3*N^4 ≤ 2*Csrc*(C+1)*E^2*M^2 :=
  HuxleyTriangularQuarticScratch.positive_difference_normalized_quartic_upper_long_block_constraint (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

end HuxleyTriangularQuarticScratch
#print axioms HuxleyTriangularQuarticScratch.positive_difference_actual_endpoint_compression

#print axioms HuxleyTriangularQuarticScratch.positive_difference_physical_upper_endpoint_compression

#print axioms HuxleyTriangularQuarticScratch.huxley_upper_endpoint_source_scale

#print axioms HuxleyTriangularQuarticScratch.positive_difference_quartic_upper_long_block_constraint

#print axioms HuxleyTriangularQuarticScratch.positive_difference_normalized_quartic_upper_long_block_constraint

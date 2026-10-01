import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyLowerQuarticScratch

private theorem positive_difference_actual_reciprocal_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b l r δ : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ η₀ → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
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
    let z₀ := (y₀,(H (y₀,x₀))⁻¹)
    l < r →
    (∀ i, xa i∈Icc (1:ℝ) 2 ∧ xb i∈Icc (1:ℝ) 2 ∧
      H (ya,xa i)=(t i)⁻¹ ∧ H (yb,xb i)=(t i+b)⁻¹) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧ ‖((yb,t i+b):ℝ × ℝ)-z₀‖ < a) →
    (∀ i, |G (yb,xb i)*((H (yb,xb i))⁻¹)^3-
      G (ya,xa i)*((H (ya,xa i))⁻¹)^3| ≤ δ) →
    ‖((yb-ya,b):ℝ × ℝ)‖*(r-l) ≤ C*δ := by
  obtain ⟨η₀,a₀,C,hη₀,hηcap,ha₀,hC,hcompression⟩ :=
    positive_difference_constructed_reciprocal_endpoint_compression hσ hc hU
  let a := min a₀ (1/2:ℝ)
  refine ⟨η₀,a,C,hη₀,hηcap,lt_min ha₀ (by norm_num),min_le_right _ _,hC,?_⟩
  intro F η x₀ y₀ ya yb b l r δ xa xb hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests H G t z₀ hlr hroots hends hnear
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  let ρ := fun w : ℝ × ℝ =>
    Function.invFunOn (fun x => H (w.1,x)) (Ioo (3/4:ℝ) (9/4)) w.2
  let g := fun w => fderiv ℝ H (w.1,ρ w) (0,1)
  let k := fun w : ℝ × ℝ => w.2^3*g (w.1,w.2⁻¹)
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
  have hcanonical i : |k (yb,t i+b)-k (ya,t i)| ≤ δ := by
    have ha : ρ (ya,(t i)⁻¹)=xa i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).1) (hyext _ hya)
      hf hbound htests (hroots i).2.2.1
    have hb : ρ (yb,(t i+b)⁻¹)=xb i := positive_difference_curvature_inverse_eq F
      hσ hc hU hη hηmax (hxext _ (hroots i).2.1) (hyext _ hyb)
      hf hbound htests (hroots i).2.2.2
    dsimp only [k,g]
    rw [ha,hb,hGder _ _ (hroots i).1 hya,hGder _ _ (hroots i).2.1 hyb]
    have hh := hnear i
    rw [(hroots i).2.2.1,(hroots i).2.2.2,inv_inv,inv_inv] at hh
    simpa only [mul_comm] using hh
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
  exact hcompression F η x₀ y₀ ya yb b l r δ hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests hlr hlen hpts (hcanonical 0) (hcanonical 1)

private theorem reciprocal_endpoint_curvature_bound
    {a b T M R C D γ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hT : 0 < T) (hM : 0 < M)
    (horder : a⁻¹ ≤ b⁻¹)
    (hA : |a| ≤ T*R/(2*M^2)) (hB : |b| ≤ T*R/(2*M^2))
    (hraw : T^2*|γ| *(b⁻¹-a⁻¹) ≤ 4*C*D*M^4) :
    |γ| *|b-a| ≤ C*D*R^2 := by
  have hi : 0 ≤ b⁻¹-a⁻¹ := sub_nonneg.mpr horder
  have hbox : 0 ≤ T*R/(2*M^2) := (abs_nonneg a).trans hA
  have hab : |a| *|b| ≤ (T*R/(2*M^2))^2 := by
    simpa only [pow_two] using mul_le_mul hA hB (abs_nonneg b) hbox
  have hid : |b-a|=|a| *|b| *(b⁻¹-a⁻¹) := by
    have he : b-a=a*b*(a⁻¹-b⁻¹) := by field_simp
    rw [he,abs_mul,abs_mul,abs_sub_comm,abs_of_nonneg hi]
  have hmain : T^2*|γ| *(b⁻¹-a⁻¹)/(4*M^4) ≤ C*D :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hraw])
  calc
    |γ| *|b-a| = |γ| *(|a| *|b| *(b⁻¹-a⁻¹)) := by rw [hid]
    _ ≤ |γ| *((T*R/(2*M^2))^2*(b⁻¹-a⁻¹)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab hi) (abs_nonneg _)
    _ = (T^2*|γ| *(b⁻¹-a⁻¹)/(4*M^4))*R^2 := by field_simp; ring
    _ ≤ C*D*R^2 := mul_le_mul_of_nonneg_right hmain (sq_nonneg R)

/-- Lower-triangular physical endpoint compression uses the actual
reciprocal curvature profile and its rounded cubic weight. -/
private theorem positive_difference_physical_lower_endpoint_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ a ≤ 1/2 ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb γ Δ T M : ℝ) (xa xb : Fin 2 → ℝ),
    0 < η → η ≤ η₀ → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 ≤ Δ →
    (∀ i, xa i∈Icc M (2*M) ∧ xb i∈Icc M (2*M)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let u := fun i => (h ya (xa i))⁻¹
    let t := fun i => (T/(2*M^2))*u i
    let bnorm := T*γ/(2*M^2)
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,(H (y₀,x₀))⁻¹)
    u 0 < u 1 →
    (∀ i, h yb (xb i)=h ya (xa i)/(γ*h ya (xa i)+1)) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)*(γ*h ya (xa i)+1)^3-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    |γ| *|h ya (xa 1)-h ya (xa 0)| ≤ C*(Δ+1/M) := by
  obtain ⟨η₀,a,C,hη₀,hηcap,ha,hac,hC,hcompression⟩ :=
    positive_difference_actual_reciprocal_endpoint_compression hσ hc hU
  let R := max 1 (max (3*U/σ) (2*σ/c))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨η₀,a,C*R^12,hη₀,hηcap,ha,hac,by positivity,?_⟩
  intro F η x₀ y₀ ya yb γ Δ T M xa xb hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f h μ u t bnorm H z₀ hu hmap hthird hends
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  have hMpos : 0 < M := by linarith only [hM]
  let G := fun v : ℝ × ℝ =>
    (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
  let P := fun v => G v*((H v)⁻¹)^3
  let L := T/(2*M^2)
  have hL : L ≠ 0 := by dsimp only [L]; positivity
  have hnorm x (hx : x ∈ Icc M (2*M)) : x/M ∈ Icc (1:ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hMpos).mpr (by simpa using hx.1)
    · exact (div_le_iff₀ hMpos).mpr hx.2
  have hpos x (hx : x ∈ Icc M (2*M)) : 0 < x := hMpos.trans_le hx.1
  have hroundpos x (hx : x ∈ Icc M (2*M)) : (0:ℝ) < round x := by
    have hh := abs_le.mp (abs_sub_round x)
    linarith only [hh.2,hx.1,hM]
  have hd n x y (hx : 0 < x) (hy : y ∈ Icc (1:ℝ) 2) :
      iteratedDeriv n (f y) x=
        T/M^n*((iteratedDeriv n F (x/M)-iteratedDeriv n F (x/M+η*y))/(σ*η)) :=
    positive_difference_physical_iteratedDeriv F hMpos hx
      (mul_nonneg hη.le (by linarith only [hy.1])) hf n
  have hHne x y (hx : x ∈ Icc M (2*M)) (hy : y ∈ Icc (1:ℝ) 2) :
      H (y,x/M) ≠ 0 := by
    have hx' := hnorm x hx
    have hxwide : x/M ∈ Icc (3/4:ℝ) (9/4) :=
      ⟨by linarith only [hx'.1],by linarith only [hx'.2]⟩
    have hywide : y ∈ Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
    have he := (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hxwide hywide hf hbound htests 3 (by norm_num) (by norm_num)).1
    change iteratedDeriv 2 (fun u => (F u-F (u+η*y))/(σ*η)) (x/M)=H (y,x/M) at he
    have hlo := positive_jets_difference_spatial_lower F hσ hc hη hηmax
      hxwide hywide hf htests 2 (by norm_num) (by norm_num)
    rw [he] at hlo
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hlo)
  have hHbound x y (hx : x∈Icc M (2*M)) (hy : y∈Icc (1:ℝ) 2) :
      |H (y,x/M)| ≤ R := by
    have hx' := hnorm x hx
    have hxwide : x/M∈Icc (3/4:ℝ) (9/4) :=
      ⟨by linarith only [hx'.1],by linarith only [hx'.2]⟩
    have hywide : y∈Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩
    have he := (positive_jets_difference_curvature_entry F hσ hc hU hη hηmax
      hxwide hywide hf hbound htests 3 (by norm_num) (by norm_num)).1
    change iteratedDeriv 2 (fun u => (F u-F (u+η*y))/(σ*η)) (x/M)=H (y,x/M) at he
    have hup := positive_jets_difference_mixed_upper F hσ hU hη hηmax
      hxwide hywide hf hbound 2 0 (by norm_num) (by norm_num)
    simp only [iteratedDeriv_zero] at hup
    rw [he] at hup
    exact hup.trans ((le_max_left _ _).trans (le_max_right _ _))
  have hscale x y (hx : x ∈ Icc M (2*M)) (hy : y ∈ Icc (1:ℝ) 2) :
      h y x=L*H (y,x/M) := by
    dsimp only [h]
    rw [hd 2 x y (hpos x hx) hy]
    dsimp only [L,H]
    ring
  have hroots k :
      xa k/M ∈ Icc (1:ℝ) 2 ∧ xb k/M ∈ Icc (1:ℝ) 2 ∧
      (H (yb,xb k/M))⁻¹=(H (ya,xa k/M))⁻¹+T*γ/(2*M^2) := by
    refine ⟨hnorm _ (hpoints k).1,hnorm _ (hpoints k).2,?_⟩
    have hh := hmap k
    rw [hscale _ _ (hpoints k).2 hyb,hscale _ _ (hpoints k).1 hya] at hh
    have hHa := hHne _ _ (hpoints k).1 hya
    calc
      _ = L*(L*H (yb,xb k/M))⁻¹ := by simp [mul_inv_rev,hL,mul_comm]
      _ = L*((γ*(L*H (ya,xa k/M))+1)/(L*H (ya,xa k/M))) := by rw [hh,inv_div]
      _ = _ := by dsimp only [L]; field_simp; ring
  have hratio k :
      H (ya,xa k/M)/H (yb,xb k/M)=γ*h ya (xa k)+1 := by
    have hHa : h ya (xa k) ≠ 0 := by
      rw [hscale _ _ (hpoints k).1 hya]
      exact mul_ne_zero hL (hHne _ _ (hpoints k).1 hya)
    calc
      _ = h ya (xa k)/h yb (xb k) := by
        rw [hscale _ _ (hpoints k).1 hya,hscale _ _ (hpoints k).2 hyb,
          mul_div_mul_left _ _ hL]
      _ = h ya (xa k)/(h ya (xa k)/(γ*h ya (xa k)+1)) := by rw [hmap k]
      _ = _ := by field_simp
  have hrounded k :
      |G (yb,(round (M*(xb k/M)):ℝ)/M)/
        G (ya,(round (M*(xa k/M)):ℝ)/M)*(H (ya,xa k/M)/H (yb,xb k/M))^3-1| ≤ Δ := by
    have he x : M*(x/M)=x := mul_div_cancel₀ x hMpos.ne'
    rw [he,he]
    have ha : μ ya (xa k)=(T/(6*M^3))*G (ya,(round (xa k):ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos _ (hpoints k).1) hya]
      dsimp only [G]
      ring
    have hb : μ yb (xb k)=(T/(6*M^3))*G (yb,(round (xb k):ℝ)/M) := by
      dsimp only [μ]
      rw [hd 3 _ _ (hroundpos _ (hpoints k).2) hyb]
      dsimp only [G]
      ring
    have hh := hthird k
    rw [←hratio k] at hh
    rw [ha,hb,mul_div_mul_left _ _ (by positivity : T/(6*M^3) ≠ 0)] at hh
    exact hh
  have hnear k : |P (yb,xb k/M)-P (ya,xa k/M)| ≤ R^10*(Δ+1/M) :=
    positive_difference_rounded_reciprocal_profile_bound F hσ hc hU hη hηmax hM
      (hroots k).1 (hroots k).2.1 hya hyb hf hbound htests hΔ (hrounded k)
  have htA k : (H (ya,xa k/M))⁻¹=t k := by
    change _=(T/(2*M^2))*(h ya (xa k))⁻¹
    rw [hscale _ _ (hpoints k).1 hya]
    change _=L*(L*H (ya,xa k/M))⁻¹
    simp [mul_inv_rev,hL,mul_comm]
  have hrootA k : H (ya,xa k/M)=(t k)⁻¹ := by
    rw [←htA,inv_inv]
  have hrootB k : H (yb,xb k/M)=(t k+bnorm)⁻¹ := by
    have hh := (hroots k).2.2
    rw [htA] at hh
    change (H (yb,xb k/M))⁻¹=t k+bnorm at hh
    rw [←hh,inv_inv]
  have ht : t 0 < t 1 := mul_lt_mul_of_pos_left hu (by positivity)
  have htvec (i : Fin 2) : (![t 0,t 1] : Fin 2 → ℝ) i=t i := by fin_cases i <;> rfl
  have hh := hcompression F η x₀ y₀ ya yb bnorm (t 0) (t 1) (R^10*(Δ+1/M))
    (fun i => xa i/M) (fun i => xb i/M) hη hηsmall hx₀ hy₀ hya hyb hf hbound htests ht
    (by intro i; rw [htvec]; exact ⟨hnorm _ (hpoints i).1,hnorm _ (hpoints i).2,hrootA i,hrootB i⟩)
    (by intro i; rw [htvec]; exact hends i)
    hnear
  have hn : T*|γ|/(2*M^2) ≤ ‖((yb-ya,bnorm):ℝ × ℝ)‖ := by
    have he := norm_snd_le ((yb-ya,bnorm):ℝ × ℝ)
    simpa only [bnorm,Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos hT,
      abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (sq_nonneg M)] using he
  have hm := (mul_le_mul_of_nonneg_right hn (sub_nonneg.mpr ht.le)).trans hh
  have hm' := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 4*M^4)
  have he : (T*|γ|/(2*M^2)*(t 1-t 0))*(4*M^4)=T^2*|γ| *(u 1-u 0) := by
    dsimp only [t]
    field_simp
    ring
  rw [he] at hm'
  have hraw : T^2*|γ| *(u 1-u 0) ≤ 4*(C*R^10)*(Δ+1/M)*M^4 :=
    hm'.trans_eq (by ring)
  have hne i : h ya (xa i) ≠ 0 := by
    rw [hscale _ _ (hpoints i).1 hya]
    exact mul_ne_zero hL (hHne _ _ (hpoints i).1 hya)
  have hheight i : |h ya (xa i)| ≤ T*R/(2*M^2) := by
    rw [hscale _ _ (hpoints i).1 hya,abs_mul,abs_of_pos (by dsimp only [L]; positivity : 0 < L)]
    calc
      L*|H (ya,xa i/M)| ≤ L*R :=
        mul_le_mul_of_nonneg_left (hHbound _ _ (hpoints i).1 hya) (by dsimp only [L]; positivity)
      _ = _ := by dsimp only [L]; ring
  have hfinal := reciprocal_endpoint_curvature_bound (hne 0) (hne 1) hT hMpos
    hu.le (hheight 0) (hheight 1) hraw
  exact hfinal.trans_eq (by ring)

private theorem huxley_lower_endpoint_source_scale
    {κ γ L N R M C K Δg : ℝ}
    (hL : 0 < L) (hN : 0 < N) (hR : 1 ≤ R) (hM : 0 < M)
    (hC : 0 ≤ C) (hNL : (L*N)^2 ≤ M*R)
    (hlo : κ*L/(8*R^2) ≤ Δg)
    (hhi : |γ| *Δg ≤ C*(K*R^2/(L^2*N^2)+1/M)) :
    κ*|γ| *L^3*N^2 ≤ 8*C*(K+1)*R^4 := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hround : 1/M ≤ R^2/(L^2*N^2) := by
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    nlinarith only [hNL,mul_nonneg hM.le (show 0 ≤ R^2-R by nlinarith only [hR])]
  have hbound := (mul_le_mul_of_nonneg_left hlo (abs_nonneg γ)).trans hhi
  have hh := hbound.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hround) hC)
  have hm := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 8*R^2*L^2*N^2)
  have he : |γ| *(κ*L/(8*R^2))*(8*R^2*L^2*N^2)=κ*|γ| *L^3*N^2 := by
    field_simp
  have he' : C*(K*R^2/(L^2*N^2)+R^2/(L^2*N^2))*(8*R^2*L^2*N^2)=8*C*(K+1)*R^4 := by
    field_simp
  rwa [he,he'] at hm

private theorem reciprocal_fraction_strictMonoOn
    {e r v s l u : ℝ} (hdet : v*r-e*s=1)
    (hne : ∀ z∈Icc l u, e*z+v ≠ 0) :
    StrictMonoOn (fun z => (r*z+s)/(e*z+v)) (Icc l u) := by
  have hd z (hz : z∈Icc l u) :
      HasDerivAt (fun z => (r*z+s)/(e*z+v)) (1/(e*z+v)^2) z := by
    have hh := (((hasDerivAt_id z).const_mul r).add_const s).div
      (((hasDerivAt_id z).const_mul e).add_const v) (hne z hz)
    convert hh using 1
    have he : r*(e*z+v)-(r*z+s)*e=1 := by linear_combination hdet
    simp only [id_eq,mul_one,he]
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc l u)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (interior_subset hz)).hasDerivWithinAt)
  intro z hz
  exact div_pos zero_lt_one (sq_pos_of_ne_zero (hne z (interior_subset hz)))

/-- The two genuine quartic witnesses discharge the weighted improved Third
Condition for a source-linked lower-triangular difference family.
Only the original endpoint chart geometry and exact physical source identity remain explicit. -/
theorem positive_difference_quartic_lower_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
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
    (e 1=e 0 ∧ v 1=v 0 ∧ r 1=r 0+γ*e 0 ∧ s 1=s 0+γ*v 0) →
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
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
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ i, f i=fun z => Src (yp i) ((A i:ℝ)+z)) →
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    κ*|γ| *L^3*N^2 ≤ 8*Csrc*(C+1)*R^4 := by
  obtain ⟨η₀,a,Csrc,hη₀,hηcap,ha,_hac,hCsrc,hcompression⟩ :=
    positive_difference_physical_lower_endpoint_compression hσsrc hcsrc hUsrc
  refine ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb γ Tsrc σ δ T M N R L d K α β x F A W x₀ e r v s x₁
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Src Hsrc center hsource hlocalEnds
  have hxleft : x 0∈Icc (x 0) (x 7) := ⟨le_rfl,hmono.monotone (by decide)⟩
  have hxright : x 7∈Icc (x 0) (x 7) := ⟨hmono.monotone (by decide),le_rfl⟩
  have hηmax' : η ≤ 1/8 := hηmax.trans hηcap
  have hjet i k t : iteratedDeriv k (f i) t=
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hrounded i t :
      iteratedDeriv 3 (f i) (round t)=
        iteratedDeriv 3 (Src (yp i)) (round ((A i:ℝ)+t)) := by
    rw [hjet,round_intCast_add,Int.cast_add]
  have hyp i : yp i∈Icc (1:ℝ) 2 := by fin_cases i <;> assumption
  have hcurvNe t (ht : t∈Icc (x 0) (x 7)) i :
      iteratedDeriv 2 (f i) (x₁ t i)/2 ≠ 0 := by
    let q := (A i:ℝ)+x₁ t i
    have hq : q∈Icc M (2*M) :=
      ⟨by dsimp only [q]; linarith only [hA i,(hx₁ _ ht i).1],
       by dsimp only [q]; linarith only [hW i,(hx₁ _ ht i).2]⟩
    have hqnorm : q/M∈Icc (3/4:ℝ) (9/4) := by
      constructor
      · apply (le_div_iff₀ hM).mpr
        linarith only [hq.1,hM]
      · apply (div_le_iff₀ hM).mpr
        linarith only [hq.2,hM]
    have hywide : yp i∈Icc (1/2:ℝ) 3 :=
      ⟨by linarith only [(hyp i).1],by linarith only [(hyp i).2]⟩
    have he := (positive_jets_difference_curvature_entry Fsrc hσsrc hcsrc hUsrc hη hηmax'
      hqnorm hywide hreg hjets htests 3 (by norm_num) (by norm_num)).1
    change iteratedDeriv 2 (fun u => (Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)) (q/M)=
      Hsrc (yp i,q/M) at he
    have hloH := positive_jets_difference_spatial_lower Fsrc hσsrc hcsrc hη hηmax'
      hqnorm hywide hreg htests 2 (by norm_num) (by norm_num)
    rw [he] at hloH
    have hneH : Hsrc (yp i,q/M) ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le (by positivity) hloH)
    have hd : iteratedDeriv 2 (Src (yp i)) q=Tsrc/M^2*Hsrc (yp i,q/M) :=
      positive_difference_physical_iteratedDeriv Fsrc hM (hM.trans_le hq.1)
        (mul_nonneg hη.le (by linarith only [(hyp i).1])) hreg 2
    rw [hjet]
    change iteratedDeriv 2 (Src (yp i)) q/2 ≠ 0
    rw [hd]
    exact div_ne_zero (mul_ne_zero (div_ne_zero hTsrc.ne' (pow_ne_zero 2 hM.ne')) hneH)
      (by norm_num)
  have hnumNe t (ht : t∈Icc (x 0) (x 7)) i : e i*t+v i ≠ 0 := by
    intro he
    have hh := hcurvNe t ht i
    rw [hpoint t ht i,he,zero_div] at hh
    exact hh rfl
  have hinvEq t (ht : t∈Icc (x 0) (x 7)) i :
      (iteratedDeriv 2 (f i) (x₁ t i)/2)⁻¹=(r i*t+s i)/(e i*t+v i) := by
    rw [hpoint t ht i,inv_div]
  have hinvMono i : StrictMonoOn
      (fun t => (iteratedDeriv 2 (f i) (x₁ t i)/2)⁻¹) (Icc (x 0) (x 7)) := by
    intro u hu w hw huw
    change (iteratedDeriv 2 (f i) (x₁ u i)/2)⁻¹ < (iteratedDeriv 2 (f i) (x₁ w i)/2)⁻¹
    rw [hinvEq u hu i,hinvEq w hw i]
    exact reciprocal_fraction_strictMonoOn (hdet i) (fun t ht => hnumNe t ht i) hu hw huw
  have hlocal z (hz : z∈Icc (x 0) (x 7)) i :
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a := by
    have hl := hlocalEnds (x 0) (by simp) i
    have hu := hlocalEnds (x 7) (by simp) i
    have hlo := mul_le_mul_of_nonneg_left ((hinvMono i).monotoneOn hxleft hz hz.1)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    have hhi := mul_le_mul_of_nonneg_left ((hinvMono i).monotoneOn hz hxright hz.2)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ (x 0) i)/2)⁻¹-center.2| < a at hl
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ (x 7) i)/2)⁻¹-center.2| < a at hu
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹-center.2| < a
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
  let z : Fin 2 → ℝ := ![z₀,z₁]
  let profile : ℝ → ℝ := fun t => iteratedDeriv 2 (f 0) (x₁ t 0)/2
  have hz p : z p∈Icc (x 0) (x 7) := by
    fin_cases p
    · exact hz₀'
    · exact hz₁'
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
  have hDmap t : D t 1=D t 0+γ*(e 0*t+v 0) := by
    dsimp only [D]
    rw [htransport.2.2.1,htransport.2.2.2]
    ring_nf
  have hratio t (ht : t∈Icc (x 0) (x 7)) : γ*profile t+1=D t 1/D t 0 := by
    change γ*(iteratedDeriv 2 (f 0) (x₁ t 0)/2)+1=_
    rw [hpoint t ht 0,hDmap]
    field_simp [(hdpos t ht 0).ne']
    ring_nf
  have hmap t (ht : t∈Icc (x 0) (x 7)) :
      iteratedDeriv 2 (f 1) (x₁ t 1)/2=profile t/(γ*profile t+1) := by
    rw [hratio t ht]
    change _=(iteratedDeriv 2 (f 0) (x₁ t 0)/2)/(D t 1/D t 0)
    rw [hpoint t ht 1,hpoint t ht 0,htransport.1,htransport.2.1]
    field_simp [(hdpos t ht 0).ne',(hdpos t ht 1).ne']
  have hinvMap t (ht : t∈Icc (x 0) (x 7)) :
      (iteratedDeriv 2 (f 1) (x₁ t 1)/2)⁻¹=(profile t)⁻¹+γ := by
    rw [hmap t ht,inv_div]
    have hp : profile t ≠ 0 := hcurvNe t ht 0
    rw [add_div,mul_div_cancel_right₀ γ hp,one_div,add_comm]
  have hthird' p :
      |μnew (z p) 1/μnew (z p) 0*(γ*profile (z p)+1)^3-1| ≤ Δ := by
    have hh := hthird (z p) (by fin_cases p <;> simp [z])
    change |μnew (z p) 1*(D (z p) 1)^3/(μnew (z p) 0*(D (z p) 0)^3)-1| ≤ Δ at hh
    have he : μnew (z p) 1/μnew (z p) 0*(D (z p) 1/D (z p) 0)^3=
        μnew (z p) 1*(D (z p) 1)^3/(μnew (z p) 0*(D (z p) 0)^3) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring_nf
    rw [hratio _ (hz p),he]
    exact hh
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
  have hub p : iteratedDeriv 2 (Src yb) (xb p)/2=profile (z p)/(γ*profile (z p)+1) := by
    exact (congrArg (fun u : ℝ => u/2) (hjet 1 2 (x₁ (z p) 1))).symm.trans (hmap _ (hz p))
  have hzstrict : z₀ < z₁ := hz₀.2.trans_le
    ((hmono.monotone (by decide : (3:Fin 8) ≤ 4)).trans hz₁.1.le)
  have hh := hcompression Fsrc η xcenter ycenter ya yb γ Δ Tsrc M xa xb
    hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hΔ hphysical
    (by
      change (iteratedDeriv 2 (Src ya) (xa 0)/2)⁻¹ <
        (iteratedDeriv 2 (Src ya) (xa 1)/2)⁻¹
      rw [hua,hua]
      exact hinvMono 0 hz₀' hz₁' hzstrict)
    (by
      intro p
      change iteratedDeriv 2 (Src yb) (xb p)/2=
        (iteratedDeriv 2 (Src ya) (xa p)/2)/(γ*(iteratedDeriv 2 (Src ya) (xa p)/2)+1)
      rw [hua,hub])
    (by
      intro p
      have hh := hthird' p
      change |(iteratedDeriv 3 (f 1) (round (x₁ (z p) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (x₁ (z p) 0))/6)*(γ*profile (z p)+1)^3-1| ≤ Δ at hh
      rw [hrounded,hrounded] at hh
      change |(iteratedDeriv 3 (Src yb) (round (xb p))/6)/
        (iteratedDeriv 3 (Src ya) (round (xa p))/6)*
        (γ*(iteratedDeriv 2 (Src ya) (xa p)/2)+1)^3-1| ≤ Δ
      rw [hua]
      exact hh)
    (by
      intro p
      change ‖((ya,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa p)/2)⁻¹):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa p)/2)⁻¹+Tsrc*γ/(2*M^2)):ℝ × ℝ)-center‖ < a
      constructor
      · rw [hua]
        exact hlocal _ (hz p) 0
      · have he : (Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa p)/2)⁻¹+
            Tsrc*γ/(2*M^2)=(Tsrc/(2*M^2))*(iteratedDeriv 2 (f 1) (x₁ (z p) 1)/2)⁻¹ := by
          rw [hua,hinvMap _ (hz p)]
          ring_nf
        rw [he]
        exact hlocal _ (hz p) 1)
  change |γ| *|iteratedDeriv 2 (Src ya) (xa 1)/2-iteratedDeriv 2 (Src ya) (xa 0)/2| ≤
    Csrc*(Δ+1/M) at hh
  rw [hua,hua] at hh
  change |γ| *|profile z₁-profile z₀| ≤ Csrc*(Δ+1/M) at hh
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr horder)] at hh
  exact huxley_lower_endpoint_source_scale hL hN hR hM hCsrc.le hNL hlo hh

/-- Source-defined normalized difference phases consume the actual
quartic witnesses and the original endpoint chart geometry. The physical
phase identities and integer-rounded jet correspondence are derived. -/
theorem positive_difference_normalized_quartic_lower_long_block_constraint
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
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
    (e 1=e 0 ∧ v 1=v 0 ∧ r 1=r 0+γ*e 0 ∧ s 1=s 0+γ*v 0) →
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
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
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    κ*|γ| *L^3*N^2 ≤ 8*Csrc*(C+1)*R^4 := by
  obtain ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,hcore⟩ :=
    positive_difference_quartic_lower_long_block_constraint hσsrc hcsrc hUsrc
  refine ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb γ Tsrc σ δ T M N R L d K α β x A W x₀ e r v s x₁
    F hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
    f n μ ν D g H G hbase hpoint hsquare hgap hres κ Γ C yp Hsrc center hlocalEnds
  let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
  have hsource i : f i=fun z => Src (yp i) ((A i:ℝ)+z) := by
    funext z
    dsimp only [f,heathBrownPhysicalPhase,F,Src,yp]
    field_simp
  exact hcore Fsrc η xcenter ycenter ya yb γ Tsrc x (F:=F) A
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hscale
    htransport hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
    hbase hpoint hsquare hgap hres hsource hlocalEnds


example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
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
    (e 1=e 0 ∧ v 1=v 0 ∧ r 1=r 0+γ*e 0 ∧ s 1=s 0+γ*v 0) →
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
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
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ i, f i=fun z => Src (yp i) ((A i:ℝ)+z)) →
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    κ*|γ| *L^3*N^2 ≤ 8*Csrc*(C+1)*R^4 :=
  HuxleyLowerQuarticScratch.positive_difference_quartic_lower_long_block_constraint (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
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
    (e 1=e 0 ∧ v 1=v 0 ∧ r 1=r 0+γ*e 0 ∧ s 1=s 0+γ*v 0) →
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
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
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ z∈({x 0,x 7} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (x₁ z i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    κ*|γ| *L^3*N^2 ≤ 8*Csrc*(C+1)*R^4 :=
  HuxleyLowerQuarticScratch.positive_difference_normalized_quartic_lower_long_block_constraint (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


end HuxleyLowerQuarticScratch
#print axioms HuxleyLowerQuarticScratch.positive_difference_normalized_quartic_lower_long_block_constraint
#print axioms HuxleyLowerQuarticScratch.positive_difference_quartic_lower_long_block_constraint
#print axioms HuxleyLowerQuarticScratch.huxley_lower_endpoint_source_scale
#print axioms HuxleyLowerQuarticScratch.reciprocal_fraction_strictMonoOn
#print axioms HuxleyLowerQuarticScratch.positive_difference_actual_reciprocal_endpoint_compression

#print axioms HuxleyLowerQuarticScratch.positive_difference_physical_lower_endpoint_compression

#print axioms HuxleyLowerQuarticScratch.reciprocal_endpoint_curvature_bound

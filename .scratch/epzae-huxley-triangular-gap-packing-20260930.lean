import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyTriangularGapScratch

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



/-- Lower-triangular physical endpoint compression uses the actual
reciprocal curvature profile and its rounded cubic weight. -/
private theorem positive_difference_physical_lower_pair_compression
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
    (∀ i, h yb (xb i)=h ya (xa i)/(γ*h ya (xa i)+1)) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)*(γ*h ya (xa i)+1)^3-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    |γ| *|h ya (xa 1)-h ya (xa 0)| ≤ C*(Δ+1/M) := by
  obtain ⟨η₀,a,C,hη₀,hηcap,ha,hac,hC,hcompression⟩ :=
    positive_difference_physical_lower_endpoint_compression hσ hc hU
  refine ⟨η₀,a,C,hη₀,hηcap,ha,hac,hC,?_⟩
  intro F η x₀ y₀ ya yb γ Δ T M xa xb hη hηsmall hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f h μ u t bnorm H z₀ hmap hthird hends
  have hpair (i j : Fin 2) (hij : u i < u j) :
      |γ| *|h ya (xa j)-h ya (xa i)| ≤ C*(Δ+1/M) := by
    exact hcompression F η x₀ y₀ ya yb γ Δ T M ![xa i,xa j] ![xb i,xb j]
      hη hηsmall hx₀ hy₀ hya hyb hf hbound htests hT hM hΔ
      (by
        intro k
        fin_cases k
        · exact hpoints i
        · exact hpoints j)
      hij
      (by
        intro k
        fin_cases k
        · exact hmap i
        · exact hmap j)
      (by
        intro k
        fin_cases k
        · exact hthird i
        · exact hthird j)
      (by
        intro k
        fin_cases k
        · exact hends i
        · exact hends j)
  rcases lt_trichotomy (u 0) (u 1) with hlt | heq | hgt
  · exact hpair 0 1 hlt
  · have he : h ya (xa 0)=h ya (xa 1) := inv_injective heq
    rw [he,sub_self,abs_zero,mul_zero]
    have hMpos : 0 < M := by linarith only [hM]
    positivity
  · have hh := hpair 1 0 hgt
    rwa [abs_sub_comm] at hh


private theorem adjacent_reference_gap_card_closed
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) {lo hi d : ℝ}
    (hd : 0 < d) (hlohi : lo ≤ hi)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1<ab.2 ∧
      ∀ t∈S, ¬(ab.1<t ∧ t<ab.2))
    (hmeet : ∀ ab∈G, ab.1 ≤ hi ∧ lo ≤ ab.2) :
    (G.card:ℝ) ≤ (hi-lo)/d+2 := by
  classical
  have hinj : Set.InjOn Prod.fst (G : Set (ℝ × ℝ)) := by
    intro ab hab cd hcd he
    apply Prod.ext he
    rcases lt_trichotomy ab.2 cd.2 with hlt | heq | hgt
    · exact False.elim ((hgap cd hcd).2.2.2 _ (hgap ab hab).2.1
        ⟨by rw [←he]; exact (hgap ab hab).2.2.1,hlt⟩)
    · exact heq
    · exact False.elim ((hgap ab hab).2.2.2 _ (hgap cd hcd).2.1
        ⟨by rw [he]; exact (hgap cd hcd).2.2.1,hgt⟩)
  let G₀ := G.filter (fun ab => ab.1<lo)
  let G₁ := G.filter (fun ab => ¬ab.1<lo)
  have hsmall : G₀.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro ab hab cd hcd
    have ha := Finset.mem_filter.mp hab
    have hc := Finset.mem_filter.mp hcd
    apply hinj ha.1 hc.1
    rcases lt_trichotomy ab.1 cd.1 with hlt | heq | hgt
    · exact False.elim ((hgap ab ha.1).2.2.2 _ (hgap cd hc.1).1
        ⟨hlt,hc.2.trans_le (hmeet ab ha.1).2⟩)
    · exact heq
    · exact False.elim ((hgap cd hc.1).2.2.2 _ (hgap ab ha.1).1
        ⟨hgt,ha.2.trans_le (hmeet cd hc.1).2⟩)
  have hlarge := separated_reference_interval_card (G₁.image Prod.fst) hd hlohi
    (by
      intro x hx y hy hne
      obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hy
      exact hsep _ (hgap ab (Finset.mem_filter.mp hab).1).1
        _ (hgap cd (Finset.mem_filter.mp hcd).1).1 hne)
    (by
      intro x hx
      obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hx
      have ha := Finset.mem_filter.mp hab
      exact ⟨le_of_not_gt ha.2,(hmeet ab ha.1).1⟩)
  have he : (G₁.image Prod.fst).card=G₁.card :=
    Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))
  rw [he] at hlarge
  have hcard : G.card=G₀.card+G₁.card :=
    (Finset.card_filter_add_card_filter_not (s:=G) (fun ab => ab.1<lo)).symm
  have hcardR : (G.card:ℝ)=(G₀.card:ℝ)+(G₁.card:ℝ) := by exact_mod_cast hcard
  have hsmallR : (G₀.card:ℝ) ≤ 1 := by exact_mod_cast hsmall
  linarith only [hcardR,hsmallR,hlarge]


private theorem reference_gap_count_of_closed_profile_width
    (S : Finset ℝ) (G : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ)
    {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → d ≤ |x-y|)
    (hgap : ∀ ab∈G, ab.1∈S ∧ ab.2∈S ∧ ab.1 < ab.2 ∧
      ∀ t∈S, ¬(ab.1 < t ∧ t < ab.2))
    (hpoint : ∀ ab∈G, p ab∈Icc ab.1 ab.2)
    (hwidth : ∀ ab∈G, ∀ cd∈G, |p cd-p ab| ≤ D) :
    (G.card:ℝ) ≤ D/d+2 := by
  classical
  by_cases hG : G.Nonempty
  · let Values := G.image p
    have hv : Values.Nonempty := Finset.Nonempty.image hG p
    let lo := Values.min' hv
    let hi := Values.max' hv
    obtain ⟨ab,hab,hablo⟩ := Finset.mem_image.mp (Finset.min'_mem Values hv)
    obtain ⟨cd,hcd,hcdhi⟩ := Finset.mem_image.mp (Finset.max'_mem Values hv)
    have hbounds g (hg : g∈G) : lo ≤ p g ∧ p g ≤ hi :=
      ⟨Finset.min'_le Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩),
        Finset.le_max' Values _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)⟩
    have hlohi : lo ≤ hi := (hbounds ab hab).1.trans (hbounds ab hab).2
    have hspan : hi-lo ≤ D := by
      change Values.max' hv-Values.min' hv ≤ D
      rw [←hablo,←hcdhi]
      exact (abs_le.mp (hwidth ab hab cd hcd)).2
    have hc := adjacent_reference_gap_card_closed S G hd hlohi hsep hgap (by
      intro g hg
      exact ⟨(hpoint g hg).1.trans (hbounds g hg).2,
        (hbounds g hg).1.trans (hpoint g hg).2⟩)
    exact hc.trans (add_le_add (div_le_div_of_nonneg_right hspan hd.le) le_rfl)
  · have he : G=∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

private theorem adjacent_reference_gap_card_of_diameter
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ)
    {d width : ℝ} (hd : 0 < d) (hwidth : 0 ≤ width)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a≠b → d ≤ |a-b|)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1<ab.2 ∧
      ∀ t∈Refs, ¬(ab.1<t ∧ t<ab.2))
    (hinside : ∀ ab∈Gaps, p ab∈Ioo ab.1 ab.2)
    (hdiam : ∀ ab∈Gaps, ∀ cd∈Gaps, |p ab-p cd| ≤ width) :
    (Gaps.card:ℝ) ≤ width/d+2 := by
  classical
  rcases Gaps.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  obtain ⟨a,ha,hmin⟩ := Gaps.exists_min_image p hne
  obtain ⟨b,hb,hmax⟩ := Gaps.exists_max_image p hne
  have horder : p a ≤ p b := hmin b hb
  have hlength : p b-p a ≤ width := by
    have hh := hdiam b hb a ha
    rwa [abs_of_nonneg (sub_nonneg.mpr horder)] at hh
  have hh := adjacent_reference_gap_card Refs Gaps hd horder hsep hgap (by
    intro ab hab
    exact ⟨(hinside ab hab).1.trans_le (hmax ab hab),
      (hmin ab hab).trans_lt (hinside ab hab).2⟩)
  exact hh.trans (add_le_add (div_le_div_of_nonneg_right hlength hd.le) le_rfl)

private theorem positive_difference_physical_lower_reference_gap_packing
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ η₀ a C : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb γ Δ T M R Uref : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (xa xb : ℝ × ℝ → ℝ),
    0 < η → η ≤ η₀ → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 < R → 0 < Uref → γ ≠ 0 → 0 ≤ Δ →
    (∀ ab∈Gaps, xa ab∈Icc M (2*M) ∧ xb ab∈Icc M (2*M)) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1<ab.2 ∧
      ∀ t∈Refs, ¬(ab.1<t ∧ t<ab.2)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let t := fun ab => (T/(2*M^2))*(h ya (xa ab))⁻¹
    let bnorm := T*γ/(2*M^2)
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,(H (y₀,x₀))⁻¹)
    (∀ ab∈Gaps, h ya (xa ab)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, h yb (xb ab)=h ya (xa ab)/(γ*h ya (xa ab)+1)) →
    (∀ ab∈Gaps, |μ yb (xb ab)/μ ya (xa ab)*(γ*h ya (xa ab)+1)^3-1| ≤ Δ) →
    (∀ ab∈Gaps, ‖((ya,t ab):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t ab+bnorm):ℝ × ℝ)-z₀‖ < a) →
    (Gaps.card:ℝ) ≤ 4*C*(Δ+1/M)*R^2/(|γ| *Uref)+2 := by
  obtain ⟨η₀,a,C,hη₀,hηcap,ha,_hac,hC,hcompression⟩ :=
    positive_difference_physical_lower_pair_compression hσ hc hU
  refine ⟨η₀,a,C,hη₀,hηcap,ha,hC,?_⟩
  intro F η x₀ y₀ ya yb γ Δ T M R Uref Refs Gaps xa xb
    hη hηsmall hx₀ hy₀ hya hyb hf hbound htests hT hM hR hUref hγ hΔ
    hpoints hsep hgap f h μ t bnorm H z₀ hinside hmap hthird hends
  have hMpos : 0 < M := by linarith only [hM]
  have hγpos : 0 < |γ| := abs_pos.mpr hγ
  have hdiam ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) :
      |h ya (xa ab)-h ya (xa cd)| ≤ C*(Δ+1/M)/|γ| := by
    have hh := hcompression F η x₀ y₀ ya yb γ Δ T M ![xa ab,xa cd] ![xb ab,xb cd]
      hη hηsmall hx₀ hy₀ hya hyb hf hbound htests hT hM hΔ
      (by
        intro i
        fin_cases i
        · exact hpoints ab hab
        · exact hpoints cd hcd)
      (by
        intro i
        fin_cases i
        · exact hmap ab hab
        · exact hmap cd hcd)
      (by
        intro i
        fin_cases i
        · exact hthird ab hab
        · exact hthird cd hcd)
      (by
        intro i
        fin_cases i
        · exact hends ab hab
        · exact hends cd hcd)
    change |γ| *|h ya (xa cd)-h ya (xa ab)| ≤ C*(Δ+1/M) at hh
    apply (le_div_iff₀ hγpos).mpr
    rw [mul_comm,abs_sub_comm]
    exact hh
  have hh := reference_gap_count_of_closed_profile_width Refs Gaps (fun ab => h ya (xa ab))
    (by positivity : 0 < Uref/(4*R^2))
    (by positivity : 0 ≤ C*(Δ+1/M)/|γ|) hsep hgap hinside (fun ab hab cd hcd => hdiam cd hcd ab hab)
  convert hh using 1
  ring_nf
  simp only [inv_inv]
  ring

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


private theorem reference_chart_fraction_antitone {e v r s a b : ℝ}
    (hdet : v*r-e*s=1) (ha : 0 < r*a+s) (hb : 0 < r*b+s) (hab : a ≤ b) :
    (e*b+v)/(r*b+s) ≤ (e*a+v)/(r*a+s) := by
  apply (div_le_div_iff₀ hb ha).mpr
  have he : (e*a+v)*(r*b+s)-(e*b+v)*(r*a+s)=b-a := by
    linear_combination (b-a)*hdet
  have hh := sub_nonneg.mpr hab
  rw [←he] at hh
  exact sub_nonneg.mp hh

/-- Actual quartic residuals yield the lower-triangular long-gap
packing bound; the improved Third witnesses are constructed internally. -/
theorem positive_difference_normalized_quartic_lower_reference_gap_packing
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R Uref L K : ℝ} (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → γ ≠ 0 →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < Uref) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (∀ ab∈Gaps, 0 < d ab) →
    (∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ i, r ab i≠0) →
    (∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab) →
    (∀ ab∈Gaps, StrictMono (x ab)) →
    (∀ ab∈Gaps,
      e ab 1=e ab 0 ∧ v ab 1=v ab 0 ∧
      r ab 1=r ab 0+γ*e ab 0 ∧ s ab 1=s ab 0+γ*v ab 0) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    (∀ ab∈Gaps, ∀ t∈({x ab 0,x ab 3} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab t i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    (Gaps.card:ℝ) ≤ 4*Csrc*(Cthird+1)*R^4/(L^2*N^2*|γ| *Uref)+2 := by
  classical
  obtain ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,hcompression⟩ :=
    positive_difference_physical_lower_reference_gap_packing hσsrc hcsrc hUsrc
  refine ⟨η₀,a,Csrc,hη₀,hηcap,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb γ Tsrc Refs Gaps x xref e r v s curve d alpha beta
    σ δ T M N R Uref L K A W
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hγ
    yp F Hsrc center hσ hδ hF hT hM hN hR hU hL hNL hK hA hW hsep hgap hd href hcurve hr hdet hden hmono htransport
    f n mu nu Den g H Gcoord profile hbase hpoint hends hsquare hspacing hres hlocalEnds
    κ Cphys Gamma Cthird
  let munew := fun ab t i => iteratedDeriv 3 (f i) (round (curve ab t i))/6
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCt : 0 ≤ Cthird := by dsimp only [Cthird,Gamma]; positivity
  have hdenpos ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      0 < Den ab t i := (hd ab hab).trans_le (hden ab hab t ht i).1
  have hex : ∀ ab∈Gaps, ∃ z∈Ioo (x ab 0) (x ab 3),
      |munew ab z 1*(Den ab z 1)^3/(munew ab z 0*(Den ab z 0)^3)-1| ≤ Cthird*R^2/(L^2*N^2) := by
    intro ab hab
    exact physicalModelPhase_quartic_long_block_third_condition (x ab)
      hσ hδ hF hT hM hN hR hL hNL (hd ab hab) hK hA hW
      (href ab hab) (hcurve ab hab) (hr ab hab) (hdet ab hab)
      (fun t ht i => (hden ab hab t ht i).1)
      (fun t ht i => (hden ab hab t ht i).2) (hmono ab hab)
      (hbase ab hab) (hpoint ab hab) (hsquare ab hab) (hspacing ab hab) (hres ab hab)
  choose! z hz hthird using hex
  have hzcc ab (hab : ab∈Gaps) : z ab∈Icc (x ab 0) (x ab 3) := ⟨(hz ab hab).1.le,(hz ab hab).2.le⟩
  have hinside ab (hab : ab∈Gaps) : profile ab (z ab)∈Ioo ab.1 ab.2 := by
    have hx03 : x ab 0 ≤ x ab 3 := (hmono ab hab).monotone (by decide)
    have hx0 : x ab 0∈Icc (x ab 0) (x ab 3) := ⟨le_rfl,hx03⟩
    have hx3 : x ab 3∈Icc (x ab 0) (x ab 3) := ⟨hx03,le_rfl⟩
    have hlow : profile ab (x ab 3) ≤ profile ab (z ab) := by
      dsimp only [profile]
      rw [hpoint ab hab _ hx3 0,hpoint ab hab _ (hzcc ab hab) 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ (hzcc ab hab) 0) (hdenpos ab hab _ hx3 0) (hzcc ab hab).2
    have hhigh : profile ab (z ab) ≤ profile ab (x ab 0) := by
      dsimp only [profile]
      rw [hpoint ab hab _ (hzcc ab hab) 0,hpoint ab hab _ hx0 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ hx0 0) (hdenpos ab hab _ (hzcc ab hab) 0) (hzcc ab hab).1
    exact ⟨(hends ab hab).2.1.trans_le hlow,hhigh.trans_lt (hends ab hab).1.2⟩
  let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
  have hsource i : f i=fun z => Src (yp i) ((A i:ℝ)+z) := by
    funext z
    dsimp only [f,heathBrownPhysicalPhase,F,Src]
    field_simp
  have hjet i k t : iteratedDeriv k (f i) t=
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hrounded i t : iteratedDeriv 3 (f i) (round t)=
      iteratedDeriv 3 (Src (yp i)) (round ((A i:ℝ)+t)) := by
    rw [hjet,round_intCast_add,Int.cast_add]
  have hyp i : yp i∈Icc (1:ℝ) 2 := by fin_cases i <;> assumption
  have hphysical ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      (A i:ℝ)+curve ab t i∈Icc M (2*M) :=
    ⟨by linarith only [hA i,(hcurve ab hab t ht i).1],
     by linarith only [hW i,(hcurve ab hab t ht i).2]⟩
  have hcurvNe ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      iteratedDeriv 2 (f i) (curve ab t i)/2 ≠ 0 := by
    rw [hjet]
    have hh := (positive_difference_half_curvature_source_bounds Fsrc
      hσsrc hcsrc hUsrc hη hηmax hTsrc hM (hyp i)
      (hphysical ab hab t ht i) hreg hjets htests).1
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hh)
  have hinvMono ab (hab : ab∈Gaps) i : StrictMonoOn
      (fun t => (iteratedDeriv 2 (f i) (curve ab t i)/2)⁻¹) (Icc (x ab 0) (x ab 3)) := by
    have hnum t (ht : t∈Icc (x ab 0) (x ab 3)) : e ab i*t+v ab i ≠ 0 := by
      intro he
      have hh := hcurvNe ab hab t ht i
      rw [hpoint ab hab t ht i,he,zero_div] at hh
      exact hh rfl
    intro u hu w hw huw
    change (iteratedDeriv 2 (f i) (curve ab u i)/2)⁻¹ <
      (iteratedDeriv 2 (f i) (curve ab w i)/2)⁻¹
    rw [hpoint ab hab u hu i,hpoint ab hab w hw i,inv_div,inv_div]
    exact reciprocal_fraction_strictMonoOn (hdet ab hab i) hnum hu hw huw
  have hlocal ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab t i)/2)⁻¹):ℝ × ℝ)-center‖ < a := by
    have hxorder := (hmono ab hab).monotone (by decide : (0:Fin 4) ≤ 3)
    have hl := hlocalEnds ab hab (x ab 0) (by simp) i
    have hu := hlocalEnds ab hab (x ab 3) (by simp) i
    have hlo := mul_le_mul_of_nonneg_left
      ((hinvMono ab hab i).monotoneOn ⟨le_rfl,hxorder⟩ ht ht.1)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    have hhi := mul_le_mul_of_nonneg_left
      ((hinvMono ab hab i).monotoneOn ht ⟨hxorder,le_rfl⟩ ht.2)
      (by positivity : 0 ≤ Tsrc/(2*M^2))
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab (x ab 0) i)/2)⁻¹-center.2| < a at hl
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab (x ab 3) i)/2)⁻¹-center.2| < a at hu
    change max |yp i-center.1|
      |(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab t i)/2)⁻¹-center.2| < a
    refine max_lt_iff.mpr ⟨(max_lt_iff.mp hl).1,abs_lt.mpr ⟨?_,?_⟩⟩
    · linarith only [(abs_lt.mp (max_lt_iff.mp hl).2).1,hlo]
    · linarith only [(abs_lt.mp (max_lt_iff.mp hu).2).2,hhi]
  have hDmap ab (hab : ab∈Gaps) t :
      Den ab t 1=Den ab t 0+γ*(e ab 0*t+v ab 0) := by
    dsimp only [Den]
    rw [(htransport ab hab).2.2.1,(htransport ab hab).2.2.2]
    ring
  have hratio ab (hab : ab∈Gaps) :
      γ*profile ab (z ab)+1=Den ab (z ab) 1/Den ab (z ab) 0 := by
    change γ*(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)+1=_
    rw [hpoint ab hab _ (hzcc ab hab) 0,hDmap ab hab]
    field_simp [(hdenpos ab hab _ (hzcc ab hab) 0).ne']
    ring_nf
  have hmap ab (hab : ab∈Gaps) :
      iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2=
        profile ab (z ab)/(γ*profile ab (z ab)+1) := by
    rw [hratio ab hab]
    change _=(iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2)/
      (Den ab (z ab) 1/Den ab (z ab) 0)
    rw [hpoint ab hab _ (hzcc ab hab) 1,hpoint ab hab _ (hzcc ab hab) 0,
      (htransport ab hab).1,(htransport ab hab).2.1]
    field_simp [(hdenpos ab hab _ (hzcc ab hab) 0).ne',
      (hdenpos ab hab _ (hzcc ab hab) 1).ne']
  have hinvMap ab (hab : ab∈Gaps) :
      (iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2)⁻¹=(profile ab (z ab))⁻¹+γ := by
    rw [hmap ab hab,inv_div]
    have hp : profile ab (z ab) ≠ 0 := hcurvNe ab hab _ (hzcc ab hab) 0
    rw [add_div,mul_div_cancel_right₀ γ hp,one_div,add_comm]
  have hweighted ab (hab : ab∈Gaps) :
      |munew ab (z ab) 1/munew ab (z ab) 0*(γ*profile ab (z ab)+1)^3-1| ≤
        Cthird*R^2/(L^2*N^2) := by
    have he : munew ab (z ab) 1/munew ab (z ab) 0*
        (Den ab (z ab) 1/Den ab (z ab) 0)^3=
        munew ab (z ab) 1*(Den ab (z ab) 1)^3/
          (munew ab (z ab) 0*(Den ab (z ab) 0)^3) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring_nf
    rw [hratio ab hab,he]
    exact hthird ab hab
  let xa := fun ab => (A 0:ℝ)+curve ab (z ab) 0
  let xb := fun ab => (A 1:ℝ)+curve ab (z ab) 1
  have hua ab : iteratedDeriv 2 (Src ya) (xa ab)/2=profile ab (z ab) :=
    (congrArg (fun u : ℝ => u/2) (hjet 0 2 (curve ab (z ab) 0))).symm
  have hub ab : iteratedDeriv 2 (Src yb) (xb ab)/2=
      iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2 :=
    (congrArg (fun u : ℝ => u/2) (hjet 1 2 (curve ab (z ab) 1))).symm
  have hcount := hcompression Fsrc η xcenter ycenter ya yb γ
    (Cthird*R^2/(L^2*N^2)) Tsrc M R Uref Refs Gaps xa xb
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hRpos hU hγ
    (by positivity) (fun ab hab => ⟨hphysical ab hab _ (hzcc ab hab) 0,
      hphysical ab hab _ (hzcc ab hab) 1⟩) hsep hgap
    (by intro ab hab; change iteratedDeriv 2 (Src ya) (xa ab)/2∈Icc ab.1 ab.2
        rw [hua]; exact ⟨(hinside ab hab).1.le,(hinside ab hab).2.le⟩)
    (by
      intro ab hab
      change iteratedDeriv 2 (Src yb) (xb ab)/2=
        (iteratedDeriv 2 (Src ya) (xa ab)/2)/(γ*(iteratedDeriv 2 (Src ya) (xa ab)/2)+1)
      rw [hua,hub]
      exact hmap ab hab)
    (by
      intro ab hab
      have hh := hweighted ab hab
      change |(iteratedDeriv 3 (f 1) (round (curve ab (z ab) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (curve ab (z ab) 0))/6)*
        (γ*profile ab (z ab)+1)^3-1| ≤ _ at hh
      rw [hrounded,hrounded] at hh
      change |(iteratedDeriv 3 (Src yb) (round (xb ab))/6)/
        (iteratedDeriv 3 (Src ya) (round (xa ab))/6)*
        (γ*(iteratedDeriv 2 (Src ya) (xa ab)/2)+1)^3-1| ≤ _
      rw [hua]
      exact hh)
    (by
      intro ab hab
      change ‖((ya,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹+
          Tsrc*γ/(2*M^2)):ℝ × ℝ)-center‖ < a
      rw [hua]
      constructor
      · exact hlocal ab hab _ (hzcc ab hab) 0
      · have he : (Tsrc/(2*M^2))*(profile ab (z ab))⁻¹+Tsrc*γ/(2*M^2)=
            (Tsrc/(2*M^2))*(iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2)⁻¹ := by
          rw [hinvMap ab hab]
          ring
        rw [he]
        exact hlocal ab hab _ (hzcc ab hab) 1)
  have hInv : 1/M ≤ R^2/(L^2*N^2) := by
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    have hRR : R ≤ R^2 := by nlinarith only [hR]
    nlinarith only [hNL,mul_le_mul_of_nonneg_left hRR hM.le]
  have herror : Cthird*R^2/(L^2*N^2)+1/M ≤ (Cthird+1)*R^2/(L^2*N^2) :=
    (add_le_add le_rfl hInv).trans_eq (by ring)
  apply hcount.trans
  calc
    _ ≤ 4*Csrc*((Cthird+1)*R^2/(L^2*N^2))*R^2/(|γ| *Uref)+2 := by
      apply add_le_add _ le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left herror (by positivity)) (sq_nonneg R)
    _ = _ := by ring_nf

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Csrc : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb γ Tsrc : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R Uref L K : ℝ} (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → γ ≠ 0 →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < Uref) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (∀ ab∈Gaps, 0 < d ab) →
    (∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ i, r ab i≠0) →
    (∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab) →
    (∀ ab∈Gaps, StrictMono (x ab)) →
    (∀ ab∈Gaps,
      e ab 1=e ab 0 ∧ v ab 1=v ab 0 ∧
      r ab 1=r ab 0+γ*e ab 0 ∧ s ab 1=s ab 0+γ*v ab 0) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    (∀ ab∈Gaps, ∀ t∈({x ab 0,x ab 3} : Finset ℝ), ∀ i,
      ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab t i)/2)⁻¹):ℝ × ℝ)-center‖ < a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    (Gaps.card:ℝ) ≤ 4*Csrc*(Cthird+1)*R^4/(L^2*N^2*|γ| *Uref)+2 :=
  HuxleyTriangularGapScratch.positive_difference_normalized_quartic_lower_reference_gap_packing (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


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



/-- Physical upper-triangular endpoint compression with the measured
rounded Third Condition. All normalization and rounding losses are derived. -/
private theorem positive_difference_physical_upper_pair_compression
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
    (∀ i, iteratedDeriv 2 (f yb) (xb i)/2=u i+b) →
    (∀ i, |μ yb (xb i)/μ ya (xa i)-1| ≤ Δ) →
    (∀ i, ‖((ya,t i):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t i+bnorm):ℝ × ℝ)-z₀‖ < a) →
    4*M^4*|b| *|u 1-u 0| ≤ C*(Δ+1/M)*T^2 := by
  obtain ⟨a,C,ha,hac,hC,hcompression⟩ :=
    positive_difference_physical_upper_endpoint_compression hσ hc hU
  refine ⟨a,C,ha,hac,hC,?_⟩
  intro F η x₀ y₀ ya yb b Δ T M xa xb hη hηmax hx₀ hy₀ hya hyb
    hf hbound htests hT hM hΔ hpoints f μ u t bnorm H z₀ hmap hthird hends
  have hpair (i j : Fin 2) (hij : u i < u j) :
      4*M^4*|b| *|u j-u i| ≤ C*(Δ+1/M)*T^2 := by
    rw [abs_of_pos (sub_pos.mpr hij)]
    exact hcompression F η x₀ y₀ ya yb b Δ T M ![xa i,xa j] ![xb i,xb j]
      hη hηmax hx₀ hy₀ hya hyb hf hbound htests hT hM hΔ
      (by
        intro k
        fin_cases k
        · exact hpoints i
        · exact hpoints j)
      hij
      (by
        intro k
        fin_cases k
        · exact hmap i
        · exact hmap j)
      (by
        intro k
        fin_cases k
        · exact hthird i
        · exact hthird j)
      (by
        intro k
        fin_cases k
        · exact hends i
        · exact hends j)
  rcases lt_trichotomy (u 0) (u 1) with hlt | heq | hgt
  · exact hpair 0 1 hlt
  · rw [heq,sub_self,abs_zero,mul_zero]
    have hMpos : 0 < M := by linarith only [hM]
    positivity
  · have hh := hpair 1 0 hgt
    rwa [abs_sub_comm] at hh


private theorem positive_difference_physical_upper_reference_gap_packing
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ (F : ℝ → ℝ) (η x₀ y₀ ya yb b Δ T M R Uref : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (xa xb : ℝ × ℝ → ℝ),
    0 < η → η ≤ 1/8 → x₀∈Icc (1:ℝ) 2 → y₀∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
    0 < T → 2 ≤ M → 0 < R → 0 < Uref → b ≠ 0 → 0 ≤ Δ →
    (∀ ab∈Gaps, xa ab∈Icc M (2*M) ∧ xb ab∈Icc M (2*M)) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1<ab.2 ∧
      ∀ t∈Refs, ¬(ab.1<t ∧ t<ab.2)) →
    let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
    let h := fun y z => iteratedDeriv 2 (f y) z/2
    let μ := fun y z => iteratedDeriv 3 (f y) (round z)/6
    let t := fun ab => (2*M^2/T)*h ya (xa ab)
    let bnorm := 2*M^2*b/T
    let H := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 F z.2-iteratedDeriv 2 F (z.2+η*z.1))/(σ*η)
    let z₀ := (y₀,H (y₀,x₀))
    (∀ ab∈Gaps, h ya (xa ab)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, h yb (xb ab)=h ya (xa ab)+b) →
    (∀ ab∈Gaps, |μ yb (xb ab)/μ ya (xa ab)-1| ≤ Δ) →
    (∀ ab∈Gaps, ‖((ya,t ab):ℝ × ℝ)-z₀‖ < a ∧
      ‖((yb,t ab+bnorm):ℝ × ℝ)-z₀‖ < a) →
    (Gaps.card:ℝ) ≤ C*(Δ+1/M)*T^2*R^2/(M^4*|b| *Uref)+2 := by
  obtain ⟨a,C,ha,_hac,hC,hcompression⟩ :=
    positive_difference_physical_upper_pair_compression hσ hc hU
  refine ⟨a,C,ha,hC,?_⟩
  intro F η x₀ y₀ ya yb b Δ T M R Uref Refs Gaps xa xb
    hη hηsmall hx₀ hy₀ hya hyb hf hbound htests hT hM hR hUref hb hΔ
    hpoints hsep hgap f h μ t bnorm H z₀ hinside hmap hthird hends
  have hMpos : 0 < M := by linarith only [hM]
  have hbpos : 0 < |b| := abs_pos.mpr hb
  have hdiam ab (hab : ab∈Gaps) cd (hcd : cd∈Gaps) :
      |h ya (xa ab)-h ya (xa cd)| ≤ C*(Δ+1/M)*T^2/(4*M^4*|b|) := by
    have hh := hcompression F η x₀ y₀ ya yb b Δ T M ![xa ab,xa cd] ![xb ab,xb cd]
      hη hηsmall hx₀ hy₀ hya hyb hf hbound htests hT hM hΔ
      (by
        intro i
        fin_cases i
        · exact hpoints ab hab
        · exact hpoints cd hcd)
      (by
        intro i
        fin_cases i
        · exact hmap ab hab
        · exact hmap cd hcd)
      (by
        intro i
        fin_cases i
        · exact hthird ab hab
        · exact hthird cd hcd)
      (by
        intro i
        fin_cases i
        · exact hends ab hab
        · exact hends cd hcd)
    change 4*M^4*|b| *|h ya (xa cd)-h ya (xa ab)| ≤ C*(Δ+1/M)*T^2 at hh
    apply (le_div_iff₀ (by positivity : 0 < 4*M^4*|b|)).mpr
    rw [mul_comm,abs_sub_comm]
    exact hh
  have hh := reference_gap_count_of_closed_profile_width Refs Gaps (fun ab => h ya (xa ab))
    (by positivity : 0 < Uref/(4*R^2))
    (by positivity : 0 ≤ C*(Δ+1/M)*T^2/(4*M^4*|b|)) hsep hgap hinside (fun ab hab cd hcd => hdiam cd hcd ab hab)
  convert hh using 1
  ring_nf
  simp only [inv_inv]
  ring

private theorem upper_reference_gap_source_scale
    {C K Tsrc E T M N R L b Uref : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hTsrc : 0 < Tsrc) (hM : 0 < M)
    (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L) (hUref : 0 < Uref) (hb : b ≠ 0)
    (hNL : (L*N)^2 ≤ M*R) (hscale : T*N*R^2=M^3) (hsource : Tsrc ≤ E*T) :
    C*(K*R^2/(L^2*N^2)+1/M)*Tsrc^2*R^2/(M^4*|b| *Uref) ≤
      C*(K+1)*E^2*M^2/(L^2*N^4*|b| *Uref) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hbpos : 0 < |b| := abs_pos.mpr hb
  have hInv : 1/M ≤ R^2/(L^2*N^2) := by
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    have hRR : R ≤ R^2 := by nlinarith only [hR]
    nlinarith only [hNL,mul_le_mul_of_nonneg_left hRR hM.le]
  have herr : K*R^2/(L^2*N^2)+1/M ≤ (K+1)*R^2/(L^2*N^2) :=
    (add_le_add le_rfl hInv).trans_eq (by ring)
  have hAmp : Tsrc^2 ≤ E^2*T^2 := by
    have hh := pow_le_pow_left₀ hTsrc.le hsource 2
    nlinarith only [hh]
  calc
    _ ≤ C*((K+1)*R^2/(L^2*N^2))*(E^2*T^2)*R^2/(M^4*|b| *Uref) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg R)
      exact mul_le_mul (mul_le_mul_of_nonneg_left herr hC) hAmp
        (sq_nonneg Tsrc) (by positivity)
    _ = _ := by
      have hTval : T=M^3/(N*R^2) :=
        (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
      rw [hTval]
      field_simp

/-- Actual quartic residuals yield the upper-triangular long-gap
packing bound; the improved Third witnesses are constructed internally. -/
theorem positive_difference_normalized_quartic_upper_reference_gap_packing
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R Uref L K : ℝ} (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → b ≠ 0 → Tsrc ≤ E*T → T*N*R^2=M^3 →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < Uref) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (∀ ab∈Gaps, 0 < d ab) →
    (∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ i, r ab i≠0) →
    (∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab) →
    (∀ ab∈Gaps, StrictMono (x ab)) →
    (∀ ab∈Gaps,
      e ab 1=e ab 0+b*r ab 0 ∧ v ab 1=v ab 0+b*s ab 0 ∧
      r ab 1=r ab 0 ∧ s ab 1=s ab 0) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    (∀ ab∈Gaps, ∀ t∈({x ab 0,x ab 3} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab t i)/2)):ℝ × ℝ)-center‖ < a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    (Gaps.card:ℝ) ≤ Csrc*(Cthird+1)*E^2*M^2/(L^2*N^4*|b| *Uref)+2 := by
  classical
  obtain ⟨a,Csrc,ha,hCsrc,hcompression⟩ :=
    positive_difference_physical_upper_reference_gap_packing hσsrc hcsrc hUsrc
  refine ⟨a,Csrc,ha,hCsrc,?_⟩
  intro Fsrc η xcenter ycenter ya yb b Tsrc E Refs Gaps x xref e r v s curve d alpha beta
    σ δ T M N R Uref L K A W
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hb hsourceScale hscale
    yp F Hsrc center hσ hδ hF hT hM hN hR hU hL hNL hK hA hW hsep hgap hd href hcurve hr hdet hden hmono htransport
    f n mu nu Den g H Gcoord profile hbase hpoint hends hsquare hspacing hres hlocalEnds
    κ Cphys Gamma Cthird
  let munew := fun ab t i => iteratedDeriv 3 (f i) (round (curve ab t i))/6
  have hηmax : η ≤ 1/8 := hηsmall
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCt : 0 ≤ Cthird := by dsimp only [Cthird,Gamma]; positivity
  have hdenpos ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      0 < Den ab t i := (hd ab hab).trans_le (hden ab hab t ht i).1
  have hex : ∀ ab∈Gaps, ∃ z∈Ioo (x ab 0) (x ab 3),
      |munew ab z 1*(Den ab z 1)^3/(munew ab z 0*(Den ab z 0)^3)-1| ≤ Cthird*R^2/(L^2*N^2) := by
    intro ab hab
    exact physicalModelPhase_quartic_long_block_third_condition (x ab)
      hσ hδ hF hT hM hN hR hL hNL (hd ab hab) hK hA hW
      (href ab hab) (hcurve ab hab) (hr ab hab) (hdet ab hab)
      (fun t ht i => (hden ab hab t ht i).1)
      (fun t ht i => (hden ab hab t ht i).2) (hmono ab hab)
      (hbase ab hab) (hpoint ab hab) (hsquare ab hab) (hspacing ab hab) (hres ab hab)
  choose! z hz hthird using hex
  have hzcc ab (hab : ab∈Gaps) : z ab∈Icc (x ab 0) (x ab 3) := ⟨(hz ab hab).1.le,(hz ab hab).2.le⟩
  have hinside ab (hab : ab∈Gaps) : profile ab (z ab)∈Ioo ab.1 ab.2 := by
    have hx03 : x ab 0 ≤ x ab 3 := (hmono ab hab).monotone (by decide)
    have hx0 : x ab 0∈Icc (x ab 0) (x ab 3) := ⟨le_rfl,hx03⟩
    have hx3 : x ab 3∈Icc (x ab 0) (x ab 3) := ⟨hx03,le_rfl⟩
    have hlow : profile ab (x ab 3) ≤ profile ab (z ab) := by
      dsimp only [profile]
      rw [hpoint ab hab _ hx3 0,hpoint ab hab _ (hzcc ab hab) 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ (hzcc ab hab) 0) (hdenpos ab hab _ hx3 0) (hzcc ab hab).2
    have hhigh : profile ab (z ab) ≤ profile ab (x ab 0) := by
      dsimp only [profile]
      rw [hpoint ab hab _ (hzcc ab hab) 0,hpoint ab hab _ hx0 0]
      exact reference_chart_fraction_antitone (hdet ab hab 0)
        (hdenpos ab hab _ hx0 0) (hdenpos ab hab _ (hzcc ab hab) 0) (hzcc ab hab).1
    exact ⟨(hends ab hab).2.1.trans_le hlow,hhigh.trans_lt (hends ab hab).1.2⟩
  let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
  have hsource i : f i=fun z => Src (yp i) ((A i:ℝ)+z) := by
    funext z
    dsimp only [f,heathBrownPhysicalPhase,F,Src]
    field_simp
  have hjet i k t : iteratedDeriv k (f i) t=
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hrounded i t : iteratedDeriv 3 (f i) (round t)=
      iteratedDeriv 3 (Src (yp i)) (round ((A i:ℝ)+t)) := by
    rw [hjet,round_intCast_add,Int.cast_add]
  have hyp i : yp i∈Icc (1:ℝ) 2 := by fin_cases i <;> assumption
  have hphysical ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      (A i:ℝ)+curve ab t i∈Icc M (2*M) :=
    ⟨by linarith only [hA i,(hcurve ab hab t ht i).1],
     by linarith only [hW i,(hcurve ab hab t ht i).2]⟩
  have horder ab (hab : ab∈Gaps) u (hu : u∈Icc (x ab 0) (x ab 3))
      w (hw : w∈Icc (x ab 0) (x ab 3)) (huw : u ≤ w) i :
      iteratedDeriv 2 (f i) (curve ab w i)/2 ≤ iteratedDeriv 2 (f i) (curve ab u i)/2 := by
    rw [hpoint ab hab w hw i,hpoint ab hab u hu i]
    exact reference_chart_fraction_antitone (hdet ab hab i)
      (hdenpos ab hab u hu i) (hdenpos ab hab w hw i) huw
  have hlocal ab (hab : ab∈Gaps) t (ht : t∈Icc (x ab 0) (x ab 3)) i :
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab t i)/2)):ℝ × ℝ)-center‖ < a := by
    have hxorder := (hmono ab hab).monotone (by decide : (0:Fin 4) ≤ 3)
    have hl := hlocalEnds ab hab (x ab 3) (by simp) i
    have hu := hlocalEnds ab hab (x ab 0) (by simp) i
    have hlo := mul_le_mul_of_nonneg_left
      (horder ab hab t ht (x ab 3) ⟨hxorder,le_rfl⟩ ht.2 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    have hhi := mul_le_mul_of_nonneg_left
      (horder ab hab (x ab 0) ⟨le_rfl,hxorder⟩ t ht ht.1 i)
      (by positivity : 0 ≤ 2*M^2/Tsrc)
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab (x ab 3) i)/2)-center.2| < a at hl
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab (x ab 0) i)/2)-center.2| < a at hu
    change max |yp i-center.1|
      |(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab t i)/2)-center.2| < a
    refine max_lt_iff.mpr ⟨(max_lt_iff.mp hl).1,abs_lt.mpr ⟨?_,?_⟩⟩
    · linarith only [(abs_lt.mp (max_lt_iff.mp hl).2).1,hlo]
    · linarith only [(abs_lt.mp (max_lt_iff.mp hu).2).2,hhi]
  have hDsame ab (hab : ab∈Gaps) t : Den ab t 1=Den ab t 0 := by
    dsimp only [Den]
    rw [(htransport ab hab).2.2.1,(htransport ab hab).2.2.2]
  have hmap ab (hab : ab∈Gaps) :
      iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2=profile ab (z ab)+b := by
    change _=iteratedDeriv 2 (f 0) (curve ab (z ab) 0)/2+b
    rw [hpoint ab hab _ (hzcc ab hab) 1,hpoint ab hab _ (hzcc ab hab) 0,hDsame ab hab]
    rw [(htransport ab hab).1,(htransport ab hab).2.1]
    have hdz : r ab 0*z ab+s ab 0 ≠ 0 := (hdenpos ab hab _ (hzcc ab hab) 0).ne'
    dsimp only [Den]
    field_simp [hdz]
    ring
  have hweighted ab (hab : ab∈Gaps) :
      |munew ab (z ab) 1/munew ab (z ab) 0-1| ≤ Cthird*R^2/(L^2*N^2) := by
    have hh := hthird ab hab
    rw [hDsame ab hab] at hh
    rwa [mul_div_mul_right _ _ (pow_ne_zero 3 (hdenpos ab hab _ (hzcc ab hab) 0).ne')] at hh
  let xa := fun ab => (A 0:ℝ)+curve ab (z ab) 0
  let xb := fun ab => (A 1:ℝ)+curve ab (z ab) 1
  have hua ab : iteratedDeriv 2 (Src ya) (xa ab)/2=profile ab (z ab) :=
    (congrArg (fun u : ℝ => u/2) (hjet 0 2 (curve ab (z ab) 0))).symm
  have hub ab : iteratedDeriv 2 (Src yb) (xb ab)/2=
      iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2 :=
    (congrArg (fun u : ℝ => u/2) (hjet 1 2 (curve ab (z ab) 1))).symm
  have hcount := hcompression Fsrc η xcenter ycenter ya yb b
    (Cthird*R^2/(L^2*N^2)) Tsrc M R Uref Refs Gaps xa xb
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hRpos hU hb
    (by positivity) (fun ab hab => ⟨hphysical ab hab _ (hzcc ab hab) 0,
      hphysical ab hab _ (hzcc ab hab) 1⟩) hsep hgap
    (by intro ab hab; change iteratedDeriv 2 (Src ya) (xa ab)/2∈Icc ab.1 ab.2
        rw [hua]; exact ⟨(hinside ab hab).1.le,(hinside ab hab).2.le⟩)
    (by
      intro ab hab
      change iteratedDeriv 2 (Src yb) (xb ab)/2=
        (iteratedDeriv 2 (Src ya) (xa ab)/2)+b
      rw [hua,hub]
      exact hmap ab hab)
    (by
      intro ab hab
      have hh := hweighted ab hab
      change |(iteratedDeriv 3 (f 1) (round (curve ab (z ab) 1))/6)/
        (iteratedDeriv 3 (f 0) (round (curve ab (z ab) 0))/6)-1| ≤ _ at hh
      rw [hrounded,hrounded] at hh
      change |(iteratedDeriv 3 (Src yb) (round (xb ab))/6)/
        (iteratedDeriv 3 (Src ya) (round (xa ab))/6)-1| ≤ _
      exact hh)
    (by
      intro ab hab
      change ‖((ya,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)):ℝ × ℝ)-center‖ < a ∧
        ‖((yb,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+
          2*M^2*b/Tsrc):ℝ × ℝ)-center‖ < a
      rw [hua]
      constructor
      · exact hlocal ab hab _ (hzcc ab hab) 0
      · have he : (2*M^2/Tsrc)*profile ab (z ab)+2*M^2*b/Tsrc=
            (2*M^2/Tsrc)*(iteratedDeriv 2 (f 1) (curve ab (z ab) 1)/2) := by
          rw [hmap ab hab]
          ring
        rw [he]
        exact hlocal ab hab _ (hzcc ab hab) 1)
  exact hcount.trans (add_le_add (upper_reference_gap_source_scale hCsrc.le hCt
    hTsrc hM hN hR hL hU hb hNL hscale hsourceScale) le_rfl)

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a Csrc : ℝ, 0 < a ∧ 0 < Csrc ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb b Tsrc E : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (x : ℝ × ℝ → Fin 4 → ℝ)
    (xref e r v s : ℝ × ℝ → Fin 2 → ℝ)
    (curve : ℝ × ℝ → ℝ → Fin 2 → ℝ) (d alpha beta : ℝ × ℝ → ℝ)
    {σ δ T M N R Uref L K : ℝ} (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    0 < η → η ≤ 1/8 → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → b ≠ 0 → Tsrc ≤ E*T → T*N*R^2=M^3 →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < Uref) →
    (0 < L) →
    ((L*N)^2 ≤ M*R) →
    (0 ≤ K) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → Uref/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (∀ ab∈Gaps, 0 < d ab) →
    (∀ ab∈Gaps, ∀ i, xref ab i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      curve ab t i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ i, r ab i≠0) →
    (∀ ab∈Gaps, ∀ i, v ab i*r ab i-e ab i*s ab i=1) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      d ab ≤ r ab i*t+s ab i ∧ r ab i*t+s ab i ≤ 2*d ab) →
    (∀ ab∈Gaps, StrictMono (x ab)) →
    (∀ ab∈Gaps,
      e ab 1=e ab 0+b*r ab 0 ∧ v ab 1=v ab 0+b*s ab 0 ∧
      r ab 1=r ab 0 ∧ s ab 1=s ab 0) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun ab t i => (round (curve ab t i):ℝ)-(round (xref ab i):ℝ)
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (xref ab i))/6
    let nu := fun ab i => iteratedDeriv 4 (f i) (round (xref ab i))/24
    let Den := fun ab t i => r ab i*t+s ab i
    let g := fun ab => rationalPhase (mu ab 0) (r ab 0) (s ab 0) (mu ab 1) (r ab 1) (s ab 1)
    let H := fun ab => quarticPhase (mu ab 0) (nu ab 0) (r ab 0) (s ab 0)
      (mu ab 1) (nu ab 1) (r ab 1) (s ab 1)
    let Gcoord := fun ab => minorArcCoordinate (mu ab 0) (r ab 0) (s ab 0)
    let profile := fun ab t => iteratedDeriv 2 (f 0) (curve ab t 0)/2
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (xref ab i)/2=e ab i/r ab i) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i,
      iteratedDeriv 2 (f i) (curve ab t i)/2=(e ab i*t+v ab i)/Den ab t i) →
    (∀ ab∈Gaps, profile ab (x ab 0)∈Ioo ab.1 ab.2 ∧
      profile ab (x ab 3)∈Ioo ab.1 ab.2) →
    (∀ ab∈Gaps, ∀ t∈Icc (x ab 0) (x ab 3), ∀ i, |n ab t i|^2 ≤ M*R) →
    (∀ ab∈Gaps, ∀ j : Fin 3, L*N ≤ |Gcoord ab (x ab j.succ)-Gcoord ab (x ab j.castSucc)|) →
    (∀ ab∈Gaps, ∀ j : Fin 4, |alpha ab*x ab j+beta ab-g ab (x ab j)+H ab (x ab j)| ≤
      K*R^2/|r ab 0*Gcoord ab (x ab j)|) →
    (∀ ab∈Gaps, ∀ t∈({x ab 0,x ab 3} : Finset ℝ), ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab t i)/2)):ℝ × ℝ)-center‖ < a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*K+9*quarticReciprocalConstant σ δ)
    (Gaps.card:ℝ) ≤ Csrc*(Cthird+1)*E^2*M^2/(L^2*N^4*|b| *Uref)+2 :=
  HuxleyTriangularGapScratch.positive_difference_normalized_quartic_upper_reference_gap_packing (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


private theorem charted_selected_blocks
    {b B c C n nSource nSelected : ℕ}
    (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    32*b*n ≤ nSelected := by
  have hbudget : 6+c*(105+544*b) ≤ 6+C*(105+544*B) := by gcongr
  have hlower := (Nat.mul_le_mul_right n hbudget).trans hblocks
  have hoffset : 6+105*c ≤ (6+105*c)*n := Nat.le_mul_of_pos_right _ hn
  have hmul : c*(17*(32*b*n)) ≤ c*(17*nSelected) := by
    nlinarith only [hlower,hselection,hoffset]
  have hh := Nat.le_of_mul_le_mul_left hmul hc
  exact Nat.le_of_mul_le_mul_left hh (by decide : 0 < (17:ℕ))

/-- The chart and height-label budgets cancel from the physical unit
length. They remain in the original-family block size, not in Lunit. -/
private theorem charted_selected_source_length
    {b B c C n nSource nSelected : ℕ} {κ Cphys : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hκ : 0 < κ) (hCphys : 0 < Cphys)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    (2*κ/Cphys)*(n:ℝ) ≤ κ/(16*(b:ℝ)*Cphys)*(nSelected:ℝ) := by
  have hmass : (32:ℝ)*(b:ℝ)*(n:ℝ) ≤ (nSelected:ℝ) := by
    exact_mod_cast charted_selected_blocks hc hbB hcC hn hselection hblocks
  have hbreal : (0:ℝ) < b := Nat.cast_pos.mpr hb
  calc
    _ = κ/(16*(b:ℝ)*Cphys)*((32:ℝ)*(b:ℝ)*(n:ℝ)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)


private theorem physical_source_quartic_constants_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 ≤ δ) :
    0 ≤ quarticReciprocalConstant σ δ ∧ 0 ≤ quarticNonlinearResidualConstant σ δ := by
  have hκ := modelPhaseThirdLower_pos hσ
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ
  constructor
  · dsimp only [quarticReciprocalConstant]
    positivity
  · dsimp only [quarticNonlinearResidualConstant]
    positivity


/-- The SAME actual Fourier families give both triangular long-gap tails
at the length of their original-family blocks. Finite source-chart
membership remains an explicit source-localization input. -/
theorem positive_difference_actual_fourier_charted_triangular_long_gap_packing
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor n : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < n) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0*n ≤ (S ab).card) →
    let L := (2*κ/Cphys)*(n:ℝ)
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (Gaps.card:ℝ) ≤ Cupper*(Cthird+1)*E^2*M^2/(L^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (Gaps.card:ℝ) ≤ 4*Clower*(Cthird+1)*R^4/(L^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2) := by
  classical
  obtain ⟨aU,CU,haU,hCU,hupper⟩ :=
    positive_difference_normalized_quartic_upper_reference_gap_packing hσsrc hcsrc hUsrc
  obtain ⟨η₀,aL,CL,hη₀,hηcap,haL,hCL,hlower⟩ :=
    positive_difference_normalized_quartic_lower_reference_gap_packing hσsrc hcsrc hUsrc
  refine ⟨η₀,min aU aL,CU,CL,hη₀,hηcap,lt_min haU haL,hCU,hCL,?_⟩
  intro Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Gaps Bselect
    Bmajor Cmajor n S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal hn
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor hblocks L Gamma Cthird
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hLp : 0 < L := by dsimp only [L]; positivity
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hS ab (hab : ab∈Gaps) :
      6+Ccharts ab*(105+544*Blabels ab) ≤ (S ab).card := by
    have hb : 6+Ccharts ab*(105+544*Blabels ab) ≤ m0 := by
      dsimp only [m0]
      gcongr
      exact hCmajor ab hab
      exact hBmajor ab hab
    exact hb.trans ((Nat.le_mul_of_pos_right m0 hn).trans (hblocks ab hab))
  have hall ab (hab : ab∈Gaps) :=
    physicalModelPhase_actual_fourier_charted_reference_gap_quartic_witnesses
      Uref Refs (Bselect:=Bselect) (gapLo:=ab.1) (gapHi:=ab.2)
      (S ab) Q K₀ (rat ab) (vinv ab) (parity ab) (anchor ab) Mat
      (e ab) (r ab) (v ab) (s ab)
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) (F:=F) (A:=fun i => (A i:ℝ)) (W:=W) (x:=x ab)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx ab hab) (hwindow ab hab) (hden ab hab) hlambda hUband hθ hθmax (hcurv ab hab) (hinv ab hab) (hchart ab hab) (horientation ab hab) hBcut (hs ab hab) (hrefSet ab hab) (hparentSet ab hab) hsep (hwideL ab hab) (hwideU ab hab) hUref hBselectSize hcutMargin hselectedWrap (hreferenceDen ab hab) (hgapWidth ab hab) hRQ hselectedUpper hscaleTen (hfamilyGap ab hab)
      (hsourceColor ab hab) (hS ab hab) (hlevel ab hab) (hcolor ab hab) (hnear ab hab)
      hsmall hNR hRN hNcube hminscale hMatdet (hMatt ab hab) (hMatmap ab hab) hMatgamma
      hNtwo (hL ab hab) (hU ab hab) (hanchor ab hab) (hcut ab hab) (hcount ab hab)
  choose! Schart hSchart hSmass Good hGood hGoodmass jref hjref xref hxr hrest using hall
  have hselected ab (hab : ab∈Gaps) := hrest ab hab hsize hD hΔ hBsize
  choose! d l w hd S₀ hS₀ hcard hinside j z curve alpha beta hj hmono hLsource hNL hKp
    hcurve hspacing hres using hselected
  let ep := fun ab => (![e ab,Mat 0*e ab+Mat 1*r ab] : Fin 2 → ℤ)
  let rp := fun ab => (![r ab,Mat 2*e ab+Mat 3*r ab] : Fin 2 → ℤ)
  let vp := fun ab => (![v ab,Mat 0*v ab+Mat 1*s ab] : Fin 2 → ℤ)
  let sp := fun ab => (![s ab,Mat 2*v ab+Mat 3*s ab] : Fin 2 → ℤ)
  have hlong ab (hab : ab∈Gaps) :
      L ≤ κ/(16*(Blabels ab:ℝ)*Cphys)*((S₀ ab).card:ℝ) :=
    charted_selected_source_length
      (by dsimp only [Blabels]; omega) (by dsimp only [Ccharts]; omega)
      (hBmajor ab hab) (hCmajor ab hab) hn hκ hCphys (hcard ab hab) (hblocks ab hab)
  by_cases hne : Gaps.Nonempty
  · obtain ⟨ab₀,hab₀⟩ := hne
    have hNLL : (L*N)^2 ≤ M*R :=
      (pow_le_pow_left₀ (mul_pos hLp hN).le
        (mul_le_mul_of_nonneg_right (hlong ab₀ hab₀) hN.le) 2).trans (hNL ab₀ hab₀)
    let take : Fin 4 → Fin 8 := fun i => ⟨i.val,by omega⟩
    have htake : StrictMono take := fun _ _ hh => hh
    let z4 := fun ab i => z ab (take i)
    have hsub ab (hab : ab∈Gaps) : Icc (z4 ab 0) (z4 ab 3) ⊆ Icc (z ab 0) (z ab 7) := by
      intro t ht
      exact ⟨ht.1,ht.2.trans ((hmono ab hab).monotone (by change (3:Fin 8) ≤ 7; decide))⟩
    have hdetp ab (hab : ab∈Gaps) i : vp ab i*rp ab i-ep ab i*sp ab i=1 := by
      fin_cases i
      · exact hchart ab hab
      · change (Mat 0*v ab+Mat 1*s ab)*(Mat 2*e ab+Mat 3*r ab)-
          (Mat 0*e ab+Mat 1*r ab)*(Mat 2*v ab+Mat 3*s ab)=1
        linear_combination (v ab*r ab-e ab*s ab)*hMatdet+hchart ab hab
    have hends ab (hab : ab∈Gaps) (a : Fin 4) :
        iteratedDeriv 2 (f 0) (curve ab (z4 ab a) 0)/2∈Ioo ab.1 ab.2 := by
      have ha : z4 ab a∈Icc (z ab 0) (z ab 7) :=
        ⟨(hmono ab hab).monotone (by omega),(hmono ab hab).monotone (by omega)⟩
      rw [((hcurve ab hab _ ha).2 0).2.2.2.1,←(hj ab hab (take a)).2 0]
      exact hinside ab hab _ (hj ab hab (take a)).1
    have hendlevel ab (hab : ab∈Gaps) k i :
        iteratedDeriv 2 (f i) (curve ab (z ab k) i)/2=(rat ab (j ab k) i:ℝ) := by
      have hzk : z ab k∈Icc (z ab 0) (z ab 7) :=
        ⟨(hmono ab hab).monotone (by omega),(hmono ab hab).monotone (by omega)⟩
      exact (((hcurve ab hab _ hzk).2 i).2.2.2.1).trans ((hj ab hab k).2 i).symm
    constructor
    · intro htri hentry
      apply hupper Fsrc η xcenter ycenter ya yb (Mat 1) Tsrc E
        Refs Gaps z4 xref
        (fun ab i => (ep ab i:ℝ)) (fun ab i => (rp ab i:ℝ))
        (fun ab i => (vp ab i:ℝ)) (fun ab i => (sp ab i:ℝ))
        curve d alpha beta (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R)
        (Uref:=(Uref:ℝ)) (L:=L) (K:=Kres) A
        hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
        (by exact_mod_cast hentry) hsourceScale hscale
        hσ hδ hF hT hM hN hR hUp hLp hNLL (hKp ab₀ hab₀) hA hW
        (by
          intro a ha b hb hne'
          calc
            (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
            _ ≤ |a-b| := (hsep a ha b hb hne').le)
        hgap hd
        (fun ab hab i => (hxr ab hab i).2.1)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).1)
        (fun ab hab i => by
          change (rp ab i:ℝ) ≠ 0
          exact_mod_cast (mul_ne_zero_iff.mp (hxr ab hab i).1.ne').1)
        (fun ab hab i => by
          change (vp ab i:ℝ)*(rp ab i:ℝ)-(ep ab i:ℝ)*(sp ab i:ℝ)=1
          exact_mod_cast hdetp ab hab i)
        (fun ab hab t ht i => ⟨((hcurve ab hab t (hsub ab hab ht)).2 i).2.1,
          ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.1⟩)
        (fun ab hab => (hmono ab hab).comp htake)
        (by
          intro ab _
          simp [ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2])
        (fun ab hab i => (hxr ab hab i).2.2.1)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.1)
        (fun ab hab => ⟨hends ab hab 0,hends ab hab 3⟩)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.2)
        (fun ab hab i => (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le).trans
          (hspacing ab hab (⟨i.val,by omega⟩ : Fin 7)))
        (fun ab hab i => hres ab hab (take i))
      intro ab hab t ht i
      have hsample (k : Fin 8) :
          ‖((yp i,(2*M^2/Tsrc)*(iteratedDeriv 2 (f i) (curve ab (z ab k) i)/2)):ℝ × ℝ)-center‖ < aU := by
        rw [hendlevel ab hab]
        exact ((hlocal ab hab _ (hS₀ ab hab (hj ab hab k).1) i).1).trans_le
          (min_le_left _ _)
      rcases Finset.mem_insert.mp ht with he | he
      · subst t
        exact hsample (take 0)
      · have he' : t=z4 ab 3 := Finset.mem_singleton.mp he
        subst t
        exact hsample (take 3)
    · intro htri hentry
      apply hlower Fsrc η xcenter ycenter ya yb (Mat 2) Tsrc
        Refs Gaps z4 xref
        (fun ab i => (ep ab i:ℝ)) (fun ab i => (rp ab i:ℝ))
        (fun ab i => (vp ab i:ℝ)) (fun ab i => (sp ab i:ℝ))
        curve d alpha beta (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R)
        (Uref:=(Uref:ℝ)) (L:=L) (K:=Kres) A
        hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo
        (by exact_mod_cast hentry)
        hσ hδ hF hT hM hN hR hUp hLp hNLL (hKp ab₀ hab₀) hA hW
        (by
          intro a ha b hb hne'
          calc
            (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
            _ ≤ |a-b| := (hsep a ha b hb hne').le)
        hgap hd
        (fun ab hab i => (hxr ab hab i).2.1)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).1)
        (fun ab hab i => by
          change (rp ab i:ℝ) ≠ 0
          exact_mod_cast (mul_ne_zero_iff.mp (hxr ab hab i).1.ne').1)
        (fun ab hab i => by
          change (vp ab i:ℝ)*(rp ab i:ℝ)-(ep ab i:ℝ)*(sp ab i:ℝ)=1
          exact_mod_cast hdetp ab hab i)
        (fun ab hab t ht i => ⟨((hcurve ab hab t (hsub ab hab ht)).2 i).2.1,
          ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.1⟩)
        (fun ab hab => (hmono ab hab).comp htake)
        (by
          intro ab _
          simp [ep,rp,vp,sp,htri.1,htri.2.1,htri.2.2,add_comm])
        (fun ab hab i => (hxr ab hab i).2.2.1)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.1)
        (fun ab hab => ⟨hends ab hab 0,hends ab hab 3⟩)
        (fun ab hab t ht i => ((hcurve ab hab t (hsub ab hab ht)).2 i).2.2.2.2)
        (fun ab hab i => (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le).trans
          (hspacing ab hab (⟨i.val,by omega⟩ : Fin 7)))
        (fun ab hab i => hres ab hab (take i))
      intro ab hab t ht i
      have hsample (k : Fin 8) :
          ‖((yp i,(Tsrc/(2*M^2))*(iteratedDeriv 2 (f i) (curve ab (z ab k) i)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL := by
        rw [hendlevel ab hab]
        exact ((hlocal ab hab _ (hS₀ ab hab (hj ab hab k).1) i).2).trans_le
          (min_le_right _ _)
      rcases Finset.mem_insert.mp ht with he | he
      · subst t
        exact hsample (take 0)
      · have he' : t=z4 ab 3 := Finset.mem_singleton.mp he
        subst t
        exact hsample (take 3)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
    have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
    have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
    obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
    have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
    constructor <;> intro _ _ <;>
      dsimp only [Cthird,Kres,Gamma,Cc,Ct,C₂,C₃] <;> positivity

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor n : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < n) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0*n ≤ (S ab).card) →
    let L := (2*κ/Cphys)*(n:ℝ)
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (Gaps.card:ℝ) ≤ Cupper*(Cthird+1)*E^2*M^2/(L^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (Gaps.card:ℝ) ≤ 4*Clower*(Cthird+1)*R^4/(L^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2) :=
  HuxleyTriangularGapScratch.positive_difference_actual_fourier_charted_triangular_long_gap_packing (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

private theorem reciprocal_square_prefix (J : ℕ) :
    (∑ m∈Finset.range J, 1/((m:ℝ)+1)^2) ≤ 2-2/((J:ℝ)+1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    have hJ : (0:ℝ) ≤ J := Nat.cast_nonneg J
    have hstep : 1/((J:ℝ)+1)^2 ≤ 2/((J:ℝ)+1)-2/((J:ℝ)+1+1) := by
      have h₁ : (J:ℝ)+1 ≠ 0 := by positivity
      have h₂ : (J:ℝ)+1+1 ≠ 0 := by positivity
      have he : 2/((J:ℝ)+1)-2/((J:ℝ)+1+1)=2/(((J:ℝ)+1)*((J:ℝ)+1+1)) := by
        field_simp
        ring
      rw [he]
      apply (div_le_div_iff₀ (by positivity : 0 < ((J:ℝ)+1)^2)
        (by positivity : 0 < ((J:ℝ)+1)*((J:ℝ)+1+1))).mpr
      nlinarith
    linarith only [ih,hstep]

private theorem finite_occupied_tail_sum
    {ι : Type*} (S : Finset ι) (n : ι → ℕ) (J : ℕ)
    {A B : ℝ} (hB : 0 ≤ B) (hcap : ∀ i∈S, n i ≤ J)
    (htail : ∀ m∈Finset.range J,
      ((S.filter (fun i => m < n i)).card:ℝ) ≤ A+B/((m:ℝ)+1)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(J:ℝ)+2*B := by
  classical
  have hrepr :
      (∑ m∈Finset.range J, ((S.filter (fun i => m < n i)).card:ℝ)) =
        ∑ i∈S, (n i:ℝ) := by
    calc
      _ = ∑ m∈Finset.range J, ∑ i∈S, if m < n i then (1:ℝ) else 0 := by
        simp
      _ = ∑ i∈S, ∑ m∈Finset.range J, if m < n i then (1:ℝ) else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfilter : (Finset.range J).filter (fun m => m < n i)=Finset.range (n i) := by
          ext m
          simp only [Finset.mem_filter,Finset.mem_range]
          have hiCap := hcap i hi
          omega
        rw [← Finset.sum_filter,hfilter]
        simp
  rw [← hrepr]
  calc
    _ ≤ ∑ m∈Finset.range J, (A+B/((m:ℝ)+1)^2) := Finset.sum_le_sum htail
    _ = A*(J:ℝ)+B*(∑ m∈Finset.range J,1/((m:ℝ)+1)^2) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
        nsmul_eq_mul,div_eq_mul_inv,one_mul,Finset.mul_sum]
      ring
    _ ≤ A*(J:ℝ)+2*B := by
      have hh : (∑ m∈Finset.range J,1/((m:ℝ)+1)^2) ≤ 2 :=
        (reciprocal_square_prefix J).trans (sub_le_self _ (by positivity))
      nlinarith only [mul_le_mul_of_nonneg_left hh hB]

private theorem finite_occupied_cubic_tail_sum
    {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    {A B K c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hc : 0 < c)
    (hcap : ∀ i∈S, (n i:ℝ)^3*c ≤ K)
    (htail : ∀ m : ℕ, 0 < m →
      ((S.filter (fun i => m ≤ n i)).card:ℝ) ≤ A+B/(m:ℝ)^2) :
    (∑ i∈S, (n i:ℝ)) ≤ A*(K/c)^((3:ℝ)⁻¹)+2*B := by
  classical
  let J := S.sup n
  let root := (K/c)^((3:ℝ)⁻¹)
  have hroot : 0 ≤ root := Real.rpow_nonneg (div_nonneg hK hc.le) _
  have hrootcube : root^3=K/c :=
    Real.rpow_inv_natCast_pow (div_nonneg hK hc.le) (by norm_num : (3:ℕ) ≠ 0)
  have hJcube : (J:ℝ)^3 ≤ K/c := by
    by_cases hs : S.Nonempty
    · obtain ⟨i,hi,he⟩ := Finset.sup_mem_of_nonempty (f:=n) hs
      change n i=J at he
      rw [← he]
      exact (le_div_iff₀ hc).mpr (hcap i hi)
    · have hJzero : J=0 := by simp [J,Finset.not_nonempty_iff_eq_empty.mp hs]
      rw [hJzero]
      simpa using div_nonneg hK hc.le
  have hJ : (J:ℝ) ≤ root := (pow_le_pow_iff_left₀ (Nat.cast_nonneg J)
    hroot (by decide : (3:ℕ) ≠ 0)).mp (by rw [hrootcube]; exact hJcube)
  have hh := finite_occupied_tail_sum S n J hB (fun i hi => Finset.le_sup hi)
    (fun m _ => by
      simpa only [Nat.lt_iff_add_one_le,Nat.cast_add,Nat.cast_one] using htail (m+1) (by omega))
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hJ hA) le_rfl)


private theorem quotient_block_mass (a b : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    0 < a/b ∧ b*(a/b) ≤ a ∧ a ≤ 2*b*(a/b) := by
  have hpos := Nat.div_pos hba hb
  have hrem := Nat.mod_lt a hb
  have he := Nat.div_add_mod a b
  have hmul : b ≤ b*(a/b) := Nat.le_mul_of_pos_right b hpos
  refine ⟨hpos,Nat.mul_div_le a b,?_⟩
  nlinarith only [hrem,he,hmul]



private theorem original_block_mass_of_cubic_and_gap_bounds
    {ι : Type*} (Gaps : Finset ι) (S : ι → Finset ℕ) (m0 : ℕ)
    {κ L P c U Bcap Btail ac bt W₁ W₂ W₃ : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) (hP : 0 < P) (hc : 0 < c) (hU : 0 < U)
    (hBcap : 0 ≤ Bcap) (hac : 0 ≤ ac) (hat : 0 ≤ bt)
    (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂) (hW₃ : 0 ≤ W₃)
    (hm0 : 0 < m0) (hS : ∀ ab∈Gaps, m0 ≤ (S ab).card)
    (hcap : ∀ ab∈Gaps, κ*c*(L*((S ab).card/m0:ℕ))^3*P ≤ ac*Bcap*W₁*W₂*W₃)
    (htail : ∀ (G : Finset ι), G ⊆ Gaps → ∀ m : ℕ, 0 < m →
      (∀ ab∈G, m0*m ≤ (S ab).card) →
      (G.card:ℝ) ≤ bt*Btail*W₁*W₂*W₃/((L*(m:ℝ))^2*P*c*U)+2) :
    (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤
      4*(m0:ℝ)*((ac*max Bcap Btail*W₁*W₂*W₃/(κ*L^3*P*c))^((3:ℝ)⁻¹)+
        bt*max Bcap Btail*W₁*W₂*W₃/(L^2*P*c*U)) := by
  classical
  let Dcap := ac*max Bcap Btail*W₁*W₂*W₃
  let Dtail := bt*max Bcap Btail*W₁*W₂*W₃
  have hDcap : 0 ≤ Dcap := by dsimp only [Dcap]; positivity
  have hDtail : 0 ≤ Dtail := by dsimp only [Dtail]; positivity
  have hcapMono : ac*Bcap*W₁*W₂*W₃ ≤ Dcap :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) hac) hW₁) hW₂) hW₃
  have htailMono : bt*Btail*W₁*W₂*W₃ ≤ Dtail :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hat) hW₁) hW₂) hW₃
  let n := fun ab => (S ab).card/m0
  have hn ab (hab : ab∈Gaps) := quotient_block_mass (S ab).card m0 hm0 (hS ab hab)
  have hcap' ab (hab : ab∈Gaps) : (n ab:ℝ)^3*c ≤ Dcap/(κ*L^3*P) := by
    apply (le_div_iff₀ (by positivity : 0 < κ*L^3*P)).mpr
    calc
      _ = κ*c*(L*(n ab:ℝ))^3*P := by ring
      _ ≤ Dcap := (hcap ab hab).trans hcapMono
  let Cost := Dtail/(L^2*P*c*U)
  have htail' (m : ℕ) (hm : 0 < m) :
      ((Gaps.filter (fun ab => m ≤ n ab)).card:ℝ) ≤ 2+Cost/(m:ℝ)^2 := by
    let Long := Gaps.filter (fun ab => m ≤ n ab)
    have hin : Long ⊆ Gaps := Finset.filter_subset _ _
    have hb ab (hab : ab∈Long) : m0*m ≤ (S ab).card :=
      (Nat.mul_le_mul_left m0 (Finset.mem_filter.mp hab).2).trans (hn ab (hin hab)).2.1
    calc
      _ ≤ bt*Btail*W₁*W₂*W₃/((L*(m:ℝ))^2*P*c*U)+2 := htail Long hin m hm hb
      _ ≤ Dtail/((L*(m:ℝ))^2*P*c*U)+2 :=
        add_le_add (div_le_div_of_nonneg_right htailMono (by positivity)) le_rfl
      _ = 2+Cost/(m:ℝ)^2 := by dsimp only [Cost]; ring
  have hsum := finite_occupied_cubic_tail_sum Gaps n (by norm_num : (0:ℝ) ≤ 2)
    (show 0 ≤ Cost by dsimp only [Cost]; positivity)
    (show 0 ≤ Dcap/(κ*L^3*P) by positivity) hc hcap' htail'
  have hmass : (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 2*(m0:ℝ)*(∑ ab∈Gaps, (n ab:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ab hab
    exact_mod_cast (hn ab hab).2.2
  calc
    _ ≤ 2*(m0:ℝ)*(∑ ab∈Gaps, (n ab:ℝ)) := hmass
    _ ≤ 2*(m0:ℝ)*(2*(Dcap/(κ*L^3*P)/c)^((3:ℝ)⁻¹)+2*Cost) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [Cost,Dcap,Dtail]; ring_nf

/-- Cubic caps and constructed improved-Third gap tails bound the total
original long-family sample mass for both triangular branches. The only
chart input is on the original finite rational-centre families. -/
theorem positive_difference_actual_fourier_charted_triangular_long_sample_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0 ≤ (S ab).card) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))) := by
  classical
  obtain ⟨ηb,ab,CUb,CLb,hηb,hηbcap,hab,hCUb,hCLb,hblock⟩ :=
    positive_difference_actual_fourier_charted_triangular_constraints hσsrc hcsrc hUsrc
  obtain ⟨ηg,ag,CUg,CLg,hηg,_hηgcap,hag,hCUg,hCLg,hgaps⟩ :=
    positive_difference_actual_fourier_charted_triangular_long_gap_packing hσsrc hcsrc hUsrc
  let CU := max CUb CUg
  let CL := max CLb CLg
  have hCU : 0 < CU := hCUb.trans_le (le_max_left _ _)
  have hCL : 0 < CL := hCLb.trans_le (le_max_left _ _)
  refine ⟨min ηb ηg,min ab ag,CU,CL,lt_min hηb hηg,
    (min_le_left _ _).trans hηbcap,lt_min hab hag,hCU,hCL,?_⟩
  intro Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Gaps Bselect
    Bmajor Cmajor S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor hS Lunit Gamma Cthird
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hunit : 0 < Lunit := div_pos (mul_pos (by norm_num) hκ) hCphys
  have hm0 : 0 < m0 := by dsimp only [m0]; omega
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  let n := fun ab => (S ab).card/m0
  have hn ab (hab : ab∈Gaps) := quotient_block_mass (S ab).card m0 hm0 (hS ab hab)
  have hfamily (G : Finset (ℝ × ℝ)) (hsub : G ⊆ Gaps) (m : ℕ) (hm : 0 < m)
      (hblocks : ∀ ab∈G, m0*m ≤ (S ab).card) :
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
        (G.card:ℝ) ≤ CUg*(Cthird+1)*E^2*M^2/
          ((Lunit*(m:ℝ))^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
        (G.card:ℝ) ≤ 4*CLg*(Cthird+1)*R^4/
          ((Lunit*(m:ℝ))^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2) := by
    exact hgaps Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs G
      (Bselect:=Bselect) Bmajor Cmajor m S Q K₀ rat vinv parity anchor Mat e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
      hη (hηsmall.trans (min_le_right _ _)) hcenterx hcentery hya hyb hreg hjets htests
      hTsrc hMtwo hsourceScale
      (fun ab hab j hj i => ⟨((hlocal ab (hsub hab) j hj i).1).trans_le (min_le_right _ _),
        ((hlocal ab (hsub hab) j hj i).2).trans_le (min_le_right _ _)⟩) hm
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hsub hab)) (fun ab hab => hwindow ab (hsub hab)) (fun ab hab => hden ab (hsub hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hsub hab)) (fun ab hab => hinv ab (hsub hab)) (fun ab hab => hchart ab (hsub hab)) (fun ab hab => horientation ab (hsub hab)) hBcut (fun ab hab => hs ab (hsub hab)) (fun ab hab => hrefSet ab (hsub hab)) (fun ab hab => hparentSet ab (hsub hab)) hsep (fun ab hab => hwideL ab (hsub hab)) (fun ab hab => hwideU ab (hsub hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hsub hab)) (fun ab hab => hgapWidth ab (hsub hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hsub hab)) (fun ab hab => hgap ab (hsub hab))
      (fun ab hab => hsourceColor ab (hsub hab)) (fun ab hab => hlevel ab (hsub hab)) (fun ab hab => hcolor ab (hsub hab)) (fun ab hab => hnear ab (hsub hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hsub hab)) (fun ab hab => hMatmap ab (hsub hab)) hMatgamma hNtwo (fun ab hab => hL ab (hsub hab)) (fun ab hab => hU ab (hsub hab)) (fun ab hab => hanchor ab (hsub hab)) (fun ab hab => hcut ab (hsub hab)) (fun ab hab => hcount ab (hsub hab)) hsize hD hΔ hBsize (fun ab hab => hBmajor ab (hsub hab)) (fun ab hab => hCmajor ab (hsub hab)) hblocks
  have hblockBound ab (hab : ab∈Gaps) :
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) →
        κ*|(Mat 1:ℝ)| *(Lunit*(n ab:ℝ))^3*N^4 ≤ 2*CUb*(Cthird+1)*E^2*M^2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) →
        κ*|(Mat 2:ℝ)| *(Lunit*(n ab:ℝ))^3*N^2 ≤ 8*CLb*(Cthird+1)*R^4) := by
    have hSlarge : 6+Ccharts ab*(105+544*Blabels ab) ≤ (S ab).card := by
      apply le_trans _ (hS ab hab)
      dsimp only [m0]
      gcongr
      exact hCmajor ab hab
      exact hBmajor ab hab
    have hh := hblock Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs
      (Bselect:=Bselect) (gapLo:=ab.1) (gapHi:=ab.2) (S ab) Q K₀
      (rat ab) (vinv ab) (parity ab) (anchor ab) Mat (e ab) (r ab) (v ab) (s ab)
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x ab)
      hη (hηsmall.trans (min_le_left _ _)) hcenterx hcentery hya hyb hreg hjets htests
      hTsrc hMtwo hsourceScale
      (fun j hj i => ⟨((hlocal ab hab j hj i).1).trans_le (min_le_left _ _),
        ((hlocal ab hab j hj i).2).trans_le (min_le_left _ _)⟩)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx ab hab) (hwindow ab hab) (hden ab hab) hlambda hUband hθ hθmax (hcurv ab hab) (hinv ab hab) (hchart ab hab) (horientation ab hab) hBcut (hs ab hab) (hrefSet ab hab) (hparentSet ab hab) hsep (hwideL ab hab) (hwideU ab hab) hUref hBselectSize hcutMargin hselectedWrap (hreferenceDen ab hab) (hgapWidth ab hab) hRQ hselectedUpper hscaleTen (hfamilyGap ab hab)
      (hsourceColor ab hab) hSlarge (hlevel ab hab) (hcolor ab hab) (hnear ab hab)
      hsmall hNR hRN hNcube hminscale hMatdet (hMatt ab hab) (hMatmap ab hab) hMatgamma
      hNtwo (hL ab hab) (hU ab hab) (hanchor ab hab) (hcut ab hab) (hcount ab hab)
      hsize hD hΔ hBsize
    obtain ⟨_S₀,_hS₀,_hmass,_hL,_hupper,_hlower,hblocks⟩ := hh
    exact hblocks Bmajor Cmajor (n ab) (hBmajor ab hab) (hCmajor ab hab)
      (hn ab hab).1 (hn ab hab).2.1
  constructor
  · intro htri hentry
    have hCmat : 0 < |(Mat 1:ℝ)| := abs_pos.mpr (by exact_mod_cast hentry)
    simpa only [one_mul] using
      original_block_mass_of_cubic_and_gap_bounds Gaps S m0
        (κ:=κ) (L:=Lunit) (P:=N^4) (c:=|(Mat 1:ℝ)|) (U:=(Uref:ℝ))
        (Bcap:=CUb) (Btail:=CUg) (ac:=2) (bt:=1)
        (W₁:=Cthird+1) (W₂:=E^2) (W₃:=M^2)
        hκ hunit (by positivity) hCmat hUp hCUb.le
        (by norm_num) (by norm_num) (by positivity) (sq_nonneg E) (sq_nonneg M)
        hm0 hS (fun ab hab => (hblockBound ab hab).1 htri)
        (fun G hsub m hm hb => by simpa only [one_mul] using
          (hfamily G hsub m hm hb).1 htri hentry)
  · intro htri hentry
    have hCmat : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hentry)
    simpa only [mul_one] using
      original_block_mass_of_cubic_and_gap_bounds Gaps S m0
        (κ:=κ) (L:=Lunit) (P:=N^2) (c:=|(Mat 2:ℝ)|) (U:=(Uref:ℝ))
        (Bcap:=CLb) (Btail:=CLg) (ac:=8) (bt:=4)
        (W₁:=Cthird+1) (W₂:=R^4) (W₃:=1)
        hκ hunit (by positivity) hCmat hUp hCLb.le
        (by norm_num) (by norm_num) (by positivity) (by positivity) (by norm_num)
        hm0 hS (fun ab hab => by simpa only [mul_one] using (hblockBound ab hab).2 htri)
        (fun G hsub m hm hb => by simpa only [mul_one] using
          (hfamily G hsub m hm hb).2 htri hentry)


example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ → xcenter∈Icc (1:ℝ) 2 → ycenter∈Icc (1:ℝ) 2 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let Hsrc := fun z : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc z.2-iteratedDeriv 2 Fsrc (z.2+η*z.1))/(σsrc*η)
    let center := (ycenter,Hsrc (ycenter,xcenter))
    let centerInv := (ycenter,(Hsrc (ycenter,xcenter))⁻¹)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab j i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), (x ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1))) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, ((rat ab) j i).den ≤ Q ∧ Q ≤ 2*((rat ab) j i).den) →
    (0 < lambda) →
    (0 ≤ Uband) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, lambda ≤ |((rat ab) j i:ℝ)| ∧ |((rat ab) j i:ℝ)| ≤ Uband) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (((rat ab) j i).den:ℤ) ∣ ((rat ab) j i).num*(vinv ab) j i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    (N^10 ≤ M^3*R^7) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((rat ab) j 0:ℝ)∈Icc ab.1 ab.2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun (ab : ℝ × ℝ) => fun j i => (⌊(((rat ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊(((rat ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ab∈Gaps, ∀ j∈(S ab), (sourceColor ab) j 0=(sourceColor ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, iteratedDeriv 2 (f i) ((x ab) j i)/2=((rat ab) j i:ℝ)) →
    let q := fun (ab : ℝ × ℝ) => fun j i => ((rat ab) j i).den
    let mu := fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round ((x ab) j i))/6
    let ell := fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round ((x ab) j i))
    let b := fun (ab : ℝ × ℝ) => fun j i => (⌊((q ab) j i:ℝ)*(ell ab) j i⌋+((parity ab) j i:ℕ) : ℤ)
    let cround := fun (ab : ℝ × ℝ) => fun j i => round (((q ab) j i:ℝ)*(ell ab) j i)
    let tau := fun (ab : ℝ × ℝ) => fun j i => (((b ab) j i:ℝ)-((q ab) j i:ℝ)*(ell ab) j i)/2
    let dual := fun (ab : ℝ × ℝ) => fun j i => -2*(mu ab) j i*(Real.sqrt (2/(3*(mu ab) j i*((q ab) j i:ℝ))))^3
    let cloud := fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-((vinv ab) j i:ℝ)*(b ab) j i/(q ab) j i),
      Int.fract (-((vinv ab) j i:ℝ)/(q ab) j i),(dual ab) j i/Real.sqrt K₀,
      (3*(dual ab) j i*(tau ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, ∀ j∈(S ab), (b ab) j 0-(cround ab) j 0=(b ab) j 1-(cround ab) j 1) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ a, |(cloud ab) j 0 a-(cloud ab) j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ ab∈Gaps, ∀ j∈(S ab), (Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3=((q ab) j 1:ℝ)/(q ab) j 0) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ((Mat 0:ℝ)*((rat ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*((rat ab) j 0:ℝ)+Mat 3)=((rat ab) j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), ∀ i, (x ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ j∈(S ab), |((anchor ab) j:ℝ)-((rat ab) j 0:ℝ)| ≤ ε) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256*(((anchor ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ab∈Gaps, ∀ j∈(S ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*((anchor ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    (∀ ab∈Gaps, m0 ≤ (S ab).card) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))) :=
  HuxleyTriangularGapScratch.positive_difference_actual_fourier_charted_triangular_long_sample_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

end HuxleyTriangularGapScratch
#print axioms HuxleyTriangularGapScratch.positive_difference_normalized_quartic_upper_reference_gap_packing
#print axioms HuxleyTriangularGapScratch.upper_reference_gap_source_scale
#print axioms HuxleyTriangularGapScratch.positive_difference_physical_upper_pair_compression
#print axioms HuxleyTriangularGapScratch.positive_difference_physical_upper_reference_gap_packing
#print axioms HuxleyTriangularGapScratch.positive_difference_normalized_quartic_lower_reference_gap_packing
#print axioms HuxleyTriangularGapScratch.positive_difference_physical_lower_pair_compression
#print axioms HuxleyTriangularGapScratch.adjacent_reference_gap_card_of_diameter
#print axioms HuxleyTriangularGapScratch.positive_difference_physical_lower_reference_gap_packing

#print axioms HuxleyTriangularGapScratch.reference_gap_count_of_closed_profile_width

#print axioms HuxleyTriangularGapScratch.positive_difference_actual_fourier_charted_triangular_long_gap_packing

#print axioms HuxleyTriangularGapScratch.positive_difference_actual_fourier_charted_triangular_long_sample_mass

#print axioms HuxleyTriangularGapScratch.original_block_mass_of_cubic_and_gap_bounds

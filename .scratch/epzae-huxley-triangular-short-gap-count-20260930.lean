import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyTriangularShortScratch

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


/-- Actual Fourier-cloud Third conditions give the triangular count for
one representative in each closed reference gap, including endpoint
coincidences. No Third-condition certificate is supplied. -/
theorem positive_difference_actual_fourier_triangular_closed_gap_count
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → Fin 2 → ℚ) (vinv : ℝ × ℝ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → Fin 2 → Fin 2) (x : ℝ × ℝ → Fin 2 → ℝ)
    {σ δ T M N R U : ℝ} (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
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
    (∀ ab∈Gaps, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < U) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (N^2 ≤ M*R) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (∀ ab∈Gaps, ∀ i, x ab i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ i, (rat ab i).den ≤ Q ∧ Q ≤ 2*(rat ab i).den) →
    (∀ ab∈Gaps, ∀ i, ((rat ab i).den:ℤ) ∣ (rat ab i).num*vinv ab i-1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (x ab i)/2=(rat ab i:ℝ)) →
    let q := fun ab i => (rat ab i).den
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (x ab i))/6
    let ell := fun ab i => deriv (f i) (round (x ab i))
    let b := fun ab i => (⌊(q ab i:ℝ)*ell ab i⌋+(parity ab i:ℕ) : ℤ)
    let cround := fun ab i => round ((q ab i:ℝ)*ell ab i)
    let tau := fun ab i => ((b ab i:ℝ)-(q ab i:ℝ)*ell ab i)/2
    let dual := fun ab i => -2*mu ab i*(Real.sqrt (2/(3*mu ab i*(q ab i:ℝ))))^3
    let cloud := fun ab i => (![Int.fract (-(vinv ab i:ℝ)*b ab i/q ab i),
      Int.fract (-(vinv ab i:ℝ)/q ab i),dual ab i/Real.sqrt K₀,
      (3*dual ab i*tau ab i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, b ab 0-cround ab 0=b ab 1-cround ab 1) →
    (∀ ab∈Gaps, ∀ a, |cloud ab 0 a-cloud ab 1 a| ≤ 2*radius a) →
    (∀ ab∈Gaps, (Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3=(q ab 1:ℝ)/q ab 0) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*(rat ab 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3)=(rat ab 1:ℝ)) →
    (∀ ab∈Gaps, (rat ab 0:ℝ)∈Icc ab.1 ab.2) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (Gaps.card:ℝ) ≤ Cupper*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *U)+2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (Gaps.card:ℝ) ≤ 4*Clower*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *U)+2) := by
  classical
  obtain ⟨aU,CU,haU,hCU,hupper⟩ :=
    positive_difference_physical_upper_reference_gap_packing hσsrc hcsrc hUsrc
  obtain ⟨η₀,aL,CL,hη₀,hηcap,haL,hCL,hlower⟩ :=
    positive_difference_physical_lower_reference_gap_packing hσsrc hcsrc hUsrc
  refine ⟨η₀,min aU aL,CU,CL,hη₀,hηcap,lt_min haU haL,hCU,hCL,?_⟩
  intro Fsrc η xcenter ycenter ya yb Tsrc E Refs Gaps Mat Q K₀ inst rat vinv parity x
    σ δ T M N R U A W
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F Hsrc center centerInv hlocal
    hσ hδ hF hT hM hN hR hU hQ hscale hmesh hNscale hA hW hsep hgap hx hden hinv
    f hlevel q mu ell b cround tau dual cloud radius hcolor hnear hMatt hMatmap
    hsourceGap κ Cphys c J B
  have hηmax : η ≤ 1/8 := hηsmall.trans hηcap
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hthird ab (hab : ab∈Gaps) :
      |mu ab 1*((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+Mat 3)^3/mu ab 0-1| ≤ B*R^2/N^2 := by
    obtain ⟨_v,_hv,hh,_hrest⟩ := physicalModelPhase_actual_fourier_conditions
      Q K₀ (rat ab) (vinv ab) (parity ab)
      hσ hδ hF hT hM hN hRp hQ hscale hmesh hA hW
      (hx ab hab) (hden ab hab) (hinv ab hab) (hlevel ab hab)
      (hcolor ab hab) (hnear ab hab)
    rw [hlevel ab hab 0,hMatt ab hab]
    have he : mu ab 1*((q ab 1:ℝ)/q ab 0)^3/mu ab 0-1=
        mu ab 1*(q ab 1:ℝ)^3/(mu ab 0*(q ab 0:ℝ)^3)-1 := by
      rw [div_pow]
      ring_nf
    rw [he]
    exact hh
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
  have hphysical ab (hab : ab∈Gaps) i :
      (A i:ℝ)+x ab i∈Icc M (2*M) :=
    ⟨by linarith only [hA i,(hx ab hab i).1],
     by linarith only [hW i,(hx ab hab i).2]⟩
  let xa := fun ab => (A 0:ℝ)+x ab 0
  let xb := fun ab => (A 1:ℝ)+x ab 1
  have hua ab : iteratedDeriv 2 (Src ya) (xa ab)/2=iteratedDeriv 2 (f 0) (x ab 0)/2 :=
    (congrArg (fun t : ℝ => t/2) (hjet 0 2 (x ab 0))).symm
  have hub ab : iteratedDeriv 2 (Src yb) (xb ab)/2=iteratedDeriv 2 (f 1) (x ab 1)/2 :=
    (congrArg (fun t : ℝ => t/2) (hjet 1 2 (x ab 1))).symm
  have hcurvNe ab (hab : ab∈Gaps) i : iteratedDeriv 2 (f i) (x ab i)/2 ≠ 0 := by
    rw [hjet]
    have hh := (positive_difference_half_curvature_source_bounds Fsrc
      hσsrc hcsrc hUsrc hη hηmax hTsrc hM (hyp i)
      (hphysical ab hab i) hreg hjets htests).1
    exact abs_pos.mp (lt_of_lt_of_le (by positivity) hh)
  have hmu ab i :
      iteratedDeriv 3 (Src (yp i)) (round ((A i:ℝ)+x ab i))/6=mu ab i :=
    (congrArg (fun t : ℝ => t/6) (hrounded i (x ab i))).symm
  constructor
  · intro htri hentry
    have hb : (Mat 1:ℝ) ≠ 0 := by exact_mod_cast hentry
    have hmap ab (hab : ab∈Gaps) :
        iteratedDeriv 2 (Src yb) (xb ab)/2=
          iteratedDeriv 2 (Src ya) (xa ab)/2+(Mat 1:ℝ) := by
      rw [hua,hub,hlevel ab hab 0,hlevel ab hab 1]
      simpa only [htri.1,htri.2.1,htri.2.2,Int.cast_one,Int.cast_zero,
        zero_mul,one_mul,zero_add,div_one] using (hMatmap ab hab).symm
    have hp := hupper Fsrc η xcenter ycenter ya yb (Mat 1) (B*R^2/N^2)
      Tsrc M R U Refs Gaps xa xb
      hη hηmax hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hRp hU hb
      (by positivity)
      (fun ab hab => ⟨hphysical ab hab 0,hphysical ab hab 1⟩) hsep hgap
      (by
        intro ab hab
        change iteratedDeriv 2 (Src ya) (xa ab)/2∈Icc ab.1 ab.2
        rw [hua,hlevel ab hab 0]
        exact hsourceGap ab hab)
      hmap
      (by
        intro ab hab
        change |(iteratedDeriv 3 (Src (yp 1)) (round ((A 1:ℝ)+x ab 1))/6)/
          (iteratedDeriv 3 (Src (yp 0)) (round ((A 0:ℝ)+x ab 0))/6)-1| ≤ _
        rw [hmu,hmu]
        simpa only [htri.2.1,htri.2.2,Int.cast_zero,Int.cast_one,zero_mul,
          zero_add,one_pow,mul_one] using hthird ab hab)
      (by
        intro ab hab
        change ‖((ya,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)):ℝ × ℝ)-center‖ < aU ∧
          ‖((yb,(2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+
            2*M^2*(Mat 1:ℝ)/Tsrc):ℝ × ℝ)-center‖ < aU
        have he : (2*M^2/Tsrc)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+2*M^2*(Mat 1:ℝ)/Tsrc=
            (2*M^2/Tsrc)*(iteratedDeriv 2 (Src yb) (xb ab)/2) := by
          rw [hmap ab hab]
          ring
        rw [he,hua,hub,hlevel ab hab 0,hlevel ab hab 1]
        exact ⟨((hlocal ab hab 0).1).trans_le (min_le_left _ _),
          ((hlocal ab hab 1).1).trans_le (min_le_left _ _)⟩)
    have hh := upper_reference_gap_source_scale (L:=1) hCU.le hB hTsrc hM hN hR
      (by norm_num) hU hb (by simpa only [one_mul] using hNscale) hscale hsourceScale
    have hh' : CU*(B*R^2/N^2+1/M)*Tsrc^2*R^2/(M^4*|(Mat 1:ℝ)| *U) ≤
        CU*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *U) := by
      simpa only [one_pow,one_mul] using hh
    exact hp.trans (add_le_add hh' le_rfl)
  · intro htri hentry
    have hc : (Mat 2:ℝ) ≠ 0 := by exact_mod_cast hentry
    have hmap ab (hab : ab∈Gaps) :
        iteratedDeriv 2 (Src yb) (xb ab)/2=
          (iteratedDeriv 2 (Src ya) (xa ab)/2)/
            ((Mat 2:ℝ)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+1) := by
      rw [hua,hub,hlevel ab hab 0,hlevel ab hab 1]
      simpa only [htri.1,htri.2.1,htri.2.2,Int.cast_one,Int.cast_zero,
        one_mul,add_zero] using (hMatmap ab hab).symm
    have hinvMap ab (hab : ab∈Gaps) :
        (iteratedDeriv 2 (Src yb) (xb ab)/2)⁻¹=
          (iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹+(Mat 2:ℝ) := by
      have hn : iteratedDeriv 2 (Src ya) (xa ab)/2 ≠ 0 := by
        rw [hua]
        exact hcurvNe ab hab 0
      rw [hmap ab hab,inv_div,add_div,mul_div_cancel_right₀ _ hn,one_div,add_comm]
    have hp := hlower Fsrc η xcenter ycenter ya yb (Mat 2) (B*R^2/N^2)
      Tsrc M R U Refs Gaps xa xb
      hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hRp hU hc
      (by positivity)
      (fun ab hab => ⟨hphysical ab hab 0,hphysical ab hab 1⟩) hsep hgap
      (by
        intro ab hab
        change iteratedDeriv 2 (Src ya) (xa ab)/2∈Icc ab.1 ab.2
        rw [hua,hlevel ab hab 0]
        exact hsourceGap ab hab)
      hmap
      (by
        intro ab hab
        change |(iteratedDeriv 3 (Src (yp 1)) (round ((A 1:ℝ)+x ab 1))/6)/
          (iteratedDeriv 3 (Src (yp 0)) (round ((A 0:ℝ)+x ab 0))/6)*
          ((Mat 2:ℝ)*(iteratedDeriv 2 (Src ya) (xa ab)/2)+1)^3-1| ≤ _
        rw [hmu,hmu,hua]
        have he : mu ab 1/mu ab 0*
            ((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+1)^3=
            mu ab 1*((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x ab 0)/2)+1)^3/mu ab 0 := by ring
        rw [he]
        simpa only [htri.2.2,Int.cast_one] using hthird ab hab)
      (by
        intro ab hab
        change ‖((ya,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹):ℝ × ℝ)-centerInv‖ < aL ∧
          ‖((yb,(Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹+
            Tsrc*(Mat 2:ℝ)/(2*M^2)):ℝ × ℝ)-centerInv‖ < aL
        have he : (Tsrc/(2*M^2))*(iteratedDeriv 2 (Src ya) (xa ab)/2)⁻¹+
            Tsrc*(Mat 2:ℝ)/(2*M^2)=
            (Tsrc/(2*M^2))*(iteratedDeriv 2 (Src yb) (xb ab)/2)⁻¹ := by
          rw [hinvMap ab hab]
          ring
        rw [he,hua,hub,hlevel ab hab 0,hlevel ab hab 1]
        exact ⟨((hlocal ab hab 0).2).trans_le (min_le_right _ _),
          ((hlocal ab hab 1).2).trans_le (min_le_right _ _)⟩)
    have hInv : 1/M ≤ R^2/N^2 := by
      apply (div_le_div_iff₀ hM (sq_pos_of_pos hN)).mpr
      have hRR : R ≤ R^2 := by nlinarith only [hR]
      nlinarith only [hNscale,mul_le_mul_of_nonneg_left hRR hM.le]
    have herror : B*R^2/N^2+1/M ≤ (B+1)*R^2/N^2 :=
      (add_le_add le_rfl hInv).trans_eq (by ring)
    apply hp.trans
    calc
      _ ≤ 4*CL*((B+1)*R^2/N^2)*R^2/(|(Mat 2:ℝ)| *U)+2 := by
        apply add_le_add _ le_rfl
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left herror (by positivity)) (sq_nonneg R)
      _ = _ := by ring_nf

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧
    ∀ (Fsrc : ℝ → ℝ) (η xcenter ycenter ya yb Tsrc E : ℝ)
    (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) (Mat : Fin 4 → ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → Fin 2 → ℚ) (vinv : ℝ × ℝ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → Fin 2 → Fin 2) (x : ℝ × ℝ → Fin 2 → ℝ)
    {σ δ T M N R U : ℝ} (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
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
    (∀ ab∈Gaps, ∀ i,
      ‖((yp i,(2*M^2/Tsrc)*(rat ab i:ℝ)):ℝ × ℝ)-center‖ < a ∧
      ‖((yp i,(Tsrc/(2*M^2))*(rat ab i:ℝ)⁻¹):ℝ × ℝ)-centerInv‖ < a) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ) →
    (0 < T) →
    (0 < M) →
    (0 < N) →
    (1 ≤ R) →
    (0 < U) →
    (0 < Q) →
    (T*N*R^2=M^3) →
    ((Q:ℝ)*N ≤ (K₀:ℝ)*R^2) →
    (N^2 ≤ M*R) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ a∈Refs, ∀ b∈Refs, a≠b → U/(4*R^2) ≤ |a-b|) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (∀ ab∈Gaps, ∀ i, x ab i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ab∈Gaps, ∀ i, (rat ab i).den ≤ Q ∧ Q ≤ 2*(rat ab i).den) →
    (∀ ab∈Gaps, ∀ i, ((rat ab i).den:ℤ) ∣ (rat ab i).num*vinv ab i-1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ ab∈Gaps, ∀ i, iteratedDeriv 2 (f i) (x ab i)/2=(rat ab i:ℝ)) →
    let q := fun ab i => (rat ab i).den
    let mu := fun ab i => iteratedDeriv 3 (f i) (round (x ab i))/6
    let ell := fun ab i => deriv (f i) (round (x ab i))
    let b := fun ab i => (⌊(q ab i:ℝ)*ell ab i⌋+(parity ab i:ℕ) : ℤ)
    let cround := fun ab i => round ((q ab i:ℝ)*ell ab i)
    let tau := fun ab i => ((b ab i:ℝ)-(q ab i:ℝ)*ell ab i)/2
    let dual := fun ab i => -2*mu ab i*(Real.sqrt (2/(3*mu ab i*(q ab i:ℝ))))^3
    let cloud := fun ab i => (![Int.fract (-(vinv ab i:ℝ)*b ab i/q ab i),
      Int.fract (-(vinv ab i:ℝ)/q ab i),dual ab i/Real.sqrt K₀,
      (3*dual ab i*tau ab i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ab∈Gaps, b ab 0-cround ab 0=b ab 1-cround ab 1) →
    (∀ ab∈Gaps, ∀ a, |cloud ab 0 a-cloud ab 1 a| ≤ 2*radius a) →
    (∀ ab∈Gaps, (Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3=(q ab 1:ℝ)/q ab 0) →
    (∀ ab∈Gaps, ((Mat 0:ℝ)*(rat ab 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat ab 0:ℝ)+Mat 3)=(rat ab 1:ℝ)) →
    (∀ ab∈Gaps, (rat ab 0:ℝ)∈Icc ab.1 ab.2) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (Gaps.card:ℝ) ≤ Cupper*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *U)+2) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (Gaps.card:ℝ) ≤ 4*Clower*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *U)+2) :=
  HuxleyTriangularShortScratch.positive_difference_actual_fourier_triangular_closed_gap_count (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

/-- Both triangular counts include ALL actual Fourier families.
Long families use quartic caps and occupied tails; short families use
actual Fourier representatives in closed gaps, including endpoints. -/
theorem positive_difference_actual_fourier_charted_triangular_all_sample_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
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
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(Dupper*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2)) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(4*Dlower*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2)) := by
  classical
  obtain ⟨ηl,al,CU,CL,hηl,hηlcap,hal,hCU,hCL,hlongFn⟩ :=
    positive_difference_actual_fourier_charted_triangular_long_sample_mass hσsrc hcsrc hUsrc
  obtain ⟨ηs,asrc,DU,DL,hηs,_hηscap,hasrc,hDU,hDL,hshortFn⟩ :=
    positive_difference_actual_fourier_triangular_closed_gap_count hσsrc hcsrc hUsrc
  refine ⟨min ηl ηs,min al asrc,CU,CL,DU,DL,lt_min hηl hηs,
    (min_le_left _ _).trans hηlcap,lt_min hal hasrc,hCU,hCL,hDU,hDL,?_⟩
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
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird
  let Long := Gaps.filter (fun ab => m0 ≤ (S ab).card)
  let Short := Gaps.filter (fun ab => (S ab).Nonempty ∧ (S ab).card < m0)
  have hinLong : Long ⊆ Gaps := Finset.filter_subset _ _
  have hinShort : Short ⊆ Gaps := Finset.filter_subset _ _
  have hlong :
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Long, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          CU*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Long, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*CL*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*CL*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))) := by
    exact hlongFn Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Long
      (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
      (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
      hη (hηsmall.trans (min_le_left _ _)) hcenterx hcentery hya hyb hreg hjets htests
      hTsrc hMtwo hsourceScale
      (fun ab hab j hj i => ⟨((hlocal ab (hinLong hab) j hj i).1).trans_le (min_le_left _ _),
        ((hlocal ab (hinLong hab) j hj i).2).trans_le (min_le_left _ _)⟩)
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (fun ab hab => hx ab (hinLong hab)) (fun ab hab => hwindow ab (hinLong hab)) (fun ab hab => hden ab (hinLong hab)) hlambda hUband hθ hθmax (fun ab hab => hcurv ab (hinLong hab)) (fun ab hab => hinv ab (hinLong hab)) (fun ab hab => hchart ab (hinLong hab)) (fun ab hab => horientation ab (hinLong hab)) hBcut (fun ab hab => hs ab (hinLong hab)) (fun ab hab => hrefSet ab (hinLong hab)) (fun ab hab => hparentSet ab (hinLong hab)) hsep (fun ab hab => hwideL ab (hinLong hab)) (fun ab hab => hwideU ab (hinLong hab)) hUref hBselectSize hcutMargin hselectedWrap (fun ab hab => hreferenceDen ab (hinLong hab)) (fun ab hab => hgapWidth ab (hinLong hab)) hRQ hselectedUpper hscaleTen (fun ab hab => hfamilyGap ab (hinLong hab)) (fun ab hab => hgap ab (hinLong hab))
      (fun ab hab => hsourceColor ab (hinLong hab)) (fun ab hab => hlevel ab (hinLong hab)) (fun ab hab => hcolor ab (hinLong hab)) (fun ab hab => hnear ab (hinLong hab)) hsmall hNR hRN hNcube hminscale hMatdet (fun ab hab => hMatt ab (hinLong hab)) (fun ab hab => hMatmap ab (hinLong hab)) hMatgamma hNtwo (fun ab hab => hL ab (hinLong hab)) (fun ab hab => hU ab (hinLong hab)) (fun ab hab => hanchor ab (hinLong hab)) (fun ab hab => hcut ab (hinLong hab)) (fun ab hab => hcount ab (hinLong hab)) hsize hD hΔ hBsize (fun ab hab => hBmajor ab (hinLong hab)) (fun ab hab => hCmajor ab (hinLong hab))
      (fun _ hab => (Finset.mem_filter.mp hab).2)
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  have hNscale : N^2 ≤ M*R := by
    apply (mul_le_mul_iff_of_pos_right hN).mp
    calc
      _ = N^3 := by ring
      _ ≤ M*R^2 := hNcube
      _ ≤ (M*R)*N := by
        have hh := mul_le_mul_of_nonneg_left hRN (mul_nonneg hM.le (zero_lt_one.trans_le hR).le)
        nlinarith only [hh]
  have hchoose ab (hab : ab∈Short) : ∃ j, j∈S ab := (Finset.mem_filter.mp hab).2.1
  choose! j hj using hchoose
  have hshortcount :
      ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
        (Short.card:ℝ) ≤ DU*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2) ∧
      ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
        (Short.card:ℝ) ≤ 4*DL*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2) := by
    exact hshortFn Fsrc η xcenter ycenter ya yb Tsrc E Refs Short Mat Q K₀
      (fun ab => rat ab (j ab)) (fun ab => vinv ab (j ab))
      (fun ab => parity ab (j ab)) (fun ab => x ab (j ab))
      (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (U:=(Uref:ℝ)) A
      hη (hηsmall.trans (min_le_right _ _)) hcenterx hcentery hya hyb hreg hjets htests
      hTsrc hMtwo hsourceScale
      (fun ab hab i => ⟨((hlocal ab (hinShort hab) _ (hj ab hab) i).1).trans_le (min_le_right _ _),
        ((hlocal ab (hinShort hab) _ (hj ab hab) i).2).trans_le (min_le_right _ _)⟩)
      hσ hδ hF₃ hT hM hN hR hUp hQ hscale hmesh hNscale hA hW
      (by
        intro a ha b hb hne
        calc
          (Uref:ℝ)/(4*R^2)=((Uref:ℝ)/R^2)/4 := by ring
          _ ≤ |a-b| := (hsep a ha b hb hne).le)
      (fun ab hab => hgap ab (hinShort hab))
      (fun ab hab => hx ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hden ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hinv ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hlevel ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hcolor ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hnear ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatt ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hMatmap ab (hinShort hab) _ (hj ab hab))
      (fun ab hab => hfamilyGap ab (hinShort hab) _ (hj ab hab))
  have hshortmass : (∑ ab∈Short, ((S ab).card:ℝ)) ≤ (m0:ℝ)*(Short.card:ℝ) := by
    calc
      _ ≤ ∑ _ab∈Short, (m0:ℝ) := by
        apply Finset.sum_le_sum
        intro ab hab
        exact_mod_cast (Finset.mem_filter.mp hab).2.2.le
      _ = _ := by simp [mul_comm]
  have hpartition : (∑ ab∈Gaps, ((S ab).card:ℝ)) =
      (∑ ab∈Long, ((S ab).card:ℝ))+(∑ ab∈Short, ((S ab).card:ℝ)) := by
    simp only [Long,Short,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ab _
    by_cases hh : m0 ≤ (S ab).card
    · simp [hh,not_lt.mpr hh]
    · have hlt : (S ab).card < m0 := lt_of_not_ge hh
      by_cases he : (S ab).Nonempty
      · simp [hh,he,hlt]
      · have hz : (S ab).card=0 := by simp [Finset.not_nonempty_iff_eq_empty.mp he]
        simp [he,hz]
  constructor
  · intro htri hentry
    rw [hpartition]
    exact add_le_add (hlong.1 htri hentry)
      (hshortmass.trans (mul_le_mul_of_nonneg_left (hshortcount.1 htri hentry) (Nat.cast_nonneg _)))
  · intro htri hentry
    rw [hpartition]
    exact add_le_add (hlong.2 htri hentry)
      (hshortmass.trans (mul_le_mul_of_nonneg_left (hshortcount.2 htri hentry) (Nat.cast_nonneg _)))

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
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
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(Dupper*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2)) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(4*Dlower*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2)) :=
  HuxleyTriangularShortScratch.positive_difference_actual_fourier_charted_triangular_all_sample_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

/-- A finite, source-uniform coloring constructs BOTH ordinary and
reciprocal source charts around actual source points. The same coloring
carries its explicit twelfth-moment loss. -/
theorem positive_difference_source_chart_twelfth_partition
    {ι : Type*} (S : Finset ι) (F : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) {σ c U η T M a : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hT : 0 < T) (hM : 0 < M) (ha : 0 < a)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 F p.2-iteratedDeriv 2 F (p.2+η*p.1))/(σ*η)
    let u := fun i => (2*M^2/T)*(rat i:ℝ)
    let w := fun i => (T/(2*M^2))*(rat i:ℝ)⁻¹
    let color := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let Cap := (4/a+3)*((6*U/σ)/a+3)*((4*σ/c)/a+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ k∈S.image color, ∃ iref∈S, color iref=k ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ i∈S, color i=k →
        ‖((y i,u i):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y i,w i):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    ∀ coeff : ι → ℂ, ‖∑ i∈S,coeff i‖^12 ≤
      Cap^11*∑ k∈S.image color, ‖∑ i∈S.filter (fun i => color i=k),coeff i‖^12 := by
  classical
  intro f hlevel Hsrc u w color Cap
  have hsp : 0 < 2*M^2/T := by positivity
  have hsip : 0 < T/(2*M^2) := by positivity
  have hbounds i (hi : i∈S) :
      c*T/(4*σ*M^2) ≤ |(rat i:ℝ)| ∧ |(rat i:ℝ)| ≤ (3*U/σ)*T/(2*M^2) := by
    rw [←hlevel i hi]
    exact positive_difference_half_curvature_source_bounds F hσ hc hU hη hηmax hT hM
      (hy i hi) (hz i hi) hf hbound htests
  have hu i (hi : i∈S) : |u i| ≤ 3*U/σ := by
    dsimp only [u]
    rw [abs_mul,abs_of_pos hsp]
    calc
      _ ≤ (2*M^2/T)*((3*U/σ)*T/(2*M^2)) :=
        mul_le_mul_of_nonneg_left (hbounds i hi).2 hsp.le
      _ = _ := by field_simp
  have hw i (hi : i∈S) : |w i| ≤ 2*σ/c := by
    have hp : 0 < |(rat i:ℝ)| :=
      (show 0 < c*T/(4*σ*M^2) by positivity).trans_le (hbounds i hi).1
    dsimp only [w]
    rw [abs_mul,abs_inv,abs_of_pos hsip,←div_eq_mul_inv]
    apply (div_le_iff₀ hp).mpr
    calc
      _ = (2*σ/c)*(c*T/(4*σ*M^2)) := by field_simp; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbounds i hi).1 (by positivity)
  have hsource i (hi : i∈S) : Hsrc (y i,z i/M)=u i := by
    have hd := positive_difference_physical_iteratedDeriv F (T:=T) (σ:=σ) hM
      (hM.trans_le (hz i hi).1) (mul_nonneg hη.le (by linarith only [(hy i hi).1])) hf 2
    have hh := hlevel i hi
    change iteratedDeriv 2 (fun t => T*(F (t/M)-F (t/M+η*y i))/(σ*η)) (z i)/2=(rat i:ℝ) at hh
    rw [hd] at hh
    dsimp only [Hsrc,u]
    rw [←hh]
    field_simp
  have hinv i : (u i)⁻¹=w i := by
    dsimp only [u,w]
    rw [mul_inv_rev,inv_div]
    ring
  have h₁ : ((S.image (fun i => (color i).1)).card:ℝ) ≤ 4/a+3 := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=2) S y
      (by norm_num) ha (by norm_num)
      (by intro i hi; rw [abs_of_nonneg (by linarith only [(hy i hi).1])]; simpa using (hy i hi).2)
    simpa only [mul_one,show (2:ℝ)*2=4 by norm_num] using hh
  have h₂ : ((S.image (fun i => (color i).2.1)).card:ℝ) ≤ (6*U/σ)/a+3 := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=3*U/σ) S u
      (by norm_num) ha (by positivity) (by intro i hi; simpa only [mul_one] using hu i hi)
    simp only [mul_one] at hh
    convert hh using 1
    ring
  have h₃ : ((S.image (fun i => (color i).2.2)).card:ℝ) ≤ (4*σ/c)/a+3 := by
    have hh := scaled_floor_image_card (Q:=1) (δ:=a) (R:=2*σ/c) S w
      (by norm_num) ha (by positivity) (by intro i hi; simpa only [mul_one] using hw i hi)
    simp only [mul_one] at hh
    convert hh using 1
    ring
  have hcard : ((S.image color).card:ℝ) ≤ Cap := by
    have hsub : S.image color ⊆
        (S.image (fun i => (color i).1)) ×ˢ
          ((S.image (fun i => (color i).2.1)) ×ˢ (S.image (fun i => (color i).2.2))) := by
      intro k hk
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,
        Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,Finset.mem_image_of_mem _ hi⟩⟩
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product,Finset.card_product] at hh
    have hh' : ((S.image color).card:ℝ) ≤
        ((S.image (fun i => (color i).1)).card:ℝ)*
          (((S.image (fun i => (color i).2.1)).card:ℝ)*
            ((S.image (fun i => (color i).2.2)).card:ℝ)) := by exact_mod_cast hh
    apply hh'.trans
    have hm := mul_le_mul h₁ (mul_le_mul h₂ h₃ (by positivity) (by positivity))
      (by positivity) (by positivity)
    simpa only [Cap,mul_assoc] using hm
  have hsame {b d : ℝ} (he : ⌊b/a⌋=⌊d/a⌋) : |b-d| < a := by
    have hh := Int.abs_sub_lt_one_of_floor_eq_floor he
    rw [←sub_div,abs_div,abs_of_pos ha] at hh
    exact (div_lt_iff₀ ha).mp hh |>.trans_eq (one_mul a)
  refine ⟨hcard,?_,?_⟩
  · intro k hk
    obtain ⟨iref,hiref,he⟩ := Finset.mem_image.mp hk
    refine ⟨iref,hiref,he,?_,hy iref hiref,?_⟩
    · exact ⟨(le_div_iff₀ hM).mpr (by simpa using (hz iref hiref).1),
        (div_le_iff₀ hM).mpr (by simpa [mul_comm] using (hz iref hiref).2)⟩
    · intro i _hi hci
      have heq : color i=color iref := hci.trans he.symm
      have hdy := hsame (congrArg Prod.fst heq)
      have hdu := hsame (congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) heq)
      have hdw := hsame (congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) heq)
      change max |y i-y iref| |u i-Hsrc (y iref,z iref/M)| < a ∧
        max |y i-y iref| |w i-(Hsrc (y iref,z iref/M))⁻¹| < a
      rw [hsource iref hiref,hinv]
      exact ⟨max_lt_iff.mpr ⟨hdy,hdu⟩,max_lt_iff.mpr ⟨hdy,hdw⟩⟩
  · intro coeff
    let Keys := S.image color
    let V := fun k => S.filter (fun i => color i=k)
    let g := fun k => ∑ i∈V k,coeff i
    have he : (∑ k∈Keys,g k)=∑ i∈S,coeff i :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem color hi) coeff
    have hnorm : ‖∑ i∈S,coeff i‖ ≤ ∑ k∈Keys,‖g k‖ := by
      rw [←he]
      exact norm_sum_le _ _
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 12
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Keys
      (f:=fun k => ‖g k‖) (p:=(12:ℝ)) (by norm_num) (fun _ _ => norm_nonneg _)
    have hh : (∑ k∈Keys,‖g k‖)^12 ≤ (Keys.card:ℝ)^11*∑ k∈Keys,‖g k‖^12 := by
      simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
    exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Keys.card) hcard 11)
      (Finset.sum_nonneg (fun _ _ => by positivity)))


/-- An actual finite source color constructs the common ordinary and
reciprocal chart and feeds the BOTH-branch all-family triangular mass
theorem. No chart centre or chart-neighborhood certificate is supplied. -/
theorem positive_difference_actual_fourier_charted_triangular_colored_sample_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ) (chartKey : ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ab j i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ab j i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹)/a⌋)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i, chartColor ab j i=chartKey) →
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
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(Dupper*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2)) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(4*Dlower*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2)) := by
  classical
  obtain ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hmassFn⟩ :=
    positive_difference_actual_fourier_charted_triangular_all_sample_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro Fsrc η ya yb Tsrc E chartKey Uref Refs Gaps Bselect
    Bmajor Cmajor S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    yp F chartColor hchartColor
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird
  let Src := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
  have hsource i : f i=fun z => Src (yp i) ((A i:ℝ)+z) := by
    funext z
    dsimp only [f,heathBrownPhysicalPhase,F,Src]
    field_simp
  have hjet i k t : iteratedDeriv k (f i) t=
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  let Hsrc := fun p : ℝ × ℝ =>
    (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
  let Points : Finset ((ℝ × ℝ) × (ℕ × Fin 2)) :=
    Gaps.biUnion (fun ab => ((S ab) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun p => (ab,p)))
  let py := fun p : (ℝ × ℝ) × (ℕ × Fin 2) => yp p.2.2
  let pz := fun p : (ℝ × ℝ) × (ℕ × Fin 2) => (A p.2.2:ℝ)+x p.1 p.2.1 p.2.2
  let pr := fun p : (ℝ × ℝ) × (ℕ × Fin 2) => rat p.1 p.2.1 p.2.2
  let pc := fun p : (ℝ × ℝ) × (ℕ × Fin 2) => chartColor p.1 p.2.1 p.2.2
  have hmem ab (hab : ab∈Gaps) j (hj : j∈S ab) i : (ab,(j,i))∈Points :=
    Finset.mem_biUnion.mpr ⟨ab,hab,Finset.mem_image_of_mem _
      (Finset.mem_product.mpr ⟨hj,Finset.mem_univ i⟩)⟩
  have hmem' p (hp : p∈Points) : p.1∈Gaps ∧ p.2.1∈S p.1 := by
    obtain ⟨ab,hab,hmem⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨⟨j,i⟩,hji,rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨hab,(Finset.mem_product.mp hji).1⟩
  have hpy p : py p∈Icc (1:ℝ) 2 := by
    have hyp i : yp i∈Icc (1:ℝ) 2 := by fin_cases i <;> assumption
    exact hyp p.2.2
  have hpz p (hp : p∈Points) : pz p∈Icc M (2*M) := by
    have hm := hmem' p hp
    have hh := hx p.1 hm.1 p.2.1 hm.2 p.2.2
    dsimp only [pz]
    exact ⟨by linarith only [hA p.2.2,hh.1],by linarith only [hW p.2.2,hh.2]⟩
  have hlevels p (hp : p∈Points) :
      iteratedDeriv 2 (Src (py p)) (pz p)/2=(pr p:ℝ) := by
    have hm := hmem' p hp
    change iteratedDeriv 2 (Src (yp p.2.2)) ((A p.2.2:ℝ)+x p.1 p.2.1 p.2.2)/2=
      (rat p.1 p.2.1 p.2.2:ℝ)
    rw [←hjet]
    exact hlevel p.1 hm.1 p.2.1 hm.2 p.2.2
  have hcolors p (hp : p∈Points) : pc p=chartKey := by
    have hm := hmem' p hp
    exact hchartColor p.1 hm.1 p.2.1 hm.2 p.2.2
  have hcentres : ∃ xcenter∈Icc (1:ℝ) 2, ∃ ycenter∈Icc (1:ℝ) 2,
      ∀ ab∈Gaps, ∀ j∈S ab, ∀ i,
        ‖((yp i,(2*M^2/Tsrc)*(rat ab j i:ℝ)):ℝ × ℝ)-
          (ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((yp i,(Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹):ℝ × ℝ)-
          (ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a := by
    by_cases hne : Points.Nonempty
    · obtain ⟨p,hp⟩ := hne
      obtain ⟨_hCap,hcenters,_hMoment⟩ := positive_difference_source_chart_twelfth_partition
        Points Fsrc py pz pr hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap)
        hTsrc hM ha (fun p _ => hpy p) hpz hreg hjets htests hlevels
      have hkey : chartKey∈Points.image pc := Finset.mem_image.mpr ⟨p,hp,hcolors p hp⟩
      obtain ⟨iref,_hiref,_hrefKey,hxc,hyc,hwithin⟩ := hcenters chartKey hkey
      refine ⟨pz iref/M,hxc,py iref,hyc,?_⟩
      intro ab hab j hj i
      exact hwithin (ab,(j,i)) (hmem ab hab j hj i) (hcolors _ (hmem ab hab j hj i))
    · refine ⟨1,by norm_num,1,by norm_num,?_⟩
      intro ab hab j hj i
      exact False.elim (hne ⟨(ab,(j,i)),hmem ab hab j hj i⟩)
  obtain ⟨xcenter,hcenterx,ycenter,hcentery,hlocal⟩ := hcentres
  exact hmassFn Fsrc η xcenter ycenter ya yb Tsrc E Uref Refs Gaps
    (Bselect:=Bselect) Bmajor Cmajor S Q K₀ rat vinv parity anchor Mat e r v s
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut)
    (lambda:=lambda) (Uband:=Uband) (θ:=θ) A (W:=W) (x:=x)
    hη hηsmall hcenterx hcentery hya hyb hreg hjets htests hTsrc hMtwo hsourceScale hlocal
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hgap
    hsourceColor hlevel hcolor hnear hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hBmajor hCmajor

example
    {ι : Type*} (S : Finset ι) (F : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) {σ c U η T M a : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hT : 0 < T) (hM : 0 < M) (ha : 0 < a)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 F p.2-iteratedDeriv 2 F (p.2+η*p.1))/(σ*η)
    let u := fun i => (2*M^2/T)*(rat i:ℝ)
    let w := fun i => (T/(2*M^2))*(rat i:ℝ)⁻¹
    let color := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let Cap := (4/a+3)*((6*U/σ)/a+3)*((4*σ/c)/a+3)
    ((S.image color).card:ℝ) ≤ Cap ∧
    (∀ k∈S.image color, ∃ iref∈S, color iref=k ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ i∈S, color i=k →
        ‖((y i,u i):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y i,w i):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    ∀ coeff : ι → ℂ, ‖∑ i∈S,coeff i‖^12 ≤
      Cap^11*∑ k∈S.image color, ‖∑ i∈S.filter (fun i => color i=k),coeff i‖^12 :=
  HuxleyTriangularShortScratch.positive_difference_source_chart_twelfth_partition (ι:=ι) S F y z rat (σ:=σ) (c:=c) (U:=U) (η:=η) (T:=T) (M:=M) (a:=a) hσ hc hU hη hηmax hT hM ha hy hz hf hbound htests

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc E : ℝ) (chartKey : ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ab j i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ab j i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ab j i:ℝ)⁻¹)/a⌋)
    (∀ ab∈Gaps, ∀ j∈S ab, ∀ i, chartColor ab j i=chartKey) →
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
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    ((Mat 0=1 ∧ Mat 2=0 ∧ Mat 3=1) → Mat 1≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((2*Cupper*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4*|(Mat 1:ℝ)|))^((3:ℝ)⁻¹)+
          Cupper*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*|(Mat 1:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(Dupper*(B+1)*E^2*M^2/(N^4*|(Mat 1:ℝ)| *(Uref:ℝ))+2)) ∧
    ((Mat 0=1 ∧ Mat 1=0 ∧ Mat 3=1) → Mat 2≠0 →
      (∑ ab∈Gaps, ((S ab).card:ℝ)) ≤ 4*(m0:ℝ)*
        ((8*Clower*(Cthird+1)*R^4/(κ*Lunit^3*N^2*|(Mat 2:ℝ)|))^((3:ℝ)⁻¹)+
          4*Clower*(Cthird+1)*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(4*Dlower*(B+1)*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))+2)) :=
  HuxleyTriangularShortScratch.positive_difference_actual_fourier_charted_triangular_colored_sample_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

end HuxleyTriangularShortScratch
#print axioms HuxleyTriangularShortScratch.positive_difference_actual_fourier_triangular_closed_gap_count
#print axioms HuxleyTriangularShortScratch.positive_difference_physical_upper_reference_gap_packing
#print axioms HuxleyTriangularShortScratch.positive_difference_physical_lower_reference_gap_packing
#print axioms HuxleyTriangularShortScratch.upper_reference_gap_source_scale

#print axioms HuxleyTriangularShortScratch.positive_difference_actual_fourier_charted_triangular_all_sample_mass

#print axioms HuxleyTriangularShortScratch.positive_difference_source_chart_twelfth_partition
#print axioms HuxleyTriangularShortScratch.positive_difference_actual_fourier_charted_triangular_colored_sample_mass

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
import TaoTrudgianYang2025.PintzEndpointResearch
import TaoTrudgianYang2025.PintzFirstEndpointResearch
import GafniTao.HeathBrownShiftDecomposition

/-! Original research on the unchanged all-integer Pintz endpoints.
The lower-coordinate curve below comes from fixing the actual next-to-last
mixed logarithmic coefficient. Its curvature is proved, not assumed.
-/

namespace TaoTrudgianYang2025.PintzTailCorrelationResearch

noncomputable section

def mixedLabelRatio (k t u q x : ℝ) : ℝ :=
  u^(1/k)*x^(-1:ℝ)*(t*x^(-k)+q)^(-1/k)

def mixedLabelCurve (k t u q x : ℝ) : ℝ :=
  u^(1/k)*(t*x^(-k)+q)^((k-1)/k)-t*x^(1-k)

/-- The exact derivative of the ratio along a fixed-label curve. -/
theorem mixedLabelRatio_derivative {k t u q x : ℝ}
    (hk : 0 < k) (ht : 0 < t) (hq : 0 ≤ q) (hx : 0 < x) :
    HasDerivAt (mixedLabelRatio k t u q)
      (-q*mixedLabelRatio k t u q x/(x*(t*x^(-k)+q))) x := by
  have hz : 0 < t*x^(-k)+q := add_pos_of_pos_of_nonneg (by positivity) hq
  have hxpow := Real.hasDerivAt_rpow_const (p:=-k) (Or.inl hx.ne')
  have hinner := (hxpow.const_mul t).add_const q
  have houter := (Real.hasDerivAt_rpow_const (p:=-1/k) (Or.inl hz.ne')).comp x hinner
  have hraw := ((Real.hasDerivAt_rpow_const (p:=(-1:ℝ)) (Or.inl hx.ne')).mul houter).const_mul (u^(1/k))
  dsimp only [Function.comp_apply,Pi.mul_apply] at hraw
  convert hraw using 1
  · ext y
    dsimp only [mixedLabelRatio]
    ring
  · have he : (-1:ℝ)-1 = -2 := by norm_num
    rw [he]
    have htwo : x^(-2:ℝ)=x^(-1:ℝ)/x := by
      calc
        _ = x^((-1:ℝ)-1) := by norm_num
        _ = _ := by rw [Real.rpow_sub hx,Real.rpow_one]
    rw [htwo,Real.rpow_sub hx,Real.rpow_sub hz,Real.rpow_one,Real.rpow_one]
    dsimp only [mixedLabelRatio]
    field_simp
    ring

#print axioms mixedLabelRatio_derivative

/-- The fixed-label lower-coordinate curve has its literal first derivative. -/
theorem mixedLabelCurve_derivative {k t u q x : ℝ}
    (hk : 0 < k) (ht : 0 < t) (hq : 0 ≤ q) (hx : 0 < x) :
    HasDerivAt (mixedLabelCurve k t u q)
      ((k-1)*t*x^(-k)*(1-mixedLabelRatio k t u q x)) x := by
  have hz : 0 < t*x^(-k)+q := add_pos_of_pos_of_nonneg (by positivity) hq
  have hinner := ((Real.hasDerivAt_rpow_const (p:=-k) (Or.inl hx.ne')).const_mul t).add_const q
  have houter := (Real.hasDerivAt_rpow_const (p:=(k-1)/k) (Or.inl hz.ne')).comp x hinner
  have hraw := (houter.const_mul (u^(1/k))).sub
    ((Real.hasDerivAt_rpow_const (p:=1-k) (Or.inl hx.ne')).const_mul t)
  convert hraw using 1
  · have he : (k-1)/k-1 = -1/k := by field_simp; ring
    have he' : 1-k-1 = -k := by ring
    rw [he,he',Real.rpow_sub hx,Real.rpow_one]
    dsimp only [mixedLabelRatio]
    rw [Real.rpow_neg_one]
    field_simp
    ring

#print axioms mixedLabelCurve_derivative

/-- Positive curvature is explicit; no spacing estimate is supplied as a premise. -/
theorem mixedLabelCurve_second_derivative {k t u q x : ℝ}
    (hk : 0 < k) (ht : 0 < t) (hq : 0 ≤ q) (hx : 0 < x) :
    HasDerivAt (fun y => (k-1)*t*y^(-k)*(1-mixedLabelRatio k t u q y))
      ((k-1)*t*x^(-k-1)*
        (k*(mixedLabelRatio k t u q x-1)+q*mixedLabelRatio k t u q x/(t*x^(-k)+q))) x := by
  have hz : 0 < t*x^(-k)+q := add_pos_of_pos_of_nonneg (by positivity) hq
  have hpow := (Real.hasDerivAt_rpow_const (p:=-k) (Or.inl hx.ne')).const_mul ((k-1)*t)
  have hratio := (mixedLabelRatio_derivative (u:=u) hk ht hq hx).const_sub 1
  convert hpow.mul hratio using 1
  rw [Real.rpow_sub hx,Real.rpow_one]
  field_simp
  ring

#print axioms mixedLabelCurve_second_derivative

/-- Exact source entry: the real mixed label recovers the original index ratio. -/
theorem mixedLabelRatio_source {k t u x m : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hm : 0 < m) :
    mixedLabelRatio k t u (u*m^(-k)-t*x^(-k)) x = m/x := by
  have hz : t*x^(-k)+(u*m^(-k)-t*x^(-k))=u*m^(-k) := by ring
  have he : (-k)*(-1/k)=(1:ℝ) := by field_simp
  have huinv : u^(1/k)*u^(-1/k)=1 := by
    rw [←Real.rpow_add hu,show 1/k+(-1/k)=(0:ℝ) by ring,Real.rpow_zero]
  unfold mixedLabelRatio
  rw [hz,Real.mul_rpow hu.le (Real.rpow_nonneg hm.le _),←Real.rpow_mul hm.le,he,Real.rpow_one]
  calc
    _ = (u^(1/k)*u^(-1/k))*m*x^(-1:ℝ) := by ring
    _ = _ := by rw [huinv,Real.rpow_neg_one]; ring

#print axioms mixedLabelRatio_source

/-- Exact source entry for the next lower mixed logarithmic coefficient. -/
theorem mixedLabelCurve_source {k t u x m : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hm : 0 < m) :
    mixedLabelCurve k t u (u*m^(-k)-t*x^(-k)) x =
      u*m^(1-k)-t*x^(1-k) := by
  have hz : t*x^(-k)+(u*m^(-k)-t*x^(-k))=u*m^(-k) := by ring
  have he : (-k)*((k-1)/k)=1-k := by field_simp; ring
  have he' : 1/k+(k-1)/k=(1:ℝ) := by field_simp; ring
  unfold mixedLabelCurve
  rw [hz,Real.mul_rpow hu.le (Real.rpow_nonneg hm.le _),←Real.rpow_mul hm.le,he,
    ←mul_assoc,←Real.rpow_add hu,he',Real.rpow_one]

#print axioms mixedLabelCurve_source

/-- The top mixed coefficient measures the exact curvature error.
At a stationary overlap the curvature is `(k^2-1)*q/x`, not a generic bound. -/
theorem mixedLabelCurve_source_curvature {k t u x m : ℝ}
    (hk : 0 < k) (hu : 0 < u) (hx : 0 < x) (hm : 0 < m) :
    let q := u*m^(-k)-t*x^(-k)
    let e := u*m^(-k-1)-t*x^(-k-1)
    (k-1)*t*x^(-k-1)*
      (k*(mixedLabelRatio k t u q x-1)+q*mixedLabelRatio k t u q x/(t*x^(-k)+q)) =
      (k^2-1)*q/x-(k-1)*(m/x)*e*(k+q/(u*m^(-k))) := by
  dsimp only
  rw [mixedLabelRatio_source hk hu hm]
  have hz : t*x^(-k)+(u*m^(-k)-t*x^(-k))=u*m^(-k) := by ring
  rw [hz,Real.rpow_sub hx,Real.rpow_sub hm,Real.rpow_one,Real.rpow_one]
  field_simp
  ring

#print axioms mixedLabelCurve_source_curvature

/-- Subtracting the actual lower curvature makes the graph convex. -/
theorem quadratic_correction_convex {a b μ : ℝ} {f f' f'' : ℝ → ℝ}
    (hfirst : ∀ x∈Set.Icc a b, HasDerivAt f (f' x) x)
    (hsecond : ∀ x∈Set.Icc a b, HasDerivAt f' (f'' x) x)
    (hcurv : ∀ x∈Set.Icc a b, μ ≤ f'' x) :
    ConvexOn ℝ (Set.Icc a b) (fun x => f x-μ/2*x^2) := by
  have hf : ContinuousOn f (Set.Icc a b) := fun x hx => (hfirst x hx).continuousAt.continuousWithinAt
  apply convexOn_of_hasDerivWithinAt2_nonneg (f':=fun x => f' x-μ*x)
    (f'':=fun x => f'' x-μ) (convex_Icc a b)
  · exact hf.sub (by fun_prop)
  · intro x hx
    have hh := (hfirst x (interior_subset hx)).sub (((hasDerivAt_id x).pow 2).const_mul (μ/2))
    convert hh.hasDerivWithinAt using 1
    simp only [id_eq]
    ring
  · intro x hx
    have hh := (hsecond x (interior_subset hx)).sub ((hasDerivAt_id x).const_mul μ)
    convert hh.hasDerivWithinAt using 1
    ring
  · intro x hx
    exact sub_nonneg.mpr (hcurv x (interior_subset hx))

#print axioms quadratic_correction_convex

/-- Three near-level points of a curved graph have a short adjacent gap. -/
theorem curved_three_point_gap {a b c μ q η : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hbc : b < c)
    (hconv : ConvexOn ℝ (Set.Icc a c) (fun x => f x-μ/2*x^2))
    (ha : |f a-q| ≤ η) (hb : |f b-q| ≤ η) (hc : |f c-q| ≤ η) :
    μ*(b-a)*(c-b) ≤ 4*η := by
  have hac : 0 < c-a := by linarith only [hab,hbc]
  let u := (c-b)/(c-a)
  let v := (b-a)/(c-a)
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have huv : u+v=1 := by dsimp only [u,v]; field_simp; ring
  have hp : u*a+v*c=b := by dsimp only [u,v]; field_simp; ring
  have hvar : u*a^2+v*c^2-b^2=(b-a)*(c-b) := by dsimp only [u,v]; field_simp; ring
  have hh := hconv.2 (show a∈Set.Icc a c by constructor; rfl; linarith only [hab,hbc])
    (show c∈Set.Icc a c by constructor; linarith only [hab,hbc]; rfl) hu hv huv
  simp only [smul_eq_mul,hp] at hh
  have hquad := congrArg (fun z : ℝ => μ/2*z) hvar
  have hlinear : u*f a+v*f c-f b ≤ 2*η := by
    have ha' := (abs_le.mp ha).2
    have hb' := (abs_le.mp hb).1
    have hc' := (abs_le.mp hc).2
    have h₁ := mul_le_mul_of_nonneg_left ha' hu
    have h₂ := mul_le_mul_of_nonneg_left hc' hv
    have he := congrArg (fun z : ℝ => z*(q+η)) huv
    nlinarith only [h₁,h₂,hb',he]
  nlinarith only [hh,hquad,hlinear]

#print axioms curved_three_point_gap

/-- A fixed integer level cuts a strongly curved graph in at most two short clusters. -/
theorem curved_single_level_card (S : Finset ℕ) {f : ℝ → ℝ} {μ q η : ℝ}
    (hμ : 0 < μ) (hη : 0 ≤ η)
    (hconv : ∀ a∈S, ∀ c∈S, ConvexOn ℝ (Set.Icc (a:ℝ) c) (fun x => f x-μ/2*x^2))
    (hlevel : ∀ n∈S, |f n-q| ≤ η) :
    (S.card:ℝ) ≤ 4+4*Real.sqrt (η/μ) := by
  classical
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let c := S.max' hS
    let D := 2*Real.sqrt (η/μ)
    let K := Nat.ceil D
    have ha : a∈S := Finset.min'_mem S hS
    have hc : c∈S := Finset.max'_mem S hS
    have hD : 0 ≤ D := by dsimp only [D]; positivity
    have hK : D ≤ (K:ℝ) := Nat.le_ceil D
    have hsqrt : μ*D^2=4*η := by
      dsimp only [D]
      rw [mul_pow,Real.sq_sqrt (div_nonneg hη hμ.le)]
      field_simp
      ring
    have hsub : S ⊆ Finset.Icc a (a+K) ∪ Finset.Icc (c-K) c := by
      intro b hb
      have hab : a ≤ b := Finset.min'_le S b hb
      have hbc : b ≤ c := Finset.le_max' S b hb
      by_cases h₁ : b ≤ a+K
      · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hab,h₁⟩)
      by_cases h₂ : c-K ≤ b
      · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨h₂,hbc⟩)
      have hab' : (a:ℝ) < b := by exact_mod_cast (by omega : a < b)
      have hbc' : (b:ℝ) < c := by exact_mod_cast (by omega : b < c)
      have hgap₁ : D < (b:ℝ)-a := by
        have hh : (a:ℝ)+(K:ℝ) < b := by exact_mod_cast (by omega : a+K < b)
        linarith only [hK,hh]
      have hgap₂ : D < (c:ℝ)-b := by
        have hh : (b:ℝ)+(K:ℝ) < c := by exact_mod_cast (by omega : b+K < c)
        linarith only [hK,hh]
      have hh := curved_three_point_gap hab' hbc' (hconv a ha c hc)
        (hlevel a ha) (hlevel b hb) (hlevel c hc)
      have hp : D*D < ((b:ℝ)-a)*((c:ℝ)-b) :=
        mul_lt_mul_of_nonneg hgap₁ hgap₂ hD hD
      have hp' := mul_lt_mul_of_pos_left hp hμ
      exfalso
      nlinarith only [hh,hp',hsqrt]
    have hcard : S.card ≤ 2*(K+1) := by
      have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Nat.card_Icc,Nat.card_Icc] at hh
      omega
    have hceil : (K:ℝ) ≤ D+1 := (Nat.ceil_lt_add_one hD).le
    have hh : (S.card:ℝ) ≤ 2*((K:ℝ)+1) := by exact_mod_cast hcard
    dsimp only [D] at hceil
    linarith only [hh,hceil]
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hz,Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms curved_single_level_card

/-- All near-integer levels in a bounded image interval, with the actual curvature saving. -/
theorem curved_bounded_range_card (S : Finset ℕ) {f : ℝ → ℝ} {μ η lo hi : ℝ}
    (hμ : 0 < μ) (hη : 0 ≤ η) (hlohi : lo ≤ hi)
    (hconv : ∀ a∈S, ∀ c∈S, ConvexOn ℝ (Set.Icc (a:ℝ) c) (fun x => f x-μ/2*x^2))
    (hvalues : ∀ n∈S, lo ≤ f n ∧ f n ≤ hi)
    (hnear : ∀ n∈S, ∃ q : ℤ, |f n-(q:ℝ)| ≤ η) :
    (S.card:ℝ) ≤ (hi-lo+2*η+1)*(4+4*Real.sqrt (η/μ)) := by
  classical
  by_cases hS : S.Nonempty
  · let label (n : ℕ) : ℤ := if hn : n∈S then Classical.choose (hnear n hn) else 0
    have hl (n : ℕ) (hn : n∈S) : |f n-(label n:ℝ)| ≤ η := by
      simpa only [label,dif_pos hn] using Classical.choose_spec (hnear n hn)
    let I := Finset.Icc (Int.ceil (lo-η)) (Int.floor (hi+η))
    have hmap (n : ℕ) (hn : n∈S) : label n∈I := by
      apply Finset.mem_Icc.mpr
      constructor
      · apply Int.ceil_le.mpr
        linarith only [(hvalues n hn).1,(abs_le.mp (hl n hn)).2]
      · apply Int.le_floor.mpr
        linarith only [(hvalues n hn).2,(abs_le.mp (hl n hn)).1]
    have hcI : (I.card:ℝ) ≤ hi-lo+2*η+1 := by
      obtain ⟨n,hn⟩ := hS
      have hp := Finset.mem_Icc.mp (hmap n hn)
      have he : (I.card:ℝ)=(Int.floor (hi+η):ℝ)+1-(Int.ceil (lo-η):ℝ) := by
        exact_mod_cast (Int.card_Icc_of_le _ _
          (show Int.ceil (lo-η) ≤ Int.floor (hi+η)+1 by omega))
      rw [he]
      linarith only [Int.floor_le (hi+η),Int.le_ceil (lo-η)]
    have hfiber (q : ℤ) :
        ((S.filter (fun n => label n=q)).card:ℝ) ≤ 4+4*Real.sqrt (η/μ) := by
      apply curved_single_level_card _ hμ hη
      · intro a ha c hc
        exact hconv a (Finset.mem_filter.mp ha).1 c (Finset.mem_filter.mp hc).1
      · intro n hn
        obtain ⟨hn,hq⟩ := Finset.mem_filter.mp hn
        simpa only [hq] using hl n hn
    have he := Finset.card_eq_sum_card_fiberwise (f:=label) (s:=S) (t:=I) hmap
    calc
      _ = ∑ q∈I, ((S.filter (fun n => label n=q)).card:ℝ) := by exact_mod_cast he
      _ ≤ ∑ _q∈I, (4+4*Real.sqrt (η/μ)) := Finset.sum_le_sum (fun q _ => hfiber q)
      _ = (I.card:ℝ)*(4+4*Real.sqrt (η/μ)) := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcI (by positivity)
  · have hz : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hz,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (by linarith only [hlohi,hη]) (by positivity)

#print axioms curved_bounded_range_card


/-- The literal mixed lower coefficient at a fixed integer index shift. -/
def mixedShiftValue (k t u h x : ℝ) : ℝ :=
  t*x^(-k)-u*(x+h)^(-k)

theorem mixedShiftValue_derivative {k t u h x : ℝ}
    (hx : 0 < x) (hxh : 0 < x+h) :
    HasDerivAt (mixedShiftValue k t u h)
      (-k*mixedShiftValue (k+1) t u h x) x := by
  have h₁ := (Real.hasDerivAt_rpow_const (p:=-k) (Or.inl hx.ne')).const_mul t
  have h₂ := ((Real.hasDerivAt_rpow_const (p:=-k) (Or.inl hxh.ne')).comp x
    ((hasDerivAt_id x).add_const h)).const_mul u
  convert h₁.sub h₂ using 1
  dsimp only [mixedShiftValue,id_eq]
  rw [show -(k+1) = -k-1 by ring]
  ring

theorem mixedShiftValue_second_derivative {k t u h x : ℝ}
    (hx : 0 < x) (hxh : 0 < x+h) :
    HasDerivAt (fun y => -k*mixedShiftValue (k+1) t u h y)
      (k*(k+1)*mixedShiftValue (k+2) t u h x) x := by
  convert (mixedShiftValue_derivative (k:=k+1) (t:=t) (u:=u) hx hxh).const_mul (-k) using 1
  rw [show k+1+1=k+2 by ring]
  ring

/-- The top-coordinate residual is the exact error in the fixed-shift curvature. -/
theorem mixedShiftValue_curvature_identity {k t u h x : ℝ}
    (hx : 0 < x) (hxh : 0 < x+h) :
    k*(k+1)*mixedShiftValue (k+2) t u h x =
      k*(k+1)/(x+h)*(t*h*x^(-k-2)+mixedShiftValue (k+1) t u h x) := by
  dsimp only [mixedShiftValue]
  have hx₂ : x^(-k-2)=x^(-k-1)/x := by
    rw [show -k-2=(-k-1)-1 by ring,Real.rpow_sub hx,Real.rpow_one]
  have hy₂ : (x+h)^(-(k+2))=(x+h)^(-k-1)/(x+h) := by
    rw [show -(k+2)=(-k-1)-1 by ring,Real.rpow_sub hxh,Real.rpow_one]
  rw [show -(k+2)=-k-2 by ring, hx₂, show -(k+1)=-k-1 by ring]
  rw [show -k-2=-(k+2) by ring,hy₂]
  field_simp
  ring

#print axioms mixedShiftValue_derivative
#print axioms mixedShiftValue_second_derivative
#print axioms mixedShiftValue_curvature_identity


/-- A uniform Lipschitz estimate for the actual power on the height-ratio interval. -/
theorem power_ratio_lipschitz {d a b : ℝ}
    (hd : 1 ≤ d) (ha : 1 ≤ a) (ha2 : a ≤ 2)
    (hb : 1 ≤ b) (hb2 : b ≤ 2) :
    |a^d-b^d| ≤ d*2^(d-1)*|a-b| := by
  have hh := (convex_Icc (1:ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f:=fun x : ℝ => x^d) (f':=fun x : ℝ => d*x^(d-1))
    (fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (by linarith only [hx.1] : x≠0))).hasDerivWithinAt)
    (fun x hx => show ‖d*x^(d-1)‖ ≤ d*2^(d-1) from by
      have hx0 : 0 ≤ x := by linarith only [hx.1]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hx0 hx.2 (by linarith only [hd])) (by linarith only [hd]))
    (show b∈Set.Icc (1:ℝ) 2 from ⟨hb,hb2⟩)
    (show a∈Set.Icc (1:ℝ) 2 from ⟨ha,ha2⟩)
  simpa only [Real.norm_eq_abs] using hh

/-- The top residual of the literal fixed-shift phase is controlled by its ratio error. -/
theorem mixedShiftValue_ratio_bound {d t r h x E : ℝ}
    (hd : 1 ≤ d) (ht : 0 ≤ t) (hx : 0 < x) (hh : 0 ≤ h)
    (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (hw2 : (x+h)/x ≤ 2) (herror : |(x+h)/x-r| ≤ E) :
    |mixedShiftValue d t (t*r^d) h x| ≤
      t*(x+h)^(-d)*(d*2^(d-1))*E := by
  have hxh : 0 < x+h := by positivity
  have hw : 1 ≤ (x+h)/x := (le_div_iff₀ hx).mpr (by linarith only [hh])
  have hpow := power_ratio_lipschitz hd hw hw2 hr hr2
  have hident : mixedShiftValue d t (t*r^d) h x =
      t*(x+h)^(-d)*(((x+h)/x)^d-r^d) := by
    dsimp only [mixedShiftValue]
    rw [Real.div_rpow hxh.le hx.le,Real.rpow_neg hxh.le]
    have hp : (x+h)^d≠0 := (Real.rpow_pos_of_pos hxh d).ne'
    have hp' : x^d≠0 := (Real.rpow_pos_of_pos hx d).ne'
    rw [Real.rpow_neg hx.le]
    field_simp
  rw [hident,abs_mul,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (t*(x+h)^(-d))*(d*2^(d-1)*|(x+h)/x-r|) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ _ := by
      have hde : 0 ≤ d*2^(d-1) := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left herror
        (mul_nonneg (show 0 ≤ t*(x+h)^(-d) by positivity) hde)]

#print axioms power_ratio_lipschitz
#print axioms mixedShiftValue_ratio_bound

/-- A fixed positive shift makes the index ratio monotone throughout the interval. -/
theorem fixed_shift_ratio_between {a b x h r E : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hax : a ≤ x) (hxb : x ≤ b)
    (hea : |(a+h)/a-r| ≤ E) (heb : |(b+h)/b-r| ≤ E) :
    |(x+h)/x-r| ≤ E := by
  have hx : 0 < x := ha.trans_le hax
  have hb : 0 < b := hx.trans_le hxb
  have hleft : (b+h)/b ≤ (x+h)/x := by
    rw [add_div,add_div,div_self hb.ne',div_self hx.ne']
    exact add_le_add le_rfl (div_le_div_of_nonneg_left hh hx hxb)
  have hright : (x+h)/x ≤ (a+h)/a := by
    rw [add_div,add_div,div_self hx.ne',div_self ha.ne']
    exact add_le_add le_rfl (div_le_div_of_nonneg_left hh ha hax)
  exact abs_le.mpr ⟨by linarith only [hleft,(abs_le.mp heb).1],
    by linarith only [hright,(abs_le.mp hea).2]⟩

/-- The actual ratio errors force a short interval of first indices at fixed shift. -/
theorem fixed_shift_diameter {N a b h r E : ℝ}
    (hN : 0 < N) (hh : 0 < h)
    (ha : N ≤ a) (ha2 : a ≤ 2*N) (hb : N ≤ b) (hb2 : b ≤ 2*N)
    (hea : |(a+h)/a-r| ≤ E) (heb : |(b+h)/b-r| ≤ E) :
    |a-b| ≤ 8*N^2*E/h := by
  have hap : 0 < a := hN.trans_le ha
  have hbp : 0 < b := hN.trans_le hb
  have hE : 0 ≤ E := (abs_nonneg _).trans hea
  have hdiff : |(a+h)/a-(b+h)/b| ≤ 2*E := by
    calc
      _ ≤ |(a+h)/a-r|+|r-(b+h)/b| := abs_sub_le _ _ _
      _ ≤ E+E := add_le_add hea (by simpa only [abs_sub_comm] using heb)
      _ = _ := by ring
  have hid : (a+h)/a-(b+h)/b = h*(b-a)/(a*b) := by field_simp; ring
  rw [hid,abs_div,abs_mul,abs_of_pos hh,abs_of_pos (mul_pos hap hbp),
    abs_sub_comm b a] at hdiff
  have hmul := (div_le_iff₀ (mul_pos hap hbp)).mp hdiff
  have hab : a*b ≤ (2*N)*(2*N) := by gcongr
  have hh' := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 2*E)
  apply (le_div_iff₀ hh).mpr
  nlinarith only [hmul,hh']

/-- A small actual top-coordinate residual gives a positive fixed-shift curvature. -/
theorem mixedShiftValue_curvature_lower {k t u h x N : ℝ}
    (hk : 0 < k) (ht : 0 < t) (hh : 0 < h) (hN : 0 < N)
    (hx : 0 < x) (hx2 : x ≤ 2*N) (hxh2 : x+h ≤ 2*N)
    (herror : |mixedShiftValue (k+1) t u h x| ≤ t*h*(2*N)^(-k-2)/2) :
    k*(k+1)*t*h*(2*N)^(-k-3)/2 ≤
      k*(k+1)*mixedShiftValue (k+2) t u h x := by
  have hxh : 0 < x+h := by positivity
  have hbase : 0 < 2*N := by positivity
  have hpow := Real.rpow_le_rpow_of_nonpos hx hx2 (show -k-2 ≤ 0 by linarith only [hk])
  have hmain := mul_le_mul_of_nonneg_left hpow (mul_nonneg ht.le hh.le)
  have hins : t*h*(2*N)^(-k-2)/2 ≤
      t*h*x^(-k-2)+mixedShiftValue (k+1) t u h x := by
    linarith only [hmain,(abs_le.mp herror).1]
  have hcoef : k*(k+1)/(2*N) ≤ k*(k+1)/(x+h) :=
    div_le_div_of_nonneg_left (by positivity) hxh hxh2
  rw [mixedShiftValue_curvature_identity hx hxh]
  calc
    _ = (k*(k+1)/(2*N))*(t*h*(2*N)^(-k-2)/2) := by
      rw [show -k-3=(-k-2)-1 by ring,Real.rpow_sub hbase,Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul hcoef hins (by positivity) (by positivity)

#print axioms fixed_shift_ratio_between
#print axioms fixed_shift_diameter
#print axioms mixedShiftValue_curvature_lower

set_option maxHeartbeats 800000 in
/-- Count the actual lower mixed coefficients at a fixed shift. The interval
length, first derivative bound, positive curvature and image range are all
derived from the literal ratio errors, rather than supplied as count hypotheses. -/
theorem mixedShift_near_integer_card (S : Finset ℕ) {k t h N r E η : ℝ}
    (hk : 1 ≤ k) (ht : 0 < t) (hh : 0 < h) (hN : 0 < N)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hE : 0 ≤ E) (hη : 0 ≤ η)
    (hsmall : t*N^(-k-1)*((k+1)*2^k)*E ≤ t*h*(2*N)^(-k-2)/2)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ)+h ≤ 2*N)
    (hratio : ∀ n∈S, |((n:ℝ)+h)/n-r| ≤ E)
    (hnear : ∀ n∈S, ∃ q : ℤ,
      |mixedShiftValue k t (t*r^(k+1)) h n-(q:ℝ)| ≤ η) :
    let D := t*N^(-k-1)*((k+1)*2^k)*E
    let B := 8*N^2*E/h
    let μ := k*(k+1)*t*h*(2*N)^(-k-3)/2
    (S.card:ℝ) ≤ (2*k*D*B+2*η+1)*(4+4*Real.sqrt (η/μ)) := by
  classical
  let D := t*N^(-k-1)*((k+1)*2^k)*E
  let B := 8*N^2*E/h
  let μ := k*(k+1)*t*h*(2*N)^(-k-3)/2
  let u := t*r^(k+1)
  let f := mixedShiftValue k t u h
  change (S.card:ℝ) ≤ (2*k*D*B+2*η+1)*(4+4*Real.sqrt (η/μ))
  have hkp : 0 < k := by linarith only [hk]
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  by_cases hne : S.Nonempty
  · let a := S.min' hne
    let c := S.max' hne
    have ha : a∈S := Finset.min'_mem S hne
    have hc : c∈S := Finset.max'_mem S hne
    have hac : (a:ℝ) ≤ c := by exact_mod_cast (Finset.min'_le S c hc)
    have hapos : 0 < (a:ℝ) := hN.trans_le (hS a ha).1
    have hinterval (x : ℝ) (hx : x∈Set.Icc (a:ℝ) c) :
        N ≤ x ∧ x ≤ 2*N ∧ x+h ≤ 2*N := by
      constructor
      · exact (hS a ha).1.trans hx.1
      constructor <;> linarith only [hx.2,(hS c hc).2,hh]
    have hresidual (x : ℝ) (hx : x∈Set.Icc (a:ℝ) c) :
        |mixedShiftValue (k+1) t u h x| ≤ D := by
      obtain ⟨hxN,_,hxm⟩ := hinterval x hx
      have hxp : 0 < x := hN.trans_le hxN
      have herr := fixed_shift_ratio_between hapos hh.le hx.1 hx.2
        (hratio a ha) (hratio c hc)
      have hb := mixedShiftValue_ratio_bound
        (show 1 ≤ k+1 by linarith only [hk]) ht.le hxp hh.le hr hr2
        ((div_le_iff₀ hxp).mpr (by linarith only [hxN,hxm])) herr
      change |mixedShiftValue (k+1) t u h x| ≤ _ at hb
      rw [show -(k+1)=-k-1 by ring,show k+1-1=k by ring] at hb
      apply hb.trans
      have hp := Real.rpow_le_rpow_of_nonpos hN
        (show N ≤ x+h by linarith only [hxN,hh]) (show -k-1 ≤ 0 by linarith only [hk])
      dsimp only [D]
      gcongr
    have hfirst (x : ℝ) (hx : x∈Set.Icc (a:ℝ) c) :
        HasDerivAt f (-k*mixedShiftValue (k+1) t u h x) x := by
      have hxp := hN.trans_le (hinterval x hx).1
      exact mixedShiftValue_derivative hxp (by positivity)
    have hsecond (x : ℝ) (hx : x∈Set.Icc (a:ℝ) c) :
        HasDerivAt (fun y => -k*mixedShiftValue (k+1) t u h y)
          (k*(k+1)*mixedShiftValue (k+2) t u h x) x := by
      have hxp := hN.trans_le (hinterval x hx).1
      exact mixedShiftValue_second_derivative hxp (by positivity)
    have hcurv (x : ℝ) (hx : x∈Set.Icc (a:ℝ) c) :
        μ ≤ k*(k+1)*mixedShiftValue (k+2) t u h x := by
      obtain ⟨hxN,hx2,hxm⟩ := hinterval x hx
      exact mixedShiftValue_curvature_lower hkp ht hh hN (hN.trans_le hxN) hx2 hxm
        ((hresidual x hx).trans hsmall)
    have hconv := quadratic_correction_convex hfirst hsecond hcurv
    have hderiv (x : ℝ) (hx : x∈Set.Icc (a:ℝ) c) :
        ‖-k*mixedShiftValue (k+1) t u h x‖ ≤ k*D := by
      rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_pos hkp]
      exact mul_le_mul_of_nonneg_left (hresidual x hx) hkp.le
    have hmember (n : ℕ) (hn : n∈S) : (n:ℝ)∈Set.Icc (a:ℝ) c := by
      constructor
      · exact_mod_cast (Finset.min'_le S n hn)
      · exact_mod_cast (Finset.le_max' S n hn)
    have hvalues (n : ℕ) (hn : n∈S) : |f n-f a| ≤ k*D*B := by
      have hdiff := (convex_Icc (a:ℝ) c).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x hx => (hfirst x hx).hasDerivWithinAt) hderiv
        (show (a:ℝ)∈Set.Icc (a:ℝ) c from ⟨le_rfl,hac⟩) (hmember n hn)
      have hdiam := fixed_shift_diameter hN hh (hS n hn).1
        (by linarith only [(hS n hn).2,hh]) (hS a ha).1
        (by linarith only [(hS a ha).2,hh]) (hratio n hn) (hratio a ha)
      simp only [Real.norm_eq_abs] at hdiff
      exact hdiff.trans (mul_le_mul_of_nonneg_left hdiam (mul_nonneg hkp.le hD))
    have hcount := curved_bounded_range_card S hμ hη
      (show f a-k*D*B ≤ f a+k*D*B by
        nlinarith only [mul_nonneg (mul_nonneg hkp.le hD) hB])
      (fun b hb d hd => hconv.subset
        (Set.Icc_subset_Icc (hmember b hb).1 (hmember d hd).2) (convex_Icc _ _))
      (fun n hn => ⟨by linarith only [(abs_le.mp (hvalues n hn)).1],
        by linarith only [(abs_le.mp (hvalues n hn)).2]⟩) hnear
    convert hcount using 1
    ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms mixedShift_near_integer_card

/-- The exact stationary product for the general-order inverse-root curve. -/
def stationaryProduct (k r w : ℝ) : ℝ :=
  (r^(k+1)*w^(-k)-1)*(w-1)^k

theorem stationaryProduct_derivative {k r w : ℝ} (hw : 1 < w) :
    HasDerivAt (stationaryProduct k r)
      (k*(w-1)^(k-1)*w^(-k-1)*(r^(k+1)-w^(k+1))) w := by
  have hwp : 0 < w := by linarith only [hw]
  have hwm : 0 < w-1 := by linarith only [hw]
  have h₁ := ((Real.hasDerivAt_rpow_const (p:=-k) (Or.inl hwp.ne')).const_mul (r^(k+1))).sub_const 1
  have h₂ := (Real.hasDerivAt_rpow_const (p:=k) (Or.inl hwm.ne')).comp w
    ((hasDerivAt_id w).sub_const 1)
  convert h₁.mul h₂ using 1
  dsimp only [id_eq,Function.comp_apply]
  rw [Real.rpow_sub hwm,Real.rpow_sub hwp,Real.rpow_one,Real.rpow_one,
    Real.rpow_add hwp,Real.rpow_one,Real.rpow_neg hwp.le]
  field_simp
  ring

theorem stationaryProduct_at_root {k r : ℝ} (hr : 1 < r) :
    stationaryProduct k r r = (r-1)^(k+1) := by
  have hrp : 0 < r := by linarith only [hr]
  have hrm : 0 < r-1 := by linarith only [hr]
  unfold stationaryProduct
  rw [←Real.rpow_add hrp,show k+1+-k=(1:ℝ) by ring,Real.rpow_one,
    Real.rpow_add hrm,Real.rpow_one]
  ring

#print axioms stationaryProduct_derivative
#print axioms stationaryProduct_at_root

set_option maxHeartbeats 800000 in
/-- General-order stationary cancellation is quadratic in the actual ratio error. -/
theorem stationaryProduct_quadratic_error {k r w : ℝ}
    (hk : 1 ≤ k) (hr : 1 < r) (hr2 : r ≤ 2)
    (hw : 1 < w) (hw2 : w ≤ 2) (hwgap : w-1 ≤ 2*(r-1)) :
    |stationaryProduct k r w-(r-1)^(k+1)| ≤
      k*(k+1)*2^(2*k-1)*(r-1)^(k-1)*(w-r)^2 := by
  let C := k*(k+1)*2^(2*k-1)*(r-1)^(k-1)
  let g := fun z : ℝ => k*(z-1)^(k-1)*z^(-k-1)*(r^(k+1)-z^(k+1))
  have hkp : 0 < k := by linarith only [hk]
  have hrm : 0 < r-1 := by linarith only [hr]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hzdom (z : ℝ) (hz : z∈Set.Icc (min r w) (max r w)) :
      1 < z ∧ z ≤ 2 ∧ z-1 ≤ 2*(r-1) := by
    refine ⟨(lt_min hr hw).trans_le hz.1,hz.2.trans (max_le hr2 hw2),?_⟩
    have hhi : max r w ≤ 1+2*(r-1) :=
      max_le (by linarith only [hr]) (by linarith only [hwgap])
    linarith only [hz.2,hhi]
  have hfirst (z : ℝ) (hz : z∈Set.Icc (min r w) (max r w)) :
      HasDerivAt (stationaryProduct k r) (g z) z :=
    stationaryProduct_derivative (hzdom z hz).1
  have hbound (z : ℝ) (hz : z∈Set.Icc (min r w) (max r w)) :
      ‖g z‖ ≤ C*|w-r| := by
    obtain ⟨hz1,hz2,hzgap⟩ := hzdom z hz
    have hzp : 0 < z := by linarith only [hz1]
    have hzm : 0 < z-1 := by linarith only [hz1]
    have hp := power_ratio_lipschitz (show 1 ≤ k+1 by linarith only [hk])
      hr.le hr2 hz1.le hz2
    rw [show k+1-1=k by ring] at hp
    have hdist : |r-z| ≤ |w-r| := by
      simpa only [abs_sub_comm r z] using (Set.abs_sub_left_of_mem_uIcc hz)
    have hinv : z^(-k-1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hz1.le (by linarith only [hk])
    have hpow : (z-1)^(k-1) ≤ (2*(r-1))^(k-1) :=
      Real.rpow_le_rpow hzm.le hzgap (by linarith only [hk])
    dsimp only [g]
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_mul,
      abs_of_pos hkp,abs_of_nonneg (Real.rpow_nonneg hzm.le _),
      abs_of_nonneg (Real.rpow_nonneg hzp.le _)]
    calc
      _ ≤ k*(2*(r-1))^(k-1)*1*((k+1)*2^k*|w-r|) := by
        apply mul_le_mul
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hkp.le) hinv
            (by positivity) (by positivity)
        · exact hp.trans (mul_le_mul_of_nonneg_left hdist (by positivity))
        · exact abs_nonneg _
        · positivity
      _ = C*|w-r| := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hrm.le]
        have he : (2:ℝ)^(k-1)*2^k=2^(2*k-1) := by
          rw [←Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          congr 1
          ring
        dsimp only [C]
        calc
          _ = k*(k+1)*(2^(k-1)*2^k)*(r-1)^(k-1)*|w-r| := by ring
          _ = _ := by rw [he]
  have hmvt := (convex_Icc (min r w) (max r w)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hfirst z hz).hasDerivWithinAt) hbound
    (show r∈Set.Icc (min r w) (max r w) from ⟨min_le_left _ _,le_max_left _ _⟩)
    (show w∈Set.Icc (min r w) (max r w) from ⟨min_le_right _ _,le_max_right _ _⟩)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,stationaryProduct_at_root hr] at hmvt
  have he : C * |w-r| * |w-r| = C*(w-r)^2 := by rw [mul_assoc,←pow_two,sq_abs]
  exact hmvt.trans_eq he

#print axioms stationaryProduct_quadratic_error

/-- Expanding an integer power cannot contract a distance from a point at least one. -/
theorem power_distance_lower {r w : ℝ} (d : ℕ) (hd : 1 ≤ d)
    (hr : 1 ≤ r) (hw : 0 ≤ w) : |w-r| ≤ |w^d-r^d| := by
  have haux (a b : ℝ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
      ∀ j : ℕ, a-b ≤ a^(j+1)-b^(j+1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hgap : 0 ≤ a-b := sub_nonneg.mpr hba
      have hp := mul_le_mul_of_nonneg_left ih (by linarith only [ha] : 0 ≤ a)
      have hsq := mul_le_mul_of_nonneg_right ha hgap
      have hbpow := mul_nonneg (pow_nonneg hb (j+1)) hgap
      rw [pow_succ a (j+1),pow_succ b (j+1)]
      nlinarith only [hp,hsq,hbpow]
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  rcases le_total w r with hwr | hrw
  · rw [abs_of_nonpos (sub_nonpos.mpr hwr),
      abs_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ hw hwr (j+1)))]
    linarith only [haux r w hr hw hwr j]
  · rw [abs_of_nonneg (sub_nonneg.mpr hrw),
      abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (by linarith only [hr]) hrw (j+1)))]
    exact haux w r (hr.trans hrw) (by linarith only [hr]) hrw j

/-- Actual general-degree logarithmic Taylor cell. -/
def tailLogCell (d H : ℕ) (t n : ℝ) :
    Set (GafniTao.HeathBrownCoefficientTorus (d+1)) :=
  GafniTao.heathBrownCoefficientCell (d+1) H
    (PintzEndpointResearch.logarithmicTaylorPhase t) n

/-- Both signs of every genuine mixed logarithmic coordinate. -/
theorem tailLogCell_mixed_coordinate {d H : ℕ} {t u n m : ℝ}
    (hn : 0 < n) (hm : 0 < m)
    (hover : (tailLogCell d H t n ∩ tailLogCell d H u m).Nonempty)
    (j : Fin d) :
    GafniTao.heathBrownDistanceToInteger
      ((t/n^((j:ℕ)+1)-u/m^((j:ℕ)+1))/(2*Real.pi*(((j:ℕ)+1:ℕ):ℝ))) ≤
      2/((H:ℝ)^((j:ℕ)+1)) := by
  obtain ⟨α,ht,hu⟩ := hover
  have htj := ht j (Set.mem_univ j)
  have huj := hu j (Set.mem_univ j)
  have hdist := dist_triangle
    (GafniTao.heathBrownCoefficientCenter (d+1)
      (PintzEndpointResearch.logarithmicTaylorPhase t) n j) (α j)
    (GafniTao.heathBrownCoefficientCenter (d+1)
      (PintzEndpointResearch.logarithmicTaylorPhase u) m j)
  unfold GafniTao.heathBrownCoefficientCenter at hdist
  rw [PintzEndpointResearch.logarithmicTaylorPhase_coordinate _ t hn,
    PintzEndpointResearch.logarithmicTaylorPhase_coordinate _ u hm,
    GafniTao.unitAddCircle_dist_real_coe] at hdist
  change dist (α j) _ ≤ _ at htj huj
  rw [dist_comm (α j)] at htj
  change dist _ _ ≤ ((H:ℝ)^((j:ℕ)+1))⁻¹ at htj huj
  unfold GafniTao.heathBrownCoefficientCenter at htj huj
  rw [PintzEndpointResearch.logarithmicTaylorPhase_coordinate _ t hn] at htj
  rw [PintzEndpointResearch.logarithmicTaylorPhase_coordinate _ u hm] at huj
  have hh := hdist.trans (show _ ≤ 2*((H:ℝ)^((j:ℕ)+1))⁻¹ by linarith only [htj,huj])
  have he : (-1:ℝ)^((j:ℕ)+1)*t/(2*Real.pi*(((j:ℕ)+1:ℕ):ℝ)*n^((j:ℕ)+1)) -
      (-1:ℝ)^((j:ℕ)+1)*u/(2*Real.pi*(((j:ℕ)+1:ℕ):ℝ)*m^((j:ℕ)+1)) =
      (-1:ℝ)^((j:ℕ)+1)*((t/n^((j:ℕ)+1)-u/m^((j:ℕ)+1))/(2*Real.pi*(((j:ℕ)+1:ℕ):ℝ))) := by ring
  rw [he] at hh
  rcases neg_one_pow_eq_or ℝ ((j:ℕ)+1) with hp | hp
  · simpa only [hp,one_mul,div_eq_mul_inv] using hh
  · simpa only [hp,neg_one_mul,GafniTao.heathBrownDistanceToInteger_neg,div_eq_mul_inv] using hh

#print axioms power_distance_lower
#print axioms tailLogCell_mixed_coordinate

/-- The genuine highest mixed coordinate has no winding on the physical slab. -/
theorem tailLogCell_top_raw {d H : ℕ} {N T t u n m : ℝ}
    (hd : 1 ≤ d) (hN : 0 < N) (hT : T ≤ N^d)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hm : N ≤ m)
    (hover : (tailLogCell d H t n ∩ tailLogCell d H u m).Nonempty) :
    |t/n^d-u/m^d| ≤ 4*Real.pi*d/(H:ℝ)^d := by
  have hnp : 0 < n := hN.trans_le hn
  have hmp : 0 < m := hN.trans_le hm
  have hdp : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hcoord := tailLogCell_mixed_coordinate hnp hmp hover ⟨d-1,by omega⟩
  simp only [show d-1+1=d by omega] at hcoord
  have ht2 : t/n^d ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hp := pow_le_pow_left₀ hN.le hn d
    linarith only [hp,hT,htT]
  have hu2 : u/m^d ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hp := pow_le_pow_left₀ hN.le hm d
    linarith only [hp,hT,huT]
  have hsize : |t/n^d-u/m^d| ≤ 2 :=
    abs_le.mpr ⟨by linarith only [hu2,show 0 ≤ t/n^d by positivity],
      by linarith only [ht2,show 0 ≤ u/m^d by positivity]⟩
  have hden : 0 < 2*Real.pi*(d:ℝ) := by positivity
  have hhalf : |(t/n^d-u/m^d)/(2*Real.pi*d)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    have hp := mul_le_mul_of_nonneg_left hdp Real.pi_pos.le
    linarith only [hp,hsize,Real.pi_gt_three]
  have hh := GafniTao.abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half hcoord hhalf
  rw [abs_div,abs_of_pos hden] at hh
  have hh' := (div_le_iff₀ hden).mp hh
  convert hh' using 1
  ring

/-- Source-entry ratio localization uses the literal no-winding highest coordinate. -/
theorem tailLogCell_ratio_error {d H : ℕ} {N T t u n m r : ℝ}
    (hd : 1 ≤ d) (hN : 0 < N) (hT : T ≤ N^d)
    (ht : 0 < t) (hu : 0 ≤ u) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hm : N ≤ m) (hm2 : m ≤ 2*N)
    (hr : 1 ≤ r) (hpow : t*r^d=u)
    (hover : (tailLogCell d H t n ∩ tailLogCell d H u m).Nonempty) :
    |m/n-r| ≤ 4*Real.pi*d*(2*N)^d/(t*(H:ℝ)^d) := by
  have hnp : 0 < n := hN.trans_le hn
  have hmp : 0 < m := hN.trans_le hm
  have hraw := tailLogCell_top_raw hd hN hT ht.le hu htT huT hn hm hover
  have he : (m/n)^d-r^d=(m^d/t)*(t/n^d-u/m^d) := by
    rw [←hpow,div_pow]
    field_simp
  calc
    _ ≤ |(m/n)^d-r^d| := power_distance_lower d hd hr (by positivity)
    _ = (m^d/t)*|t/n^d-u/m^d| := by rw [he,abs_mul,abs_of_pos (by positivity)]
    _ ≤ ((2*N)^d/t)*(4*Real.pi*d/(H:ℝ)^d) := by gcongr
    _ = _ := by ring

#print axioms tailLogCell_top_raw
#print axioms tailLogCell_ratio_error

def tailHeightRatio (d : ℕ) (t u : ℝ) : ℝ := (u/t)^(1/(d:ℝ))

theorem tailHeightRatio_bounds {d : ℕ} {t u : ℝ}
    (hd : 1 ≤ d) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) :
    1 < tailHeightRatio d t u ∧ tailHeightRatio d t u ≤ 2 ∧
      t*(tailHeightRatio d t u)^d=u := by
  have hdp : 0 < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hratio : 0 < u/t := div_pos (ht.trans htu) ht
  have hgt : 1 < u/t := (lt_div_iff₀ ht).mpr (by linarith only [htu])
  have hhi : u/t ≤ 2 := (div_le_iff₀ ht).mpr hu
  have hr : 1 < tailHeightRatio d t u := Real.one_lt_rpow hgt (by positivity)
  have hpow : (tailHeightRatio d t u)^d=u/t := by
    unfold tailHeightRatio
    rw [←Real.rpow_mul_natCast hratio.le]
    rw [show 1/(d:ℝ)*(d:ℝ)=1 by field_simp,Real.rpow_one]
  refine ⟨hr,?_,?_⟩
  · have hh := pow_le_pow_right₀ hr.le hd
    rw [pow_one,hpow] at hh
    exact hh.trans hhi
  · rw [hpow]
    field_simp

/-- The root displacement retains the exact height-difference scale at every order. -/
theorem tailHeightRatio_gap {d : ℕ} {t u : ℝ}
    (hd : 1 ≤ d) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) :
    (u-t)/((d:ℝ)*2^(d-1)) ≤ t*(tailHeightRatio d t u-1) ∧
      t*(tailHeightRatio d t u-1) ≤ (u-t)/(d:ℝ) := by
  obtain ⟨hr,hr2,hpow⟩ := tailHeightRatio_bounds hd ht htu hu
  let r := tailHeightRatio d t u
  have hdp : 0 < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hrp : 0 ≤ r := by dsimp only [r]; linarith only [hr]
  have hr1 : 1 ≤ r := hr.le
  have hpow1 : 1 ≤ r^d := one_le_pow₀ hr1
  have hlower := one_add_mul_sub_le_pow (show -1 ≤ r by linarith only [hr1]) d
  have hupper := abs_pow_sub_pow_le (a:=r) (b:=(1:ℝ)) (n:=d)
  rw [one_pow,abs_of_nonneg (sub_nonneg.mpr hpow1),
    abs_of_nonneg (sub_nonneg.mpr hr1),abs_of_nonneg hrp,abs_one,max_eq_left hr1] at hupper
  have hpower := pow_le_pow_left₀ hrp hr2 (d-1)
  have hupper' := hupper.trans (mul_le_mul_of_nonneg_left hpower (by positivity))
  have hl := mul_le_mul_of_nonneg_left hlower ht.le
  have hu' := mul_le_mul_of_nonneg_left hupper' ht.le
  change t*r^d=u at hpow
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < (d:ℝ)*2^(d-1))).mpr
    nlinarith only [hu',hpow]
  · apply (le_div_iff₀ hdp).mpr
    nlinarith only [hl,hpow]

#print axioms tailHeightRatio_bounds
#print axioms tailHeightRatio_gap

def tailRatioError (d H : ℕ) (N t : ℝ) : ℝ :=
  4*Real.pi*d*(2*N)^d/(t*(H:ℝ)^d)

/-- The original next-to-highest cell supplies the integer label of the fixed-shift phase. -/
theorem tailLogCell_lower_near_integer {k H : ℕ} {t u n m : ℝ}
    (hk : 1 ≤ k) (hn : 0 < n) (hm : 0 < m)
    (hover : (tailLogCell (k+1) H t n ∩ tailLogCell (k+1) H u m).Nonempty) :
    ∃ q : ℤ, |mixedShiftValue (k:ℝ) (t/(2*Real.pi*k))
      (u/(2*Real.pi*k)) (m-n) n-(q:ℝ)| ≤ 2/(H:ℝ)^k := by
  have hcoord := tailLogCell_mixed_coordinate hn hm hover ⟨k-1,by omega⟩
  simp only [show k-1+1=k by omega] at hcoord
  have he : mixedShiftValue (k:ℝ) (t/(2*Real.pi*k)) (u/(2*Real.pi*k)) (m-n) n =
      (t/n^k-u/m^k)/(2*Real.pi*k) := by
    unfold mixedShiftValue
    rw [show n+(m-n)=m by ring,Real.rpow_neg hn.le,Real.rpow_neg hm.le,
      Real.rpow_natCast,Real.rpow_natCast]
    ring
  rw [he]
  exact ⟨round _,hcoord⟩

def tailFixedShiftIndices (S : Finset ℕ) (k H : ℕ) (t u : ℝ) (s : ℕ) : Finset ℕ := by
  classical
  exact S.filter (fun n => n+s∈S ∧
    (tailLogCell (k+1) H t n ∩ tailLogCell (k+1) H u (n+s)).Nonempty)

set_option maxHeartbeats 800000 in
/-- The fixed-shift curvature count consumes actual mixed Taylor-cell overlaps.
All derivative, interval, label and curvature premises are discharged by source entry. -/
theorem tailFixedShiftIndices_card (S : Finset ℕ) {k H s : ℕ} {N T t u : ℝ}
    (hk : 1 ≤ k) (hs : 0 < s) (hN : 0 < N) (ht : 0 < t)
    (htu : t < u) (hu : u ≤ 2*t) (hT : T ≤ N^(k+1))
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : (t/(2*Real.pi*k))*N^(-(k:ℝ)-1)*(((k:ℝ)+1)*2^(k:ℝ))*
      tailRatioError (k+1) H N t ≤
        (t/(2*Real.pi*k))*(s:ℝ)*(2*N)^(-(k:ℝ)-2)/2) :
    let a := t/(2*Real.pi*k)
    let E := tailRatioError (k+1) H N t
    let D := a*N^(-(k:ℝ)-1)*(((k:ℝ)+1)*2^(k:ℝ))*E
    let B := 8*N^2*E/s
    let μ := (k:ℝ)*((k:ℝ)+1)*a*s*(2*N)^(-(k:ℝ)-3)/2
    let η := 2/(H:ℝ)^k
    ((tailFixedShiftIndices S k H t u s).card:ℝ) ≤
      (2*(k:ℝ)*D*B+2*η+1)*(4+4*Real.sqrt (η/μ)) := by
  classical
  let F := tailFixedShiftIndices S k H t u s
  let r := tailHeightRatio (k+1) t u
  let a := t/(2*Real.pi*k)
  let E := tailRatioError (k+1) H N t
  let η := 2/(H:ℝ)^k
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0:ℝ) < k := by linarith only [hkR]
  have hsp : (0:ℝ) < s := by exact_mod_cast hs
  have ha : 0 < a := by dsimp only [a]; positivity
  have hE : 0 ≤ E := by dsimp only [E,tailRatioError]; positivity
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  obtain ⟨hr,hr2,hpow⟩ := tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu
  change 1 < r at hr
  change r ≤ 2 at hr2
  change t*r^(k+1)=u at hpow
  have hpow' : a*r^((k:ℝ)+1)=u/(2*Real.pi*k) := by
    rw [show (k:ℝ)+1=((k+1:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    dsimp only [a]
    rw [div_mul_eq_mul_div,hpow]
  have hsource (n : ℕ) (hn : n∈F) :
      n∈S ∧ n+s∈S ∧
      (tailLogCell (k+1) H t n ∩ tailLogCell (k+1) H u (n+s)).Nonempty :=
    Finset.mem_filter.mp hn
  apply mixedShift_near_integer_card F hkR ha hsp hN hr.le hr2 hE hη hsmall
  · intro n hn
    obtain ⟨hnS,hnsS,_⟩ := hsource n hn
    refine ⟨(hS n hnS).1,?_⟩
    exact_mod_cast (hS (n+s) hnsS).2
  · intro n hn
    obtain ⟨hnS,hnsS,hover⟩ := hsource n hn
    have he := tailLogCell_ratio_error (H:=H) (show 1 ≤ k+1 by omega) hN hT ht
      (ht.trans htu).le htT huT (hS n hnS).1 (hS (n+s) hnsS).1
      (hS (n+s) hnsS).2 hr.le hpow (by simpa only [Nat.cast_add] using hover)
    simpa only [E,tailRatioError,Nat.cast_add] using he
  · intro n hn
    obtain ⟨hnS,hnsS,hover⟩ := hsource n hn
    have he := tailLogCell_lower_near_integer (k:=k) (H:=H) hk (hN.trans_le (hS n hnS).1)
      (hN.trans_le (hS (n+s) hnsS).1) (by simpa only [Nat.cast_add] using hover)
    rw [hpow']
    simpa only [Nat.cast_add,add_sub_cancel_left] using he

#print axioms tailLogCell_lower_near_integer
#print axioms tailFixedShiftIndices_card

/-- The inverse power map is controlled at the actual positive displacement. -/
theorem power_difference_lower {k : ℕ} {p h : ℝ}
    (hk : 1 ≤ k) (hp : 0 ≤ p) (hh : 0 < h) :
    |p-h| * h^(k-1) ≤ |p^k-h^k| := by
  have hb := power_distance_lower k hk (r:=1) (w:=p/h) le_rfl (by positivity)
  rw [one_pow,div_pow,div_sub_one hh.ne',
    div_sub_one (pow_ne_zero k hh.ne'),abs_div,abs_of_pos hh,
    abs_div,abs_of_pos (pow_pos hh k)] at hb
  have hc := (div_le_div_iff₀ hh (pow_pos hh k)).mp hb
  have he : h^k=h^(k-1)*h := by rw [←pow_succ,show k-1+1=k by omega]
  nth_rw 1 [he] at hc
  apply (mul_le_mul_iff_left₀ hh).mp
  nlinarith only [hc]

/-- The stationary product is an exact identity for the original reciprocal phase. -/
theorem stationaryProduct_source {k : ℕ} {t r n m : ℝ}
    (hn : 0 < n) (hm : n < m) :
    (t*r^(k+1)/m^k-t/n^k)*(m-n)^k =
      t*stationaryProduct (k:ℝ) r (m/n) := by
  have hmp : 0 < m := hn.trans hm
  have hratio : 0 < m/n := div_pos hmp hn
  unfold stationaryProduct
  rw [show (k:ℝ)+1=((k+1:ℕ):ℝ) by norm_num,Real.rpow_natCast,
    Real.rpow_neg hratio.le,Real.rpow_natCast,Real.rpow_natCast,
    div_sub_one hn.ne',div_pow,div_pow]
  field_simp

#print axioms power_difference_lower
#print axioms stationaryProduct_source

set_option maxHeartbeats 800000 in
/-- The literal mixed reciprocal phase controls displacement from its stationary
inverse-root curve, with the quadratic ratio error retained. -/
theorem stationary_inverse_root_displacement {k : ℕ} {t r n m q p E : ℝ}
    (hk : 1 ≤ k) (ht : 0 < t) (hn : 0 < n) (hm : n < m)
    (hq : 0 < q) (hp : 0 ≤ p) (hr : 1 < r) (hr2 : r ≤ 2)
    (hm2 : m/n ≤ 2) (hmgap : m/n-1 ≤ 2*(r-1))
    (hpq : p^k=t*(r-1)^(k+1)/q)
    (hres : |t*r^(k+1)/m^k-t/n^k-q| ≤ E) :
    |p-(m-n)| ≤
      t*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*(r-1)^(k-1)*(m/n-r)^2 /
        (q*(m-n)^(k-1)) + E*(m-n)/q := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hD : 0 < m-n := sub_pos.mpr hm
  have hw : 1 < m/n := (lt_div_iff₀ hn).mpr (by linarith only [hm])
  have hquad := stationaryProduct_quadratic_error hkR hr hr2 hw hm2 hmgap
  have hkminus : (k:ℝ)-1=((k-1:ℕ):ℝ) := by rw [Nat.cast_sub hk]; norm_num
  rw [show (k:ℝ)+1=((k+1:ℕ):ℝ) by norm_num,Real.rpow_natCast,
    hkminus,Real.rpow_natCast] at hquad
  let A := t*r^(k+1)/m^k-t/n^k
  let M := t*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*(r-1)^(k-1)*(m/n-r)^2
  have hstationary := stationaryProduct_source (k:=k) (t:=t) (r:=r) hn hm
  have hqp : q*p^k=t*(r-1)^(k+1) := by
    have he := (eq_div_iff hq.ne').mp hpq
    nlinarith only [he]
  have hid : q*(p^k-(m-n)^k) =
      t*((r-1)^(k+1)-stationaryProduct (k:ℝ) r (m/n))+(A-q)*(m-n)^k := by
    dsimp only [A]
    nlinarith only [hstationary,hqp]
  have hmain : |t*((r-1)^(k+1)-stationaryProduct (k:ℝ) r (m/n))| ≤ M := by
    rw [abs_mul,abs_of_pos ht,abs_sub_comm]
    have hh := mul_le_mul_of_nonneg_left hquad ht.le
    convert hh using 1
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  have habs : |q*(p^k-(m-n)^k)| ≤ M+E*(m-n)^k := by
    rw [hid]
    apply (abs_add_le _ _).trans (add_le_add hmain _)
    rw [abs_mul,abs_of_pos (pow_pos hD k)]
    exact mul_le_mul_of_nonneg_right hres (pow_nonneg hD.le k)
  have hlower := mul_le_mul_of_nonneg_left (power_difference_lower hk hp hD) hq.le
  rw [abs_mul,abs_of_pos hq] at habs
  have hfrac : |p-(m-n)| ≤ (M+E*(m-n)^k)/(q*(m-n)^(k-1)) := by
    apply (le_div_iff₀ (mul_pos hq (pow_pos hD (k-1)))).mpr
    nlinarith only [hlower,habs]
  convert hfrac using 1
  have he : (m-n)^k=(m-n)^(k-1)*(m-n) := by rw [←pow_succ,show k-1+1=k by omega]
  rw [he]
  dsimp only [M]
  field_simp

#print axioms stationary_inverse_root_displacement

def reciprocalRoot (k A x : ℝ) : ℝ := A*x^(-1/k)

def reciprocalRootNearIntegers (k A Q : ℝ) (N : ℕ) (η : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun n =>
    GafniTao.heathBrownDistanceToInteger (reciprocalRoot k A (Q+n)) ≤ η)

theorem reciprocalRoot_derivative (k A : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (reciprocalRoot k A) (-(A/k)*x^(-1/k-1)) x := by
  convert (Real.hasDerivAt_rpow_const
    (p:=-1/k) (Or.inl hx.ne')).const_mul A using 1
  ring

theorem reciprocalRoot_second_derivative {k : ℝ} (hk : 0 < k) (A : ℝ)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(A/k)*x^(-1/k-1))
      (A*(k+1)/k^2*x^(-1/k-2)) x := by
  convert (Real.hasDerivAt_rpow_const
    (p:=-1/k-1) (Or.inl hx.ne')).const_mul (-(A/k)) using 1
  rw [show -1/k-1-1=-1/k-2 by ring]
  field_simp
  ring

theorem reciprocalRoot_curvature_bounds {k A Q x : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hQ : 0 < Q) (hx : x∈Set.Icc Q (2*Q)) :
    let μ := A*(k+1)/k^2*(2*Q)^(-1/k-2)
    μ ≤ A*(k+1)/k^2*x^(-1/k-2) ∧
      A*(k+1)/k^2*x^(-1/k-2) ≤ 8*μ := by
  intro μ
  have hkp : 0 < k := by linarith only [hk]
  have hxpos : 0 < x := hQ.trans_le hx.1
  have hexp : -1/k-2 ≤ 0 := by
    have hp : -1/k ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hkp.le
    linarith only [hp]
  have hpow : Q^(-1/k-2) ≤ 8*(2*Q)^(-1/k-2) := by
    have he : Q^(-1/k-2)= (2:ℝ)^(1/k+2)*(2*Q)^(-1/k-2) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hQ.le,
        ←mul_assoc,←Real.rpow_add (by norm_num : (0:ℝ) < 2),
        show 1/k+2+(-1/k-2)=(0:ℝ) by ring,Real.rpow_zero,one_mul]
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      (2:ℝ)^(1/k+2) ≤ (2:ℝ)^(3:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by have hh : 1/k ≤ 1 := (div_le_one hkp).mpr hk; linarith only [hh])
      _ = 8 := by norm_num
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hxpos hx.2 hexp) (by positivity)
  · have hp := Real.rpow_le_rpow_of_nonpos hQ hx.1 hexp
    have hh := mul_le_mul_of_nonneg_left (hp.trans hpow)
      (by positivity : 0 ≤ A*(k+1)/k^2)
    dsimp only [μ]
    nlinarith only [hh]

/-- Every general-order reciprocal-root label curve has a proved curvature-saving count. -/
theorem reciprocalRootNearIntegers_card {k A Q η : ℝ} {N : ℕ}
    (hk : 1 ≤ k) (hA : 0 < A) (hQ : 0 < Q) (hN : (N:ℝ) ≤ Q) (hη : 0 ≤ η) :
    let μ := A*(k+1)/k^2*(2*Q)^(-1/k-2)
    ((reciprocalRootNearIntegers k A Q N η).card:ℝ) ≤
      1204*((N:ℝ)*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
  intro μ
  have hkp : 0 < k := by linarith only [hk]
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hdom x (hx : x∈Set.Icc Q (Q+N)) : x∈Set.Icc Q (2*Q) :=
    ⟨hx.1,by linarith only [hx.2,hN]⟩
  have hh := positive_second_derivative_count_optimized
    (reciprocalRoot k A) (fun x => -(A/k)*x^(-1/k-1))
    (fun x => A*(k+1)/k^2*x^(-1/k-2)) Q N
    (reciprocalRootNearIntegers k A Q N η) (C:=8) (by norm_num) hμ hη
    (fun x hx => reciprocalRoot_derivative k A (hQ.trans_le hx.1))
    (fun x hx => reciprocalRoot_second_derivative hkp A (hQ.trans_le hx.1))
    (fun x hx => (reciprocalRoot_curvature_bounds hk hA hQ (hdom x hx)).1)
    (fun x hx => (reciprocalRoot_curvature_bounds hk hA hQ (hdom x hx)).2)
    (Finset.filter_subset _ _) (fun n hn =>
      ⟨round (reciprocalRoot k A (Q+n)), (Finset.mem_filter.mp hn).2⟩)
  norm_num only [show (52:ℝ)+144*8=1204 by norm_num] at hh
  simpa only [neg_div] using hh

#print axioms reciprocalRoot_derivative
#print axioms reciprocalRoot_second_derivative
#print axioms reciprocalRoot_curvature_bounds
#print axioms reciprocalRootNearIntegers_card

def tailLogLabel (k : ℕ) (t u n m : ℝ) : ℤ :=
  round ((u/m^k-t/n^k)/(2*Real.pi*k))

theorem tailLogCell_label_error {k H : ℕ} {t u n m : ℝ}
    (hk : 1 ≤ k) (hn : 0 < n) (hm : 0 < m)
    (hover : (tailLogCell (k+1) H t n ∩ tailLogCell (k+1) H u m).Nonempty) :
    |u/m^k-t/n^k-2*Real.pi*k*(tailLogLabel k t u n m:ℝ)| ≤
      4*Real.pi*k/(H:ℝ)^k := by
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hcoord := tailLogCell_mixed_coordinate hn hm hover ⟨k-1,by omega⟩
  simp only [show k-1+1=k by omega] at hcoord
  have he : (t/n^k-u/m^k)/(2*Real.pi*k) = -((u/m^k-t/n^k)/(2*Real.pi*k)) := by ring
  rw [he,GafniTao.heathBrownDistanceToInteger_neg] at hcoord
  have hh := mul_le_mul_of_nonneg_left hcoord (by positivity : 0 ≤ 2*Real.pi*k)
  change 2*Real.pi*k*|(u/m^k-t/n^k)/(2*Real.pi*k)-
    (tailLogLabel k t u n m:ℝ)| ≤ _ at hh
  have he' : u/m^k-t/n^k-2*Real.pi*k*(tailLogLabel k t u n m:ℝ) =
      (2*Real.pi*k)*((u/m^k-t/n^k)/(2*Real.pi*k)-(tailLogLabel k t u n m:ℝ)) := by field_simp
  rw [he',abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi*k)]
  convert hh using 1
  ring

def tailStationaryAmplitude (k : ℕ) (t u : ℝ) : ℝ :=
  (t*(tailHeightRatio (k+1) t u-1)^(k+1)/(2*Real.pi*k))^(1/(k:ℝ))

theorem tailStationaryAmplitude_pos {k : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) :
    0 < tailStationaryAmplitude k t u := by
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hr := (tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu).1
  unfold tailStationaryAmplitude
  apply Real.rpow_pos_of_pos
  positivity

theorem tailStationaryCurve_power {k : ℕ} {t u q : ℝ}
    (hk : 1 ≤ k) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) (hq : 0 < q) :
    (reciprocalRoot (k:ℝ) (tailStationaryAmplitude k t u) q)^k =
      t*(tailHeightRatio (k+1) t u-1)^(k+1)/(2*Real.pi*k*q) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hr := (tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu).1
  have hbase : 0 < t*(tailHeightRatio (k+1) t u-1)^(k+1)/(2*Real.pi*k) := by positivity
  unfold reciprocalRoot tailStationaryAmplitude
  rw [mul_pow,←Real.rpow_mul_natCast hbase.le,←Real.rpow_mul_natCast hq.le,
    show 1/(k:ℝ)*(k:ℝ)=1 by field_simp,
    show -1/(k:ℝ)*(k:ℝ)= -1 by field_simp,Real.rpow_one,Real.rpow_neg_one]
  ring

#print axioms tailLogCell_label_error
#print axioms tailStationaryAmplitude_pos
#print axioms tailStationaryCurve_power

/-- The original mixed-cell coordinates put the actual integer shift near its
general-order stationary curve; the retained error is genuinely quadratic. -/
theorem tailLogCell_stationary_near_integer {k H : ℕ} {N T t u n m : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hm : N ≤ m) (hmN : m ≤ 2*N)
    (hsmall : tailRatioError (k+1) H N t ≤ (tailHeightRatio (k+1) t u-1)/2)
    (hq : 0 < (tailLogLabel k t u n m:ℝ))
    (hover : (tailLogCell (k+1) H t n ∩ tailLogCell (k+1) H u m).Nonempty) :
    let r := tailHeightRatio (k+1) t u
    let q : ℝ := tailLogLabel k t u n m
    |reciprocalRoot (k:ℝ) (tailStationaryAmplitude k t u) q-(m-n)| ≤
      t*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*(r-1)^(k-1)*
        (tailRatioError (k+1) H N t)^2/(2*Real.pi*k*q*(m-n)^(k-1))+
      2*(m-n)/((H:ℝ)^k*q) := by
  let r := tailHeightRatio (k+1) t u
  let q : ℝ := tailLogLabel k t u n m
  let E := tailRatioError (k+1) H N t
  have hnp : 0 < n := hN.trans_le hn
  have hmp : 0 < m := hN.trans_le hm
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨hr,hr2,hpow⟩ := tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu
  change 1 < r at hr
  change r ≤ 2 at hr2
  change t*r^(k+1)=u at hpow
  have herr : |m/n-r| ≤ E :=
    tailLogCell_ratio_error (show 1 ≤ k+1 by omega) hN hT ht (ht.trans htu).le
      htT huT hn hm hmN hr.le hpow hover
  have hE : 0 ≤ E := (abs_nonneg _).trans herr
  change E ≤ (r-1)/2 at hsmall
  have hmgt : n < m := by
    have hlo : 1 < m/n := by linarith only [(abs_le.mp herr).1,hsmall,hr]
    have hh := (lt_div_iff₀ hnp).mp hlo
    linarith only [hh]
  have hw2 : m/n ≤ 2 := (div_le_iff₀ hnp).mpr (by linarith only [hmN,hn])
  have hgap : m/n-1 ≤ 2*(r-1) := by linarith only [(abs_le.mp herr).2,hsmall,hr]
  have hres := tailLogCell_label_error hk hnp hmp hover
  nth_rw 1 [←hpow] at hres
  have hp : 0 ≤ reciprocalRoot (k:ℝ) (tailStationaryAmplitude k t u) q := by
    unfold reciprocalRoot
    exact mul_nonneg (tailStationaryAmplitude_pos hk ht htu hu).le (Real.rpow_nonneg hq.le _)
  have hpq : (reciprocalRoot (k:ℝ) (tailStationaryAmplitude k t u) q)^k =
      t*(r-1)^(k+1)/(2*Real.pi*k*q) := tailStationaryCurve_power hk ht htu hu hq
  have hh := stationary_inverse_root_displacement hk ht hnp hmgt
    (by positivity : 0 < 2*Real.pi*k*q) hp hr hr2 hw2 hgap hpq hres
  have hsquare : (m/n-r)^2 ≤ E^2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) herr 2
    simpa only [sq_abs] using hs
  apply hh.trans
  apply add_le_add
  · gcongr
  · change (4*Real.pi*k/(H:ℝ)^k)*(m-n)/(2*Real.pi*k*q) ≤
      2*(m-n)/((H:ℝ)^k*q)
    apply le_of_eq
    field_simp
    ring

#print axioms tailLogCell_stationary_near_integer

/-- The actual ordered index shift lies at the stationary ratio scale. -/
theorem tailLogCell_shift_bounds {k H : ℕ} {N T t u n m : ℝ}
    (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hnN : n ≤ 2*N) (hm : N ≤ m) (hmN : m ≤ 2*N)
    (hsmall : tailRatioError (k+1) H N t ≤ (tailHeightRatio (k+1) t u-1)/2)
    (hover : (tailLogCell (k+1) H t n ∩ tailLogCell (k+1) H u m).Nonempty) :
    N*(tailHeightRatio (k+1) t u-1)/2 ≤ m-n ∧
      m-n ≤ 4*N*(tailHeightRatio (k+1) t u-1) := by
  let r := tailHeightRatio (k+1) t u
  have hnp : 0 < n := hN.trans_le hn
  obtain ⟨hr,_,hpow⟩ := tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu
  have herr := tailLogCell_ratio_error (show 1 ≤ k+1 by omega) hN hT ht
    (ht.trans htu).le htT huT hn hm hmN hr.le hpow hover
  change |m/n-r| ≤ tailRatioError (k+1) H N t at herr
  change tailRatioError (k+1) H N t ≤ (r-1)/2 at hsmall
  change 1 < r at hr
  have hb : 0 ≤ r-1 := by linarith only [hr]
  have hlo : 1+(r-1)/2 ≤ m/n := by linarith only [(abs_le.mp herr).1,hsmall]
  have hhi : m/n ≤ 1+2*(r-1) := by linarith only [(abs_le.mp herr).2,hsmall,hb]
  have hlo' := (le_div_iff₀ hnp).mp hlo
  have hhi' := (div_le_iff₀ hnp).mp hhi
  have hNb := mul_le_mul_of_nonneg_right hn hb
  have hnB := mul_le_mul_of_nonneg_right hnN hb
  constructor <;> nlinarith only [hlo',hhi',hNb,hnB]

#print axioms tailLogCell_shift_bounds

set_option maxHeartbeats 800000 in
/-- Actual far-cell labels are positive and occupy their physical height-difference scale. -/
theorem tailLogCell_label_bounds {k H : ℕ} {N T t u n m : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hm : N ≤ m) (hmN : m ≤ 2*N)
    (hsmall : (k:ℝ)*2^(k-1)*tailRatioError (k+1) H N t ≤
      (tailHeightRatio (k+1) t u-1)/2)
    (hround : 4*Real.pi*k/(H:ℝ)^k ≤
      t*(tailHeightRatio (k+1) t u-1)/(4*(2*N)^k))
    (hover : (tailLogCell (k+1) H t n ∩ tailLogCell (k+1) H u m).Nonempty) :
    t*(tailHeightRatio (k+1) t u-1)/(4*(2*N)^k) ≤
      2*Real.pi*k*(tailLogLabel k t u n m:ℝ) ∧
    2*Real.pi*k*(tailLogLabel k t u n m:ℝ) ≤
      t*(2^k+1)*(tailHeightRatio (k+1) t u-1)/N^k := by
  let r := tailHeightRatio (k+1) t u
  let w := m/n
  let b := r-1
  let E := tailRatioError (k+1) H N t
  have hnp : 0 < n := hN.trans_le hn
  have hmp : 0 < m := hN.trans_le hm
  obtain ⟨hr,hr2,hpow⟩ := tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu
  change 1 < r at hr
  change r ≤ 2 at hr2
  change t*r^(k+1)=u at hpow
  have hrp : 0 ≤ r := by linarith only [hr]
  have hb : 0 < b := by dsimp only [b]; linarith only [hr]
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hw2 : w ≤ 2 := (div_le_iff₀ hnp).mpr (by linarith only [hmN,hn])
  have herr : |w-r| ≤ E := tailLogCell_ratio_error (show 1 ≤ k+1 by omega)
    hN hT ht (ht.trans htu).le htT huT hn hm hmN hr.le hpow hover
  have hE : 0 ≤ E := (abs_nonneg _).trans herr
  have hpower : |w^k-r^k| ≤ b/2 := by
    have hh := abs_pow_sub_pow_le (a:=w) (b:=r) (n:=k)
    rw [abs_of_nonneg hw,abs_of_nonneg hrp] at hh
    calc
      _ ≤ |w-r| * (k:ℝ)*(max w r)^(k-1) := hh
      _ ≤ E*(k:ℝ)*2^(k-1) := by gcongr; exact max_le hw2 hr2
      _ ≤ _ := by dsimp only [E,b] at *; nlinarith only [hsmall]
  have hrklo : 1 ≤ r^k := one_le_pow₀ hr.le
  have hrkhi : r^k ≤ (2:ℝ)^k := pow_le_pow_left₀ hrp hr2 k
  have hid : r^(k+1)-w^k = r^k*b+(r^k-w^k) := by
    dsimp only [b]
    rw [pow_succ]
    ring
  have hnumlo : b/2 ≤ r^(k+1)-w^k := by
    rw [hid]
    nlinarith only [(abs_le.mp hpower).2,mul_le_mul_of_nonneg_right hrklo hb.le]
  have hnumhi : r^(k+1)-w^k ≤ ((2:ℝ)^k+1/2)*b := by
    rw [hid]
    nlinarith only [(abs_le.mp hpower).1,mul_le_mul_of_nonneg_right hrkhi hb.le]
  have hnum : 0 ≤ r^(k+1)-w^k := by linarith only [hb,hnumlo]
  have he : u/m^k-t/n^k=t*(r^(k+1)-w^k)/m^k := by
    rw [←hpow]
    dsimp only [w]
    rw [div_pow]
    field_simp
  have hlo : t*b/(2*(2*N)^k) ≤ u/m^k-t/n^k := by
    rw [he]
    calc
      _ = t*(b/2)/(2*N)^k := by ring
      _ ≤ _ := by gcongr
  have hhi : u/m^k-t/n^k ≤ t*((2:ℝ)^k+1/2)*b/N^k := by
    rw [he]
    calc
      _ ≤ t*(((2:ℝ)^k+1/2)*b)/N^k := by gcongr
      _ = _ := by ring
  have hres := tailLogCell_label_error hk hnp hmp hover
  change 4*Real.pi*k/(H:ℝ)^k ≤ t*b/(4*(2*N)^k) at hround
  have hround' : 4*Real.pi*k/(H:ℝ)^k ≤ t*b/(4*N^k) := by
    apply hround.trans
    gcongr
    linarith only [hN]
  change t*b/(4*(2*N)^k) ≤ _ ∧ _ ≤ t*(2^k+1)*b/N^k
  have hpos : 0 ≤ t*b/N^k := by positivity
  constructor
  · have he' : t*b/(2*(2*N)^k)=2*(t*b/(4*(2*N)^k)) := by ring
    rw [he'] at hlo
    linarith only [hlo,(abs_le.mp hres).2,hround]
  · have he' : t*((2:ℝ)^k+1/2)*b/N^k+t*b/(4*N^k) ≤ t*(2^k+1)*b/N^k := by
      ring_nf at hpos ⊢
      linarith only [hpos]
    linarith only [hhi,(abs_le.mp hres).1,hround',he']

#print axioms tailLogCell_label_bounds

/-- General-order reciprocal-root curvature on a whole bounded-ratio label interval. -/
theorem reciprocalRoot_curvature_bounds_wide {k A Q L x : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hQ : 0 < Q) (hL : 1 ≤ L)
    (hx : x∈Set.Icc Q (L*Q)) :
    let μ := A*(k+1)/k^2*(L*Q)^(-1/k-2)
    μ ≤ A*(k+1)/k^2*x^(-1/k-2) ∧
      A*(k+1)/k^2*x^(-1/k-2) ≤ L^3*μ := by
  intro μ
  have hkp : 0 < k := by linarith only [hk]
  have hLp : 0 < L := by linarith only [hL]
  have hxpos : 0 < x := hQ.trans_le hx.1
  have hexp : -1/k-2 ≤ 0 := by
    have hp : -1/k ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hkp.le
    linarith only [hp]
  have hpow : Q^(-1/k-2) ≤ L^3*(L*Q)^(-1/k-2) := by
    have he : Q^(-1/k-2)=L^(1/k+2)*(L*Q)^(-1/k-2) := by
      rw [Real.mul_rpow hLp.le hQ.le,←mul_assoc,←Real.rpow_add hLp,
        show 1/k+2+(-1/k-2)=(0:ℝ) by ring,Real.rpow_zero,one_mul]
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      L^(1/k+2) ≤ L^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hL
        (by have hh : 1/k ≤ 1 := (div_le_one hkp).mpr hk; linarith only [hh])
      _ = L^3 := by norm_cast
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hxpos hx.2 hexp) (by positivity)
  · have hp := Real.rpow_le_rpow_of_nonpos hQ hx.1 hexp
    have hh := mul_le_mul_of_nonneg_left (hp.trans hpow)
      (by positivity : 0 ≤ A*(k+1)/k^2)
    dsimp only [μ]
    nlinarith only [hh]

/-- A single bounded-ratio label interval suffices; no growing family of dyadic labels is needed. -/
theorem reciprocalRootNearIntegers_card_wide {k A Q L η : ℝ} {N : ℕ}
    (hk : 1 ≤ k) (hA : 0 < A) (hQ : 0 < Q) (hL : 1 ≤ L)
    (hN : Q+(N:ℝ) ≤ L*Q) (hη : 0 ≤ η) :
    let μ := A*(k+1)/k^2*(L*Q)^(-1/k-2)
    ((reciprocalRootNearIntegers k A Q N η).card:ℝ) ≤
      (52+144*L^3)*((N:ℝ)*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
  intro μ
  have hkp : 0 < k := by linarith only [hk]
  have hLp : 0 < L := by linarith only [hL]
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hdom x (hx : x∈Set.Icc Q (Q+N)) : x∈Set.Icc Q (L*Q) :=
    ⟨hx.1,hx.2.trans hN⟩
  have hh := positive_second_derivative_count_optimized
    (reciprocalRoot k A) (fun x => -(A/k)*x^(-1/k-1))
    (fun x => A*(k+1)/k^2*x^(-1/k-2)) Q N
    (reciprocalRootNearIntegers k A Q N η) (C:=L^3) (one_le_pow₀ hL) hμ hη
    (fun x hx => reciprocalRoot_derivative k A (hQ.trans_le hx.1))
    (fun x hx => reciprocalRoot_second_derivative hkp A (hQ.trans_le hx.1))
    (fun x hx => (reciprocalRoot_curvature_bounds_wide hk hA hQ hL (hdom x hx)).1)
    (fun x hx => (reciprocalRoot_curvature_bounds_wide hk hA hQ hL (hdom x hx)).2)
    (Finset.filter_subset _ _) (fun n hn =>
      ⟨round (reciprocalRoot k A (Q+n)), (Finset.mem_filter.mp hn).2⟩)
  simpa only [neg_div] using hh

#print axioms reciprocalRoot_curvature_bounds_wide
#print axioms reciprocalRootNearIntegers_card_wide

def tailCurveError (k H : ℕ) (N t u q : ℝ) : ℝ :=
  t*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*2^(k-1)*
    (tailRatioError (k+1) H N t)^2/(2*Real.pi*k*q*N^(k-1))+
  8*N*(tailHeightRatio (k+1) t u-1)/((H:ℝ)^k*q)

/-- The actual stationary error is uniform over both source indices. -/
theorem tailLogCell_stationary_uniform_error {k H : ℕ} {N T t u n m : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hnN : n ≤ 2*N) (hm : N ≤ m) (hmN : m ≤ 2*N)
    (hsmall : tailRatioError (k+1) H N t ≤ (tailHeightRatio (k+1) t u-1)/2)
    (hq : 0 < (tailLogLabel k t u n m:ℝ))
    (hover : (tailLogCell (k+1) H t n ∩ tailLogCell (k+1) H u m).Nonempty) :
    |reciprocalRoot (k:ℝ) (tailStationaryAmplitude k t u) (tailLogLabel k t u n m)-(m-n)| ≤
      tailCurveError k H N t u (tailLogLabel k t u n m) := by
  let b := tailHeightRatio (k+1) t u-1
  let q : ℝ := tailLogLabel k t u n m
  let E := tailRatioError (k+1) H N t
  let K := (k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1)
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hr := (tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu).1
  have hb : 0 < b := by dsimp only [b]; linarith only [hr]
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hh := tailLogCell_stationary_near_integer hk hN ht htu hu hT htT huT hn hm hmN hsmall hq hover
  have hshift := tailLogCell_shift_bounds hN ht htu hu hT htT huT hn hnN hm hmN hsmall hover
  change N*b/2 ≤ m-n ∧ m-n ≤ 4*N*b at hshift
  change _ ≤ t*K*b^(k-1)*E^2/(2*Real.pi*k*q*(m-n)^(k-1))+
    2*(m-n)/((H:ℝ)^k*q) at hh
  change _ ≤ t*K*2^(k-1)*E^2/(2*Real.pi*k*q*N^(k-1))+8*N*b/((H:ℝ)^k*q)
  apply hh.trans
  apply add_le_add
  · calc
      _ ≤ t*K*b^(k-1)*E^2/(2*Real.pi*k*q*(N*b/2)^(k-1)) := by gcongr; exact hshift.1
      _ = _ := by
        rw [div_pow,mul_pow]
        field_simp
  · calc
      _ ≤ 2*(4*N*b)/((H:ℝ)^k*q) := by gcongr; exact hshift.2
      _ = _ := by ring

/-- With the derived uniform curve error below half an integer, equal actual labels
force equal integer shifts; no spacing or uniqueness premise is supplied. -/
theorem tailLogCell_same_label_same_shift {k H n m n' m' : ℕ} {N T t u : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ (n:ℝ)) (hnN : (n:ℝ) ≤ 2*N) (hm : N ≤ (m:ℝ)) (hmN : (m:ℝ) ≤ 2*N)
    (hn' : N ≤ (n':ℝ)) (hnN' : (n':ℝ) ≤ 2*N) (hm' : N ≤ (m':ℝ)) (hmN' : (m':ℝ) ≤ 2*N)
    (hsmall : tailRatioError (k+1) H N t ≤ (tailHeightRatio (k+1) t u-1)/2)
    (hq : 0 < (tailLogLabel k t u n m:ℝ))
    (heq : tailLogLabel k t u n m = tailLogLabel k t u n' m')
    (herror : tailCurveError k H N t u (tailLogLabel k t u n m) < 1/2)
    (hover : (tailLogCell (k+1) H t n ∩ tailLogCell (k+1) H u m).Nonempty)
    (hover' : (tailLogCell (k+1) H t n' ∩ tailLogCell (k+1) H u m').Nonempty) :
    (m:ℤ)-n=(m':ℤ)-n' := by
  have h₁ := tailLogCell_stationary_uniform_error hk hN ht htu hu hT htT huT hn hnN hm hmN hsmall hq hover
  have hq' : 0 < (tailLogLabel k t u n' m':ℝ) := by simpa only [heq] using hq
  have h₂ := tailLogCell_stationary_uniform_error hk hN ht htu hu hT htT huT hn' hnN' hm' hmN' hsmall hq' hover'
  rw [←heq] at h₂
  have hdist : |((m:ℝ)-n)-((m':ℝ)-n')| < 1 := by
    have hh := abs_sub_le ((m:ℝ)-n)
      (reciprocalRoot (k:ℝ) (tailStationaryAmplitude k t u) (tailLogLabel k t u n m))
      ((m':ℝ)-n')
    rw [abs_sub_comm ((m:ℝ)-n)
      (reciprocalRoot (k:ℝ) (tailStationaryAmplitude k t u) (tailLogLabel k t u n m))] at hh
    linarith only [hh,h₁,h₂,herror]
  have hi : |((m:ℤ)-n)-((m':ℤ)-n')| < 1 := by exact_mod_cast hdist
  have hlohi := abs_lt.mp hi
  omega

#print axioms tailLogCell_stationary_uniform_error
#print axioms tailLogCell_same_label_same_shift

def tailMixedPairs (S : Finset ℕ) (k H : ℕ) (t u : ℝ) : Finset (ℕ×ℕ) := by
  classical
  exact (S×ˢS).filter (fun p =>
    (tailLogCell (k+1) H t p.1 ∩ tailLogCell (k+1) H u p.2).Nonempty)

def tailLabelPairs (S : Finset ℕ) (k H : ℕ) (t u : ℝ) (q : ℤ) : Finset (ℕ×ℕ) := by
  classical
  exact (tailMixedPairs S k H t u).filter (fun p => tailLogLabel k t u p.1 p.2=q)

set_option maxHeartbeats 1000000 in
/-- A same-label fibre of the literal mixed overlap set has a derived short-interval count. -/
theorem tailLabelPairs_card (S : Finset ℕ) {k H : ℕ} {N T t u : ℝ} {q : ℤ}
    (hk : 1 ≤ k) (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : tailRatioError (k+1) H N t ≤ (tailHeightRatio (k+1) t u-1)/2)
    (hq : 0 < (q:ℝ)) (herror : tailCurveError k H N t u q < 1/2) :
    ((tailLabelPairs S k H t u q).card:ℝ) ≤
      1+32*N*tailRatioError (k+1) H N t/(tailHeightRatio (k+1) t u-1) := by
  classical
  let F := tailLabelPairs S k H t u q
  let r := tailHeightRatio (k+1) t u
  let b := r-1
  let E := tailRatioError (k+1) H N t
  let D := 16*N*E/b
  obtain ⟨hr,_,hpow⟩ := tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu
  have hb : 0 < b := by dsimp only [b,r]; linarith only [hr]
  have hE : 0 ≤ E := by dsimp only [E,tailRatioError]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hspec (p : ℕ×ℕ) (hp : p∈F) : p.1∈S ∧ p.2∈S ∧
      (tailLogCell (k+1) H t p.1 ∩ tailLogCell (k+1) H u p.2).Nonempty ∧
      tailLogLabel k t u p.1 p.2=q := by
    obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hover⟩ := Finset.mem_filter.mp hp
    obtain ⟨hn,hm⟩ := Finset.mem_product.mp hp
    exact ⟨hn,hm,hover,hl⟩
  have hsame (p : ℕ×ℕ) (hp : p∈F) (p' : ℕ×ℕ) (hp' : p'∈F) :
      (p.2:ℤ)-p.1=(p'.2:ℤ)-p'.1 := by
    obtain ⟨hn,hm,hover,hl⟩ := hspec p hp
    obtain ⟨hn',hm',hover',hl'⟩ := hspec p' hp'
    exact tailLogCell_same_label_same_shift hk hN ht htu hu hT htT huT
      (hS _ hn).1 (hS _ hn).2 (hS _ hm).1 (hS _ hm).2
      (hS _ hn').1 (hS _ hn').2 (hS _ hm').1 (hS _ hm').2 hsmall
      (by simpa only [hl] using hq) (hl.trans hl'.symm)
      (by simpa only [hl] using herror) hover hover'
  by_cases hF : F.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hF
    obtain ⟨hn₀,hm₀,hover₀,_⟩ := hspec p₀ hp₀
    let J : Finset ℤ := F.image (fun p => (p.1:ℤ))
    have hcard : J.card=F.card := by
      apply Finset.card_image_iff.mpr
      intro p hp p' hp' he
      change (p.1:ℤ)=(p'.1:ℤ) at he
      have hfst : p.1=p'.1 := by exact_mod_cast he
      have hshift := hsame p hp p' hp'
      have hsnd : p.2=p'.2 := by omega
      exact Prod.ext hfst hsnd
    have hbound := integer_card_le_of_abs_sub_le J (a:=(p₀.1:ℝ)) hD (by
      intro z hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hn,hm,hover,_⟩ := hspec p hp
      let h : ℝ := (p₀.2:ℝ)-p₀.1
      have hshift : (p.2:ℝ)-p.1=(p₀.2:ℝ)-p₀.1 := by exact_mod_cast hsame p hp p₀ hp₀
      have hscale := tailLogCell_shift_bounds hN ht htu hu hT htT huT
        (hS _ hn₀).1 (hS _ hn₀).2 (hS _ hm₀).1 (hS _ hm₀).2 hsmall hover₀
      change N*b/2 ≤ h ∧ h ≤ 4*N*b at hscale
      have hpos : 0 < h := lt_of_lt_of_le (by positivity) hscale.1
      have he₁ := tailLogCell_ratio_error (show 1 ≤ k+1 by omega) hN hT ht (ht.trans htu).le
        htT huT (hS _ hn).1 (hS _ hm).1 (hS _ hm).2 hr.le hpow hover
      have he₀ := tailLogCell_ratio_error (show 1 ≤ k+1 by omega) hN hT ht (ht.trans htu).le
        htT huT (hS _ hn₀).1 (hS _ hm₀).1 (hS _ hm₀).2 hr.le hpow hover₀
      have hmshift : (p.1:ℝ)+h=p.2 := by dsimp only [h]; linarith only [hshift]
      have hmshift₀ : (p₀.1:ℝ)+h=p₀.2 := by dsimp only [h]; ring
      have hd := fixed_shift_diameter (h:=h) (r:=r) hN hpos
        (hS _ hn).1 (hS _ hn).2 (hS _ hn₀).1 (hS _ hn₀).2
        (by simpa only [hmshift] using he₁) (by simpa only [hmshift₀] using he₀)
      have hd' : 8*N^2*E/h ≤ D := by
        calc
          _ ≤ 8*N^2*E/(N*b/2) := by gcongr; exact hscale.1
          _ = D := by dsimp only [D]; field_simp; ring
      simpa only [Int.cast_natCast] using hd.trans hd')
    rw [hcard] at hbound
    convert hbound using 1
    dsimp only [D,E,b,r]
    ring
  · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card:ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    change 0 ≤ 1+32*N*E/b
    positivity

#print axioms tailLabelPairs_card

set_option maxHeartbeats 800000 in
/-- The curvature count on an arbitrary finite set of integer labels, with exact
ceiling and translation losses rather than a separate dyadic-label family. -/
theorem reciprocalRoot_integer_set_card (I : Finset ℤ) {k A Q R L η : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hQ : 1 ≤ Q) (hQR : Q ≤ R) (hL : 1 ≤ L)
    (hwindow : R+4 ≤ L*Q) (hη : 0 ≤ η)
    (hI : ∀ q∈I, Q ≤ (q:ℝ) ∧ (q:ℝ) ≤ R)
    (hnear : ∀ q∈I, ∃ z : ℤ, |reciprocalRoot k A q-(z:ℝ)| ≤ η) :
    let a : ℝ := Int.ceil Q
    let μ := A*(k+1)/k^2*(L*a)^(-1/k-2)
    (I.card:ℝ) ≤ (52+144*L^3)*((R+3)*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
  classical
  let a : ℤ := Int.ceil Q
  let M := Nat.ceil (R-Q)+2
  let J := I.image (fun q => (q-a).toNat)
  have haQ : Q ≤ (a:ℝ) := Int.le_ceil Q
  have hap : (0:ℝ) < a := lt_of_lt_of_le (by linarith only [hQ]) haQ
  have haUp : (a:ℝ) ≤ Q+1 := (Int.ceil_lt_add_one Q).le
  have hM : (M:ℝ) ≤ R-Q+3 := by
    have hh := (Nat.ceil_lt_add_one (sub_nonneg.mpr hQR)).le
    dsimp only [M]
    push_cast
    linarith only [hh]
  have hdom : (a:ℝ)+M ≤ L*(a:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left haQ (by linarith only [hL] : 0 ≤ L)
    linarith only [haUp,hM,hwindow,hh]
  have hqa (q : ℤ) (hq : q∈I) : a ≤ q := Int.ceil_le.mpr (hI q hq).1
  have hcast (q : ℤ) (hq : q∈I) : (a:ℝ)+((q-a).toNat:ℝ)=(q:ℝ) := by
    have hh := Int.toNat_of_nonneg (sub_nonneg.mpr (hqa q hq))
    have hh' : ((q-a).toNat:ℝ)=(q:ℝ)-(a:ℝ) := by exact_mod_cast hh
    linarith only [hh']
  have hcard : J.card=I.card := by
    apply Finset.card_image_of_injOn
    intro q hq q' hq' he
    change (q-a).toNat=(q'-a).toNat at he
    have hh : (q:ℝ)=(q':ℝ) := by rw [←hcast q hq,←hcast q' hq',he]
    exact_mod_cast hh
  have hsub : J ⊆ reciprocalRootNearIntegers k A a M η := by
    intro j hj
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hnat : (q-a).toNat ≤ Nat.ceil (R-Q) := by
        have hreal : ((q-a).toNat:ℝ) ≤ (Nat.ceil (R-Q):ℝ) := by
          have hh := hcast q hq
          have hc := Nat.le_ceil (R-Q)
          linarith only [hh,haQ,(hI q hq).2,hc]
        exact_mod_cast hreal
      dsimp only [M]
      omega
    · rw [hcast q hq]
      obtain ⟨z,hz⟩ := hnear q hq
      exact (round_le (reciprocalRoot k A q) z).trans hz
  have hc := (Nat.cast_le (α:=ℝ)).mpr (Finset.card_le_card hsub)
  rw [hcard] at hc
  have hcount := reciprocalRootNearIntegers_card_wide hk hA hap hL hdom hη
  apply (hc.trans hcount).trans
  have hMR : (M:ℝ) ≤ R+3 := by linarith only [hM,hQ]
  gcongr

#print axioms reciprocalRoot_integer_set_card

def tailLabelLower (k : ℕ) (N t u : ℝ) : ℝ :=
  (t*(tailHeightRatio (k+1) t u-1)/(4*(2*N)^k))/(2*Real.pi*k)

def tailLabelUpper (k : ℕ) (N t u : ℝ) : ℝ :=
  (t*(2^k+1)*(tailHeightRatio (k+1) t u-1)/N^k)/(2*Real.pi*k)

def tailLabelStretch (k : ℕ) : ℝ := 4*(2:ℝ)^k*(2^k+1)+4

set_option maxHeartbeats 1500000 in
/-- Complete large-shift mixed-cell counting from the original overlap set.
Every label range, curve estimate and fibre count is derived; the remaining
premises are explicit physical smallness inequalities, not counting assumptions. -/
theorem tailMixedPairs_card_stationary (S : Finset ℕ) {k H : ℕ} {N T t u : ℝ}
    (hk : 1 ≤ k) (hH : 0 < H) (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : tailRatioError (k+1) H N t ≤ (tailHeightRatio (k+1) t u-1)/2)
    (hsmallLabel : (k:ℝ)*2^(k-1)*tailRatioError (k+1) H N t ≤
      (tailHeightRatio (k+1) t u-1)/2)
    (hround : 4*Real.pi*k/(H:ℝ)^k ≤ t*(tailHeightRatio (k+1) t u-1)/(4*(2*N)^k))
    (hQ : 1 ≤ tailLabelLower k N t u)
    (herror : tailCurveError k H N t u (tailLabelLower k N t u) < 1/2) :
    let Q := tailLabelLower k N t u
    let R := tailLabelUpper k N t u
    let L := tailLabelStretch k
    let A := tailStationaryAmplitude k t u
    let μ := A*((k:ℝ)+1)/(k:ℝ)^2*(L*(Int.ceil Q:ℝ))^(-1/(k:ℝ)-2)
    let η := tailCurveError k H N t u Q
    ((tailMixedPairs S k H t u).card:ℝ) ≤
      (1+32*N*tailRatioError (k+1) H N t/(tailHeightRatio (k+1) t u-1))*
      (52+144*L^3)*((R+3)*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
  classical
  let Q := tailLabelLower k N t u
  let R := tailLabelUpper k N t u
  let L := tailLabelStretch k
  let A := tailStationaryAmplitude k t u
  let η := tailCurveError k H N t u Q
  let B := 1+32*N*tailRatioError (k+1) H N t/(tailHeightRatio (k+1) t u-1)
  let F := tailMixedPairs S k H t u
  let label := fun p : ℕ×ℕ => tailLogLabel k t u p.1 p.2
  let J := F.image label
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0:ℝ) < k := by linarith only [hkR]
  have hQp : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hb : 0 < tailHeightRatio (k+1) t u-1 :=
    sub_pos.mpr (tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu).1
  have hη : 0 ≤ η := by dsimp only [η,tailCurveError]; positivity
  have hB : 0 ≤ B := by dsimp only [B,tailRatioError]; positivity
  have hL : 1 ≤ L := by
    have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    dsimp only [L,tailLabelStretch]
    nlinarith only [hp,sq_nonneg ((2:ℝ)^k)]
  have hrel : R=(L-4)*Q := by
    dsimp only [R,L,Q,tailLabelLower,tailLabelUpper,tailLabelStretch]
    rw [mul_pow]
    field_simp
    ring
  have hK : 1 ≤ L-4 := by
    have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    dsimp only [L,tailLabelStretch]
    nlinarith only [hp,sq_nonneg ((2:ℝ)^k)]
  have hQR : Q ≤ R := by nlinarith only [hrel,mul_le_mul_of_nonneg_right hK hQp.le]
  have hwindow : R+4 ≤ L*Q := by nlinarith only [hrel,hQ]
  have hspec (p : ℕ×ℕ) (hp : p∈F) : p.1∈S ∧ p.2∈S ∧
      (tailLogCell (k+1) H t p.1 ∩ tailLogCell (k+1) H u p.2).Nonempty := by
    obtain ⟨hp,hover⟩ := Finset.mem_filter.mp hp
    obtain ⟨hn,hm⟩ := Finset.mem_product.mp hp
    exact ⟨hn,hm,hover⟩
  have hlabel (p : ℕ×ℕ) (hp : p∈F) : Q ≤ (label p:ℝ) ∧ (label p:ℝ) ≤ R := by
    obtain ⟨hn,hm,hover⟩ := hspec p hp
    have hh := tailLogCell_label_bounds hk hN ht htu hu hT htT huT
      (hS _ hn).1 (hS _ hm).1 (hS _ hm).2 hsmallLabel hround hover
    have hden : 0 < 2*Real.pi*k := by positivity
    constructor
    · exact (div_le_iff₀ hden).mpr (by nlinarith only [hh.1])
    · exact (le_div_iff₀ hden).mpr (by nlinarith only [hh.2])
  have hlabelJ (q : ℤ) (hq : q∈J) : Q ≤ (q:ℝ) ∧ (q:ℝ) ≤ R := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact hlabel p hp
  have hηq (q : ℤ) (hq : q∈J) : tailCurveError k H N t u q ≤ η := by
    have hqlo := (hlabelJ q hq).1
    dsimp only [η,tailCurveError]
    gcongr
  have hnear (q : ℤ) (hq : q∈J) :
      ∃ z : ℤ, |reciprocalRoot (k:ℝ) A q-(z:ℝ)| ≤ η := by
    obtain ⟨p,hp,hpl⟩ := Finset.mem_image.mp hq
    obtain ⟨hn,hm,hover⟩ := hspec p hp
    have hqpos : 0 < (tailLogLabel k t u p.1 p.2:ℝ) := hQp.trans_le (hlabel p hp).1
    have hh := tailLogCell_stationary_uniform_error hk hN ht htu hu hT htT huT
      (hS _ hn).1 (hS _ hn).2 (hS _ hm).1 (hS _ hm).2 hsmall hqpos hover
    change tailLogLabel k t u p.1 p.2=q at hpl
    rw [hpl] at hh
    refine ⟨(p.2:ℤ)-p.1,?_⟩
    simpa only [Int.cast_sub,Int.cast_natCast] using hh.trans (hηq q hq)
  have hcurve := reciprocalRoot_integer_set_card J hkR
    (tailStationaryAmplitude_pos hk ht htu hu) hQ hQR hL hwindow hη hlabelJ hnear
  have hfiber (q : ℤ) (hq : q∈J) :
      ((F.filter (fun p => label p=q)).card:ℝ) ≤ B := by
    exact tailLabelPairs_card S hk hN ht htu hu hT htT huT hS hsmall
      (hQp.trans_le (hlabelJ q hq).1) ((hηq q hq).trans_lt herror)
  have hsum := Finset.card_eq_sum_card_fiberwise (f:=label) (s:=F) (t:=J)
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  have hcard : (F.card:ℝ) ≤ (J.card:ℝ)*B := by
    calc
      _ = ∑ q∈J, ((F.filter (fun p => label p=q)).card:ℝ) := by exact_mod_cast hsum
      _ ≤ ∑ _q∈J, B := Finset.sum_le_sum hfiber
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  apply hcard.trans
  have hh := mul_le_mul_of_nonneg_right hcurve hB
  convert hh using 1
  ring

#print axioms tailMixedPairs_card_stationary

/-- Every actual mixed pair lies in its genuine positive fixed-shift fibre. -/
theorem tailMixedPairs_card_le_sum_shifts (S : Finset ℕ) {k H : ℕ} {N T t u : ℝ}
    (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : tailRatioError (k+1) H N t ≤ (tailHeightRatio (k+1) t u-1)/2) :
    (tailMixedPairs S k H t u).card ≤
      ∑ s∈Finset.Icc 1 (Nat.ceil (4*N*(tailHeightRatio (k+1) t u-1))),
        (tailFixedShiftIndices S k H t u s).card := by
  classical
  let I := Finset.Icc 1 (Nat.ceil (4*N*(tailHeightRatio (k+1) t u-1)))
  have hb : 0 < tailHeightRatio (k+1) t u-1 :=
    sub_pos.mpr (tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu).1
  have hcover : tailMixedPairs S k H t u ⊆
      I.biUnion (fun s => (tailFixedShiftIndices S k H t u s).image (fun n => (n,n+s))) := by
    intro p hp
    obtain ⟨hp,hover⟩ := Finset.mem_filter.mp hp
    obtain ⟨hn,hm⟩ := Finset.mem_product.mp hp
    have hshift := tailLogCell_shift_bounds hN ht htu hu hT htT huT
      (hS _ hn).1 (hS _ hn).2 (hS _ hm).1 (hS _ hm).2 hsmall hover
    have hnmR : (p.1:ℝ) < p.2 := by
      have hh : 0 < N*(tailHeightRatio (k+1) t u-1)/2 := by positivity
      linarith only [hh,hshift.1]
    have hnm : p.1 < p.2 := by exact_mod_cast hnmR
    have hbound : ((p.2-p.1:ℕ):ℝ) ≤ Nat.ceil (4*N*(tailHeightRatio (k+1) t u-1)) := by
      rw [Nat.cast_sub hnm.le]
      exact hshift.2.trans (Nat.le_ceil _)
    have hindex : p.2-p.1∈I := by
      apply Finset.mem_Icc.mpr
      constructor
      · omega
      · exact_mod_cast hbound
    have he : p.1+(p.2-p.1)=p.2 := by omega
    have heR : (p.1:ℝ)+(p.2-p.1:ℕ)=p.2 := by exact_mod_cast he
    apply Finset.mem_biUnion.mpr
    refine ⟨p.2-p.1,hindex,Finset.mem_image.mpr ⟨p.1,?_,?_⟩⟩
    · apply Finset.mem_filter.mpr
      refine ⟨hn,?_,?_⟩
      · simpa only [he] using hm
      · simpa only [heR] using hover
    · exact Prod.ext rfl he
  calc
    _ ≤ (I.biUnion (fun s => (tailFixedShiftIndices S k H t u s).image (fun n => (n,n+s)))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ s∈I, ((tailFixedShiftIndices S k H t u s).image (fun n => (n,n+s))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ s∈I, (tailFixedShiftIndices S k H t u s).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)

#print axioms tailMixedPairs_card_le_sum_shifts

set_option maxHeartbeats 1200000 in
/-- Complete small-shift mixed-cell count on the actual source set, including
the finite shift sum. The uniform curvature and range are derived at the
minimal possible physical shift. -/
theorem tailMixedPairs_card_fixed_shifts (S : Finset ℕ) {k H : ℕ} {N T t u : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : tailRatioError (k+1) H N t ≤ (tailHeightRatio (k+1) t u-1)/2)
    (hcurvature : (t/(2*Real.pi*k))*N^(-(k:ℝ)-1)*(((k:ℝ)+1)*2^(k:ℝ))*
      tailRatioError (k+1) H N t ≤
      (t/(2*Real.pi*k))*(N*(tailHeightRatio (k+1) t u-1)/2)*(2*N)^(-(k:ℝ)-2)/2) :
    let b := tailHeightRatio (k+1) t u-1
    let a := t/(2*Real.pi*k)
    let E := tailRatioError (k+1) H N t
    let D := a*N^(-(k:ℝ)-1)*(((k:ℝ)+1)*2^(k:ℝ))*E
    let B := 16*N*E/b
    let μ := (k:ℝ)*((k:ℝ)+1)*a*(N*b/2)*(2*N)^(-(k:ℝ)-3)/2
    let η := 2/(H:ℝ)^k
    ((tailMixedPairs S k H t u).card:ℝ) ≤
      (4*N*b+1)*(2*(k:ℝ)*D*B+2*η+1)*(4+4*Real.sqrt (η/μ)) := by
  classical
  let b := tailHeightRatio (k+1) t u-1
  let a := t/(2*Real.pi*k)
  let E := tailRatioError (k+1) H N t
  let D := a*N^(-(k:ℝ)-1)*(((k:ℝ)+1)*2^(k:ℝ))*E
  let B := 16*N*E/b
  let μ := (k:ℝ)*((k:ℝ)+1)*a*(N*b/2)*(2*N)^(-(k:ℝ)-3)/2
  let η := 2/(H:ℝ)^k
  let U := (2*(k:ℝ)*D*B+2*η+1)*(4+4*Real.sqrt (η/μ))
  let I := Finset.Icc 1 (Nat.ceil (4*N*b))
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0:ℝ) < k := by linarith only [hkR]
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (show 1 ≤ k+1 by omega) ht htu hu).1
  have ha : 0 < a := by dsimp only [a]; positivity
  have hE : 0 ≤ E := by dsimp only [E,tailRatioError]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hlocal (s : ℕ) : ((tailFixedShiftIndices S k H t u s).card:ℝ) ≤ U := by
    by_cases hF : (tailFixedShiftIndices S k H t u s).Nonempty
    · obtain ⟨n,hn⟩ := hF
      obtain ⟨hnS,hnsS,hover⟩ := Finset.mem_filter.mp hn
      have hms : N ≤ (n:ℝ)+s := by exact_mod_cast (hS (n+s) hnsS).1
      have hms2 : (n:ℝ)+s ≤ 2*N := by exact_mod_cast (hS (n+s) hnsS).2
      have hshift := tailLogCell_shift_bounds hN ht htu hu hT htT huT
        (hS n hnS).1 (hS n hnS).2 hms hms2 hsmall hover
      rw [add_sub_cancel_left] at hshift
      change N*b/2 ≤ (s:ℝ) ∧ (s:ℝ) ≤ 4*N*b at hshift
      have hsp : (0:ℝ) < s := lt_of_lt_of_le (by positivity) hshift.1
      have hs : 0 < s := by exact_mod_cast hsp
      have hsmallS : a*N^(-(k:ℝ)-1)*(((k:ℝ)+1)*2^(k:ℝ))*E ≤
          a*(s:ℝ)*(2*N)^(-(k:ℝ)-2)/2 := by
        apply hcurvature.trans
        gcongr
        exact hshift.1
      have hcount := tailFixedShiftIndices_card S hk hs hN ht htu hu hT htT huT hS hsmallS
      change ((tailFixedShiftIndices S k H t u s).card:ℝ) ≤
        (2*(k:ℝ)*D*(8*N^2*E/s)+2*η+1)*
        (4+4*Real.sqrt (η/((k:ℝ)*((k:ℝ)+1)*a*s*(2*N)^(-(k:ℝ)-3)/2))) at hcount
      have hBs : 8*N^2*E/s ≤ B := by
        calc
          _ ≤ 8*N^2*E/(N*b/2) := by gcongr; exact hshift.1
          _ = B := by dsimp only [B]; field_simp; ring
      have hμs : μ ≤ (k:ℝ)*((k:ℝ)+1)*a*s*(2*N)^(-(k:ℝ)-3)/2 := by
        dsimp only [μ]
        gcongr
        exact hshift.1
      have hroot := Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hη hμ hμs)
      apply hcount.trans
      dsimp only [U]
      apply mul_le_mul
      · gcongr
      · linarith only [hroot]
      · positivity
      · positivity
    · rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
      exact hU
  have hsum := tailMixedPairs_card_le_sum_shifts S hN ht htu hu hT htT huT hS hsmall
  have hsumR : ((tailMixedPairs S k H t u).card:ℝ) ≤
      ∑ s∈I, ((tailFixedShiftIndices S k H t u s).card:ℝ) := by exact_mod_cast hsum
  have hIc : (I.card:ℝ) ≤ 4*N*b+1 := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ 4*N*b by positivity)).le
    simpa only [I,Nat.card_Icc,Nat.add_sub_cancel] using hh
  calc
    _ ≤ ∑ s∈I, ((tailFixedShiftIndices S k H t u s).card:ℝ) := hsumR
    _ ≤ ∑ _s∈I, U := Finset.sum_le_sum (fun s _ => hlocal s)
    _ = (I.card:ℝ)*U := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (4*N*b+1)*U := mul_le_mul_of_nonneg_right hIc hU
    _ = _ := by dsimp only [U]; ring

#print axioms tailMixedPairs_card_fixed_shifts

/-- The adaptive block length bounds the actual top-coordinate error at every
Taylor order. The height and block scales are linked by ordinary powers. -/
theorem tailRatioError_le_adaptive {d H : ℕ} {N X t : ℝ}
    (hN : 0 < N) (hX : 0 < X) (hscale : X^(d+1) ≤ t)
    (hblock : N ≤ (H:ℝ)*X) :
    tailRatioError d H N t ≤ (4*Real.pi*d*2^d)/X := by
  have hHp : (0:ℝ) < H := by nlinarith only [hN,hblock,hX]
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hscale
  have hp := pow_le_pow_left₀ hN.le hblock d
  rw [mul_pow] at hp
  have hs := mul_le_mul_of_nonneg_right hscale (pow_nonneg hHp.le d)
  dsimp only [tailRatioError]
  rw [mul_pow]
  apply (div_le_div_iff₀ (by positivity : 0 < t*(H:ℝ)^d) hX).mpr
  have hh : N^d*X ≤ t*(H:ℝ)^d := by
    calc
      _ ≤ ((H:ℝ)^d*X^d)*X := mul_le_mul_of_nonneg_right hp hX.le
      _ = X^(d+1)*(H:ℝ)^d := by rw [pow_succ]; ring
      _ ≤ _ := hs
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4*Real.pi*d*2^d)
  nlinarith only [hh']

#print axioms tailRatioError_le_adaptive

set_option maxHeartbeats 1800000 in
/-- Physical-scale fixed-shift count. The top error, curvature and rounding
losses are discharged from the linked height/root/block scales; no counting
or derivative hypothesis is supplied. -/
theorem tailMixedPairs_card_fixed_shifts_adaptive (S : Finset ℕ)
    {k H : ℕ} {N T t u X : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (hX : 0 < X) (hXN : X ≤ N)
    (hscale : X^(k+2) ≤ t) (hblock : N ≤ (H:ℝ)*X)
    (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : (4*Real.pi*(k+1)*2^(k+1))*
      (4*((k:ℝ)+1)*2^k*2^(k+2)) ≤ (tailHeightRatio (k+1) t u-1)*X) :
    let b := tailHeightRatio (k+1) t u-1
    let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
    ((tailMixedPairs S k H t u).card:ℝ) ≤
      (4*N*b+1)*((16*((k:ℝ)+1)*2^k*K^2/Real.pi)*t/(N^k*b*X^2)+5)*
      (4+4*Real.sqrt (16*Real.pi*2^(k+3)/((k:ℝ)+1))*N/(X*Real.sqrt b)) := by
  let b := tailHeightRatio (k+1) t u-1
  let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
  let J : ℝ := 4*((k:ℝ)+1)*2^k*2^(k+2)
  let E := tailRatioError (k+1) H N t
  let a := t/(2*Real.pi*k)
  let D := a*N^(-(k:ℝ)-1)*(((k:ℝ)+1)*2^(k:ℝ))*E
  let B := 16*N*E/b
  let μ := (k:ℝ)*((k:ℝ)+1)*a*(N*b/2)*(2*N)^(-(k:ℝ)-3)/2
  let η := 2/(H:ℝ)^k
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hscale
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hHp : (0:ℝ) < H := by nlinarith only [hN,hblock,hX]
  have hHone : (1:ℝ) ≤ H := by nlinarith only [hblock,hXN,hX]
  have hK : 0 < K := by dsimp only [K]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hJ2 : 2 ≤ J := by
    have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    have hp' : (1:ℝ) ≤ 2^(k+2) := one_le_pow₀ (by norm_num)
    have hmul := mul_le_mul hp hp' (by positivity) (by positivity)
    dsimp only [J]
    nlinarith only [hmul,hkR]
  have hE : 0 ≤ E := by dsimp only [E,tailRatioError]; positivity
  have hEK : E ≤ K/X := by
    have hh := tailRatioError_le_adaptive (d:=k+1) (H:=H) hN hX
      (by simpa only [Nat.add_assoc] using hscale) hblock
    simpa only [E,K,Nat.cast_add,Nat.cast_one] using hh
  have hEb : E ≤ b/J := by
    apply hEK.trans
    apply (div_le_div_iff₀ hX hJ).mpr
    exact hsmall
  have hEhalf : E ≤ b/2 := hEb.trans (by gcongr)
  have hneg (Y : ℝ) (hY : 0 < Y) (j : ℕ) :
      Y^(-(k:ℝ)-(j:ℝ))=1/Y^(k+j) := by
    rw [show -(k:ℝ)-(j:ℝ)=-((k+j:ℕ):ℝ) by push_cast; ring,
      Real.rpow_neg hY.le,Real.rpow_natCast,one_div]
  have hD : D = a*((k:ℝ)+1)*2^k*E/N^(k+1) := by
    dsimp only [D]
    rw [show N^(-(k:ℝ)-1)=1/N^(k+1) by simpa only [Nat.cast_one] using hneg N hN 1,
      Real.rpow_natCast]
    ring
  have hcurv : D ≤ a*(N*b/2)*(2*N)^(-(k:ℝ)-2)/2 := by
    have ha : 0 ≤ a := by dsimp only [a]; positivity
    rw [hD]
    calc
      _ ≤ a*((k:ℝ)+1)*2^k*(b/J)/N^(k+1) := by gcongr
      _ = _ := by
        rw [show (2*N)^(-(k:ℝ)-2)=1/(2*N)^(k+2) by
          simpa only [Nat.cast_ofNat] using hneg (2*N) (by positivity) 2,mul_pow]
        dsimp only [J]
        rw [pow_succ N (k+1)]
        field_simp
        ring
  have hcount := tailMixedPairs_card_fixed_shifts S hk hN ht htu hu hT htT huT hS hEhalf hcurv
  change ((tailMixedPairs S k H t u).card:ℝ) ≤
    (4*N*b+1)*(2*(k:ℝ)*D*B+2*η+1)*(4+4*Real.sqrt (η/μ)) at hcount
  have hDB : 2*(k:ℝ)*D*B =
      (16*((k:ℝ)+1)*2^k/Real.pi)*t*E^2/(N^k*b) := by
    rw [hD]
    dsimp only [B,a]
    rw [pow_succ N k]
    field_simp
  have hDBupper : 2*(k:ℝ)*D*B ≤
      (16*((k:ℝ)+1)*2^k*K^2/Real.pi)*t/(N^k*b*X^2) := by
    rw [hDB]
    calc
      _ ≤ (16*((k:ℝ)+1)*2^k/Real.pi)*t*(K/X)^2/(N^k*b) := by gcongr
      _ = _ := by field_simp
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hηtwo : η ≤ 2 := by
    have hp : (1:ℝ) ≤ (H:ℝ)^k := one_le_pow₀ hHone
    dsimp only [η]
    exact (div_le_iff₀ (by positivity : 0 < (H:ℝ)^k)).mpr (by linarith only [hp])
  have hμ : 0 < μ := by dsimp only [μ,a]; positivity
  have hμeq : μ = ((k:ℝ)+1)*t*b/(8*Real.pi*2^(k+3)*N^(k+2)) := by
    dsimp only [μ,a]
    rw [show (2*N)^(-(k:ℝ)-3)=1/(2*N)^(k+3) by
      simpa only [Nat.cast_ofNat] using hneg (2*N) (by positivity) 3,mul_pow,
      pow_succ N (k+2)]
    field_simp
    ring
  have hpow : N^k*X^2 ≤ t*(H:ℝ)^k := by
    have hp := pow_le_pow_left₀ hN.le hblock k
    rw [mul_pow] at hp
    calc
      _ ≤ ((H:ℝ)^k*X^k)*X^2 := mul_le_mul_of_nonneg_right hp (sq_nonneg X)
      _ = X^(k+2)*(H:ℝ)^k := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)
  have hratio : η/μ ≤ (16*Real.pi*2^(k+3)/((k:ℝ)+1))*N^2/(X^2*b) := by
    rw [hμeq]
    dsimp only [η]
    have he : (2/(H:ℝ)^k)/(((k:ℝ)+1)*t*b/(8*Real.pi*2^(k+3)*N^(k+2))) =
        (16*Real.pi*2^(k+3)*N^2/(((k:ℝ)+1)*b))*(N^k/(t*(H:ℝ)^k)) := by
      rw [pow_add]
      field_simp
      ring
    rw [he]
    calc
      _ ≤ (16*Real.pi*2^(k+3)*N^2/(((k:ℝ)+1)*b))*(1/X^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_div_iff₀ (by positivity : 0 < t*(H:ℝ)^k) (by positivity : 0 < X^2)).mpr
          (by simpa only [one_mul] using hpow)
      _ = _ := by field_simp
  have hsqrt : Real.sqrt (η/μ) ≤
      Real.sqrt (16*Real.pi*2^(k+3)/((k:ℝ)+1))*N/(X*Real.sqrt b) := by
    apply (Real.sqrt_le_sqrt hratio).trans_eq
    rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity),Real.sqrt_sq hN.le,Real.sqrt_sq hX.le]
  change ((tailMixedPairs S k H t u).card:ℝ) ≤
    (4*N*b+1)*((16*((k:ℝ)+1)*2^k*K^2/Real.pi)*t/(N^k*b*X^2)+5)*
    (4+4*Real.sqrt (16*Real.pi*2^(k+3)/((k:ℝ)+1))*N/(X*Real.sqrt b))
  apply hcount.trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [hDBupper,hηtwo]
  · calc
      _ ≤ 4+4*(Real.sqrt (16*Real.pi*2^(k+3)/((k:ℝ)+1))*N/(X*Real.sqrt b)) := by
        linarith only [hsqrt]
      _ = _ := by ring
  · positivity
  · positivity

#print axioms tailMixedPairs_card_fixed_shifts_adaptive

set_option maxHeartbeats 1000000 in
/-- The stationary-curve error at the actual smallest label, after inserting
the adaptive block scale. Its two terms retain the linked root displacement. -/
theorem tailCurveError_le_adaptive {k H : ℕ} {N X t u : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (hX : 0 < X)
    (hscale : X^(k+2) ≤ t) (hblock : N ≤ (H:ℝ)*X)
    (htu : t < u) (hu : u ≤ 2*t) :
    let b := tailHeightRatio (k+1) t u-1
    let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
    let F : ℝ := 4*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*2^(k-1)*2^k
    tailCurveError k H N t u (tailLabelLower k N t u) ≤
      F*K^2*N/(b*X^2)+(64*Real.pi*k*2^k)*N/X^2 := by
  let b := tailHeightRatio (k+1) t u-1
  let E := tailRatioError (k+1) H N t
  let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
  let F : ℝ := 4*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*2^(k-1)*2^k
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hscale
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hHp : (0:ℝ) < H := by nlinarith only [hN,hblock,hX]
  have hE : 0 ≤ E := by dsimp only [E,tailRatioError]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hEK : E ≤ K/X := by
    have hh := tailRatioError_le_adaptive (d:=k+1) (H:=H) hN hX
      (by simpa only [Nat.add_assoc] using hscale) hblock
    simpa only [E,K,Nat.cast_add,Nat.cast_one] using hh
  have hNk : N^k=N^(k-1)*N := by rw [←pow_succ]; congr 1; omega
  have he : tailCurveError k H N t u (tailLabelLower k N t u) =
      F*N*E^2/b+(64*Real.pi*k*2^k)*N^(k+1)/(t*(H:ℝ)^k) := by
    dsimp only [tailCurveError,tailLabelLower,F]
    change t*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*2^(k-1)*E^2/
      (2*Real.pi*k*(t*b/(4*(2*N)^k)/(2*Real.pi*k))*N^(k-1))+
      8*N*b/((H:ℝ)^k*(t*b/(4*(2*N)^k)/(2*Real.pi*k))) = _
    rw [mul_pow,pow_succ N k,hNk]
    field_simp
    ring
  have hp : N^k*X^2 ≤ t*(H:ℝ)^k := by
    have hh := pow_le_pow_left₀ hN.le hblock k
    rw [mul_pow] at hh
    calc
      _ ≤ ((H:ℝ)^k*X^k)*X^2 := mul_le_mul_of_nonneg_right hh (sq_nonneg X)
      _ = X^(k+2)*(H:ℝ)^k := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)
  change tailCurveError k H N t u (tailLabelLower k N t u) ≤
    F*K^2*N/(b*X^2)+(64*Real.pi*k*2^k)*N/X^2
  rw [he]
  apply add_le_add
  · calc
      _ ≤ F*N*(K/X)^2/b := by gcongr
      _ = _ := by field_simp
  · have hh : N^k/(t*(H:ℝ)^k) ≤ 1/X^2 :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa only [one_mul] using hp)
    calc
      _ = ((64*Real.pi*k*2^k)*N)*(N^k/(t*(H:ℝ)^k)) := by rw [pow_succ]; ring
      _ ≤ ((64*Real.pi*k*2^k)*N)*(1/X^2) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring

#print axioms tailCurveError_le_adaptive

set_option maxHeartbeats 1000000 in
/-- At the true lower label the stationary curve has the physical index-shift
scale, uniformly in the height and length. -/
theorem tailStationaryCurve_at_lower {k : ℕ} {N t u : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) :
    let b := tailHeightRatio (k+1) t u-1
    let p := reciprocalRoot (k:ℝ) (tailStationaryAmplitude k t u) (tailLabelLower k N t u)
    N*b ≤ p ∧ p ≤ 8*N*b := by
  let b := tailHeightRatio (k+1) t u-1
  let Q := tailLabelLower k N t u
  let p := reciprocalRoot (k:ℝ) (tailStationaryAmplitude k t u) Q
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hQ : 0 < Q := by dsimp only [Q,tailLabelLower]; change 0 < (t*b/(4*(2*N)^k))/(2*Real.pi*k); positivity
  have hp : 0 < p := by
    dsimp only [p,reciprocalRoot]
    exact mul_pos (tailStationaryAmplitude_pos hk ht htu hu) (Real.rpow_pos_of_pos hQ _)
  have hpower : p^k=4*(2*N*b)^k := by
    have hh := tailStationaryCurve_power hk ht htu hu hQ
    change p^k=t*b^(k+1)/(2*Real.pi*k*Q) at hh
    rw [hh]
    dsimp only [Q,tailLabelLower]
    change t*b^(k+1)/(2*Real.pi*k*((t*b/(4*(2*N)^k))/(2*Real.pi*k)))=4*(2*N*b)^k
    rw [pow_succ b k]
    simp only [mul_pow]
    field_simp
  change N*b ≤ p ∧ p ≤ 8*N*b
  constructor
  · by_contra! hh
    have hlt := pow_lt_pow_left₀ hh hp.le (by omega : k ≠ 0)
    have hmul : (N*b)^k ≤ (2*N*b)^k := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith only [mul_pos hN hb]
    rw [hpower] at hlt
    nlinarith only [hlt,hmul,pow_pos (by positivity : 0 < 2*N*b) k]
  · by_contra! hh
    have hlt := pow_lt_pow_left₀ hh (by positivity : 0 ≤ 8*N*b) (by omega : k ≠ 0)
    have hfour : (4:ℝ) ≤ 4^k := by
      calc
        _ = (4:ℝ)^1 := by ring
        _ ≤ 4^k := pow_le_pow_right₀ (by norm_num) hk
    have hmul := mul_le_mul_of_nonneg_right hfour (by positivity : 0 ≤ (2*N*b)^k)
    have he : (8*N*b)^k=4^k*(2*N*b)^k := by rw [←mul_pow]; congr 1; ring
    rw [he,hpower] at hlt
    linarith only [hlt,hmul]

#print axioms tailStationaryCurve_at_lower

set_option maxHeartbeats 1200000 in
/-- The actual ceiling-based curvature parameter in the label count is
comparable to the physical shift divided by the square of the label scale. -/
theorem tailStationaryCurvature_physical {k : ℕ} {N t u : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (hQ : 1 ≤ tailLabelLower k N t u) :
    let b := tailHeightRatio (k+1) t u-1
    let Q := tailLabelLower k N t u
    let L := tailLabelStretch k
    let A := tailStationaryAmplitude k t u
    let μ := A*((k:ℝ)+1)/(k:ℝ)^2*(L*(Int.ceil Q:ℝ))^(-1/(k:ℝ)-2)
    let c := ((k:ℝ)+1)/(k:ℝ)^2
    c*(2*L)^(-1/(k:ℝ)-2)*(N*b/Q^2) ≤ μ ∧ μ ≤ 8*c*(N*b/Q^2) := by
  let b := tailHeightRatio (k+1) t u-1
  let Q := tailLabelLower k N t u
  let L := tailLabelStretch k
  let A := tailStationaryAmplitude k t u
  let c := ((k:ℝ)+1)/(k:ℝ)^2
  let e := -1/(k:ℝ)-2
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hA : 0 < A := tailStationaryAmplitude_pos hk ht htu hu
  have hc : 0 < c := by dsimp only [c]; positivity
  have he : e ≤ 0 := by
    dsimp only [e]
    have hh : -1/(k:ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hkR.le
    linarith only [hh]
  have hL : 1 ≤ L := by
    have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    dsimp only [L,tailLabelStretch]
    nlinarith only [hp,sq_nonneg ((2:ℝ)^k)]
  have ha : Q ≤ (Int.ceil Q:ℝ) := Int.le_ceil Q
  have haup : (Int.ceil Q:ℝ) ≤ 2*Q := by
    have hh := Int.ceil_lt_add_one Q
    linarith only [hh,hQ]
  have hlow : Q ≤ L*(Int.ceil Q:ℝ) := by
    calc
      _ ≤ (Int.ceil Q:ℝ) := ha
      _ ≤ L*(Int.ceil Q:ℝ) := le_mul_of_one_le_left (hQp.trans_le ha).le hL
  have hhigh : L*(Int.ceil Q:ℝ) ≤ (2*L)*Q := by nlinarith only [mul_le_mul_of_nonneg_left haup (by linarith only [hL] : 0 ≤ L)]
  have hhom (z : ℝ) (hz : 0 < z) :
      A*c*(z*Q)^e=c*z^e*reciprocalRoot (k:ℝ) A Q/Q^2 := by
    dsimp only [e,reciprocalRoot]
    rw [Real.mul_rpow hz.le hQp.le,show -1/(k:ℝ)-2=(-1/(k:ℝ))+(-2) by ring,
      Real.rpow_add hQp,Real.rpow_neg hQp.le,Real.rpow_two]
    ring
  obtain ⟨hpLo,hpHi⟩ := tailStationaryCurve_at_lower hk hN ht htu hu
  change N*b ≤ reciprocalRoot (k:ℝ) A Q at hpLo
  change reciprocalRoot (k:ℝ) A Q ≤ 8*N*b at hpHi
  change c*(2*L)^e*(N*b/Q^2) ≤ A*((k:ℝ)+1)/(k:ℝ)^2*(L*(Int.ceil Q:ℝ))^e ∧
    A*((k:ℝ)+1)/(k:ℝ)^2*(L*(Int.ceil Q:ℝ))^e ≤ 8*c*(N*b/Q^2)
  have hAc : A*((k:ℝ)+1)/(k:ℝ)^2=A*c := by dsimp only [c]; ring
  rw [hAc]
  constructor
  · calc
      _ ≤ c*(2*L)^e*reciprocalRoot (k:ℝ) A Q/Q^2 := by
        have hh := mul_le_mul_of_nonneg_left hpLo (by positivity : 0 ≤ c*(2*L)^e)
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh (sq_nonneg Q)
      _ = A*c*((2*L)*Q)^e := (hhom (2*L) (by positivity)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (hQp.trans_le hlow) hhigh he) (by positivity)
  · calc
      _ ≤ A*c*Q^e := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hQp hlow he) (by positivity)
      _ = c*reciprocalRoot (k:ℝ) A Q/Q^2 := by simpa only [one_mul,Real.one_rpow,mul_one] using hhom 1 (by norm_num)
      _ ≤ c*(8*N*b)/Q^2 := by gcongr
      _ = _ := by ring

#print axioms tailStationaryCurvature_physical

set_option maxHeartbeats 1000000 in
/-- The far-height cutoff forces a growing root-displacement scale. This is
the physical input that discharges the small-error conditions at every order. -/
theorem tailHeightRatio_adaptive_gap {d : ℕ} {N T t u ε : ℝ}
    (hd : 1 ≤ d) (hN : 0 < N) (hTp : 0 < T) (ht : 0 < t)
    (htu : t < u) (hu : u ≤ 2*t) (htT : t ≤ 2*T)
    (hT : T ≤ N^d)
    (hgap : N^((d:ℝ)-1+2/((d:ℝ)+1)-ε) ≤ u-t) :
    N^(1/((d:ℝ)+1)-ε)/(2*(d:ℝ)*2^(d-1)) ≤
      (tailHeightRatio d t u-1)*T^(1/((d:ℝ)+1)) := by
  let b := tailHeightRatio d t u-1
  let c : ℝ := (d:ℝ)*2^(d-1)
  let a : ℝ := (d:ℝ)-1+2/((d:ℝ)+1)-ε
  let e : ℝ := 1/((d:ℝ)+1)-1
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hc : 0 < c := by dsimp only [c]; positivity
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds hd ht htu hu).1
  have he : e ≤ 0 := by
    have hh : 1/((d:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hdR])
    dsimp only [e]
    linarith only [hh]
  have hlinked : N^a/(2*c*T) ≤ b := by
    have hh := (tailHeightRatio_gap hd ht htu hu).1
    change (u-t)/c ≤ t*b at hh
    have hh' := (div_le_iff₀ hc).mp hh
    have ht' := mul_le_mul_of_nonneg_right htT hb.le
    have ht'' := mul_le_mul_of_nonneg_right ht' hc.le
    apply (div_le_iff₀ (by positivity : 0 < 2*c*T)).mpr
    change N^a ≤ u-t at hgap
    nlinarith only [hgap,hh',ht'']
  have hexponent : a+(d:ℝ)*e=1/((d:ℝ)+1)-ε := by
    dsimp only [a,e]
    field_simp
    ring
  rw [mul_assoc (2:ℝ) (d:ℝ)]
  change N^(1/((d:ℝ)+1)-ε)/(2*c) ≤ b*T^(1/((d:ℝ)+1))
  calc
    _ = (N^a/(2*c))*(N^d)^e := by
      rw [←Real.rpow_natCast N d,←Real.rpow_mul hN.le]
      rw [div_mul_eq_mul_div,←Real.rpow_add hN,hexponent]
    _ ≤ (N^a/(2*c))*T^e := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hTp hT he) (by positivity)
    _ = (N^a/(2*c*T))*T^(1/((d:ℝ)+1)) := by
      dsimp only [e]
      rw [Real.rpow_sub hTp,Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hlinked (by positivity)

#print axioms tailHeightRatio_adaptive_gap

set_option maxHeartbeats 1600000 in
/-- Actual stationary-label mixed-cell count in physical variables. The
ceiling curvature, label rounding and cell error have all been eliminated
from the conclusion; the remaining conditions are numerical scale bounds. -/
theorem tailMixedPairs_card_stationary_adaptive (S : Finset ℕ)
    {k H : ℕ} {N T t u X : ℝ}
    (hk : 1 ≤ k) (hN : 0 < N) (hX : 0 < X)
    (hscale : X^(k+2) ≤ t) (hblock : N ≤ (H:ℝ)*X)
    (htu : t < u) (hu : u ≤ 2*t)
    (hT : T ≤ N^(k+1)) (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 2*(4*Real.pi*(k+1)*2^(k+1)) ≤ (tailHeightRatio (k+1) t u-1)*X)
    (hsmallLabel : 2*(k:ℝ)*2^(k-1)*(4*Real.pi*(k+1)*2^(k+1)) ≤
      (tailHeightRatio (k+1) t u-1)*X)
    (hround : 16*Real.pi*k*2^k ≤ (tailHeightRatio (k+1) t u-1)*X^2)
    (hQ : 1 ≤ tailLabelLower k N t u)
    (herror :
      let b := tailHeightRatio (k+1) t u-1
      let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
      let F : ℝ := 4*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*2^(k-1)*2^k
      F*K^2*N/(b*X^2)+(64*Real.pi*k*2^k)*N/X^2 < 1/2) :
    let b := tailHeightRatio (k+1) t u-1
    let Q := tailLabelLower k N t u
    let L := tailLabelStretch k
    let c := ((k:ℝ)+1)/(k:ℝ)^2
    let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
    let F : ℝ := 4*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*2^(k-1)*2^k
    let U := F*K^2*N/(b*X^2)+(64*Real.pi*k*2^k)*N/X^2
    ((tailMixedPairs S k H t u).card:ℝ) ≤
      (1+32*K*N/(b*X))*(52+144*L^3)*
        (L*Q*(U+(8*c*(N*b/Q^2))^((1:ℝ)/3))+
          (c*(2*L)^(-1/(k:ℝ)-2)*(N*b/Q^2))^(-(1:ℝ)/2)) := by
  let b := tailHeightRatio (k+1) t u-1
  let Q := tailLabelLower k N t u
  let R := tailLabelUpper k N t u
  let L := tailLabelStretch k
  let c := ((k:ℝ)+1)/(k:ℝ)^2
  let A := tailStationaryAmplitude k t u
  let μ := A*((k:ℝ)+1)/(k:ℝ)^2*(L*(Int.ceil Q:ℝ))^(-1/(k:ℝ)-2)
  let E := tailRatioError (k+1) H N t
  let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
  let F : ℝ := 4*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*2^(k-1)*2^k
  let U := F*K^2*N/(b*X^2)+(64*Real.pi*k*2^k)*N/X^2
  let η := tailCurveError k H N t u Q
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hscale
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hHp : (0:ℝ) < H := by nlinarith only [hN,hblock,hX]
  have hH : 0 < H := by exact_mod_cast hHp
  have hK : 0 < K := by dsimp only [K]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hE : 0 ≤ E := by dsimp only [E,tailRatioError]; positivity
  have hEK : E ≤ K/X := by
    have hh := tailRatioError_le_adaptive (d:=k+1) (H:=H) hN hX
      (by simpa only [Nat.add_assoc] using hscale) hblock
    simpa only [E,K,Nat.cast_add,Nat.cast_one] using hh
  have hEsmall : E ≤ b/2 := hEK.trans
    ((div_le_div_iff₀ hX (by norm_num)).mpr (by change 2*K ≤ b*X at hsmall; linarith only [hsmall]))
  have hElabel : (k:ℝ)*2^(k-1)*E ≤ b/2 := by
    calc
      _ ≤ (k:ℝ)*2^(k-1)*(K/X) := by gcongr
      _ ≤ b/2 := by
        rw [←mul_div_assoc]
        apply (div_le_div_iff₀ hX (by norm_num)).mpr
        change 2*(k:ℝ)*2^(k-1)*K ≤ b*X at hsmallLabel
        nlinarith only [hsmallLabel]
  have hround' : 4*Real.pi*k/(H:ℝ)^k ≤ t*b/(4*(2*N)^k) := by
    let C : ℝ := 16*Real.pi*k*2^k
    have hp := pow_le_pow_left₀ hN.le hblock k
    rw [mul_pow] at hp
    have hs : C*X^k ≤ b*t := by
      calc
        _ ≤ (b*X^2)*X^k := mul_le_mul_of_nonneg_right hround (by positivity)
        _ = b*X^(k+2) := by rw [pow_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale hb.le
    have hh : C*N^k ≤ b*t*(H:ℝ)^k := by
      calc
        _ ≤ C*((H:ℝ)^k*X^k) := mul_le_mul_of_nonneg_left hp (by dsimp only [C]; positivity)
        _ = (C*X^k)*(H:ℝ)^k := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hs (by positivity)
    apply (div_le_div_iff₀ (by positivity : 0 < (H:ℝ)^k) (by positivity : 0 < 4*(2*N)^k)).mpr
    rw [mul_pow]
    dsimp only [C] at hh
    nlinarith only [hh]
  have hη : 0 ≤ η := by dsimp only [η,tailCurveError]; positivity
  have hηU : η ≤ U := tailCurveError_le_adaptive hk hN hX hscale hblock htu hu
  have hηsmall : η < 1/2 := hηU.trans_lt herror
  have hcount := tailMixedPairs_card_stationary S hk hH hN ht htu hu hT htT huT hS
    hEsmall hElabel hround' hQ hηsmall
  change ((tailMixedPairs S k H t u).card:ℝ) ≤
    (1+32*N*E/b)*(52+144*L^3)*((R+3)*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) at hcount
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hc : 0 < c := by dsimp only [c]; positivity
  have hL : 0 < L := by dsimp only [L,tailLabelStretch]; positivity
  have hrel : R=(L-4)*Q := by
    dsimp only [R,L,Q,tailLabelLower,tailLabelUpper,tailLabelStretch]
    rw [mul_pow]
    field_simp
    ring
  have hRQ : R+3 ≤ L*Q := by nlinarith only [hrel,hQ]
  have hR : 0 < R := by
    dsimp only [R,tailLabelUpper]
    change 0 < (t*(2^k+1)*b/N^k)/(2*Real.pi*k)
    positivity
  obtain ⟨hμlo,hμhi⟩ := tailStationaryCurvature_physical hk hN ht htu hu hQ
  change c*(2*L)^(-1/(k:ℝ)-2)*(N*b/Q^2) ≤ μ at hμlo
  change μ ≤ 8*c*(N*b/Q^2) at hμhi
  have hμloPos : 0 < c*(2*L)^(-1/(k:ℝ)-2)*(N*b/Q^2) := by positivity
  have hμp : 0 < μ := hμloPos.trans_le hμlo
  have hμthird : μ^((1:ℝ)/3) ≤ (8*c*(N*b/Q^2))^((1:ℝ)/3) :=
    Real.rpow_le_rpow hμp.le hμhi (by norm_num)
  have hμhalf : μ^(-(1:ℝ)/2) ≤ (c*(2*L)^(-1/(k:ℝ)-2)*(N*b/Q^2))^(-(1:ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos hμloPos hμlo (by norm_num)
  have hfiber : 1+32*N*E/b ≤ 1+32*K*N/(b*X) := by
    calc
      _ ≤ 1+32*N*(K/X)/b := by gcongr
      _ = _ := by field_simp
  change ((tailMixedPairs S k H t u).card:ℝ) ≤
    (1+32*K*N/(b*X))*(52+144*L^3)*
      (L*Q*(U+(8*c*(N*b/Q^2))^((1:ℝ)/3))+
        (c*(2*L)^(-1/(k:ℝ)-2)*(N*b/Q^2))^(-(1:ℝ)/2))
  apply hcount.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hfiber (by positivity)
  · apply add_le_add _ hμhalf
    exact mul_le_mul hRQ (add_le_add hηU hμthird) (by positivity) (by positivity)
  · positivity
  · positivity

#print axioms tailMixedPairs_card_stationary_adaptive

set_option maxHeartbeats 1400000 in
/-- The fixed-shift source count with the actual adaptive integer block and
all geometric smallness premises discharged uniformly from the far cutoff.
The next step is to combine this with the large-shift count for a power saving. -/
theorem tailMixedPairs_card_fixed_shifts_far {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k) (hε : ε < 1/((k:ℝ)+2)) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (S : Finset ℕ) (N T t u : ℝ), C ≤ N →
      0 < T → T ≤ N^(k+1) → T ≤ t → t ≤ 2*T → u ≤ 2*T →
      N^((k:ℝ)+2/((k:ℝ)+2)-ε) ≤ u-t →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      let b := tailHeightRatio (k+1) t u-1
      let X := T^(1/((k:ℝ)+2))
      let H := Nat.ceil (N/X)
      let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
      ((tailMixedPairs S k H t u).card:ℝ) ≤
        (4*N*b+1)*((16*((k:ℝ)+1)*2^k*K^2/Real.pi)*t/(N^k*b*X^2)+5)*
        (4+4*Real.sqrt (16*Real.pi*2^(k+3)/((k:ℝ)+1))*N/(X*Real.sqrt b)) := by
  let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
  let J : ℝ := 4*((k:ℝ)+1)*2^k*2^(k+2)
  let c : ℝ := 2*((k:ℝ)+1)*2^k
  have hc : 0 < c := by dsimp only [c]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hev : ∀ᶠ N : ℝ in Filter.atTop, c*(K*J) ≤ N^(1/((k:ℝ)+2)-ε) := by
    simpa only [pow_zero,mul_one] using eventually_const_log_pow_le_rpow (c*(K*J))
      (by positivity) 0 (η:=1/((k:ℝ)+2)-ε) (sub_pos.mpr hε)
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 2 C,le_max_left _ _,?_⟩
  intro S N T t u hCN hTp hT htT ht2T hu2T hfar hS
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hCN
  have hNp : 0 < N := by linarith only [hN2]
  have hN1 : 1 ≤ N := by linarith only [hN2]
  have ht : 0 < t := hTp.trans_le htT
  have htu : t < u := sub_pos.mp ((Real.rpow_pos_of_pos hNp _).trans_le hfar)
  have hu : u ≤ 2*t := by linarith only [htT,hu2T]
  let b := tailHeightRatio (k+1) t u-1
  let X := T^(1/((k:ℝ)+2))
  let H := Nat.ceil (N/X)
  have hX : 0 < X := Real.rpow_pos_of_pos hTp _
  have hn : 0 < (k:ℝ)+2 := by positivity
  have hscale : X^(k+2)=T := by
    dsimp only [X]
    rw [←Real.rpow_mul_natCast hTp.le]
    have he : 1/((k:ℝ)+2)*(k+2:ℕ)=1 := by push_cast; field_simp
    rw [he,Real.rpow_one]
  have hXN : X ≤ N := by
    calc
      _ ≤ (N^(k+1))^(1/((k:ℝ)+2)) := Real.rpow_le_rpow hTp.le hT (by positivity)
      _ = N^(((k:ℝ)+1)/((k:ℝ)+2)) := by
        rw [←Real.rpow_natCast N (k+1),←Real.rpow_mul hNp.le]
        congr 1
        push_cast
        ring
      _ ≤ N := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
          ((div_le_iff₀ hn).mpr (by linarith : (k:ℝ)+1 ≤ 1*((k:ℝ)+2)))
  have hblock : N ≤ (H:ℝ)*X := (div_le_iff₀ hX).mp (Nat.le_ceil (N/X))
  have hgap := tailHeightRatio_adaptive_gap (d:=k+1) (ε:=ε) (by omega) hNp hTp ht
    htu hu ht2T hT (by convert hfar using 1; congr 1; push_cast; ring)
  have hgap' : N^(1/((k:ℝ)+2)-ε)/c ≤ b*X := by
    convert hgap using 1 <;> dsimp only [c,b,X] <;>
      simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] <;> ring_nf
  have hconst := hC N ((le_max_right _ _).trans hCN)
  have hsmall : K*J ≤ b*X := by
    apply le_trans _ hgap'
    apply (le_div_iff₀ hc).mpr
    nlinarith only [hconst]
  exact tailMixedPairs_card_fixed_shifts_adaptive S hk hNp hX hXN
    (hscale.trans_le htT) hblock htu hu hT ht2T hu2T hS hsmall

#print axioms tailMixedPairs_card_fixed_shifts_far

/-- The actual height gap is linked to the root displacement, before any
power estimates are taken. This dependence must be retained in both branches. -/
theorem tailHeightRatio_linked_height {d : ℕ} {T t u : ℝ}
    (hd : 1 ≤ d) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) (htT : t ≤ 2*T) :
    (u-t)/(2*(d:ℝ)*2^(d-1)) ≤ T*(tailHeightRatio d t u-1) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hb : 0 < tailHeightRatio d t u-1 := sub_pos.mpr (tailHeightRatio_bounds hd ht htu hu).1
  have hh := (tailHeightRatio_gap hd ht htu hu).1
  have hh' := (div_le_iff₀ (by positivity : 0 < (d:ℝ)*2^(d-1))).mp hh
  have ht' := mul_le_mul_of_nonneg_right htT hb.le
  have ht'' := mul_le_mul_of_nonneg_right ht' (by positivity : 0 ≤ (d:ℝ)*2^(d-1))
  apply (div_le_iff₀ (by positivity : 0 < 2*(d:ℝ)*2^(d-1))).mpr
  nlinarith only [hh',ht'']

#print axioms tailHeightRatio_linked_height

set_option maxHeartbeats 1200000 in
/-- The range factor in the actual fixed-shift count loses only the chosen
far-cutoff epsilon. The height and displacement are not bounded independently. -/
theorem tailFixedShiftRange_le_power {k : ℕ} {N T t u ε : ℝ}
    (hN : 0 < N) (hTp : 0 < T) (ht : 0 < t)
    (htu : t < u) (hu : u ≤ 2*t) (htT : t ≤ 2*T) (hT : T ≤ N^(k+1))
    (hfar : N^((k:ℝ)+2/((k:ℝ)+2)-ε) ≤ u-t) :
    let b := tailHeightRatio (k+1) t u-1
    let X := T^(1/((k:ℝ)+2))
    t/(N^k*b*X^2) ≤ (4*((k:ℝ)+1)*2^k)*N^ε := by
  let b := tailHeightRatio (k+1) t u-1
  let X := T^(1/((k:ℝ)+2))
  let c : ℝ := 2*((k:ℝ)+1)*2^k
  let a : ℝ := (k:ℝ)+2/((k:ℝ)+2)-ε
  let e : ℝ := 2-2/((k:ℝ)+2)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hX : 0 < X := Real.rpow_pos_of_pos hTp _
  have hnp : 0 < (k:ℝ)+2 := by positivity
  have he : 0 ≤ e := by
    have hh : 2/((k:ℝ)+2) ≤ 2 := (div_le_iff₀ hnp).mpr (by nlinarith only [Nat.cast_nonneg (α:=ℝ) k])
    dsimp only [e]
    linarith only [hh]
  have hlink : N^a ≤ c*T*b := by
    have hh := tailHeightRatio_linked_height (d:=k+1) (by omega) ht htu hu htT
    have hh' : (u-t)/c ≤ T*b := by
      simpa only [c,b,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] using hh
    have hh'' := (div_le_iff₀ hc).mp hh'
    change N^a ≤ u-t at hfar
    nlinarith only [hfar,hh'']
  have hbinv : 1/b ≤ c*T/N^a :=
    (div_le_div_iff₀ hb (by positivity)).mpr (by simpa only [one_mul] using hlink)
  have hidentity : 2*c*T^2/(N^k*N^a*X^2)=2*c*T^e/N^((k:ℝ)+a) := by
    dsimp only [X,e]
    rw [←Real.rpow_mul_natCast hTp.le,←Real.rpow_natCast N k]
    norm_num only [Nat.cast_ofNat]
    have hx : (1/((k:ℝ)+2))*(2:ℝ)=2/((k:ℝ)+2) := by ring
    rw [hx,Real.rpow_sub hTp,Real.rpow_two,Real.rpow_add hN]
    field_simp
  change t/(N^k*b*X^2) ≤ (4*((k:ℝ)+1)*2^k)*N^ε
  calc
    _ = (t/(N^k*X^2))*(1/b) := by field_simp
    _ ≤ (2*T/(N^k*X^2))*(c*T/N^a) := mul_le_mul
      (div_le_div_of_nonneg_right htT (by positivity)) hbinv (by positivity) (by positivity)
    _ = 2*c*T^2/(N^k*N^a*X^2) := by ring
    _ = 2*c*T^e/N^((k:ℝ)+a) := hidentity
    _ ≤ 2*c*(N^(k+1))^e/N^((k:ℝ)+a) := by gcongr
    _ = (4*((k:ℝ)+1)*2^k)*N^ε := by
      rw [←Real.rpow_natCast N (k+1),←Real.rpow_mul hN.le]
      rw [mul_div_assoc,←Real.rpow_sub hN]
      have hexp : ((k+1:ℕ):ℝ)*e-((k:ℝ)+a)=ε := by
        dsimp only [a,e]
        push_cast
        field_simp
        ring
      rw [hexp]
      dsimp only [c]
      ring

#print axioms tailFixedShiftRange_le_power

set_option maxHeartbeats 1400000 in
/-- The curved-fibre term, multiplied by the number of actual shifts, has a
strict sublinear exponent on the small-shift branch. The crucial lower height
bound is derived from the same physical displacement, not supplied separately. -/
theorem tailFixedShiftMain_le_power {k : ℕ} {N T t u ε : ℝ}
    (hN : 0 < N) (hTp : 0 < T) (ht : 0 < t)
    (htu : t < u) (hu : u ≤ 2*t) (htT : t ≤ 2*T)
    (hfar : N^((k:ℝ)+2/((k:ℝ)+2)-ε) ≤ u-t)
    (hshift : N*(tailHeightRatio (k+1) t u-1) ≤ N^((11:ℝ)/20)) :
    let b := tailHeightRatio (k+1) t u-1
    let n : ℝ := (k:ℝ)+2
    N^2*Real.sqrt b/T^(1/n) ≤ (2*((k:ℝ)+1)*2^k)^(1/n)*
      N^(31/40+31/(20*n)-2/n^2+ε/n) := by
  let b := tailHeightRatio (k+1) t u-1
  let n : ℝ := (k:ℝ)+2
  let r : ℝ := 1/n
  let c : ℝ := 2*((k:ℝ)+1)*2^k
  let a : ℝ := (k:ℝ)+2/n-ε
  have hc : 0 < c := by dsimp only [c]; positivity
  have hn : 0 < n := by dsimp only [n]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hlink : N^a ≤ c*T*b := by
    have hh := tailHeightRatio_linked_height (d:=k+1) (by omega) ht htu hu htT
    have hh' : (u-t)/c ≤ T*b := by
      simpa only [c,b,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] using hh
    have hh'' := (div_le_iff₀ hc).mp hh'
    change N^a ≤ u-t at hfar
    nlinarith only [hfar,hh'']
  have hTinv : 1/T ≤ c*b/N^a :=
    (div_le_div_iff₀ hTp (by positivity)).mpr (by nlinarith only [hlink])
  have hroot : 1/T^r ≤ c^r*b^r/N^(a*r) := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1/T) hTinv hr.le
    simpa only [Real.div_rpow zero_le_one hTp.le,Real.one_rpow,
      Real.div_rpow (mul_pos hc hb).le (Real.rpow_pos_of_pos hN a).le,
      Real.mul_rpow hc.le hb.le,←Real.rpow_mul hN.le] using hh
  have hbpower : b ≤ N^(-(9:ℝ)/20) := by
    calc
      _ ≤ N^((11:ℝ)/20)/N := (le_div_iff₀ hN).mpr (by change N*b ≤ _ at hshift; nlinarith only [hshift])
      _ = _ := by nth_rw 2 [←Real.rpow_one N]; rw [←Real.rpow_sub hN]; norm_num
  have hexp : (2-a*r)+(-(9:ℝ)/20)*(1/2+r)=31/40+31/(20*n)-2/n^2+ε/n := by
    dsimp only [a,r,n]
    field_simp
    ring
  change N^2*Real.sqrt b/T^r ≤ c^r*N^(31/40+31/(20*n)-2/n^2+ε/n)
  calc
    _ = (N^2*Real.sqrt b)*(1/T^r) := by ring
    _ ≤ (N^2*Real.sqrt b)*(c^r*b^r/N^(a*r)) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = c^r*N^(2-a*r)*b^(1/2+r) := by
      rw [Real.rpow_sub hN,Real.rpow_two,Real.sqrt_eq_rpow,Real.rpow_add hb]
      ring
    _ ≤ c^r*N^(2-a*r)*(N^(-(9:ℝ)/20))^(1/2+r) := by gcongr
    _ = _ := by
      rw [←Real.rpow_mul hN.le,mul_assoc,←Real.rpow_add hN,hexp]

#print axioms tailFixedShiftMain_le_power

set_option maxHeartbeats 2200000 in
/-- A uniform power saving on the actual small-shift mixed-cell set at
every tail order. The adaptive block, curvature and range hypotheses are
all derived from the physical source parameters. -/
theorem tailMixedPairs_card_small_far {k : ℕ} (hk : 4 ≤ k) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (S : Finset ℕ) (N T t u : ℝ), C ≤ N →
      0 < T → T ≤ N^(k+1) → T ≤ t → t ≤ 2*T → u ≤ 2*T →
      N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))) ≤ u-t →
      N*(tailHeightRatio (k+1) t u-1) ≤ N^((11:ℝ)/20) →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ((tailMixedPairs S k (Nat.ceil (N/T^(1/((k:ℝ)+2)))) t u).card:ℝ) ≤
        N^((99:ℝ)/100) := by
  let n : ℝ := (k:ℝ)+2
  let r : ℝ := 1/n
  let ε : ℝ := 1/(10000*n)
  let ρ : ℝ := 49/50-ε
  let c : ℝ := 2*((k:ℝ)+1)*2^k
  let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
  let m : ℝ := 16*((k:ℝ)+1)*2^k*K^2/Real.pi
  let s : ℝ := Real.sqrt (16*Real.pi*2^(k+3)/((k:ℝ)+1))
  let D : ℝ := 20*(2*c*m+5)*(1+s*c^r)
  have hn6 : 6 ≤ n := by dsimp only [n]; exact_mod_cast (by omega : 6 ≤ k+2)
  have hn : 0 < n := by linarith only [hn6]
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr6 : r ≤ 1/6 := by dsimp only [r]; exact one_div_le_one_div_of_le (by norm_num) hn6
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεr : ε=r/10000 := by dsimp only [ε,r]; field_simp
  have hεmax : ε ≤ 1/60000 := by rw [hεr]; linarith only [hr6]
  have hεsmall : ε < 1/((k:ℝ)+2) := by
    change ε < r
    rw [hεr]
    linarith only [hr]
  have hρ : 11/20 ≤ ρ := by dsimp only [ρ]; linarith only [hεmax]
  have hexponent : 31/40+31/(20*n)-2/n^2+ε/n ≤ ρ := by
    have hprod := mul_nonneg (show 0 ≤ 1/6-r by linarith only [hr6])
      (show 0 ≤ 73/60-2*r by linarith only [hr6])
    have hg : 31/40+31*r/20-2*r^2 ≤ 44/45 := by nlinarith only [hprod]
    have hεprod := mul_le_mul_of_nonneg_left hr6 hε.le
    have hid : 31/40+31/(20*n)-2/n^2+ε/n=31/40+31*r/20-2*r^2+ε*r := by
      dsimp only [r]
      field_simp
    rw [hid]
    dsimp only [ρ]
    nlinarith only [hg,hεprod,hεmax]
  have hc : 0 < c := by dsimp only [c]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hm : 0 < m := by dsimp only [m]; positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hD : 0 < D := by dsimp only [D]; positivity
  obtain ⟨C₀,hC₀,hbase⟩ := tailMixedPairs_card_fixed_shifts_far (by omega : 1 ≤ k) hεsmall
  have hev : ∀ᶠ N : ℝ in Filter.atTop, c ≤ N^(r-ε) ∧ D ≤ N^((1:ℝ)/100) := by
    filter_upwards [eventually_const_log_pow_le_rpow c hc.le 0
        (η:=r-ε) (by change 0 < 1/((k:ℝ)+2)-ε; linarith only [hεsmall]),
      eventually_const_log_pow_le_rpow D hD.le 0 (η:=(1:ℝ)/100) (by norm_num)] with N h1 h2
    simpa only [pow_zero,mul_one] using And.intro h1 h2
  obtain ⟨C₁,hC₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 2 (max C₀ C₁),le_max_left _ _,?_⟩
  intro S N T t u hCN hTp hT htT ht2T hu2T hfar hshift hS
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hCN
  have hN1 : 1 ≤ N := by linarith only [hN2]
  have hNp : 0 < N := by linarith only [hN2]
  have hNC₀ : C₀ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hCN)
  have hNC₁ : C₁ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hCN)
  have hconst := hC₁ N hNC₁
  have ht : 0 < t := hTp.trans_le htT
  have htu : t < u := sub_pos.mp ((Real.rpow_pos_of_pos hNp _).trans_le hfar)
  have hu : u ≤ 2*t := by linarith only [htT,hu2T]
  let b := tailHeightRatio (k+1) t u-1
  let X := T^r
  let W := N*b
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hX : 0 < X := Real.rpow_pos_of_pos hTp _
  have hW : 0 < W := by dsimp only [W]; positivity
  have hXN : X ≤ N := by
    calc
      _ ≤ (N^(k+1))^r := Real.rpow_le_rpow hTp.le hT hr.le
      _ = N^(((k:ℝ)+1)/n) := by
        rw [←Real.rpow_natCast N (k+1),←Real.rpow_mul hNp.le]
        congr 1
        dsimp only [r]
        push_cast
        ring
      _ ≤ N := by
        have he : ((k:ℝ)+1)/n ≤ (1:ℝ) :=
          (div_le_iff₀ hn).mpr (by dsimp only [n]; linarith)
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 he
  have hgap := tailHeightRatio_adaptive_gap (d:=k+1) (ε:=ε) (by omega) hNp hTp ht
    htu hu ht2T hT (by convert hfar using 1; congr 1; dsimp only [ε,n]; push_cast; ring)
  have hgap' : N^(r-ε)/c ≤ b*X := by
    convert hgap using 1 <;> dsimp only [c,b,X,r,n] <;>
      simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] <;> ring_nf
  have hWone : 1 ≤ W := by
    have hh : 1 ≤ N^(r-ε)/c := (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hconst.1)
    have hh' : b*X ≤ W := by dsimp only [W]; nlinarith only [mul_le_mul_of_nonneg_left hXN hb.le]
    exact (hh.trans hgap').trans hh'
  have hWρ : W ≤ N^ρ := hshift.trans (Real.rpow_le_rpow_of_exponent_le hN1 hρ)
  have hmain := tailFixedShiftMain_le_power (ε:=ε) hNp hTp ht htu hu ht2T hfar hshift
  have hmainρ : N^2*Real.sqrt b/X ≤ c^r*N^ρ := hmain.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hexponent) (by positivity))
  have hrange := tailFixedShiftRange_le_power (ε:=ε) hNp hTp ht htu hu ht2T hT hfar
  have hrange' : t/(N^k*b*X^2) ≤ 2*c*N^ε := by
    convert hrange using 1
    dsimp only [c]
    ring
  have hunit : 1 ≤ N^ε := Real.one_le_rpow hN1 hε.le
  have hmid : m*t/(N^k*b*X^2)+5 ≤ (2*c*m+5)*N^ε := by
    have hh := mul_le_mul_of_nonneg_left hrange' hm.le
    calc
      _ = m*(t/(N^k*b*X^2))+5 := by ring
      _ ≤ m*(2*c*N^ε)+5*N^ε := add_le_add hh (by linarith only [hunit])
      _ = _ := by ring
  have hcount := hbase S N T t u hNC₀ hTp hT htT ht2T hu2T hfar hS
  change ((tailMixedPairs S k (Nat.ceil (N/X)) t u).card:ℝ) ≤
    (4*N*b+1)*(m*t/(N^k*b*X^2)+5)*(4+4*s*N/(X*Real.sqrt b)) at hcount
  rw [show 4*N*b=4*W by dsimp only [W]; ring] at hcount
  have hrootb : (Real.sqrt b)^2=b := Real.sq_sqrt hb.le
  have hsqrtb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hid : (5*W)*((2*c*m+5)*N^ε)*(4+4*s*N/(X*Real.sqrt b)) =
      20*(2*c*m+5)*N^ε*(W+s*(N^2*Real.sqrt b/X)) := by
    dsimp only [W]
    field_simp
    linear_combination -20*N*s*hrootb
  change ((tailMixedPairs S k (Nat.ceil (N/X)) t u).card:ℝ) ≤ N^((99:ℝ)/100)
  calc
    _ ≤ (4*W+1)*(m*t/(N^k*b*X^2)+5)*(4+4*s*N/(X*Real.sqrt b)) := hcount
    _ ≤ (5*W)*((2*c*m+5)*N^ε)*(4+4*s*N/(X*Real.sqrt b)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (by linarith only [hWone]) hmid (by positivity) (by positivity)
    _ = 20*(2*c*m+5)*N^ε*(W+s*(N^2*Real.sqrt b/X)) := hid
    _ ≤ 20*(2*c*m+5)*N^ε*(N^ρ+s*(c^r*N^ρ)) := by gcongr
    _ = D*N^((49:ℝ)/50) := by
      have he : ε+ρ=(49:ℝ)/50 := by dsimp only [ρ]; ring
      dsimp only [D]
      rw [←he,Real.rpow_add hNp]
      ring
    _ ≤ N^((1:ℝ)/100)*N^((49:ℝ)/50) := mul_le_mul_of_nonneg_right hconst.2 (by positivity)
    _ = _ := by rw [←Real.rpow_add hNp]; norm_num

#print axioms tailMixedPairs_card_small_far

set_option maxHeartbeats 1600000 in
/-- On the complementary large-shift branch the actual quadratic stationary
error scale decays by a fixed power, at every tail order. -/
theorem tailStationaryErrorScale_le_power {k : ℕ} {N T t u : ℝ}
    (hk : 4 ≤ k) (hN : 1 ≤ N) (hTp : 0 < T) (ht : 0 < t)
    (htu : t < u) (hu : u ≤ 2*t) (htT : t ≤ 2*T)
    (hfar : N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))) ≤ u-t)
    (hshift : N^((11:ℝ)/20) ≤ N*(tailHeightRatio (k+1) t u-1)) :
    let b := tailHeightRatio (k+1) t u-1
    let n : ℝ := (k:ℝ)+2
    let X := T^(1/n)
    let C := (2*((k:ℝ)+1)*2^k)^(2/n)
    N/(b*X^2) ≤ C*N^(-(1:ℝ)/10) ∧ N/X^2 ≤ C*N^(-(1:ℝ)/10) := by
  let b := tailHeightRatio (k+1) t u-1
  let n : ℝ := (k:ℝ)+2
  let r : ℝ := 1/n
  let ε : ℝ := 1/(10000*n)
  let c : ℝ := 2*((k:ℝ)+1)*2^k
  let a : ℝ := (k:ℝ)+2/n-ε
  let X := T^(1/n)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hn6 : 6 ≤ n := by dsimp only [n]; exact_mod_cast (by omega : 6 ≤ k+2)
  have hn : 0 < n := by linarith only [hn6]
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr6 : r ≤ 1/6 := by dsimp only [r]; exact one_div_le_one_div_of_le (by norm_num) hn6
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεr : ε=r/10000 := by dsimp only [ε,r]; field_simp
  have hεmax : ε ≤ 1/60000 := by rw [hεr]; linarith only [hr6]
  have hc : 0 < c := by dsimp only [c]; positivity
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hb1 : b ≤ 1 := by
    have hh := (tailHeightRatio_bounds (by omega : 1 ≤ k+1) ht htu hu).2.1
    dsimp only [b]
    linarith only [hh]
  have hX : 0 < X := Real.rpow_pos_of_pos hTp _
  have he : -1+2/n ≤ 0 := by
    calc
      _ = -1+2*r := by dsimp only [r]; ring
      _ ≤ 0 := by linarith only [hr6]
  have hlink : N^a ≤ c*T*b := by
    have hh := tailHeightRatio_linked_height (d:=k+1) (by omega) ht htu hu htT
    have hh' : (u-t)/c ≤ T*b := by
      simpa only [c,b,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] using hh
    have hh'' := (div_le_iff₀ hc).mp hh'
    change N^a ≤ u-t at hfar
    nlinarith only [hfar,hh'']
  have hTinv : 1/T ≤ c*b/N^a :=
    (div_le_div_iff₀ hTp (by positivity)).mpr (by nlinarith only [hlink])
  have hroot : 1/T^(2/n) ≤ c^(2/n)*b^(2/n)/N^(a*(2/n)) := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1/T) hTinv (by positivity : 0 ≤ 2/n)
    simpa only [Real.div_rpow zero_le_one hTp.le,Real.one_rpow,
      Real.div_rpow (mul_pos hc hb).le (Real.rpow_pos_of_pos hNp a).le,
      Real.mul_rpow hc.le hb.le,←Real.rpow_mul hNp.le] using hh
  have hbpower : N^(-(9:ℝ)/20) ≤ b := by
    calc
      _ = N^((11:ℝ)/20)/N := by symm; nth_rw 2 [←Real.rpow_one N]; rw [←Real.rpow_sub hNp]; norm_num
      _ ≤ b := (div_le_iff₀ hNp).mpr (by change _ ≤ N*b at hshift; nlinarith only [hshift])
  have hexponent : (1-a*(2/n))+(-(9:ℝ)/20)*(-1+2/n) ≤ -(1:ℝ)/10 := by
    have hprod := mul_nonneg (show 0 ≤ 1/6-r by linarith only [hr6])
      (show 0 ≤ 73/30-4*r by linarith only [hr6])
    have hg : -11/20+31*r/10-4*r^2 ≤ -13/90 := by nlinarith only [hprod]
    have hεprod := mul_le_mul_of_nonneg_left hr6 hε.le
    have hid : (1-a*(2/n))+(-(9:ℝ)/20)*(-1+2/n)=-11/20+31*r/10-4*r^2+2*ε*r := by
      dsimp only [a,r,n]
      field_simp
      ring
    rw [hid]
    nlinarith only [hg,hεprod,hεmax]
  have hmain : N/(b*X^2) ≤ c^(2/n)*N^(-(1:ℝ)/10) := by
    calc
      _ = (N*b^(-1:ℝ))*(1/T^(2/n)) := by
        dsimp only [X]
        rw [←Real.rpow_mul_natCast hTp.le]
        norm_num only [Nat.cast_ofNat]
        rw [show 1/n*(2:ℝ)=2/n by ring,Real.rpow_neg_one]
        field_simp
      _ ≤ (N*b^(-1:ℝ))*(c^(2/n)*b^(2/n)/N^(a*(2/n))) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = c^(2/n)*N^(1-a*(2/n))*b^(-1+2/n) := by
        rw [Real.rpow_sub hNp,Real.rpow_one,Real.rpow_add hb]
        ring
      _ ≤ c^(2/n)*N^(1-a*(2/n))*(N^(-(9:ℝ)/20))^(-1+2/n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hbpower he
      _ = c^(2/n)*N^((1-a*(2/n))+(-(9:ℝ)/20)*(-1+2/n)) := by
        rw [←Real.rpow_mul hNp.le,mul_assoc,←Real.rpow_add hNp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hexponent) (by positivity)
  refine ⟨hmain,?_⟩
  apply le_trans _ hmain
  apply div_le_div_of_nonneg_left hNp.le (by positivity)
  nlinarith only [mul_le_mul_of_nonneg_right hb1 (sq_nonneg X)]

#print axioms tailStationaryErrorScale_le_power

/-- Linked height/root monomials used in the three terms of the actual
stationary count and in their products with the fibre diameter. -/
theorem tailAdaptiveHeightMonomial {d j : ℕ} {N T t : ℝ}
    (hN : 0 < N) (hTp : 0 < T) (hT : T ≤ N^d) (ht : t ≤ 2*T)
    (hj : j ≤ d+1) :
    t/(N^d*(T^(1/((d:ℝ)+1)))^j) ≤
      2*N^(-(d:ℝ)*(j:ℝ)/((d:ℝ)+1)) := by
  have hn : 0 < (d:ℝ)+1 := by positivity
  have hjR : (j:ℝ) ≤ (d:ℝ)+1 := by exact_mod_cast hj
  have he : 0 ≤ 1-(j:ℝ)/((d:ℝ)+1) := by
    have hh : (j:ℝ)/((d:ℝ)+1) ≤ 1 := (div_le_iff₀ hn).mpr (by simpa only [one_mul] using hjR)
    linarith only [hh]
  have hroot : (T^(1/((d:ℝ)+1)))^j=T^((j:ℝ)/((d:ℝ)+1)) := by
    rw [←Real.rpow_mul_natCast hTp.le]
    congr 1
    ring
  calc
    _ ≤ 2*T/(N^d*(T^(1/((d:ℝ)+1)))^j) := div_le_div_of_nonneg_right ht (by positivity)
    _ = 2*T^(1-(j:ℝ)/((d:ℝ)+1))/N^d := by
      rw [hroot,Real.rpow_sub hTp,Real.rpow_one]
      field_simp
    _ ≤ 2*(N^d)^(1-(j:ℝ)/((d:ℝ)+1))/N^d := by gcongr
    _ = _ := by
      rw [←Real.rpow_natCast N d,←Real.rpow_mul hN.le,mul_div_assoc,←Real.rpow_sub hN]
      congr 2
      ring

#print axioms tailAdaptiveHeightMonomial

set_option maxHeartbeats 2000000 in
/-- The three physical terms in the stationary count, including their
products with the actual fibre scale, have a uniform power saving. -/
theorem tailStationaryCountScale_le_power {d : ℕ} {N T t W : ℝ}
    (hd : 5 ≤ d) (hN : 1 ≤ N) (hTp : 0 < T) (ht : 0 < t)
    (hT : T ≤ N^d) (htT : t ≤ 2*T)
    (hWlo : N^((11:ℝ)/20) ≤ W) (hWup : W ≤ N) :
    let n : ℝ := (d:ℝ)+1
    let X := T^(1/n)
    let B := N^2/(W*X)
    let A := t*N^2/(N^d*X^2)
    let C := (t*W^2/N^d)^((1:ℝ)/3)
    let E := t*Real.sqrt W/N^d
    (1+B)*(A+C+E) ≤ 12*N^((59:ℝ)/60) := by
  let n : ℝ := (d:ℝ)+1
  let X := T^(1/n)
  let B := N^2/(W*X)
  let A := t*N^2/(N^d*X^2)
  let C := (t*W^2/N^d)^((1:ℝ)/3)
  let E := t*Real.sqrt W/N^d
  let Z := N^((59:ℝ)/60)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hn6 : 6 ≤ n := by dsimp only [n]; exact_mod_cast (by omega : 6 ≤ d+1)
  have hn : 0 < n := by linarith only [hn6]
  have h2n : 2/n ≤ 1/3 := (div_le_iff₀ hn).mpr (by nlinarith only [hn6])
  have h3n : 3/n ≤ 1/2 := (div_le_iff₀ hn).mpr (by nlinarith only [hn6])
  have hWp : 0 < W := (Real.rpow_pos_of_pos hNp _).trans_le hWlo
  have hX : 0 < X := Real.rpow_pos_of_pos hTp _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hZ : 0 < Z := Real.rpow_pos_of_pos hNp _
  have hmono (j : ℕ) (hj : j ≤ d+1) : t/(N^d*X^j) ≤ 2*N^(-(d:ℝ)*(j:ℝ)/n) :=
    tailAdaptiveHeightMonomial hNp hTp hT htT hj
  have hY : t/N^d ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < N^d)).mpr
    nlinarith only [htT,hT]
  have hZcube : (2*Z)^3=8*N^((59:ℝ)/20) := by
    dsimp only [Z]
    rw [mul_pow,←Real.rpow_mul_natCast hNp.le]
    norm_num
  have hZsquare : (2*Z)^2=4*N^((59:ℝ)/30) := by
    dsimp only [Z]
    rw [mul_pow,←Real.rpow_mul_natCast hNp.le]
    norm_num
  have hAup : A ≤ 2*Z := by
    calc
      _ = N^2*(t/(N^d*X^2)) := by dsimp only [A]; ring
      _ ≤ N^2*(2*N^(-(d:ℝ)*(2:ℕ)/n)) := mul_le_mul_of_nonneg_left (hmono 2 (by omega)) (by positivity)
      _ = 2*N^(2/n) := by
        rw [←Real.rpow_two,mul_left_comm,←Real.rpow_add hNp]
        congr 2
        dsimp only [n]
        norm_num only [Nat.cast_ofNat]
        field_simp
        ring
      _ ≤ 2*Z := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN
        (by linarith only [h2n] : 2/n ≤ (59:ℝ)/60)) (by norm_num)
  have hBA : B*A ≤ 2*Z := by
    calc
      _ = (N^4/W)*(t/(N^d*X^3)) := by dsimp only [B,A]; field_simp
      _ ≤ (N^4/W)*(2*N^(-(d:ℝ)*(3:ℕ)/n)) := mul_le_mul_of_nonneg_left (hmono 3 (by omega)) (by positivity)
      _ = 2*N^(1+3/n)/W := by
        rw [←Real.rpow_ofNat N 4]
        have he : 4+(-(d:ℝ)*(3:ℕ)/n)=1+3/n := by dsimp only [n]; norm_num only [Nat.cast_ofNat]; field_simp; ring
        rw [div_mul_eq_mul_div]
        rw [show N^(4:ℝ)*(2*N^(-(d:ℝ)*(3:ℕ)/n))=2*(N^(4:ℝ)*N^(-(d:ℝ)*(3:ℕ)/n)) by ring,
          ←Real.rpow_add hNp,he]
      _ ≤ 2*N^(1+3/n)/N^((11:ℝ)/20) := by gcongr
      _ = 2*N^(9/20+3/n) := by rw [mul_div_assoc,←Real.rpow_sub hNp]; congr 2; ring
      _ ≤ 2*Z := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN
        (by linarith only [h3n] : 9/20+3/n ≤ (59:ℝ)/60)) (by norm_num)
  have hCcube : C^3=t*W^2/N^d := by
    dsimp only [C]
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ t*W^2/N^d)]
    norm_num
  have hCcubeUp : C^3 ≤ (2*Z)^3 := by
    rw [hCcube,hZcube]
    calc
      _ = (t/N^d)*W^2 := by ring
      _ ≤ 2*N^2 := mul_le_mul hY (pow_le_pow_left₀ hWp.le hWup 2) (by positivity) (by norm_num)
      _ ≤ 8*N^((59:ℝ)/20) := by
        rw [←Real.rpow_two]
        exact mul_le_mul (by norm_num) (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) (by positivity) (by norm_num)
  have hCup : C ≤ 2*Z := by
    by_contra! hh
    exact (not_lt_of_ge hCcubeUp) (pow_lt_pow_left₀ hh (by positivity) (by decide : 3 ≠ 0))
  have hBCcube : (B*C)^3 ≤ (2*Z)^3 := by
    rw [mul_pow,hCcube,hZcube]
    calc
      _ = (N^6/W)*(t/(N^d*X^3)) := by dsimp only [B]; field_simp
      _ ≤ (N^6/W)*(2*N^(-(d:ℝ)*(3:ℕ)/n)) := mul_le_mul_of_nonneg_left (hmono 3 (by omega)) (by positivity)
      _ = 2*N^(3+3/n)/W := by
        rw [←Real.rpow_ofNat N 6]
        have he : 6+(-(d:ℝ)*(3:ℕ)/n)=3+3/n := by dsimp only [n]; norm_num only [Nat.cast_ofNat]; field_simp; ring
        rw [div_mul_eq_mul_div]
        rw [show N^(6:ℝ)*(2*N^(-(d:ℝ)*(3:ℕ)/n))=2*(N^(6:ℝ)*N^(-(d:ℝ)*(3:ℕ)/n)) by ring,
          ←Real.rpow_add hNp,he]
      _ ≤ 2*N^(3+3/n)/N^((11:ℝ)/20) := by gcongr
      _ = 2*N^(49/20+3/n) := by rw [mul_div_assoc,←Real.rpow_sub hNp]; congr 2; ring
      _ ≤ 8*N^((59:ℝ)/20) := mul_le_mul (by norm_num)
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [h3n])) (by positivity) (by norm_num)
  have hBC : B*C ≤ 2*Z := by
    by_contra! hh
    exact (not_lt_of_ge hBCcube) (pow_lt_pow_left₀ hh (by positivity) (by decide : 3 ≠ 0))
  have hEsquare : E^2=(t/N^d)^2*W := by
    dsimp only [E]
    rw [div_pow,mul_pow,Real.sq_sqrt hWp.le]
    ring
  have hEsquareUp : E^2 ≤ (2*Z)^2 := by
    rw [hEsquare,hZsquare]
    calc
      _ ≤ (2:ℝ)^2*N := mul_le_mul (pow_le_pow_left₀ (by positivity) hY 2) hWup hWp.le (by norm_num)
      _ ≤ 4*N^((59:ℝ)/30) := by
        norm_num only [show (2:ℝ)^2=4 by norm_num]
        gcongr
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1:ℝ) ≤ 59/30)
  have hEup : E ≤ 2*Z := by
    by_contra! hh
    exact (not_lt_of_ge hEsquareUp) (pow_lt_pow_left₀ hh (by positivity) (by decide : 2 ≠ 0))
  have hBEsquare : (B*E)^2 ≤ (2*Z)^2 := by
    rw [mul_pow,hEsquare,hZsquare]
    calc
      _ = (N^4/W)*(t/(N^d*X))^2 := by dsimp only [B]; field_simp
      _ ≤ (N^4/W)*(2*N^(-(d:ℝ)/n))^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        simpa only [pow_one,Nat.cast_one,mul_one] using hmono 1 (by omega)
      _ = 4*N^(2+2/n)/W := by
        rw [mul_pow,←Real.rpow_mul_natCast hNp.le,←Real.rpow_ofNat N 4]
        norm_num only [Nat.cast_ofNat,show (2:ℝ)^2=4 by norm_num]
        have he : 4+(-(d:ℝ)/n)*2=2+2/n := by dsimp only [n]; field_simp; ring
        rw [div_mul_eq_mul_div]
        rw [show N^(4:ℝ)*(4*N^(-(d:ℝ)/n*2))=4*(N^(4:ℝ)*N^(-(d:ℝ)/n*2)) by ring,
          ←Real.rpow_add hNp,he]
      _ ≤ 4*N^(2+2/n)/N^((11:ℝ)/20) := by gcongr
      _ = 4*N^(29/20+2/n) := by rw [mul_div_assoc,←Real.rpow_sub hNp]; congr 2; ring
      _ ≤ 4*N^((59:ℝ)/30) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [h2n])) (by norm_num)
  have hBE : B*E ≤ 2*Z := by
    by_contra! hh
    exact (not_lt_of_ge hBEsquare) (pow_lt_pow_left₀ hh (by positivity) (by decide : 2 ≠ 0))
  change (1+B)*(A+C+E) ≤ 12*Z
  nlinarith only [hAup,hBA,hCup,hBC,hEup,hBE]

#print axioms tailStationaryCountScale_le_power

set_option maxHeartbeats 1600000 in
/-- Exact conversion of the three stationary-label terms to physical
monomials. In particular, the label and shift scales remain linked. -/
theorem tailStationaryTerms_le_physical {k : ℕ} {N X t b Q F G L P Z : ℝ}
    (hN : 0 < N) (hX : 0 < X) (ht : 0 < t) (hb : 0 < b) (hb1 : b ≤ 1)
    (hQ : 0 < Q) (hQupper : Q ≤ t*b/N^k)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hL : 0 ≤ L) (hP : 0 < P) (hZ : 0 < Z) :
    let W := N*b
    let A := t*N^2/(N^(k+1)*X^2)
    let C := (t*W^2/N^(k+1))^((1:ℝ)/3)
    let E := t*Real.sqrt W/N^(k+1)
    let M := L*(F+G)+L*P^((1:ℝ)/3)+Z^(-(1:ℝ)/2)
    L*Q*((F*N/(b*X^2)+G*N/X^2)+(P*(W/Q^2))^((1:ℝ)/3))+
      (Z*(W/Q^2))^(-(1:ℝ)/2) ≤ M*(A+C+E) := by
  let W := N*b
  let A := t*N^2/(N^(k+1)*X^2)
  let C := (t*W^2/N^(k+1))^((1:ℝ)/3)
  let E := t*Real.sqrt W/N^(k+1)
  let M := L*(F+G)+L*P^((1:ℝ)/3)+Z^(-(1:ℝ)/2)
  have hW : 0 < W := by dsimp only [W]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hQW : Q ≤ t*W/N^(k+1) := by
    convert hQupper using 1
    dsimp only [W]
    rw [pow_succ]
    field_simp
  have herr : Q*(F*N/(b*X^2)+G*N/X^2) ≤ (F+G)*A := by
    calc
      _ ≤ (t*b/N^k)*(F*N/(b*X^2)+G*N/X^2) := mul_le_mul_of_nonneg_right hQupper (by positivity)
      _ = F*A+G*b*A := by dsimp only [A]; rw [pow_succ]; field_simp; ring
      _ ≤ (F+G)*A := by
        have hh := mul_le_mul_of_nonneg_right hb1 (mul_nonneg hG hA)
        nlinarith only [hh]
  have hcubep (Y : ℝ) (hY : 0 ≤ Y) : (Y^((1:ℝ)/3))^3=Y := by
    rw [←Real.rpow_mul_natCast hY]
    norm_num
  have hthirdCube : (Q*(P*(W/Q^2))^((1:ℝ)/3))^3 ≤ (P^((1:ℝ)/3)*C)^3 := by
    rw [mul_pow,mul_pow,hcubep _ (by positivity),hcubep P hP.le]
    have hCp : C^3=t*W^2/N^(k+1) := hcubep _ (by positivity)
    rw [hCp]
    have he : Q^3*(P*(W/Q^2))=P*W*Q := by field_simp
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hQW (mul_pos hP hW).le
    convert hh using 1; ring
  have hthird : Q*(P*(W/Q^2))^((1:ℝ)/3) ≤ P^((1:ℝ)/3)*C := by
    by_contra! hh
    exact (not_lt_of_ge hthirdCube) (pow_lt_pow_left₀ hh (by positivity) (by decide : 3 ≠ 0))
  have hsqrtW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hrootW : (Real.sqrt W)^2=W := Real.sq_sqrt hW.le
  have hQsqrt : Q/Real.sqrt W ≤ E := by
    apply (div_le_iff₀ hsqrtW).mpr
    have he : E*Real.sqrt W=t*W/N^(k+1) := by
      dsimp only [E]
      rw [div_mul_eq_mul_div,mul_assoc,←pow_two,hrootW]
    rw [he]
    exact hQW
  have hinvEq : (W/Q^2)^(-(1:ℝ)/2)=Q/Real.sqrt W := by
    rw [show -(1:ℝ)/2=-((1:ℝ)/2) by ring,Real.rpow_neg (by positivity : 0 ≤ W/Q^2),
      ←Real.sqrt_eq_rpow,Real.sqrt_div hW.le,Real.sqrt_sq hQ.le]
    field_simp
  have hinv : (Z*(W/Q^2))^(-(1:ℝ)/2) ≤ Z^(-(1:ℝ)/2)*E := by
    rw [Real.mul_rpow hZ.le (by positivity : 0 ≤ W/Q^2),hinvEq]
    exact mul_le_mul_of_nonneg_left hQsqrt (by positivity)
  have hweightA : 0 ≤ L*(F+G) := by positivity
  have hweightC : 0 ≤ L*P^((1:ℝ)/3) := by positivity
  have hweightE : 0 ≤ Z^(-(1:ℝ)/2) := by positivity
  have hMa : L*(F+G) ≤ M := by dsimp only [M]; linarith only [hweightC,hweightE]
  have hMc : L*P^((1:ℝ)/3) ≤ M := by dsimp only [M]; linarith only [hweightA,hweightE]
  have hMe : Z^(-(1:ℝ)/2) ≤ M := by dsimp only [M]; linarith only [hweightA,hweightC]
  change L*Q*((F*N/(b*X^2)+G*N/X^2)+(P*(W/Q^2))^((1:ℝ)/3))+
    (Z*(W/Q^2))^(-(1:ℝ)/2) ≤ M*(A+C+E)
  calc
    _ = L*(Q*(F*N/(b*X^2)+G*N/X^2))+L*(Q*(P*(W/Q^2))^((1:ℝ)/3))+
        (Z*(W/Q^2))^(-(1:ℝ)/2) := by ring
    _ ≤ L*((F+G)*A)+L*(P^((1:ℝ)/3)*C)+Z^(-(1:ℝ)/2)*E :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left herr hL) (mul_le_mul_of_nonneg_left hthird hL)) hinv
    _ ≤ M*A+M*C+M*E := by
      apply add_le_add _ (mul_le_mul_of_nonneg_right hMe hE)
      rw [←mul_assoc,←mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_right hMa hA) (mul_le_mul_of_nonneg_right hMc hC)
    _ = _ := by ring

#print axioms tailStationaryTerms_le_physical

set_option maxHeartbeats 1600000 in
/-- Uniform discharge of the stationary-count numerical conditions from
the genuine far-height cutoff on the large-shift branch. -/
theorem tailStationaryFarNumerics {k : ℕ} (hk : 4 ≤ k) (J : ℝ) (hJ : 1 ≤ J) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (N T t u : ℝ), C ≤ N →
      0 < T → T ≤ N^(k+1) → T ≤ t → t ≤ 2*T → u ≤ 2*T →
      N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))) ≤ u-t →
      N^((11:ℝ)/20) ≤ N*(tailHeightRatio (k+1) t u-1) →
      let b := tailHeightRatio (k+1) t u-1
      let X := T^(1/((k:ℝ)+2))
      J ≤ b*X ∧ J ≤ tailLabelLower k N t u ∧ 1 ≤ X ∧
        N/(b*X^2) ≤ 1/(4*J) ∧ N/X^2 ≤ 1/(4*J) := by
  let n : ℝ := (k:ℝ)+2
  let r : ℝ := 1/n
  let ε : ℝ := 1/(10000*n)
  let c : ℝ := ((k:ℝ)+1)*2^k
  let c₀ : ℝ := 2*((k:ℝ)+1)*2^k
  let qden : ℝ := 8*Real.pi*k*2^k
  let M : ℝ := c₀^(2/n)
  have hkR : (4:ℝ) ≤ k := by exact_mod_cast hk
  have hn : 0 < n := by dsimp only [n]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεr : ε=r/10000 := by dsimp only [ε,r]; field_simp
  have hp : 0 < r-ε := by rw [hεr]; linarith only [hr]
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc₀ : 0 < c₀ := by dsimp only [c₀]; positivity
  have hqden : 0 < qden := by dsimp only [qden]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hev : ∀ᶠ N : ℝ in Filter.atTop,
      c₀*J*(qden+1) ≤ N^(r-ε) ∧ 4*J*M ≤ N^((1:ℝ)/10) := by
    filter_upwards [eventually_const_log_pow_le_rpow (c₀*J*(qden+1)) (by positivity) 0 hp,
      eventually_const_log_pow_le_rpow (4*J*M) (by positivity) 0 (η:=(1:ℝ)/10) (by norm_num)] with N h1 h2
    simpa only [pow_zero,mul_one] using And.intro h1 h2
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 2 C,le_max_left _ _,?_⟩
  intro N T t u hCN hTp hT htT ht2T hu2T hfar hshift
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hCN
  have hN1 : 1 ≤ N := by linarith only [hN2]
  have hNp : 0 < N := by linarith only [hN2]
  have hconst := hC N ((le_max_right _ _).trans hCN)
  have ht : 0 < t := hTp.trans_le htT
  have htu : t < u := sub_pos.mp ((Real.rpow_pos_of_pos hNp _).trans_le hfar)
  have hu : u ≤ 2*t := by linarith only [htT,hu2T]
  let b := tailHeightRatio (k+1) t u-1
  let X := T^r
  let a := (k:ℝ)+2/n-ε
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hX : 0 < X := Real.rpow_pos_of_pos hTp _
  have hgap := tailHeightRatio_adaptive_gap (d:=k+1) (ε:=ε) (by omega) hNp hTp ht
    htu hu ht2T hT (by convert hfar using 1; congr 1; dsimp only [ε,n]; push_cast; ring)
  have hgap' : N^(r-ε)/c₀ ≤ b*X := by
    convert hgap using 1 <;> dsimp only [c₀,b,X,r,n] <;>
      simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] <;> ring_nf
  have hJb : J ≤ b*X := by
    apply le_trans _ hgap'
    apply (le_div_iff₀ hc₀).mpr
    have hh : c₀*J ≤ c₀*J*(qden+1) := by nlinarith only [mul_pos (mul_pos hc₀ hJp) hqden]
    nlinarith only [hh,hconst.1]
  have hexp : r-ε ≤ 2/n-ε := by
    rw [show 2/n=2*r by dsimp only [r]; ring]
    linarith only [hr]
  have hqpower : c*J*qden ≤ N^(2/n-ε) := by
    calc
      _ ≤ c₀*J*(qden+1) := by
        have hcRel : c₀=2*c := by dsimp only [c₀,c]; ring
        rw [hcRel]
        nlinarith only [mul_pos hc hJp,mul_pos (mul_pos hc hJp) hqden]
      _ ≤ N^(r-ε) := hconst.1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have htb := (tailHeightRatio_gap (d:=k+1) (by omega) ht htu hu).1
  have htb' : (u-t)/c ≤ t*b := by
    simpa only [c,b,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] using htb
  have hsplit : N^a=N^k*N^(2/n-ε) := by
    dsimp only [a]
    rw [←Real.rpow_natCast N k,←Real.rpow_add hNp]
    congr 1
    ring
  have hQt : J*qden*N^k ≤ t*b := by
    calc
      _ ≤ N^a/c := by
        apply (le_div_iff₀ hc).mpr
        rw [hsplit]
        have hh := mul_le_mul_of_nonneg_left hqpower (by positivity : 0 ≤ N^k)
        nlinarith only [hh]
      _ ≤ (u-t)/c := div_le_div_of_nonneg_right hfar hc.le
      _ ≤ _ := htb'
  have hQ : J ≤ tailLabelLower k N t u := by
    have he : tailLabelLower k N t u=t*b/(qden*N^k) := by
      dsimp only [tailLabelLower,qden]
      change (t*b/(4*(2*N)^k))/(2*Real.pi*k)=t*b/((8*Real.pi*k*2^k)*N^k)
      rw [mul_pow]
      field_simp
      norm_num
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < qden*N^k)).mpr
    nlinarith only [hQt]
  have ha : 0 ≤ a := by
    have hh : 0 < 2/n-ε := lt_of_lt_of_le hp hexp
    dsimp only [a]
    linarith only [hh,hkR]
  have hT1 : 1 ≤ T := (Real.one_le_rpow hN1 ha).trans (hfar.trans (by linarith only [htT,hu2T]))
  have hX1 : 1 ≤ X := Real.one_le_rpow hT1 hr.le
  have herrors := tailStationaryErrorScale_le_power hk hN1 hTp ht htu hu ht2T hfar hshift
  change N/(b*X^2) ≤ M*N^(-(1:ℝ)/10) ∧ N/X^2 ≤ M*N^(-(1:ℝ)/10) at herrors
  have hsmall : M*N^(-(1:ℝ)/10) ≤ 1/(4*J) := by
    have he : N^(-(1:ℝ)/10)=1/N^((1:ℝ)/10) := by
      rw [show -(1:ℝ)/10=-((1:ℝ)/10) by ring,Real.rpow_neg hNp.le]
      simp only [one_div]
    rw [he,mul_one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < N^((1:ℝ)/10)) (by positivity : 0 < 4*J)).mpr
    nlinarith only [hconst.2]
  exact ⟨hJb,hQ,hX1,herrors.1.trans hsmall,herrors.2.trans hsmall⟩

#print axioms tailStationaryFarNumerics

set_option maxHeartbeats 2400000 in
/-- Uniform power saving for the actual large-shift mixed-cell set. Every
stationary-label, curvature and rounding condition is derived from the
far cutoff and the linked physical scales. -/
theorem tailMixedPairs_card_large_far {k : ℕ} (hk : 4 ≤ k) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (S : Finset ℕ) (N T t u : ℝ), C ≤ N →
      0 < T → T ≤ N^(k+1) → T ≤ t → t ≤ 2*T → u ≤ 2*T →
      N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))) ≤ u-t →
      N^((11:ℝ)/20) ≤ N*(tailHeightRatio (k+1) t u-1) →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ((tailMixedPairs S k (Nat.ceil (N/T^(1/((k:ℝ)+2)))) t u).card:ℝ) ≤
        N^((99:ℝ)/100) := by
  let K : ℝ := 4*Real.pi*(k+1)*2^(k+1)
  let F : ℝ := 4*((k:ℝ)*((k:ℝ)+1)*2^(2*(k:ℝ)-1))*2^(k-1)*2^k
  let G : ℝ := 64*Real.pi*k*2^k
  let L := tailLabelStretch k
  let c : ℝ := ((k:ℝ)+1)/(k:ℝ)^2
  let P := 8*c
  let Z := c*(2*L)^(-1/(k:ℝ)-2)
  let M := L*(F*K^2+G)+L*P^((1:ℝ)/3)+Z^(-(1:ℝ)/2)
  let D := (1+32*K)*(52+144*L^3)*M
  let J : ℝ := 1+2*K+2*(k:ℝ)*2^(k-1)*K+16*Real.pi*k*2^k+F*K^2+G
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  have hL : 0 < L := by dsimp only [L,tailLabelStretch]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hP : 0 < P := by dsimp only [P]; positivity
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hJ : 1 ≤ J := by
    have h1 : 0 ≤ 2*(k:ℝ)*2^(k-1)*K := by positivity
    have h2 : 0 ≤ 16*Real.pi*k*2^k := by positivity
    have h3 : 0 ≤ F*K^2 := by positivity
    dsimp only [J]
    linarith only [hK,hG,h1,h2,h3]
  have hJK : 2*K ≤ J := by
    have hh : 0 ≤ 1+2*(k:ℝ)*2^(k-1)*K+16*Real.pi*k*2^k+F*K^2+G := by positivity
    dsimp only [J]
    linarith only [hh]
  have hJlabel : 2*(k:ℝ)*2^(k-1)*K ≤ J := by
    have hh : 0 ≤ 1+2*K+16*Real.pi*k*2^k+F*K^2+G := by positivity
    dsimp only [J]
    linarith only [hh]
  have hJround : 16*Real.pi*k*2^k ≤ J := by
    have hh : 0 ≤ 1+2*K+2*(k:ℝ)*2^(k-1)*K+F*K^2+G := by positivity
    dsimp only [J]
    linarith only [hh]
  have hJerr : F*K^2+G ≤ J := by
    have hh : 0 ≤ 1+2*K+2*(k:ℝ)*2^(k-1)*K+16*Real.pi*k*2^k := by positivity
    dsimp only [J]
    linarith only [hh]
  obtain ⟨C₀,hC₀,hnum⟩ := tailStationaryFarNumerics hk J hJ
  have hev : ∀ᶠ N : ℝ in Filter.atTop, 12*D ≤ N^((1:ℝ)/150) := by
    simpa only [pow_zero,mul_one] using
      eventually_const_log_pow_le_rpow (12*D) (by positivity) 0 (η:=(1:ℝ)/150) (by norm_num)
  obtain ⟨C₁,hC₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro S N T t u hCN hTp hT htT ht2T hu2T hfar hshift hS
  have hNC₀ : C₀ ≤ N := (le_max_left _ _).trans hCN
  have hN2 : 2 ≤ N := hC₀.trans hNC₀
  have hN1 : 1 ≤ N := by linarith only [hN2]
  have hNp : 0 < N := by linarith only [hN2]
  have ht : 0 < t := hTp.trans_le htT
  have htu : t < u := sub_pos.mp ((Real.rpow_pos_of_pos hNp _).trans_le hfar)
  have hu : u ≤ 2*t := by linarith only [htT,hu2T]
  let b := tailHeightRatio (k+1) t u-1
  let X := T^(1/((k:ℝ)+2))
  let H := Nat.ceil (N/X)
  let Q := tailLabelLower k N t u
  let W := N*b
  let B := N^2/(W*X)
  let A := t*N^2/(N^(k+1)*X^2)
  let C := (t*W^2/N^(k+1))^((1:ℝ)/3)
  let E := t*Real.sqrt W/N^(k+1)
  have hb : 0 < b := sub_pos.mpr (tailHeightRatio_bounds (by omega) ht htu hu).1
  have hb1 : b ≤ 1 := by
    have hh := (tailHeightRatio_bounds (d:=k+1) (by omega) ht htu hu).2
    dsimp only [b]
    linarith only [hh]
  have hX : 0 < X := Real.rpow_pos_of_pos hTp _
  have hW : 0 < W := by dsimp only [W]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  obtain ⟨hJb,hJQ,hX1,herror₁,herror₂⟩ :=
    hnum N T t u hNC₀ hTp hT htT ht2T hu2T hfar hshift
  change J ≤ b*X at hJb
  change J ≤ Q at hJQ
  change 1 ≤ X at hX1
  change N/(b*X^2) ≤ 1/(4*J) at herror₁
  change N/X^2 ≤ 1/(4*J) at herror₂
  have hQ : 0 < Q := zero_lt_one.trans_le (hJ.trans hJQ)
  have hscale : X^(k+2) ≤ t := by
    have he : X^(k+2)=T := by
      dsimp only [X]
      rw [←Real.rpow_natCast,←Real.rpow_mul hTp.le]
      have hn : (0:ℝ) < k+2 := by positivity
      rw [show (1/((k:ℝ)+2))*((k+2:ℕ):ℝ)=1 by push_cast; field_simp,Real.rpow_one]
    exact he.le.trans htT
  have hblock : N ≤ (H:ℝ)*X := (div_le_iff₀ hX).mp (Nat.le_ceil (N/X))
  have hround : 16*Real.pi*k*2^k ≤ b*X^2 := by
    apply (hJround.trans hJb).trans
    nlinarith only [mul_nonneg hb.le (mul_nonneg hX.le (sub_nonneg.mpr hX1))]
  have herror : F*K^2*N/(b*X^2)+G*N/X^2 < 1/2 := by
    calc
      _ = F*K^2*(N/(b*X^2))+G*(N/X^2) := by ring
      _ ≤ F*K^2*(1/(4*J))+G*(1/(4*J)) := by gcongr
      _ = (F*K^2+G)/(4*J) := by ring
      _ ≤ J/(4*J) := div_le_div_of_nonneg_right hJerr (by linarith only [hJ])
      _ = 1/4 := by have hJp : 0 < J := zero_lt_one.trans_le hJ; field_simp
      _ < _ := by norm_num
  have hcount := tailMixedPairs_card_stationary_adaptive S (k:=k) (H:=H)
    (by omega) hNp hX hscale hblock htu hu hT ht2T hu2T hS
    (hJK.trans hJb) (hJlabel.trans hJb) hround (hJ.trans hJQ) herror
  have hQupper : Q ≤ t*b/N^k := by
    have he : Q=(t*b/N^k)/(8*Real.pi*k*2^k) := by
      dsimp only [Q,tailLabelLower]
      change (t*b/(4*(2*N)^k))/(2*Real.pi*k)=(t*b/N^k)/(8*Real.pi*k*2^k)
      rw [mul_pow]
      field_simp
      norm_num
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hpow : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    have hden : 1 ≤ 8*Real.pi*k*2^k := by
      have hp : 1 ≤ 8*Real.pi := by linarith only [Real.pi_gt_three]
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp hk1) hpow
    rw [he]
    exact div_le_self (by positivity) hden
  have hterms := tailStationaryTerms_le_physical (k:=k) (F:=F*K^2) (G:=G)
    (L:=L) (P:=P) (Z:=Z) hNp hX ht hb hb1 hQ hQupper
    (by positivity) hG.le hL.le hP hZ
  change L*Q*((F*K^2*N/(b*X^2)+G*N/X^2)+(P*(W/Q^2))^((1:ℝ)/3))+
      (Z*(W/Q^2))^(-(1:ℝ)/2) ≤ M*(A+C+E) at hterms
  change ((tailMixedPairs S k H t u).card:ℝ) ≤
    (1+32*K*N/(b*X))*(52+144*L^3)*
      (L*Q*((F*K^2*N/(b*X^2)+G*N/X^2)+(P*(W/Q^2))^((1:ℝ)/3))+
        (Z*(W/Q^2))^(-(1:ℝ)/2)) at hcount
  have hfiber : 1+32*K*N/(b*X) ≤ (1+32*K)*(1+B) := by
    have he : N/(b*X)=B := by dsimp only [B,W]; field_simp
    rw [show 32*K*N/(b*X)=32*K*(N/(b*X)) by ring,he]
    nlinarith only [hK,hB]
  have hphysical : ((tailMixedPairs S k H t u).card:ℝ) ≤ D*((1+B)*(A+C+E)) := by
    apply hcount.trans
    calc
      _ ≤ ((1+32*K)*(1+B))*(52+144*L^3)*(M*(A+C+E)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hfiber (by positivity)
        · exact hterms
        · positivity
        · positivity
      _ = _ := by dsimp only [D]; ring
  have hscaleCount : (1+B)*(A+C+E) ≤ 12*N^((59:ℝ)/60) := by
    have hh := tailStationaryCountScale_le_power (d:=k+1) (W:=W)
      (by omega) hN1 hTp ht hT ht2T hshift
      (by dsimp only [W]; nlinarith only [mul_nonneg hNp.le (sub_nonneg.mpr hb1)])
    convert hh using 1
    dsimp only [B,A,C,E,X]
    push_cast
    ring_nf
  calc
    _ ≤ D*((1+B)*(A+C+E)) := hphysical
    _ ≤ D*(12*N^((59:ℝ)/60)) := mul_le_mul_of_nonneg_left hscaleCount hD.le
    _ = (12*D)*N^((59:ℝ)/60) := by ring
    _ ≤ N^((1:ℝ)/150)*N^((59:ℝ)/60) :=
      mul_le_mul_of_nonneg_right (hC₁ N ((le_max_right _ _).trans hCN)) (by positivity)
    _ = N^((99:ℝ)/100) := by rw [←Real.rpow_add hNp]; norm_num

#print axioms tailMixedPairs_card_large_far

/-- The full far-correlation mixed-cell set has a power saving at every
integer tail order, with no displacement case or counting assumption left
in the public hypotheses. -/
theorem tailMixedPairs_card_far {k : ℕ} (hk : 4 ≤ k) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (S : Finset ℕ) (N T t u : ℝ), C ≤ N →
      0 < T → T ≤ N^(k+1) → T ≤ t → t ≤ 2*T → u ≤ 2*T →
      N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))) ≤ u-t →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ((tailMixedPairs S k (Nat.ceil (N/T^(1/((k:ℝ)+2)))) t u).card:ℝ) ≤
        N^((99:ℝ)/100) := by
  obtain ⟨C₁,hC₁,hsmall⟩ := tailMixedPairs_card_small_far hk
  obtain ⟨C₂,hC₂,hlarge⟩ := tailMixedPairs_card_large_far hk
  refine ⟨max C₁ C₂,hC₁.trans (le_max_left _ _),?_⟩
  intro S N T t u hCN hTp hT htT ht2T hu2T hfar hS
  by_cases hshift : N*(tailHeightRatio (k+1) t u-1) ≤ N^((11:ℝ)/20)
  · exact hsmall S N T t u ((le_max_left _ _).trans hCN)
      hTp hT htT ht2T hu2T hfar hshift hS
  · exact hlarge S N T t u ((le_max_right _ _).trans hCN)
      hTp hT htT ht2T hu2T hfar (le_of_not_ge hshift) hS

#print axioms tailMixedPairs_card_far

/-- Sign normalization only: it preserves every derivative-distance cell. -/
def tailPositiveLogPhase (m : ℕ) (t a x : ℝ) : ℝ :=
  (-1:ℝ)^m*PintzEndpointResearch.logarithmicTaylorPhase t (a+x)

theorem tailPositiveLogPhase_coordinate (m j : ℕ) (t a x : ℝ) :
    GafniTao.heathBrownDerivativeCoordinate (tailPositiveLogPhase m t a) j x =
      (-1:ℝ)^m*GafniTao.heathBrownDerivativeCoordinate
        (PintzEndpointResearch.logarithmicTaylorPhase t) j (a+x) := by
  unfold tailPositiveLogPhase GafniTao.heathBrownDerivativeCoordinate
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_comp_const_add]
  ring

theorem tailPositiveLogPhase_contDiffAt (m j : ℕ) (t a : ℝ) {x : ℝ}
    (hx : 0 < a+x) : ContDiffAt ℝ j (tailPositiveLogPhase m t a) x := by
  unfold tailPositiveLogPhase PintzEndpointResearch.logarithmicTaylorPhase
  have hlog : ContDiffAt ℝ j (fun y : ℝ => Real.log (a+y)) x :=
    (contDiffAt_const.add contDiffAt_id).log hx.ne'
  exact contDiffAt_const.mul (contDiffAt_const.mul hlog)

theorem tailPositiveLogPhase_derivative (d : ℕ) (t a : ℝ) {x : ℝ}
    (hx : 0 < a+x) :
    iteratedDeriv (d+1) (tailPositiveLogPhase (d+1) t a) x =
      (d.factorial:ℝ)*t/(2*Real.pi*(a+x)^(d+1)) := by
  unfold tailPositiveLogPhase
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_comp_const_add]
  have hfac : ((d+1).factorial:ℝ) ≠ 0 := by positivity
  have hh := (div_eq_iff hfac).mp
    (PintzEndpointResearch.logarithmicTaylorPhase_coordinate d t hx)
  dsimp only
  rw [hh,Nat.factorial_succ]
  push_cast
  rcases neg_one_pow_eq_or ℝ (d+1) with hsign | hsign
  · rw [hsign]
    field_simp
  · rw [hsign]
    field_simp

#print axioms tailPositiveLogPhase_coordinate
#print axioms tailPositiveLogPhase_contDiffAt
#print axioms tailPositiveLogPhase_derivative

/-- The genuine same-height pairs inject into the existing native refined
derivative count, at every Taylor order. No multiplicity is discarded. -/
theorem tailMixedPairs_self_le_native_count (S : Finset ℕ)
    {k H H₀ a M : ℕ} {t : ℝ} (hH₀ : 0 < H₀) (hH : H₀ ≤ H)
    (hS : ∀ n∈S, a < n ∧ n-a ≤ M) :
    (tailMixedPairs S k H t t).card ≤
      (GafniTao.heathBrownPairCount M (k+2) H₀
        (tailPositiveLogPhase (k+2) t a)).card := by
  classical
  let F := tailMixedPairs S k H t t
  let f := fun p : ℕ × ℕ => (p.1-a,p.2-a)
  have hmem p (hp : p∈F) : p.1∈S ∧ p.2∈S ∧
      (tailLogCell (k+1) H t p.1 ∩ tailLogCell (k+1) H t p.2).Nonempty := by
    obtain ⟨hmem,hover⟩ := Finset.mem_filter.mp hp
    obtain ⟨hn,hm⟩ := Finset.mem_product.mp hmem
    exact ⟨hn,hm,hover⟩
  have hinj : Set.InjOn f (↑F:Set (ℕ×ℕ)) := by
    rintro ⟨n,m⟩ hp ⟨n',m'⟩ hp' he
    have hn := (hS n (hmem _ hp).1).1
    have hm := (hS m (hmem _ hp).2.1).1
    have hn' := (hS n' (hmem _ hp').1).1
    have hm' := (hS m' (hmem _ hp').2.1).1
    have he1 : n-a=n'-a := congrArg Prod.fst he
    have he2 : m-a=m'-a := congrArg Prod.snd he
    have hnn : n=n' := by omega
    have hmm : m=m' := by omega
    simp only [hnn,hmm]
  have hsub : F.image f ⊆ GafniTao.heathBrownPairCount M (k+2) H₀
      (tailPositiveLogPhase (k+2) t a) := by
    intro p hp
    obtain ⟨⟨n,m⟩,hnm,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hn,hm,hover⟩ := hmem _ hnm
    have hnb := hS n hn
    have hmb := hS m hm
    have hnp : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hmp : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hncast : (a:ℝ)+((n-a:ℕ):ℝ)=(n:ℝ) := by rw [Nat.cast_sub (by omega)]; ring
    have hmcast : (a:ℝ)+((m-a:ℕ):ℝ)=(m:ℝ) := by rw [Nat.cast_sub (by omega)]; ring
    apply GafniTao.mem_heathBrownPairCount.mpr
    refine ⟨by dsimp only [f]; omega,hnb.2,by dsimp only [f]; omega,hmb.2,?_⟩
    intro j hj
    have hjb := Finset.mem_Icc.mp hj
    have hjlo : 1 ≤ j := hjb.1
    let q : Fin (k+1) := ⟨j-1,by omega⟩
    have hq : (q:ℕ)+1=j := by dsimp only [q]; omega
    have hc := tailLogCell_mixed_coordinate hnp hmp hover q
    rw [hq] at hc
    have hncoord := PintzEndpointResearch.logarithmicTaylorPhase_coordinate (j-1) t hnp
    have hmcoord := PintzEndpointResearch.logarithmicTaylorPhase_coordinate (j-1) t hmp
    rw [Nat.sub_add_cancel hjlo] at hncoord hmcoord
    change GafniTao.heathBrownDistanceToInteger
      (GafniTao.heathBrownDerivativeCoordinate (tailPositiveLogPhase (k+2) t a) j ((n-a:ℕ):ℝ) -
        GafniTao.heathBrownDerivativeCoordinate (tailPositiveLogPhase (k+2) t a) j ((m-a:ℕ):ℝ)) ≤ _
    rw [tailPositiveLogPhase_coordinate,tailPositiveLogPhase_coordinate,hncast,hmcast]
    unfold GafniTao.heathBrownDerivativeCoordinate
    rw [hncoord,hmcoord,←mul_sub]
    have hsign : ∀ (v : ℕ) (z : ℝ), GafniTao.heathBrownDistanceToInteger ((-1:ℝ)^v*z)=
        GafniTao.heathBrownDistanceToInteger z := by
      intro v z
      rcases neg_one_pow_eq_or ℝ v with hs | hs
      · rw [hs,one_mul]
      · rw [hs,neg_one_mul,GafniTao.heathBrownDistanceToInteger_neg]
    rw [hsign]
    rw [show (-1:ℝ)^j*t/(2*Real.pi*j*(n:ℝ)^j)-(-1:ℝ)^j*t/(2*Real.pi*j*(m:ℝ)^j)=
      (-1:ℝ)^j*((t/(n:ℝ)^j-t/(m:ℝ)^j)/(2*Real.pi*j)) by ring,hsign]
    apply hc.trans
    have hHpos : 0 < (H₀:ℝ) := by exact_mod_cast hH₀
    have hHcast : (H₀:ℝ) ≤ H := by exact_mod_cast hH
    have hh := one_div_le_one_div_of_le (pow_pos hHpos j) (pow_le_pow_left₀ hHpos.le hHcast j)
    simpa only [one_div,div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)
  rw [←Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub

#print axioms tailMixedPairs_self_le_native_count

def tailDerivativeLower (k : ℕ) : ℝ :=
  ((k+1).factorial:ℝ)/(2*Real.pi*3^(k+2))

def tailDerivativeSpread (k : ℕ) : ℝ :=
  12^(k+2)+1/tailDerivativeLower k

theorem tailDerivativeLower_pos (k : ℕ) : 0 < tailDerivativeLower k := by
  unfold tailDerivativeLower
  positivity

theorem tailDerivativeSpread_pos (k : ℕ) : 0 < tailDerivativeSpread k := by
  have h := tailDerivativeLower_pos k
  unfold tailDerivativeSpread
  positivity

theorem tailDerivativeSpread_mul_lower (k : ℕ) :
    tailDerivativeSpread k*tailDerivativeLower k =
      ((k+1).factorial:ℝ)/(2*Real.pi)*4^(k+2)+1 := by
  have h := tailDerivativeLower_pos k
  unfold tailDerivativeSpread
  rw [add_mul,one_div_mul_cancel h.ne']
  congr 1
  unfold tailDerivativeLower
  rw [show (12:ℝ)=(3:ℝ)*4 by norm_num,mul_pow]
  field_simp

theorem tailPositiveLogPhase_derivative_bounds {k : ℕ} {N t a x : ℝ}
    (hN : 0 < N) (ht : 0 < t) (hxlo : N/4 ≤ a+x) (hxhi : a+x ≤ 3*N) :
    tailDerivativeLower k*t/N^(k+2) ≤
        iteratedDeriv (k+2) (tailPositiveLogPhase (k+2) t a) x ∧
      iteratedDeriv (k+2) (tailPositiveLogPhase (k+2) t a) x ≤
        tailDerivativeSpread k*(tailDerivativeLower k*t/N^(k+2)) := by
  have hx : 0 < a+x := lt_of_lt_of_le (by positivity) hxlo
  rw [show k+2=(k+1)+1 by omega,tailPositiveLogPhase_derivative (k+1) t a hx]
  simp only [Nat.add_assoc]
  let D : ℝ := ((k+1).factorial:ℝ)/(2*Real.pi)
  have hD : 0 < D := by dsimp only [D]; positivity
  have he : ((k+1).factorial:ℝ)*t/(2*Real.pi*(a+x)^(k+2))=D*t/(a+x)^(k+2) := by
    dsimp only [D]
    field_simp
  rw [he]
  constructor
  · calc
      _ = D*t/(3*N)^(k+2) := by dsimp only [D,tailDerivativeLower]; rw [mul_pow]; ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ D*t/(N/4)^(k+2) := by gcongr
      _ = (D*4^(k+2))*t/N^(k+2) := by rw [div_pow]; field_simp
      _ ≤ (D*4^(k+2)+1)*t/N^(k+2) := by gcongr; linarith
      _ = _ := by rw [←tailDerivativeSpread_mul_lower]; ring

#print axioms tailDerivativeLower_pos
#print axioms tailDerivativeSpread_pos
#print axioms tailDerivativeSpread_mul_lower
#print axioms tailPositiveLogPhase_derivative_bounds

/-- Existing native refined counting applied to the actual logarithmic
phase. The remaining conditions concern only the physical scale. -/
theorem tailMixedPairs_self_le_native_scale (S : Finset ℕ)
    {k H a M : ℕ} {N t : ℝ} (hk : 1 ≤ k)
    (hN : 0 < N) (ht : 0 < t) (hM : 1 ≤ M)
    (ha : N/4 ≤ (a:ℝ)) (haM : (a:ℝ)+M ≤ 3*N)
    (hS : ∀ n∈S, a < n ∧ n-a ≤ M)
    (hlambda : tailDerivativeLower k*t/N^(k+2) ≤ 1)
    (hsmall : tailDerivativeSpread k*(tailDerivativeLower k*t/N^(k+2)) ≤ 1/4)
    (hlarge : 8 ≤ GafniTao.heathBrownHChoice (k+2) (tailDerivativeSpread k)
      (tailDerivativeLower k*t/N^(k+2)))
    (hH : GafniTao.heathBrownHChoice (k+2) (tailDerivativeSpread k)
      (tailDerivativeLower k*t/N^(k+2)) ≤ H) :
    ((tailMixedPairs S k H t t).card:ℝ) ≤
      GafniTao.heathBrownRefinedCountConstant (k+2) (tailDerivativeSpread k)*
        (1+tailDerivativeSpread k*(tailDerivativeLower k*t/N^(k+2))*M)*
        ((M:ℝ)+(tailDerivativeLower k*t/N^(k+2))^(-(2/((k:ℝ)+2))))*
        (1+Real.log M) := by
  have hsmooth (j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
      ContDiffAt ℝ 1 (iteratedDeriv j (tailPositiveLogPhase (k+2) t a)) x := by
    apply contDiffAt_iteratedDeriv_finite
    exact tailPositiveLogPhase_contDiffAt (k+2) (1+j) t a (by linarith)
  have hc (j : ℕ) : ContinuousOn
      (GafniTao.heathBrownDerivativeCoordinate (tailPositiveLogPhase (k+2) t a) j)
      (Set.Icc 0 (M:ℝ)) := by
    intro x hx
    exact ((hsmooth j hx.1).continuousAt.div_const _).continuousWithinAt
  have hd (j : ℕ) : DifferentiableOn ℝ
      (GafniTao.heathBrownDerivativeCoordinate (tailPositiveLogPhase (k+2) t a) j)
      (Set.Ioo 0 (M:ℝ)) := by
    intro x hx
    exact (((hsmooth j hx.1.le).differentiableAt (by norm_num)).div_const _).differentiableWithinAt
  have hraw : ContinuousOn (iteratedDeriv (k+1) (tailPositiveLogPhase (k+2) t a))
      (Set.Icc 0 (M:ℝ)) := fun _ hx => (hsmooth (k+1) hx.1).continuousAt.continuousWithinAt
  have hrawd : DifferentiableOn ℝ (iteratedDeriv (k+1) (tailPositiveLogPhase (k+2) t a))
      (Set.Ioo 0 (M:ℝ)) := fun _ hx =>
    ((hsmooth (k+1) hx.1.le).differentiableAt (by norm_num)).differentiableWithinAt
  have hb : ∀ x∈Set.Ioo (0:ℝ) (M:ℝ),
      tailDerivativeLower k*t/N^(k+2) ≤ iteratedDeriv (k+2) (tailPositiveLogPhase (k+2) t a) x ∧
        iteratedDeriv (k+2) (tailPositiveLogPhase (k+2) t a) x ≤
          tailDerivativeSpread k*(tailDerivativeLower k*t/N^(k+2)) := by
    intro x hx
    exact tailPositiveLogPhase_derivative_bounds hN ht (by linarith [hx.1]) (by linarith [hx.2])
  have hlam : 0 < tailDerivativeLower k*t/N^(k+2) :=
    div_pos (mul_pos (tailDerivativeLower_pos k) ht) (pow_pos hN _)
  have hn := GafniTao.heathBrownPairCount_card_cast_le_source_scale (k:=k+2)
    (A:=tailDerivativeSpread k) (lambda:=tailDerivativeLower k*t/N^(k+2))
    (f:=tailPositiveLogPhase (k+2) t a)
    (by omega) hM (tailDerivativeSpread_pos k) hlam hlambda hsmall hlarge
    (hc k) (hd k) (hc (k+1)) (hd (k+1)) hraw hrawd hb
  have hcard := tailMixedPairs_self_le_native_count S (k:=k) (t:=t) (by omega) hH hS
  apply (Nat.cast_le.mpr hcard).trans
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hn

#print axioms tailMixedPairs_self_le_native_scale

set_option maxHeartbeats 1200000 in
/-- All native diagonal-count scale conditions follow uniformly from
N^k <= T <= N^(k+1), including the closed upper height boundary. -/
theorem tailSelf_native_parameters {k : ℕ} (hk : 4 ≤ k) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (H : ℕ) (N T t : ℝ), C ≤ N →
      N^k ≤ T → T ≤ N^(k+1) → T ≤ t → t ≤ 2*T →
      N/T^(1/((k:ℝ)+2)) ≤ (H:ℝ) →
      let l := tailDerivativeLower k
      let A := tailDerivativeSpread k
      let lam := l*t/N^(k+2)
      lam ≤ 1 ∧ A*lam ≤ 1/4 ∧ A*lam*(3*N) ≤ 6*A*l ∧
        lam^(-(2/((k:ℝ)+2))) ≤ N ∧
        8 ≤ GafniTao.heathBrownHChoice (k+2) A lam ∧
        GafniTao.heathBrownHChoice (k+2) A lam ≤ H := by
  let l := tailDerivativeLower k
  let A := tailDerivativeSpread k
  let m : ℝ := (k:ℝ)+2
  have hl : 0 < l := tailDerivativeLower_pos k
  have hA : 0 < A := tailDerivativeSpread_pos k
  have hm : 0 < m := by dsimp only [m]; positivity
  have hA1 : 1 ≤ A := by
    have hp : (1:ℝ) ≤ 12^(k+2) := one_le_pow₀ (by norm_num)
    have hi : 0 < 1/l := by positivity
    dsimp only [A,tailDerivativeSpread]
    linarith only [hp,hi]
  have hAl : 1 ≤ A*l := by
    rw [tailDerivativeSpread_mul_lower]
    have hp : 0 ≤ ((k+1).factorial:ℝ)/(2*Real.pi)*4^(k+2) := by positivity
    linarith only [hp]
  refine ⟨max 4 (max (1/l) (2*A*l*8^(k+2))),le_max_left _ _,?_⟩
  intro H N T t hCN hTlo hThi ht htT hH
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hCN
  have hN1 : 1 ≤ N := by linarith only [hN4]
  have hNp : 0 < N := by linarith only [hN4]
  have hlN : 1/l ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hCN)
  have hbig : 2*A*l*8^(k+2) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hCN)
  have hTp : 0 < T := (pow_pos hNp k).trans_le hTlo
  have htp : 0 < t := hTp.trans_le ht
  let lam := l*t/N^(k+2)
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hmassN : A*lam*N ≤ 2*A*l := by
    have he : A*lam*N=(A*l)*t/N^(k+1) := by
      dsimp only [lam]
      rw [show k+2=(k+1)+1 by omega,pow_succ]
      field_simp
    rw [he]
    apply (div_le_iff₀ (pow_pos hNp _)).mpr
    have hh : t ≤ 2*N^(k+1) := htT.trans (mul_le_mul_of_nonneg_left hThi (by norm_num))
    have hh' := mul_le_mul_of_nonneg_left hh (mul_pos hA hl).le
    nlinarith only [hh']
  have hsmallPow : A*lam ≤ 1/8^(k+2) := by
    apply (le_div_iff₀ (by positivity : 0 < (8:ℝ)^(k+2))).mpr
    have hh := mul_le_mul_of_nonneg_left hbig (mul_pos hA hlam).le
    have hc := hmassN.trans' hh
    have hAlp : 0 < 2*A*l := by positivity
    nlinarith only [hc,hAlp]
  have hsmall : A*lam ≤ 1/4 := by
    have hp : (8:ℝ)^2 ≤ 8^(k+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    apply hsmallPow.trans
    apply (div_le_div_iff₀ (by positivity : 0 < (8:ℝ)^(k+2)) (by norm_num)).mpr
    norm_num at hp ⊢
    linarith only [hp]
  have hlam1 : lam ≤ 1 := by
    have hh : lam ≤ A*lam := le_mul_of_one_le_left hlam.le hA1
    linarith only [hh,hsmall]
  have hmass : A*lam*(3*N) ≤ 6*A*l := by nlinarith only [hmassN]
  have hlower : N^(-(3:ℝ)) ≤ lam := by
    have hlN' : 1 ≤ l*N := by have hh := (div_le_iff₀ hl).mp hlN; nlinarith only [hh]
    have htlower : N^k ≤ t := hTlo.trans ht
    have he : N^(-(3:ℝ))=1/N^3 := by rw [Real.rpow_neg hNp.le,Real.rpow_ofNat,one_div]
    rw [he]
    dsimp only [lam]
    apply (div_le_div_iff₀ (pow_pos hNp 3) (pow_pos hNp (k+2))).mpr
    have hh := mul_le_mul_of_nonneg_right hlN' (pow_nonneg hNp.le (k+2))
    have ht' := mul_le_mul_of_nonneg_left htlower (by positivity : 0 ≤ l*N^3)
    rw [one_mul] at hh
    have he' : l*N*N^(k+2)=l*N^3*N^k := by rw [pow_add]; ring
    rw [he'] at hh
    nlinarith only [hh,ht']
  have hinv : lam^(-(2/m)) ≤ N := by
    calc
      _ ≤ (N^(-(3:ℝ)))^(-(2/m)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hlower (neg_nonpos.mpr (by positivity))
      _ = N^(6/m) := by rw [←Real.rpow_mul hNp.le]; congr 1; ring
      _ ≤ N := by
        have hm6 : 6 ≤ m := by dsimp only [m]; exact_mod_cast (by omega : 6 ≤ k+2)
        have he : 6/m ≤ 1 := (div_le_iff₀ hm).mpr (by linarith only [hm6])
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 he
  have hlarge : 8 ≤ GafniTao.heathBrownHChoice (k+2) A lam := by
    unfold GafniTao.heathBrownHChoice
    apply Nat.le_floor
    norm_num only [Nat.cast_ofNat]
    have he : (1/(8:ℝ)^(k+2))^(-(1/((k+2:ℕ):ℝ)))=8 := by
      rw [show 1/(8:ℝ)^(k+2)=(8:ℝ)^(-((k+2:ℕ):ℝ)) by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 8),Real.rpow_natCast,one_div],
        ←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 8)]
      rw [show -((k+2:ℕ):ℝ)*(-(1/((k+2:ℕ):ℝ)))=1 by field_simp,Real.rpow_one]
    rw [←he]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hsmallPow (neg_nonpos.mpr (by positivity))
  have hchosen : (GafniTao.heathBrownHChoice (k+2) A lam:ℝ) ≤ N/T^(1/m) := by
    have hb : T/N^(k+2) ≤ A*lam := by
      dsimp only [lam]
      rw [←mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (pow_nonneg hNp.le _)
      have hh := mul_le_mul_of_nonneg_right hAl htp.le
      nlinarith only [ht,hh]
    calc
      _ ≤ (A*lam)^(-(1/((k+2:ℕ):ℝ))) :=
        GafniTao.heathBrownHChoice_cast_le_rpow hA hlam
      _ ≤ (T/N^(k+2))^(-(1/((k+2:ℕ):ℝ))) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hb (neg_nonpos.mpr (by positivity))
      _ = _ := by
        rw [Real.div_rpow hTp.le (pow_nonneg hNp.le _),←Real.rpow_natCast,
          ←Real.rpow_mul hNp.le]
        rw [show ((k+2:ℕ):ℝ)*(-(1/((k+2:ℕ):ℝ)))=(-1:ℝ) by field_simp,
          Real.rpow_neg_one,div_inv_eq_mul,Real.rpow_neg hTp.le]
        dsimp only [m]
        push_cast
        ring
  exact ⟨hlam1,hsmall,hmass,hinv,hlarge,Nat.cast_le.mp (hchosen.trans hH)⟩

#print axioms tailSelf_native_parameters

set_option maxHeartbeats 1200000 in
/-- The actual same-height tail cells have essentially linear overlap
count at every order, including T=N^(k+1). -/
theorem tailMixedPairs_card_self {k : ℕ} (hk : 4 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (H : ℕ) (N T t : ℝ), C ≤ N →
      N^k ≤ T → T ≤ N^(k+1) → N/T^(1/((k:ℝ)+2)) ≤ (H:ℝ) →
      T ≤ t → t ≤ 2*T → (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ((tailMixedPairs S k H t t).card:ℝ) ≤ N^(1+ε) := by
  let l := tailDerivativeLower k
  let A := tailDerivativeSpread k
  let K := GafniTao.heathBrownRefinedCountConstant (k+2) A
  let B := 12*K*(1+6*A*l)
  have hl : 0 < l := tailDerivativeLower_pos k
  have hA : 0 < A := tailDerivativeSpread_pos k
  have hK : 0 < K := GafniTao.heathBrownRefinedCountConstant_pos _ hA
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨C₀,hC₀,hparam⟩ := tailSelf_native_parameters hk
  have hev : ∀ᶠ N : ℝ in Filter.atTop, 2*B ≤ N^ε ∧ 2*B*Real.log N ≤ N^ε := by
    filter_upwards [eventually_const_log_pow_le_rpow (2*B) (by positivity) 0 hε,
      eventually_const_log_pow_le_rpow (2*B) (by positivity) 1 hε] with N h1 h2
    simpa only [pow_zero,mul_one,pow_one] using And.intro h1 h2
  obtain ⟨C₁,hC₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro S H N T t hCN hTlo hThi hH ht htT hS
  have hNC₀ : C₀ ≤ N := (le_max_left _ _).trans hCN
  have hN4 : 4 ≤ N := hC₀.trans hNC₀
  have hN1 : 1 ≤ N := by linarith only [hN4]
  have hNp : 0 < N := by linarith only [hN4]
  have htp : 0 < t := (pow_pos hNp _).trans_le (hTlo.trans ht)
  have hconst := hC₁ N ((le_max_right _ _).trans hCN)
  obtain ⟨hlam1,hsmall,hmass,hinv,hlarge,hchosen⟩ :=
    hparam H N T t hNC₀ hTlo hThi ht htT hH
  let a : ℕ := ⌊N/2⌋₊
  let M : ℕ := ⌈2*N⌉₊
  have haHi : (a:ℝ) ≤ N/2 := Nat.floor_le (by positivity)
  have haLo : N/2 < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have hMLo : 2*N ≤ (M:ℝ) := Nat.le_ceil _
  have hMHi : (M:ℝ) < 2*N+1 := Nat.ceil_lt_add_one (by positivity)
  have hM : 1 ≤ M := by exact_mod_cast (show (1:ℝ) ≤ M by linarith only [hN4,hMLo])
  have hM3 : (M:ℝ) ≤ 3*N := by linarith only [hN4,hMHi]
  have hsupp : ∀ n∈S, a < n ∧ n-a ≤ M := by
    intro n hn
    have hnb := hS n hn
    have han : a < n := by exact_mod_cast (show (a:ℝ) < n by linarith only [haHi,hnb.1,hNp])
    have hnM : n ≤ M := by exact_mod_cast hnb.2.trans hMLo
    exact ⟨han,(Nat.sub_le n a).trans hnM⟩
  have hcount := tailMixedPairs_self_le_native_scale S (by omega : 1 ≤ k) hNp htp hM
    (by linarith only [haLo,hN4]) (by linarith only [haHi,hMHi,hN4]) hsupp
    hlam1 hsmall hlarge hchosen
  have hlam : 0 < l*t/N^(k+2) := by positivity
  have hmassM : A*(l*t/N^(k+2))*(M:ℝ) ≤ 6*A*l :=
    (mul_le_mul_of_nonneg_left hM3 (mul_pos hA hlam).le).trans hmass
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogM : 1+Real.log (M:ℝ) ≤ 3+Real.log N := by
    have hMp : 0 < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hh := Real.log_le_log hMp hM3
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hNp.ne'] at hh
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith only [hh,h3]
  have hsum : B*(1+Real.log N) ≤ N^ε := by nlinarith only [hconst.1,hconst.2]
  calc
    _ ≤ K*(1+A*(l*t/N^(k+2))*M)*
        ((M:ℝ)+(l*t/N^(k+2))^(-(2/((k:ℝ)+2))))*(1+Real.log M) := hcount
    _ ≤ K*(1+6*A*l)*(4*N)*(3+Real.log N) := by
      gcongr
      linarith only [hmassM,hM3,hinv,hlogM]
    _ ≤ N*(B*(1+Real.log N)) := by
      dsimp only [B]
      have hh : 0 ≤ K*(1+6*A*l)*N*Real.log N := by positivity
      nlinarith only [hh]
    _ ≤ N*N^ε := mul_le_mul_of_nonneg_left hsum hNp.le
    _ = N^(1+ε) := by rw [Real.rpow_add hNp,Real.rpow_one]

#print axioms tailMixedPairs_card_self

open MeasureTheory
open scoped ENNReal

def tailNuAt (S : Finset ℕ) (k H : ℕ) (t : ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus (k+2)) : ℝ :=
  ∑ n∈S, GafniTao.heathBrownCellIndicator (k+2) H
    (PintzEndpointResearch.logarithmicTaylorPhase t) n α

def tailOverlapIndicator (k H : ℕ) (t u : ℝ) (p : ℕ×ℕ) :
    GafniTao.HeathBrownCoefficientTorus (k+2) → ℝ :=
  (tailLogCell (k+1) H t p.1 ∩ tailLogCell (k+1) H u p.2).indicator (fun _ => 1)

def tailCellVolume (k H : ℕ) : ℝ :=
  2^(k+1)/(H:ℝ)^(GafniTao.heathBrownCriticalMoment (k+2))

theorem integrable_tailOverlapIndicator (k H : ℕ) (t u : ℝ) (p : ℕ×ℕ) :
    Integrable (tailOverlapIndicator k H t u p) (GafniTao.heathBrownCoefficientMeasure (k+2)) := by
  letI : IsFiniteMeasure (GafniTao.heathBrownCoefficientMeasure (k+2)) := by
    unfold GafniTao.heathBrownCoefficientMeasure
    infer_instance
  exact (integrable_const (1:ℝ)).indicator
    ((GafniTao.measurableSet_heathBrownCoefficientCell (k+2) _ _ _).inter
      (GafniTao.measurableSet_heathBrownCoefficientCell (k+2) _ _ _))

theorem tailNuAt_mul (S : Finset ℕ) (k H : ℕ) (t u : ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus (k+2)) :
    tailNuAt S k H t α*tailNuAt S k H u α =
      ∑ p∈S.product S, tailOverlapIndicator k H t u p α := by
  classical
  unfold tailNuAt
  rw [Finset.sum_mul_sum,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ha : α∈tailLogCell (k+1) H t n
  <;> by_cases hb : α∈tailLogCell (k+1) H u m
  <;> simp only [tailLogCell] at ha hb
  <;> simp [GafniTao.heathBrownCellIndicator,tailOverlapIndicator,tailLogCell,ha,hb]

theorem integrable_tailNuAt_mul (S : Finset ℕ) (k H : ℕ) (t u : ℝ) :
    Integrable (fun α => tailNuAt S k H t α*tailNuAt S k H u α)
      (GafniTao.heathBrownCoefficientMeasure (k+2)) := by
  have hh := integrable_finsetSum (S.product S)
    (fun p _ => integrable_tailOverlapIndicator k H t u p)
  apply hh.congr
  filter_upwards [] with α
  exact (tailNuAt_mul S k H t u α).symm

theorem tailLogCell_measureReal {k H : ℕ} (hH : 2 ≤ H) (t : ℝ) (n : ℕ) :
    (GafniTao.heathBrownCoefficientMeasure (k+2)).real (tailLogCell (k+1) H t n)=
      tailCellVolume k H := by
  unfold GafniTao.heathBrownCoefficientMeasure tailLogCell
  rw [GafniTao.measureReal_heathBrownCoefficientCell_exact hH]
  simp only [tailCellVolume,show k+2-1=k+1 by omega,div_eq_mul_inv]

theorem integral_tailNuAt_mul_le (S : Finset ℕ) {k H : ℕ} (hH : 2 ≤ H) (t u : ℝ) :
    (∫ α, tailNuAt S k H t α*tailNuAt S k H u α
      ∂(GafniTao.heathBrownCoefficientMeasure (k+2))) ≤
      ((tailMixedPairs S k H t u).card:ℝ)*tailCellVolume k H := by
  classical
  letI : IsFiniteMeasure (GafniTao.heathBrownCoefficientMeasure (k+2)) := by
    unfold GafniTao.heathBrownCoefficientMeasure
    infer_instance
  let A := tailMixedPairs S k H t u
  let μ := GafniTao.heathBrownCoefficientMeasure (k+2)
  let v := tailCellVolume k H
  have hint (p : ℕ×ℕ) : (∫ α, tailOverlapIndicator k H t u p α ∂μ) =
      μ.real (tailLogCell (k+1) H t p.1 ∩ tailLogCell (k+1) H u p.2) :=
    integral_indicator_one
      ((GafniTao.measurableSet_heathBrownCoefficientCell (k+2) _ _ _).inter
        (GafniTao.measurableSet_heathBrownCoefficientCell (k+2) _ _ _))
  have hterm (p : ℕ×ℕ) (hp : p∈S.product S) :
      (∫ α, tailOverlapIndicator k H t u p α ∂μ) ≤ if p∈A then v else 0 := by
    rw [hint]
    by_cases hover : (tailLogCell (k+1) H t p.1 ∩ tailLogCell (k+1) H u p.2).Nonempty
    · have hpA : p∈A := Finset.mem_filter.mpr ⟨hp,hover⟩
      rw [if_pos hpA]
      exact (measureReal_mono Set.inter_subset_left).trans_eq (tailLogCell_measureReal hH t p.1)
    · have hpA : p∉A := fun hh => hover (Finset.mem_filter.mp hh).2
      rw [if_neg hpA,Set.not_nonempty_iff_eq_empty.mp hover]
      simp
  have hAS : A ⊆ S.product S := fun _ hp => (Finset.mem_filter.mp hp).1
  simp_rw [tailNuAt_mul]
  rw [integral_finsetSum _ (fun p _ => integrable_tailOverlapIndicator k H t u p)]
  calc
    _ ≤ ∑ p∈S.product S, (if p∈A then v else 0) := Finset.sum_le_sum hterm
    _ = (A.card:ℝ)*v := by
      rw [←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hAS,
        Finset.sum_const,nsmul_eq_mul]

theorem tailNuAt_nonneg (S : Finset ℕ) (k H : ℕ) (t : ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus (k+2)) : 0 ≤ tailNuAt S k H t α :=
  Finset.sum_nonneg (fun n _ => GafniTao.heathBrownCellIndicator_nonneg (k+2) H n _ α)

theorem integrable_tailNuAt (S : Finset ℕ) (k H : ℕ) (t : ℝ) :
    Integrable (tailNuAt S k H t) (GafniTao.heathBrownCoefficientMeasure (k+2)) :=
  integrable_finsetSum _ (fun n _ => GafniTao.integrable_heathBrownCellIndicator (k+2) H n _)

theorem integral_tailNuAt (S : Finset ℕ) {k H : ℕ} (hH : 2 ≤ H) (t : ℝ) :
    (∫ α, tailNuAt S k H t α ∂(GafniTao.heathBrownCoefficientMeasure (k+2))) =
      (S.card:ℝ)*tailCellVolume k H := by
  unfold tailNuAt
  rw [integral_finsetSum _ (fun n _ => GafniTao.integrable_heathBrownCellIndicator (k+2) H n _)]
  simp_rw [GafniTao.integral_heathBrownCellIndicator]
  change (∑ n∈S, (GafniTao.heathBrownCoefficientMeasure (k+2)).real (tailLogCell (k+1) H t n)) = _
  simp_rw [tailLogCell_measureReal hH t]
  rw [Finset.sum_const,nsmul_eq_mul]

#print axioms integrable_tailOverlapIndicator
#print axioms tailNuAt_mul
#print axioms integrable_tailNuAt_mul
#print axioms tailLogCell_measureReal
#print axioms integral_tailNuAt_mul_le
#print axioms tailNuAt_nonneg
#print axioms integrable_tailNuAt
#print axioms integral_tailNuAt

/-- The near/far integral bound for the actual coefficient-cell
multiplicities, using the proved native diagonal and far counts. -/
theorem integral_tailNuAt_mul_uniform {k : ℕ} (hk : 4 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (N T t u : ℝ), C ≤ N →
      N^k ≤ T → T ≤ N^(k+1) → 2 ≤ Nat.ceil (N/T^(1/((k:ℝ)+2))) →
      T ≤ t → t ≤ 2*T → T ≤ u → u ≤ 2*T →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
      let L := N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2)))
      (∫ α, tailNuAt S k H t α*tailNuAt S k H u α
        ∂(GafniTao.heathBrownCoefficientMeasure (k+2))) ≤
      ((if |t-u| ≤ L then N^(1+ε) else 0)+N^((99:ℝ)/100))*tailCellVolume k H := by
  classical
  obtain ⟨C₀,hC₀,hself⟩ := tailMixedPairs_card_self hk hε
  obtain ⟨C₁,_,hfar⟩ := tailMixedPairs_card_far hk
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro S N T t u hNC hTlo hThi hH ht htT hu huT hS
  have hNp : 0 < N := by linarith [(le_max_left C₀ C₁).trans hNC]
  have hTp : 0 < T := (pow_pos hNp k).trans_le hTlo
  let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
  let L := N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2)))
  let μ := GafniTao.heathBrownCoefficientMeasure (k+2)
  let v := tailCellVolume k H
  have hv : 0 ≤ v := by dsimp only [v,tailCellVolume]; positivity
  have hHlo : N/T^(1/((k:ℝ)+2)) ≤ (H:ℝ) := Nat.le_ceil _
  change (∫ α, tailNuAt S k H t α*tailNuAt S k H u α ∂μ) ≤
    ((if |t-u| ≤ L then N^(1+ε) else 0)+N^((99:ℝ)/100))*v
  by_cases hnear : |t-u| ≤ L
  · rw [if_pos hnear]
    have hst : (∫ α, tailNuAt S k H t α*tailNuAt S k H t α ∂μ) ≤ N^(1+ε)*v :=
      (integral_tailNuAt_mul_le S hH t t).trans
        (mul_le_mul_of_nonneg_right
          (hself S H N T t ((le_max_left _ _).trans hNC) hTlo hThi hHlo ht htT hS) hv)
    have hsu : (∫ α, tailNuAt S k H u α*tailNuAt S k H u α ∂μ) ≤ N^(1+ε)*v :=
      (integral_tailNuAt_mul_le S hH u u).trans
        (mul_le_mul_of_nonneg_right
          (hself S H N T u ((le_max_left _ _).trans hNC) hTlo hThi hHlo hu huT hS) hv)
    have hh := integral_mono (integrable_tailNuAt_mul S k H t u)
      (((integrable_tailNuAt_mul S k H t t).add (integrable_tailNuAt_mul S k H u u)).div_const 2)
      (fun α => show tailNuAt S k H t α*tailNuAt S k H u α ≤
        (tailNuAt S k H t α*tailNuAt S k H t α+tailNuAt S k H u α*tailNuAt S k H u α)/2
        by nlinarith only [sq_nonneg (tailNuAt S k H t α-tailNuAt S k H u α)])
    simp only [Pi.add_apply] at hh
    rw [integral_div,integral_add (integrable_tailNuAt_mul S k H t t)
      (integrable_tailNuAt_mul S k H u u)] at hh
    have hp : 0 ≤ N^((99:ℝ)/100)*v := by positivity
    change (∫ α, tailNuAt S k H t α*tailNuAt S k H u α ∂μ) ≤ _ at hh
    nlinarith only [hh,hst,hsu,hp]
  · rw [if_neg hnear,zero_add]
    have hgap : L < |t-u| := lt_of_not_ge hnear
    rcases le_total t u with htu | hut
    · have hfar' : L ≤ u-t := by
        rw [abs_of_nonpos (sub_nonpos.mpr htu)] at hgap
        linarith only [hgap]
      exact (integral_tailNuAt_mul_le S hH t u).trans
        (mul_le_mul_of_nonneg_right
          (hfar S N T t u ((le_max_right _ _).trans hNC) hTp hThi ht htT huT hfar' hS) hv)
    · have hfar' : L ≤ t-u := by
        rw [abs_of_nonneg (sub_nonneg.mpr hut)] at hgap
        exact hgap.le
      simp_rw [mul_comm (tailNuAt S k H t _) (tailNuAt S k H u _)]
      exact (integral_tailNuAt_mul_le S hH u t).trans
        (mul_le_mul_of_nonneg_right
          (hfar S N T u t ((le_max_right _ _).trans hNC) hTp hThi hu huT htT hfar' hS) hv)

#print axioms integral_tailNuAt_mul_uniform

def tailDifferenceNu (S : Finset ℕ) (k H : ℕ) (E : Finset (ℝ×ℝ))
    (α : GafniTao.HeathBrownCoefficientTorus (k+2)) : ℝ :=
  ∑ p∈E, tailNuAt S k H (p.2-p.1) α

theorem tailDifferenceNu_sq (S : Finset ℕ) (k H : ℕ) (E : Finset (ℝ×ℝ))
    (α : GafniTao.HeathBrownCoefficientTorus (k+2)) :
    (tailDifferenceNu S k H E α)^2 =
      ∑ p∈E, ∑ q∈E, tailNuAt S k H (p.2-p.1) α*tailNuAt S k H (q.2-q.1) α := by
  unfold tailDifferenceNu
  rw [pow_two,Finset.sum_mul_sum]

theorem integrable_tailDifferenceNu_sq (S : Finset ℕ) (k H : ℕ) (E : Finset (ℝ×ℝ)) :
    Integrable (fun α => (tailDifferenceNu S k H E α)^2)
      (GafniTao.heathBrownCoefficientMeasure (k+2)) := by
  have hh := integrable_finsetSum E (fun p _ => integrable_finsetSum E
    (fun q _ => integrable_tailNuAt_mul S k H (p.2-p.1) (q.2-q.1)))
  apply hh.congr
  filter_upwards [] with α
  exact (tailDifferenceNu_sq S k H E α).symm

/-- Actual ordered ordinate-pair multiplicities are retained in this
second moment. Local occupancy controls the near term; the proved
far-cell theorem supplies the power saving on the quartic term. -/
theorem integral_tailDifferenceNu_sq_uniform {k : ℕ} (hk : 4 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (N T ρ : ℝ), C ≤ N →
      N^k ≤ T → T ≤ N^(k+1) → 2 ≤ Nat.ceil (N/T^(1/((k:ℝ)+2))) →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ∀ (W : Finset ℝ) (E : Finset (ℝ×ℝ)), E ⊆ W.product W →
      (∀ x : ℝ, ((W.filter (fun y =>
        |x-y| ≤ N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))))).card:ℝ) ≤ N^ρ) →
      (∀ p∈E, T ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*T) →
      let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
      (∫ α, (tailDifferenceNu S k H E α)^2 ∂(GafniTao.heathBrownCoefficientMeasure (k+2))) ≤
        ((W.card:ℝ)^3*N^(1+ρ+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*tailCellVolume k H := by
  classical
  obtain ⟨C,hC,hpair⟩ := integral_tailNuAt_mul_uniform hk hε
  refine ⟨C,hC,?_⟩
  intro S N T ρ hNC hTlo hThi hH hS W E hE hlocal hheight
  have hNp : 0 < N := by linarith only [hC,hNC]
  let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
  let L := N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2)))
  let v := tailCellVolume k H
  have hv : 0 ≤ v := by dsimp only [v,tailCellVolume]; positivity
  have hEc : (E.card:ℝ) ≤ (W.card:ℝ)^2 := by
    have hh := Finset.card_le_card hE
    rw [Finset.product_eq_sprod,Finset.card_product] at hh
    exact_mod_cast (show E.card ≤ W.card^2 by simpa only [pow_two] using hh)
  have hrow (p : ℝ×ℝ) (hp : p∈E) :
      (∑ q∈E, (∫ α, tailNuAt S k H (p.2-p.1) α*tailNuAt S k H (q.2-q.1) α
        ∂(GafniTao.heathBrownCoefficientMeasure (k+2)))) ≤
        ((W.card:ℝ)*N^(1+ρ+ε)+(E.card:ℝ)*N^((99:ℝ)/100))*v := by
    have hnear := PintzFirstEndpointResearch.difference_near_card_le_local W E hE hlocal (p.2-p.1)
    calc
      _ ≤ ∑ q∈E, ((if |(p.2-p.1)-(q.2-q.1)| ≤ L
          then N^(1+ε) else 0)+N^((99:ℝ)/100))*v := by
        apply Finset.sum_le_sum
        intro q hq
        exact hpair S N T _ _ hNC hTlo hThi hH
          (hheight p hp).1 (hheight p hp).2 (hheight q hq).1 (hheight q hq).2 hS
      _ = (((E.filter (fun q => |(p.2-p.1)-(q.2-q.1)| ≤ L)).card:ℝ)*
          N^(1+ε)+(E.card:ℝ)*N^((99:ℝ)/100))*v := by
        rw [←Finset.sum_mul,Finset.sum_add_distrib,←Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (((W.card:ℝ)*N^ρ)*N^(1+ε)+(E.card:ℝ)*N^((99:ℝ)/100))*v := by gcongr
      _ = _ := by
        have he : N^ρ*N^(1+ε)=N^(1+ρ+ε) := by rw [←Real.rpow_add hNp]; congr 1; ring
        simp only [mul_assoc,he]
  change (∫ α, (tailDifferenceNu S k H E α)^2
    ∂(GafniTao.heathBrownCoefficientMeasure (k+2))) ≤
    ((W.card:ℝ)^3*N^(1+ρ+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*v
  simp_rw [tailDifferenceNu_sq]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum E
    (fun q _ => integrable_tailNuAt_mul S k H (p.2-p.1) (q.2-q.1)))]
  have hrowint (p : ℝ×ℝ) :
      (∫ α, ∑ q∈E, tailNuAt S k H (p.2-p.1) α*tailNuAt S k H (q.2-q.1) α
        ∂(GafniTao.heathBrownCoefficientMeasure (k+2))) =
      ∑ q∈E, (∫ α, tailNuAt S k H (p.2-p.1) α*tailNuAt S k H (q.2-q.1) α
        ∂(GafniTao.heathBrownCoefficientMeasure (k+2))) :=
    integral_finsetSum E (fun q _ => integrable_tailNuAt_mul S k H (p.2-p.1) (q.2-q.1))
  simp_rw [hrowint]
  calc
    _ ≤ ∑ _p∈E, ((W.card:ℝ)*N^(1+ρ+ε)+(E.card:ℝ)*N^((99:ℝ)/100))*v := Finset.sum_le_sum hrow
    _ = ((E.card:ℝ)*(W.card:ℝ)*N^(1+ρ+ε)+(E.card:ℝ)^2*N^((99:ℝ)/100))*v := by
      rw [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ ((W.card:ℝ)^2*(W.card:ℝ)*N^(1+ρ+ε)+((W.card:ℝ)^2)^2*N^((99:ℝ)/100))*v := by gcongr
    _ = _ := by dsimp only [v]; ring

#print axioms tailDifferenceNu_sq
#print axioms integrable_tailDifferenceNu_sq
#print axioms integral_tailDifferenceNu_sq_uniform

/-- The required local occupancy is derived from the existing analytic
Heath--Brown pair on the original large-value pattern. -/
theorem tail_endpoint_local_occupancy {k : ℕ} (hk : 4 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/(100000*(((k:ℝ)+2)*((k:ℝ)+1))^2) ∧
      ∃ C : ℝ, 4 ≤ C ∧ ∀ P : LargeValuePattern, C ≤ P.N →
      P.N^(1-1/(2*((k:ℝ)+2)*((k:ℝ)+1))-δ) ≤ P.V →
      ∀ x : ℝ, ((P.ordinates.filter (fun y =>
        |x-y| ≤ P.N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))))).card:ℝ) ≤
        P.N^(101/(100*((k:ℝ)+2)*((k:ℝ)+1))) := by
  classical
  let p : ℝ := ((k:ℝ)+2)*((k:ℝ)+1)
  let σ : ℝ := 1-1/(2*((k:ℝ)+2)*((k:ℝ)+1))
  let a : ℝ := (k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))
  let η : ℝ := 1/(1000*p)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hbase : IsLargeValueBound σ ((k:ℝ)+2/((k:ℝ)+2)) (1/p) := by
    have hh := pintz_tail_endpoint_pair_largeValueBound (n:=k+2) (by omega)
    convert hh using 1 <;> dsimp only [σ,p] <;> push_cast <;> ring_nf
  have hbound : IsLargeValueBound σ a (1/p) := hbase.of_height_le (by
    have he : 0 < 1/(10000*((k:ℝ)+2)) := by positivity
    dsimp only [a]
    linarith only [he])
  obtain ⟨K,hK,δ₀,hδ₀,hcount⟩ := hbound η hη
  let δ : ℝ := min δ₀ (1/(100000*p^2))
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hev : ∀ᶠ N : ℝ in Filter.atTop, K ≤ N^(9*η) ∧ 2 ≤ N^δ₀ := by
    filter_upwards [eventually_const_log_pow_le_rpow K (by linarith only [hK]) 0
        (η:=9*η) (by positivity),eventually_const_log_pow_le_rpow 2 (by norm_num) 0 hδ₀]
      with N h1 h2
    simpa only [pow_zero,mul_one] using And.intro h1 h2
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp hev
  refine ⟨δ,hδ,min_le_right _ _,max 4 (max K C),le_max_left _ _,?_⟩
  intro P hPN hV x
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hPK : K ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans hPN)
  have hconst := hC P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  let L : ℝ := P.N^a
  have hL : 0 < L := by dsimp only [L]; positivity
  let Q : LargeValuePattern := { P with
    T := 2*L
    T_pos := by positivity
    V := P.N^(σ-δ)
    V_pos := by positivity
    intervalLeft := x-L
    intervalRight := x+L
    ordinates := P.ordinates.filter (fun y => |x-y| ≤ L)
    interval_length := by ring
    ordinates_in_interval := by
      intro y hy
      have hh := abs_le.mp (Finset.mem_filter.mp hy).2
      constructor <;> linarith only [hh.1,hh.2]
    ordinates_oneSeparated := fun y hy z hz hyz =>
      P.ordinates_oneSeparated y (Finset.mem_filter.mp hy).1 z (Finset.mem_filter.mp hz).1 hyz
    large := fun y hy => hV.trans (P.large y (Finset.mem_filter.mp hy).1) }
  have hTlo : Q.N^(a-δ₀) ≤ Q.T := by
    change P.N^(a-δ₀) ≤ 2*L
    have hh := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (show a-δ₀ ≤ a by linarith only [hδ₀])
    change P.N^(a-δ₀) ≤ L at hh
    linarith only [hh,hL]
  have hThi : Q.T ≤ Q.N^(a+δ₀) := by
    change 2*L ≤ P.N^(a+δ₀)
    calc
      _ ≤ P.N^δ₀*L := mul_le_mul_of_nonneg_right hconst.2 hL.le
      _ = _ := by dsimp only [L]; rw [←Real.rpow_add hNp]; congr 1; ring
  have hVlo : Q.N^(σ-δ₀) ≤ Q.V :=
    Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδle])
  have hVhi : Q.V ≤ Q.N^(σ+δ₀) :=
    Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδ,hδ₀])
  have hh := hcount Q hPK hTlo hThi hVlo hVhi
  change ((P.ordinates.filter (fun y => |x-y| ≤ L)).card:ℝ) ≤ K*P.N^(1/p+η) at hh
  calc
    _ ≤ K*P.N^(1/p+η) := hh
    _ ≤ P.N^(9*η)*P.N^(1/p+η) := by gcongr; exact hconst.1
    _ = _ := by
      rw [←Real.rpow_add hNp]
      congr 1
      dsimp only [η,p]
      field_simp
      ring

#print axioms tail_endpoint_local_occupancy

theorem tailDifferenceNu_nonneg (S : Finset ℕ) (k H : ℕ) (E : Finset (ℝ×ℝ))
    (α : GafniTao.HeathBrownCoefficientTorus (k+2)) : 0 ≤ tailDifferenceNu S k H E α :=
  Finset.sum_nonneg (fun p _ => tailNuAt_nonneg S k H (p.2-p.1) α)

theorem integrable_tailDifferenceNu (S : Finset ℕ) (k H : ℕ) (E : Finset (ℝ×ℝ)) :
    Integrable (tailDifferenceNu S k H E) (GafniTao.heathBrownCoefficientMeasure (k+2)) :=
  integrable_finsetSum E (fun p _ => integrable_tailNuAt S k H (p.2-p.1))

theorem measurable_tailDifferenceNu (S : Finset ℕ) (k H : ℕ) (E : Finset (ℝ×ℝ)) :
    Measurable (tailDifferenceNu S k H E) := by
  unfold tailDifferenceNu tailNuAt
  exact Finset.measurable_sum E (fun p _ => Finset.measurable_sum S
    (fun n _ => GafniTao.measurable_heathBrownCellIndicator (k+2) H n
      (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1))))

theorem integral_tailDifferenceNu (S : Finset ℕ) {k H : ℕ} (hH : 2 ≤ H) (E : Finset (ℝ×ℝ)) :
    (∫ α, tailDifferenceNu S k H E α ∂(GafniTao.heathBrownCoefficientMeasure (k+2))) =
      (E.card:ℝ)*(S.card:ℝ)*tailCellVolume k H := by
  unfold tailDifferenceNu
  rw [integral_finsetSum E (fun p _ => integrable_tailNuAt S k H (p.2-p.1))]
  simp_rw [integral_tailNuAt S hH]
  rw [Finset.sum_const,nsmul_eq_mul,mul_assoc]

#print axioms tailDifferenceNu_nonneg
#print axioms integrable_tailDifferenceNu
#print axioms measurable_tailDifferenceNu
#print axioms integral_tailDifferenceNu

def tailIntegratedWeyl (S : Finset ℕ) (k H : ℕ) (E : Finset (ℝ×ℝ)) (Q : ℕ) : ENNReal :=
  ∫⁻ α : GafniTao.HeathBrownCoefficientTorus (k+2),
    ENNReal.ofReal ‖GafniTao.heathBrownWeylSum (k+2) Q α‖*
      ENNReal.ofReal (tailDifferenceNu S k H E α) ∂(GafniTao.heathBrownCoefficientMeasure (k+2))

def tailJointMajorant (S : Finset ℕ) (k H : ℕ) (W : Finset ℝ) (E : Finset (ℝ×ℝ))
    (N ε ρ : ℝ) : ℝ :=
  let s := GafniTao.heathBrownCriticalMoment (k+2)
  (GafniTao.fordVinogradovMomentNat s (k+1) H : ℝ)^(1/(2*(s:ℝ)))*
    (((W.card:ℝ)^3*N^(1+ρ+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*tailCellVolume k H)^(1/(2*(s:ℝ)))*
    ((E.card:ℝ)*(S.card:ℝ)*tailCellVolume k H)^(1-1/(s:ℝ))

/-- Joint critical Holder estimate on the genuine ordered-difference
ensemble. The far correlation saving enters through its proved second
moment, rather than an independent pointwise kernel bound. -/
theorem tail_joint_weyl_mean {k : ℕ} (hk : 4 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (N T ρ : ℝ), C ≤ N →
      N^k ≤ T → T ≤ N^(k+1) → 2 ≤ Nat.ceil (N/T^(1/((k:ℝ)+2))) →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ∀ (W : Finset ℝ) (E : Finset (ℝ×ℝ)), E ⊆ W.product W →
      (∀ x : ℝ, ((W.filter (fun y =>
        |x-y| ≤ N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))))).card:ℝ) ≤ N^ρ) →
      (∀ p∈E, T ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*T) →
      let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
      ∀ Q : ℕ, Q ≤ H → tailIntegratedWeyl S k H E Q ≤
        ENNReal.ofReal (tailJointMajorant S k H W E N ε ρ) := by
  obtain ⟨C,hC,hsecond⟩ := integral_tailDifferenceNu_sq_uniform hk hε
  refine ⟨C,hC,?_⟩
  intro S N T ρ hNC hTlo hThi hH hS W E hE hlocal hheight
  dsimp only
  intro Q hQ
  have hNp : 0 < N := by linarith only [hC,hNC]
  let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
  let s := GafniTao.heathBrownCriticalMoment (k+2)
  have hspos : (0:ℝ) < s := GafniTao.heathBrownCriticalMoment_pos (by omega)
  have hs : 1 ≤ s := by exact_mod_cast hspos
  have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hlast : 0 ≤ 1-1/(s:ℝ) := by
    have hh : 1/(s:ℝ) ≤ 1 := (div_le_iff₀ hspos).mpr (by linarith only [hsR])
    linarith only [hh]
  let μ := GafniTao.heathBrownCoefficientMeasure (k+2)
  let v := tailCellVolume k H
  have hv : 0 ≤ v := by dsimp only [v,tailCellVolume]; positivity
  let A : GafniTao.HeathBrownCoefficientTorus (k+2) → ENNReal :=
    fun α => ENNReal.ofReal ‖GafniTao.heathBrownWeylSum (k+2) Q α‖
  let B : GafniTao.HeathBrownCoefficientTorus (k+2) → ENNReal :=
    fun α => ENNReal.ofReal (tailDifferenceNu S k H E α)
  have hA : AEMeasurable A μ :=
    (ENNReal.continuous_ofReal.comp (GafniTao.continuous_fordVinogradovWeylSum (k+1) Q).norm).aemeasurable
  have hB : AEMeasurable B μ := (integrable_tailDifferenceNu S k H E).aemeasurable.ennreal_ofReal
  have hholder := GafniTao.heathBrown_lintegral_mul_le_three_moments hA hB hs
  have hAI : (∫⁻ α, A α^(2*s) ∂μ) = (GafniTao.fordVinogradovMomentNat s (k+1) Q : ENNReal) :=
    GafniTao.ford_vinogradov_lintegral_mean_eq s (k+1) Q
  have hBI : (∫⁻ α, B α ∂μ) = ENNReal.ofReal ((E.card:ℝ)*(S.card:ℝ)*v) := by
    rw [←integral_tailDifferenceNu S hH E]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_tailDifferenceNu S k H E)
      (Filter.Eventually.of_forall (tailDifferenceNu_nonneg S k H E))).symm
  have hBII : (∫⁻ α, B α^2 ∂μ) ≤ ENNReal.ofReal
      (((W.card:ℝ)^3*N^(1+ρ+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*v) := by
    calc
      _ = ∫⁻ α, ENNReal.ofReal ((tailDifferenceNu S k H E α)^2) ∂μ := by
        apply lintegral_congr
        intro α
        exact (ENNReal.ofReal_pow (tailDifferenceNu_nonneg S k H E α) 2).symm
      _ = ENNReal.ofReal (∫ α, (tailDifferenceNu S k H E α)^2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_tailDifferenceNu_sq S k H E)
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hsecond S N T ρ hNC hTlo hThi hH hS W E hE hlocal hheight)
  have hmono : (GafniTao.fordVinogradovMomentNat s (k+1) Q : ENNReal) ≤
      (GafniTao.fordVinogradovMomentNat s (k+1) H : ENNReal) := by
    have hQH : Q ≤ H := by simpa only [H,Nat.cast_add,Nat.cast_ofNat] using hQ
    exact_mod_cast GafniTao.fordVinogradovMomentNat_mono s (k+1) hQH
  rw [hAI,hBI] at hholder
  have hmajor : ENNReal.ofReal (tailJointMajorant S k H W E N ε ρ) =
      (GafniTao.fordVinogradovMomentNat s (k+1) H : ENNReal)^(1/(2*(s:ℝ)))*
        ENNReal.ofReal (((W.card:ℝ)^3*N^(1+ρ+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*v)^(1/(2*(s:ℝ)))*
        ENNReal.ofReal ((E.card:ℝ)*(S.card:ℝ)*v)^(1-1/(s:ℝ)) := by
    unfold tailJointMajorant
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
    rw [←ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ←ENNReal.ofReal_rpow_of_nonneg (by dsimp only [tailCellVolume]; positivity) (by positivity),
      ←ENNReal.ofReal_rpow_of_nonneg (by dsimp only [tailCellVolume]; positivity) hlast,
      ENNReal.ofReal_natCast]
  apply hholder.trans
  rw [hmajor]
  gcongr

#print axioms tail_joint_weyl_mean

/-- Bounds for the literal adaptive integer block throughout the closed
physical height range. -/
theorem tail_adaptive_block_scales {k : ℕ} {N T : ℝ} (hk : 1 ≤ k)
    (hN : 2 ≤ N) (hbig : (2:ℝ)^(k+2) ≤ N) (hTlo : N^k ≤ T) (hThi : T ≤ N^(k+1)) :
    let X := T^(1/((k:ℝ)+2))
    let H := Nat.ceil (N/X)
    2 ≤ H ∧ N/X ≤ (H:ℝ) ∧ (H:ℝ) ≤ 2*N/X ∧ (H:ℝ) ≤ N := by
  let n : ℝ := (k:ℝ)+2
  let X := T^(1/n)
  let H := Nat.ceil (N/X)
  have hn : 0 < n := by dsimp only [n]; positivity
  have hNp : 0 < N := by linarith only [hN]
  have hN1 : 1 ≤ N := by linarith only [hN]
  have hTp : 0 < T := (pow_pos hNp _).trans_le hTlo
  have hX : 0 < X := Real.rpow_pos_of_pos hTp _
  have hroot : 2 ≤ N^(1/n) := by
    have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 2^(k+2)) hbig (by positivity : 0 ≤ 1/n)
    have he : ((2:ℝ)^(k+2))^(1/n)=2 := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [show ((k+2:ℕ):ℝ)*(1/n)=1 by dsimp only [n]; push_cast; field_simp,Real.rpow_one]
    rwa [he] at hh
  have hXlo : 2 ≤ X := by
    calc
      _ ≤ N^(1/n) := hroot
      _ ≤ N^((k:ℝ)/n) := Real.rpow_le_rpow_of_exponent_le hN1
        (div_le_div_of_nonneg_right (by exact_mod_cast hk) hn.le)
      _ = (N^k)^(1/n) := by rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]; congr 1; ring
      _ ≤ X := Real.rpow_le_rpow (pow_nonneg hNp.le _) hTlo (by positivity)
  have hXhi : X ≤ N^(((k:ℝ)+1)/n) := by
    have hh := Real.rpow_le_rpow hTp.le hThi (by positivity : 0 ≤ 1/n)
    apply hh.trans_eq
    rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
    congr 1
    push_cast
    ring
  have hYlo : 2 ≤ N/X := by
    apply hroot.trans
    apply (le_div_iff₀ hX).mpr
    calc
      _ ≤ N^(1/n)*N^(((k:ℝ)+1)/n) := mul_le_mul_of_nonneg_left hXhi (by positivity)
      _ = N := by
        rw [←Real.rpow_add hNp]
        rw [show 1/n+((k:ℝ)+1)/n=1 by dsimp only [n]; field_simp; ring,Real.rpow_one]
  have hceilLo : N/X ≤ (H:ℝ) := Nat.le_ceil _
  have hceilHi : (H:ℝ) < N/X+1 := Nat.ceil_lt_add_one (by positivity)
  have hYhi : N/X ≤ N/2 := div_le_div_of_nonneg_left hNp.le (by norm_num) hXlo
  change 2 ≤ H ∧ N/X ≤ (H:ℝ) ∧ (H:ℝ) ≤ 2*N/X ∧ (H:ℝ) ≤ N
  refine ⟨by exact_mod_cast hYlo.trans hceilLo,hceilLo,?_,?_⟩
  · rw [show 2*N/X=2*(N/X) by ring]
    linarith only [hceilHi,hYlo]
  · linarith only [hceilHi,hYhi,hN]

#print axioms tail_adaptive_block_scales

theorem tail_joint_cellwise_le (S : Finset ℕ) (E : Finset (ℝ×ℝ))
    {k H : ℕ} (hH : 2 ≤ H) {Q : ℕ} (hQ : 1 ≤ Q)
    (hQH : Q ≤ H)
    (α : GafniTao.HeathBrownCoefficientTorus (k+2)) :
    (∑ t ∈ E, ∑ n ∈ S,
      GafniTao.heathBrownCellIndicator (k+2) (H)
        (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n α *
      ‖GafniTao.heathBrownWeylSum (k+2) Q
        (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)‖) ≤
      ‖GafniTao.heathBrownWeylSum (k+2) Q α‖*tailDifferenceNu S k H E α+
      (2*Real.pi*((k:ℝ)+2)^2/(H : ℝ))*
        ∑ j ∈ Finset.Ico 1 Q,
          ‖GafniTao.heathBrownWeylSum (k+2) j α‖*tailDifferenceNu S k H E α := by
  classical
  let c : ℝ := 2*Real.pi*((k:ℝ)+2)^2/(H : ℝ)
  let F (j : ℕ) : ℝ := ‖GafniTao.heathBrownWeylSum (k+2) j α‖
  let I (t : ℝ×ℝ) (n : ℕ) : ℝ :=
    GafniTao.heathBrownCellIndicator (k+2) H (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n α
  have hpoint (t : ℝ×ℝ) (n : ℕ) :
      I t n*‖GafniTao.heathBrownWeylSum (k+2) Q
        (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)‖ ≤
        I t n*(F Q+c*∑ j ∈ Finset.Ico 1 Q, F j) := by
    by_cases hα : α ∈ GafniTao.heathBrownCoefficientCell (k+2) H (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n
    · have hi : I t n = 1 := by simp [I,GafniTao.heathBrownCellIndicator,hα]
      rw [hi,one_mul,one_mul]
      have hh := GafniTao.norm_heathBrown_centerWeyl_le hH hQ hQH hα
      have he : 2*Real.pi*(((k+2:ℕ):ℝ)^2/(H : ℝ)) = c := by
        dsimp only [c]
        push_cast
        ring
      simpa only [he,F] using hh
    · have hi : I t n = 0 := by simp [I,GafniTao.heathBrownCellIndicator,hα]
      simp only [hi,zero_mul,le_refl]
  calc
    _ ≤ ∑ t ∈ E, ∑ n ∈ S, I t n*(F Q+c*∑ j ∈ Finset.Ico 1 Q, F j) :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun n _ => hpoint t n))
    _ = (tailDifferenceNu S k H E α)*(F Q+c*∑ j ∈ Finset.Ico 1 Q, F j) := by
      simp_rw [← Finset.sum_mul]
      rfl
    _ = _ := by
      rw [mul_add]
      simp_rw [← Finset.sum_mul]
      dsimp only [c,F]
      ring

#print axioms tail_joint_cellwise_le

theorem tail_joint_center_integral (S : Finset ℕ) (E : Finset (ℝ×ℝ))
    {k H : ℕ} (hH : 2 ≤ H) {Q : ℕ} (hQ : 1 ≤ Q)
    (hQH : Q ≤ H) :
    ENNReal.ofReal (tailCellVolume k H)*
      (∑ t ∈ E, ∑ n ∈ S,
        ENNReal.ofReal ‖GafniTao.heathBrownWeylSum (k+2) Q
          (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)‖) ≤
      tailIntegratedWeyl S k H E Q+
        ENNReal.ofReal (2*Real.pi*((k:ℝ)+2)^2/(H : ℝ))*
          ∑ j ∈ Finset.Ico 1 Q, tailIntegratedWeyl S k H E j := by
  classical
  let μ := GafniTao.heathBrownCoefficientMeasure (k+2)
  let c : ℝ := 2*Real.pi*((k:ℝ)+2)^2/(H : ℝ)
  let v : ℝ := tailCellVolume k H
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  let F (j : ℕ) (α : GafniTao.HeathBrownCoefficientTorus (k+2)) : ENNReal :=
    ENNReal.ofReal ‖GafniTao.heathBrownWeylSum (k+2) j α‖*
      ENNReal.ofReal (tailDifferenceNu S k H E α)
  let I (t : ℝ×ℝ) (n : ℕ) (α : GafniTao.HeathBrownCoefficientTorus (k+2)) : ℝ :=
    GafniTao.heathBrownCellIndicator (k+2) H (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n α
  let K (t : ℝ×ℝ) (n : ℕ) : ℝ := ‖GafniTao.heathBrownWeylSum (k+2) Q
    (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)‖
  have hI (t : ℝ×ℝ) (n : ℕ) (α : GafniTao.HeathBrownCoefficientTorus (k+2)) : 0 ≤ I t n α :=
    GafniTao.heathBrownCellIndicator_nonneg (k+2) H n (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) α
  have hK (t : ℝ×ℝ) (n : ℕ) : 0 ≤ K t n := norm_nonneg _
  have hpoint (α : GafniTao.HeathBrownCoefficientTorus (k+2)) :
      (∑ t ∈ E, ∑ n ∈ S, ENNReal.ofReal (I t n α)*ENNReal.ofReal (K t n)) ≤
        F Q α+ENNReal.ofReal c*∑ j ∈ Finset.Ico 1 Q, F j α := by
    have hh := ENNReal.ofReal_le_ofReal (tail_joint_cellwise_le S E hH hQ hQH α)
    change ENNReal.ofReal (∑ t ∈ E, ∑ n ∈ S, I t n α*K t n) ≤ _ at hh
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => Finset.sum_nonneg
      (fun n _ => mul_nonneg (hI t n α) (hK t n)))] at hh
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (hI _ n α) (hK _ n)),
      ENNReal.ofReal_mul (hI _ _ α)] at hh
    have hprod (j : ℕ) : 0 ≤ ‖GafniTao.heathBrownWeylSum (k+2) j α‖*tailDifferenceNu S k H E α :=
      mul_nonneg (norm_nonneg _) (tailDifferenceNu_nonneg S k H E α)
    rw [ENNReal.ofReal_add (hprod Q) (mul_nonneg hc (Finset.sum_nonneg (fun j _ => hprod j))),
      ENNReal.ofReal_mul (norm_nonneg _),ENNReal.ofReal_mul hc,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => hprod j)] at hh
    simp_rw [ENNReal.ofReal_mul (norm_nonneg _)] at hh
    exact hh
  have hcell (t : ℝ×ℝ) (n : ℕ) : μ (GafniTao.heathBrownCoefficientCell (k+2) H (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n) =
      ENNReal.ofReal v := by
    have hh := GafniTao.measure_heathBrownCoefficientCell_exact (k := k+2) hH (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) (n : ℝ)
    simpa only [μ,v,tailCellVolume,GafniTao.heathBrownCoefficientMeasure,
      show k+2-1=k+1 by omega,div_eq_mul_inv] using hh
  have hmeas (t : ℝ×ℝ) (n : ℕ) : Measurable (fun α => ENNReal.ofReal (I t n α)*ENNReal.ofReal (K t n)) :=
    (GafniTao.measurable_heathBrownCellIndicator (k+2) H n (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1))).ennreal_ofReal.mul measurable_const
  have hleft : (∫⁻ α, ∑ t ∈ E, ∑ n ∈ S,
      ENNReal.ofReal (I t n α)*ENNReal.ofReal (K t n) ∂μ) =
      ENNReal.ofReal v*(∑ t ∈ E, ∑ n ∈ S, ENNReal.ofReal (K t n)) := by
    rw [lintegral_finsetSum E (fun t _ => Finset.measurable_sum S (fun n _ => hmeas t n))]
    simp_rw [lintegral_finsetSum S (fun n _ => hmeas _ n)]
    simp_rw [I,μ,GafniTao.lintegral_heathBrownCellIndicator_mul_const]
    change (∑ t ∈ E, ∑ n ∈ S, μ (GafniTao.heathBrownCoefficientCell (k+2) H
      (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)*ENNReal.ofReal (K t n)) = _
    simp_rw [hcell,← Finset.mul_sum]
  have hF (j : ℕ) : Measurable (F j) :=
    (ENNReal.continuous_ofReal.comp (GafniTao.continuous_fordVinogradovWeylSum (k+1) j).norm).measurable.mul
      (measurable_tailDifferenceNu S k H E).ennreal_ofReal
  have hh := lintegral_mono (μ := μ) hpoint
  rw [hleft,lintegral_add_left (hF Q),lintegral_const_mul _
    (Finset.measurable_sum (Finset.Ico 1 Q) (fun j _ => hF j)),
    lintegral_finsetSum (Finset.Ico 1 Q) (fun j _ => hF j)] at hh
  exact hh

#print axioms tail_joint_center_integral

theorem tail_joint_center_uniform {k : ℕ} (hk : 4 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (N T ρ : ℝ), C ≤ N →
      N^k ≤ T → T ≤ N^(k+1) → 2 ≤ Nat.ceil (N/T^(1/((k:ℝ)+2))) →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ∀ (W : Finset ℝ) (E : Finset (ℝ×ℝ)), E ⊆ W.product W →
      (∀ x : ℝ, ((W.filter (fun y =>
        |x-y| ≤ N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))))).card:ℝ) ≤ N^ρ) →
      (∀ p∈E, T ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*T) →
      let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
      ∀ Q : ℕ, 1 ≤ Q → Q ≤ H →
      tailCellVolume k H*(∑ p∈E, ∑ n∈S, ‖GafniTao.heathBrownWeylSum (k+2) Q
        (GafniTao.heathBrownCoefficientCenter (k+2)
          (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1)) n)‖) ≤
      (1+2*Real.pi*((k:ℝ)+2)^2)*tailJointMajorant S k H W E N ε ρ := by
  classical
  obtain ⟨C,hC,hmean⟩ := tail_joint_weyl_mean hk hε
  refine ⟨C,hC,?_⟩
  intro S N T ρ hNC hTlo hThi hH hS W E hE hlocal hheight
  dsimp only
  intro Q hQ hQH
  have hNp : 0 < N := by linarith only [hC,hNC]
  let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
  have hHp : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H from lt_of_lt_of_le (by norm_num) hH)
  let v := tailCellVolume k H
  let c : ℝ := 2*Real.pi*((k:ℝ)+2)^2/(H:ℝ)
  let M := tailJointMajorant S k H W E N ε ρ
  have hv : 0 ≤ v := by dsimp only [v,tailCellVolume]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hM : 0 ≤ M := by dsimp only [M,tailJointMajorant,tailCellVolume]; positivity
  have hI (j : ℕ) (hj : j ≤ H) : tailIntegratedWeyl S k H E j ≤ ENNReal.ofReal M :=
    hmean S N T ρ hNC hTlo hThi hH hS W E hE hlocal hheight j hj
  have htail : (∑ j∈Finset.Ico 1 Q, tailIntegratedWeyl S k H E j) ≤
      (H:ENNReal)*ENNReal.ofReal M := by
    calc
      _ ≤ ∑ _j∈Finset.Ico 1 Q, ENNReal.ofReal M := Finset.sum_le_sum
        (fun j hj => hI j ((Finset.mem_Ico.mp hj).2.le.trans hQH))
      _ = ((Finset.Ico 1 Q).card:ENNReal)*ENNReal.ofReal M := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_left
        exact_mod_cast (show (Finset.Ico 1 Q).card ≤ H by simp only [Nat.card_Ico]; omega)
  have hh := (tail_joint_center_integral S E (k:=k) hH hQ hQH).trans
    (add_le_add (hI Q hQH) (mul_le_mul_right htail (ENNReal.ofReal c)))
  let U : ℝ := ∑ p∈E, ∑ n∈S, ‖GafniTao.heathBrownWeylSum (k+2) Q
    (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1)) n)‖
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have heleft : ENNReal.ofReal (v*U) = ENNReal.ofReal v*
      (∑ p∈E, ∑ n∈S, ENNReal.ofReal ‖GafniTao.heathBrownWeylSum (k+2) Q
        (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1)) n)‖) := by
    rw [ENNReal.ofReal_mul hv]
    congr 1
    dsimp only [U]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  change ENNReal.ofReal v*_ ≤ ENNReal.ofReal M+ENNReal.ofReal c*((H:ENNReal)*ENNReal.ofReal M) at hh
  rw [←heleft] at hh
  have hr := ENNReal.toReal_mono
    (show ENNReal.ofReal M+ENNReal.ofReal c*((H:ENNReal)*ENNReal.ofReal M) ≠ ∞ by finiteness) hh
  rw [ENNReal.toReal_ofReal (mul_nonneg hv hU),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hM,ENNReal.toReal_ofReal hc,
    ENNReal.toReal_natCast] at hr
  have he : M+c*((H:ℝ)*M)=(1+2*Real.pi*((k:ℝ)+2)^2)*M := by dsimp only [c]; field_simp
  exact hr.trans_eq he

#print axioms tail_joint_center_uniform

theorem logarithmicTaylorPhase_tail_norm (k : ℕ) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ‖iteratedDeriv (k+2) (PintzEndpointResearch.logarithmicTaylorPhase t) x‖ =
      ((k+1).factorial:ℝ)*t/(2*Real.pi*x^(k+2)) := by
  have hh := PintzEndpointResearch.logarithmicTaylorPhase_coordinate (k+1) t hx
  have hfac : (((k+1)+1).factorial:ℝ) ≠ 0 := by positivity
  have hraw : iteratedDeriv (k+2) (PintzEndpointResearch.logarithmicTaylorPhase t) x =
      (-1:ℝ)^(k+2)*(((k+1).factorial:ℝ)*t/(2*Real.pi*x^(k+2))) := by
    rw [(div_eq_iff hfac).mp hh,Nat.factorial_succ]
    push_cast
    field_simp
  rw [hraw,norm_mul]
  have hsign : ‖(-1:ℝ)^(k+2)‖=1 := by simp
  rw [hsign,one_mul,Real.norm_eq_abs,abs_of_pos (by positivity)]

theorem tail_shifted_Abel {k : ℕ} {N T t : ℝ} {n H : ℕ}
    (hN : 0 < N) (hT : 0 < T) (ht : 0 < t) (htT : t ≤ 2*T)
    (hn : N ≤ (n:ℝ)) (hH : 1 ≤ H) :
    ‖∑ h∈Finset.Icc 1 H, GafniTao.heathBrownPhase
      (PintzEndpointResearch.logarithmicTaylorPhase t ((n+h:ℕ):ℝ))‖ ≤
      ‖GafniTao.heathBrownWeylSum (k+2) H
        (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖+
      (2*((k+1).factorial:ℝ)*T/N^(k+2)*(H:ℝ)^(k+1))*∑ j∈Finset.Ico 1 H,
        ‖GafniTao.heathBrownWeylSum (k+2) j
          (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖ := by
  have hnp : 0 < (n:ℝ) := hN.trans_le hn
  have hsmooth : ContDiffOn ℝ (k+2:ℕ) (PintzEndpointResearch.logarithmicTaylorPhase t) (Set.Ioi 0) := by
    intro x hx
    have hl : ContDiffAt ℝ (k+2:ℕ) Real.log x := Real.contDiffAt_log.mpr (ne_of_gt hx)
    exact (contDiffAt_const.mul hl).contDiffWithinAt
  have hsmoothD : ContDiffOn ℝ (k+1:ℕ) (deriv (PintzEndpointResearch.logarithmicTaylorPhase t)) (Set.Ioi 0) :=
    hsmooth.deriv_of_isOpen isOpen_Ioi (by norm_cast)
  have hfat : ContDiffAt ℝ k (deriv (PintzEndpointResearch.logarithmicTaylorPhase t)) n :=
    (hsmoothD.contDiffAt (Ioi_mem_nhds hnp)).of_le (by norm_cast; omega)
  have hfd (x : ℝ) (hx : x∈Set.Icc (1:ℝ) H) :
      HasDerivAt (PintzEndpointResearch.logarithmicTaylorPhase t)
        (deriv (PintzEndpointResearch.logarithmicTaylorPhase t) ((n:ℝ)+x)) ((n:ℝ)+x) := by
    have hnx : 0 < (n:ℝ)+x := by linarith only [hnp,hx.1]
    exact ((hsmooth.contDiffAt (Ioi_mem_nhds hnx)).differentiableAt (by norm_cast)).hasDerivAt
  have hfon (x : ℝ) (_hx : x∈Set.Icc (1:ℝ) H) :
      ContDiffOn ℝ (k+1:ℕ) (deriv (PintzEndpointResearch.logarithmicTaylorPhase t))
        (Set.Icc (n:ℝ) ((n:ℝ)+x)) :=
    hsmoothD.mono (fun _ hξ => hnp.trans_le hξ.1)
  have hderiv (x : ℝ) (_hx : x∈Set.Icc (1:ℝ) H) (ξ : ℝ)
      (hξ : ξ∈Set.Ioo (n:ℝ) ((n:ℝ)+x)) :
      ‖iteratedDeriv (k+2) (PintzEndpointResearch.logarithmicTaylorPhase t) ξ‖ ≤
        ((k+1).factorial:ℝ)*(T/(Real.pi*N^(k+2))) := by
    have hξp : 0 < ξ := hnp.trans hξ.1
    rw [logarithmicTaylorPhase_tail_norm k ht hξp]
    calc
      _ ≤ ((k+1).factorial:ℝ)*(2*T)/(2*Real.pi*N^(k+2)) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN.le (hn.trans hξ.1.le) (k+2)) (by positivity)
      _ = _ := by field_simp
  have hh := GafniTao.heathBrown_shifted_source_sum_norm_le_partial
    (k:=k+2) (H:=H) (A:=((k+1).factorial:ℝ)) (lambda:=T/(Real.pi*N^(k+2)))
    (by omega) hH hfat hfd hfon hderiv
  simp only [show k+2-1=k+1 by omega,Nat.cast_add] at hh ⊢
  simp_rw [GafniTao.norm_heathBrownWeylSum_center_eq_TaylorPolynomialSum (by omega : 1 ≤ k+2)]
  have hc : 2*Real.pi*(((k+1).factorial:ℝ)*(T/(Real.pi*N^(k+2)))*(H:ℝ)^(k+1))=
      2*((k+1).factorial:ℝ)*T/N^(k+2)*(H:ℝ)^(k+1) := by field_simp
  rw [hc] at hh
  exact hh

#print axioms logarithmicTaylorPhase_tail_norm
#print axioms tail_shifted_Abel

abbrev tailLogKernel := PintzFirstEndpointResearch.quarticLogKernel

theorem tail_actual_Abel (S : Finset ℕ) {N T t : ℝ} {k H : ℕ}
    (hN : 0 < N) (hT : 0 < T) (ht : 0 < t) (htT : t ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ)) (hinterval : ∃ a b : ℕ, S=Finset.Icc a b) (hH : 1 ≤ H) :
    (H:ℝ)*‖tailLogKernel S t‖ ≤
      (∑ n∈S, ‖GafniTao.heathBrownWeylSum (k+2) H
        (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖)+
      (2*((k+1).factorial:ℝ)*T/N^(k+2)*(H:ℝ)^(k+1))*(∑ j∈Finset.Ico 1 H, ∑ n∈S, ‖GafniTao.heathBrownWeylSum (k+2) j
        (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖)+
      (H:ℝ)*((H:ℝ)+1) := by
  classical
  by_cases hempty : S=∅
  · simp only [hempty,PintzFirstEndpointResearch.quarticLogKernel,Finset.sum_empty,norm_zero,mul_zero,zero_add]
    positivity
  have hnonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨a,b,habS⟩ := hinterval
  have hab : a ≤ b := by
    obtain ⟨n,hn⟩ := hnonempty
    rw [habS] at hn
    exact (Finset.mem_Icc.mp hn).1.trans (Finset.mem_Icc.mp hn).2
  have ha : 1 ≤ a := by
    have hh := hS a (by rw [habS]; exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩)
    have hap : 0 < a := by exact_mod_cast hN.trans_le hh
    omega
  let U : ℂ := ∑ n∈S, ∑ h∈Finset.Icc 1 H,
    GafniTao.heathBrownPhase (PintzEndpointResearch.logarithmicTaylorPhase t ((n+h:ℕ):ℝ))
  have hboundary : ‖U-(H:ℂ)*tailLogKernel S t‖ ≤ (H:ℝ)*((H:ℝ)+1) := by
    have hh := PintzEndpointResearch.norm_interval_phase_average_sub_le
      (PintzEndpointResearch.logarithmicTaylorPhase t) ha hab H
    rw [Finset.sum_comm] at hh
    simpa only [U,PintzFirstEndpointResearch.quarticLogKernel,habS] using hh
  have hentry : (H:ℝ)*‖tailLogKernel S t‖ ≤ ‖U‖+(H:ℝ)*((H:ℝ)+1) := by
    calc
      _ = ‖(H:ℂ)*tailLogKernel S t‖ := by rw [norm_mul,Complex.norm_natCast]
      _ = ‖U-(U-(H:ℂ)*tailLogKernel S t)‖ := by congr 1; ring
      _ ≤ ‖U‖+‖U-(H:ℂ)*tailLogKernel S t‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl hboundary
  let c : ℝ := 2*((k+1).factorial:ℝ)*T/N^(k+2)*(H:ℝ)^(k+1)
  let F (j n : ℕ) : ℝ := ‖GafniTao.heathBrownWeylSum (k+2) j
    (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖
  have hsum : ‖U‖ ≤ (∑ n∈S, F H n)+c*(∑ j∈Finset.Ico 1 H, ∑ n∈S, F j n) := by
    calc
      _ ≤ ∑ n∈S, ‖∑ h∈Finset.Icc 1 H, GafniTao.heathBrownPhase
          (PintzEndpointResearch.logarithmicTaylorPhase t ((n+h:ℕ):ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ n∈S, (F H n+c*∑ j∈Finset.Ico 1 H, F j n) :=
        Finset.sum_le_sum (fun n hn => tail_shifted_Abel (k:=k) hN hT ht htT (hS n hn) hH)
      _ = _ := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
  exact hentry.trans (add_le_add hsum le_rfl)

#print axioms tail_actual_Abel

/-- Source entry for the actual logarithmic kernel, with both Abel
transfers and the exact finite-interval boundary term retained. -/
theorem tail_joint_source {k : ℕ} (hk : 4 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (N T ρ : ℝ), C ≤ N →
      N^k ≤ T → T ≤ N^(k+1) → 2 ≤ Nat.ceil (N/T^(1/((k:ℝ)+2))) →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) → (∃ a b : ℕ, S=Finset.Icc a b) →
      ∀ (W : Finset ℝ) (E : Finset (ℝ×ℝ)), E ⊆ W.product W →
      (∀ x : ℝ, ((W.filter (fun y =>
        |x-y| ≤ N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))))).card:ℝ) ≤ N^ρ) →
      (∀ p∈E, T ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*T) →
      let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
      tailCellVolume k H*(H:ℝ)*(∑ p∈E, ‖tailLogKernel S (p.2-p.1)‖) ≤
        (1+2*((k+1).factorial:ℝ)*T/N^(k+2)*(H:ℝ)^(k+2))*
          (1+2*Real.pi*((k:ℝ)+2)^2)*tailJointMajorant S k H W E N ε ρ+
        tailCellVolume k H*(E.card:ℝ)*(H:ℝ)*((H:ℝ)+1) := by
  classical
  obtain ⟨C,hC,hcenter⟩ := tail_joint_center_uniform hk hε
  refine ⟨C,hC,?_⟩
  intro S N T ρ hNC hTlo hThi hH hS hinterval W E hE hlocal hheight
  have hNp : 0 < N := by linarith only [hC,hNC]
  have hTp : 0 < T := (pow_pos hNp _).trans_le hTlo
  let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
  let v := tailCellVolume k H
  let c : ℝ := 2*((k+1).factorial:ℝ)*T/N^(k+2)*(H:ℝ)^(k+1)
  let M := (1+2*Real.pi*((k:ℝ)+2)^2)*tailJointMajorant S k H W E N ε ρ
  let A (p : ℝ×ℝ) (j : ℕ) : ℝ := ∑ n∈S, ‖GafniTao.heathBrownWeylSum (k+2) j
    (GafniTao.heathBrownCoefficientCenter (k+2) (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1)) n)‖
  have hv : 0 ≤ v := by dsimp only [v,tailCellVolume]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hM : 0 ≤ M := by dsimp only [M,tailJointMajorant,tailCellVolume]; positivity
  have hpartial (j : ℕ) (hj : 1 ≤ j) (hjH : j ≤ H) : v*(∑ p∈E, A p j) ≤ M :=
    hcenter S N T ρ hNC hTlo hThi hH hS W E hE hlocal hheight j hj hjH
  have htail : (∑ j∈Finset.Ico 1 H, v*(∑ p∈E, A p j)) ≤ (H:ℝ)*M := by
    calc
      _ ≤ ∑ _j∈Finset.Ico 1 H, M := Finset.sum_le_sum (fun j hj =>
        hpartial j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2.le)
      _ = ((Finset.Ico 1 H).card:ℝ)*M := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast
        (show (Finset.Ico 1 H).card ≤ H by simp only [Nat.card_Ico]; omega)) hM
  have hsum : (H:ℝ)*(∑ p∈E, ‖tailLogKernel S (p.2-p.1)‖) ≤
      (∑ p∈E, A p H)+c*(∑ j∈Finset.Ico 1 H, ∑ p∈E, A p j)+
      (E.card:ℝ)*((H:ℝ)*((H:ℝ)+1)) := by
    have hh := Finset.sum_le_sum (fun p hp => tail_actual_Abel S (k:=k) (H:=H) hNp hTp
      (hTp.trans_le (hheight p hp).1) (hheight p hp).2 (fun n hn => (hS n hn).1) hinterval (by omega))
    change (∑ p∈E, (H:ℝ)*‖tailLogKernel S (p.2-p.1)‖) ≤
      ∑ p∈E, (A p H+c*(∑ j∈Finset.Ico 1 H, A p j)+(H:ℝ)*((H:ℝ)+1)) at hh
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hh
    rw [Finset.sum_comm (s:=E) (t:=Finset.Ico 1 H) (f:=A)] at hh
    exact hh
  calc
    _ = v*((H:ℝ)*(∑ p∈E, ‖tailLogKernel S (p.2-p.1)‖)) := by ring
    _ ≤ v*((∑ p∈E, A p H)+c*(∑ j∈Finset.Ico 1 H, ∑ p∈E, A p j)+
        (E.card:ℝ)*((H:ℝ)*((H:ℝ)+1))) := mul_le_mul_of_nonneg_left hsum hv
    _ = v*(∑ p∈E, A p H)+c*(∑ j∈Finset.Ico 1 H, v*(∑ p∈E, A p j))+
        v*(E.card:ℝ)*(H:ℝ)*((H:ℝ)+1) := by rw [←Finset.mul_sum]; ring
    _ ≤ M+c*((H:ℝ)*M)+v*(E.card:ℝ)*(H:ℝ)*((H:ℝ)+1) :=
      add_le_add (add_le_add (hpartial H (by omega) le_rfl) (mul_le_mul_of_nonneg_left htail hc)) le_rfl
    _ = _ := by
      dsimp only [M,c,v]
      rw [show (H:ℝ)^(k+2)=(H:ℝ)^(k+1)*(H:ℝ) by rw [pow_succ]]
      ring

#print axioms tail_joint_source

theorem tailJointMajorant_pow (S : Finset ℕ) (k H : ℕ) (W : Finset ℝ) (E : Finset (ℝ×ℝ))
    {N ε ρ : ℝ} (hN : 0 ≤ N) :
    let s := GafniTao.heathBrownCriticalMoment (k+2)
    (tailJointMajorant S k H W E N ε ρ)^(2*s) =
      (GafniTao.fordVinogradovMomentNat s (k+1) H:ℝ)*
        (((W.card:ℝ)^3*N^(1+ρ+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*tailCellVolume k H)*
        ((E.card:ℝ)*(S.card:ℝ)*tailCellVolume k H)^(2*s-2) := by
  let s := GafniTao.heathBrownCriticalMoment (k+2)
  let J := GafniTao.fordVinogradovMomentNat s (k+1) H
  let A : ℝ := ((W.card:ℝ)^3*N^(1+ρ+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*tailCellVolume k H
  let B : ℝ := (E.card:ℝ)*(S.card:ℝ)*tailCellVolume k H
  have hspos : (0:ℝ) < s := GafniTao.heathBrownCriticalMoment_pos (by omega)
  have hs : 1 ≤ s := by exact_mod_cast hspos
  have hA : 0 ≤ A := by dsimp only [A,tailCellVolume]; positivity
  have hB : 0 ≤ B := by dsimp only [B,tailCellVolume]; positivity
  have hexp : (1/(2*(s:ℝ)))*((2*s:ℕ):ℝ)=1 := by push_cast; field_simp
  have hJpow : ((J:ℝ)^(1/(2*(s:ℝ))))^(2*s)=J := by
    rw [←Real.rpow_mul_natCast (Nat.cast_nonneg J),hexp,Real.rpow_one]
  have hApow : (A^(1/(2*(s:ℝ))))^(2*s)=A := by
    rw [←Real.rpow_mul_natCast hA,hexp,Real.rpow_one]
  have hBpow : (B^(1-1/(s:ℝ)))^(2*s)=B^(2*s-2) := by
    rw [←Real.rpow_mul_natCast hB]
    have he : (1-1/(s:ℝ))*((2*s:ℕ):ℝ)=((2*s-2:ℕ):ℝ) := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2*s)]
      push_cast
      field_simp
    rw [he,Real.rpow_natCast]
  change ((J:ℝ)^(1/(2*(s:ℝ)))*A^(1/(2*(s:ℝ)))*B^(1-1/(s:ℝ)))^(2*s)=
    (J:ℝ)*A*B^(2*s-2)
  rw [mul_pow,mul_pow,hJpow,hApow,hBpow]

#print axioms tailJointMajorant_pow

theorem tail_adaptive_remainder_scales {k : ℕ} {N T : ℝ} (hk : 4 ≤ k)
    (hN : 2 ≤ N) (hbig : (2:ℝ)^(k+2) ≤ N) (hTlo : N^k ≤ T) (hThi : T ≤ N^(k+1)) :
    let H := Nat.ceil (N/T^(1/((k:ℝ)+2)))
    T/N^(k+2)*(H:ℝ)^(k+2) ≤ 2^(k+2) ∧ (H:ℝ) ≤ 2*N^((1:ℝ)/3) := by
  let n : ℝ := (k:ℝ)+2
  let X := T^(1/n)
  let H := Nat.ceil (N/X)
  have hn : 0 < n := by dsimp only [n]; positivity
  have hn6 : 6 ≤ n := by dsimp only [n]; exact_mod_cast (by omega : 6 ≤ k+2)
  have hNp : 0 < N := by linarith only [hN]
  have hN1 : 1 ≤ N := by linarith only [hN]
  have hTp : 0 < T := (pow_pos hNp _).trans_le hTlo
  have hX : 0 < X := Real.rpow_pos_of_pos hTp _
  obtain ⟨hH,hHlo,hHscale,hHN⟩ := tail_adaptive_block_scales (by omega : 1 ≤ k) hN hbig hTlo hThi
  change (H:ℝ) ≤ 2*N/X at hHscale
  have hXpow : X^(k+2)=T := by
    dsimp only [X]
    rw [←Real.rpow_natCast,←Real.rpow_mul hTp.le]
    rw [show (1/n)*((k+2:ℕ):ℝ)=1 by dsimp only [n]; push_cast; field_simp,Real.rpow_one]
  have hXlo : N^((k:ℝ)/n) ≤ X := by
    calc
      _ = (N^k)^(1/n) := by rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow (pow_nonneg hNp.le _) hTlo (by positivity)
  change T/N^(k+2)*(H:ℝ)^(k+2) ≤ 2^(k+2) ∧ (H:ℝ) ≤ 2*N^((1:ℝ)/3)
  constructor
  · calc
      _ ≤ T/N^(k+2)*(2*N/X)^(k+2) := by gcongr
      _ = _ := by rw [div_pow,mul_pow,hXpow]; field_simp
  · apply hHscale.trans
    calc
      _ ≤ 2*N/N^((k:ℝ)/n) := div_le_div_of_nonneg_left (by positivity) (by positivity) hXlo
      _ = 2*N^(2/n) := by
        rw [mul_div_assoc]
        congr 1
        nth_rw 1 [←Real.rpow_one N]
        rw [←Real.rpow_sub hNp]
        congr 1
        dsimp only [n]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 ((div_le_iff₀ hn).mpr (by nlinarith only [hn6]))) (by norm_num)

#print axioms tail_adaptive_remainder_scales

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Critical moment of the actual logarithmic kernels at every integer
order. Both the local occupancy and the Vinogradov input are derived here
for the original large-value pattern. -/
theorem tail_endpoint_kernel_moment {k : ℕ} (hk : 4 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    let p := 2*GafniTao.heathBrownCriticalMoment (k+2)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/(100000*(((k:ℝ)+2)*((k:ℝ)+1))^2) ∧
      ∃ C : ℝ, 4 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ P : LargeValuePattern, C ≤ P.N →
      P.N^(1-1/(2*((k:ℝ)+2)*((k:ℝ)+1))-δ) ≤ P.V →
      ∀ T : ℝ, P.N^k ≤ T → T ≤ P.N^(k+1) →
      ∀ E : Finset (ℝ×ℝ), E ⊆ P.ordinates.product P.ordinates →
      (∀ q∈E, T ≤ q.2-q.1 ∧ q.2-q.1 ≤ 2*T) →
      (∑ q∈E, ‖tailLogKernel P.indices (q.2-q.1)‖)^p ≤
        K*P.N^ε*((P.ordinates.card:ℝ)^(2*p-1)*
          P.N^((p:ℝ)-1+101/(100*((k:ℝ)+2)*((k:ℝ)+1))+ε)+
          (P.ordinates.card:ℝ)^(2*p)*P.N^((p:ℝ)-1-1/100)) := by
  classical
  let s := GafniTao.heathBrownCriticalMoment (k+2)
  let p := 2*s
  let q := p-2
  let ρ : ℝ := 101/(100*((k:ℝ)+2)*((k:ℝ)+1))
  have hspos : (0:ℝ) < s := GafniTao.heathBrownCriticalMoment_pos (by omega)
  have hs : 1 ≤ s := by exact_mod_cast hspos
  have hp : 2 ≤ p := by dsimp only [p]; omega
  have hqcast : (q:ℝ)=(p:ℝ)-2 := by dsimp only [q]; rw [Nat.cast_sub hp]; norm_num
  obtain ⟨δ,hδ,hδle,C₀,hC₀,hlocal⟩ := tail_endpoint_local_occupancy hk
  obtain ⟨C₁,_,hsource⟩ := tail_joint_source hk hε
  obtain ⟨J₀,hJ₀,hvmvt⟩ := GafniTao.heathBrownVMVTMainConjecture_native.critical
    (by omega : 2 ≤ k+2) hε
  let D : ℝ := (1+2*((k+1).factorial:ℝ)*2^(k+2))*(1+2*Real.pi*((k:ℝ)+2)^2)
  let K₀ : ℝ := D^p*J₀/2^(k+1)*2^q
  let K : ℝ := 2^(p-1)*(K₀+3^p)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hK₀ : 0 < K₀ := by dsimp only [K₀]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨δ,hδ,hδle,max C₀ (max C₁ (2^(k+2))),hC₀.trans (le_max_left _ _),K,hK,?_⟩
  intro P hPN hV T hTlo hThi E hE hheight
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hN2 : 2 ≤ P.N := (by linarith only [hC₀] : 2 ≤ C₀).trans ((le_max_left _ _).trans hPN)
  have hbig : (2:ℝ)^(k+2) ≤ P.N := (le_max_right _ _).trans ((le_max_right _ _).trans hPN)
  have hTp : 0 < T := (pow_pos hNp _).trans_le hTlo
  let H := Nat.ceil (P.N/T^(1/((k:ℝ)+2)))
  let v := tailCellVolume k H
  let R : ℝ := P.ordinates.card
  let I : ℝ := P.indices.card
  let A : ℝ := E.card
  let B : ℝ := R^3*P.N^(1+ρ+ε)+R^4*P.N^((99:ℝ)/100)
  let F : ℝ := R^(2*p-1)*P.N^((p:ℝ)-1+ρ+ε)+R^(2*p)*P.N^((p:ℝ)-1-1/100)
  let U : ℝ := ∑ z∈E, ‖tailLogKernel P.indices (z.2-z.1)‖
  let M := tailJointMajorant P.indices k H P.ordinates E P.N ε ρ
  let J := GafniTao.fordVinogradovMomentNat s (k+1) H
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hI : 0 ≤ I := Nat.cast_nonneg _
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : 0 ≤ M := by dsimp only [M,tailJointMajorant,tailCellVolume]; positivity
  obtain ⟨hH,_,_,hHN⟩ := tail_adaptive_block_scales (by omega : 1 ≤ k) hN2 hbig hTlo hThi
  obtain ⟨hTscale,hHscale⟩ := tail_adaptive_remainder_scales hk hN2 hbig hTlo hThi
  have hHp : 0 < (H:ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hv : 0 < v := by dsimp only [v,tailCellVolume]; positivity
  have hAI : A ≤ R^2 := by
    dsimp only [A,R]
    have hh := Finset.card_le_card hE
    rw [Finset.product_eq_sprod,Finset.card_product] at hh
    exact_mod_cast (show E.card ≤ P.ordinates.card^2 by simpa only [pow_two] using hh)
  have hIN : I ≤ 2*P.N := P.indices_card_cast_le_two_mul_N
  have hsource' := hsource P.indices P.N T ρ
    ((le_max_left _ _).trans ((le_max_right _ _).trans hPN)) hTlo hThi hH
    (fun n hn => (P.mem_indices_iff n).mp hn)
    ⟨P.scale,2*P.scale,P.indices_eq_dyadicInterval⟩ P.ordinates E hE
    (hlocal P ((le_max_left _ _).trans hPN) hV) hheight
  have hmain : v*(H:ℝ)*U ≤ D*M+v*A*(H:ℝ)*((H:ℝ)+1) := by
    apply hsource'.trans
    change (1+2*((k+1).factorial:ℝ)*T/P.N^(k+2)*(H:ℝ)^(k+2))*
      (1+2*Real.pi*((k:ℝ)+2)^2)*M+_ ≤ D*M+_
    apply add_le_add _ le_rfl
    dsimp only [D]
    apply mul_le_mul_of_nonneg_right _ hM
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply add_le_add_right _ 1
    convert mul_le_mul_of_nonneg_left hTscale
      (show 0 ≤ 2*((k+1).factorial:ℝ) by positivity) using 1
    ring
  have hentry : U ≤ D*M/(v*(H:ℝ))+A*((H:ℝ)+1) := by
    apply (mul_le_mul_iff_left₀ (mul_pos hv hHp)).mp
    convert hmain using 1 <;> field_simp
  have hMpow : M^p=(J:ℝ)*(B*v)*(A*I*v)^q := tailJointMajorant_pow _ _ _ _ _ hNp.le
  have hJbound : (J:ℝ) ≤ J₀*(H:ℝ)^((s:ℝ)+ε) := by
    simpa only [show k+2-1=k+1 by omega] using
      (GafniTao.heathBrownCriticalMoment_bound (by omega : 2 ≤ k+2) (by omega : 1 ≤ H) hvmvt)
  have hcoef : D^p*(J:ℝ)/(v*(H:ℝ)^p) ≤ (D^p*J₀/2^(k+1))*P.N^ε := by
    calc
      _ ≤ D^p*(J₀*(H:ℝ)^((s:ℝ)+ε))/(v*(H:ℝ)^p) := by gcongr
      _ = (D^p*J₀/2^(k+1))*(H:ℝ)^ε := by
        rw [Real.rpow_add hHp,Real.rpow_natCast]
        have hpow : (H:ℝ)^p=(H:ℝ)^s*(H:ℝ)^s := by dsimp only [p]; rw [two_mul,pow_add]
        rw [hpow]
        dsimp only [v,tailCellVolume]
        change D^p*(J₀*((H:ℝ)^s*(H:ℝ)^ε))/((2^(k+1)/(H:ℝ)^s)*((H:ℝ)^s*(H:ℝ)^s))=_
        field_simp
      _ ≤ _ := by gcongr
  have hfarPow : (D*M/(v*(H:ℝ)))^p ≤ K₀*P.N^ε*F := by
    calc
      _ = (D^p*(J:ℝ)/(v*(H:ℝ)^p))*(A^q*I^q*B) := by
        rw [div_pow,mul_pow,hMpow]
        simp only [mul_pow]
        have hvpow : v^p=v^q*v^2 := by rw [show p=q+2 by dsimp only [q]; omega,pow_add]
        rw [hvpow]
        field_simp
      _ ≤ ((D^p*J₀/2^(k+1))*P.N^ε)*((R^2)^q*(2*P.N)^q*B) := by gcongr
      _ = K₀*P.N^ε*F := by
        have he1 : P.N^q*P.N^(1+ρ+ε)=P.N^((p:ℝ)-1+ρ+ε) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hNp,hqcast]
          congr 1
          ring
        have he2 : P.N^q*P.N^((99:ℝ)/100)=P.N^((p:ℝ)-1-1/100) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hNp,hqcast]
          congr 1
          ring
        have heB : P.N^q*B=R^3*P.N^((p:ℝ)-1+ρ+ε)+R^4*P.N^((p:ℝ)-1-1/100) := by
          calc
            _ = R^3*(P.N^q*P.N^(1+ρ+ε))+R^4*(P.N^q*P.N^((99:ℝ)/100)) := by
              dsimp only [B]
              ring
            _ = _ := by rw [he1,he2]
        have hr1 : (R^2)^q*R^3=R^(2*p-1) := by rw [←pow_mul,←pow_add]; congr 1; omega
        have hr2 : (R^2)^q*R^4=R^(2*p) := by rw [←pow_mul,←pow_add]; congr 1; omega
        have heF : (R^2)^q*(P.N^q*B)=F := by
          rw [heB,mul_add,←mul_assoc,←mul_assoc,hr1,hr2]
        calc
          _ = K₀*P.N^ε*((R^2)^q*(P.N^q*B)) := by dsimp only [K₀]; rw [mul_pow]; ring
          _ = _ := by rw [heF]
  have hboundary : (A*((H:ℝ)+1))^p ≤ 3^p*P.N^ε*F := by
    have h1 : 1 ≤ P.N^((1:ℝ)/3) := Real.one_le_rpow P.one_lt_N.le (by norm_num)
    have hHplus : (H:ℝ)+1 ≤ 3*P.N^((1:ℝ)/3) := by linarith only [hHscale,h1]
    have hpow : (P.N^((1:ℝ)/3))^p=P.N^((p:ℝ)/3) := by
      rw [←Real.rpow_mul_natCast hNp.le]
      congr 1
      ring
    have hpr : (2:ℝ) ≤ p := by exact_mod_cast hp
    calc
      _ ≤ (R^2*(3*P.N^((1:ℝ)/3)))^p := by gcongr
      _ = 3^p*R^(2*p)*P.N^((p:ℝ)/3) := by rw [mul_pow,mul_pow,hpow,←pow_mul]; ring
      _ ≤ 3^p*R^(2*p)*P.N^((p:ℝ)-1-1/100) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hpr])) (by positivity)
      _ ≤ 3^p*F := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left
          (mul_nonneg (pow_nonneg hR (2*p-1))
            (Real.rpow_nonneg hNp.le ((p:ℝ)-1+ρ+ε)))) (by positivity)
      _ ≤ _ := by
        have hh := Real.one_le_rpow P.one_lt_N.le hε.le
        calc
          _ = 3^p*1*F := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) hF
  calc
    _ ≤ (D*M/(v*(H:ℝ))+A*((H:ℝ)+1))^p := pow_le_pow_left₀ hU hentry p
    _ ≤ 2^(p-1)*((D*M/(v*(H:ℝ)))^p+(A*((H:ℝ)+1))^p) :=
      add_pow_le (by positivity) (by positivity) p
    _ ≤ 2^(p-1)*(K₀*P.N^ε*F+3^p*P.N^ε*F) := by gcongr
    _ = _ := by dsimp only [K,F,R,ρ]; ring

#print axioms tail_endpoint_kernel_moment

def tailFarPairs (P : LargeValuePattern) (L : ℝ) : Finset (ℝ×ℝ) :=
  (P.ordinates.product P.ordinates).filter (fun p => L < p.2-p.1)

def tailDyadicPairs (P : LargeValuePattern) (L : ℝ) (j : ℕ) : Finset (ℝ×ℝ) :=
  (P.ordinates.product P.ordinates).filter (fun p =>
    L*(2:ℝ)^j ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*(L*(2:ℝ)^j))

def tailFarKernelSum (P : LargeValuePattern) (L : ℝ) : ℝ :=
  ∑ p∈tailFarPairs P L, ‖tailLogKernel P.indices (p.2-p.1)‖

theorem tailFarKernelSum_le_dyadic (P : LargeValuePattern) (L : ℝ) (hL : 1 ≤ L) :
    tailFarKernelSum P L ≤ ∑ j : Fin (⌊Real.logb 2 P.T⌋₊+1),
      ∑ p∈tailDyadicPairs P L j, ‖tailLogKernel P.indices (p.2-p.1)‖ := by
  classical
  let F := tailFarPairs P L
  let J := Fin (⌊Real.logb 2 P.T⌋₊+1)
  let g (p : ℝ×ℝ) := ‖tailLogKernel P.indices (p.2-p.1)‖
  have hpoint (p : ℝ×ℝ) (hp : p∈F) : g p ≤ ∑ j:J, if p∈tailDyadicPairs P L j then g p else 0 := by
    obtain ⟨hmem,hgap⟩ := Finset.mem_filter.mp hp
    have hpW := Finset.mem_product.mp hmem
    have hheight : p.2-p.1 ≤ P.T := (le_abs_self _).trans (P.ordinate_gap_le_height hpW.1 hpW.2)
    obtain ⟨j,_,hjlo,hjhi⟩ := exists_bounded_dyadic_slab (L) P.T (p.2-p.1)
      hL hgap.le hheight
    have hpj : p∈tailDyadicPairs P L j := Finset.mem_filter.mpr ⟨hmem,hjlo,hjhi⟩
    have hh := Finset.single_le_sum (s:=Finset.univ) (a:=j)
      (f:=fun i:J => if p∈tailDyadicPairs P L i then g p else 0)
      (fun i _ => by dsimp only [g]; split_ifs <;> positivity) (Finset.mem_univ j)
    simpa only [if_pos hpj] using hh
  calc
    _ ≤ ∑ p∈F, ∑ j:J, if p∈tailDyadicPairs P L j then g p else 0 := Finset.sum_le_sum hpoint
    _ = ∑ j:J, ∑ p∈F, if p∈tailDyadicPairs P L j then g p else 0 := Finset.sum_comm
    _ ≤ ∑ j:J, ∑ p∈tailDyadicPairs P L j, g p := by
      apply Finset.sum_le_sum
      intro j _
      rw [←Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p _ _
        exact norm_nonneg _

#print axioms tailFarKernelSum_le_dyadic


/-- Exact near/far decomposition of the Gram norm sum, retaining all ordered pairs. -/
theorem tail_gram_near_far (P : LargeValuePattern) (L : ℝ) (hL : 0 < L) :
    (∑ t∈P.ordinates, ∑ u∈P.ordinates, ‖tailLogKernel P.indices (u-t)‖) =
      (∑ t∈P.ordinates, ∑ u∈P.ordinates,
        if |u-t| ≤ L then ‖tailLogKernel P.indices (u-t)‖ else 0)+
        2*tailFarKernelSum P L := by
  classical
  let f (t u : ℝ) := ‖tailLogKernel P.indices (u-t)‖
  have hp (t u : ℝ) : f t u =
      (if |u-t| ≤ L then f t u else 0)+
      (if L < u-t then f t u else 0)+(if L < t-u then f t u else 0) := by
    by_cases h : |u-t| ≤ L
    · have h₁ : ¬L < u-t := not_lt.mpr ((le_abs_self _).trans h)
      have h₂ : ¬L < t-u := by rw [abs_sub_comm] at h; exact not_lt.mpr ((le_abs_self _).trans h)
      simp only [if_pos h,if_neg h₁,if_neg h₂,add_zero]
    · have hh : L < u-t ∨ L < t-u := by
        have := lt_of_not_ge h
        rcases le_total t u with ht|ht
        · rw [abs_of_nonneg (sub_nonneg.mpr ht)] at this
          exact Or.inl this
        · rw [abs_of_nonpos (sub_nonpos.mpr ht)] at this
          exact Or.inr (by linarith)
      rcases hh with hh|hh
      · have h₂ : ¬L < t-u := by linarith
        simp only [if_neg h,if_pos hh,if_neg h₂,zero_add,add_zero]
      · have h₁ : ¬L < u-t := by linarith
        simp only [if_neg h,if_neg h₁,if_pos hh,zero_add]
  have hpos : (∑ t∈P.ordinates, ∑ u∈P.ordinates, if L < u-t then f t u else 0)=tailFarKernelSum P L := by
    unfold tailFarKernelSum tailFarPairs
    rw [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  have hneg : (∑ t∈P.ordinates, ∑ u∈P.ordinates, if L < t-u then f t u else 0)=tailFarKernelSum P L := by
    rw [Finset.sum_comm]
    simpa only [f,PintzFirstEndpointResearch.quarticLogKernel_norm_sub_swap P] using hpos
  calc
    _ = ∑ t∈P.ordinates, ∑ u∈P.ordinates,
        ((if |u-t| ≤ L then f t u else 0)+(if L < u-t then f t u else 0)+
          (if L < t-u then f t u else 0)) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_congr rfl (fun u _ => hp t u)
    _ = _ := by simp only [Finset.sum_add_distrib,hpos,hneg]; dsimp only [f]; ring

#print axioms tail_gram_near_far

theorem tail_near_far_gram_source {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : LargeValuePattern) (L : ℝ), 0 < L →
      ((P.ordinates.card:ℝ)*P.V)^2 ≤ 2*P.N*
        ((P.ordinates.card:ℝ)*(2*P.N+C*(P.ordinates.card:ℝ)*
          ((2*L)/P.N)^(k+ε)*P.N^(l+ε)+
          4*Real.pi*C*P.N*(harmonic (Nat.ceil (2*L)) : ℝ))+
          2*tailFarKernelSum P L) := by
  classical
  obtain ⟨C,hC,hrow⟩ := PintzEndpointResearch.exponentPair_nearMatrix_row hpair hε
  refine ⟨C,hC,?_⟩
  intro P L hL
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hr (t : ℝ) (ht : t∈P.ordinates) := hrow P L hL ⟨t,ht⟩
  have he (t : ℝ) (ht : t∈P.ordinates) :
      (∑ u : P.ordinates, ‖PintzEndpointResearch.nearMatrix P (L) ⟨t,ht⟩ u‖) =
      ∑ u∈P.ordinates, if |u-t| ≤ L then ‖tailLogKernel P.indices (u-t)‖ else 0 := by
    simp only [PintzEndpointResearch.nearMatrix,PintzEndpointResearch.gramKernel,
      apply_ite norm,norm_zero,tailLogKernel,PintzFirstEndpointResearch.quarticLogKernel_eq_dirichlet]
    exact Finset.sum_attach P.ordinates (fun u : ℝ =>
      if |u-t| ≤ L then ‖∑ n∈P.indices, dirichletPhase n (u-t)‖ else 0)
  have hnear : (∑ t∈P.ordinates, ∑ u∈P.ordinates,
      if |u-t| ≤ L then ‖tailLogKernel P.indices (u-t)‖ else 0) ≤
      ∑ _t∈P.ordinates, (2*P.N+C*(P.ordinates.card:ℝ)*
        ((2*L)/P.N)^(k+ε)*P.N^(l+ε)+
        4*Real.pi*C*P.N*(harmonic (Nat.ceil (2*L)) : ℝ)) := by
    apply Finset.sum_le_sum
    intro t ht
    have hh := hr t ht
    rw [he t ht] at hh
    exact hh
  have hg := P.sharp_gram
  simp_rw [←PintzFirstEndpointResearch.quarticLogKernel_eq_dirichlet P] at hg
  rw [tail_gram_near_far P L hL] at hg
  apply hg.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  simpa only [Finset.sum_const,nsmul_eq_mul] using hnear

#print axioms tail_near_far_gram_source

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- The actual positive far-correlation sum, with all dyadic slabs and
their logarithmic cost assembled at the critical moment. -/
theorem tail_endpoint_far_moment {k : ℕ} (hk : 4 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    let p := 2*GafniTao.heathBrownCriticalMoment (k+2)
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/(100000*(((k:ℝ)+2)*((k:ℝ)+1))^2) ∧
      ∃ C : ℝ, 4 ≤ C ∧ ∀ P : LargeValuePattern, C ≤ P.N →
      P.N^(1-1/(2*((k:ℝ)+2)*((k:ℝ)+1))-δ) ≤ P.V →
      P.T ≤ P.N^(k+1) → ∀ L : ℝ, P.N^k ≤ L → L ≤ P.T →
      (tailFarKernelSum P L)^p ≤
        P.N^(2*ε)*((P.ordinates.card:ℝ)^(2*p-1)*
          P.N^((p:ℝ)-1+101/(100*((k:ℝ)+2)*((k:ℝ)+1))+ε)+
          (P.ordinates.card:ℝ)^(2*p)*P.N^((p:ℝ)-1-1/100)) := by
  classical
  let p := 2*GafniTao.heathBrownCriticalMoment (k+2)
  have hs : 1 ≤ GafniTao.heathBrownCriticalMoment (k+2) := by
    have hh := GafniTao.heathBrownCriticalMoment_pos (k:=k+2) (by omega)
    exact_mod_cast hh
  have hp : 2 ≤ p := by dsimp only [p]; omega
  obtain ⟨δ,hδ,hδle,C₀,hC₀,K,hK,hstep⟩ := tail_endpoint_kernel_moment hk hε
  let D : ℝ := ((k:ℝ)+1)/Real.log 2+1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp only [D]; positivity
  obtain ⟨C₁,hC₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (K*D^p) (by positivity) p hε)
  refine ⟨δ,hδ,hδle,max 8 (max C₀ C₁),(by norm_num : (4:ℝ) ≤ 8).trans (le_max_left _ _),?_⟩
  intro P hPN hV hThi L hLlo hLhi
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hN8 : 8 ≤ P.N := (le_max_left _ _).trans hPN
  have hPN₀ : C₀ ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans hPN)
  have hconst := hC₁ P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  have hL1 : 1 ≤ L := (one_le_pow₀ P.one_lt_N.le).trans hLlo
  have hT1 : 1 ≤ P.T := hL1.trans hLhi
  have hlogN : 1 ≤ Real.log P.N := by
    have he : Real.exp 1 ≤ P.N := Real.exp_one_lt_three.le.trans (by linarith only [hN8])
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  let J := Fin (⌊Real.logb 2 P.T⌋₊+1)
  let F : ℝ := (P.ordinates.card:ℝ)^(2*p-1)*
    P.N^((p:ℝ)-1+101/(100*((k:ℝ)+2)*((k:ℝ)+1))+ε)+
    (P.ordinates.card:ℝ)^(2*p)*P.N^((p:ℝ)-1-1/100)
  let U (j:J) : ℝ := ∑ q∈tailDyadicPairs P L j, ‖tailLogKernel P.indices (q.2-q.1)‖
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hJ : (Fintype.card J:ℝ) ≤ D*Real.log P.N := by
    have hh := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hT1)
    rw [Real.logb] at hh
    have hh' := (le_div_iff₀ hlog2).mp hh
    have htlog := Real.log_le_log P.T_pos hThi
    rw [←Real.rpow_natCast,Real.log_rpow hNp] at htlog
    simp only [J,Fintype.card_fin]
    push_cast at htlog ⊢
    apply (mul_le_mul_iff_left₀ hlog2).mp
    dsimp only [D]
    field_simp
    rw [Real.logb]
    nlinarith only [hh',htlog,hlogN,mul_le_mul_of_nonneg_right hlogN hlog2.le]
  have hU (j:J) : 0 ≤ U j := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hstep' (j:J) : (U j)^p ≤ K*P.N^ε*F := by
    by_cases he : (tailDyadicPairs P L j).Nonempty
    · obtain ⟨z,hz⟩ := he
      have hz' := Finset.mem_filter.mp hz
      have hzW := Finset.mem_product.mp hz'.1
      have hlow : P.N^k ≤ L*(2:ℝ)^(j:ℕ) := hLlo.trans
        (le_mul_of_one_le_right (by linarith only [hL1]) (one_le_pow₀ (by norm_num)))
      have hhigh : L*(2:ℝ)^(j:ℕ) ≤ P.N^(k+1) :=
        hz'.2.1.trans (((le_abs_self _).trans (P.ordinate_gap_le_height hzW.1 hzW.2)).trans hThi)
      exact hstep P hPN₀ hV _ hlow hhigh (tailDyadicPairs P L j)
        (Finset.filter_subset _ _) (fun _ hq => (Finset.mem_filter.mp hq).2)
    · have hz : tailDyadicPairs P L j=∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simp only [U,hz,Finset.sum_empty,zero_pow (by omega : p ≠ 0)]
      positivity
  have hsum : (∑ j:J, U j)^p ≤ (Fintype.card J:ℝ)^p*(K*P.N^ε*F) := by
    have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ) (f:=U) (fun j _ => hU j) (p-1)
    rw [show p-1+1=p by omega,Finset.card_univ] at hh
    calc
      _ ≤ (Fintype.card J:ℝ)^(p-1)*∑ j:J, (U j)^p := hh
      _ ≤ (Fintype.card J:ℝ)^(p-1)*∑ _j:J, (K*P.N^ε*F) := by gcongr with j; exact hstep' j
      _ = _ := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,←pow_succ]
        rw [show p-1+1=p by omega]
  calc
    _ ≤ (∑ j:J, U j)^p := pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (tailFarKernelSum_le_dyadic P L hL1) p
    _ ≤ (Fintype.card J:ℝ)^p*(K*P.N^ε*F) := hsum
    _ ≤ (D*Real.log P.N)^p*(K*P.N^ε*F) := by gcongr
    _ = (K*D^p*(Real.log P.N)^p)*P.N^ε*F := by rw [mul_pow]; ring
    _ ≤ P.N^ε*P.N^ε*F := by gcongr
    _ = _ := by rw [←Real.rpow_add hNp,show ε+ε=2*ε by ring]

#print axioms tail_endpoint_far_moment

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1400000 in
/-- The already proved analytic Heath--Brown pair absorbs the near part
at the order-dependent cutoff used in the mixed-cell argument. -/
theorem tail_endpoint_gram {k : ℕ} (hk : 4 ≤ k) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/(100000*(((k:ℝ)+2)*((k:ℝ)+1))^2) ∧
      ∃ C : ℝ, 4 ≤ C ∧ ∀ P : LargeValuePattern, C ≤ P.N →
      P.N^(1-1/(2*((k:ℝ)+2)*((k:ℝ)+1))-δ) ≤ P.V →
      (P.ordinates.card:ℝ)^2*P.V^2 ≤ (P.ordinates.card:ℝ)*P.N^(2+η)+
        8*P.N*tailFarKernelSum P
          (P.N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2)))) := by
  let n : ℝ := (k:ℝ)+2
  let σ : ℝ := 1-1/(2*n*(n-1))
  let κ : ℝ := 2/((n-1)^2*(n+2))
  let l : ℝ := 1-(3*n-2)/(n*(n-1)*(n+2))
  let a : ℝ := (k:ℝ)+2/n-1/(10000*n)
  let g : ℝ := κ/(10000*n)
  have hn : 0 < n := by dsimp only [n]; positivity
  have hnm : 0 < n-1 := by dsimp only [n]; linarith only [Nat.cast_nonneg (α:=ℝ) k]
  have hn2 : 0 < n+2 := by positivity
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hg : 0 < g := by dsimp only [g]; positivity
  have ha : 0 ≤ a := by
    have he : 2/n-1/(10000*n)=19999/(10000*n) := by field_simp; ring
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
    dsimp only [a]
    linarith only [hk0,show 0 < 19999/(10000*n) by positivity,he]
  have hbase : 1+l-κ+κ*a=2*σ-g := by
    have hkn : (k:ℝ)=n-2 := by dsimp only [n]; ring
    dsimp only [σ,l,κ,a,g]
    rw [hkn]
    field_simp
    ring
  let β : ℝ := min 1 (g/(8*(a+1)))
  let δ : ℝ := min (1/(100000*(n*(n-1))^2)) (g/8)
  have hβ : 0 < β := lt_min (by norm_num) (by positivity)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδle : δ ≤ g/8 := min_le_right _ _
  have hβa : β*(a+1) ≤ g/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*(a+1))).mp
      (show β ≤ g/(8*(a+1)) from min_le_right _ _)
    nlinarith only [hh]
  have hbudget : β+1+(a-1)*(κ+β)+(l+β) ≤ (σ-δ)*2 := by
    nlinarith only [hbase,hβa,hδle,hg]
  have hpair : ExponentPair κ l := by
    convert exponentPair_heathBrown (k:=k+2) (by omega) using 1 <;>
      dsimp only [κ,l,n] <;> push_cast <;> ring_nf
  obtain ⟨C₀,hC₀,hsource⟩ := tail_near_far_gram_source hpair hβ
  obtain ⟨C₁,hC₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (4*C₀*(2:ℝ)^(κ+β)) (by positivity) 0 hβ)
  obtain ⟨C₂,hC₂⟩ := Filter.eventually_atTop.mp
    (eventually_exponentPair_gram_diagonal hC₀ ha hη)
  have hδbound : δ ≤ 1/(100000*(((k:ℝ)+2)*((k:ℝ)+1))^2) := by
    convert (min_le_left (1/(100000*(n*(n-1))^2)) (g/8)) using 1
    dsimp only [n]
    ring_nf
  refine ⟨δ,hδ,hδbound,max 4 (max C₁ C₂),le_max_left _ _,?_⟩
  intro P hPN hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hN2 : 2 ≤ P.N := (by norm_num : (2:ℝ) ≤ 4).trans ((le_max_left _ _).trans hPN)
  have hV' : P.N^(σ-δ) ≤ P.V := by
    convert hV using 1
    dsimp only [σ,n]
    ring_nf
  have hc : 4*C₀*(2:ℝ)^(κ+β) ≤ P.N^β := by
    simpa only [pow_zero,mul_one] using
      hC₁ P.N ((le_max_left _ _).trans ((le_max_right _ _).trans hPN))
  have hratio : (2*P.N^a)/P.N=2*P.N^(a-1) := by
    rw [mul_div_assoc,Real.rpow_sub hNp a 1,Real.rpow_one]
  have hvalue : 4*P.N*(C₀*((2*P.N^a)/P.N)^(κ+β)*P.N^(l+β)) ≤ P.V^2 := by
    calc
      _ = (4*C₀*(2:ℝ)^(κ+β))*P.N^(1+(a-1)*(κ+β)+(l+β)) := by
        rw [hratio,Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNp.le _),
          ←Real.rpow_mul hNp.le,Real.rpow_add hNp (1+(a-1)*(κ+β)) (l+β),
          Real.rpow_add hNp 1 ((a-1)*(κ+β)),Real.rpow_one]
        ring
      _ ≤ P.N^β*P.N^(1+(a-1)*(κ+β)+(l+β)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = P.N^(β+1+(a-1)*(κ+β)+(l+β)) := by rw [←Real.rpow_add hNp]; congr 1; ring
      _ ≤ P.N^((σ-δ)*2) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hbudget
      _ ≤ P.V^2 := by
        rw [Real.rpow_mul hNp.le,Real.rpow_two]
        exact pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hV' 2
  have hdiag : 4*P.N*(2*P.N+4*Real.pi*C₀*P.N*
      (harmonic (Nat.ceil (2*P.N^a)) : ℝ)) ≤ P.N^(2+η) := by
    apply hC₂ P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN)) _ (by positivity)
    calc
      _ ≤ P.N*P.N^a := mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = _ := by rw [Real.rpow_add hNp,Real.rpow_one]; ring
  let R : ℝ := P.ordinates.card
  let D := 2*P.N+4*Real.pi*C₀*P.N*(harmonic (Nat.ceil (2*P.N^a)) : ℝ)
  let F := C₀*((2*P.N^a)/P.N)^(κ+β)*P.N^(l+β)
  have hg' : (R*P.V)^2 ≤ 2*P.N*(R*(D+R*F)+2*tailFarKernelSum P (P.N^a)) := by
    convert hsource P (P.N^a) (by positivity) using 1
    dsimp only [R,D,F]
    ring
  have hmul := mul_le_mul_of_nonneg_left hvalue (sq_nonneg R)
  have hd := mul_le_mul_of_nonneg_left hdiag (show 0 ≤ R by positivity)
  change R^2*P.V^2 ≤ R*P.N^(2+η)+8*P.N*tailFarKernelSum P (P.N^a)
  dsimp only [D,F] at hg'
  nlinarith only [hg',hmul,hd]

#print axioms tail_endpoint_gram

theorem tailCriticalOrder_cast (k : ℕ) :
    ((2*GafniTao.heathBrownCriticalMoment (k+2):ℕ):ℝ)=((k:ℝ)+2)*((k:ℝ)+1) := by
  unfold GafniTao.heathBrownCriticalMoment
  rw [Nat.cast_mul,Nat.cast_div
    (even_iff_two_dvd.mp (Nat.even_mul_pred_self (k+2))) (by norm_num : (2:ℝ) ≠ 0)]
  rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ k+2)]
  push_cast
  ring

theorem tailCutoff_bounds {k : ℕ} (hk : 4 ≤ k) :
    (k:ℝ) ≤ (k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2)) ∧
    (k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2)) < (k:ℝ)+1 := by
  have hkr : (4:ℝ) ≤ k := by exact_mod_cast hk
  have hn : 0 < (k:ℝ)+2 := by positivity
  have he : 2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))=19999/(10000*((k:ℝ)+2)) := by
    field_simp
    ring
  have hf : 2/((k:ℝ)+2) ≤ 1/3 := (div_le_iff₀ hn).mpr (by linarith only [hkr])
  constructor
  · linarith only [he,show 0 ≤ 19999/(10000*((k:ℝ)+2)) by positivity]
  · linarith only [hf,show 0 < 1/(10000*((k:ℝ)+2)) by positivity]

#print axioms tailCriticalOrder_cast
#print axioms tailCutoff_bounds

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2200000 in
/-- Original-pattern cardinality from the new far-correlation argument,
uniformly through the closed physical top height. -/
theorem tail_endpoint_card {k : ℕ} (hk : 4 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/(100000*(((k:ℝ)+2)*((k:ℝ)+1))^2) ∧
      ∃ C : ℝ, 4 ≤ C ∧ ∀ P : LargeValuePattern, C ≤ P.N →
      P.N^(1-1/(2*((k:ℝ)+2)*((k:ℝ)+1))-δ) ≤ P.V →
      P.N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))) ≤ P.T →
      P.T ≤ P.N^(k+1) →
      (P.ordinates.card:ℝ) ≤ P.N^(6/(5*((k:ℝ)+2)*((k:ℝ)+1))) := by
  let p := 2*GafniTao.heathBrownCriticalMoment (k+2)
  have hpc : (p:ℝ)=((k:ℝ)+2)*((k:ℝ)+1) := tailCriticalOrder_cast k
  have hp0 : 0 < (p:ℝ) := by rw [hpc]; positivity
  have hp2 : (2:ℝ) ≤ p := by
    rw [hpc]
    have hh : (4:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith only [hh,sq_nonneg (k:ℝ)]
  have hp : 2 ≤ p := by exact_mod_cast hp2
  let ε : ℝ := 1/(10000*(p:ℝ))
  let ρ : ℝ := 101/(100*(p:ℝ))
  let b : ℝ := 1/(100*(p:ℝ))
  let r : ℝ := 6/(5*(p:ℝ))
  let d : ℝ := 1/(100000*(p:ℝ)^2)
  let σ : ℝ := 1-1/(2*(p:ℝ))
  let v : ℝ := σ-d
  let a : ℝ := (k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hsigma : 1-1/(2*((k:ℝ)+2)*((k:ℝ)+1))=σ := by dsimp only [σ]; rw [hpc]; ring
  have hrho : 101/(100*((k:ℝ)+2)*((k:ℝ)+1))=ρ := by dsimp only [ρ]; rw [hpc]; ring
  have hrtarget : 6/(5*((k:ℝ)+2)*((k:ℝ)+1))=r := by dsimp only [r]; rw [hpc]; ring
  have hb : b ≤ 1/100 := by
    dsimp only [b]
    apply (div_le_iff₀ (by positivity : 0 < 100*(p:ℝ))).mpr
    linarith only [hp2]
  have hnearBudget : ρ+ε+b ≤ r := by
    dsimp only [ρ,ε,b,r]
    field_simp
    norm_num
  have hdiagBudget : 2+2*ε ≤ r+2*v := by
    dsimp only [ε,r,v,σ,d]
    field_simp
    nlinarith only [hp2]
  have hfinalBudget : 2*(p:ℝ)-1-b+3*ε < (2*v)*(p:ℝ) := by
    dsimp only [b,ε,v,σ,d]
    field_simp
    nlinarith only [hp0]
  obtain ⟨δ₀,hδ₀,hδ₀le,C₀,hC₀,hfar⟩ := tail_endpoint_far_moment hk hε
  obtain ⟨δ₁,hδ₁,_hδ₁le,C₁,_,hgram⟩ := tail_endpoint_gram hk hε
  obtain ⟨C₂,hC₂⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (2*16^p) (by positivity) 0 hε)
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hδdb : δ ≤ d := by
    apply hδle.trans
    dsimp only [d]
    rw [hpc]
    exact hδ₀le
  refine ⟨δ,hδ,hδle.trans hδ₀le,max C₀ (max C₁ C₂),hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hV hTlo hThi
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hN1 := P.one_lt_N.le
  have hV' : P.N^(σ-δ) ≤ P.V := by simpa only [hsigma] using hV
  have hv : P.N^v ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp only [v]; linarith only [hδdb])).trans hV'
  have hv2 : P.N^(2*v) ≤ P.V^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hv 2
    rw [←Real.rpow_mul_natCast hNp.le] at hh
    simpa only [Nat.cast_ofNat,mul_comm v (2:ℝ)] using hh
  have hv2p : P.N^((2*v)*(p:ℝ)) ≤ P.V^(2*p) := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hv (2*p)
    rw [←Real.rpow_mul_natCast hNp.le] at hh
    have he : v*((2*p:ℕ):ℝ)=(2*v)*(p:ℝ) := by push_cast; ring
    rw [he] at hh
    exact hh
  have hc : 2*16^p ≤ P.N^ε := by
    simpa only [pow_zero,mul_one] using
      hC₂ P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  have hc2 : 2 ≤ P.N^ε := by
    have hh : (1:ℝ) ≤ 16^p := one_le_pow₀ (by norm_num)
    exact (by linarith only [hh] : (2:ℝ) ≤ 2*16^p).trans hc
  let R : ℝ := P.ordinates.card
  let U := tailFarKernelSum P (P.N^a)
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rw [hrtarget]
  change R ≤ P.N^r
  by_contra hRbound
  have hR : P.N^r < R := lt_of_not_ge hRbound
  have hRp : 0 < R := (Real.rpow_pos_of_pos hNp _).trans hR
  have hd : 2*P.N^(2+ε) ≤ R*P.V^2 := by
    calc
      _ ≤ P.N^ε*P.N^(2+ε) := mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ = P.N^(2+2*ε) := by rw [←Real.rpow_add hNp]; congr 1; ring
      _ ≤ P.N^r*P.N^(2*v) := by
        rw [←Real.rpow_add hNp]
        exact Real.rpow_le_rpow_of_exponent_le hN1 hdiagBudget
      _ ≤ R*P.V^2 := mul_le_mul hR.le hv2 (by positivity) hR0
  have hg := hgram P ((le_max_left _ _).trans ((le_max_right _ _).trans hPN))
    (by
      rw [hsigma]
      exact (Real.rpow_le_rpow_of_exponent_le hN1
        (by have hh : δ ≤ δ₁ := min_le_right _ _; linarith only [hh])).trans hV')
  have hg' : R^2*P.V^2 ≤ 16*P.N*U := by
    change R^2*P.V^2 ≤ R*P.N^(2+ε)+8*P.N*U at hg
    have hh := mul_le_mul_of_nonneg_left hd hR0
    nlinarith only [hg,hh]
  have hLlo : P.N^k ≤ P.N^a := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (tailCutoff_bounds hk).1
  have hm := hfar P ((le_max_left _ _).trans hPN)
    (by
      rw [hsigma]
      exact (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδle])).trans hV')
    hThi (P.N^a) hLlo hTlo
  rw [hrho] at hm
  change U^p ≤ P.N^(2*ε)*
    (R^(2*p-1)*P.N^((p:ℝ)-1+ρ+ε)+R^(2*p)*P.N^((p:ℝ)-1-1/100)) at hm
  have hnear : R^(2*p-1)*P.N^((p:ℝ)-1+ρ+ε) ≤ R^(2*p)*P.N^((p:ℝ)-1-b) := by
    have hr : P.N^(ρ+ε+b) ≤ R :=
      (Real.rpow_le_rpow_of_exponent_le hN1 hnearBudget).trans hR.le
    calc
      _ = (R^(2*p-1)*P.N^((p:ℝ)-1-b))*P.N^(ρ+ε+b) := by
        rw [mul_assoc,←Real.rpow_add hNp]
        congr 2
        ring
      _ ≤ (R^(2*p-1)*P.N^((p:ℝ)-1-b))*R := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by
        rw [mul_right_comm,←pow_succ,show 2*p-1+1=2*p by omega]
  have hsecond : R^(2*p)*P.N^((p:ℝ)-1-1/100) ≤ R^(2*p)*P.N^((p:ℝ)-1-b) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hb])) (by positivity)
  have hm' : U^p ≤ 2*R^(2*p)*P.N^((p:ℝ)-1-b+2*ε) := by
    calc
      _ ≤ P.N^(2*ε)*(2*(R^(2*p)*P.N^((p:ℝ)-1-b))) :=
        hm.trans (mul_le_mul_of_nonneg_left (by linarith only [hnear,hsecond]) (by positivity))
      _ = _ := by
        calc
          _ = 2*R^(2*p)*(P.N^(2*ε)*P.N^((p:ℝ)-1-b)) := by ring
          _ = _ := by rw [←Real.rpow_add hNp]; congr 2; ring
  have hpGram := pow_le_pow_left₀ (mul_nonneg (sq_nonneg R) (sq_nonneg P.V)) hg' p
  have hp' : R^(2*p)*P.V^(2*p) ≤ 16^p*P.N^p*U^p := by
    simpa only [mul_pow,←pow_mul] using hpGram
  have hfinal : R^(2*p)*P.N^((2*v)*(p:ℝ)) ≤ R^(2*p)*P.N^(2*(p:ℝ)-1-b+3*ε) := by
    calc
      _ ≤ R^(2*p)*P.V^(2*p) := mul_le_mul_of_nonneg_left hv2p (by positivity)
      _ ≤ 16^p*P.N^p*U^p := hp'
      _ ≤ 16^p*P.N^p*(2*R^(2*p)*P.N^((p:ℝ)-1-b+2*ε)) :=
        mul_le_mul_of_nonneg_left hm' (by positivity)
      _ = (2*16^p)*R^(2*p)*P.N^(2*(p:ℝ)-1-b+2*ε) := by
        calc
          _ = (2*16^p)*R^(2*p)*(P.N^p*P.N^((p:ℝ)-1-b+2*ε)) := by ring
          _ = _ := by rw [←Real.rpow_natCast P.N p,←Real.rpow_add hNp]; congr 2; ring
      _ ≤ P.N^ε*R^(2*p)*P.N^(2*(p:ℝ)-1-b+2*ε) := by gcongr
      _ = _ := by
        calc
          _ = R^(2*p)*(P.N^ε*P.N^(2*(p:ℝ)-1-b+2*ε)) := by ring
          _ = _ := by rw [←Real.rpow_add hNp]; congr 2; ring
  have hh := (mul_le_mul_iff_right₀ (pow_pos hRp (2*p))).mp hfinal
  exact (not_le_of_gt (Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hfinalBudget)) hh

#print axioms tail_endpoint_card

/-- Genuine source-pattern subdivision preserves the closed top height;
the physical moment proof is used on every actual bin. -/
theorem tail_endpoint_largeValueBound_uniform {k : ℕ} (hk : 4 ≤ k) {τ : ℝ}
    (hτ : τ ≤ (k:ℝ)+1) :
    IsLargeValueBound (1-1/(2*((k:ℝ)+2)*((k:ℝ)+1))) τ
      (6/(5*((k:ℝ)+2)*((k:ℝ)+1))) := by
  intro ε hε
  obtain ⟨δ₀,hδ₀,_,C,hC,hcard⟩ := tail_endpoint_card hk
  let δ := min δ₀ (ε/2)
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hδε : δ ≤ ε/2 := min_le_right _ _
  refine ⟨C,(by linarith only [hC]),δ,hδ,?_⟩
  intro P hPN _hTlo hThi hVlo _hVhi
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  let L : ℝ := P.N^((k:ℝ)+1)
  let r : ℝ := 6/(5*((k:ℝ)+2)*((k:ℝ)+1))
  have hL : 0 < L := Real.rpow_pos_of_pos hNp _
  have hlocal (j : ℕ) : ((P.localized L hL j).ordinates.card:ℝ) ≤ P.N^r := by
    apply hcard (P.localized L hL j) hPN
    · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδle])).trans hVlo
    · change P.N^((k:ℝ)+2/((k:ℝ)+2)-1/(10000*((k:ℝ)+2))) ≤ L
      exact Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (tailCutoff_bounds hk).2.le
    · change L ≤ P.N^(k+1)
      rw [←Real.rpow_natCast]
      simp only [Nat.cast_add,Nat.cast_one]
      exact le_rfl
  have hratio : P.T/L ≤ P.N^δ := by
    calc
      _ ≤ P.N^(((k:ℝ)+1)+δ)/L := div_le_div_of_nonneg_right
        (hThi.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hτ]))) hL.le
      _ = _ := by
        dsimp only [L]
        rw [←Real.rpow_sub hNp]
        congr 1
        ring
  have hbins : ((Nat.floor (P.T/L)+1:ℕ):ℝ) ≤ 2*P.N^δ := by
    have hf := Nat.floor_le (div_nonneg P.T_pos.le hL.le)
    have h1 := Real.one_le_rpow P.one_lt_N.le hδ.le
    push_cast
    linarith only [hf,hratio,h1]
  calc
    _ ≤ ((Nat.floor (P.T/L)+1:ℕ):ℝ)*P.N^r :=
      P.card_le_of_localized hL _ (fun j _ => hlocal j)
    _ ≤ (2*P.N^δ)*P.N^r := mul_le_mul_of_nonneg_right hbins (by positivity)
    _ = 2*P.N^(r+δ) := by rw [mul_assoc,←Real.rpow_add hNp]; congr 2; ring
    _ ≤ C*P.N^(r+ε) := mul_le_mul (by linarith only [hC])
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδε,hε]))
      (by positivity) (by linarith only [hC])

#print axioms tail_endpoint_largeValueBound_uniform

/-- Uniform upper strip at the unchanged all-integer Pintz endpoints.
This is an original research strengthening, not the strict printed cell. -/
theorem pintz_tail_research_upper_exponent {n : ℕ} (hn : 6 ≤ n) {τ : ℝ}
    (hτlo : (n:ℝ)-2+2/(n:ℝ) ≤ τ) (hτhi : τ ≤ (n:ℝ)-1) :
    largeValueExponent (1-1/(2*(n:ℝ)*((n:ℝ)-1))) τ ≤
      ((3*τ/(2*(n:ℝ)*((n:ℝ)-1)^2):ℝ):EReal) := by
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith only [hnr]
  have hnm : 0 < (n:ℝ)-1 := by linarith only [hnr]
  have hcast : ((n-2:ℕ):ℝ)=(n:ℝ)-2 := by rw [Nat.cast_sub (by omega),Nat.cast_ofNat]
  have hb : IsLargeValueBound (1-1/(2*(n:ℝ)*((n:ℝ)-1))) τ (6/(5*(n:ℝ)*((n:ℝ)-1))) := by
    have hh := tail_endpoint_largeValueBound_uniform (k:=n-2) (by omega)
      (τ:=τ) (by rw [hcast]; linarith only [hτhi])
    convert hh using 1 <;> rw [hcast] <;> ring_nf
  apply (largeValueExponent_le_of_bound hb).trans
  apply EReal.coe_le_coe_iff.mpr
  apply (div_le_div_iff₀ (by positivity : 0 < 5*(n:ℝ)*((n:ℝ)-1))
    (by positivity : 0 < 2*(n:ℝ)*((n:ℝ)-1)^2)).mpr
  have ht : (n:ℝ)-2 ≤ τ := by
    linarith only [hτlo,show 0 < 2/(n:ℝ) by positivity]
  have hgap : 0 ≤ 15*τ-12*((n:ℝ)-1) := by linarith only [ht,hnr]
  have hh := mul_nonneg (show 0 ≤ (n:ℝ)*((n:ℝ)-1) by positivity) hgap
  nlinarith only [hh]

#print axioms pintz_tail_research_upper_exponent

theorem pintz_tail_research_exponent {n : ℕ} (hn : 6 ≤ n) {τ : ℝ}
    (hτlo : 2*((n:ℝ)-1)/3 ≤ τ) (hτhi : τ ≤ (n:ℝ)-1) :
    largeValueExponent (1-1/(2*(n:ℝ)*((n:ℝ)-1))) τ ≤
      ((3*τ/(2*(n:ℝ)*((n:ℝ)-1)^2):ℝ):EReal) := by
  by_cases hlow : τ < (n:ℝ)-2+2/(n:ℝ)
  · exact largeValueExponent_le_pintz_tail_endpoint_lower hn hτlo hlow
  · exact pintz_tail_research_upper_exponent hn (le_of_not_gt hlow) hτhi

#print axioms pintz_tail_research_exponent

/-- The frozen closed integer endpoint, proved by the new actual
far-correlation argument while preserving the audited source statement. -/
theorem pintz_tail_research_density {n : ℕ} (hn : 6 ≤ n) :
    zeroDensityExponent (1-1/(2*(n:ℝ)*((n:ℝ)-1))) ≤
      ((3/((n:ℝ)-1):ℝ):EReal) := by
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith only [hnr]
  have hnm : 0 < (n:ℝ)-1 := by linarith only [hnr]
  have hsmall : 1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ 1/60 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hnr,sq_nonneg ((n:ℝ)-6)])
  have hpos : 0 < 1/(2*(n:ℝ)*((n:ℝ)-1)) := by positivity
  have hh := zeroDensityExponent_le_of_two_thirds_largeValue_ranges
    (1-1/(2*(n:ℝ)*((n:ℝ)-1))) (3/(2*(n:ℝ)*((n:ℝ)-1)^2)) ((n:ℝ)-1)
    (by linarith only [hsmall]) (by linarith only [hpos]) (by positivity) hnm
  have he : (3/(2*(n:ℝ)*((n:ℝ)-1)^2))/(1-(1-1/(2*(n:ℝ)*((n:ℝ)-1))))=3/((n:ℝ)-1) := by
    field_simp
    ring
  rw [he] at hh
  apply hh
  · intro τ hτ
    rw [zetaLargeValueExponent_eq_bot_pintz_tail_endpoint hn hτ.1 hτ.2]
    exact bot_le
  · intro τ hτ
    rw [div_mul_eq_mul_div]
    exact pintz_tail_research_exponent hn hτ.1 hτ.2

#print axioms pintz_tail_research_density

/-- Exact closed-lower/open-upper tail cell of the frozen printed table. -/
theorem pintz_tail_research_cell {n : ℕ} {σ : ℝ} (hn : 6 ≤ n)
    (hleft : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ)
    (hright : σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1))) :
    zeroDensityExponent σ ≤
      ((3/((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))):ℝ):EReal) := by
  by_cases he : σ=1-1/(2*(n:ℝ)*((n:ℝ)-1))
  · subst σ
    have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
    have hnp : (0:ℝ) < n := by linarith only [hnr]
    have hnm : 0 < (n:ℝ)-1 := by linarith only [hnr]
    have hd : (n:ℝ)*(1-2*((n:ℝ)-1)*(1-(1-1/(2*(n:ℝ)*((n:ℝ)-1)))))=(n:ℝ)-1 := by
      field_simp
      ring
    rw [hd]
    exact pintz_tail_research_density hn
  · exact zeroDensityExponent_le_pintz_tail_interior hn
      (lt_of_le_of_ne hleft (Ne.symm he)) hright.le

#print axioms pintz_tail_research_cell

/-- Deterministic least index with the frozen CLOSED lower boundary.
This does not alter the separately preserved source-faithful index. -/
def printedTailIndex (σ : ℝ) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, 6 ≤ n ∧
      1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ ∧
      σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1)) then Nat.find h else 6

theorem printedTailIndex_spec {σ : ℝ}
    (hlo : 59/60 ≤ σ) (hhi : σ < 1) :
    6 ≤ printedTailIndex σ ∧
      1-1/(2*(printedTailIndex σ:ℝ)*((printedTailIndex σ:ℝ)-1)) ≤ σ ∧
      σ < 1-1/(2*(printedTailIndex σ:ℝ)*((printedTailIndex σ:ℝ)+1)) := by
  have he := LiteratureTable.exists_printed_tail_cell hlo hhi
  simp only [printedTailIndex,dif_pos he]
  exact Nat.find_spec he

#print axioms printedTailIndex_spec

/-- The unchanged printed finite table and its closed-lower integer tail.
The source-faithful substitute remains a different preserved definition. -/
def printedDensityTable (σ : ℝ) : ℝ :=
  if σ < 59/60 then LiteratureTable.printedFiniteDensityTable σ else
    3/((printedTailIndex σ:ℝ)*(1-2*((printedTailIndex σ:ℝ)-1)*(1-σ)))

/-- EPZAE-30: the entire frozen printed density envelope on [1/2,1),
including both finite endpoints and every integer-tail lower endpoint.
The disputed values use original research, not false source attribution. -/
theorem zeroDensityExponent_le_printedTable {σ : ℝ}
    (hlo : 1/2 ≤ σ) (hhi : σ < 1) :
    zeroDensityExponent σ ≤ ((printedDensityTable σ):EReal) := by
  unfold printedDensityTable
  split_ifs with hs
  · exact PintzFirstEndpointResearch.zeroDensityExponent_le_printedFinite hlo hs
  · obtain ⟨hn,hleft,hright⟩ := printedTailIndex_spec (le_of_not_gt hs) hhi
    exact pintz_tail_research_cell hn hleft hright

#print axioms zeroDensityExponent_le_printedTable

/-- The chosen index is the actual unique printed cell index. -/
theorem printedTailIndex_eq {n : ℕ} {σ : ℝ} (hn : 6 ≤ n)
    (hleft : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ)
    (hright : σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1))) :
    printedTailIndex σ = n := by
  classical
  have he : ∃ j : ℕ, 6 ≤ j ∧
      1-1/(2*(j:ℝ)*((j:ℝ)-1)) ≤ σ ∧
      σ < 1-1/(2*(j:ℝ)*((j:ℝ)+1)) := ⟨n,hn,hleft,hright⟩
  simp only [printedTailIndex,dif_pos he]
  apply (Nat.find_eq_iff he).mpr
  refine ⟨⟨hn,hleft,hright⟩,?_⟩
  intro m hmn hm
  have hmr : (6:ℝ) ≤ m := by exact_mod_cast hm.1
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hmnreal : (m:ℝ)+1 ≤ n := by exact_mod_cast hmn
  have hd : 0 < 2*(m:ℝ)*((m:ℝ)+1) := by positivity
  have hdd : 2*(m:ℝ)*((m:ℝ)+1) ≤ 2*(n:ℝ)*((n:ℝ)-1) := by
    nlinarith only [hmr,hnr,hmnreal,
      mul_nonneg (show 0 ≤ (n:ℝ)-(m:ℝ)-1 by linarith only [hmnreal])
        (show 0 ≤ (n:ℝ)+(m:ℝ) by linarith only [hmr,hnr])]
  have hi := one_div_le_one_div_of_le hd hdd
  linarith only [hm.2.2,hleft,hi]

#print axioms printedTailIndex_eq

theorem printedDensityTable_of_tail_cell {n : ℕ} {σ : ℝ}
    (hlo : 59/60 ≤ σ) (hn : 6 ≤ n)
    (hleft : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) ≤ σ)
    (hright : σ < 1-1/(2*(n:ℝ)*((n:ℝ)+1))) :
    printedDensityTable σ = 3/((n:ℝ)*(1-2*((n:ℝ)-1)*(1-σ))) := by
  rw [printedDensityTable,if_neg (not_lt.mpr hlo),printedTailIndex_eq hn hleft hright]

#print axioms printedDensityTable_of_tail_cell

/-- Every frozen integer endpoint has exactly its originally requested value. -/
theorem printedDensityTable_tail_lower {n : ℕ} (hn : 6 ≤ n) :
    printedDensityTable (1-1/(2*(n:ℝ)*((n:ℝ)-1)))=3/((n:ℝ)-1) := by
  have hnr : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith only [hnr]
  have hnm : 0 < (n:ℝ)-1 := by linarith only [hnr]
  have hd : (60:ℝ) ≤ 2*(n:ℝ)*((n:ℝ)-1) := by nlinarith only [hnr,sq_nonneg ((n:ℝ)-6)]
  have hlo : (59/60:ℝ) ≤ 1-1/(2*(n:ℝ)*((n:ℝ)-1)) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 60) hd
    linarith only [hh]
  have hright : 1-1/(2*(n:ℝ)*((n:ℝ)-1)) < 1-1/(2*(n:ℝ)*((n:ℝ)+1)) := by
    exact sub_lt_sub_left (one_div_lt_one_div_of_lt (by positivity)
      (by nlinarith only [hnp] : 2*(n:ℝ)*((n:ℝ)-1) < 2*(n:ℝ)*((n:ℝ)+1))) 1
  rw [printedDensityTable_of_tail_cell hlo hn le_rfl hright]
  field_simp [ne_of_gt hnp, ne_of_gt hnm]
  ring

#print axioms printedDensityTable_tail_lower









end
end TaoTrudgianYang2025.PintzTailCorrelationResearch

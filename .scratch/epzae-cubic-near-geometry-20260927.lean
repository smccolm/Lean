import TaoTrudgianYang2025.SquareProductCount

noncomputable section
open Set MeasureTheory GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025.CubicNearCurveGeometry

/-- The actual second-derivative difference has a signed derivative with
the correct displacement factor. -/
theorem cubic_second_difference_derivative
    (f : ℝ → ℝ) {x q B lam : ℝ} (hq : 0 < q)
    (hf : ∀ t∈Icc x (x+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc x (x+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) :
    HasDerivAt (fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2)
      ((iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2) x ∧
    -(B*q/2) ≤ (iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2 ∧
      (iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2 ≤ -(lam*q/2) := by
  have hxx : x ≤ x+q := by linarith
  have hd (t : ℝ) (ht : t∈Icc x (x+q)) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=3) (by norm_num : 3 < 4) (hf t ht)
  have hd₀ := hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 4)
    (hf x ⟨le_rfl,hxx⟩)
  have hd₁ := hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 4)
    (hf (x+q) ⟨hxx,le_rfl⟩)
  constructor
  · convert ((hd₁.comp x ((hasDerivAt_id x).add_const q)).sub hd₀).div_const 2 using 1; ring
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f)
    (iteratedDeriv 4 f) (show x < x+q by linarith)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' : iteratedDeriv 4 f t*q=iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x := by
    have hh := (eq_div_iff (show x+q-x ≠ 0 by linarith)).mp he
    nlinarith only [hh]
  have hlo := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩).1 hq.le
  have hhi := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩).2 hq.le
  constructor <;> nlinarith only [he',hlo,hhi]

/-- A near-resonant second derivative is moved to its exact integer
level inside the prescribed physical buffer. -/
theorem cubic_exact_second_difference_level
    (f : ℝ → ℝ) {n q B lam R δ K : ℝ}
    (hq : 0 < q) (hR : 0 < R)
    (hbudget : δ ≤ lam*q*R/2)
    (hf : ∀ t∈Icc (n-R) (n+R+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc (n-R) (n+R+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hnear : |(iteratedDeriv 2 f (n+q)-iteratedDeriv 2 f n)/2-K| ≤ δ) :
    ∃ x∈Icc (n-R) (n+R),
      (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=K ∧ |x-n| ≤ R := by
  let g := fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2
  let dg := fun t => (iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t)/2
  have hsub (x : ℝ) (hx : x∈Icc (n-R) (n+R)) :
      Icc x (x+q) ⊆ Icc (n-R) (n+R+q) := by
    intro t ht
    constructor <;> linarith [hx.1,hx.2,ht.1,ht.2]
  have hd (x : ℝ) (hx : x∈Icc (n-R) (n+R)) :
      HasDerivAt g (dg x) x ∧ dg x ≤ -(lam*q/2) := by
    have hh := cubic_second_difference_derivative f hq
      (fun t ht => hf t (hsub x hx ht)) (fun t ht => hfour t (hsub x hx ht))
    exact ⟨hh.1,hh.2.2⟩
  have hdec {a b : ℝ} (hab : a < b)
      (ha : n-R ≤ a) (hb : b ≤ n+R) :
      g b-g a ≤ -(lam*q/2)*(b-a) := by
    have hi (t : ℝ) (ht : t∈Icc a b) : t∈Icc (n-R) (n+R) :=
      ⟨ha.trans ht.1,ht.2.trans hb⟩
    obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope g dg hab
      (fun t ht => (hd t (hi t ht)).1.continuousAt.continuousWithinAt)
      (fun t ht => (hd t (hi t ⟨ht.1.le,ht.2.le⟩)).1)
    have he' := (eq_div_iff (sub_pos.mpr hab).ne').mp he
    have hh := mul_le_mul_of_nonneg_right (hd t (hi t ⟨ht.1.le,ht.2.le⟩)).2
      (sub_nonneg.mpr hab.le)
    nlinarith only [he',hh]
  have hleft := hdec (a:=n-R) (b:=n) (by linarith) le_rfl (by linarith)
  have hright := hdec (a:=n) (b:=n+R) (by linarith) (by linarith) le_rfl
  have hnear' : |g n-K| ≤ δ := hnear
  have hK : K∈Icc (g (n+R)) (g (n-R)) := by
    have hh := abs_le.mp hnear'
    constructor <;> nlinarith only [hleft,hright,hbudget,hh.1,hh.2]
  obtain ⟨x,hx,he⟩ := intermediate_value_Icc' (by linarith : n-R ≤ n+R)
    (fun t ht => (hd t ht).1.continuousAt.continuousWithinAt) hK
  exact ⟨x,hx,he,abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩⟩

/-- The exact level curve preserves the first-derivative integer
resonance up to a quadratic error, not a first-order displacement loss. -/
theorem cubic_stationary_curve_near_integer
    (f : ℝ → ℝ) (n K e : ℤ) {x q B lam R δ : ℝ}
    (hq : 0 < q) (hlam : 0 < lam) (hR : 0 ≤ R)
    (hx : x∈Icc ((n:ℝ)-R) ((n:ℝ)+R))
    (hf : ∀ t∈Icc ((n:ℝ)-R) ((n:ℝ)+R+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc ((n:ℝ)-R) ((n:ℝ)+R+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hlevel : (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=(K:ℝ))
    (hnear : |iteratedDeriv 1 f ((n:ℝ)+q)-iteratedDeriv 1 f n-(e:ℝ)| ≤ δ) :
    |(iteratedDeriv 1 f (x+q)-iteratedDeriv 1 f x-2*(K:ℝ)*x)-
      ((e-2*K*n:ℤ):ℝ)| ≤ δ+B*q*R^2 := by
  let G := fun t => iteratedDeriv 1 f (t+q)-iteratedDeriv 1 f t-2*(K:ℝ)*t
  let G₁ := fun t => iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t-2*(K:ℝ)
  let G₂ := fun t => iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t
  have hsub (t : ℝ) (ht : t∈uIcc x (n:ℝ)) : t∈Icc ((n:ℝ)-R) ((n:ℝ)+R) :=
    (convex_Icc _ _).ordConnected.uIcc_subset hx ⟨by linarith,by linarith⟩ ht
  have hseg (t : ℝ) (ht : t∈uIcc x (n:ℝ)) :
      Icc t (t+q) ⊆ Icc ((n:ℝ)-R) ((n:ℝ)+R+q) := by
    intro z hz
    have hh := hsub t ht
    constructor <;> linarith [hh.1,hh.2,hz.1,hz.2]
  have hjets (t : ℝ) (ht : t∈uIcc x (n:ℝ)) :
      HasDerivAt G (G₁ t) t ∧ HasDerivAt G₁ (G₂ t) t ∧ |G₂ t| ≤ B*q := by
    have hI := hseg t ht
    have ht₀ := hf t (hI ⟨le_rfl,by linarith⟩)
    have ht₁ := hf (t+q) (hI ⟨by linarith,le_rfl⟩)
    have hd (j : ℕ) (hj : j < 4) :
        HasDerivAt (fun z => iteratedDeriv j f (z+q)-iteratedDeriv j f z)
          (iteratedDeriv (j+1) f (t+q)-iteratedDeriv (j+1) f t) t := by
      have h₀ := hasDerivAt_iteratedDeriv_finite hj ht₀
      have h₁ := hasDerivAt_iteratedDeriv_finite hj ht₁
      convert (h₁.comp t ((hasDerivAt_id t).add_const q)).sub h₀ using 1; ring
    constructor
    · convert (hd 1 (by norm_num)).sub ((hasDerivAt_id t).const_mul (2*(K:ℝ))) using 1; ring
    constructor
    · exact (hd 2 (by norm_num)).sub_const (2*(K:ℝ))
    · have hh := cubic_second_difference_derivative f hq
        (fun z hz => hf z (hI hz)) (fun z hz => hfour z (hI hz))
      dsimp only [G₂]
      apply abs_le.mpr
      constructor <;> nlinarith [hh.2.1,hh.2.2,mul_pos hlam hq]
  have hB : 0 ≤ B := by
    have hh := hfour n ⟨by linarith,by linarith⟩
    linarith [hh.1,hh.2]
  have hG₁x : G₁ x=0 := by dsimp only [G₁]; linarith only [hlevel]
  have hdist : |(n:ℝ)-x| ≤ R := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2]
  have hfirst (t : ℝ) (ht : t∈uIcc x (n:ℝ)) : |G₁ t| ≤ B*q*R := by
    have hh := (convex_uIcc x (n:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hjets z hz).2.1.hasDerivWithinAt)
      (fun z hz => by simpa only [Real.norm_eq_abs] using (hjets z hz).2.2)
      left_mem_uIcc ht
    rw [hG₁x,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      ((abs_sub_left_of_mem_uIcc ht).trans hdist) (mul_nonneg hB hq.le))
  have herror := (convex_uIcc x (n:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hjets z hz).1.hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hfirst z hz)
    left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at herror
  have herror' : |G x-G n| ≤ B*q*R^2 := by
    rw [abs_sub_comm]
    exact herror.trans ((mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ B*q*R)).trans_eq (by ring))
  have hnear' : |G n-((e-2*K*n:ℤ):ℝ)| ≤ δ := by
    convert hnear using 1
    congr 1
    dsimp only [G]
    push_cast
    ring
  have hh := (abs_sub_le (G x) (G n) ((e-2*K*n:ℤ):ℝ)).trans (add_le_add herror' hnear')
  change |G x-((e-2*K*n:ℤ):ℝ)| ≤ _
  exact hh.trans_eq (by ring)

#print axioms cubic_second_difference_derivative
#print axioms cubic_exact_second_difference_level
#print axioms cubic_stationary_curve_near_integer

open SquareProductCount.CubicSource

/-- Integer resonances extracted from the actual source-label pair set.
The third coordinate is not reduced modulo integers. -/
theorem cubicDerivativePairs_integer_resonances
    (f : ℝ → ℝ) {M H : ℕ} {p : ℕ × ℕ}
    (hp : p∈cubicDerivativePairs f M H) :
    p.1 < M ∧ p.2 < M ∧
    ∃ e K : ℤ,
      |iteratedDeriv 1 f ((p.2:ℝ)+1)-iteratedDeriv 1 f ((p.1:ℝ)+1)-(e:ℝ)| ≤ 1/(4*(H:ℝ)) ∧
      |(iteratedDeriv 2 f ((p.2:ℝ)+1)-iteratedDeriv 2 f ((p.1:ℝ)+1))/2-(K:ℝ)| ≤
        1/(4*(H:ℝ)^2) ∧
      |iteratedDeriv 3 f ((p.2:ℝ)+1)-iteratedDeriv 3 f ((p.1:ℝ)+1)| ≤
        3/(2*(H:ℝ)^3) := by
  obtain ⟨hmem,hnear⟩ := Finset.mem_filter.mp hp
  have hmem' := Finset.mem_product.mp hmem
  refine ⟨Finset.mem_range.mp hmem'.1,Finset.mem_range.mp hmem'.2,
    ⌊deriv f ((p.2:ℝ)+1)⌋-⌊deriv f ((p.1:ℝ)+1)⌋,
    ⌊iteratedDeriv 2 f ((p.2:ℝ)+1)/2⌋-⌊iteratedDeriv 2 f ((p.1:ℝ)+1)/2⌋,
    ?_,?_,?_⟩
  · have hh := hnear 0
    change |Int.fract (deriv f ((p.1:ℝ)+1))-Int.fract (deriv f ((p.2:ℝ)+1))| ≤
      2*(1/(8*(H:ℝ))) at hh
    rw [abs_sub_comm] at hh
    convert hh using 1
    · congr 1
      simp only [Int.fract,Int.cast_sub,iteratedDeriv_one]
      ring
    · ring
  · have hh := hnear 1
    change |Int.fract (iteratedDeriv 2 f ((p.1:ℝ)+1)/2)-
      Int.fract (iteratedDeriv 2 f ((p.2:ℝ)+1)/2)| ≤ 2*(1/(8*(H:ℝ)^2)) at hh
    rw [abs_sub_comm] at hh
    convert hh using 1
    · congr 1
      simp only [Int.fract,Int.cast_sub]
      ring
    · ring
  · have hh := hnear 2
    change |iteratedDeriv 3 f ((p.1:ℝ)+1)/6-iteratedDeriv 3 f ((p.2:ℝ)+1)/6| ≤
      2*(1/(8*(H:ℝ)^3)) at hh
    rw [abs_sub_comm,←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<6)] at hh
    have he := (div_le_iff₀ (by norm_num : (0:ℝ)<6)).mp hh
    exact he.trans_eq (by ring)

/-- Fourth-derivative separation bounds the actual integer displacement. -/
theorem cubicDerivativePairs_displacement
    (f : ℝ → ℝ) {M H : ℕ} {p : ℕ × ℕ} {lam : ℝ}
    (hH : 1 ≤ H) (hlam : 0 < lam)
    (hp : p∈cubicDerivativePairs f M H) (hlt : p.1 < p.2)
    (hf : ∀ t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), iteratedDeriv 4 f t ≤ -lam) :
    (p.2:ℝ)-p.1 ≤ 3/(2*lam*(H:ℝ)^3) := by
  obtain ⟨_,_,e,K,_hfirst,_hsecond,hthird⟩ := cubicDerivativePairs_integer_resonances f hp
  have hHpos : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hxy : (p.1:ℝ)+1 < (p.2:ℝ)+1 := by exact_mod_cast Nat.add_lt_add_right hlt 1
  have hd (t : ℝ) (ht : t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1)) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=3) (by norm_num : 3 < 4) (hf t ht)
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f)
    (iteratedDeriv 4 f) hxy
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' := (eq_div_iff (sub_pos.mpr hxy).ne').mp he
  have hlow := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩) (sub_pos.mpr hxy).le
  have hprod : lam*((p.2:ℝ)-p.1) ≤ 3/(2*(H:ℝ)^3) := by
    have hab := abs_le.mp hthird
    nlinarith only [he',hlow,hab.1]
  have hh : (p.2:ℝ)-p.1 ≤ (3/(2*(H:ℝ)^3))/lam :=
    (le_div_iff₀ hlam).mpr (by nlinarith only [hprod])
  exact hh.trans_eq (by ring)

/-- Multiplicity of one exact displacement/level label; this controls
actual integer source points, including both closed endpoints. -/
theorem cubic_second_difference_fiber_card
    (f : ℝ → ℝ) (S : Finset ℤ) {a b q B lam δ K : ℝ}
    (hq : 0 < q) (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hf : ∀ t∈Icc a (b+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc a (b+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hS : ∀ n∈S, (n:ℝ)∈Icc a b)
    (hnear : ∀ n∈S, |(iteratedDeriv 2 f ((n:ℝ)+q)-iteratedDeriv 2 f n)/2-K| ≤ δ) :
    (S.card:ℝ) ≤ 4*δ/(lam*q)+1 := by
  classical
  by_cases hne : S.Nonempty
  · let n₀ := S.min' hne
    have hn₀ : n₀∈S := Finset.min'_mem S hne
    let g := fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2
    let dg := fun t => (iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t)/2
    have hd (t : ℝ) (ht : t∈Icc a b) : HasDerivAt g (dg t) t ∧ dg t ≤ -(lam*q/2) := by
      have hsub : Icc t (t+q) ⊆ Icc a (b+q) := by
        intro z hz
        constructor <;> linarith [ht.1,ht.2,hz.1,hz.2]
      have hh := cubic_second_difference_derivative f hq
        (fun z hz => hf z (hsub hz)) (fun z hz => hfour z (hsub hz))
      exact ⟨hh.1,hh.2.2⟩
    have hbound (n : ℤ) (hn : n∈S) :
        (n₀:ℝ) ≤ n ∧ (n:ℝ) ≤ n₀+4*δ/(lam*q) := by
      have hle : n₀ ≤ n := Finset.min'_le S n hn
      have hleR : (n₀:ℝ) ≤ n := by exact_mod_cast hle
      refine ⟨hleR,?_⟩
      rcases eq_or_lt_of_le hleR with heq|hlt
      · rw [←heq]
        exact le_add_of_nonneg_right (by positivity)
      have hsub (t : ℝ) (ht : t∈Icc (n₀:ℝ) n) : t∈Icc a b :=
        ⟨(hS n₀ hn₀).1.trans ht.1,ht.2.trans (hS n hn).2⟩
      obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope g dg hlt
        (fun t ht => (hd t (hsub t ht)).1.continuousAt.continuousWithinAt)
        (fun t ht => (hd t (hsub t ⟨ht.1.le,ht.2.le⟩)).1)
      have he' := (eq_div_iff (sub_pos.mpr hlt).ne').mp he
      have hdec := mul_le_mul_of_nonneg_right (hd t (hsub t ⟨ht.1.le,ht.2.le⟩)).2
        (sub_pos.mpr hlt).le
      have hnear₀ : |g n₀-K| ≤ δ := hnear n₀ hn₀
      have hnear₁ : |g n-K| ≤ δ := hnear n hn
      have hp : ((n:ℝ)-n₀)*(lam*q) ≤ 4*δ := by
        have hh₀ := abs_le.mp hnear₀
        have hh₁ := abs_le.mp hnear₁
        nlinarith only [he',hdec,hh₀.2,hh₁.1]
      have hh := (le_div_iff₀ (mul_pos hlam hq)).mpr hp
      linarith
    have hinterval : (n₀:ℝ) ≤ n₀+4*δ/(lam*q) :=
      le_add_of_nonneg_right (by positivity)
    have hcount := integer_card_le_interval_length_add_one S hinterval
      hbound
    exact hcount.trans_eq (by ring)
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms cubicDerivativePairs_integer_resonances
#print axioms cubicDerivativePairs_displacement
#print axioms cubic_second_difference_fiber_card

/-- In the short-source regime an off-diagonal integer second-derivative
level is positive. Its displacement is at least the reciprocal third-
derivative scale; this controls the exact-level buffer near the source edges. -/
theorem cubic_second_level_positive
    (f : ℝ → ℝ) (K : ℤ) {n q L U δ : ℝ}
    (hq : 1 ≤ q) (hL : 0 < L)
    (hδL : δ ≤ L/4) (hδhalf : δ ≤ 1/2)
    (hf : ∀ t∈Icc n (n+q), ContDiffAt ℝ 3 f t)
    (hthree : ∀ t∈Icc n (n+q),
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ U)
    (hnear : |(iteratedDeriv 2 f (n+q)-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ) :
    0 < K ∧ 0 < U ∧ 1/U ≤ q ∧ (K:ℝ) ≤ U*q := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hU : 0 < U := hL.trans_le ((hthree n ⟨le_rfl,by linarith⟩).1.trans
    (hthree n ⟨le_rfl,by linarith⟩).2)
  have hd (t : ℝ) (ht : t∈Icc n (n+q)) :
      HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 3) (hf t ht)
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 2 f)
    (iteratedDeriv 3 f) (show n < n+q by linarith)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' := (eq_div_iff (show n+q-n ≠ 0 by linarith)).mp he
  have hlo := mul_le_mul_of_nonneg_right (hthree t ⟨ht.1.le,ht.2.le⟩).1 hqpos.le
  have hhi := mul_le_mul_of_nonneg_right (hthree t ⟨ht.1.le,ht.2.le⟩).2 hqpos.le
  have hab := abs_le.mp hnear
  have hLq : L ≤ L*q := by nlinarith only [mul_le_mul_of_nonneg_left hq hL.le]
  have hKpos : (0:ℝ) < K := by nlinarith only [he',hlo,hab.2,hδL,hLq,hL]
  have hKi : 0 < K := by exact_mod_cast hKpos
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast (show (1:ℤ) ≤ K by omega)
  refine ⟨hKi,hU,?_,?_⟩
  · apply (div_le_iff₀ hU).mpr
    nlinarith only [he',hhi,hab.1,hδhalf,hK1]
  · have hLU : L ≤ U := (hthree t ⟨ht.1.le,ht.2.le⟩).1.trans
      (hthree t ⟨ht.1.le,ht.2.le⟩).2
    have hUq : U ≤ U*q := by nlinarith only [mul_le_mul_of_nonneg_left hq hU.le]
    nlinarith only [he',hhi,hab.1,hδL,hLU,hUq,hU]

-- The actual diagonal is retained for every source label.
example (f : ℝ → ℝ) {M H n : ℕ} (hH : 1 ≤ H) (hn : n < M) :
    (n,n)∈cubicDerivativePairs f M H := by
  unfold cubicDerivativePairs cubicSamplePairs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hn,Finset.mem_range.mpr hn⟩,?_⟩
  intro d
  simp only [sub_self,abs_zero]
  exact (mul_pos (by norm_num : (0:ℝ)<2) (cubicSamplingScale_pos hH d)).le

-- A zero-width level fiber has at most one integer source point.
example (f : ℝ → ℝ) (S : Finset ℤ) {a b q B lam K : ℝ}
    (hq : 0 < q) (hlam : 0 < lam)
    (hf : ∀ t∈Icc a (b+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc a (b+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hS : ∀ n∈S, (n:ℝ)∈Icc a b)
    (hlevel : ∀ n∈S, (iteratedDeriv 2 f ((n:ℝ)+q)-iteratedDeriv 2 f n)/2=K) :
    S.card ≤ 1 := by
  have hh := cubic_second_difference_fiber_card f S (K:=K) hq hlam (le_refl (0:ℝ))
    hf hfour hS (fun n hn => by rw [hlevel n hn]; simp)
  norm_num only [mul_zero,zero_div,zero_add] at hh
  exact_mod_cast hh

#print axioms cubic_second_level_positive

end TaoTrudgianYang2025.CubicNearCurveGeometry

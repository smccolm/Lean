import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff FourierTransform
namespace HuxleyIdentifiedWholeGridScratch

private theorem actual_reference_hull_order_bound
    (S : Finset ℝ) {H : ℤ} {δ scale : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ) (hscale : 0 < scale)
    (hhull : ∀ a∈S, ∀ b∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc a b → (q:ℝ)∈S)
    (henclose : ∃ l∈S, ∃ u∈S, l ≤ -scale ∧ scale ≤ u)
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ := by
  obtain ⟨l,hl,u,hu,hlow,hupp⟩ := henclose
  have hup : 0 < u := hscale.trans_le hupp
  have hlneg : l < 0 := hlow.trans_lt (neg_neg_of_pos hscale)
  have hHp : 0 < H := lt_of_lt_of_le (by decide : (0:ℤ)<1) hH
  have hHR : (0:ℝ) < H := by exact_mod_cast hHp
  have hzero : (0:ℝ)∈S := by
    exact_mod_cast hhull l hl u hu 0
      (by simpa only [Rat.den_zero,Int.natCast_one] using hH)
      (by simpa only [Rat.cast_zero] using (show (0:ℝ)∈Icc l u from ⟨hlneg.le,hup.le⟩))
  have huwide : δ/4 < u := by
    simpa only [sub_zero,abs_of_pos hup] using hsep u hu 0 hzero hup.ne'
  by_contra hnot
  have hbig : 4/δ ≤ (H:ℝ) := le_of_not_gt hnot
  have hrecip : (1:ℝ)/H ≤ δ/4 := by
    have hh := (div_le_iff₀ hδ).mp hbig
    apply (div_le_iff₀ hHR).mpr
    nlinarith only [hh]
  have hunit : (1:ℝ)/H∈S := by
    have hq := hhull 0 hzero u hu (Rat.divInt 1 H)
      (Int.le_of_dvd hHp (Rat.den_dvd 1 H))
      (by
        rw [Rat.cast_divInt,Int.cast_one]
        exact ⟨(one_div_pos.mpr hHR).le,hrecip.trans huwide.le⟩)
    simpa only [Rat.cast_divInt,Int.cast_one] using hq
  have hsmall := hsep _ hunit _ hzero (one_div_ne_zero hHR.ne')
  rw [sub_zero,abs_of_pos (one_div_pos.mpr hHR)] at hsmall
  exact (not_lt_of_ge hrecip) hsmall

private theorem actual_reference_hull_label_heights
    (S : Finset ℝ) {H : ℤ} {δ scale : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ) (hscale : 0 < scale)
    (hhull : ∀ a∈S, ∀ b∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc a b → (q:ℝ)∈S)
    (henclose : ∃ l∈S, ∃ u∈S, l ≤ -scale ∧ scale ≤ u)
    (hpoints : ∀ z∈S, |z| ≤ scale+1)
    (hlabels : ∀ z∈S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ (u:ℝ)/v∈S ∧ |m*v-u*n|=1))
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ ∧
    ∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
      (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ (scale+1)*(4/δ) := by
  have hHbound := actual_reference_hull_order_bound S hH hδ hscale hhull henclose hsep
  refine ⟨hHbound,?_⟩
  have hfinish (z : ℝ) (hz : z∈S) (m n : ℤ)
      (hval : z=(m:ℝ)/n) (hcop : IsCoprime m n) (hn : 0 < n)
      (hnb : (n:ℝ)<4/δ) :
      ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ (scale+1)*(4/δ) := by
    refine ⟨m,n,hval,hcop,hn,hnb,?_⟩
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hnum : (m:ℝ)=z*(n:ℝ) := (div_eq_iff hnR.ne').mp hval.symm
    rw [hnum,abs_mul,abs_of_pos hnR]
    exact mul_le_mul (hpoints z hz) hnb.le hnR.le (by linarith only [hscale])
  intro z hz
  rcases hlabels z hz with ⟨q,hval,hqH⟩ | ⟨m,n,u,v,hval,hcop,hn,hv,hu,hdet⟩
  · apply hfinish z hz q.num q.den
    · simpa only [Rat.cast_def,Int.cast_natCast] using hval
    · exact q.isCoprime_num_den
    · exact_mod_cast q.pos
    · exact (show (q.den:ℝ) ≤ H by exact_mod_cast hqH).trans_lt hHbound
  · exact hfinish z hz m n hval hcop hn
      (separated_reference_parent_denominator_bound S hδ hn hv
        (hval ▸ hz) hu hdet hsep).2


private theorem actual_reference_gap_oriented_chart
    (S : Finset ℝ) {H : ℤ} {R U scale a b : ℝ}
    (hR : 0 < R) (hU : 0 < U) (hscale : 0 ≤ scale)
    (hhull : ∀ x∈S, ∀ y∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc x y → (q:ℝ)∈S)
    (hpoints : ∀ z∈S, |z| ≤ scale+1)
    (hlabels : ∀ z∈S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ v ≤ H ∧ (u:ℝ)/v∈S ∧ |m*v-u*n|=1))
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → U/(4*R^2) < |x-y|)
    (ha : a∈S) (hb : b∈S) (hab : a < b)
    (hadj : ∀ z∈S, ¬(a < z ∧ z < b))
    (hends : ∃ m n p q : ℤ, a=(m:ℝ)/n ∧ b=(p:ℝ)/q ∧
      IsCoprime m n ∧ IsCoprime p q ∧ 0 < n ∧ 0 < q ∧
      R^2 ≤ U*((max n q:ℤ):ℝ)^2) :
    ∃ e r v s : ℤ, v*r-e*s=1 ∧
      ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
      s≠0 ∧ (e:ℝ)/r∈S ∧ (v:ℝ)/s∈S ∧ R^2 ≤ (r:ℝ)^2*U ∧
      |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
      |(e:ℝ)| ≤ (scale+1)*(4*R^2/U) ∧
      |(v:ℝ)| ≤ (scale+1)*(4*R^2/U) := by
  obtain ⟨m,n,p,q,haval,hbval,hcopn,hcopq,hn,hq,hmax⟩ := hends
  obtain ⟨e,r,f,s,hwhich,hrmax,_hcop,hr,hs,hsr,_hsH,hfS,hdet⟩ :=
    reference_max_denominator_neighbor S (L:=a) (U:=b)
      (fun q hqH hqI => hhull a ha b hb q hqH hqI) hlabels hn hq hcopn hcopq
      (by simpa only [←haval] using ha) (by simpa only [←hbval] using hb)
      (by rw [←haval]; exact ⟨le_rfl,hab.le⟩)
      (by rw [←hbval]; exact ⟨hab.le,le_rfl⟩)
      (by simpa only [←haval,←hbval] using hab)
      (by simpa only [←haval,←hbval] using hadj)
  have heval : (e:ℝ)/r=a ∨ (e:ℝ)/r=b := by
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl haval.symm
    · exact Or.inr hbval.symm
  have heS : (e:ℝ)/r∈S := heval.elim (fun he => he ▸ ha) (fun he => he ▸ hb)
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hsep' : ∀ x∈S, ∀ y∈S, x≠y → (U/R^2)/4 < |x-y| := by
    intro x hx y hy hne
    convert hsep x hx y hy hne using 1
    ring
  have hheight := (separated_reference_parent_denominator_bound S
    (div_pos hU (sq_pos_of_pos hR)) hr hs heS hfS hdet hsep').2
  have hbudget : 4/(U/R^2)=4*R^2/U := by field_simp
  rw [hbudget] at hheight
  have hsheight : (s:ℝ) < 4*R^2/U :=
    (show (s:ℝ) ≤ r by exact_mod_cast hsr).trans_lt hheight
  have hrscale : R^2 ≤ (r:ℝ)^2*U := by simpa only [hrmax,mul_comm U] using hmax
  have hsigned : ∃ e' r' : ℤ,
      ((0 < r' ∧ (e':ℝ)/r'=a) ∨ (r' < 0 ∧ (e':ℝ)/r'=b)) ∧
      (e':ℝ)/r'∈S ∧ R^2 ≤ (r':ℝ)^2*U ∧
      |(r':ℝ)| < 4*R^2/U ∧ |e'*s-f*r'|=1 := by
    rcases heval with he | he
    · exact ⟨e,r,Or.inl ⟨hr,he⟩,heS,hrscale,
        by simpa only [abs_of_pos hrR] using hheight,hdet⟩
    · refine ⟨-e,-r,Or.inr ⟨neg_neg_of_pos hr,?_⟩,?_,?_,?_,?_⟩
      · simpa only [Int.cast_neg,neg_div_neg_eq] using he
      · simpa only [Int.cast_neg,neg_div_neg_eq] using heS
      · simpa only [Int.cast_neg,neg_sq] using hrscale
      · simpa only [Int.cast_neg,abs_neg,abs_of_pos hrR] using hheight
      · have heq : -e*s-f*(-r)= -(e*s-f*r) := by ring
        rw [heq,abs_neg,hdet]
  obtain ⟨e',r',horient,he'S,hr'scale,hr'height,hdet'⟩ := hsigned
  let d : ℤ := f*r'-e'*s
  have hdabs : |d|=1 := by simpa only [d,abs_sub_comm] using hdet'
  have hdne : d≠0 := by intro hd; norm_num [hd] at hdabs
  have hdsq : d^2=1 := by
    calc
      _ = |d|^2 := (sq_abs d).symm
      _ = 1 := by rw [hdabs]; norm_num
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hdne
  have hdabsR : |(d:ℝ)|=1 := by exact_mod_cast hdabs
  have hneighbor : ((d*f:ℤ):ℝ)/(d*s:ℤ)=(f:ℝ)/s := by
    push_cast
    field_simp
  have hsheights : |((d*s:ℤ):ℝ)| < 4*R^2/U := by
    rw [Int.cast_mul,abs_mul,hdabsR,one_mul,abs_of_pos hsR]
    exact hsheight
  have hnum (u v : ℤ) (huS : (u:ℝ)/v∈S) (hvheight : |(v:ℝ)| < 4*R^2/U)
      (hv : v≠0) : |(u:ℝ)| ≤ (scale+1)*(4*R^2/U) := by
    have hvR : (v:ℝ)≠0 := by exact_mod_cast hv
    have heq : (u:ℝ)=((u:ℝ)/v)*v := (div_mul_cancel₀ _ hvR).symm
    rw [heq,abs_mul]
    exact mul_le_mul (hpoints _ huS) hvheight.le (abs_nonneg _) (by linarith only [hscale])
  have hr'ne : r'≠0 := horient.elim (fun h => h.1.ne') (fun h => h.1.ne)
  have hdsne : d*s≠0 := mul_ne_zero hdne hs.ne'
  have hdsS : ((d*f:ℤ):ℝ)/(d*s:ℤ)∈S := hneighbor ▸ hfS
  refine ⟨e',r',d*f,d*s,?_,horient,hdsne,he'S,hdsS,hr'scale,hr'height,hsheights,
    hnum e' r' he'S hr'height hr'ne,hnum (d*f) (d*s) hdsS hsheights hdsne⟩
  calc
    d*f*r'-e'*(d*s) = d^2 := by dsimp only [d]; ring
    _ = 1 := hdsq

/-- The actual whole-grid source witness retains derived reference heights
and oriented determinant-one charts, together with injective phase/block identification. No replacement reference system,
multiplicity bound or geometric disjointness certificate is assumed. -/
theorem positive_difference_constructed_reference_family_identified_source_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (Y : Finset ℝ)
      (N : ℕ) (s : ℤ) (H : ℝ → ℤ → ℕ)
      (η T M R U : ℝ),
      1 ≤ N → (∀ y∈Y, ∀ k, H y k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U → U ≤ R^2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ Href : ℤ, 2 ≤ Href ∧ (Href:ℝ)<4*R^2/U ∧ ∃ Refs : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ Href → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ Refs) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, ∀ q : ℚ, (q.den:ℤ) ≤ Href →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ Refs) ∧
      (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ Refs, |z| ≤ curvatureScale+1) ∧
      (∀ z∈Refs, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ Refs,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ Href) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ Href ∧ (u:ℝ)/v ∈ Refs ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ Refs, ∀ z ∈ Refs, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ Refs, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ Refs,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b →
        (∀ z ∈ Refs, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*U*N)) ∧
      (∀ a∈Refs, ∀ b∈Refs, a < b →
        (∀ z∈Refs, ¬(a < z ∧ z < b)) →
        ∃ e r v s : ℤ, v*r-e*s=1 ∧
          ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
          s≠0 ∧ (e:ℝ)/r∈Refs ∧ (v:ℝ)/s∈Refs ∧ R^2 ≤ (r:ℝ)^2*U ∧
          |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
          |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
          |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
    let V := (Y ×ˢ (Refs ×ˢ Refs)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈Refs, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let Gref := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ Gref).card ≤ 2*Y.card ∧ (Gref.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈Gref, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈Gref, ∀ j∈Gref, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gref,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i.1) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (x₁ i)) ((h i.1) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Gref.biUnion (fun i => (S i).image (fun k => (i,k)))
      Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (Sall : Set _) ∧
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : (ℝ × (ℝ × ℝ)) × ℤ → ℚ) (z : (ℝ × (ℝ × ℝ)) × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1.1) (m i)/6
      let ℓ := fun i => deriv (f i.1.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : (ℝ × (ℝ × ℝ)) × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gref.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gref.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(28*σ/c)*(N:ℝ)*U+4*(N:ℝ))
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gref.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gref.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) := by
  classical
  obtain ⟨C,hC,hsource⟩ :=
    positive_difference_constructed_reference_family_whole_grid_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro F Y N s H η T M R U hN hH hη hηmax hy hT hM hR hU hUmax
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    f h curvatureScale
  obtain ⟨Href,hHref,Refs,hseed,hhull,henclose,hpoints,hcurv,hlabels,hsep,hcover,hroots,hgaps,hrest⟩ :=
    hsource F Y N s H η T M R U hN hH hη hηmax hy hT hM hR hU hUmax
      hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
  have hscale : 0 < curvatureScale := by dsimp only [curvatureScale]; positivity
  have hsep' : ∀ x∈Refs, ∀ y∈Refs, x≠y → (U/R^2)/4 < |x-y| := by
    intro x hx y hy hne
    convert hsep x hx y hy hne using 1
    ring
  have hheights := actual_reference_hull_label_heights Refs
    (by omega : 1 ≤ Href) (div_pos hU (sq_pos_of_pos hR)) hscale hhull henclose hpoints
    (by
      intro z hz
      rcases hlabels z hz with hseed | ⟨m,n,u,v,hval,hcop,hn,_hnscale,hv,_hvH,hu,hdet⟩
      · exact Or.inl hseed
      · exact Or.inr ⟨m,n,u,v,hval,hcop,hn,hv,hu,hdet⟩)
    hsep'
  have hbudgetEq : 4/(U/R^2)=4*R^2/U := by field_simp
  rw [hbudgetEq] at hheights
  have hcharts : (∀ a∈Refs, ∀ b∈Refs, a < b →
        (∀ z∈Refs, ¬(a < z ∧ z < b)) →
        ∃ e r v s : ℤ, v*r-e*s=1 ∧
          ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
          s≠0 ∧ (e:ℝ)/r∈Refs ∧ (v:ℝ)/s∈Refs ∧ R^2 ≤ (r:ℝ)^2*U ∧
          |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
          |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
          |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) := by
    intro a ha b hb hab hadj
    apply actual_reference_gap_oriented_chart Refs hR hU hscale.le hhull hpoints
      (fun z hz => ?_) hsep ha hb hab hadj (hgaps a ha b hb hab hadj).2.2.1
    rcases hlabels z hz with hseed | ⟨m,n,u,v,hval,hcop,hn,_hnscale,hv,hvH,hu,hdet⟩
    · exact Or.inl hseed
    · exact Or.inr ⟨m,n,u,v,hval,hcop,hn,hv,hvH,hu,hdet⟩
  refine ⟨Href,hHref,hheights.1,Refs,hseed,hhull,henclose,hpoints,hheights.2,
    hcurv,hlabels,hsep,hcover,hroots,hgaps,hcharts,?_⟩
  intro V Gref
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,hgrid⟩ := hrest
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,?_⟩
  letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
  intro t L delta Vbound
  obtain ⟨S,anchor,za,hS,hforQ⟩ := hgrid
  refine ⟨S,anchor,za,hS,?_⟩
  intro Q hQ hQN Acut Bmajor hAcut hAQ hBmajor Sall
  have hmem p (hp : p∈Sall) : p.1∈Gref ∧ p.2∈S p.1 := by
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hpi
    exact ⟨hi,hk⟩
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hinj : Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (Sall : Set _) := by
    intro p hp q hq he
    have hpdata := hmem p hp
    have hqdata := hmem q hq
    have hpwindow := ((hS p.1 hpdata.1).1 p.2).mp hpdata.2
    have hqwindow := ((hS q.1 hqdata.1).1 q.2).mp hqdata.2
    have hk : p.2=q.2 := congrArg (fun i : ℝ × ℤ => i.2) he
    have hy : p.1.1=q.1.1 := congrArg (fun i : ℝ × ℤ => i.1) he
    by_cases hpq : p.1=q.1
    · exact Prod.ext hpq hk
    · have hd := hdisjoint p.1 hpdata.1 q.1 hqdata.1 hpq hy
      change x₁ p.1+(N:ℝ)/4 ≤ t p.2 ∧ t p.2 ≤ x₂ p.1-(N:ℝ)/4 at hpwindow
      change x₁ q.1+(N:ℝ)/4 ≤ t q.2 ∧ t q.2 ≤ x₂ q.1-(N:ℝ)/4 at hqwindow
      rw [hk] at hpwindow
      rcases hd with hd | hd
      all_goals linarith only [hpwindow.1,hpwindow.2,hqwindow.1,hqwindow.2,hd,hNp]
  exact ⟨hinj,hforQ Q hQ hQN Acut Bmajor hAcut hAQ hBmajor⟩

example
    (S : Finset ℝ) {H : ℤ} {R U scale a b : ℝ}
    (hR : 0 < R) (hU : 0 < U) (hscale : 0 ≤ scale)
    (hhull : ∀ x∈S, ∀ y∈S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
      (q:ℝ)∈Icc x y → (q:ℝ)∈S)
    (hpoints : ∀ z∈S, |z| ≤ scale+1)
    (hlabels : ∀ z∈S,
      (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
      (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
        0 < v ∧ v ≤ H ∧ (u:ℝ)/v∈S ∧ |m*v-u*n|=1))
    (hsep : ∀ x∈S, ∀ y∈S, x≠y → U/(4*R^2) < |x-y|)
    (ha : a∈S) (hb : b∈S) (hab : a < b)
    (hadj : ∀ z∈S, ¬(a < z ∧ z < b))
    (hends : ∃ m n p q : ℤ, a=(m:ℝ)/n ∧ b=(p:ℝ)/q ∧
      IsCoprime m n ∧ IsCoprime p q ∧ 0 < n ∧ 0 < q ∧
      R^2 ≤ U*((max n q:ℤ):ℝ)^2) :
    ∃ e r v s : ℤ, v*r-e*s=1 ∧
      ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
      s≠0 ∧ (e:ℝ)/r∈S ∧ (v:ℝ)/s∈S ∧ R^2 ≤ (r:ℝ)^2*U ∧
      |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
      |(e:ℝ)| ≤ (scale+1)*(4*R^2/U) ∧
      |(v:ℝ)| ≤ (scale+1)*(4*R^2/U) :=
  HuxleyIdentifiedWholeGridScratch.actual_reference_gap_oriented_chart S (H:=H) (R:=R) (U:=U) (scale:=scale) (a:=a) (b:=b) hR hU hscale hhull hpoints hlabels hsep ha hb hab hadj hends


example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (Y : Finset ℝ)
      (N : ℕ) (s : ℤ) (H : ℝ → ℤ → ℕ)
      (η T M R U : ℝ),
      1 ≤ N → (∀ y∈Y, ∀ k, H y k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ y∈Y, y∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U → U ≤ R^2 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ Href : ℤ, 2 ≤ Href ∧ (Href:ℝ)<4*R^2/U ∧ ∃ Refs : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ Href → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ Refs) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, ∀ q : ℚ, (q.den:ℤ) ≤ Href →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ Refs) ∧
      (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ Refs, |z| ≤ curvatureScale+1) ∧
      (∀ z∈Refs, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ Refs,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ Href) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ Href ∧ (u:ℝ)/v ∈ Refs ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ Refs, ∀ z ∈ Refs, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ Refs, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ Refs,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b →
        (∀ z ∈ Refs, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*U*N)) ∧
      (∀ a∈Refs, ∀ b∈Refs, a < b →
        (∀ z∈Refs, ¬(a < z ∧ z < b)) →
        ∃ e r v s : ℤ, v*r-e*s=1 ∧
          ((0 < r ∧ (e:ℝ)/r=a) ∨ (r < 0 ∧ (e:ℝ)/r=b)) ∧
          s≠0 ∧ (e:ℝ)/r∈Refs ∧ (v:ℝ)/s∈Refs ∧ R^2 ≤ (r:ℝ)^2*U ∧
          |(r:ℝ)| < 4*R^2/U ∧ |(s:ℝ)| < 4*R^2/U ∧
          |(e:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U) ∧
          |(v:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
    let V := (Y ×ˢ (Refs ×ˢ Refs)).filter (fun i =>
      i.2.1 < i.2.2 ∧ (∀ t∈Refs, ¬(i.2.1 < t ∧ t < i.2.2)) ∧
        i.2.1 < h i.1 (2*M) ∧ h i.1 M < i.2.2)
    let Gref := V.filter (fun i => h i.1 M ≤ i.2.1 ∧ i.2.2 ≤ h i.1 (2*M))
    (V.card:ℝ) ≤ ((12*J/σ)*M/(N*U)+2)*(Y.card:ℝ) ∧
    (V \ Gref).card ≤ 2*Y.card ∧ (Gref.image Prod.fst).card ≤ Y.card ∧
    ∃ x₁ x₂ : ℝ × (ℝ × ℝ) → ℝ,
      (∀ i∈Gref, x₁ i∈Icc M (2*M) ∧ x₂ i∈Icc M (2*M) ∧ x₁ i < x₂ i ∧
        h i.1 (x₁ i)=i.2.1 ∧ h i.1 (x₂ i)=i.2.2 ∧
        U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2)) ∧
      (∀ i∈Gref, ∀ j∈Gref, i≠j → i.1=j.1 → x₂ i ≤ x₁ j ∨ x₂ j ≤ x₁ i) ∧
      letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gref,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i.1) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (x₁ i)) ((h i.1) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i.1) (t k)-delta) ((h i.1) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      ∀ (Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 128*σ ≤ Bmajor →
      let Sall := Gref.biUnion (fun i => (S i).image (fun k => (i,k)))
      Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (Sall : Set _) ∧
      let Good := fun i => Acut*(anchor i.1 i.2).den ≤ Q ∧
        Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      let Dlow := Bmajor*R^2/(c*(Q:ℝ))
      let Khigh := Q/Acut+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Dlog := 64*σ*R^2/(c*((Q:ℝ)/Acut))
      let Cost := 4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ∃ (r : (ℝ × (ℝ × ℝ)) × ℤ → ℚ) (z : (ℝ × (ℝ × ℝ)) × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      (768 ≤ Acut → 24576*σ ≤ Bmajor →
        ∀ i∈G, 256*((anchor i.1 i.2).den:ℝ) ≤ (Q:ℝ)/3 ∧
          ∀ eps : ℝ, delta ≤ eps → 256 ≤ 2*eps*((Q:ℝ)/3)*(anchor i.1 i.2).den) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1.1) (m i)/6
      let ℓ := fun i => deriv (f i.1.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : (ℝ × (ℝ × ℝ)) × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
      let FourierCost :=
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))
      let Cerror := (Acut:ℝ)*((6*J/σ)*(64*σ/c)^2+192*σ/c)+
        ((3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c)
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gref.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gref.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(28*σ/c)*(N:ℝ)*U+4*(N:ℝ))
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gref.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gref.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) :=
  HuxleyIdentifiedWholeGridScratch.positive_difference_constructed_reference_family_identified_source_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ


#print axioms actual_reference_hull_order_bound
#print axioms actual_reference_hull_label_heights
#print axioms actual_reference_gap_oriented_chart
#print axioms positive_difference_constructed_reference_family_identified_source_fourier
end HuxleyIdentifiedWholeGridScratch

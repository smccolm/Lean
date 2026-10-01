import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff FourierTransform
namespace HuxleyBufferedWholeGridScratch
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

private theorem actual_tagged_grid_endpoint_trim
    {ι : Type*} (S : Finset (ι × ℤ)) (Y : Finset ℝ)
    (y x₁ x₂ : ι → ℝ) {M N s B C : ℝ}
    (hN : 0 < N) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hinj : Set.InjOn (fun i : ι × ℤ => (y i.1,i.2)) (S : Set _))
    (hy : ∀ i∈S, y i.1∈Y)
    (hgeometry : ∀ i∈S, M ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M ∧
      x₂ i.1-x₁ i.1 ≤ C*N)
    (hwindow : ∀ i∈S, x₁ i.1 ≤ s+N*(i.2:ℝ) ∧ s+N*(i.2:ℝ) ≤ x₂ i.1) :
    let Inner := S.filter (fun i => M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B)
    ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2+2*(B+C*N)/N) ∧
    (∀ i∈Inner, M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B) ∧
    ∀ (w : ι × ℤ → ℝ), (∀ i∈S, w i ≤ N) →
      (∑ i∈S, w i) ≤ (∑ i∈Inner, w i)+(Y.card:ℝ)*(2*N+2*B+2*C*N) := by
  classical
  intro Inner
  have hwidth : 0 ≤ B+C*N := add_nonneg hB (mul_nonneg hC hN.le)
  obtain ⟨Ileft,hIl,_hIll,hIlu⟩ := physical_grid_interval_card
    (N:=N) (Z:=s) (x:=M) (z:=M+B+C*N) hN (by linarith only [hwidth])
  obtain ⟨Iright,hIr,_hIrl,hIru⟩ := physical_grid_interval_card
    (N:=N) (Z:=s) (x:=2*M-B-C*N) (z:=2*M) hN (by linarith only [hwidth])
  have hcover : (S\Inner).card ≤ (Y ×ˢ (Ileft ∪ Iright)).card := by
    apply Finset.card_le_card_of_injOn (fun i : ι × ℤ => (y i.1,i.2))
    · intro i hi
      obtain ⟨hiS,hiNot⟩ := Finset.mem_sdiff.mp hi
      refine Finset.mem_product.mpr ⟨hy i hiS,?_⟩
      have hbad : ¬(M+B ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-B) := by
        intro hgood
        exact hiNot (Finset.mem_filter.mpr ⟨hiS,hgood⟩)
      have hg := hgeometry i hiS
      have hw := hwindow i hiS
      by_cases hl : M+B ≤ x₁ i.1
      · apply Finset.mem_union.mpr
        right
        apply (hIr i.2).mpr
        have hr : 2*M-B < x₂ i.1 := lt_of_not_ge (fun hr => hbad ⟨hl,hr⟩)
        constructor <;> nlinarith only [hg.1,hg.2.1,hg.2.2,hw.1,hw.2,hr]
      · apply Finset.mem_union.mpr
        left
        apply (hIl i.2).mpr
        have hl' : x₁ i.1 < M+B := lt_of_not_ge hl
        constructor <;> nlinarith only [hg.1,hg.2.1,hg.2.2,hw.1,hw.2,hl']
    · intro i hi j hj he
      exact hinj (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 he
  have hcount : ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2+2*(B+C*N)/N) := by
    have hc : ((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*((Ileft.card:ℝ)+(Iright.card:ℝ)) := by
      exact_mod_cast hcover.trans
        ((Finset.card_product Y (Ileft ∪ Iright)).le.trans
          (Nat.mul_le_mul_left Y.card (Finset.card_union_le Ileft Iright)))
    have hinterval : (Ileft.card:ℝ)+(Iright.card:ℝ) ≤ 2+2*(B+C*N)/N := by
      have hh := add_le_add hIlu hIru
      convert hh using 1
      ring
    exact hc.trans (mul_le_mul_of_nonneg_left hinterval (Nat.cast_nonneg _))
  refine ⟨hcount,(fun i hi => (Finset.mem_filter.mp hi).2),?_⟩
  intro w hw
  have hcost : (∑ i∈S\Inner, w i) ≤ N*((S\Inner).card:ℝ) := by
    calc
      _ ≤ ∑ _i∈S\Inner, N := Finset.sum_le_sum (fun i hi => hw i (Finset.mem_sdiff.mp hi).1)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
  have hphysical : N*((S\Inner).card:ℝ) ≤ (Y.card:ℝ)*(2*N+2*B+2*C*N) := by
    have hh := mul_le_mul_of_nonneg_left hcount hN.le
    convert hh using 1
    field_simp
    ring
  have hsplit : (∑ i∈Inner,w i)+(∑ i∈S\Inner,w i)=∑ i∈S,w i :=
    by simpa only [add_comm] using Finset.sum_sdiff (f:=w) (Finset.filter_subset _ _)
  linarith only [hcost,hphysical,hsplit]

private theorem source_integer_window_of_endpoint_buffer
    {M B D z : ℝ} (hB : D+2 ≤ B) (hz : z∈Ioo (M+B) (2*M-B)) :
    let A : ℤ := ⌈M⌉
    let W := 2*M-(A:ℝ)
    M ≤ (A:ℝ) ∧ (A:ℝ)+W=2*M ∧
    ∀ d : ℝ, |d| ≤ D → z-(A:ℝ)+d∈Ioo (1/2:ℝ) (W-1/2) := by
  intro A W
  have hceilLow : M ≤ (A:ℝ) := Int.le_ceil M
  have hceilHigh : (A:ℝ) < M+1 := Int.ceil_lt_add_one M
  refine ⟨hceilLow,by dsimp only [W]; ring,?_⟩
  intro d hd
  have hdb := abs_le.mp hd
  change (1/2:ℝ) < z-(A:ℝ)+d ∧ z-(A:ℝ)+d < 2*M-(A:ℝ)-1/2
  constructor <;> linarith only [hz.1,hz.2,hB,hdb.1,hdb.2,hceilHigh]

private theorem source_buffered_boundary_cost
    {σ c J M N U Y Buffer : ℝ} (hσ : 0 < σ) (hN : 0 < N) (hc : 0 < c) (hU : 0 < U) :
    N*(Y*((24*J/σ)*M/(N*U)+28*σ*U/c+4))+
      Y*(2*N+2*Buffer+2*((14*σ/c)*U)*N) =
      Y*((24*J/σ)*M/U+(56*σ/c)*N*U+6*N+2*Buffer) := by
  field_simp
  ring

/-- The actual reference family is trimmed by a physical endpoint buffer BEFORE
Fourier completion. All heights, orientations and source-block identification
are derived, and the original discarded sums have an explicit boundary cost. -/
theorem positive_difference_constructed_reference_family_buffered_source_fourier
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
      ∀ Buffer : ℝ, 0 ≤ Buffer →
      let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gcore,
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
      let Sall := Gcore.biUnion (fun i => (S i).image (fun k => (i,k)))
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
      (∀ i∈G, z i∈Ioo (M+Buffer) (2*M-Buffer)) ∧
      (∀ i∈G, ∀ d : ℝ, |d|+2 ≤ Buffer →
        z i-(⌈M⌉:ℤ)+d∈Ioo (1/2:ℝ) (2*M-(⌈M⌉:ℤ)-1/2)) ∧
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
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer)
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_tagged_gap_controlled_complement_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro F Y N s H η T M R U hN hH hη hηmax hy hT hM hR hU hUmax
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    f h curvatureScale
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨Href,hHref,Refs,hseed,hhull,henclose,hpoints,hcurv,hlabels,hsep,hcover,hroots,hgaps⟩ :=
    positive_difference_constructed_reference_system F hσ hc hJ hη hηmax hf hbound htests
      hnegative hT hM hNp hR hU hUmax hphase
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
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,hbudget⟩ :=
    positive_difference_reference_family_whole_grid_geometry F Y Refs
      hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hNp hR hU hphase
      (fun a ha b hb hne => (hsep a ha b hb hne).le)
      (fun a ha b hb hab hadj => (hgaps a ha b hb hab hadj).2.1)
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,?_⟩
  letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
  intro t L delta Vbound Buffer hBuffer Gcore
  have hcore : Gcore⊆Gref := Finset.filter_subset _ _
  have hyG i (hi : i∈Gref) : i.1∈Y := by
    have hh := Finset.mem_filter.mp hi
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hh.1).1).1
  obtain ⟨S,anchor,za,hS,hforQ⟩ := hentry (ℝ × (ℝ × ℝ)) Gcore F N s
    (fun i k => H i.1 k) η T M R U Prod.fst x₁ x₂
    hN (fun i hi => hH i.1 (hyG i (hcore hi))) hη hηmax (fun i hi => hy i.1 (hyG i (hcore hi)))
    hT hM hR hU hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    (fun i hi => (hgeometry i (hcore hi)).1) (fun i hi => (hgeometry i (hcore hi)).2.1)
    (fun i hi j hj hne he => hdisjoint i (hcore hi) j (hcore hj) hne he)
    (fun i hi => (hgeometry i (hcore hi)).2.2.2.2.2)
  have hencloseCurv y (hyY : y∈Y) : ∃ l∈Refs, ∃ u∈Refs, l ≤ h y M ∧ h y (2*M) ≤ u := by
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
    have hleft := abs_le.mp (hcurv y (hy y hyY) M ⟨le_rfl,by linarith only [hM]⟩)
    have hright := abs_le.mp (hcurv y (hy y hyY) (2*M) ⟨by linarith only [hM],le_rfl⟩)
    exact ⟨l,hl,u,hu,hlo.trans hleft.1,hright.2.trans hhi⟩
  have hidentify (D : Finset ((ℝ × (ℝ × ℝ)) × ℤ))
      (hD : ∀ i∈D, i.1∈Gref ∧
        x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4) :
      Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (D : Set _) := by
    intro p hp q hq he
    have hpdata := hD p hp
    have hqdata := hD q hq
    have hk : p.2=q.2 := congrArg (fun i : ℝ × ℤ => i.2) he
    have hy : p.1.1=q.1.1 := congrArg (fun i : ℝ × ℤ => i.1) he
    by_cases hpq : p.1=q.1
    · exact Prod.ext hpq hk
    · have hd := hdisjoint p.1 hpdata.1 q.1 hqdata.1 hpq hy
      rw [hk] at hpdata
      rcases hd with hd | hd
      all_goals linarith only [hpdata.2.1,hpdata.2.2,hqdata.2.1,hqdata.2.2,hd,hNp]
  have hgapwidth i (hi : i∈Gref) : x₂ i-x₁ i ≤ ((14*σ/c)*U)*(N:ℝ) := by
    have hg := hgeometry i hi
    have hgap : U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2) := hg.2.2.2.2.2
    have hpos : 0 ≤ U/(4*R^2) := by positivity
    have hh := positive_difference_reference_preimage_width F hσ hc hη hηmax
      (hy i.1 (hyG i hi)) hf hnegative hT hM hNp hR hphase hg.1 hg.2.1
      (show |h i.1 (x₂ i)-h i.1 (x₁ i)| ≤ 7*U/(2*R^2) from
        (by rw [abs_of_nonneg (hpos.trans hgap.1)]; exact hgap.2))
    exact (le_abs_self _).trans hh
  refine ⟨S,anchor,za,hS,?_⟩
  intro Q hQ hQN Acut Bmajor hAcut hAQ hBmajor Sall
  have hmem p (hp : p∈Sall) : p.1∈Gcore ∧ p.2∈S p.1 := by
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hpi
    exact ⟨hi,hk⟩
  refine ⟨hidentify Sall (fun i hi =>
    ⟨hcore (hmem i hi).1,((hS i.1 (hmem i hi).1).1 i.2).mp (hmem i hi).2⟩),?_⟩
  intro Good G Dlow Khigh Dhigh Dlog Cost
  have hfull (I : Finset ℤ) (hI : ∀ j∈I, t j∈Icc M (2*M)) :
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖)+
        (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer) := by
    let AllInner := (Gref ×ˢ I).filter (fun i =>
      x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4)
    let Retained := AllInner.filter (fun i => M+Buffer ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-Buffer)
    let w := fun i : (ℝ × (ℝ × ℝ)) × ℤ =>
      ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖
    have hdata i (hi : i∈AllInner) : i.1∈Gref ∧
        x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4 := by
      have hh := Finset.mem_filter.mp hi
      exact ⟨(Finset.mem_product.mp hh.1).1,hh.2⟩
    have htrim := (actual_tagged_grid_endpoint_trim AllInner Y Prod.fst x₁ x₂
      (M:=M) (N:=(N:ℝ)) (s:=(s:ℝ)) (B:=Buffer) (C:=(14*σ/c)*U)
      hNp hBuffer (by positivity) (hidentify AllInner hdata)
      (fun i hi => hyG i.1 (hdata i hi).1)
      (fun i hi => ⟨(hgeometry i.1 (hdata i hi).1).1.1,
        (hgeometry i.1 (hdata i hi).1).2.1.2,hgapwidth i.1 (hdata i hi).1⟩)
      (by
        intro i hi
        have hh := (hdata i hi).2
        change x₁ i.1 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1
        constructor <;> linarith only [hh.1,hh.2,hNp])).2.2 w (by
          intro i hi
          have hsum : w i ≤ H i.1.1 i.2 := by
            apply (norm_sum_le _ _).trans_eq
            simp
          exact hsum.trans (Nat.cast_le.mpr (hH i.1.1 (hyG i.1 (hdata i hi).1) i.2)))
    have hsub : Retained⊆Sall := by
      intro i hi
      have hh := Finset.mem_filter.mp hi
      have hd := hdata i hh.1
      have hiCore : i.1∈Gcore := Finset.mem_filter.mpr ⟨hd.1,hh.2⟩
      exact Finset.mem_biUnion.mpr ⟨i.1,hiCore,
        Finset.mem_image.mpr ⟨i.2,((hS i.1 hiCore).1 i.2).mpr hd.2,rfl⟩⟩
    have hsum : (∑ i∈Retained,w i) ≤ ∑ i∈Sall,w i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    have hgs := (hbudget (s:ℝ) I hI hencloseCurv).2 L H
      (fun y hyY j _ => Nat.cast_le.mpr (hH y hyY j))
    have he := source_buffered_boundary_cost (σ:=σ) (J:=J) (M:=M)
      (Y:=(Y.card:ℝ)) (Buffer:=Buffer) hσ hNp hc hU
    change (∑ i∈AllInner,w i) ≤ (∑ i∈Retained,w i)+_ at htrim
    change (∑ p∈Y ×ˢ I, _) ≤ (∑ i∈AllInner,w i)+_ at hgs
    change (∑ p∈Y ×ˢ I, _) ≤ (∑ i∈Sall,w i)+_
    linarith only [hgs,htrim,hsum,he]
  obtain ⟨r,z,hr,hzin,hdense,hround,hmodes⟩ := hforQ Q hQ hQN Acut Bmajor hAcut hAQ hBmajor
  have hzBuffer i (hi : i∈G) : z i∈Ioo (M+Buffer) (2*M-Buffer) := by
    have hc := (Finset.mem_filter.mp (hmem i (Finset.mem_filter.mp hi).1).1).2
    have hz := hzin i hi
    exact ⟨hc.1.trans_lt hz.1,hz.2.trans_le hc.2⟩
  refine ⟨r,z,hr,hzin,hzBuffer,?_,hdense,?_⟩
  · intro i hi d hd
    exact (source_integer_window_of_endpoint_buffer hd (hzBuffer i hi)).2.2 d le_rfl
  intro m A q μ ℓ U₃
  refine ⟨hround,?_⟩
  intro K₀ inst hK₀
  obtain ⟨v,hv,k,hraw,hnorm⟩ := hmodes K₀ hK₀
  refine ⟨v,hv,?_⟩
  intro b τ sPhase K x
  refine ⟨k,?_⟩
  intro FourierCost Cerror
  refine ⟨hraw,hnorm,?_⟩
  intro I hI BoundaryCost
  have hs := hfull I hI
  refine ⟨hs.trans (add_le_add hraw le_rfl),?_⟩
  intro hRQ hNR
  exact hs.trans (add_le_add (hnorm hRQ hNR) le_rfl)

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
      ∀ Buffer : ℝ, 0 ≤ Buffer →
      let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gcore,
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
      let Sall := Gcore.biUnion (fun i => (S i).image (fun k => (i,k)))
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
      (∀ i∈G, z i∈Ioo (M+Buffer) (2*M-Buffer)) ∧
      (∀ i∈G, ∀ d : ℝ, |d|+2 ≤ Buffer →
        z i-(⌈M⌉:ℤ)+d∈Ioo (1/2:ℝ) (2*M-(⌈M⌉:ℤ)-1/2)) ∧
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
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer)
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) :=
  HuxleyBufferedWholeGridScratch.positive_difference_constructed_reference_family_buffered_source_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ


#print axioms actual_reference_hull_order_bound
#print axioms actual_reference_hull_label_heights
#print axioms actual_reference_gap_oriented_chart
#print axioms actual_tagged_grid_endpoint_trim
#print axioms source_integer_window_of_endpoint_buffer
#print axioms source_buffered_boundary_cost
#print axioms positive_difference_constructed_reference_family_buffered_source_fourier
/-- One constructed reference system and its actual roots work for EVERY grid
origin and prefix-length family. The choice of references precedes those inputs. -/
theorem positive_difference_constructed_reference_family_uniform_grid_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (Y : Finset ℝ)
      (N : ℕ) (η T M R U : ℝ),
      1 ≤ N →
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
      ∀ (s : ℤ) (H : ℝ → ℤ → ℕ), (∀ y∈Y, ∀ k, H y k ≤ N) →
      letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∀ Buffer : ℝ, 0 ≤ Buffer →
      let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gcore,
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
      let Sall := Gcore.biUnion (fun i => (S i).image (fun k => (i,k)))
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
      (∀ i∈G, z i∈Ioo (M+Buffer) (2*M-Buffer)) ∧
      (∀ i∈G, ∀ d : ℝ, |d|+2 ≤ Buffer →
        z i-(⌈M⌉:ℤ)+d∈Ioo (1/2:ℝ) (2*M-(⌈M⌉:ℤ)-1/2)) ∧
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
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer)
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_tagged_gap_controlled_complement_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro F Y N η T M R U hN hη hηmax hy hT hM hR hU hUmax
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    f h curvatureScale
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨Href,hHref,Refs,hseed,hhull,henclose,hpoints,hcurv,hlabels,hsep,hcover,hroots,hgaps⟩ :=
    positive_difference_constructed_reference_system F hσ hc hJ hη hηmax hf hbound htests
      hnegative hT hM hNp hR hU hUmax hphase
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
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,hbudget⟩ :=
    positive_difference_reference_family_whole_grid_geometry F Y Refs
      hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hNp hR hU hphase
      (fun a ha b hb hne => (hsep a ha b hb hne).le)
      (fun a ha b hb hab hadj => (hgaps a ha b hb hab hadj).2.1)
  refine ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,?_⟩
  intro s H hH
  letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
  intro t L delta Vbound Buffer hBuffer Gcore
  have hcore : Gcore⊆Gref := Finset.filter_subset _ _
  have hyG i (hi : i∈Gref) : i.1∈Y := by
    have hh := Finset.mem_filter.mp hi
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hh.1).1).1
  obtain ⟨S,anchor,za,hS,hforQ⟩ := hentry (ℝ × (ℝ × ℝ)) Gcore F N s
    (fun i k => H i.1 k) η T M R U Prod.fst x₁ x₂
    hN (fun i hi => hH i.1 (hyG i (hcore hi))) hη hηmax (fun i hi => hy i.1 (hyG i (hcore hi)))
    hT hM hR hU hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    (fun i hi => (hgeometry i (hcore hi)).1) (fun i hi => (hgeometry i (hcore hi)).2.1)
    (fun i hi j hj hne he => hdisjoint i (hcore hi) j (hcore hj) hne he)
    (fun i hi => (hgeometry i (hcore hi)).2.2.2.2.2)
  have hencloseCurv y (hyY : y∈Y) : ∃ l∈Refs, ∃ u∈Refs, l ≤ h y M ∧ h y (2*M) ≤ u := by
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
    have hleft := abs_le.mp (hcurv y (hy y hyY) M ⟨le_rfl,by linarith only [hM]⟩)
    have hright := abs_le.mp (hcurv y (hy y hyY) (2*M) ⟨by linarith only [hM],le_rfl⟩)
    exact ⟨l,hl,u,hu,hlo.trans hleft.1,hright.2.trans hhi⟩
  have hidentify (D : Finset ((ℝ × (ℝ × ℝ)) × ℤ))
      (hD : ∀ i∈D, i.1∈Gref ∧
        x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4) :
      Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (D : Set _) := by
    intro p hp q hq he
    have hpdata := hD p hp
    have hqdata := hD q hq
    have hk : p.2=q.2 := congrArg (fun i : ℝ × ℤ => i.2) he
    have hy : p.1.1=q.1.1 := congrArg (fun i : ℝ × ℤ => i.1) he
    by_cases hpq : p.1=q.1
    · exact Prod.ext hpq hk
    · have hd := hdisjoint p.1 hpdata.1 q.1 hqdata.1 hpq hy
      rw [hk] at hpdata
      rcases hd with hd | hd
      all_goals linarith only [hpdata.2.1,hpdata.2.2,hqdata.2.1,hqdata.2.2,hd,hNp]
  have hgapwidth i (hi : i∈Gref) : x₂ i-x₁ i ≤ ((14*σ/c)*U)*(N:ℝ) := by
    have hg := hgeometry i hi
    have hgap : U/(4*R^2) ≤ h i.1 (x₂ i)-h i.1 (x₁ i) ∧
        h i.1 (x₂ i)-h i.1 (x₁ i) ≤ 7*U/(2*R^2) := hg.2.2.2.2.2
    have hpos : 0 ≤ U/(4*R^2) := by positivity
    have hh := positive_difference_reference_preimage_width F hσ hc hη hηmax
      (hy i.1 (hyG i hi)) hf hnegative hT hM hNp hR hphase hg.1 hg.2.1
      (show |h i.1 (x₂ i)-h i.1 (x₁ i)| ≤ 7*U/(2*R^2) from
        (by rw [abs_of_nonneg (hpos.trans hgap.1)]; exact hgap.2))
    exact (le_abs_self _).trans hh
  refine ⟨S,anchor,za,hS,?_⟩
  intro Q hQ hQN Acut Bmajor hAcut hAQ hBmajor Sall
  have hmem p (hp : p∈Sall) : p.1∈Gcore ∧ p.2∈S p.1 := by
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hpi
    exact ⟨hi,hk⟩
  refine ⟨hidentify Sall (fun i hi =>
    ⟨hcore (hmem i hi).1,((hS i.1 (hmem i hi).1).1 i.2).mp (hmem i hi).2⟩),?_⟩
  intro Good G Dlow Khigh Dhigh Dlog Cost
  have hfull (I : Finset ℤ) (hI : ∀ j∈I, t j∈Icc M (2*M)) :
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖)+
        (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer) := by
    let AllInner := (Gref ×ˢ I).filter (fun i =>
      x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4)
    let Retained := AllInner.filter (fun i => M+Buffer ≤ x₁ i.1 ∧ x₂ i.1 ≤ 2*M-Buffer)
    let w := fun i : (ℝ × (ℝ × ℝ)) × ℤ =>
      ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖
    have hdata i (hi : i∈AllInner) : i.1∈Gref ∧
        x₁ i.1+(N:ℝ)/4 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1-(N:ℝ)/4 := by
      have hh := Finset.mem_filter.mp hi
      exact ⟨(Finset.mem_product.mp hh.1).1,hh.2⟩
    have htrim := (actual_tagged_grid_endpoint_trim AllInner Y Prod.fst x₁ x₂
      (M:=M) (N:=(N:ℝ)) (s:=(s:ℝ)) (B:=Buffer) (C:=(14*σ/c)*U)
      hNp hBuffer (by positivity) (hidentify AllInner hdata)
      (fun i hi => hyG i.1 (hdata i hi).1)
      (fun i hi => ⟨(hgeometry i.1 (hdata i hi).1).1.1,
        (hgeometry i.1 (hdata i hi).1).2.1.2,hgapwidth i.1 (hdata i hi).1⟩)
      (by
        intro i hi
        have hh := (hdata i hi).2
        change x₁ i.1 ≤ t i.2 ∧ t i.2 ≤ x₂ i.1
        constructor <;> linarith only [hh.1,hh.2,hNp])).2.2 w (by
          intro i hi
          have hsum : w i ≤ H i.1.1 i.2 := by
            apply (norm_sum_le _ _).trans_eq
            simp
          exact hsum.trans (Nat.cast_le.mpr (hH i.1.1 (hyG i.1 (hdata i hi).1) i.2)))
    have hsub : Retained⊆Sall := by
      intro i hi
      have hh := Finset.mem_filter.mp hi
      have hd := hdata i hh.1
      have hiCore : i.1∈Gcore := Finset.mem_filter.mpr ⟨hd.1,hh.2⟩
      exact Finset.mem_biUnion.mpr ⟨i.1,hiCore,
        Finset.mem_image.mpr ⟨i.2,((hS i.1 hiCore).1 i.2).mpr hd.2,rfl⟩⟩
    have hsum : (∑ i∈Retained,w i) ≤ ∑ i∈Sall,w i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    have hgs := (hbudget (s:ℝ) I hI hencloseCurv).2 L H
      (fun y hyY j _ => Nat.cast_le.mpr (hH y hyY j))
    have he := source_buffered_boundary_cost (σ:=σ) (J:=J) (M:=M)
      (Y:=(Y.card:ℝ)) (Buffer:=Buffer) hσ hNp hc hU
    change (∑ i∈AllInner,w i) ≤ (∑ i∈Retained,w i)+_ at htrim
    change (∑ p∈Y ×ˢ I, _) ≤ (∑ i∈AllInner,w i)+_ at hgs
    change (∑ p∈Y ×ˢ I, _) ≤ (∑ i∈Sall,w i)+_
    linarith only [hgs,htrim,hsum,he]
  obtain ⟨r,z,hr,hzin,hdense,hround,hmodes⟩ := hforQ Q hQ hQN Acut Bmajor hAcut hAQ hBmajor
  have hzBuffer i (hi : i∈G) : z i∈Ioo (M+Buffer) (2*M-Buffer) := by
    have hc := (Finset.mem_filter.mp (hmem i (Finset.mem_filter.mp hi).1).1).2
    have hz := hzin i hi
    exact ⟨hc.1.trans_lt hz.1,hz.2.trans_le hc.2⟩
  refine ⟨r,z,hr,hzin,hzBuffer,?_,hdense,?_⟩
  · intro i hi d hd
    exact (source_integer_window_of_endpoint_buffer hd (hzBuffer i hi)).2.2 d le_rfl
  intro m A q μ ℓ U₃
  refine ⟨hround,?_⟩
  intro K₀ inst hK₀
  obtain ⟨v,hv,k,hraw,hnorm⟩ := hmodes K₀ hK₀
  refine ⟨v,hv,?_⟩
  intro b τ sPhase K x
  refine ⟨k,?_⟩
  intro FourierCost Cerror
  refine ⟨hraw,hnorm,?_⟩
  intro I hI BoundaryCost
  have hs := hfull I hI
  refine ⟨hs.trans (add_le_add hraw le_rfl),?_⟩
  intro hRQ hNR
  exact hs.trans (add_le_add (hnorm hRQ hNR) le_rfl)

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (Y : Finset ℝ)
      (N : ℕ) (η T M R U : ℝ),
      1 ≤ N →
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
      ∀ (s : ℤ) (H : ℝ → ℤ → ℕ), (∀ y∈Y, ∀ k, H y k ≤ N) →
      letI : DecidableEq (ℝ × (ℝ × ℝ)) := Classical.decEq _
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      ∀ Buffer : ℝ, 0 ≤ Buffer →
      let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gcore,
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
      let Sall := Gcore.biUnion (fun i => (S i).image (fun k => (i,k)))
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
      (∀ i∈G, z i∈Ioo (M+Buffer) (2*M-Buffer)) ∧
      (∀ i∈G, ∀ d : ℝ, |d|+2 ≤ Buffer →
        z i-(⌈M⌉:ℤ)+d∈Ioo (1/2:ℝ) (2*M-(⌈M⌉:ℤ)-1/2)) ∧
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
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer)
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) :=
  HuxleyBufferedWholeGridScratch.positive_difference_constructed_reference_family_uniform_grid_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ


#print axioms positive_difference_constructed_reference_family_uniform_grid_fourier

/-- The actual reference family is trimmed by a physical endpoint buffer BEFORE
Fourier completion. All heights, orientations and source-block identification
are derived, and the original discarded sums have an explicit boundary cost. -/
theorem positive_difference_uniform_grid_preserves_buffered_contract
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
      ∀ Buffer : ℝ, 0 ≤ Buffer →
      let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gcore,
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
      let Sall := Gcore.biUnion (fun i => (S i).image (fun k => (i,k)))
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
      (∀ i∈G, z i∈Ioo (M+Buffer) (2*M-Buffer)) ∧
      (∀ i∈G, ∀ d : ℝ, |d|+2 ≤ Buffer →
        z i-(⌈M⌉:ℤ)+d∈Ioo (1/2:ℝ) (2*M-(⌈M⌉:ℤ)-1/2)) ∧
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
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer)
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) := by
  obtain ⟨C,hC,hsource⟩ :=
    positive_difference_constructed_reference_family_uniform_grid_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro F Y N s H η T M R U hN hH hη hηmax hy hT hM hR hU hUmax
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
    f h curvatureScale
  obtain ⟨Href,hHref,hHrefHeight,Refs,hseed,hhull,henclose,hpoints,hheights,
    hcurv,hlabels,hsep,hcover,hroots,hgaps,hcharts,hrest⟩ :=
      hsource F Y N η T M R U hN hη hηmax hy hT hM hR hU hUmax
        hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge
  refine ⟨Href,hHref,hHrefHeight,Refs,hseed,hhull,henclose,hpoints,hheights,
    hcurv,hlabels,hsep,hcover,hroots,hgaps,hcharts,?_⟩
  intro V Gref
  obtain ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,hgrid⟩ := hrest
  exact ⟨hpack,hboundary,hphaseCount,x₁,x₂,hgeometry,hdisjoint,hgrid s H hH⟩

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
      ∀ Buffer : ℝ, 0 ≤ Buffer →
      let Gcore := Gref.filter (fun i => M+Buffer ≤ x₁ i ∧ x₂ i ≤ 2*M-Buffer)
      ∃ (S : (ℝ × (ℝ × ℝ)) → Finset ℤ) (anchor : (ℝ × (ℝ × ℝ)) → ℤ → ℚ) (za : (ℝ × (ℝ × ℝ)) → ℤ → ℝ),
        (∀ i∈Gcore,
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
      let Sall := Gcore.biUnion (fun i => (S i).image (fun k => (i,k)))
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
      (∀ i∈G, z i∈Ioo (M+Buffer) (2*M-Buffer)) ∧
      (∀ i∈G, ∀ d : ℝ, |d|+2 ≤ Buffer →
        z i-(⌈M⌉:ℤ)+d∈Ioo (1/2:ℝ) (2*M-(⌈M⌉:ℤ)-1/2)) ∧
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
      (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤ C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost) ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1.1 i.2),(𝐞 (f i.1.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)) ∧
      ∀ (I : Finset ℤ), (∀ j∈I, t j∈Icc M (2*M)) →
      let BoundaryCost := (Y.card:ℝ)*((24*J/σ)*M/U+(56*σ/c)*(N:ℝ)*U+6*(N:ℝ)+2*Buffer)
      (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
        C*(((Gcore.image Prod.fst).card:ℝ)*(N:ℝ)*Cost+FourierCost)+BoundaryCost ∧
      ((Acut:ℝ)*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
        (∑ p∈Y ×ˢ I, ‖∑ n∈Finset.Ioc (L p.2) (L p.2+H p.1 p.2),(𝐞 (f p.1 n):ℂ)‖) ≤
          C*(((Gcore.image Prod.fst).card:ℝ)*Cerror*(M*R/Q)*(2+Real.log (Dlog+1))+FourierCost)+BoundaryCost) :=
  HuxleyBufferedWholeGridScratch.positive_difference_uniform_grid_preserves_buffered_contract (σ:=σ) (c:=c) (J:=J) hσ hc hJ


#print axioms positive_difference_uniform_grid_preserves_buffered_contract

end HuxleyBufferedWholeGridScratch

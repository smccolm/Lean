import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff FourierTransform
namespace HuxleyBoundaryCoverScratch
private theorem two_probes_avoid_separated_set
    (S : Set ℝ) {x y radius spacing : ℝ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → spacing ≤ |a-b|)
    (hprobe : 2*radius < |x-y|)
    (hspan : |x-y|+2*radius < spacing) :
    (∀ a ∈ S, radius < |x-a|) ∨ (∀ a ∈ S, radius < |y-a|) := by
  classical
  by_contra hh
  obtain ⟨hx,hy⟩ := not_or.mp hh
  push Not at hx hy
  obtain ⟨a,ha,hxa⟩ := hx
  obtain ⟨b,hb,hyb⟩ := hy
  have hab : a = b := by
    by_contra hne
    have htriangle : |a-b| ≤ |x-a|+|x-y|+|y-b| := by
      calc
        |a-b| ≤ |a-x|+|x-b| := abs_sub_le _ _ _
        _ ≤ |a-x|+(|x-y|+|y-b|) := add_le_add le_rfl (abs_sub_le _ _ _)
        _ = _ := by rw [abs_sub_comm a x]; ring
    have hs := hsep a ha b hb hne
    linarith only [hs,htriangle,hxa,hyb,hspan]
  subst b
  have htriangle : |x-y| ≤ |x-a|+|y-a| := by
    simpa only [abs_sub_comm a y] using abs_sub_le x a y
  linarith only [htriangle,hprobe,hxa,hyb]

private theorem positive_difference_two_safe_block_starts
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hUlarge : 12*J ≤ σ*U) (hx : x ∈ Icc (M+3*N) (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    ((x-2*N) ∈ Icc M (2*M) ∧
      ∀ z ∈ Icc M (2*M), h z ∈ Refs → N/4 < |(x-2*N)-z|) ∨
    ((x-11*N/4) ∈ Icc M (2*M) ∧
      ∀ z ∈ Icc M (2*M), h z ∈ Refs → N/4 < |(x-11*N/4)-z|) := by
  intro f h
  have hwide w (hw : w ∈ Icc M (2*M)) : w ∈ Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hmono := positive_difference_physical_curvature_strictMono F
    hσ hc hη hηmax hy hreg hnegative hT hM
  change StrictMonoOn h (Icc (3*M/4) (9*M/4)) at hmono
  have hsize : 2 ≤ (σ/(6*J))*U := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 6*J)).mpr
    linarith only [hUlarge]
  let Roots : Set ℝ := {z | z ∈ Icc M (2*M) ∧ h z ∈ Refs}
  have hrootSep a (ha : a ∈ Roots) b (hb : b ∈ Roots) (hab : a ≠ b) :
      2*N ≤ |a-b| := by
    have hne : h b ≠ h a := fun he =>
      hab (hmono.injOn (hwide _ ha.1) (hwide _ hb.1) he.symm)
    have hg := hsep (h b) hb.2 (h a) ha.2 hne
    have hw := positive_difference_reference_preimage_width_lower F
      hσ hJ hη hηmax hy hreg hbound hT hM hN hR hscale
      (hwide _ ha.1) (hwide _ hb.1) hg
    calc
      2*N ≤ ((σ/(6*J))*U)*N := mul_le_mul_of_nonneg_right hsize hN.le
      _ ≤ |b-a| := hw
      _ = |a-b| := abs_sub_comm _ _
  have hdist : |(x-2*N)-(x-11*N/4)| = 3*N/4 := by
    rw [show (x-2*N)-(x-11*N/4) = 3*N/4 by ring,abs_of_nonneg (by positivity)]
  have havoid := two_probes_avoid_separated_set Roots
    (x:=x-2*N) (y:=x-11*N/4) (radius:=N/4) (spacing:=2*N) hrootSep
    (by rw [hdist]; linarith only [hN]) (by rw [hdist]; linarith only [hN])
  rcases havoid with hleft | hright
  · exact Or.inl ⟨⟨by linarith only [hx.1,hN],by linarith only [hx.2,hN]⟩,
      fun z hz hzref => hleft z ⟨hz,hzref⟩⟩
  · exact Or.inr ⟨⟨by linarith only [hx.1,hN],by linarith only [hx.2,hN]⟩,
      fun z hz hzref => hright z ⟨hz,hzref⟩⟩

private theorem coarse_boundary_exponent_floor
    {n r q u : ℝ} (hscale : n+2*r = 1/2) (hNR : n ≤ 2*r)
    (hRQ : r ≤ q) (hU : u ≤ (2/3:ℝ)*(n-q)) :
    (5/12:ℝ) ≤ 1/2-u ∧ (463/1140:ℝ) < 5/12 := by
  constructor
  · linarith only [hscale,hNR,hRQ,hU]
  · norm_num

example
    (S : Set ℝ) {x y radius spacing : ℝ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → spacing ≤ |a-b|)
    (hprobe : 2*radius < |x-y|)
    (hspan : |x-y|+2*radius < spacing) :
    (∀ a ∈ S, radius < |x-a|) ∨ (∀ a ∈ S, radius < |y-a|) :=
  HuxleyBoundaryCoverScratch.two_probes_avoid_separated_set S (x:=x) (y:=y) (radius:=radius) (spacing:=spacing) hsep hprobe hspan

example
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hUlarge : 12*J ≤ σ*U) (hx : x ∈ Icc (M+3*N) (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    ((x-2*N) ∈ Icc M (2*M) ∧
      ∀ z ∈ Icc M (2*M), h z ∈ Refs → N/4 < |(x-2*N)-z|) ∨
    ((x-11*N/4) ∈ Icc M (2*M) ∧
      ∀ z ∈ Icc M (2*M), h z ∈ Refs → N/4 < |(x-11*N/4)-z|) :=
  HuxleyBoundaryCoverScratch.positive_difference_two_safe_block_starts F Refs (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (x:=x) hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hN hR hscale hsep hUlarge hx

example
    {n r q u : ℝ} (hscale : n+2*r = 1/2) (hNR : n ≤ 2*r)
    (hRQ : r ≤ q) (hU : u ≤ (2/3:ℝ)*(n-q)) :
    (5/12:ℝ) ≤ 1/2-u ∧ (463/1140:ℝ) < 5/12 :=
  HuxleyBoundaryCoverScratch.coarse_boundary_exponent_floor (n:=n) (r:=r) (q:=q) (u:=u) hscale hNR hRQ hU


private theorem finite_reference_safe_start_buffered_bracket
    (S : Finset ℝ) (h : ℝ → ℝ) {M N Buffer D t : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hBuffer : 0 ≤ Buffer) (hD : 0 ≤ D)
    (hmono : StrictMonoOn h (Icc M (2*M)))
    (henclose : ∃ l ∈ S, ∃ u ∈ S, l ≤ h M ∧ h (2*M) ≤ u)
    (hroots : ∀ q ∈ S, q ∈ Icc (h M) (h (2*M)) →
      ∃ z ∈ Icc M (2*M), h z = q)
    (hwidth : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ q ∈ S,¬(a < q ∧ q < b)) →
      ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
        h x ∈ Icc a b → h z ∈ Icc a b → |z-x| ≤ D)
    (ht : t ∈ Icc (M+Buffer+D+N) (2*M-Buffer-D-N))
    (hsafe : ∀ z ∈ Icc M (2*M), h z ∈ S → N/4 < |t-z|) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ q ∈ S,¬(a < q ∧ q < b)) ∧
      ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
        h z₁ = a ∧ h z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
        z₁+N/4 ≤ t ∧ t ≤ z₂-N/4 := by
  have hleft : M ∈ Icc M (2*M) := ⟨le_rfl,by linarith only [hM]⟩
  have hright : 2*M ∈ Icc M (2*M) := ⟨by linarith only [hM],le_rfl⟩
  have htphys : t ∈ Icc M (2*M) :=
    ⟨by linarith only [ht.1,hBuffer,hD,hN],by linarith only [ht.2,hBuffer,hD,hN]⟩
  have hcurv : h t ∈ Icc (h M) (h (2*M)) :=
    ⟨hmono.monotoneOn hleft htphys htphys.1,hmono.monotoneOn htphys hright htphys.2⟩
  have htNot : h t∉S := by
    intro hh
    have hb := hsafe t htphys hh
    rw [sub_self,abs_zero] at hb
    linarith only [hb,hN]
  obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
  obtain ⟨a,ha,b,hb,hat,htb,hadj⟩ :=
    finite_reference_bracket S hl hu (hlo.trans hcurv.1) (hcurv.2.trans hhi) htNot
  have hab : a < b := hat.trans htb
  have haInner : h M ≤ a := by
    by_contra hnot
    have hma : a < h M := lt_of_not_ge hnot
    have hw := hwidth a ha b hb hab hadj M hleft t htphys
      ⟨hma.le,hcurv.1.trans htb.le⟩ ⟨hat.le,htb.le⟩
    have hx := (abs_le.mp hw).2
    linarith only [hx,ht.1,hBuffer,hN]
  have hbInner : b ≤ h (2*M) := by
    by_contra hnot
    have hmb : h (2*M) < b := lt_of_not_ge hnot
    have hw := hwidth a ha b hb hab hadj t htphys (2*M) hright
      ⟨hat.le,htb.le⟩ ⟨hat.le.trans hcurv.2,hmb.le⟩
    have hx := (abs_le.mp hw).2
    linarith only [hx,ht.2,hBuffer,hN]
  obtain ⟨z₁,hz₁,hza⟩ := hroots a ha ⟨haInner,hab.le.trans hbInner⟩
  obtain ⟨z₂,hz₂,hzb⟩ := hroots b hb ⟨haInner.trans hab.le,hbInner⟩
  have hz₁t : z₁ < t := by
    by_contra hnot
    have hh := hmono.monotoneOn htphys hz₁ (le_of_not_gt hnot)
    rw [hza] at hh
    exact (not_lt_of_ge hh) hat
  have htz₂ : t < z₂ := by
    by_contra hnot
    have hh := hmono.monotoneOn hz₂ htphys (le_of_not_gt hnot)
    rw [hzb] at hh
    exact (not_lt_of_ge hh) htb
  have hwleft := hwidth a ha b hb hab hadj z₁ hz₁ t htphys
    (by rw [hza]; exact ⟨le_rfl,hab.le⟩) ⟨hat.le,htb.le⟩
  have hwright := hwidth a ha b hb hab hadj t htphys z₂ hz₂
    ⟨hat.le,htb.le⟩ (by rw [hzb]; exact ⟨hab.le,le_rfl⟩)
  have hsleft := hsafe z₁ hz₁ (hza.symm ▸ ha)
  have hsright := hsafe z₂ hz₂ (hzb.symm ▸ hb)
  rw [abs_of_pos (sub_pos.mpr hz₁t)] at hsleft
  rw [abs_of_neg (sub_neg.mpr htz₂)] at hsright
  refine ⟨a,ha,b,hb,hab,hadj,z₁,z₂,hz₁,hz₂,hza,hzb,?_,?_,?_,?_⟩
  · have hh := (abs_le.mp hwleft).2
    linarith only [hh,ht.1,hN]
  · have hh := (abs_le.mp hwright).2
    linarith only [hh,ht.2,hN]
  · linarith only [hsleft]
  · linarith only [hsright]

example
    (S : Finset ℝ) (h : ℝ → ℝ) {M N Buffer D t : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hBuffer : 0 ≤ Buffer) (hD : 0 ≤ D)
    (hmono : StrictMonoOn h (Icc M (2*M)))
    (henclose : ∃ l ∈ S, ∃ u ∈ S, l ≤ h M ∧ h (2*M) ≤ u)
    (hroots : ∀ q ∈ S, q ∈ Icc (h M) (h (2*M)) →
      ∃ z ∈ Icc M (2*M), h z = q)
    (hwidth : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ q ∈ S,¬(a < q ∧ q < b)) →
      ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
        h x ∈ Icc a b → h z ∈ Icc a b → |z-x| ≤ D)
    (ht : t ∈ Icc (M+Buffer+D+N) (2*M-Buffer-D-N))
    (hsafe : ∀ z ∈ Icc M (2*M), h z ∈ S → N/4 < |t-z|) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ q ∈ S,¬(a < q ∧ q < b)) ∧
      ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
        h z₁ = a ∧ h z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
        z₁+N/4 ≤ t ∧ t ≤ z₂-N/4 :=
  HuxleyBoundaryCoverScratch.finite_reference_safe_start_buffered_bracket S h (M:=M) (N:=N) (Buffer:=Buffer) (D:=D) (t:=t) hM hN hBuffer hD hmono henclose hroots hwidth ht hsafe


private theorem positive_difference_two_buffered_block_starts
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U Buffer x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
      b-a ≤ 7*U/(2*R^2))
    (hUlarge : 12*J ≤ σ*U) (hBuffer : 0 ≤ Buffer) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let D := (14*σ/c)*U*N
    (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h M ∧ h (2*M) ≤ u) →
    (∀ q ∈ Refs, q ∈ Icc (h M) (h (2*M)) → ∃ z ∈ Icc M (2*M), h z = q) →
    x ∈ Icc (M+Buffer+D+4*N) (2*M-Buffer-D-N) →
    ∃ t : ℝ, (t = x-2*N ∨ t = x-11*N/4) ∧
      ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h z₁ = a ∧ h z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ t ∧ t ≤ z₂-N/4 := by
  intro f h D henclose hroots hx
  have hU : 0 < U := (div_pos (by positivity : 0 < 12*J) hσ).trans_le
    ((div_le_iff₀ hσ).mpr (by simpa only [mul_comm] using hUlarge))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hmono : StrictMonoOn h (Icc M (2*M)) := by
    apply (positive_difference_physical_curvature_strictMono F hσ hc hη hηmax hy
      hreg hnegative hT hM).mono
    intro w hw
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hwidth a (ha : a ∈ Refs) b (hb : b ∈ Refs) (hab : a < b)
      (hadj : ∀ q ∈ Refs,¬(a < q ∧ q < b))
      u (hu : u ∈ Icc M (2*M)) z (hz : z ∈ Icc M (2*M))
      (huc : h u ∈ Icc a b) (hzc : h z ∈ Icc a b) : |z-u| ≤ D := by
    apply positive_difference_reference_preimage_width F
      hσ hc hη hηmax hy hreg hnegative hT hM hN hR hscale hu hz
    change |h z-h u| ≤ 7*U/(2*R^2)
    apply (abs_le.mpr ?_).trans (hgap a ha b hb hab hadj)
    constructor <;> linarith only [huc.1,huc.2,hzc.1,hzc.2]
  have hsafe := positive_difference_two_safe_block_starts F Refs
    hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hN hR hscale hsep hUlarge
    (show x ∈ Icc (M+3*N) (2*M) from
      ⟨by linarith only [hx.1,hBuffer,hD,hN],by linarith only [hx.2,hBuffer,hD,hN]⟩)
  have hleft : x-2*N ∈ Icc (M+Buffer+D+N) (2*M-Buffer-D-N) :=
    ⟨by linarith only [hx.1,hN],by linarith only [hx.2,hN]⟩
  have hright : x-11*N/4 ∈ Icc (M+Buffer+D+N) (2*M-Buffer-D-N) :=
    ⟨by linarith only [hx.1,hN],by linarith only [hx.2,hN]⟩
  rcases hsafe with hgood | hgood
  · exact ⟨x-2*N,Or.inl rfl,
      finite_reference_safe_start_buffered_bracket Refs h hM hN hBuffer hD
        hmono henclose hroots hwidth hleft hgood.2⟩
  · exact ⟨x-11*N/4,Or.inr rfl,
      finite_reference_safe_start_buffered_bracket Refs h hM hN hBuffer hD
        hmono henclose hroots hwidth hright hgood.2⟩

example
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U Buffer x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
      b-a ≤ 7*U/(2*R^2))
    (hUlarge : 12*J ≤ σ*U) (hBuffer : 0 ≤ Buffer) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let D := (14*σ/c)*U*N
    (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h M ∧ h (2*M) ≤ u) →
    (∀ q ∈ Refs, q ∈ Icc (h M) (h (2*M)) → ∃ z ∈ Icc M (2*M), h z = q) →
    x ∈ Icc (M+Buffer+D+4*N) (2*M-Buffer-D-N) →
    ∃ t : ℝ, (t = x-2*N ∨ t = x-11*N/4) ∧
      ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h z₁ = a ∧ h z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ t ∧ t ≤ z₂-N/4 :=
  HuxleyBoundaryCoverScratch.positive_difference_two_buffered_block_starts F Refs (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (Buffer:=Buffer) (x:=x) hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hN hR hscale hsep hgap hUlarge hBuffer



private theorem finite_prefix_maximizers {α : Type*} (v : α → ℤ → ℂ) (N : ℕ) :
    ∃ H : α → ℤ → ℕ, ∀ y L, H y L ≤ N ∧
      ∀ h ≤ N, ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖ ≤
        ‖∑ k ∈ Finset.Ioc L (L+(H y L:ℤ)), v y k‖ := by
  classical
  have hex (y : α) (L : ℤ) : ∃ h ≤ N, ∀ t ≤ N,
      ‖∑ k ∈ Finset.Ioc L (L+(t:ℤ)), v y k‖ ≤
        ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖ := by
    obtain ⟨h,hh,hmax⟩ := (Finset.range (N+1)).exists_max_image
      (fun h => ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖)
      ⟨0,by simp⟩
    exact ⟨h,by simpa using hh,fun t ht => hmax t (by simpa using ht)⟩
  choose H hH using hex
  exact ⟨H,hH⟩

private theorem integer_subinterval_le_two_prefixes
    (v : ℤ → ℂ) {L A B : ℤ} {N : ℕ} {W : ℝ}
    (hLA : L ≤ A) (hAB : A ≤ B) (hBN : B ≤ L+(N:ℤ))
    (hprefix : ∀ h ≤ N, ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v k‖ ≤ W) :
    ‖∑ k ∈ Finset.Ioc A B, v k‖ ≤ 2*W := by
  have hsub : Finset.Ioc L A ⊆ Finset.Ioc L B := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk ⊢
    exact ⟨hk.1,hk.2.trans hAB⟩
  have hdiff : Finset.Ioc L B \ Finset.Ioc L A = Finset.Ioc A B := by
    ext k
    simp only [Finset.mem_sdiff,Finset.mem_Ioc]
    omega
  have hsum := Finset.sum_sdiff (f:=v) hsub
  rw [hdiff] at hsum
  have heq : (∑ k ∈ Finset.Ioc A B, v k) =
      (∑ k ∈ Finset.Ioc L B, v k)-(∑ k ∈ Finset.Ioc L A, v k) := by
    exact eq_sub_iff_add_eq.mpr hsum
  have hA : (A-L).toNat ≤ N := by omega
  have hB : (B-L).toNat ≤ N := by omega
  have ha := hprefix (A-L).toNat hA
  have hb := hprefix (B-L).toNat hB
  have hcastA : L+((A-L).toNat:ℤ) = A := by omega
  have hcastB : L+((B-L).toNat:ℤ) = B := by omega
  rw [hcastA] at ha
  rw [hcastB] at hb
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith only [ha,hb])

private theorem two_start_chunk_cover {α : Type*}
    (v : α → ℤ → ℂ) (C D : Finset (α × ℤ)) (n : ℕ)
    (H : α → ℤ → ℕ)
    (hprefix : ∀ y L, ∀ h ≤ 8*n,
      ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖ ≤
        ‖∑ k ∈ Finset.Ioc L (L+(H y L:ℤ)), v y k‖)
    (hcover : ∀ p ∈ C, p ∈ D ∨ (p.1,p.2-6) ∈ D) :
    (∑ p ∈ C, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)), v p.1 k‖) ≤
      4*∑ p ∈ D, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2)
        ((n:ℤ)*p.2+(H p.1 ((n:ℤ)*p.2):ℤ)), v p.1 k‖ := by
  classical
  let w (p : α × ℤ) := ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2)
    ((n:ℤ)*p.2+(H p.1 ((n:ℤ)*p.2):ℤ)), v p.1 k‖
  let f (p : α × ℤ) := ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2)
    ((n:ℤ)*(p.2+1)), v p.1 k‖
  let shift (p : α × ℤ) := (p.1,p.2-6)
  have hn : (0:ℤ) ≤ n := Int.natCast_nonneg n
  have hleft (p : α × ℤ) : f p ≤ 2*w p := by
    apply integer_subinterval_le_two_prefixes (v p.1) (N:=8*n) le_rfl
      (by nlinarith only [hn]) (by push_cast; nlinarith only [hn])
    exact hprefix p.1 ((n:ℤ)*p.2)
  have hright (p : α × ℤ) : f p ≤ 2*w (shift p) := by
    apply integer_subinterval_le_two_prefixes (v p.1) (L:=(n:ℤ)*(p.2-6)) (N:=8*n)
      (by nlinarith only [hn])
      (by nlinarith only [hn])
      (by push_cast; nlinarith only [hn])
    exact hprefix p.1 ((n:ℤ)*(p.2-6))
  have hw (p : α × ℤ) : 0 ≤ w p := norm_nonneg _
  let C₀ := C.filter (fun p => p ∈ D)
  let C₁ := C.filter (fun p => p ∉ D)
  have hsub₀ : C₀ ⊆ D := fun p hp => (Finset.mem_filter.mp hp).2
  have hsub₁ : C₁.image shift ⊆ D := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqC,hqD⟩ := Finset.mem_filter.mp hq
    exact (hcover q hqC).resolve_left hqD
  have hinj : Function.Injective shift := by
    intro p q heq
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    change p.1 = q.1 at hfirst
    change p.2-6 = q.2-6 at hsecond
    apply Prod.ext hfirst
    omega
  have hs₀ : (∑ p ∈ C₀, w p) ≤ ∑ p ∈ D, w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub₀ (fun p _ _ => hw p)
  have hs₁ : (∑ p ∈ C₁, w (shift p)) ≤ ∑ p ∈ D, w p := by
    rw [← Finset.sum_image hinj.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub₁ (fun p _ _ => hw p)
  have hsum₀ := Finset.sum_le_sum (fun p (_ : p ∈ C₀) => hleft p)
  have hsum₁ := Finset.sum_le_sum (fun p (_ : p ∈ C₁) => hright p)
  rw [← Finset.mul_sum] at hsum₀ hsum₁
  have hsplit : (∑ p ∈ C₀, f p)+(∑ p ∈ C₁, f p) = ∑ p ∈ C, f p :=
    Finset.sum_filter_add_sum_filter_not C (fun p => p ∈ D) f
  change (∑ p ∈ C, f p) ≤ 4*∑ p ∈ D, w p
  linarith only [hs₀,hs₁,hsum₀,hsum₁,hsplit]

example {α : Type*} (v : α → ℤ → ℂ) (N : ℕ) :
    ∃ H : α → ℤ → ℕ, ∀ y L, H y L ≤ N ∧
      ∀ h ≤ N, ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖ ≤
        ‖∑ k ∈ Finset.Ioc L (L+(H y L:ℤ)), v y k‖ :=
  HuxleyBoundaryCoverScratch.finite_prefix_maximizers (α:=α) v N

example
    (v : ℤ → ℂ) {L A B : ℤ} {N : ℕ} {W : ℝ}
    (hLA : L ≤ A) (hAB : A ≤ B) (hBN : B ≤ L+(N:ℤ))
    (hprefix : ∀ h ≤ N, ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v k‖ ≤ W) :
    ‖∑ k ∈ Finset.Ioc A B, v k‖ ≤ 2*W :=
  HuxleyBoundaryCoverScratch.integer_subinterval_le_two_prefixes v (L:=L) (A:=A) (B:=B) (N:=N) (W:=W) hLA hAB hBN hprefix

example {α : Type*}
    (v : α → ℤ → ℂ) (C D : Finset (α × ℤ)) (n : ℕ)
    (H : α → ℤ → ℕ)
    (hprefix : ∀ y L, ∀ h ≤ 8*n,
      ‖∑ k ∈ Finset.Ioc L (L+(h:ℤ)), v y k‖ ≤
        ‖∑ k ∈ Finset.Ioc L (L+(H y L:ℤ)), v y k‖)
    (hcover : ∀ p ∈ C, p ∈ D ∨ (p.1,p.2-6) ∈ D) :
    (∑ p ∈ C, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)), v p.1 k‖) ≤
      4*∑ p ∈ D, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2)
        ((n:ℤ)*p.2+(H p.1 ((n:ℤ)*p.2):ℤ)), v p.1 k‖ :=
  HuxleyBoundaryCoverScratch.two_start_chunk_cover (α:=α) v C D n H hprefix hcover



private theorem eight_grid_sum_reindex {α : Type*}
    (D : Finset (α × ℤ)) (w : α × ℤ → ℝ) :
    (∑ p ∈ D, w p) =
      ∑ r ∈ Finset.Ico (0:ℤ) 8,
        ∑ p ∈ (D.filter (fun p => p.2%8 = r)).image (fun p => (p.1,p.2/8-2)),
          w (p.1,r+8*p.2+16) := by
  classical
  have hmaps : ∀ p ∈ D, p.2%8 ∈ Finset.Ico (0:ℤ) 8 := by
    intro p _
    simp only [Finset.mem_Ico]
    exact ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps w]
  apply Finset.sum_congr rfl
  intro r _
  have hinj : Set.InjOn (fun p : α × ℤ => (p.1,p.2/8-2))
      ↑(D.filter (fun p => p.2%8 = r)) := by
    intro p hp q hq heq
    have hpmod := (Finset.mem_filter.mp hp).2
    have hqmod := (Finset.mem_filter.mp hq).2
    have hf := congrArg Prod.fst heq
    have hs := congrArg Prod.snd heq
    change p.1 = q.1 at hf
    change p.2/8-2 = q.2/8-2 at hs
    apply Prod.ext hf
    omega
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro p hp
  have hpmod := (Finset.mem_filter.mp hp).2
  have heq : r+8*(p.2/8-2)+16 = p.2 := by omega
  dsimp only
  rw [heq]

example {α : Type*}
    (D : Finset (α × ℤ)) (w : α × ℤ → ℝ) :
    (∑ p ∈ D, w p) =
      ∑ r ∈ Finset.Ico (0:ℤ) 8,
        ∑ p ∈ (D.filter (fun p => p.2%8 = r)).image (fun p => (p.1,p.2/8-2)),
          w (p.1,r+8*p.2+16) :=
  HuxleyBoundaryCoverScratch.eight_grid_sum_reindex (α:=α) D w



private theorem integer_chunk_partition (v : ℤ → ℂ) (n : ℕ)
    {a b : ℤ} (hab : a ≤ b) :
    (∑ m ∈ Finset.Ico a b, ∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k) =
      ∑ k ∈ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b), v k := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hab ih =>
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hab,ih]
    have hn : (0:ℤ) ≤ n := Int.natCast_nonneg n
    have h₁ : (n:ℤ)*a ≤ (n:ℤ)*b := mul_le_mul_of_nonneg_left hab hn
    have h₂ : (n:ℤ)*b ≤ (n:ℤ)*(b+1) := by nlinarith only [hn]
    have hdis : Disjoint (Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b))
        (Finset.Ioc ((n:ℤ)*b) ((n:ℤ)*(b+1))) := by
      apply Finset.disjoint_left.mpr
      intro k hk hl
      have hx := (Finset.mem_Ioc.mp hk).2
      have hy := (Finset.mem_Ioc.mp hl).1
      omega
    rw [← Finset.sum_union hdis,Finset.Ioc_union_Ioc_eq_Ioc h₁ h₂]

private theorem integer_whole_sum_le_chunks_and_endpoints
    (v : ℤ → ℂ) (n : ℕ) {A B a b : ℤ}
    (ha : A ≤ (n:ℤ)*a) (hab : a ≤ b) (hb : (n:ℤ)*b ≤ B)
    (hv : ∀ k ∈ Finset.Ioc A B, ‖v k‖ ≤ 1) :
    ‖∑ k ∈ Finset.Ioc A B, v k‖ ≤
      (∑ m ∈ Finset.Ico a b, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k‖)+
        (((n:ℤ)*a-A:ℤ):ℝ)+((B-(n:ℤ)*b:ℤ):ℝ) := by
  have hmiddle : (n:ℤ)*a ≤ (n:ℤ)*b :=
    mul_le_mul_of_nonneg_left hab (Int.natCast_nonneg n)
  have hsub : Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b) ⊆ Finset.Ioc A B := by
    intro k hk
    obtain ⟨hk₁,hk₂⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨ha.trans_lt hk₁,hk₂.trans hb⟩
  let S := Finset.Ioc A B \ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b)
  have hsum := Finset.sum_sdiff (f:=v) hsub
  have hnorm : ‖∑ k ∈ S, v k‖ ≤ (S.card:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      (∑ k ∈ S, ‖v k‖) ≤ ∑ _k ∈ S, (1:ℝ) := Finset.sum_le_sum
        (fun k hk => hv k (Finset.mem_sdiff.mp hk).1)
      _ = (S.card:ℝ) := by simp
  have hcount := Finset.card_sdiff_of_subset hsub
  have hcountZ : (S.card:ℤ) = ((n:ℤ)*a-A)+(B-(n:ℤ)*b) := by
    dsimp only [S]
    rw [hcount,Int.card_Ioc,Int.card_Ioc]
    omega
  have hcountR : (S.card:ℝ) = (((n:ℤ)*a-A:ℤ):ℝ)+((B-(n:ℤ)*b:ℤ):ℝ) := by
    exact_mod_cast hcountZ
  have hinner : ‖∑ k ∈ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b), v k‖ ≤
      ∑ m ∈ Finset.Ico a b, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k‖ := by
    rw [← integer_chunk_partition v n hab]
    exact norm_sum_le _ _
  rw [← hsum]
  have htriangle := norm_add_le (∑ k ∈ S,v k)
    (∑ k ∈ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b),v k)
  rw [hcountR] at hnorm
  linarith only [htriangle,hnorm,hinner]

example (v : ℤ → ℂ) (n : ℕ)
    {a b : ℤ} (hab : a ≤ b) :
    (∑ m ∈ Finset.Ico a b, ∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k) =
      ∑ k ∈ Finset.Ioc ((n:ℤ)*a) ((n:ℤ)*b), v k :=
  HuxleyBoundaryCoverScratch.integer_chunk_partition v n (a:=a) (b:=b) hab

example
    (v : ℤ → ℂ) (n : ℕ) {A B a b : ℤ}
    (ha : A ≤ (n:ℤ)*a) (hab : a ≤ b) (hb : (n:ℤ)*b ≤ B)
    (hv : ∀ k ∈ Finset.Ioc A B, ‖v k‖ ≤ 1) :
    ‖∑ k ∈ Finset.Ioc A B, v k‖ ≤
      (∑ m ∈ Finset.Ico a b, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*m) ((n:ℤ)*(m+1)), v k‖)+
        (((n:ℤ)*a-A:ℤ):ℝ)+((B-(n:ℤ)*b:ℤ):ℝ) :=
  HuxleyBoundaryCoverScratch.integer_whole_sum_le_chunks_and_endpoints v n (A:=A) (B:=B) (a:=a) (b:=b) ha hab hb hv



private theorem positive_difference_eight_grid_chunk_cover
    (F : ℝ → ℝ) (Y Refs : Finset ℝ) (n : ℕ)
    {σ c J η T M R U Buffer : ℝ}
    (hn : 0 < n) (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ k ≤ 6, |iteratedDeriv (k+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hscale : T*(8*(n:ℝ))*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
      b-a ≤ 7*U/(2*R^2))
    (hUlarge : 12*J ≤ σ*U) (hBuffer : 0 ≤ Buffer) :
    let N : ℝ := 8*n
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let Width := (14*σ/c)*U*N
    let Good : ℝ × ℤ → Prop := fun p =>
      ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ (n:ℝ)*p.2-2*N ∧ (n:ℝ)*p.2-2*N ≤ z₂-N/4
    (∀ y ∈ Y, ∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h y M ∧ h y (2*M) ≤ u) →
    (∀ y ∈ Y, ∀ q ∈ Refs, q ∈ Icc (h y M) (h y (2*M)) →
      ∃ z ∈ Icc M (2*M), h y z = q) →
    ∃ H : ℝ → ℤ → ℕ, (∀ y L, H y L ≤ 8*n) ∧
      ∀ C : Finset (ℝ × ℤ), (∀ p ∈ C, p.1 ∈ Y) →
        (∀ p ∈ C, (n:ℝ)*p.2 ∈ Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N)) →
      ∃ D : Finset (ℝ × ℤ),
        D ⊆ C ∪ C.image (fun p => (p.1,p.2-6)) ∧
        (∀ p ∈ D, Good p) ∧
        (∑ p ∈ C, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
          (𝐞 (f p.1 k):ℂ)‖) ≤
        4*∑ r ∈ Finset.Ico (0:ℤ) 8,
          ∑ p ∈ (D.filter (fun p => p.2%8 = r)).image (fun p => (p.1,p.2/8-2)),
            ‖∑ k ∈ Finset.Ioc ((n:ℤ)*(r+8*p.2+16))
              ((n:ℤ)*(r+8*p.2+16)+(H p.1 ((n:ℤ)*(r+8*p.2+16)):ℤ)),
                (𝐞 (f p.1 k):ℂ)‖ := by
  classical
  intro N f h Width Good henclose hroots
  let v : ℝ → ℤ → ℂ := fun y k => 𝐞 (f y k)
  obtain ⟨H,hH⟩ := finite_prefix_maximizers v (8*n)
  refine ⟨H,fun y L => (hH y L).1,?_⟩
  intro C hCY hdeep
  let shift : ℝ × ℤ → ℝ × ℤ := fun p => (p.1,p.2-6)
  let D := (C ∪ C.image shift).filter Good
  have hNp : 0 < N := by dsimp only [N]; positivity
  have hsafe p (hp : p ∈ C) : Good p ∨ Good (shift p) := by
    obtain ⟨t,ht,hdata⟩ := positive_difference_two_buffered_block_starts F Refs
      hσ hc hJ hη hηmax (hy p.1 (hCY p hp)) hreg hbound hnegative
      hT hM hNp hR hscale hsep hgap hUlarge hBuffer
      (henclose p.1 (hCY p hp)) (hroots p.1 (hCY p hp)) (hdeep p hp)
    rcases ht with ht | ht
    · subst t
      exact Or.inl hdata
    · subst t
      right
      change ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ (n:ℝ)*(p.2-6:ℤ)-2*N ∧
            (n:ℝ)*(p.2-6:ℤ)-2*N ≤ z₂-N/4
      have hshift : (n:ℝ)*(p.2-6:ℤ)-2*N = (n:ℝ)*p.2-11*N/4 := by
        push_cast
        dsimp only [N]
        ring
      rw [hshift]
      exact hdata
  have hcover p (hp : p ∈ C) : p ∈ D ∨ (p.1,p.2-6) ∈ D := by
    rcases hsafe p hp with hh | hh
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hp,hh⟩)
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩),hh⟩)
  refine ⟨D,Finset.filter_subset _ _,fun p hp => (Finset.mem_filter.mp hp).2,?_⟩
  have hsum := two_start_chunk_cover v C D n H (fun y L => (hH y L).2) hcover
  rw [eight_grid_sum_reindex D] at hsum
  exact hsum

example
    (F : ℝ → ℝ) (Y Refs : Finset ℝ) (n : ℕ)
    {σ c J η T M R U Buffer : ℝ}
    (hn : 0 < n) (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ k ≤ 6, |iteratedDeriv (k+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hscale : T*(8*(n:ℝ))*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
      b-a ≤ 7*U/(2*R^2))
    (hUlarge : 12*J ≤ σ*U) (hBuffer : 0 ≤ Buffer) :
    let N : ℝ := 8*n
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let Width := (14*σ/c)*U*N
    let Good : ℝ × ℤ → Prop := fun p =>
      ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ (n:ℝ)*p.2-2*N ∧ (n:ℝ)*p.2-2*N ≤ z₂-N/4
    (∀ y ∈ Y, ∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h y M ∧ h y (2*M) ≤ u) →
    (∀ y ∈ Y, ∀ q ∈ Refs, q ∈ Icc (h y M) (h y (2*M)) →
      ∃ z ∈ Icc M (2*M), h y z = q) →
    ∃ H : ℝ → ℤ → ℕ, (∀ y L, H y L ≤ 8*n) ∧
      ∀ C : Finset (ℝ × ℤ), (∀ p ∈ C, p.1 ∈ Y) →
        (∀ p ∈ C, (n:ℝ)*p.2 ∈ Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N)) →
      ∃ D : Finset (ℝ × ℤ),
        D ⊆ C ∪ C.image (fun p => (p.1,p.2-6)) ∧
        (∀ p ∈ D, Good p) ∧
        (∑ p ∈ C, ‖∑ k ∈ Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
          (𝐞 (f p.1 k):ℂ)‖) ≤
        4*∑ r ∈ Finset.Ico (0:ℤ) 8,
          ∑ p ∈ (D.filter (fun p => p.2%8 = r)).image (fun p => (p.1,p.2/8-2)),
            ‖∑ k ∈ Finset.Ioc ((n:ℤ)*(r+8*p.2+16))
              ((n:ℤ)*(r+8*p.2+16)+(H p.1 ((n:ℤ)*(r+8*p.2+16)):ℤ)),
                (𝐞 (f p.1 k):ℂ)‖ :=
  HuxleyBoundaryCoverScratch.positive_difference_eight_grid_chunk_cover F Y Refs n (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (R:=R) (U:=U) (Buffer:=Buffer) hn hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hR hscale hsep hgap hUlarge hBuffer



private theorem eight_grid_endpoint_selection (n : ℕ) (hn : 0 < n)
    {M Buffer Width : ℝ} (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(8*(n:ℝ)) ≤ M) :
    let N : ℝ := 8*n
    ∃ a b : ℤ,
      ⌈M⌉ ≤ (n:ℤ)*a ∧ a ≤ b ∧ (n:ℤ)*b ≤ ⌊2*M⌋ ∧
      (∀ m ∈ Finset.Ico a b, (n:ℝ)*m ∈
        Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N)) ∧
      ((((n:ℤ)*a-⌈M⌉:ℤ):ℝ)+((⌊2*M⌋-(n:ℤ)*b:ℤ):ℝ)) ≤
        2*Buffer+2*Width+6*N := by
  intro N
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let L := M+Buffer+Width+4*N
  let R := 2*M-Buffer-Width-N
  let a : ℤ := ⌈L/(n:ℝ)⌉
  let b : ℤ := ⌊R/(n:ℝ)⌋
  have haL : L ≤ (n:ℝ)*a := by
    have hh := Int.le_ceil (L/(n:ℝ))
    exact (div_le_iff₀ hnp).mp hh |>.trans_eq (mul_comm _ _)
  have haU : (n:ℝ)*a < L+(n:ℝ) := by
    have hh := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (L/(n:ℝ))) hnp
    change (n:ℝ)*a < (n:ℝ)*(L/(n:ℝ)+1) at hh
    convert hh using 1
    field_simp
  have hbL : R-(n:ℝ) < (n:ℝ)*b := by
    have hh := mul_lt_mul_of_pos_left (Int.sub_one_lt_floor (R/(n:ℝ))) hnp
    change (n:ℝ)*(R/(n:ℝ)-1) < (n:ℝ)*b at hh
    convert hh using 1
    field_simp
  have hbU : (n:ℝ)*b ≤ R := by
    have hh := (le_div_iff₀ hnp).mp (Int.floor_le (R/(n:ℝ)))
    exact (mul_comm _ _).le.trans hh
  have hLroom : L+2*(n:ℝ) ≤ R := by
    dsimp only [L,R,N]
    linarith only [hroom,hnp]
  have habR : (a:ℝ) ≤ b :=
    le_of_mul_le_mul_left
      (show (n:ℝ)*(a:ℝ) ≤ (n:ℝ)*b by linarith only [haU,hbL,hLroom]) hnp
  have hab : a ≤ b := by exact_mod_cast habR
  have haM : M ≤ (n:ℝ)*a := by
    dsimp only [L,N] at haL
    linarith only [haL,hBuffer,hWidth,hnp]
  have hbM : (n:ℝ)*b ≤ 2*M := by
    dsimp only [R,N] at hbU
    linarith only [hbU,hBuffer,hWidth,hnp]
  refine ⟨a,b,?_,hab,?_,?_,?_⟩
  · apply Int.ceil_le.mpr
    simpa only [Int.cast_mul,Int.cast_natCast] using haM
  · apply Int.le_floor.mpr
    simpa only [Int.cast_mul,Int.cast_natCast] using hbM
  · intro m hm
    obtain ⟨ham,hmb⟩ := Finset.mem_Ico.mp hm
    have hmL := mul_le_mul_of_nonneg_left (show (a:ℝ) ≤ m by exact_mod_cast ham) hnp.le
    have hmR := mul_le_mul_of_nonneg_left (show (m:ℝ) ≤ b by exact_mod_cast hmb.le) hnp.le
    exact ⟨haL.trans hmL,hmR.trans hbU⟩
  · have hceil := Int.le_ceil M
    have hfloor := Int.floor_le (2*M)
    push_cast
    dsimp only [L,R,N] at haU hbL ⊢
    linarith only [haU,hbL,hceil,hfloor,hnp]

example (n : ℕ) (hn : 0 < n)
    {M Buffer Width : ℝ} (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(8*(n:ℝ)) ≤ M) :
    let N : ℝ := 8*n
    ∃ a b : ℤ,
      ⌈M⌉ ≤ (n:ℤ)*a ∧ a ≤ b ∧ (n:ℤ)*b ≤ ⌊2*M⌋ ∧
      (∀ m ∈ Finset.Ico a b, (n:ℝ)*m ∈
        Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N)) ∧
      ((((n:ℤ)*a-⌈M⌉:ℤ):ℝ)+((⌊2*M⌋-(n:ℤ)*b:ℤ):ℝ)) ≤
        2*Buffer+2*Width+6*N :=
  HuxleyBoundaryCoverScratch.eight_grid_endpoint_selection n hn (M:=M) (Buffer:=Buffer) (Width:=Width) hBuffer hWidth hroom



private theorem direct_monomial_majorant_floor
    {m h n r q b : ℝ} (hscale : n+2*r = 4*m-1-h)
    (hdiagonal : m-h/2 ≤ b) (hmajor : m+(r-q)/2 ≤ b)
    (htype : (23*m-h-12*r+5*q+2*n)/24 ≤ b)
    (hlarge : m-r/3+5*q/18-7*n/36 ≤ b) :
    (53+882*m)/1106 ≤ b := by
  linarith only [hscale,hdiagonal,hmajor,htype,hlarge]

private theorem direct_monomial_majorant_misses_third_row :
    (89/1282:ℝ)+(454/641)*(1/3) < (347/1106:ℝ) ∧
      (53+882*(1/3:ℝ))/1106 = 347/1106 := by
  constructor <;> norm_num

example
    {m h n r q b : ℝ} (hscale : n+2*r = 4*m-1-h)
    (hdiagonal : m-h/2 ≤ b) (hmajor : m+(r-q)/2 ≤ b)
    (htype : (23*m-h-12*r+5*q+2*n)/24 ≤ b)
    (hlarge : m-r/3+5*q/18-7*n/36 ≤ b) :
    (53+882*m)/1106 ≤ b :=
  HuxleyBoundaryCoverScratch.direct_monomial_majorant_floor (m:=m) (h:=h) (n:=n) (r:=r) (q:=q) (b:=b) hscale hdiagonal hmajor htype hlarge

example :
    (89/1282:ℝ)+(454/641)*(1/3) < (347/1106:ℝ) ∧
      (53+882*(1/3:ℝ))/1106 = 347/1106 :=
  HuxleyBoundaryCoverScratch.direct_monomial_majorant_misses_third_row 



private theorem positive_difference_actual_anchor_family_band_card
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (anchor : ℝ × ℤ → ℚ) (N Q : ℕ) (s : ℝ)
    {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) (hYS : ∀ p ∈ S, p.1 ∈ Y)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ k ≤ 6, |iteratedDeriv (k+1) F w| ≤ J)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2 = M^3) (hQ : 2 ≤ Q)
    (hpoints : ∀ p ∈ S, s+(N:ℝ)*p.2 ∈ Icc M (2*M))
    (hband : ∀ p ∈ S, Q ≤ (anchor p).den) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(64*σ*R^2)
    let Vcurv := 3*J*M/(2*σ*(N:ℝ)*R^2)
    let D := 64*σ*R^2/(c*(Q:ℝ))
    (∀ p ∈ S, ∀ a : ℚ,
      (a:ℝ) ∈ Ioo (h p.1 (t p.2)-delta) (h p.1 (t p.2)+delta) →
        (anchor p).den ≤ a.den) →
    (S.card:ℝ) ≤ (Y.card:ℝ)*(4*Vcurv*D^2+3*D*(2+Real.log (D+1))) := by
  classical
  intro f h t delta Vcurv D hminimal
  let Sy := fun y => (S.filter (fun p => p.1 = y)).image Prod.snd
  have hSy y k : k ∈ Sy y ↔ (y,k) ∈ S := by
    constructor
    · intro hk
      obtain ⟨p,hp,hpk⟩ := Finset.mem_image.mp hk
      obtain ⟨hpS,hpy⟩ := Finset.mem_filter.mp hp
      have heq : p = (y,k) := Prod.ext hpy hpk
      exact heq ▸ hpS
    · intro hk
      exact Finset.mem_image.mpr ⟨(y,k),Finset.mem_filter.mpr ⟨hk,rfl⟩,rfl⟩
  have hcard y (hyY : y ∈ Y) : ((Sy y).card:ℝ) ≤
      4*Vcurv*D^2+3*D*(2+Real.log (D+1)) := by
    have hh := positive_difference_actual_minimal_anchor_sharp_tail
      (Sy y) F (fun k => anchor (y,k)) N s
      hσ hc hJ hη hηmax (hy y hyY) hf hbound htests hnegative
      hT hM hN hR hphase (fun k hk => hpoints (y,k) ((hSy y k).mp hk))
      (fun k hk a ha => hminimal (y,k) ((hSy y k).mp hk) a ha) Q hQ
    have heq : (Sy y).filter (fun k => Q ≤ (anchor (y,k)).den) = Sy y :=
      Finset.filter_eq_self.mpr (fun k hk => hband (y,k) ((hSy y k).mp hk))
    simpa only [heq] using hh.1
  have hcardImage y : (Sy y).card = (S.filter (fun p => p.1 = y)).card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq heq
    apply Prod.ext
    · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    · exact heq
  have hsum : (∑ y ∈ Y, ((Sy y).card:ℝ)) = S.card := by
    simp_rw [hcardImage]
    have hh := Finset.sum_fiberwise_of_maps_to hYS (fun _ => (1:ℝ))
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
  rw [←hsum]
  calc
    _ ≤ ∑ _y ∈ Y, (4*Vcurv*D^2+3*D*(2+Real.log (D+1))) :=
      Finset.sum_le_sum hcard
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

example
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (anchor : ℝ × ℤ → ℚ) (N Q : ℕ) (s : ℝ)
    {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) (hYS : ∀ p ∈ S, p.1 ∈ Y)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ k ≤ 6, |iteratedDeriv (k+1) F w| ≤ J)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2 = M^3) (hQ : 2 ≤ Q)
    (hpoints : ∀ p ∈ S, s+(N:ℝ)*p.2 ∈ Icc M (2*M))
    (hband : ∀ p ∈ S, Q ≤ (anchor p).den) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(64*σ*R^2)
    let Vcurv := 3*J*M/(2*σ*(N:ℝ)*R^2)
    let D := 64*σ*R^2/(c*(Q:ℝ))
    (∀ p ∈ S, ∀ a : ℚ,
      (a:ℝ) ∈ Ioo (h p.1 (t p.2)-delta) (h p.1 (t p.2)+delta) →
        (anchor p).den ≤ a.den) →
    (S.card:ℝ) ≤ (Y.card:ℝ)*(4*Vcurv*D^2+3*D*(2+Real.log (D+1))) :=
  HuxleyBoundaryCoverScratch.positive_difference_actual_anchor_family_band_card S Y F anchor N Q s (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (R:=R) hσ hc hJ hη hηmax hy hYS hf hbound htests hnegative hT hM hN hR hphase hQ hpoints hband



private theorem two_probes_avoid_open_neighborhoods
    (S : Set ℝ) {x y radius spacing : ℝ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → spacing ≤ |a-b|)
    (hprobe : 2*radius ≤ |x-y|)
    (hspan : |x-y|+2*radius < spacing) :
    (∀ a ∈ S, radius ≤ |x-a|) ∨ (∀ a ∈ S, radius ≤ |y-a|) := by
  classical
  by_contra hh
  obtain ⟨hx,hy⟩ := not_or.mp hh
  push Not at hx hy
  obtain ⟨a,ha,hxa⟩ := hx
  obtain ⟨b,hb,hyb⟩ := hy
  have hab : a = b := by
    by_contra hne
    have htriangle : |a-b| ≤ |x-a|+|x-y|+|y-b| := by
      calc
        |a-b| ≤ |a-x|+|x-b| := abs_sub_le _ _ _
        _ ≤ |a-x|+(|x-y|+|y-b|) := add_le_add le_rfl (abs_sub_le _ _ _)
        _ = _ := by rw [abs_sub_comm a x]; ring
    have hs := hsep a ha b hb hne
    linarith only [hs,htriangle,hxa,hyb,hspan]
  subst b
  have htriangle : |x-y| ≤ |x-a|+|y-a| := by
    simpa only [abs_sub_comm a y] using abs_sub_le x a y
  linarith only [htriangle,hprobe,hxa,hyb]

private theorem four_grid_probes_avoid_separated_sets
    (Roots Low : Set ℝ) (g : ℝ → ℝ) {x n delta spacing : ℝ}
    (hn : 0 < n)
    (hroots : ∀ a ∈ Roots, ∀ b ∈ Roots, a ≠ b → 16*n ≤ |a-b|)
    (hlow : ∀ a ∈ Low, ∀ b ∈ Low, a ≠ b → spacing ≤ |a-b|)
    (hvalueLower : ∀ a ∈ Icc (x-6*n) x, ∀ b ∈ Icc (x-6*n) x,
      n ≤ |a-b| → 2*delta ≤ |g a-g b|)
    (hvalueUpper : ∀ a ∈ Icc (x-6*n) x, ∀ b ∈ Icc (x-6*n) x,
      |g a-g b|+2*delta < spacing) :
    ∃ j : ℤ, (j=0 ∨ j=1 ∨ j=5 ∨ j=6) ∧
      (∀ z ∈ Roots, 2*n < |(x-j*n)-z|) ∧
      (∀ q ∈ Low, delta ≤ |g (x-j*n)-q|) := by
  have hfirst := two_probes_avoid_separated_set Roots
    (x:=x) (y:=x-5*n) (radius:=2*n) (spacing:=16*n) hroots
    (by rw [show x-(x-5*n)=5*n by ring,abs_of_pos (by positivity)]; linarith only [hn])
    (by rw [show x-(x-5*n)=5*n by ring,abs_of_pos (by positivity)]; linarith only [hn])
  have hsecond := two_probes_avoid_separated_set Roots
    (x:=x-n) (y:=x-6*n) (radius:=2*n) (spacing:=16*n) hroots
    (by rw [show (x-n)-(x-6*n)=5*n by ring,abs_of_pos (by positivity)]; linarith only [hn])
    (by rw [show (x-n)-(x-6*n)=5*n by ring,abs_of_pos (by positivity)]; linarith only [hn])
  obtain ⟨i,hi,hiroot⟩ :
      ∃ i : ℤ, (i=0 ∨ i=5) ∧ ∀ z ∈ Roots, 2*n < |(x-i*n)-z| := by
    rcases hfirst with hfirst | hfirst
    · exact ⟨0,Or.inl rfl,by simpa only [Int.cast_zero,zero_mul,sub_zero] using hfirst⟩
    · exact ⟨5,Or.inr rfl,by simpa only [Int.cast_ofNat] using hfirst⟩
  obtain ⟨j,hj,hjroot⟩ :
      ∃ j : ℤ, (j=1 ∨ j=6) ∧ ∀ z ∈ Roots, 2*n < |(x-j*n)-z| := by
    rcases hsecond with hsecond | hsecond
    · exact ⟨1,Or.inl rfl,by simpa only [Int.cast_one,one_mul] using hsecond⟩
    · exact ⟨6,Or.inr rfl,by simpa only [Int.cast_ofNat] using hsecond⟩
  have hipoint : x-i*n ∈ Icc (x-6*n) x := by
    rcases hi with rfl | rfl <;>
      simp only [Int.cast_zero,Int.cast_ofNat,zero_mul,sub_zero,mem_Icc] <;>
      constructor <;> linarith only [hn]
  have hjpoint : x-j*n ∈ Icc (x-6*n) x := by
    rcases hj with rfl | rfl <;>
      simp only [Int.cast_one,Int.cast_ofNat,one_mul,mem_Icc] <;>
      constructor <;> linarith only [hn]
  have hdist : n ≤ |(x-i*n)-(x-j*n)| := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp only [Int.cast_zero,Int.cast_one,Int.cast_ofNat,zero_mul,one_mul,sub_zero]
    all_goals rw [le_abs]; first | left; linarith only [hn] | right; linarith only [hn]
  have hpair := two_probes_avoid_open_neighborhoods Low hlow
    (hvalueLower _ hipoint _ hjpoint hdist) (hvalueUpper _ hipoint _ hjpoint)
  rcases hpair with hpair | hpair
  · refine ⟨i,?_,hiroot,hpair⟩
    rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inr (Or.inl hi))
  · refine ⟨j,?_,hjroot,hpair⟩
    rcases hj with hj | hj
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr (Or.inr hj))

example
    (S : Set ℝ) {x y radius spacing : ℝ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → spacing ≤ |a-b|)
    (hprobe : 2*radius ≤ |x-y|)
    (hspan : |x-y|+2*radius < spacing) :
    (∀ a ∈ S, radius ≤ |x-a|) ∨ (∀ a ∈ S, radius ≤ |y-a|) :=
  HuxleyBoundaryCoverScratch.two_probes_avoid_open_neighborhoods S (x:=x) (y:=y) (radius:=radius) (spacing:=spacing) hsep hprobe hspan

example
    (Roots Low : Set ℝ) (g : ℝ → ℝ) {x n delta spacing : ℝ}
    (hn : 0 < n)
    (hroots : ∀ a ∈ Roots, ∀ b ∈ Roots, a ≠ b → 16*n ≤ |a-b|)
    (hlow : ∀ a ∈ Low, ∀ b ∈ Low, a ≠ b → spacing ≤ |a-b|)
    (hvalueLower : ∀ a ∈ Icc (x-6*n) x, ∀ b ∈ Icc (x-6*n) x,
      n ≤ |a-b| → 2*delta ≤ |g a-g b|)
    (hvalueUpper : ∀ a ∈ Icc (x-6*n) x, ∀ b ∈ Icc (x-6*n) x,
      |g a-g b|+2*delta < spacing) :
    ∃ j : ℤ, (j=0 ∨ j=1 ∨ j=5 ∨ j=6) ∧
      (∀ z ∈ Roots, 2*n < |(x-j*n)-z|) ∧
      (∀ q ∈ Low, delta ≤ |g (x-j*n)-q|) :=
  HuxleyBoundaryCoverScratch.four_grid_probes_avoid_separated_sets Roots Low g (x:=x) (n:=n) (delta:=delta) (spacing:=spacing) hn hroots hlow hvalueLower hvalueUpper

#print axioms two_probes_avoid_open_neighborhoods
#print axioms four_grid_probes_avoid_separated_sets


private theorem positive_difference_four_safe_denominator_starts
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U D x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hUlarge : 12*J ≤ σ*U) (hD : 0 < D)
    (hbudget : (36*J+c)*D^2 < 32*σ*R^2)
    (hx : x ∈ Icc (M+3*N) (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let delta := c/(64*σ*R^2)
    ∃ j : ℤ, (j=0 ∨ j=1 ∨ j=5 ∨ j=6) ∧
      let t := x-2*N-j*(N/8)
      t ∈ Icc M (2*M) ∧
      (∀ z ∈ Icc M (2*M), h z ∈ Refs → N/4 < |t-z|) ∧
      (∀ q : ℚ, (q:ℝ) ∈ Ioo (h t-delta) (h t+delta) → D < q.den) := by
  intro f h delta
  let x₀ := x-2*N
  let n := N/8
  have hn : 0 < n := by dsimp only [n]; positivity
  have hpoints a (ha : a ∈ Icc (x₀-6*n) x₀) : a ∈ Icc M (2*M) := by
    dsimp only [x₀,n] at ha
    constructor <;> linarith only [ha.1,ha.2,hx.1,hx.2,hN]
  have hwide a (ha : a ∈ Icc M (2*M)) : a ∈ Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [ha.1,ha.2,hM]
  let Roots : Set ℝ := {z | z ∈ Icc M (2*M) ∧ h z ∈ Refs}
  have hmono := positive_difference_physical_curvature_strictMono F
    hσ hc hη hηmax hy hreg hnegative hT hM
  change StrictMonoOn h (Icc (3*M/4) (9*M/4)) at hmono
  have hsize : 2 ≤ (σ/(6*J))*U := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 6*J)).mpr
    linarith only [hUlarge]
  have hrootSep a (ha : a ∈ Roots) b (hb : b ∈ Roots) (hab : a ≠ b) :
      16*n ≤ |a-b| := by
    have hne : h b ≠ h a := fun he =>
      hab (hmono.injOn (hwide _ ha.1) (hwide _ hb.1) he.symm)
    have hw := positive_difference_reference_preimage_width_lower F
      hσ hJ hη hηmax hy hreg hbound hT hM hN hR hscale
      (hwide _ ha.1) (hwide _ hb.1) (hsep _ hb.2 _ ha.2 hne)
    calc
      16*n = 2*N := by dsimp only [n]; ring
      _ ≤ ((σ/(6*J))*U)*N := mul_le_mul_of_nonneg_right hsize hN.le
      _ ≤ |b-a| := hw
      _ = |a-b| := abs_sub_comm _ _
  let Low : Set ℝ := {v | ∃ q : ℚ, (q:ℝ)=v ∧ (q.den:ℝ) ≤ D}
  have hlow a (ha : a ∈ Low) b (hb : b ∈ Low) (hab : a ≠ b) :
      1/D^2 ≤ |a-b| := by
    obtain ⟨q,rfl,hq⟩ := ha
    obtain ⟨r,rfl,hr⟩ := hb
    have hne : q ≠ r := fun he => hab (congrArg (fun s : ℚ => (s:ℝ)) he)
    have hrat := rational_separation_scaled hne
    have hden : (q.den:ℝ)*r.den ≤ D^2 := by
      simpa only [pow_two] using mul_le_mul hq hr (Nat.cast_nonneg r.den) hD.le
    apply (div_le_iff₀ (pow_pos hD 2)).mpr
    calc
      1 ≤ |(q:ℝ)-(r:ℝ)| * (q.den:ℝ)*r.den := hrat
      _ = |(q:ℝ)-(r:ℝ)| * ((q.den:ℝ)*r.den) := by ring
      _ ≤ |(q:ℝ)-(r:ℝ)| * D^2 :=
        mul_le_mul_of_nonneg_left hden (abs_nonneg _)
  have hlower a (ha : a ∈ Icc (x₀-6*n) x₀)
      b (hb : b ∈ Icc (x₀-6*n) x₀) (hab : n ≤ |a-b|) :
      2*delta ≤ |h a-h b| := by
    let V := |h a-h b|
    have he : 7*(2*R^2*V/7)/(2*R^2) = V := by field_simp
    have hnear : |h b-h a| ≤ 7*(2*R^2*V/7)/(2*R^2) := by
      rw [he,abs_sub_comm]
    have hw := positive_difference_reference_preimage_width F
      hσ hc hη hηmax hy hreg hnegative hT hM hN hR hscale
      (hpoints a ha) (hpoints b hb) hnear
    have hmul : N*(1/8) ≤ N*((4*σ*R^2*V)/c) := by
      calc
        N*(1/8) = n := by dsimp only [n]; ring
        _ ≤ |a-b| := hab
        _ = |b-a| := abs_sub_comm _ _
        _ ≤ (14*σ/c)*(2*R^2*V/7)*N := hw
        _ = _ := by ring
    have hcancel := (mul_le_mul_iff_right₀ hN).mp hmul
    have hprod := (le_div_iff₀ hc).mp hcancel
    have hv : c/(32*σ*R^2) ≤ V := by
      apply (div_le_iff₀ (by positivity : 0 < 32*σ*R^2)).mpr
      nlinarith only [hprod]
    calc
      2*delta = c/(32*σ*R^2) := by dsimp only [delta]; ring
      _ ≤ V := hv
  have hupper a (ha : a ∈ Icc (x₀-6*n) x₀)
      b (hb : b ∈ Icc (x₀-6*n) x₀) :
      |h a-h b|+2*delta < 1/D^2 := by
    let V := |h a-h b|
    have he : (4*R^2*V)/(4*R^2) = V := by field_simp
    have hgap : (4*R^2*V)/(4*R^2) ≤ |h b-h a| := by
      rw [he,abs_sub_comm]
    have hw := positive_difference_reference_preimage_width_lower F
      hσ hJ hη hηmax hy hreg hbound hT hM hN hR hscale
      (hwide _ (hpoints a ha)) (hwide _ (hpoints b hb)) hgap
    have hdist : |b-a| ≤ 3*N/4 := by
      rw [abs_le]
      dsimp only [x₀,n] at ha hb
      constructor <;> linarith only [ha.1,ha.2,hb.1,hb.2]
    have hmul : N*((2*σ*R^2*V)/(3*J)) ≤ N*(3/4) := by
      calc
        N*((2*σ*R^2*V)/(3*J)) = (σ/(6*J))*(4*R^2*V)*N := by ring
        _ ≤ |b-a| := hw
        _ ≤ 3*N/4 := hdist
        _ = _ := by ring
    have hcancel := (mul_le_mul_iff_right₀ hN).mp hmul
    have hprod := (div_le_iff₀ (by positivity : 0 < 3*J)).mp hcancel
    have hv : V ≤ 9*J/(8*σ*R^2) := by
      apply (le_div_iff₀ (by positivity : 0 < 8*σ*R^2)).mpr
      nlinarith only [hprod]
    have hcap : (36*J+c)/(32*σ*R^2) < 1/D^2 := by
      apply (div_lt_div_iff₀ (by positivity : 0 < 32*σ*R^2) (pow_pos hD 2)).mpr
      simpa only [one_mul] using hbudget
    calc
      |h a-h b|+2*delta ≤ 9*J/(8*σ*R^2)+2*delta := add_le_add hv le_rfl
      _ = (36*J+c)/(32*σ*R^2) := by dsimp only [delta]; ring
      _ < 1/D^2 := hcap
  obtain ⟨j,hj,hroot,hlowj⟩ := four_grid_probes_avoid_separated_sets Roots Low h
    hn hrootSep hlow hlower hupper
  have hjpoint : x₀-j*n ∈ Icc (x₀-6*n) x₀ := by
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp only [Int.cast_zero,Int.cast_one,Int.cast_ofNat,zero_mul,one_mul,sub_zero,mem_Icc] <;>
      constructor <;> linarith only [hn]
  refine ⟨j,hj,hpoints _ hjpoint,?_,?_⟩
  · intro z hz hzref
    have hs := hroot z ⟨hz,hzref⟩
    convert hs using 1
    dsimp only [x₀,n]
    ring
  · intro q hq
    by_contra hnot
    have hqLow : (q:ℝ) ∈ Low := ⟨q,rfl,le_of_not_gt hnot⟩
    have hbad := hlowj _ hqLow
    have hnear : |h (x₀-j*n)-(q:ℝ)| < delta := by
      rw [abs_lt]
      constructor <;> linarith only [hq.1,hq.2]
    exact (not_lt_of_ge hbad) hnear

example
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U D x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hUlarge : 12*J ≤ σ*U) (hD : 0 < D)
    (hbudget : (36*J+c)*D^2 < 32*σ*R^2)
    (hx : x ∈ Icc (M+3*N) (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let delta := c/(64*σ*R^2)
    ∃ j : ℤ, (j=0 ∨ j=1 ∨ j=5 ∨ j=6) ∧
      let t := x-2*N-j*(N/8)
      t ∈ Icc M (2*M) ∧
      (∀ z ∈ Icc M (2*M), h z ∈ Refs → N/4 < |t-z|) ∧
      (∀ q : ℚ, (q:ℝ) ∈ Ioo (h t-delta) (h t+delta) → D < q.den) :=
  HuxleyBoundaryCoverScratch.positive_difference_four_safe_denominator_starts F Refs (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (D:=D) (x:=x) hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hN hR hscale hsep hUlarge hD hbudget hx

#print axioms positive_difference_four_safe_denominator_starts

private theorem positive_difference_four_buffered_denominator_starts
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U Buffer Dmin x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
      b-a ≤ 7*U/(2*R^2))
    (hUlarge : 12*J ≤ σ*U) (hBuffer : 0 ≤ Buffer)
    (hDmin : 0 < Dmin) (hbudget : (36*J+c)*Dmin^2 < 32*σ*R^2) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let Width := (14*σ/c)*U*N
    let delta := c/(64*σ*R^2)
    (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h M ∧ h (2*M) ≤ u) →
    (∀ q ∈ Refs, q ∈ Icc (h M) (h (2*M)) → ∃ z ∈ Icc M (2*M), h z = q) →
    x ∈ Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N) →
    ∃ j : ℤ, (j=0 ∨ j=1 ∨ j=5 ∨ j=6) ∧
      let t := x-2*N-j*(N/8)
      (∀ q : ℚ, (q:ℝ) ∈ Ioo (h t-delta) (h t+delta) → Dmin < q.den) ∧
      ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h z₁ = a ∧ h z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ t ∧ t ≤ z₂-N/4 := by
  intro f h Width delta henclose hroots hx
  have hU : 0 < U := (div_pos (by positivity : 0 < 12*J) hσ).trans_le
    ((div_le_iff₀ hσ).mpr (by simpa only [mul_comm] using hUlarge))
  have hWidth : 0 ≤ Width := by dsimp only [Width]; positivity
  have hmono : StrictMonoOn h (Icc M (2*M)) := by
    apply (positive_difference_physical_curvature_strictMono F hσ hc hη hηmax hy
      hreg hnegative hT hM).mono
    intro w hw
    constructor <;> linarith only [hw.1,hw.2,hM]
  have hwidth a (ha : a ∈ Refs) b (hb : b ∈ Refs) (hab : a < b)
      (hadj : ∀ q ∈ Refs,¬(a < q ∧ q < b))
      u (hu : u ∈ Icc M (2*M)) z (hz : z ∈ Icc M (2*M))
      (huc : h u ∈ Icc a b) (hzc : h z ∈ Icc a b) : |z-u| ≤ Width := by
    apply positive_difference_reference_preimage_width F
      hσ hc hη hηmax hy hreg hnegative hT hM hN hR hscale hu hz
    change |h z-h u| ≤ 7*U/(2*R^2)
    apply (abs_le.mpr ?_).trans (hgap a ha b hb hab hadj)
    constructor <;> linarith only [huc.1,huc.2,hzc.1,hzc.2]
  obtain ⟨j,hj,_,hsafe,hden⟩ := positive_difference_four_safe_denominator_starts F Refs
    hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hN hR hscale hsep hUlarge
    hDmin hbudget
    (show x ∈ Icc (M+3*N) (2*M) from
      ⟨by linarith only [hx.1,hBuffer,hWidth,hN],by linarith only [hx.2,hBuffer,hWidth,hN]⟩)
  have ht : x-2*N-j*(N/8) ∈ Icc (M+Buffer+Width+N) (2*M-Buffer-Width-N) := by
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp only [Int.cast_zero,Int.cast_one,Int.cast_ofNat,zero_mul,one_mul,sub_zero,mem_Icc] <;>
      constructor <;> linarith only [hx.1,hx.2,hN]
  exact ⟨j,hj,hden,finite_reference_safe_start_buffered_bracket Refs h hM hN hBuffer hWidth
    hmono henclose hroots hwidth ht hsafe⟩


private theorem huxley_sharp_tail_quadratic_density_scale
    {σ c J M N R Q : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hNQ : N*Q ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let D := 64*σ*R^2/(c*Q)
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    4*Vcurv*D^2+3*D*(2+Real.log (D+1)) ≤
      C*(M*R^2/(N*Q^2))*(2+Real.log (D+1)) := by
  intro Vcurv D C
  let A := 64*σ/c
  let K := M*R^2/(N*Q^2)
  let L := 2+Real.log (D+1)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 1 ≤ L := by
    have hh := Real.log_nonneg (show 1 ≤ D+1 by linarith only [hD])
    dsimp only [L]
    linarith only [hh]
  have hbase : R^2/Q ≤ K := by
    apply (div_le_div_iff₀ hQ (by positivity : 0 < N*Q^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNQ (show 0 ≤ R^2*Q by positivity)]
  have hfirst : 4*Vcurv*D^2 ≤ (6*J/σ)*A^2*K*L := by
    have he : 4*Vcurv*D^2 = (6*J/σ)*A^2*K := by
      dsimp only [Vcurv,D,A,K]
      field_simp
      ring
    rw [he]
    exact le_mul_of_one_le_right (by positivity) hL
  have hsecond : 3*D*L ≤ 3*A*K*L := by
    have he : D=A*(R^2/Q) := by dsimp only [D,A]; ring
    rw [he,←mul_assoc (3:ℝ) A]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbase (by positivity)) (by linarith only [hL])
  have hh := add_le_add hfirst hsecond
  convert hh using 1
  dsimp only [C,A]
  ring

example
    (F : ℝ → ℝ) (Refs : Finset ℝ) {σ c J η y T M N R U Buffer Dmin x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2 = M^3)
    (hsep : ∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → U/(4*R^2) ≤ |a-b|)
    (hgap : ∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
      b-a ≤ 7*U/(2*R^2))
    (hUlarge : 12*J ≤ σ*U) (hBuffer : 0 ≤ Buffer)
    (hDmin : 0 < Dmin) (hbudget : (36*J+c)*Dmin^2 < 32*σ*R^2) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let Width := (14*σ/c)*U*N
    let delta := c/(64*σ*R^2)
    (∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h M ∧ h (2*M) ≤ u) →
    (∀ q ∈ Refs, q ∈ Icc (h M) (h (2*M)) → ∃ z ∈ Icc M (2*M), h z = q) →
    x ∈ Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N) →
    ∃ j : ℤ, (j=0 ∨ j=1 ∨ j=5 ∨ j=6) ∧
      let t := x-2*N-j*(N/8)
      (∀ q : ℚ, (q:ℝ) ∈ Ioo (h t-delta) (h t+delta) → Dmin < q.den) ∧
      ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
        ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
          h z₁ = a ∧ h z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
          z₁+N/4 ≤ t ∧ t ≤ z₂-N/4 :=
  HuxleyBoundaryCoverScratch.positive_difference_four_buffered_denominator_starts F Refs (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) (Buffer:=Buffer) (Dmin:=Dmin) (x:=x) hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hN hR hscale hsep hgap hUlarge hBuffer hDmin hbudget

example
    {σ c J M N R Q : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hNQ : N*Q ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let D := 64*σ*R^2/(c*Q)
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    4*Vcurv*D^2+3*D*(2+Real.log (D+1)) ≤
      C*(M*R^2/(N*Q^2))*(2+Real.log (D+1)) :=
  HuxleyBoundaryCoverScratch.huxley_sharp_tail_quadratic_density_scale (σ:=σ) (c:=c) (J:=J) (M:=M) (N:=N) (R:=R) (Q:=Q) hσ hc hJ hM hN hR hQ hNQ

#print axioms positive_difference_four_buffered_denominator_starts
#print axioms huxley_sharp_tail_quadratic_density_scale


private theorem positive_difference_actual_anchor_family_quadratic_density
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (anchor : ℝ × ℤ → ℚ) (N Q : ℕ) (s : ℝ)
    {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) (hYS : ∀ p ∈ S, p.1 ∈ Y)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ k ≤ 6, |iteratedDeriv (k+1) F w| ≤ J)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2 = M^3) (hQ : 2 ≤ Q)
    (hpoints : ∀ p ∈ S, s+(N:ℝ)*p.2 ∈ Icc M (2*M))
    (hband : ∀ p ∈ S, Q ≤ (anchor p).den)
    (hNQ : (N:ℝ)*(Q:ℝ) ≤ M) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(64*σ*R^2)
    let D := 64*σ*R^2/(c*(Q:ℝ))
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    (∀ p ∈ S, ∀ a : ℚ,
      (a:ℝ) ∈ Ioo (h p.1 (t p.2)-delta) (h p.1 (t p.2)+delta) →
        (anchor p).den ≤ a.den) →
    (S.card:ℝ) ≤ (Y.card:ℝ)*C*(M*R^2/((N:ℝ)*(Q:ℝ)^2))*(2+Real.log (D+1)) := by
  intro f h t delta D C hminimal
  have hraw := positive_difference_actual_anchor_family_band_card S Y F anchor N Q s
    hσ hc hJ hη hηmax hy hYS hf hbound htests hnegative
    hT hM hN hR hphase hQ hpoints hband hminimal
  have hscaled := huxley_sharp_tail_quadratic_density_scale hσ hc hJ hM
    (Nat.cast_pos.mpr hN) hR (show (0:ℝ) < Q by exact_mod_cast (show 0 < Q by omega)) hNQ
  have hh := hraw.trans (mul_le_mul_of_nonneg_left hscaled (Nat.cast_nonneg Y.card))
  convert hh using 1
  ring

example
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (anchor : ℝ × ℤ → ℚ) (N Q : ℕ) (s : ℝ)
    {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) (hYS : ∀ p ∈ S, p.1 ∈ Y)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ k ≤ 6, |iteratedDeriv (k+1) F w| ≤ J)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2 = M^3) (hQ : 2 ≤ Q)
    (hpoints : ∀ p ∈ S, s+(N:ℝ)*p.2 ∈ Icc M (2*M))
    (hband : ∀ p ∈ S, Q ≤ (anchor p).den)
    (hNQ : (N:ℝ)*(Q:ℝ) ≤ M) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let t := fun k : ℤ => s+(N:ℝ)*k
    let delta := c/(64*σ*R^2)
    let D := 64*σ*R^2/(c*(Q:ℝ))
    let C := (6*J/σ)*(64*σ/c)^2+192*σ/c
    (∀ p ∈ S, ∀ a : ℚ,
      (a:ℝ) ∈ Ioo (h p.1 (t p.2)-delta) (h p.1 (t p.2)+delta) →
        (anchor p).den ≤ a.den) →
    (S.card:ℝ) ≤ (Y.card:ℝ)*C*(M*R^2/((N:ℝ)*(Q:ℝ)^2))*(2+Real.log (D+1)) :=
  HuxleyBoundaryCoverScratch.positive_difference_actual_anchor_family_quadratic_density S Y F anchor N Q s (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (R:=R) hσ hc hJ hη hηmax hy hYS hf hbound htests hnegative hT hM hN hR hphase hQ hpoints hband hNQ

#print axioms positive_difference_actual_anchor_family_quadratic_density


private theorem positive_difference_local_pair_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η xa xb ya yb : ℝ),
      0 < η → η ≤ 1/8 → xa ∈ Icc (1:ℝ) 2 → xb ∈ Icc (1:ℝ) 2 →
      ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 → |yb-ya| < a →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      H (yb,xb)=H (ya,xa) →
      |yb-ya| ≤ C*|G (yb,xb)-G (ya,xa)| := by
  classical
  obtain ⟨a,C,ha,hacap,hC,hlocal⟩ := positive_difference_local_parameter_count hσ hc hU
  refine ⟨a,C,ha,hacap,hC,?_⟩
  intro F η xa xb ya yb hη hηmax hxa hxb hya hyb hclose hreg hbound htests H G hroot
  by_cases heq : ya=yb
  · subst yb
    simp only [sub_self,abs_zero]
    exact mul_nonneg hC.le (abs_nonneg _)
  have hd : 0 < |yb-ya| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm heq))
  let S : Finset ℝ := {ya,yb}
  let point := fun y : ℝ => if y=ya then xa else xb
  have hpa : point ya=xa := by simp only [point,ite_true]
  have hpb : point yb=xb := by simp only [point,if_neg (Ne.symm heq)]
  have hmem y : y ∈ S ↔ y=ya ∨ y=yb := by
    simp only [S,Finset.mem_insert,Finset.mem_singleton]
  have hpoints y (hy : y ∈ S) :
      y ∈ Icc (1:ℝ) 2 ∧ |y-ya| < a ∧ point y ∈ Icc (1:ℝ) 2 := by
    rcases (hmem y).mp hy with rfl | rfl
    · exact ⟨hya,by simpa only [sub_self,abs_zero] using ha,hpa.symm ▸ hxa⟩
    · exact ⟨hyb,hclose,hpb.symm ▸ hxb⟩
  have hsep y (hy : y ∈ S) z (hz : z ∈ S) (hne : y ≠ z) :
      1 ≤ (1/|yb-ya|)*|y-z| := by
    rcases (hmem y).mp hy with hy | hy <;> rcases (hmem z).mp hz with hz | hz <;>
      rw [hy,hz] at hne ⊢
    · exact (hne rfl).elim
    · rw [abs_sub_comm ya yb,one_div_mul_cancel hd.ne']
    · rw [one_div_mul_cancel hd.ne']
    · exact (hne rfl).elim
  have hroots y (hy : y ∈ S) : H (y,point y)=H (ya,xa) := by
    rcases (hmem y).mp hy with rfl | rfl
    · rw [hpa]
    · rw [hpb]; exact hroot
  have hres y (hy : y ∈ S) :
      |G (y,point y)-G (ya,xa)| ≤ |G (yb,xb)-G (ya,xa)| := by
    rcases (hmem y).mp hy with rfl | rfl
    · rw [hpa,sub_self,abs_zero]; exact abs_nonneg _
    · rw [hpb]
  have hh := hlocal F η xa ya |G (yb,xb)-G (ya,xa)|
    (1/|yb-ya|) (G (ya,xa)) S point hη hηmax hxa hya hreg hbound htests
    (abs_nonneg _) (one_div_pos.mpr hd) hpoints hsep hroots hres
  have hcard : S.card=2 := by simp only [S,Finset.card_insert_of_notMem
    (show ya ∉ ({yb}:Finset ℝ) by simpa only [Finset.mem_singleton] using heq),
    Finset.card_singleton]
  rw [hcard] at hh
  have hone : 1 ≤ (C*|G (yb,xb)-G (ya,xa)|)/|yb-ya| := by
    simpa only [mul_one_div] using (show (1:ℝ) ≤ C*|G (yb,xb)-G (ya,xa)| * (1/|yb-ya|)
      by norm_num only [Nat.cast_ofNat] at hh; linarith only [hh])
  simpa only [one_mul] using (le_div_iff₀ hd).mp hone

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η xa xb ya yb : ℝ),
      0 < η → η ≤ 1/8 → xa ∈ Icc (1:ℝ) 2 → xb ∈ Icc (1:ℝ) 2 →
      ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 → |yb-ya| < a →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let H := fun v : ℝ × ℝ =>
        (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
      let G := fun v : ℝ × ℝ =>
        (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
      H (yb,xb)=H (ya,xa) →
      |yb-ya| ≤ C*|G (yb,xb)-G (ya,xa)| :=
  HuxleyBoundaryCoverScratch.positive_difference_local_pair_compression (σ:=σ) (c:=c) (U:=U) hσ hc hU

#print axioms positive_difference_local_pair_compression


private theorem positive_difference_physical_identity_pair_compression
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η xa xb ya yb T M Δ : ℝ),
      0 < η → η ≤ 1/8 → 0 < T → 2 ≤ M → 0 ≤ Δ →
      xa ∈ Icc M (2*M) → xb ∈ Icc M (2*M) →
      ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 → |yb-ya| < a →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let mu := fun y z => iteratedDeriv 3 (f y) (round z)/6
      iteratedDeriv 2 (f yb) xb/2=iteratedDeriv 2 (f ya) xa/2 →
      |mu yb xb/mu ya xa-1| ≤ Δ →
      |yb-ya| ≤ C*(Δ+1/M) := by
  obtain ⟨a,C,ha,hacap,hC,hpair⟩ := positive_difference_local_pair_compression hσ hc hU
  let B := max 1 (max (3*U/σ) (2*σ/c))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨a,C*B,ha,hacap,mul_pos hC hB,?_⟩
  intro F η xa xb ya yb T M Δ hη hηmax hT hM hΔ hxa hxb hya hyb hclose
    hreg hbound htests f mu hlevel hthird
  have hMpos : 0 < M := by linarith only [hM]
  let H := fun v : ℝ × ℝ =>
    (iteratedDeriv 2 F v.2-iteratedDeriv 2 F (v.2+η*v.1))/(σ*η)
  let G := fun v : ℝ × ℝ =>
    (iteratedDeriv 3 F v.2-iteratedDeriv 3 F (v.2+η*v.1))/(σ*η)
  have hnorm z (hz : z ∈ Icc M (2*M)) : z/M ∈ Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hMpos).mpr (by simpa using hz.1),(div_le_iff₀ hMpos).mpr hz.2⟩
  have hd n z y (hz : 0 < z) (hy : y ∈ Icc (1:ℝ) 2) :
      iteratedDeriv n (f y) z =
        T/M^n*((iteratedDeriv n F (z/M)-iteratedDeriv n F (z/M+η*y))/(σ*η)) :=
    positive_difference_physical_iteratedDeriv F hMpos hz
      (mul_nonneg hη.le (by linarith only [hy.1])) hreg n
  have hHid y z (hy : y ∈ Icc (1:ℝ) 2) (hz : z ∈ Icc M (2*M)) :
      H (y,z/M) = (2*M^2/T)*(iteratedDeriv 2 (f y) z/2) := by
    rw [hd 2 z y (hMpos.trans_le hz.1) hy]
    dsimp only [H]
    field_simp
  have hroot : H (yb,xb/M)=H (ya,xa/M) := by
    rw [hHid yb xb hyb hxb,hHid ya xa hya hxa,hlevel]
  have hcompress := hpair F η (xa/M) (xb/M) ya yb hη hηmax
    (hnorm xa hxa) (hnorm xb hxb) hya hyb hclose hreg hbound htests hroot
  have hroundpos z (hz : z ∈ Icc M (2*M)) : (0:ℝ) < round z := by
    have hh := abs_le.mp (abs_sub_round z)
    linarith only [hh.2,hz.1,hM]
  have hmu y z (hy : y ∈ Icc (1:ℝ) 2) (hz : z ∈ Icc M (2*M)) :
      mu y z=(T/(6*M^3))*G (y,(round z:ℝ)/M) := by
    dsimp only [mu]
    rw [hd 3 (round z) y (hroundpos z hz) hy]
    dsimp only [G]
    ring
  have hthird' :
      |G (yb,(round (M*(xb/M)):ℝ)/M)/G (ya,(round (M*(xa/M)):ℝ)/M)*1-1| ≤ Δ := by
    have he z : M*(z/M)=z := mul_div_cancel₀ z hMpos.ne'
    rw [he,he,mul_one]
    rw [hmu yb xb hyb hxb,hmu ya xa hya hxa,
      mul_div_mul_left _ _ (show T/(6*M^3) ≠ 0 by positivity)] at hthird
    exact hthird
  have hraw := positive_difference_rounded_weighted_third_bound F hσ hc hU hη hηmax
    hM (hnorm xa hxa) (hnorm xb hxb) hya hyb hreg hbound htests hΔ hthird'
  have hnear : |G (yb,xb/M)-G (ya,xa/M)| ≤ B*(Δ+1/M) := by
    convert hraw using 1 <;> simp only [mul_one,abs_one] <;> ring
  calc
    |yb-ya| ≤ C*|G (yb,xb/M)-G (ya,xa/M)| := hcompress
    _ ≤ C*(B*(Δ+1/M)) := mul_le_mul_of_nonneg_left hnear hC.le
    _ = _ := by ring

example
    {σ c U : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (η xa xb ya yb T M Δ : ℝ),
      0 < η → η ≤ 1/8 → 0 < T → 2 ≤ M → 0 ≤ Δ →
      xa ∈ Icc M (2*M) → xb ∈ Icc M (2*M) →
      ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 → |yb-ya| < a →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      let f := fun y z => T*(F (z/M)-F (z/M+η*y))/(σ*η)
      let mu := fun y z => iteratedDeriv 3 (f y) (round z)/6
      iteratedDeriv 2 (f yb) xb/2=iteratedDeriv 2 (f ya) xa/2 →
      |mu yb xb/mu ya xa-1| ≤ Δ →
      |yb-ya| ≤ C*(Δ+1/M) :=
  HuxleyBoundaryCoverScratch.positive_difference_physical_identity_pair_compression (σ:=σ) (c:=c) (U:=U) hσ hc hU

#print axioms positive_difference_physical_identity_pair_compression


private theorem positive_difference_identity_quartic_long_block_parameter_gap
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ)
      (x : Fin 4 → ℝ) (A : Fin 2 → ℤ) (W x₀ : Fin 2 → ℝ)
      (curve : ℝ → Fin 2 → ℝ) (e r v s : ℝ)
      {σ δ T M N R L d K α β : ℝ},
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 → |yb-ya| < a →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      0 < Tsrc → 2 ≤ M →
      let yp : Fin 2 → ℝ := ![ya,yb]
      let F := fun (i : Fin 2) u =>
        (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
      (0 < σ) →
      (δ ≤ min (modelPhaseThirdLower σ) 1) →
      (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
      0 < T → 0 < N → 1 ≤ R → 0 < L → (L*N)^2 ≤ M*R → 0 < d → 0 ≤ K →
      (∀ i, M ≤ A i) → (∀ i, A i+W i ≤ 2*M) →
      (∀ i, x₀ i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ z ∈ Icc (x 0) (x 3), ∀ i, curve z i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      r ≠ 0 → v*r-e*s=1 →
      (∀ z ∈ Icc (x 0) (x 3), d ≤ r*z+s ∧ r*z+s ≤ 2*d) →
      StrictMono x →
      let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
      let n := fun z i => (round (curve z i):ℝ)-(round (x₀ i):ℝ)
      let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
      let nu := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
      let g := rationalPhase (mu 0) r s (mu 1) r s
      let H := quarticPhase (mu 0) (nu 0) r s (mu 1) (nu 1) r s
      let G := minorArcCoordinate (mu 0) r s
      (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e/r) →
      (∀ z ∈ Icc (x 0) (x 3), ∀ i, iteratedDeriv 2 (f i) (curve z i)/2=(e*z+v)/(r*z+s)) →
      (∀ z ∈ Icc (x 0) (x 3), ∀ i, |n z i|^2 ≤ M*R) →
      (∀ j : Fin 3, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
      (∀ j : Fin 4, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r*G (x j)|) →
      let Cthird := ((σ*(σ+1)+1)/modelPhaseThirdLower σ)*
        (32*K+9*quarticReciprocalConstant σ δ)
      |yb-ya| ≤ C*(Cthird+1)*R^2/(L^2*N^2) := by
  obtain ⟨a,C,ha,hacap,hC,hpair⟩ :=
    positive_difference_physical_identity_pair_compression hσsrc hcsrc hUsrc
  refine ⟨a,C,ha,hacap,hC,?_⟩
  intro Fsrc η ya yb Tsrc x A W x₀ curve e r v s σ δ T M N R L d K α β
    hη hηmax hya hyb hclose hreg hbound htests hTsrc hMtwo yp F hσ hδ hF
    hT hN hR hL hNL hd hK hA hW hx₀ hcurve hr hdet hden hmono
    f n mu nu g H G hbase hpoint hsquare hspacing hres Cthird
  have hM : 0 < M := by linarith only [hMtwo]
  obtain ⟨z,hz,hthird⟩ := physicalModelPhase_quartic_long_block_third_condition x
    (r:=fun _ => r) (s:=fun _ => s) (e:=fun _ => e) (v:=fun _ => v)
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hcurve
    (fun _ => hr) (fun _ => hdet) (fun z hz _ => (hden z hz).1)
    (fun z hz _ => (hden z hz).2) hmono hbase hpoint hsquare hspacing hres
  have hzcc : z ∈ Icc (x 0) (x 3) := ⟨hz.1.le,hz.2.le⟩
  have hdenpos : 0 < r*z+s := hd.trans_le (hden z hzcc).1
  let Src := fun y w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
  have hsource i : f i=fun w => Src (yp i) ((A i:ℝ)+w) := by
    funext w
    dsimp only [f,heathBrownPhysicalPhase,F,Src]
    field_simp
  have hjet i k t : iteratedDeriv k (f i) t =
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hround i k t : iteratedDeriv k (f i) (round t) =
      iteratedDeriv k (Src (yp i)) (round ((A i:ℝ)+t)) := by
    rw [hjet,round_intCast_add,Int.cast_add]
  have hphysical i : (A i:ℝ)+curve z i ∈ Icc M (2*M) :=
    ⟨by linarith only [hA i,(hcurve z hzcc i).1],
     by linarith only [hW i,(hcurve z hzcc i).2]⟩
  have hlevel : iteratedDeriv 2 (Src yb) ((A 1:ℝ)+curve z 1)/2 =
      iteratedDeriv 2 (Src ya) ((A 0:ℝ)+curve z 0)/2 := by
    change iteratedDeriv 2 (Src (yp 1)) ((A 1:ℝ)+curve z 1)/2 =
      iteratedDeriv 2 (Src (yp 0)) ((A 0:ℝ)+curve z 0)/2
    rw [←hjet 1 2,←hjet 0 2,hpoint z hzcc 1,hpoint z hzcc 0]
  have hthird' :
      |(iteratedDeriv 3 (Src yb) (round ((A 1:ℝ)+curve z 1))/6)/
        (iteratedDeriv 3 (Src ya) (round ((A 0:ℝ)+curve z 0))/6)-1| ≤
          Cthird*R^2/(L^2*N^2) := by
    change |(iteratedDeriv 3 (Src (yp 1)) (round ((A 1:ℝ)+curve z 1))/6)/
        (iteratedDeriv 3 (Src (yp 0)) (round ((A 0:ℝ)+curve z 0))/6)-1| ≤ _
    rw [←hround 1 3,←hround 0 3]
    simpa only [mul_div_mul_right _ _ (pow_ne_zero 3 hdenpos.ne')] using hthird
  have hδ0 : 0 ≤ δ := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := modelPhaseJetCoefficient_nonneg σ 2
  have hC₃ := modelPhaseJetCoefficient_nonneg σ 3
  have hC₄ := modelPhaseJetCoefficient_nonneg σ 4
  have hκ := modelPhaseThirdLower_pos hσ
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]
    positivity
  have hCt : 0 ≤ Cthird := by
    dsimp only [Cthird]
    exact mul_nonneg (div_nonneg (by positivity) (modelPhaseThirdLower_pos hσ).le)
      (add_nonneg (mul_nonneg (by norm_num) hK) (mul_nonneg (by norm_num) hCR))
  have hgap := hpair Fsrc η ((A 0:ℝ)+curve z 0) ((A 1:ℝ)+curve z 1)
    ya yb Tsrc M (Cthird*R^2/(L^2*N^2)) hη hηmax hTsrc hMtwo
    (by positivity) (hphysical 0) (hphysical 1) hya hyb hclose hreg hbound htests hlevel hthird'
  have habsorb : 1/M ≤ R^2/(L^2*N^2) := by
    apply (div_le_div_iff₀ hM (by positivity : 0 < L^2*N^2)).mpr
    have hRR : R ≤ R^2 := by nlinarith only [hR]
    have hh := mul_le_mul_of_nonneg_left hRR hM.le
    nlinarith only [hNL,hh]
  calc
    |yb-ya| ≤ C*(Cthird*R^2/(L^2*N^2)+1/M) := hgap
    _ ≤ C*(Cthird*R^2/(L^2*N^2)+R^2/(L^2*N^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl habsorb) hC.le
    _ = _ := by ring

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ)
      (x : Fin 4 → ℝ) (A : Fin 2 → ℤ) (W x₀ : Fin 2 → ℝ)
      (curve : ℝ → Fin 2 → ℝ) (e r v s : ℝ)
      {σ δ T M N R L d K α β : ℝ},
      0 < η → η ≤ 1/8 → ya ∈ Icc (1:ℝ) 2 → yb ∈ Icc (1:ℝ) 2 → |yb-ya| < a →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      0 < Tsrc → 2 ≤ M →
      let yp : Fin 2 → ℝ := ![ya,yb]
      let F := fun (i : Fin 2) u =>
        (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
      (0 < σ) →
      (δ ≤ min (modelPhaseThirdLower σ) 1) →
      (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
      0 < T → 0 < N → 1 ≤ R → 0 < L → (L*N)^2 ≤ M*R → 0 < d → 0 ≤ K →
      (∀ i, M ≤ A i) → (∀ i, A i+W i ≤ 2*M) →
      (∀ i, x₀ i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ z ∈ Icc (x 0) (x 3), ∀ i, curve z i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      r ≠ 0 → v*r-e*s=1 →
      (∀ z ∈ Icc (x 0) (x 3), d ≤ r*z+s ∧ r*z+s ≤ 2*d) →
      StrictMono x →
      let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
      let n := fun z i => (round (curve z i):ℝ)-(round (x₀ i):ℝ)
      let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
      let nu := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
      let g := rationalPhase (mu 0) r s (mu 1) r s
      let H := quarticPhase (mu 0) (nu 0) r s (mu 1) (nu 1) r s
      let G := minorArcCoordinate (mu 0) r s
      (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e/r) →
      (∀ z ∈ Icc (x 0) (x 3), ∀ i, iteratedDeriv 2 (f i) (curve z i)/2=(e*z+v)/(r*z+s)) →
      (∀ z ∈ Icc (x 0) (x 3), ∀ i, |n z i|^2 ≤ M*R) →
      (∀ j : Fin 3, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
      (∀ j : Fin 4, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r*G (x j)|) →
      let Cthird := ((σ*(σ+1)+1)/modelPhaseThirdLower σ)*
        (32*K+9*quarticReciprocalConstant σ δ)
      |yb-ya| ≤ C*(Cthird+1)*R^2/(L^2*N^2) :=
  HuxleyBoundaryCoverScratch.positive_difference_identity_quartic_long_block_parameter_gap (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

#print axioms positive_difference_identity_quartic_long_block_parameter_gap


private theorem fourier_matrix_constructed_upper_triangular_narrowing
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K N R : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hN : 0 < N)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2)) :
    let V := 1+R^4/(6*N^2)
    1 ≤ V ∧ (|Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V) →
      A 0=1 ∧ A 3=1 ∧ A 2=0 ∧ q 0=q 1 ∧ e 1=e 0+A 1*q 0) := by
  intro V
  have hV : 1 ≤ V := by
    dsimp only [V]
    have hh : 0 ≤ R^4/(6*N^2) := div_nonneg (by positivity) (by positivity)
    linarith only [hh]
  refine ⟨hV,?_⟩
  intro hnear
  have hcap := (fourier_matrix_narrowed_coordinate_entry_bound q e vinv A
    hq hK hV hN hmesh hband hinv hdet ht hmap hgamma hnear).2
  have hstrict : R^4/(6*N^2*V) < 1 := by
    have hden : 0 < 6*N^2*V := mul_pos (by positivity) (zero_lt_one.trans_le hV)
    apply (div_lt_one₀ hden).mpr
    have he : 6*N^2*V=6*N^2+R^4 := by
      dsimp only [V]
      field_simp
    rw [he]
    nlinarith only [sq_pos_of_pos hN]
  have hc : A 2=0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hcap.trans_lt hstrict)
  have hqr i : (0:ℝ) < q i := by exact_mod_cast hq i
  have hdet' : A 0*A 3=1 := by simpa only [hc,mul_zero,sub_zero] using hdet
  have ht' : (A 3:ℝ)=(q 1:ℝ)/q 0 := by
    simpa only [hc,Int.cast_zero,zero_mul,zero_add] using ht
  have hdpos : 0 < A 3 := by
    have hh : (0:ℝ) < A 3 := by rw [ht']; exact div_pos (hqr 1) (hqr 0)
    exact_mod_cast hh
  have hapos : 0 < A 0 := by nlinarith only [hdet',hdpos]
  have ha : A 0=1 := by nlinarith only [hdet',hdpos,hapos]
  have hd : A 3=1 := by simpa only [ha,one_mul] using hdet'
  have hqeq : q 0=q 1 := by
    have hh : (q 0:ℝ)=(q 1:ℝ) := by
      rw [hd,Int.cast_one] at ht'
      have heq := (div_eq_iff (hqr 0).ne').mp ht'.symm
      simpa only [one_mul] using heq.symm
    exact_mod_cast hh
  have hmap' : (e 0:ℝ)/q 0+A 1=(e 1:ℝ)/q 0 := by
    simpa only [ha,hd,hc,Int.cast_one,Int.cast_zero,zero_mul,zero_add,
      one_mul,div_one,←hqeq] using hmap
  have he : (e 1:ℝ)=(e 0:ℝ)+(A 1:ℝ)*q 0 := by
    have hh := (eq_div_iff (hqr 0).ne').mp hmap'
    rw [add_mul,div_mul_cancel₀ _ (hqr 0).ne'] at hh
    exact hh.symm
  refine ⟨ha,hd,hc,hqeq,?_⟩
  exact_mod_cast he

example
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K N R : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hN : 0 < N)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2)) :
    let V := 1+R^4/(6*N^2)
    1 ≤ V ∧ (|Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V) →
      A 0=1 ∧ A 3=1 ∧ A 2=0 ∧ q 0=q 1 ∧ e 1=e 0+A 1*q 0) :=
  HuxleyBoundaryCoverScratch.fourier_matrix_constructed_upper_triangular_narrowing q e vinv A (Q:=Q) (K:=K) (N:=N) (R:=R) hq hK hN hmesh hband hinv hdet ht hmap hgamma

#print axioms fourier_matrix_constructed_upper_triangular_narrowing


/-- Two comparisons with one reference phase and one target Farey chart
are evaluated at the SAME middle point.  The common matrix weight cancels.
The quartic residuals, not an improved Third Condition, are hypotheses. -/
private theorem positive_difference_shared_chart_quartic_parameter_gap
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (Fsrc : ℝ → ℝ) (η Tsrc : ℝ) (yp : Fin 3 → ℝ)
      (x : Fin 8 → ℝ) (A : Fin 3 → ℤ) (W x₀ : Fin 3 → ℝ)
      (curve : ℝ → Fin 3 → ℝ) (e r v s α β : Fin 2 → ℝ)
      {σ δ T M N R L d K nSpan : ℝ},
      0 < η → η ≤ 1/8 → (∀ i, yp i ∈ Icc (1:ℝ) 2) → |yp 2-yp 1| < a →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      0 < Tsrc → 2 ≤ M →
      let F := fun (i : Fin 3) u =>
        (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
      (0 < σ) → (δ ≤ min (modelPhaseThirdLower σ) 1) →
      (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
      0 < T → 0 < N → 1 ≤ R → 0 < L → (L*N)^2 ≤ M*R → 0 < d → 0 ≤ K →
      (∀ i, M ≤ A i) → (∀ i, A i+W i ≤ 2*M) →
      (∀ i, x₀ i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ z ∈ Icc (x 0) (x 7), ∀ i, curve z i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ i, r i ≠ 0) → (∀ i, v i*r i-e i*s i=1) →
      (∀ z ∈ Icc (x 0) (x 7), ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d) →
      StrictMono x → L*N ≤ nSpan → nSpan^3 ≤ M*R^2 →
      (∀ y ∈ Icc (x 0) (x 7), ∀ z ∈ Icc (x 0) (x 7), ∀ i,
        |(round (curve y i):ℝ)-(round (curve z i):ℝ)| ≤ nSpan) →
      let tag := fun i : Fin 3 => (if i=0 then 0 else 1 : Fin 2)
      let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
      let n := fun z i => (round (curve z i):ℝ)-(round (x₀ i):ℝ)
      let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
      let nu := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
      let g := fun j : Fin 2 => rationalPhase (mu 0) (r 0) (s 0) (mu j.succ) (r 1) (s 1)
      let H := fun j : Fin 2 => quarticPhase (mu 0) (nu 0) (r 0) (s 0)
        (mu j.succ) (nu j.succ) (r 1) (s 1)
      let G := minorArcCoordinate (mu 0) (r 0) (s 0)
      (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e (tag i)/r (tag i)) →
      (∀ z ∈ Icc (x 0) (x 7), ∀ i, iteratedDeriv 2 (f i) (curve z i)/2=
        (e (tag i)*z+v (tag i))/(r (tag i)*z+s (tag i))) →
      (∀ z ∈ Icc (x 0) (x 7), ∀ i, |n z i|^2 ≤ M*R) →
      (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
      (∀ j : Fin 2, ∀ k : Fin 8,
        |α j*x k+β j-g j (x k)+H j (x k)| ≤ K*R^2/|r 0*G (x k)|) →
      let κ := modelPhaseThirdLower σ
      let Γ := (σ*(σ+1)+1)/κ
      let Cmid := Γ^2*(Γ*(32*K+9*quarticReciprocalConstant σ δ))+
        2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ
      |yp 2-yp 1| ≤ C*(16*Γ*Cmid+1)*R^2/(L^2*N^2) := by
  obtain ⟨a,C,ha,hacap,hC,hpair⟩ :=
    positive_difference_physical_identity_pair_compression hσsrc hcsrc hUsrc
  refine ⟨a,C,ha,hacap,hC,?_⟩
  intro Fsrc η Tsrc yp x A W x₀ curve e r v s α β σ δ T M N R L d K nSpan
    hη hηmax hyp hclose hreg hbound htests hTsrc hMtwo F hσ hδ hF
    hT hN hR hL hNL hd hK hA hW hx₀ hcurve hr hdet hden hmono hsize hcube hwindow
    tag f n mu nu g H G hbase hpoint hsquare hspacing hres κ Γ Cmid
  have hM : 0 < M := by linarith only [hMtwo]
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hΓ : 0 < Γ := by dsimp only [Γ]; positivity
  let p := fun j : Fin 2 => (![0,j.succ] : Fin 2 → Fin 3)
  have htag j i : tag (p j i)=i := by fin_cases j <;> fin_cases i <;> rfl
  let munew := fun z i => iteratedDeriv 3 (f i) (round (curve z i))/6
  let D := fun z i => r i*z+s i
  have hmiddle (j : Fin 2) :
      ∀ z ∈ Icc (x 3) (x 4),
        |munew z j.succ*(D z 1)^3/(munew z 0*(D z 0)^3)-1| ≤
          Cmid*R^2/(L^2*N^2) := by
    have hh := physicalModelPhase_quartic_middle_third_condition
      (F:=fun i => F (p j i)) (A:=fun i => (A (p j i):ℝ))
      (W:=fun i => W (p j i)) (x₀:=fun i => x₀ (p j i))
      (x₁:=fun z i => curve z (p j i)) (e:=e) (r:=r) (v:=v) (s:=s)
      (α:=α j) (β:=β j) x hσ hδ (fun i => hF (p j i))
      hT hM hN hR hL hNL hd hK (fun i => hA (p j i)) (fun i => hW (p j i))
      (fun i => hx₀ (p j i)) (fun z hz i => hcurve z hz (p j i)) hr hdet
      (fun z hz i => (hden z hz i).1) (fun z hz i => (hden z hz i).2) hmono
      hsize hcube (fun y hy z hz i => hwindow y hy z hz (p j i))
      (fun i => by simpa only [htag] using hbase (p j i))
      (fun z hz i => by simpa only [htag] using hpoint z hz (p j i))
      (fun z hz i => hsquare z hz (p j i)) hspacing (hres j)
    exact hh
  let z := x 3
  have hzmid : z ∈ Icc (x 3) (x 4) := ⟨le_rfl,hmono.monotone (by decide)⟩
  have hz : z ∈ Icc (x 0) (x 7) :=
    ⟨hmono.monotone (by decide),hmono.monotone (by decide)⟩
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hb i := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hcurve z hz i)
  have hcoef i := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i)
    hT hM (hA i) (hW i) (hb i).1
  have hmupos i : 0 < munew z i :=
    lt_of_lt_of_le (by positivity : 0 < κ*T/(6*M^3)) (hcoef i).1
  have hmule i j : munew z i ≤ Γ*munew z j := by
    calc
      _ ≤ (σ*(σ+1)+1)*T/(6*M^3) := (hcoef i).2
      _ = Γ*(κ*T/(6*M^3)) := by dsimp only [Γ]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcoef j).1 hΓ.le
  have hdpos i : 0 < D z i := hd.trans_le (hden z hz i).1
  have hweight i j k l :
      0 < munew z i*(D z k)^3/(munew z j*(D z l)^3) ∧
      munew z i*(D z k)^3/(munew z j*(D z l)^3) ≤ 8*Γ := by
    have hdl : D z k ≤ 2*D z l := by
      have hhi := (hden z hz k).2
      have hlo := (hden z hz l).1
      change D z k ≤ 2*d at hhi
      change d ≤ D z l at hlo
      linarith only [hhi,hlo]
    have hdenpos := mul_pos (hmupos j) (pow_pos (hdpos l) 3)
    refine ⟨div_pos (mul_pos (hmupos i) (pow_pos (hdpos k) 3)) hdenpos,
      (div_le_iff₀ hdenpos).mpr ?_⟩
    calc
      _ ≤ (Γ*munew z j)*(2*D z l)^3 :=
        mul_le_mul (hmule i j) (pow_le_pow_left₀ (hdpos k).le hdl 3)
          (pow_nonneg (hdpos k).le 3) (mul_nonneg hΓ.le (hmupos j).le)
      _ = _ := by ring
  have hthird : |munew z 2/munew z 1-1| ≤
      16*Γ*Cmid*R^2/(L^2*N^2) := by
    have hfirst : |munew z 1*(D z 1)^3/(munew z 0*(D z 0)^3)-1| ≤
        Cmid*R^2/(L^2*N^2) := hmiddle 0 z hzmid
    have hsecond : |munew z 2*(D z 1)^3/(munew z 0*(D z 0)^3)-1| ≤
        Cmid*R^2/(L^2*N^2) := hmiddle 1 z hzmid
    have hinv : 1/(munew z 1*(D z 1)^3/(munew z 0*(D z 0)^3)) ≤ 8*Γ := by
      rw [one_div_div]
      exact (hweight 0 1 0 1).2
    have hh := ratio_relative_perturbation_of_inverse_bound
      (hweight 1 0 1 0).1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hΓ.le)
      (a:=1) (ε:=0) (by norm_num) hsecond hfirst
      (by rw [abs_of_pos (hweight 2 0 1 0).1]; exact (hweight 2 0 1 0).2) hinv
    have he : (1:ℝ)*(munew z 2*(D z 1)^3/(munew z 0*(D z 0)^3))/
        (munew z 1*(D z 1)^3/(munew z 0*(D z 0)^3)) = munew z 2/munew z 1 := by
      field_simp [(hmupos 0).ne',(hmupos 1).ne',(hdpos 0).ne',(hdpos 1).ne']
    rw [he] at hh
    convert hh using 1
    ring
  let Src := fun y w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
  have hsource i : f i=fun w => Src (yp i) ((A i:ℝ)+w) := by
    funext w
    dsimp only [f,heathBrownPhysicalPhase,F,Src]
    field_simp
  have hjet i k t : iteratedDeriv k (f i) t =
      iteratedDeriv k (Src (yp i)) ((A i:ℝ)+t) := by
    rw [hsource,iteratedDeriv_comp_const_add]
  have hround i k t : iteratedDeriv k (f i) (round t) =
      iteratedDeriv k (Src (yp i)) (round ((A i:ℝ)+t)) := by
    rw [hjet,round_intCast_add,Int.cast_add]
  have hphysical i : (A i:ℝ)+curve z i ∈ Icc M (2*M) :=
    ⟨by linarith only [hA i,(hcurve z hz i).1],
     by linarith only [hW i,(hcurve z hz i).2]⟩
  have hlevel : iteratedDeriv 2 (Src (yp 2)) ((A 2:ℝ)+curve z 2)/2 =
      iteratedDeriv 2 (Src (yp 1)) ((A 1:ℝ)+curve z 1)/2 := by
    rw [←hjet 2 2,←hjet 1 2,hpoint z hz 2,hpoint z hz 1]
    rfl
  have hthird' :
      |(iteratedDeriv 3 (Src (yp 2)) (round ((A 2:ℝ)+curve z 2))/6)/
        (iteratedDeriv 3 (Src (yp 1)) (round ((A 1:ℝ)+curve z 1))/6)-1| ≤
          16*Γ*Cmid*R^2/(L^2*N^2) := by
    rw [←hround 2 3,←hround 1 3]
    exact hthird
  have hΔ : 0 ≤ 16*Γ*Cmid*R^2/(L^2*N^2) := (abs_nonneg _).trans hthird
  have hgap := hpair Fsrc η ((A 1:ℝ)+curve z 1) ((A 2:ℝ)+curve z 2)
    (yp 1) (yp 2) Tsrc M (16*Γ*Cmid*R^2/(L^2*N^2))
    hη hηmax hTsrc hMtwo hΔ (hphysical 1) (hphysical 2) (hyp 1) (hyp 2)
    hclose hreg hbound htests hlevel hthird'
  have habsorb : 1/M ≤ R^2/(L^2*N^2) := by
    apply (div_le_div_iff₀ hM (by positivity : 0 < L^2*N^2)).mpr
    have hR2 : R ≤ R^2 := by nlinarith only [hR]
    have hh := mul_le_mul_of_nonneg_left hR2 hM.le
    nlinarith only [hNL,hh]
  calc
    _ ≤ C*(16*Γ*Cmid*R^2/(L^2*N^2)+1/M) := hgap
    _ ≤ C*(16*Γ*Cmid*R^2/(L^2*N^2)+R^2/(L^2*N^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl habsorb) hC.le
    _ = _ := by ring

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (Fsrc : ℝ → ℝ) (η Tsrc : ℝ) (yp : Fin 3 → ℝ)
      (x : Fin 8 → ℝ) (A : Fin 3 → ℤ) (W x₀ : Fin 3 → ℝ)
      (curve : ℝ → Fin 3 → ℝ) (e r v s α β : Fin 2 → ℝ)
      {σ δ T M N R L d K nSpan : ℝ},
      0 < η → η ≤ 1/8 → (∀ i, yp i ∈ Icc (1:ℝ) 2) → |yp 2-yp 1| < a →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
      (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
      0 < Tsrc → 2 ≤ M →
      let F := fun (i : Fin 3) u =>
        (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
      (0 < σ) → (δ ≤ min (modelPhaseThirdLower σ) 1) →
      (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
      0 < T → 0 < N → 1 ≤ R → 0 < L → (L*N)^2 ≤ M*R → 0 < d → 0 ≤ K →
      (∀ i, M ≤ A i) → (∀ i, A i+W i ≤ 2*M) →
      (∀ i, x₀ i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ z ∈ Icc (x 0) (x 7), ∀ i, curve z i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ i, r i ≠ 0) → (∀ i, v i*r i-e i*s i=1) →
      (∀ z ∈ Icc (x 0) (x 7), ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d) →
      StrictMono x → L*N ≤ nSpan → nSpan^3 ≤ M*R^2 →
      (∀ y ∈ Icc (x 0) (x 7), ∀ z ∈ Icc (x 0) (x 7), ∀ i,
        |(round (curve y i):ℝ)-(round (curve z i):ℝ)| ≤ nSpan) →
      let tag := fun i : Fin 3 => (if i=0 then 0 else 1 : Fin 2)
      let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
      let n := fun z i => (round (curve z i):ℝ)-(round (x₀ i):ℝ)
      let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
      let nu := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
      let g := fun j : Fin 2 => rationalPhase (mu 0) (r 0) (s 0) (mu j.succ) (r 1) (s 1)
      let H := fun j : Fin 2 => quarticPhase (mu 0) (nu 0) (r 0) (s 0)
        (mu j.succ) (nu j.succ) (r 1) (s 1)
      let G := minorArcCoordinate (mu 0) (r 0) (s 0)
      (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e (tag i)/r (tag i)) →
      (∀ z ∈ Icc (x 0) (x 7), ∀ i, iteratedDeriv 2 (f i) (curve z i)/2=
        (e (tag i)*z+v (tag i))/(r (tag i)*z+s (tag i))) →
      (∀ z ∈ Icc (x 0) (x 7), ∀ i, |n z i|^2 ≤ M*R) →
      (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
      (∀ j : Fin 2, ∀ k : Fin 8,
        |α j*x k+β j-g j (x k)+H j (x k)| ≤ K*R^2/|r 0*G (x k)|) →
      let κ := modelPhaseThirdLower σ
      let Γ := (σ*(σ+1)+1)/κ
      let Cmid := Γ^2*(Γ*(32*K+9*quarticReciprocalConstant σ δ))+
        2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ
      |yp 2-yp 1| ≤ C*(16*Γ*Cmid+1)*R^2/(L^2*N^2) :=
  HuxleyBoundaryCoverScratch.positive_difference_shared_chart_quartic_parameter_gap (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


#print axioms positive_difference_shared_chart_quartic_parameter_gap



/-- Joint coefficient selection for TWO actual quartic comparisons.
The eight nodes and their occupied rank gaps are constructed, not supplied.
The input set consists of points common to the two curvature cells. -/
private theorem quartic_two_comparisons_common_coefficient_samples
    (S : Finset ℕ) (y : ℕ → ℝ) (hS : 2592 ≤ S.card)
    (mu nu : Fin 3 → ℝ) (r s U l w x₀ ac bc : Fin 2 → ℝ) (k : Fin 2 → Fin 17)
    (hmu : ∀ i, mu i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hden : ∀ j, ∀ z ∈ Icc (l j) (w j), ∀ i, r i*z+s i ≠ 0)
    (hwidth : ∀ j, U j*(w j-l j) ≤ 1/2)
    (hheight : ∀ j, U j*(w j-l j)*(max |l j| |w j|+(w j-l j)/2) ≤ 1/2) :
    let g := fun j : Fin 2 => rationalPhase (mu 0) (r 0) (s 0) (mu j.succ) (r 1) (s 1)
    let H := fun j : Fin 2 => quarticPhase (mu 0) (nu 0) (r 0) (s 0)
      (mu j.succ) (nu j.succ) (r 1) (s 1)
    let phi := fun j z => g j z-H j z
    let Z := fun j : Fin 2 => quarticCurvatureBoundaryRoots
      (mu 0) (nu 0) (r 0) (s 0) (mu j.succ) (nu j.succ) (r 1) (s 1) (U j)
    (∀ j, x₀ j ∈ finiteBoundaryCell (Z j) (l j) (w j) (k j)) →
    (∀ j, ∀ i ∈ S, y i ∈ finiteBoundaryCell (Z j) (l j) (w j) (k j)) →
    (∀ j, |iteratedDeriv 2 (g j) (x₀ j)-iteratedDeriv 2 (H j) (x₀ j)| ≤ U j) →
    ∃ (a b : Fin 2 → ℤ) (idx : Fin 8 → ℕ), StrictMono idx ∧
      (∀ j i, idx i ∈ S ∧ round (ac j-deriv (phi j) (y (idx i)))=a j ∧
        round (bc j-phi j (y (idx i))+y (idx i)*deriv (phi j) (y (idx i)))=b j) ∧
      (∀ i : Fin 7, (S.card:ℝ)/1296 ≤ (idx i.succ:ℝ)-(idx i.castSucc:ℝ)-1) ∧
      ∀ i : Fin 7, (S.card:ℝ)/1296 ≤
        ((S.filter (fun n => idx i.castSucc<n ∧ n < idx i.succ)).card:ℝ) := by
  classical
  intro g H phi Z hx₀ hy hcurv
  let color := fun i => (round (ac 0-deriv (phi 0) (y i)),
    round (bc 0-phi 0 (y i)+y i*deriv (phi 0) (y i)))
  let Colors := S.image color
  have hcolors : Colors.card ≤ 9 :=
    quartic_phase_coefficient_color_count S y (hmu 0) (hmu 1) (hr 0) (hr 1)
      (fun z hz => hden 0 z hz 0) (fun z hz => hden 0 z hz 1)
      (hwidth 0) (hheight 0) (hx₀ 0) (hy 0) (hcurv 0)
  have hne : Colors.Nonempty := (Finset.card_pos.mp (by omega : 0 < S.card)).image color
  have hbudget : Colors.card • ((S.card:ℝ)/9) ≤ (S.card:ℝ) := by
    rw [nsmul_eq_mul]
    have hh : (Colors.card:ℝ) ≤ 9 := by exact_mod_cast hcolors
    nlinarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg S.card : (0:ℝ) ≤ S.card)]
  obtain ⟨c,_hc,hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (fun i hi => Finset.mem_image_of_mem color hi) hne hbudget
  let V := S.filter (fun i => color i=c)
  have hlargeR : (S.card:ℝ) ≤ 9*(V.card:ℝ) := by
    change (S.card:ℝ)/9 ≤ (V.card:ℝ) at hlarge
    linarith only [hlarge]
  have hlargeN : S.card ≤ 9*V.card := by exact_mod_cast hlargeR
  have hV : 288 ≤ V.card := by omega
  have hVS : V ⊆ S := Finset.filter_subset _ _
  obtain ⟨a₁,b₁,idx,hidx,hcoeff,hgap,hmass⟩ :=
    quartic_phase_common_coefficient_windows_with_mass V y hV
      (hmu 0) (hmu 2) (hr 0) (hr 1)
      (fun z hz => hden 1 z hz 0) (fun z hz => hden 1 z hz 1)
      (hwidth 1) (hheight 1) (hx₀ 1) (fun i hi => hy 1 i (hVS hi)) (hcurv 1)
  refine ⟨![c.1,a₁],![c.2,b₁],idx,hidx,?_,?_,?_⟩
  · intro j i
    have hi := hcoeff i
    have hci := Finset.mem_filter.mp hi.1
    fin_cases j
    · exact ⟨hci.1,congrArg Prod.fst hci.2,congrArg Prod.snd hci.2⟩
    · exact ⟨hci.1,hi.2.1,hi.2.2⟩
  · intro i
    linarith only [hlargeR,hgap i]
  · intro i
    have hsub : V.filter (fun n => idx i.castSucc<n ∧ n < idx i.succ) ⊆
        S.filter (fun n => idx i.castSucc<n ∧ n < idx i.succ) :=
      Finset.filter_subset_filter _ hVS
    have hh : ((V.filter (fun n => idx i.castSucc<n ∧ n < idx i.succ)).card:ℝ) ≤
        ((S.filter (fun n => idx i.castSucc<n ∧ n < idx i.succ)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    linarith only [hlargeR,hmass i,hh]

example
    (S : Finset ℕ) (y : ℕ → ℝ) (hS : 2592 ≤ S.card)
    (mu nu : Fin 3 → ℝ) (r s U l w x₀ ac bc : Fin 2 → ℝ) (k : Fin 2 → Fin 17)
    (hmu : ∀ i, mu i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hden : ∀ j, ∀ z ∈ Icc (l j) (w j), ∀ i, r i*z+s i ≠ 0)
    (hwidth : ∀ j, U j*(w j-l j) ≤ 1/2)
    (hheight : ∀ j, U j*(w j-l j)*(max |l j| |w j|+(w j-l j)/2) ≤ 1/2) :
    let g := fun j : Fin 2 => rationalPhase (mu 0) (r 0) (s 0) (mu j.succ) (r 1) (s 1)
    let H := fun j : Fin 2 => quarticPhase (mu 0) (nu 0) (r 0) (s 0)
      (mu j.succ) (nu j.succ) (r 1) (s 1)
    let phi := fun j z => g j z-H j z
    let Z := fun j : Fin 2 => quarticCurvatureBoundaryRoots
      (mu 0) (nu 0) (r 0) (s 0) (mu j.succ) (nu j.succ) (r 1) (s 1) (U j)
    (∀ j, x₀ j ∈ finiteBoundaryCell (Z j) (l j) (w j) (k j)) →
    (∀ j, ∀ i ∈ S, y i ∈ finiteBoundaryCell (Z j) (l j) (w j) (k j)) →
    (∀ j, |iteratedDeriv 2 (g j) (x₀ j)-iteratedDeriv 2 (H j) (x₀ j)| ≤ U j) →
    ∃ (a b : Fin 2 → ℤ) (idx : Fin 8 → ℕ), StrictMono idx ∧
      (∀ j i, idx i ∈ S ∧ round (ac j-deriv (phi j) (y (idx i)))=a j ∧
        round (bc j-phi j (y (idx i))+y (idx i)*deriv (phi j) (y (idx i)))=b j) ∧
      (∀ i : Fin 7, (S.card:ℝ)/1296 ≤ (idx i.succ:ℝ)-(idx i.castSucc:ℝ)-1) ∧
      ∀ i : Fin 7, (S.card:ℝ)/1296 ≤
        ((S.filter (fun n => idx i.castSucc<n ∧ n < idx i.succ)).card:ℝ) :=
  HuxleyBoundaryCoverScratch.quartic_two_comparisons_common_coefficient_samples S y hS mu nu r s U l w x₀ ac bc k hmu hr hden hwidth hheight


#print axioms quartic_two_comparisons_common_coefficient_samples


/-- The two-comparison selector applied to actual physical windows derives
the common physical and minor-arc-coordinate spacing from the source model. -/
private theorem physical_two_comparisons_common_samples
    (S : Finset ℕ) (y xpos : ℕ → ℝ) (hS : 2592 ≤ S.card)
    (mu nu : Fin 3 → ℝ) (r s U l w x₀ ac bc : Fin 2 → ℝ) (k : Fin 2 → Fin 17)
    {σ δ T M A W step base e v : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hmu0 : 0 < mu 0)
    (hmu : ∀ i, mu i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hdet : v*r 0-e*s 0=1)
    (hden : ∀ j, ∀ z ∈ Icc (l j) (w j), ∀ i, 0 < r i*z+s i)
    (hwidth : ∀ j, U j*(w j-l j) ≤ 1/2)
    (hheight : ∀ j, U j*(w j-l j)*(max |l j| |w j|+(w j-l j)/2) ≤ 1/2)
    (hx : ∀ i ∈ S, xpos i ∈ Ioo 0 W)
    (hwindow : ∀ i ∈ S, xpos i ∈ Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let f := heathBrownPhysicalPhase F T M A 1
    let g := fun j : Fin 2 => rationalPhase (mu 0) (r 0) (s 0) (mu j.succ) (r 1) (s 1)
    let H := fun j : Fin 2 => quarticPhase (mu 0) (nu 0) (r 0) (s 0)
      (mu j.succ) (nu j.succ) (r 1) (s 1)
    let phi := fun j z => g j z-H j z
    let Z := fun j : Fin 2 => quarticCurvatureBoundaryRoots
      (mu 0) (nu 0) (r 0) (s 0) (mu j.succ) (nu j.succ) (r 1) (s 1) (U j)
    (∀ i ∈ S, iteratedDeriv 2 f (xpos i)/2=(e*y i+v)/(r 0*y i+s 0)) →
    (∀ j, x₀ j ∈ finiteBoundaryCell (Z j) (l j) (w j) (k j)) →
    (∀ j, ∀ i ∈ S, y i ∈ finiteBoundaryCell (Z j) (l j) (w j) (k j)) →
    (∀ j, |iteratedDeriv 2 (g j) (x₀ j)-iteratedDeriv 2 (H j) (x₀ j)| ≤ U j) →
    ∃ (a b : Fin 2 → ℤ) (idx : Fin 8 → ℕ), StrictMono idx ∧
      (∀ j i, idx i ∈ S ∧ round (ac j-deriv (phi j) (y (idx i)))=a j ∧
        round (bc j-phi j (y (idx i))+y (idx i)*deriv (phi j) (y (idx i)))=b j) ∧
      StrictAnti (fun i => y (idx i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/1296 ≤ xpos (idx i.succ)-xpos (idx i.castSucc)) ∧
      (∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*mu 0*M^3)*(step*(S.card:ℝ)/1296) ≤
        minorArcCoordinate (mu 0) (r 0) (s 0) (y (idx i.succ))-
        minorArcCoordinate (mu 0) (r 0) (s 0) (y (idx i.castSucc))) ∧
      (∀ i : Fin 7, (S.card:ℝ)/1296 ≤
        ((S.filter (fun n => idx i.castSucc<n ∧ n < idx i.succ)).card:ℝ)) ∧
      AntitoneOn y (S:Set ℕ) := by
  classical
  intro f g H phi Z hroot hx₀ hy hcurv
  obtain ⟨a,b,idx,hidx,hcoeff,hgap,hmass⟩ :=
    quartic_two_comparisons_common_coefficient_samples S y hS mu nu r s U l w x₀ ac bc k
      hmu hr (fun j z hz i => (hden j z hz i).ne') hwidth hheight hx₀ hy hcurv
  have hcount : (0:ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hcoef : 0 < modelPhaseThirdLower σ*T/(6*mu 0*M^3) :=
    div_pos (mul_pos (modelPhaseThirdLower_pos hσ) hT) (by positivity)
  have hspace (i : Fin 7) : step*(S.card:ℝ)/1296 ≤ xpos (idx i.succ)-xpos (idx i.castSucc) := by
    have hh := mul_le_mul_of_nonneg_left (hgap i) hstep.le
    have hlo := (hwindow _ (hcoeff 0 i.succ).1).1
    have hhi := (hwindow _ (hcoeff 0 i.castSucc).1).2
    nlinarith only [hh,hlo,hhi]
  have hdAll i (hi : i ∈ S) : 0 < r 0*y i+s 0 := hden 0 _ (hy 0 i hi).1 0
  have hgrowth i (hi : i ∈ S) j (hj : j ∈ S) (hij : xpos i ≤ xpos j) :
      modelPhaseThirdLower σ*T/(6*mu 0*M^3)*(xpos j-xpos i) ≤
        minorArcCoordinate (mu 0) (r 0) (s 0) (y j)-
          minorArcCoordinate (mu 0) (r 0) (s 0) (y i) := by
    have hh := physicalModelPhase_minorArcCoordinate_growth
      ![y i,y j] ![1,1] hσ hδ hF hT hM hA hW (hx i hi) (hx j hj) hij hmu0 (hr 0)
      (by intro n; fin_cases n <;> norm_num)
      (by
        intro n
        fin_cases n
        · change r 0*y i+s 0*1 ≠ 0
          simpa only [mul_one] using (hdAll i hi).ne'
        · change r 0*y j+s 0*1 ≠ 0
          simpa only [mul_one] using (hdAll j hj).ne')
      hdet
      (by simpa only [Matrix.cons_val_zero,mul_one] using hroot i hi)
      (by simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,mul_one] using hroot j hj)
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,div_one] using hh
  have hG (i : Fin 7) : modelPhaseThirdLower σ*T/(6*mu 0*M^3)*(step*(S.card:ℝ)/1296) ≤
      minorArcCoordinate (mu 0) (r 0) (s 0) (y (idx i.succ))-
        minorArcCoordinate (mu 0) (r 0) (s 0) (y (idx i.castSucc)) := by
    have hpos : 0 < step*(S.card:ℝ)/1296 := by positivity
    exact (mul_le_mul_of_nonneg_left (hspace i) hcoef.le).trans
      (hgrowth _ (hcoeff 0 i.castSucc).1 _ (hcoeff 0 i.succ).1
        (by linarith only [hspace i,hpos]))
  have hanti : AntitoneOn y (S:Set ℕ) := by
    intro i hi j hj hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    have hstepR : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have horder : xpos i ≤ xpos j := by
      have hh := mul_le_mul_of_nonneg_left hstepR hstep.le
      linarith only [hh,(hwindow i hi).2,(hwindow j hj).1]
    have hh := (mul_nonneg hcoef.le (sub_nonneg.mpr horder)).trans (hgrowth i hi j hj horder)
    rw [minorArcCoordinate_difference hmu0.ne' (hr 0) (hdAll i hi).ne' (hdAll j hj).ne'] at hh
    have hn := (le_div_iff₀ (show 0 < 3*mu 0*(r 0*y j+s 0)*(r 0*y i+s 0) by
      exact mul_pos (mul_pos (mul_pos (by norm_num) hmu0) (hdAll j hj)) (hdAll i hi))).mp hh
    linarith only [hn]
  refine ⟨a,b,idx,hidx,hcoeff,?_,hspace,hG,hmass,hanti⟩
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  have hh := lt_of_lt_of_le
    (mul_pos hcoef (div_pos (mul_pos hstep hcount) (by norm_num))) (hG i)
  rw [minorArcCoordinate_difference hmu0.ne' (hr 0)
    (hdAll _ (hcoeff 0 i.castSucc).1).ne' (hdAll _ (hcoeff 0 i.succ).1).ne'] at hh
  have hn := (div_pos_iff_of_pos_right
    (show 0 < 3*mu 0*(r 0*y (idx i.succ)+s 0)*(r 0*y (idx i.castSucc)+s 0) by
      exact mul_pos (mul_pos (mul_pos (by norm_num) hmu0)
        (hdAll _ (hcoeff 0 i.succ).1)) (hdAll _ (hcoeff 0 i.castSucc).1))).mp hh
  linarith only [hn]

example
    (S : Finset ℕ) (y xpos : ℕ → ℝ) (hS : 2592 ≤ S.card)
    (mu nu : Fin 3 → ℝ) (r s U l w x₀ ac bc : Fin 2 → ℝ) (k : Fin 2 → Fin 17)
    {σ δ T M A W step base e v : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hmu0 : 0 < mu 0)
    (hmu : ∀ i, mu i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (hdet : v*r 0-e*s 0=1)
    (hden : ∀ j, ∀ z ∈ Icc (l j) (w j), ∀ i, 0 < r i*z+s i)
    (hwidth : ∀ j, U j*(w j-l j) ≤ 1/2)
    (hheight : ∀ j, U j*(w j-l j)*(max |l j| |w j|+(w j-l j)/2) ≤ 1/2)
    (hx : ∀ i ∈ S, xpos i ∈ Ioo 0 W)
    (hwindow : ∀ i ∈ S, xpos i ∈ Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let f := heathBrownPhysicalPhase F T M A 1
    let g := fun j : Fin 2 => rationalPhase (mu 0) (r 0) (s 0) (mu j.succ) (r 1) (s 1)
    let H := fun j : Fin 2 => quarticPhase (mu 0) (nu 0) (r 0) (s 0)
      (mu j.succ) (nu j.succ) (r 1) (s 1)
    let phi := fun j z => g j z-H j z
    let Z := fun j : Fin 2 => quarticCurvatureBoundaryRoots
      (mu 0) (nu 0) (r 0) (s 0) (mu j.succ) (nu j.succ) (r 1) (s 1) (U j)
    (∀ i ∈ S, iteratedDeriv 2 f (xpos i)/2=(e*y i+v)/(r 0*y i+s 0)) →
    (∀ j, x₀ j ∈ finiteBoundaryCell (Z j) (l j) (w j) (k j)) →
    (∀ j, ∀ i ∈ S, y i ∈ finiteBoundaryCell (Z j) (l j) (w j) (k j)) →
    (∀ j, |iteratedDeriv 2 (g j) (x₀ j)-iteratedDeriv 2 (H j) (x₀ j)| ≤ U j) →
    ∃ (a b : Fin 2 → ℤ) (idx : Fin 8 → ℕ), StrictMono idx ∧
      (∀ j i, idx i ∈ S ∧ round (ac j-deriv (phi j) (y (idx i)))=a j ∧
        round (bc j-phi j (y (idx i))+y (idx i)*deriv (phi j) (y (idx i)))=b j) ∧
      StrictAnti (fun i => y (idx i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/1296 ≤ xpos (idx i.succ)-xpos (idx i.castSucc)) ∧
      (∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*mu 0*M^3)*(step*(S.card:ℝ)/1296) ≤
        minorArcCoordinate (mu 0) (r 0) (s 0) (y (idx i.succ))-
        minorArcCoordinate (mu 0) (r 0) (s 0) (y (idx i.castSucc))) ∧
      (∀ i : Fin 7, (S.card:ℝ)/1296 ≤
        ((S.filter (fun n => idx i.castSucc<n ∧ n < idx i.succ)).card:ℝ)) ∧
      AntitoneOn y (S:Set ℕ) :=
  HuxleyBoundaryCoverScratch.physical_two_comparisons_common_samples S y xpos hS mu nu r s U l w x₀ ac bc k (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (step:=step) (base:=base) (e:=e) (v:=v) (F:=F) hσ hδ hF hT hM hA hW hstep hmu0 hmu hr hdet hden hwidth hheight hx hwindow


#print axioms physical_two_comparisons_common_samples


/-- Actual common occupied windows construct the eight joint samples and
all three root curves before the shared-chart vertical comparison is applied.
The two curvature cells and their measured residuals remain upstream inputs. -/
private theorem positive_difference_common_occupied_quartic_parameter_gap
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (Fsrc : ℝ → ℝ) (η Tsrc : ℝ) (yp : Fin 3 → ℝ)
      (S : Finset ℕ) (y : ℕ → ℝ) (xp : ℕ → Fin 3 → ℝ)
      (A : Fin 3 → ℤ) (W xref Hspan : Fin 3 → ℝ)
      (e r v s U l w y₀ ac bc : Fin 2 → ℝ) (cell : Fin 2 → Fin 17)
      {σ δ T M N R d K nSpan base : ℝ},
      0 < η → η ≤ 1/8 → (∀ i, yp i ∈ Icc (1:ℝ) 2) → |yp 2-yp 1| < a →
      (∀ t, 0 < t → ContDiffAt ℝ ∞ Fsrc t) →
      (∀ t ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc t| ≤ Usrc) →
      (∀ t ∈ Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc t) j|) →
      0 < Tsrc → 2 ≤ M → 2592 ≤ S.card →
      let F := fun (i : Fin 3) u =>
        (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
      (0 < σ) → (δ ≤ min (modelPhaseThirdLower σ) 1) →
      (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
      0 < T → 0 < N → 1 ≤ R → R ≤ M → 0 < d → 0 ≤ K →
      (∀ i, M ≤ A i) → (∀ i, A i+W i ≤ 2*M) →
      (∀ i, xref i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ n ∈ S, ∀ i, xp n i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ n ∈ S, xp n 0 ∈ Icc (base+N*(n:ℝ)) (base+N*((n:ℝ)+1))) →
      (∀ n ∈ S, ∀ i, |xp n i-xref i| ≤ Hspan i) →
      (∀ i, 2*Hspan i+1 ≤ nSpan) → nSpan^3 ≤ M*R^2 →
      (∀ i, r i ≠ 0) → (∀ i, v i*r i-e i*s i=1) →
      (∀ j, ∀ z ∈ Icc (l j) (w j), ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d) →
      (∀ j, U j*(w j-l j) ≤ 1/2) →
      (∀ j, U j*(w j-l j)*(max |l j| |w j|+(w j-l j)/2) ≤ 1/2) →
      let tag := fun i : Fin 3 => (if i=0 then 0 else 1 : Fin 2)
      let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
      let mu := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
      let nu := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
      let g := fun j : Fin 2 => rationalPhase (mu 0) (r 0) (s 0) (mu j.succ) (r 1) (s 1)
      let H := fun j : Fin 2 => quarticPhase (mu 0) (nu 0) (r 0) (s 0)
        (mu j.succ) (nu j.succ) (r 1) (s 1)
      let phi := fun j z => g j z-H j z
      let G := minorArcCoordinate (mu 0) (r 0) (s 0)
      let Z := fun j : Fin 2 => quarticCurvatureBoundaryRoots
        (mu 0) (nu 0) (r 0) (s 0) (mu j.succ) (nu j.succ) (r 1) (s 1) (U j)
      (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e (tag i)/r (tag i)) →
      (∀ n ∈ S, ∀ i, iteratedDeriv 2 (f i) (xp n i)/2=
        (e (tag i)*y n+v (tag i))/(r (tag i)*y n+s (tag i))) →
      (∀ j, y₀ j ∈ finiteBoundaryCell (Z j) (l j) (w j) (cell j)) →
      (∀ j, ∀ n ∈ S, y n ∈ finiteBoundaryCell (Z j) (l j) (w j) (cell j)) →
      (∀ j, |iteratedDeriv 2 (g j) (y₀ j)-iteratedDeriv 2 (H j) (y₀ j)| ≤ U j) →
      (∀ j, ∀ n ∈ S,
        |(ac j-round (ac j-deriv (phi j) (y n)))*y n+
          (bc j-round (bc j-phi j (y n)+y n*deriv (phi j) (y n)))-g j (y n)+H j (y n)| ≤
            K*R^2/|r 0*G (y n)|) →
      let κ := modelPhaseThirdLower σ
      let Γ := (σ*(σ+1)+1)/κ
      let L := κ/(1296*(σ*(σ+1)+1))*(S.card:ℝ)
      let Cmid := Γ^2*(Γ*(32*K+9*quarticReciprocalConstant σ δ))+
        2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ
      |yp 2-yp 1| ≤ C*(16*Γ*Cmid+1)*R^2/(L^2*N^2) := by
  obtain ⟨a,C,ha,hacap,hC,hgapFn⟩ :=
    positive_difference_shared_chart_quartic_parameter_gap hσsrc hcsrc hUsrc
  refine ⟨a,C,ha,hacap,hC,?_⟩
  intro Fsrc η Tsrc yp S y xp A W xref Hspan e r v s U l w y₀ ac bc cell
    σ δ T M N R d K nSpan base hη hηmax hyp hclose hreg hbound htests hTsrc hMtwo hS
    F hσ hδ hF hT hN hR hRM hd hK hA hW hxref hxp hwindow hdisplacement hspan
    hcube hr hdet hden hwidth hheight tag f mu nu g H phi G Z hbase hpoint
    hy₀ hy hcurv hres κ Γ L Cmid
  have hM : 0 < M := by linarith only [hMtwo]
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hcount : (0:ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hCphys : 0 < σ*(σ+1)+1 := by positivity
  have hL : 0 < L := mul_pos (div_pos hκ (mul_pos (by norm_num) hCphys)) hcount
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hround i := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hxref i)
  have hμbounds i := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i)
    hT hM (hA i) (hW i) (hround i).1
  have hμpos i : 0 < mu i := lt_of_lt_of_le (by positivity) (hμbounds i).1
  obtain ⟨a₀,b₀,idx,_hidx,hcoeff,hanti,hphys,hG,_hmass,_hantiAll⟩ :=
    physical_two_comparisons_common_samples S y (fun n => xp n 0) hS
      mu nu r s U l w y₀ ac bc cell
      hσ hδ (hF₂ 0) hT hM (hA 0) (hW 0) hN (hμpos 0)
      (fun i => (hμpos i).ne') hr (hdet 0)
      (fun j z hz i => hd.trans_le (hden j z hz i).1) hwidth hheight
      (fun n hn => ⟨by linarith only [(hxp n hn 0).1],by linarith only [(hxp n hn 0).2]⟩)
      hwindow (fun n hn => hpoint n hn 0) hy₀ hy hcurv
  have hmem i : idx i ∈ S := (hcoeff 0 i).1
  have hHspan i : 0 ≤ Hspan i := (abs_nonneg _).trans (hdisplacement _ (hmem 0) i)
  have hn : 0 < nSpan := by linarith only [hHspan 0,hspan 0]
  have hnsquare : nSpan^2 ≤ M*R := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg nSpan) (mul_nonneg hM.le hRpos.le)
      (by norm_num : (3:ℕ) ≠ 0)).mp
    have hh := pow_le_pow_left₀ (pow_nonneg hn.le 3) hcube 2
    have hh' := mul_le_mul_of_nonneg_left hRM (show 0 ≤ M^2*R^3 by positivity)
    nlinarith only [hh,hh']
  have hsquare i : (Hspan i+1)^2 ≤ M*R :=
    (pow_le_pow_left₀ (add_nonneg (hHspan i) zero_le_one)
      (show Hspan i+1 ≤ nSpan by linarith only [hHspan i,hspan i]) 2).trans hnsquare
  have hκle : κ ≤ σ*(σ+1)+1 := by
    have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ (hF₂ 0)
      (by norm_num : (3/2:ℝ) ∈ Ioo 1 2)
    exact hh.1.trans hh.2
  have hLspan : L*N ≤ nSpan := by
    have hh := mul_le_mul_of_nonneg_right ((div_le_one hCphys).mpr hκle)
      (div_pos (mul_pos hN hcount) (by norm_num : (0:ℝ) < 1296)).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/1296) := by
      dsimp only [L]
      field_simp
    rw [←he,one_mul] at hh
    have hp := hphys (0:Fin 7)
    change N*(S.card:ℝ)/1296 ≤ xp (idx 1) 0-xp (idx 0) 0 at hp
    have ht := abs_sub_le (xp (idx 1) 0) (xref 0) (xp (idx 0) 0)
    rw [abs_sub_comm (xref 0)] at ht
    linarith only [hh,hp,le_abs_self (xp (idx 1) 0-xp (idx 0) 0),ht,
      hdisplacement _ (hmem 0) 0,hdisplacement _ (hmem 1) 0,hspan 0]
  have hNL : (L*N)^2 ≤ M*R :=
    (pow_le_pow_left₀ (mul_pos hL hN).le hLspan 2).trans hnsquare
  let z : Fin 8 → ℝ := fun i => y (idx i.rev)
  have hmono : StrictMono z := hanti.comp Fin.rev_strictAnti
  have hz j i : z i ∈ Icc (l j) (w j) := (hy j _ (hmem i.rev)).1
  have hsub j : Icc (z 0) (z 7) ⊆ Icc (l j) (w j) :=
    fun t ht => ⟨(hz j 0).1.trans ht.1,ht.2.trans (hz j 7).2⟩
  have hcoef : κ/(σ*(σ+1)+1) ≤ κ*T/(6*mu 0*M^3) := by
    have hb := (le_div_iff₀ (show 0 < 6*M^3 by positivity)).mp (hμbounds 0).2
    change mu 0*(6*M^3) ≤ (σ*(σ+1)+1)*T at hb
    apply (div_le_div_iff₀ hCphys
      (mul_pos (mul_pos (by norm_num) (hμpos 0)) (pow_pos hM 3))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hb hκ.le]
  have hgap (i : Fin 7) : L*N ≤ |G (z i.succ)-G (z i.castSucc)| := by
    have hh := mul_le_mul_of_nonneg_right hcoef
      (div_pos (mul_pos hN hcount) (by norm_num : (0:ℝ) < 1296)).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/1296) := by
      dsimp only [L]
      field_simp
    rw [he]
    dsimp only [z]
    rw [Fin.rev_succ,Fin.rev_castSucc,abs_sub_comm]
    exact (hh.trans (hG i.rev)).trans (le_abs_self _)
  have hroot i t : iteratedDeriv 2 (f i) (xp (idx t.rev) i)/2=
      (e (tag i)*z t+v (tag i))/(r (tag i)*z t+s (tag i)) := hpoint _ (hmem t.rev) i
  have hex (i : Fin 3) := physicalModelPhase_interval_root_family
    (l:=z 0) (w:=z 7) (x₀:=xref i) hσ.le (hF₂ i) hT hM (hA i) (hW i)
    (hxp _ (hmem (0:Fin 8).rev) i) (hxp _ (hmem (7:Fin 8).rev) i)
    (hd.trans_le (hden 0 _ (hz 0 0) (tag i)).1)
    (hd.trans_le (hden 0 _ (hz 0 7) (tag i)).1)
    (hdisplacement _ (hmem (0:Fin 8).rev) i)
    (hdisplacement _ (hmem (7:Fin 8).rev) i)
    (by rw [←hroot i 0]; exact Set.left_mem_uIcc)
    (by rw [←hroot i 7]; exact Set.right_mem_uIcc)
  choose rho hρ hρdiam using hex
  have hdiam i : |xp (idx (7:Fin 8).rev) i-xp (idx (0:Fin 8).rev) i|+1 ≤ nSpan := by
    have hh := abs_sub_le (xp (idx (7:Fin 8).rev) i) (xref i) (xp (idx (0:Fin 8).rev) i)
    rw [abs_sub_comm (xref i)] at hh
    linarith only [hh,hdisplacement _ (hmem (7:Fin 8).rev) i,
      hdisplacement _ (hmem (0:Fin 8).rev) i,hspan i]
  exact hgapFn Fsrc η Tsrc yp z A W xref (fun t i => rho i t) e r v s
    (fun j => ac j-(a₀ j:ℝ)) (fun j => bc j-(b₀ j:ℝ))
    hη hηmax hyp hclose hreg hbound htests hTsrc hMtwo hσ hδ hF
    hT hN hR hL hNL hd hK hA hW hxref
    (fun t ht i => (hρ i t ht).2.1) hr hdet
    (fun t ht i => hden 0 t (hsub 0 ht) i) hmono hLspan hcube
    (fun t ht u hu i => (hρdiam i t ht u hu).trans (hdiam i))
    hbase (fun t ht i => (hρ i t ht).2.2.1)
    (fun t ht i => (pow_le_pow_left₀ (abs_nonneg _)
      (hρ i t ht).2.2.2.2 2).trans (hsquare i))
    hgap (fun j i => by
      have hh := hres j _ (hmem i.rev)
      rw [(hcoeff j i.rev).2.1,(hcoeff j i.rev).2.2] at hh
      exact hh)

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
      ∀ (Fsrc : ℝ → ℝ) (η Tsrc : ℝ) (yp : Fin 3 → ℝ)
      (S : Finset ℕ) (y : ℕ → ℝ) (xp : ℕ → Fin 3 → ℝ)
      (A : Fin 3 → ℤ) (W xref Hspan : Fin 3 → ℝ)
      (e r v s U l w y₀ ac bc : Fin 2 → ℝ) (cell : Fin 2 → Fin 17)
      {σ δ T M N R d K nSpan base : ℝ},
      0 < η → η ≤ 1/8 → (∀ i, yp i ∈ Icc (1:ℝ) 2) → |yp 2-yp 1| < a →
      (∀ t, 0 < t → ContDiffAt ℝ ∞ Fsrc t) →
      (∀ t ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc t| ≤ Usrc) →
      (∀ t ∈ Icc (1/2:ℝ) 3, ∀ j,
        csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc t) j|) →
      0 < Tsrc → 2 ≤ M → 2592 ≤ S.card →
      let F := fun (i : Fin 3) u =>
        (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
      (0 < σ) → (δ ≤ min (modelPhaseThirdLower σ) 1) →
      (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
      0 < T → 0 < N → 1 ≤ R → R ≤ M → 0 < d → 0 ≤ K →
      (∀ i, M ≤ A i) → (∀ i, A i+W i ≤ 2*M) →
      (∀ i, xref i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ n ∈ S, ∀ i, xp n i ∈ Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ n ∈ S, xp n 0 ∈ Icc (base+N*(n:ℝ)) (base+N*((n:ℝ)+1))) →
      (∀ n ∈ S, ∀ i, |xp n i-xref i| ≤ Hspan i) →
      (∀ i, 2*Hspan i+1 ≤ nSpan) → nSpan^3 ≤ M*R^2 →
      (∀ i, r i ≠ 0) → (∀ i, v i*r i-e i*s i=1) →
      (∀ j, ∀ z ∈ Icc (l j) (w j), ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d) →
      (∀ j, U j*(w j-l j) ≤ 1/2) →
      (∀ j, U j*(w j-l j)*(max |l j| |w j|+(w j-l j)/2) ≤ 1/2) →
      let tag := fun i : Fin 3 => (if i=0 then 0 else 1 : Fin 2)
      let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
      let mu := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
      let nu := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
      let g := fun j : Fin 2 => rationalPhase (mu 0) (r 0) (s 0) (mu j.succ) (r 1) (s 1)
      let H := fun j : Fin 2 => quarticPhase (mu 0) (nu 0) (r 0) (s 0)
        (mu j.succ) (nu j.succ) (r 1) (s 1)
      let phi := fun j z => g j z-H j z
      let G := minorArcCoordinate (mu 0) (r 0) (s 0)
      let Z := fun j : Fin 2 => quarticCurvatureBoundaryRoots
        (mu 0) (nu 0) (r 0) (s 0) (mu j.succ) (nu j.succ) (r 1) (s 1) (U j)
      (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e (tag i)/r (tag i)) →
      (∀ n ∈ S, ∀ i, iteratedDeriv 2 (f i) (xp n i)/2=
        (e (tag i)*y n+v (tag i))/(r (tag i)*y n+s (tag i))) →
      (∀ j, y₀ j ∈ finiteBoundaryCell (Z j) (l j) (w j) (cell j)) →
      (∀ j, ∀ n ∈ S, y n ∈ finiteBoundaryCell (Z j) (l j) (w j) (cell j)) →
      (∀ j, |iteratedDeriv 2 (g j) (y₀ j)-iteratedDeriv 2 (H j) (y₀ j)| ≤ U j) →
      (∀ j, ∀ n ∈ S,
        |(ac j-round (ac j-deriv (phi j) (y n)))*y n+
          (bc j-round (bc j-phi j (y n)+y n*deriv (phi j) (y n)))-g j (y n)+H j (y n)| ≤
            K*R^2/|r 0*G (y n)|) →
      let κ := modelPhaseThirdLower σ
      let Γ := (σ*(σ+1)+1)/κ
      let L := κ/(1296*(σ*(σ+1)+1))*(S.card:ℝ)
      let Cmid := Γ^2*(Γ*(32*K+9*quarticReciprocalConstant σ δ))+
        2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ
      |yp 2-yp 1| ≤ C*(16*Γ*Cmid+1)*R^2/(L^2*N^2) :=
  HuxleyBoundaryCoverScratch.positive_difference_common_occupied_quartic_parameter_gap (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


#print axioms positive_difference_common_occupied_quartic_parameter_gap


/-- Integral bounded-action matrices cannot remain nontriangular outside
the curvature transition band.  Trace two is derived from the actual
narrow homography, not assumed as a matrix classification. -/
private theorem bounded_action_off_transition_triangular
    (a b c d : ℤ) {x y H L : ℝ}
    (hdet : a*d-b*c=1) (hx0 : x ≠ 0)
    (hx : |x| ≤ H) (hy : |y| ≤ H)
    (haction : |(c:ℝ)| *H ≤ L)
    (hmap : ((a:ℝ)*x+b)/((c:ℝ)*x+d)=y)
    (hden : |(c:ℝ)*x+d-1| ≤ 1/(8*(L+3)))
    (hnum : |((a:ℝ)*x+b)/x-1| ≤ 1/(8*(L+3)))
    (hregime : L < H ∨ (L+4)*H < 1) :
    a=1 ∧ d=1 ∧ (b=0 ∨ c=0) := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hx
  have hL : 0 ≤ L := (mul_nonneg (abs_nonneg _) hH).trans haction
  obtain ⟨htrace,hbc⟩ := bounded_action_narrow_ratios_trace_two a b c d
    hdet hx0 hx hy haction hmap hden hnum
  have htri : b=0 ∨ c=0 := by
    rcases hregime with hhigh | hlow
    · right
      by_contra hc
      have hcR : (1:ℝ) ≤ |(c:ℝ)| := by exact_mod_cast Int.one_le_abs hc
      have hh := mul_le_mul_of_nonneg_right hcR hH
      nlinarith only [hh,haction,hhigh]
    · left
      have hε : 1/(8*(L+3)) ≤ (1:ℝ)/24 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith only [hL])
      have ht := abs_le.mp (hden.trans hε)
      have htpos : 0 < (c:ℝ)*x+d := by linarith only [ht.1]
      have htlo : (1:ℝ)/2 ≤ (c:ℝ)*x+d := by linarith only [ht.1]
      have hthi : (c:ℝ)*x+d ≤ 2 := by linarith only [ht.2]
      have hdetR : (a:ℝ)*d-(b:ℝ)*c=1 := by exact_mod_cast hdet
      have ha := (bourgain_mobius_entry_bounds hdetR htlo hthi hmap hx hy).1
      have ha' : |(a:ℝ)| ≤ L+2 := by linarith only [ha,haction]
      have hprod := (div_eq_iff htpos.ne').mp hmap
      have hb : |(b:ℝ)| ≤ (L+4)*H := by
        calc
          _ = |((a:ℝ)*x+b)-(a:ℝ)*x| := by congr 1; ring
          _ ≤ |(a:ℝ)*x+b|+|(a:ℝ)*x| := abs_sub _ _
          _ = |y| * ((c:ℝ)*x+d)+|(a:ℝ)| * |x| := by
            rw [hprod,abs_mul,abs_of_pos htpos,abs_mul]
          _ ≤ H*2+(L+2)*H := add_le_add
            (mul_le_mul hy hthi htpos.le hH)
            (mul_le_mul ha' hx (abs_nonneg _) (by linarith only [hL]))
          _ = _ := by ring
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast hb.trans_lt hlow)
  have ha : a=1 := by
    rcases htri with hb | hc
    · simp only [hb,neg_zero,zero_mul] at hbc
      nlinarith only [hbc]
    · simp only [hc,mul_zero] at hbc
      nlinarith only [hbc]
  exact ⟨ha,by omega,htri⟩

example
    (a b c d : ℤ) {x y H L : ℝ}
    (hdet : a*d-b*c=1) (hx0 : x ≠ 0)
    (hx : |x| ≤ H) (hy : |y| ≤ H)
    (haction : |(c:ℝ)| *H ≤ L)
    (hmap : ((a:ℝ)*x+b)/((c:ℝ)*x+d)=y)
    (hden : |(c:ℝ)*x+d-1| ≤ 1/(8*(L+3)))
    (hnum : |((a:ℝ)*x+b)/x-1| ≤ 1/(8*(L+3)))
    (hregime : L < H ∨ (L+4)*H < 1) :
    a=1 ∧ d=1 ∧ (b=0 ∨ c=0) :=
  HuxleyBoundaryCoverScratch.bounded_action_off_transition_triangular a b c d (x:=x) (y:=y) (H:=H) (L:=L) hdet hx0 hx hy haction hmap hden hnum hregime


#print axioms bounded_action_off_transition_triangular


/-- The off-transition classification is linked to physical power scales:
Tphys=X^p and M=X^m. The transition p=2*m is excluded explicitly. -/
private theorem eventually_source_scaled_bounded_action_triangular
    {K p m L : ℝ} (hK : 0 < K) (hexponent : p ≠ 2*m) :
    ∀ᶠ X : ℝ in Filter.atTop,
      let H := K*X^p/(X^m)^2
      ∀ (a b c d : ℤ) (x y : ℝ),
      a*d-b*c=1 → x ≠ 0 → |x| ≤ H → |y| ≤ H →
      |(c:ℝ)| *H ≤ L → ((a:ℝ)*x+b)/((c:ℝ)*x+d)=y →
      |(c:ℝ)*x+d-1| ≤ 1/(8*(L+3)) →
      |((a:ℝ)*x+b)/x-1| ≤ 1/(8*(L+3)) →
      a=1 ∧ d=1 ∧ (b=0 ∨ c=0) := by
  have hidentity X (hX : 0 < X) : K*X^p/(X^m)^2=K*X^(p-2*m) := by
    have hh : (X^m)^2=X^(2*m) := by
      rw [mul_comm 2 m,Real.rpow_mul hX.le,Real.rpow_two]
    rw [hh,Real.rpow_sub hX]
    ring
  have hregime : ∀ᶠ X : ℝ in Filter.atTop,
      L < K*X^(p-2*m) ∨ (L+4)*(K*X^(p-2*m)) < 1 := by
    rcases lt_or_gt_of_ne hexponent with hsmall | hlarge
    · have hpow := tendsto_rpow_neg_atTop (show 0 < -(p-2*m) by linarith only [hsmall])
      have hlim := hpow.const_mul ((L+4)*K)
      have hlim' : Filter.Tendsto (fun X : ℝ => (L+4)*K*X^(p-2*m))
          Filter.atTop (nhds 0) := by simpa only [neg_neg,mul_zero] using hlim
      filter_upwards [hlim'.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with X hX
      right
      convert hX using 1
      ring
    · have hpow := tendsto_rpow_atTop (show 0 < p-2*m by linarith only [hlarge])
      filter_upwards [hpow.eventually (Filter.eventually_gt_atTop (L/K))] with X hX
      left
      simpa only [mul_comm K] using (div_lt_iff₀ hK).mp hX
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ),hregime] with X hX hreg
  intro H a b c d x y hdet hx0 hx hy haction hmap hden hnum
  apply bounded_action_off_transition_triangular a b c d hdet hx0 hx hy haction hmap hden hnum
  simpa only [H,hidentity X hX] using hreg

example
    {K p m L : ℝ} (hK : 0 < K) (hexponent : p ≠ 2*m) :
    ∀ᶠ X : ℝ in Filter.atTop,
      let H := K*X^p/(X^m)^2
      ∀ (a b c d : ℤ) (x y : ℝ),
      a*d-b*c=1 → x ≠ 0 → |x| ≤ H → |y| ≤ H →
      |(c:ℝ)| *H ≤ L → ((a:ℝ)*x+b)/((c:ℝ)*x+d)=y →
      |(c:ℝ)*x+d-1| ≤ 1/(8*(L+3)) →
      |((a:ℝ)*x+b)/x-1| ≤ 1/(8*(L+3)) →
      a=1 ∧ d=1 ∧ (b=0 ∨ c=0) :=
  HuxleyBoundaryCoverScratch.eventually_source_scaled_bounded_action_triangular (K:=K) (p:=p) (m:=m) (L:=L) hK hexponent


#print axioms eventually_source_scaled_bounded_action_triangular


/-- The identity long-block parameter bound consumes the installed actual
Fourier-gap witness constructor. No selected samples, quartic residuals,
root curves or improved Third estimates are supplied by the caller. -/
private theorem positive_difference_actual_fourier_identity_long_gap_parameter_gap
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor n : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ 1/8 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 → |yb-ya| < a →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
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
    (Mat 0=1 ∧ Mat 1=0 ∧ Mat 2=0 ∧ Mat 3=1) →
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
    Gaps.Nonempty → |yb-ya| ≤ C*(Cthird+1)*R^2/(L^2*N^2) := by
  classical
  obtain ⟨a,C,ha,hacap,hC,hpair⟩ :=
    positive_difference_identity_quartic_long_block_parameter_gap hσsrc hcsrc hUsrc
  refine ⟨a,C,ha,hacap,hC,?_⟩
  intro Fsrc η ya yb Tsrc Uref Refs Gaps Bselect
    Bmajor Cmajor n S Q K₀ inst rat vinv parity anchor Mat e r v s
    σ δ T M N R base Bcut lambda Uband θ A W x
    hη hηmax hya hyb hclose hreg hjets htests hTsrc hMtwo
    yp F hn
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hidentity hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor hblocks L Gamma Cthird
  obtain ⟨hI0,hI1,hI2,hI3⟩ := hidentity
  have hMatdet : Mat 0*Mat 3-Mat 1*Mat 2=1 := by rw [hI0,hI1,hI2,hI3]; norm_num
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hLp : 0 < L := by dsimp only [L]; positivity
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
      L ≤ κ/(16*(Blabels ab:ℝ)*Cphys)*((S₀ ab).card:ℝ) := by
    have hchartpos : 0 < Ccharts ab := by dsimp only [Ccharts]; omega
    have hlabelpos : 0 < Blabels ab := by dsimp only [Blabels]; omega
    have hbudget : 6+Ccharts ab*(105+544*Blabels ab) ≤ m0 := by
      dsimp only [m0]
      gcongr
      exact hCmajor ab hab
      exact hBmajor ab hab
    have hlower := (Nat.mul_le_mul_right n hbudget).trans (hblocks ab hab)
    have hoffset : 6+105*Ccharts ab ≤ (6+105*Ccharts ab)*n :=
      Nat.le_mul_of_pos_right _ hn
    have hselection : (S ab).card ≤ 6+Ccharts ab*(105+17*(S₀ ab).card) :=
      hcard ab hab
    have hmul : Ccharts ab*(17*(32*Blabels ab*n)) ≤
        Ccharts ab*(17*(S₀ ab).card) := by
      nlinarith only [hlower,hselection,hoffset]
    have hmassNat : 32*Blabels ab*n ≤ (S₀ ab).card :=
      Nat.le_of_mul_le_mul_left
        (Nat.le_of_mul_le_mul_left hmul hchartpos) (by decide : 0 < (17:ℕ))
    have hmass : (32:ℝ)*(Blabels ab:ℝ)*(n:ℝ) ≤ ((S₀ ab).card:ℝ) := by
      exact_mod_cast hmassNat
    have hbreal : (0:ℝ) < Blabels ab := Nat.cast_pos.mpr hlabelpos
    calc
      L = κ/(16*(Blabels ab:ℝ)*Cphys)*((32:ℝ)*(Blabels ab:ℝ)*(n:ℝ)) := by
        dsimp only [L]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

  intro hne
  obtain ⟨ab,hab⟩ := hne
  have hNLL : (L*N)^2 ≤ M*R :=
    (pow_le_pow_left₀ (mul_pos hLp hN).le
      (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le) 2).trans (hNL ab hab)
  let take : Fin 4 → Fin 8 := fun i => ⟨i.val,by omega⟩
  have htake : StrictMono take := fun _ _ hh => hh
  let z4 : Fin 4 → ℝ := fun i => z ab (take i)
  have hsub : Icc (z4 0) (z4 3) ⊆ Icc (z ab 0) (z ab 7) := by
    intro t ht
    exact ⟨ht.1,ht.2.trans ((hmono ab hab).monotone (by change (3:Fin 8) ≤ 7; decide))⟩
  have hrab : (r ab:ℝ) ≠ 0 := by
    have hh : rp ab 0 ≠ 0 := (mul_ne_zero_iff.mp (hxr ab hab 0).1.ne').1
    exact_mod_cast hh
  have hchartR : (v ab:ℝ)*r ab-(e ab:ℝ)*s ab=1 := by exact_mod_cast hchart ab hab
  apply hpair Fsrc η ya yb Tsrc z4 A W (xref ab) (curve ab)
    (e ab:ℝ) (r ab:ℝ) (v ab:ℝ) (s ab:ℝ)
    (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L)
    (d:=d ab) (K:=Kres) (α:=alpha ab) (β:=beta ab)
    hη hηmax hya hyb hclose hreg hjets htests hTsrc hMtwo hσ hδ hF
    hT hN hR hLp hNLL (hd ab hab) (hKp ab hab) hA hW
    (fun i => (hxr ab hab i).2.1)
    (fun t ht i => ((hcurve ab hab t (hsub ht)).2 i).1)
    hrab hchartR
    (fun t ht => ⟨((hcurve ab hab t (hsub ht)).2 0).2.1,
      ((hcurve ab hab t (hsub ht)).2 0).2.2.1⟩)
    ((hmono ab hab).comp htake)
  · intro i
    have hh := (hxr ab hab i).2.2.1
    fin_cases i <;> simpa [ep,rp,hI0,hI1,hI2,hI3] using hh
  · intro t ht i
    have hh := ((hcurve ab hab t (hsub ht)).2 i).2.2.2.1
    fin_cases i <;> simpa [ep,rp,vp,sp,hI0,hI1,hI2,hI3] using hh
  · exact fun t ht i => ((hcurve ab hab t (hsub ht)).2 i).2.2.2.2
  · intro i
    exact (mul_le_mul_of_nonneg_right (hlong ab hab) hN.le).trans
      (hspacing ab hab (⟨i.val,by omega⟩ : Fin 7))
  · intro i
    simpa [rp,sp,hI0,hI1,hI2,hI3,F,yp,z4,Kres,Cc,Ct,C₂,C₃,B,J,c,Cphys,κ]
      using hres ab hab (take i)

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1/4 ∧ 0 < C ∧
    ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Bmajor Cmajor n : ℕ)
    (S : ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℝ × ℝ → ℕ → Fin 2 → ℚ) (vinv : ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : ℝ × ℝ → ℕ → Fin 2 → Fin 2) (anchor : ℝ × ℝ → ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ}
    {x : ℝ × ℝ → ℕ → Fin 2 → ℝ},
    0 < η → η ≤ 1/8 →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 → |yb-ya| < a →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M →
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
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
    (Mat 0=1 ∧ Mat 1=0 ∧ Mat 2=0 ∧ Mat 3=1) →
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
    Gaps.Nonempty → |yb-ya| ≤ C*(Cthird+1)*R^2/(L^2*N^2) :=
  HuxleyBoundaryCoverScratch.positive_difference_actual_fourier_identity_long_gap_parameter_gap (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc


#print axioms positive_difference_actual_fourier_identity_long_gap_parameter_gap


/-- Finite tail summation for separated parameters with an inverse-square
long-block bound. This is the combinatorial averaging step only; analytic
applications must derive the displayed parameter-compression hypothesis. -/
private theorem separated_inverse_square_weight_sum
    (Y : Finset ℝ) (w : ℝ → ℕ) (U : ℕ) {center D J : ℝ}
    (hD : 0 ≤ D) (hJ : 0 < J)
    (hsep : ∀ x∈Y, ∀ y∈Y, x ≠ y → 1 ≤ J*|x-y|)
    (hcap : ∀ y∈Y, w y ≤ U)
    (hcompress : ∀ y∈Y, ∀ n : ℕ, 0 < n → n ≤ w y →
      |y-center| ≤ D/(n:ℝ)^2) :
    (∑ y∈Y, (w y:ℝ)) ≤ (U:ℝ)+4*D*J := by
  classical
  let E := fun n : ℕ => Y.filter (fun y => n ≤ w y)
  have hcount (n : ℕ) (hn : 0 < n) :
      ((E n).card:ℝ) ≤ 1+2*D*J/(n:ℝ)^2 := by
    have hrad : 0 ≤ D/(n:ℝ)^2 := by positivity
    have hh := separated_reference_interval_card (E n)
      (a:=center-D/(n:ℝ)^2) (b:=center+D/(n:ℝ)^2) (d:=1/J)
      (by positivity) (by linarith only [hrad])
      (by
        intro x hx y hy hne
        apply (div_le_iff₀ hJ).mpr
        simpa only [mul_comm] using
          hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne)
      (by
        intro y hy
        have hh := abs_le.mp (hcompress y (Finset.mem_filter.mp hy).1 n hn
          (Finset.mem_filter.mp hy).2)
        constructor <;> linarith only [hh.1,hh.2])
    convert hh using 1
    field_simp
    ring
  have hlevels y (hy : y∈Y) :
      (w y:ℝ) = ∑ n∈Finset.Icc 1 U, if n ≤ w y then (1:ℝ) else 0 := by
    have hfilter : (Finset.Icc 1 U).filter (fun n => n ≤ w y) =
        Finset.Icc 1 (w y) := by
      ext n
      simp only [Finset.mem_filter,Finset.mem_Icc]
      constructor
      · intro hh
        exact ⟨hh.1.1,hh.2⟩
      · intro hh
        exact ⟨⟨hh.1,hh.2.trans (hcap y hy)⟩,hh.2⟩
    rw [← Finset.sum_filter,hfilter]
    simp
  have hsum : (∑ y∈Y, (w y:ℝ)) =
      ∑ n∈Finset.Icc 1 U, ((E n).card:ℝ) := by
    calc
      _ = ∑ y∈Y, ∑ n∈Finset.Icc 1 U,
          if n ≤ w y then (1:ℝ) else 0 :=
        Finset.sum_congr rfl hlevels
      _ = ∑ n∈Finset.Icc 1 U, ∑ y∈Y,
          if n ≤ w y then (1:ℝ) else 0 := Finset.sum_comm
      _ = _ := by simp only [← Finset.sum_filter,Finset.sum_const,
        nsmul_eq_mul,mul_one,E]
  have hinv : (∑ n∈Finset.Icc 1 U, 1/(n:ℝ)^2) ≤ 2 := by
    have he : Finset.Ioo 0 (U+1) = Finset.Icc 1 U := by
      ext n
      simp only [Finset.mem_Ioo,Finset.mem_Icc]
      omega
    have hh := sum_Ioo_inv_sq_le (α:=ℝ) 0 (U+1)
    simpa only [he,Nat.cast_zero,zero_add,div_one,one_div] using hh
  rw [hsum]
  calc
    _ ≤ ∑ n∈Finset.Icc 1 U, (1+2*D*J/(n:ℝ)^2) :=
      Finset.sum_le_sum (fun n hn => hcount n (by
        have hh := (Finset.mem_Icc.mp hn).1
        omega))
    _ = (U:ℝ)+2*D*J*(∑ n∈Finset.Icc 1 U, 1/(n:ℝ)^2) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,
        Nat.card_Icc,Nat.add_sub_cancel]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ (U:ℝ)+4*D*J := by
      have hh := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 2*D*J)
      nlinarith only [hh]

example
    (Y : Finset ℝ) (w : ℝ → ℕ) (U : ℕ) {center D J : ℝ}
    (hD : 0 ≤ D) (hJ : 0 < J)
    (hsep : ∀ x∈Y, ∀ y∈Y, x ≠ y → 1 ≤ J*|x-y|)
    (hcap : ∀ y∈Y, w y ≤ U)
    (hcompress : ∀ y∈Y, ∀ n : ℕ, 0 < n → n ≤ w y →
      |y-center| ≤ D/(n:ℝ)^2) :
    (∑ y∈Y, (w y:ℝ)) ≤ (U:ℝ)+4*D*J :=
  HuxleyBoundaryCoverScratch.separated_inverse_square_weight_sum Y w U (center:=center) (D:=D) (J:=J) hD hJ hsep hcap hcompress


#print axioms separated_inverse_square_weight_sum


/-- Choose the two probe anchors BEFORE any reference system or safe-probe
selection. Minimum denominators are independent of the anchor witness.
The least finite dyadic band works for BOTH probes; a noninitial band
has an actual failed probe at its preceding cutoff. -/
private theorem fixed_probe_minimal_anchor_band
    (value : Fin 2 → ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (Qbase kmax Acut : ℕ) (B c R : ℝ) :
    ∃ anchor : Fin 2 → ℚ,
      (∀ i, (anchor i:ℝ)∈Ioo (value i-delta) (value i+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (value i-delta) (value i+delta) →
          (anchor i).den ≤ q.den) ∧
      (∀ i, ∀ q : ℚ, (q:ℝ)∈Ioo (value i-delta) (value i+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (value i-delta) (value i+delta) →
          q.den ≤ r.den) → q.den=(anchor i).den) ∧
      let Q := fun k => Qbase*2^k
      let Good := fun k (d : ℕ) =>
        Acut*d ≤ Q k ∧ B*R^2 ≤ c*(Q k:ℝ)*d
      ((∃ k ≤ kmax,
          (∀ i, Good k (anchor i).den) ∧
          (k=0 ∨ ∃ i, ¬Good (k-1) (anchor i).den) ∧
          (∀ i, ∀ q : ℚ, (q:ℝ)∈Ioo (value i-delta) (value i+delta) →
            (∀ r : ℚ, (r:ℝ)∈Ioo (value i-delta) (value i+delta) →
              q.den ≤ r.den) → Good k q.den)) ∨
        ∃ i, ¬Good kmax (anchor i).den) := by
  classical
  have hex (i : Fin 2) : ∃ a : ℚ,
      (a:ℝ)∈Ioo (value i-delta) (value i+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (value i-delta) (value i+delta) →
          a.den ≤ q.den := by
    obtain ⟨t,htl,htu⟩ := exists_rat_btwn (show value i-delta < value i+delta by
      linarith only [hdelta])
    let P : ℕ → Prop := fun n =>
      ∃ q : ℚ, q.den=n ∧ (q:ℝ)∈Ioo (value i-delta) (value i+delta)
    have he : ∃ n, P n := ⟨t.den,t,rfl,htl,htu⟩
    obtain ⟨a,haden,ha⟩ := Nat.find_spec he
    refine ⟨a,ha,?_⟩
    intro q hq
    rw [haden]
    exact Nat.find_min' he ⟨q,rfl,hq⟩
  choose anchor hanchor using hex
  have hsame i (q : ℚ)
      (hq : (q:ℝ)∈Ioo (value i-delta) (value i+delta))
      (hmin : ∀ r : ℚ, (r:ℝ)∈Ioo (value i-delta) (value i+delta) →
        q.den ≤ r.den) : q.den=(anchor i).den :=
    le_antisymm (hmin _ (hanchor i).1) ((hanchor i).2 q hq)
  refine ⟨anchor,hanchor,hsame,?_⟩
  intro Q Good
  by_cases hlast : ∀ i, Good kmax (anchor i).den
  · have he : ∃ k : ℕ, k ≤ kmax ∧ ∀ i, Good k (anchor i).den :=
      ⟨kmax,le_rfl,hlast⟩
    let k := Nat.find he
    have hk : k ≤ kmax ∧ ∀ i, Good k (anchor i).den := Nat.find_spec he
    left
    refine ⟨k,hk.1,hk.2,?_,?_⟩
    · by_cases hz : k=0
      · exact Or.inl hz
      · right
        by_contra hno
        have hall : ∀ i, Good (k-1) (anchor i).den := not_exists_not.mp hno
        exact Nat.find_min he (show k-1 < k by omega)
          ⟨(Nat.sub_le k 1).trans hk.1,hall⟩
    · intro i q hq hmin
      rw [hsame i q hq hmin]
      exact hk.2 i
  · right
    exact not_forall.mp hlast

example
    (value : Fin 2 → ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (Qbase kmax Acut : ℕ) (B c R : ℝ) :
    ∃ anchor : Fin 2 → ℚ,
      (∀ i, (anchor i:ℝ)∈Ioo (value i-delta) (value i+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (value i-delta) (value i+delta) →
          (anchor i).den ≤ q.den) ∧
      (∀ i, ∀ q : ℚ, (q:ℝ)∈Ioo (value i-delta) (value i+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (value i-delta) (value i+delta) →
          q.den ≤ r.den) → q.den=(anchor i).den) ∧
      let Q := fun k => Qbase*2^k
      let Good := fun k (d : ℕ) =>
        Acut*d ≤ Q k ∧ B*R^2 ≤ c*(Q k:ℝ)*d
      ((∃ k ≤ kmax,
          (∀ i, Good k (anchor i).den) ∧
          (k=0 ∨ ∃ i, ¬Good (k-1) (anchor i).den) ∧
          (∀ i, ∀ q : ℚ, (q:ℝ)∈Ioo (value i-delta) (value i+delta) →
            (∀ r : ℚ, (r:ℝ)∈Ioo (value i-delta) (value i+delta) →
              q.den ≤ r.den) → Good k q.den)) ∨
        ∃ i, ¬Good kmax (anchor i).den) :=
  HuxleyBoundaryCoverScratch.fixed_probe_minimal_anchor_band value (delta:=delta) hdelta Qbase kmax Acut B c R


#print axioms fixed_probe_minimal_anchor_band


/-- Source-level use of the fixed-probe band choice. The denominator band
is selected before the reference system. The actual safe-start theorem
then selects a buffered bracket, and every minimum-denominator anchor
constructed there inherits the selected band's two inequalities. -/
private theorem positive_difference_fixed_probe_band_safe_start
    (F : ℝ → ℝ) (Qbase kmax Acut : ℕ) (Bmajor : ℝ)
    {σ c J η y T M N R x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let delta := c/(64*σ*R^2)
    let probe : Fin 2 → ℝ := ![x-2*N,x-11*N/4]
    ∃ anchor : Fin 2 → ℚ,
      (∀ i, (anchor i:ℝ)∈Ioo (h (probe i)-delta) (h (probe i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (probe i)-delta) (h (probe i)+delta) →
          (anchor i).den ≤ q.den) ∧
      let Q := fun k => Qbase*2^k
      let Good := fun k (d : ℕ) =>
        Acut*d ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*d
      ((∃ k ≤ kmax,
          (∀ i, Good k (anchor i).den) ∧
          (k=0 ∨ ∃ i, ¬Good (k-1) (anchor i).den) ∧
          ∀ (Refs : Finset ℝ) (U Buffer : ℝ),
            (∀ a∈Refs, ∀ b∈Refs, a ≠ b → U/(4*R^2) ≤ |a-b|) →
            (∀ a∈Refs, ∀ b∈Refs, a < b →
              (∀ q∈Refs, ¬(a < q ∧ q < b)) → b-a ≤ 7*U/(2*R^2)) →
            12*J ≤ σ*U → 0 ≤ Buffer →
            (∃ l∈Refs, ∃ u∈Refs, l ≤ h M ∧ h (2*M) ≤ u) →
            (∀ q∈Refs, q∈Icc (h M) (h (2*M)) →
              ∃ z∈Icc M (2*M), h z=q) →
            let Width := (14*σ/c)*U*N
            x∈Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N) →
            ∃ i : Fin 2,
              (∃ a∈Refs, ∃ b∈Refs, a < b ∧ (∀ q∈Refs, ¬(a < q ∧ q < b)) ∧
                ∃ z₁ z₂ : ℝ, z₁∈Icc M (2*M) ∧ z₂∈Icc M (2*M) ∧
                  h z₁=a ∧ h z₂=b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
                  z₁+N/4 ≤ probe i ∧ probe i ≤ z₂-N/4) ∧
              (∀ q : ℚ, (q:ℝ)∈Ioo (h (probe i)-delta) (h (probe i)+delta) →
                (∀ r : ℚ, (r:ℝ)∈Ioo (h (probe i)-delta) (h (probe i)+delta) →
                  q.den ≤ r.den) → Good k q.den)) ∨
        ∃ i, ¬Good kmax (anchor i).den) := by
  intro f h delta probe
  obtain ⟨anchor,hanchor,_hsame,hband⟩ :=
    fixed_probe_minimal_anchor_band (fun i => h (probe i))
      (show 0 < delta by dsimp only [delta]; positivity)
      Qbase kmax Acut Bmajor c R
  refine ⟨anchor,hanchor,?_⟩
  intro Q Good
  rcases hband with ⟨k,hk,hgood,hprevious,htransfer⟩ | hbad
  · left
    refine ⟨k,hk,hgood,hprevious,?_⟩
    intro Refs U Buffer hsep hgap hU hBuffer henclose hroots Width hx
    obtain ⟨t,ht,hbracket⟩ := positive_difference_two_buffered_block_starts F Refs
      hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hN hR hscale
      hsep hgap hU hBuffer henclose hroots hx
    rcases ht with ht | ht
    · refine ⟨0,?_,htransfer 0⟩
      simpa only [probe,Matrix.cons_val_zero,ht] using hbracket
    · refine ⟨1,?_,htransfer 1⟩
      simpa only [probe,Matrix.cons_val_one,ht] using hbracket
  · exact Or.inr hbad

example
    (F : ℝ → ℝ) (Qbase kmax Acut : ℕ) (Bmajor : ℝ)
    {σ c J η y T M N R x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let delta := c/(64*σ*R^2)
    let probe : Fin 2 → ℝ := ![x-2*N,x-11*N/4]
    ∃ anchor : Fin 2 → ℚ,
      (∀ i, (anchor i:ℝ)∈Ioo (h (probe i)-delta) (h (probe i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (probe i)-delta) (h (probe i)+delta) →
          (anchor i).den ≤ q.den) ∧
      let Q := fun k => Qbase*2^k
      let Good := fun k (d : ℕ) =>
        Acut*d ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*d
      ((∃ k ≤ kmax,
          (∀ i, Good k (anchor i).den) ∧
          (k=0 ∨ ∃ i, ¬Good (k-1) (anchor i).den) ∧
          ∀ (Refs : Finset ℝ) (U Buffer : ℝ),
            (∀ a∈Refs, ∀ b∈Refs, a ≠ b → U/(4*R^2) ≤ |a-b|) →
            (∀ a∈Refs, ∀ b∈Refs, a < b →
              (∀ q∈Refs, ¬(a < q ∧ q < b)) → b-a ≤ 7*U/(2*R^2)) →
            12*J ≤ σ*U → 0 ≤ Buffer →
            (∃ l∈Refs, ∃ u∈Refs, l ≤ h M ∧ h (2*M) ≤ u) →
            (∀ q∈Refs, q∈Icc (h M) (h (2*M)) →
              ∃ z∈Icc M (2*M), h z=q) →
            let Width := (14*σ/c)*U*N
            x∈Icc (M+Buffer+Width+4*N) (2*M-Buffer-Width-N) →
            ∃ i : Fin 2,
              (∃ a∈Refs, ∃ b∈Refs, a < b ∧ (∀ q∈Refs, ¬(a < q ∧ q < b)) ∧
                ∃ z₁ z₂ : ℝ, z₁∈Icc M (2*M) ∧ z₂∈Icc M (2*M) ∧
                  h z₁=a ∧ h z₂=b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
                  z₁+N/4 ≤ probe i ∧ probe i ≤ z₂-N/4) ∧
              (∀ q : ℚ, (q:ℝ)∈Ioo (h (probe i)-delta) (h (probe i)+delta) →
                (∀ r : ℚ, (r:ℝ)∈Ioo (h (probe i)-delta) (h (probe i)+delta) →
                  q.den ≤ r.den) → Good k q.den)) ∨
        ∃ i, ¬Good kmax (anchor i).den) :=
  HuxleyBoundaryCoverScratch.positive_difference_fixed_probe_band_safe_start F Qbase kmax Acut Bmajor (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (N:=N) (R:=R) (x:=x) hσ hc hJ hη hηmax hy hreg hbound hnegative hT hM hN hR hscale


#print axioms positive_difference_fixed_probe_band_safe_start


/-- Noninitial two-probe bands have a derived source-family density.
Canonical minimum-denominator anchors and the finite band labels are
constructed. Every band is charged to one of the two previous-cutoff
bad-anchor sets; the terminal remainder is counted at the last cutoff.
No source-band cardinality or reference-dependent anchor choice is assumed. -/
private theorem positive_difference_two_probe_dyadic_band_card
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ)
    (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*σ*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    let Cost := fun q : ℕ =>
      let Dlow := Bmajor*R^2/(c*(q:ℝ))
      let Dhigh := 64*σ*R^2/(c*((q/Acut+1:ℕ):ℝ))
      4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ),
      (∀ j i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ 2*Cost (Q k)) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ 2*Cost (Q kmax) := by
  classical
  intro f h t delta Q Vbound Cost
  have hex j := fixed_probe_minimal_anchor_band (fun i => h (t j i))
    (show 0 < delta by dsimp only [delta]; positivity)
    Qbase kmax Acut Bmajor c R
  choose anchor hanchor hsame hresult using hex
  let Good := fun (j : ℤ) (k : ℕ) (i : Fin 2) =>
    Acut*(anchor j i).den ≤ Q k ∧
      Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
  have hchoose j : ∃ label : Option ℕ, match label with
      | none => ∃ i, ¬Good j kmax i
      | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
          (k=0 ∨ ∃ i, ¬Good j (k-1) i) := by
    rcases hresult j with ⟨k,hk,hgood,hprev,_htransfer⟩ | hbad
    · exact ⟨some k,hk,hgood,hprev⟩
    · exact ⟨none,hbad⟩
  choose band hband using hchoose
  have hqA k : Acut ≤ Q k :=
    hAQ.trans (Nat.le_mul_of_pos_right Qbase (pow_pos (by decide : 0 < (2:ℕ)) k))
  have hbadcard k :
      ((S.filter (fun j => ∃ i, ¬Good j k i)).card:ℝ) ≤ 2*Cost (Q k) := by
    let Bad := fun i : Fin 2 => S.filter (fun j => ¬Good j k i)
    have hone (i : Fin 2) : ((Bad i).card:ℝ) ≤ Cost (Q k) :=
      (positive_difference_minimal_anchor_complement_count S F (fun j => anchor j i)
        N (base i) hσ hc hJ hη hηmax hy hreg hbound htests hnegative
        hT hM hN hR hscale (fun j hj => hpoints j hj i)
        (fun j _ => hanchor j i) (Q k) Acut Bmajor hAcut (hqA k) hBmajor).1
    have hsub : S.filter (fun j => ∃ i, ¬Good j k i) ⊆ Bad 0 ∪ Bad 1 := by
      intro j hj
      obtain ⟨hjS,i,hi⟩ := Finset.mem_filter.mp hj
      fin_cases i
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjS,hi⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjS,hi⟩)
    have hh : ((S.filter (fun j => ∃ i, ¬Good j k i)).card:ℝ) ≤
        ((Bad 0).card:ℝ)+((Bad 1).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hzero := hone 0
    have hone' := hone 1
    linarith only [hh,hzero,hone']
  refine ⟨anchor,band,hanchor,?_⟩
  change (∀ j, match band j with
    | none => ∃ i, ¬Good j kmax i
    | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
      (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧ _
  refine ⟨hband,?_,?_,?_⟩
  · intro j k hj i q hq hmin
    have hd := hband j
    rw [hj] at hd
    rw [hsame j i q hq hmin]
    exact hd.2.1 i
  · intro k
    have hsub : S.filter (fun j => band j=some (k+1)) ⊆
        S.filter (fun j => ∃ i, ¬Good j k i) := by
      intro j hj
      obtain ⟨hjS,hjband⟩ := Finset.mem_filter.mp hj
      have hd := hband j
      rw [hjband] at hd
      refine Finset.mem_filter.mpr ⟨hjS,?_⟩
      rcases hd.2.2 with hz | hprev
      · omega
      · simpa only [Nat.add_sub_cancel] using hprev
    exact (show ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤
      ((S.filter (fun j => ∃ i, ¬Good j k i)).card:ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans (hbadcard k)
  · have hsub : S.filter (fun j => band j=none) ⊆
        S.filter (fun j => ∃ i, ¬Good j kmax i) := by
      intro j hj
      obtain ⟨hjS,hjband⟩ := Finset.mem_filter.mp hj
      have hd := hband j
      rw [hjband] at hd
      exact Finset.mem_filter.mpr ⟨hjS,hd⟩
    exact (show ((S.filter (fun j => band j=none)).card:ℝ) ≤
      ((S.filter (fun j => ∃ i, ¬Good j kmax i)).card:ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans (hbadcard kmax)

example
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ)
    (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*σ*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    let Cost := fun q : ℕ =>
      let Dlow := Bmajor*R^2/(c*(q:ℝ))
      let Dhigh := 64*σ*R^2/(c*((q/Acut+1:ℕ):ℝ))
      4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ),
      (∀ j i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ 2*Cost (Q k)) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ 2*Cost (Q kmax) :=
  HuxleyBoundaryCoverScratch.positive_difference_two_probe_dyadic_band_card S F N Qbase kmax Acut base Bmajor (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (R:=R) hσ hc hJ hη hηmax hy hreg hbound htests hnegative hT hM hN hR hscale hAcut hAQ hBmajor hpoints


#print axioms positive_difference_two_probe_dyadic_band_card


/-- The actual two-sided anchor-complement cost retains quadratic
denominator decay under N*Q<=M. No R<=Q weakening is used. -/
private theorem huxley_anchor_complement_quadratic_density_scale
    (Q Acut : ℕ) {σ c J M N R B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : 2 ≤ Acut) (hAQ : Acut ≤ Q) (hB : 0 ≤ B)
    (hNQ : N*(Q:ℝ) ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let delta := c/(64*σ*R^2)
    let Dlow := B*R^2/(c*(Q:ℝ))
    let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
    let Dupper := 64*σ*R^2/(c*((Q:ℝ)/Acut))
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(B/c)^2+B/c
    (4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)))+
      Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
        ((Acut:ℝ)^2*Ctail+Clow)*(M*R^2/(N*(Q:ℝ)^2))*
          (2+Real.log (Dupper+1)) := by
  intro Vcurv delta Dlow Dhigh Dupper Ctail Clow
  have hAp : 0 < Acut := by omega
  have hQp : 0 < Q := by omega
  have hAr : (0:ℝ) < Acut := Nat.cast_pos.mpr hAp
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQp
  have hA1 : (1:ℝ) ≤ Acut := by exact_mod_cast (show 1 ≤ Acut by omega)
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQp
  have hNM : N ≤ M := by
    have hh : N ≤ N*(Q:ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ1 hN.le
    exact hh.trans hNQ
  have hthreshold : (Q:ℝ)/Acut ≤ (Q/Acut+1:ℕ) := by
    apply (div_le_iff₀ hAr).mpr
    have hh : Q < Acut*(Q/Acut+1) := Nat.lt_mul_div_succ Q hAp
    have hr : (Q:ℝ) < (Acut:ℝ)*((Q/Acut+1:ℕ):ℝ) := by exact_mod_cast hh
    simpa only [mul_comm] using hr.le
  have hDhigh : 0 ≤ Dhigh := by dsimp only [Dhigh]; positivity
  have hDupper : 0 ≤ Dupper := by dsimp only [Dupper]; positivity
  have hDle : Dhigh ≤ Dupper :=
    div_le_div_of_nonneg_left (by positivity)
      (mul_pos hc (div_pos hQr hAr)) (mul_le_mul_of_nonneg_left hthreshold hc.le)
  have hlog : 1 ≤ 2+Real.log (Dupper+1) := by
    have hh := Real.log_nonneg (show 1 ≤ Dupper+1 by linarith only [hDupper])
    linarith only [hh]
  have hNQeff : N*((Q:ℝ)/Acut) ≤ M :=
    (mul_le_mul_of_nonneg_left (div_le_self hQr.le hA1) hN.le).trans hNQ
  have hhigh :
      4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) ≤
        (Acut:ℝ)^2*Ctail*(M*R^2/(N*(Q:ℝ)^2))*(2+Real.log (Dupper+1)) := by
    have hmono :
        4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)) ≤
          4*Vcurv*Dupper^2+3*Dupper*(2+Real.log (Dupper+1)) := by
      have hX : 0 ≤ Vcurv := by dsimp only [Vcurv]; positivity
      have hlogHigh : 0 ≤ Real.log (Dhigh+1) :=
        Real.log_nonneg (by linarith only [hDhigh])
      gcongr
    have hh := hmono.trans
      (huxley_sharp_tail_quadratic_density_scale hσ hc hJ hM hN hR
        (div_pos hQr hAr) hNQeff)
    change _ ≤ Ctail*(M*R^2/(N*((Q:ℝ)/Acut)^2))*(2+Real.log (Dupper+1)) at hh
    convert hh using 1
    field_simp
  let E := B/c
  let K := M*R^2/(N*(Q:ℝ)^2)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hbase : R^2/(Q:ℝ) ≤ K := by
    apply (div_le_div_iff₀ hQr (by positivity : 0 < N*(Q:ℝ)^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNQ
      (show 0 ≤ R^2*(Q:ℝ) by positivity)]
  have hsquare : R^2/(Q:ℝ)^2 ≤ K := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hQr)
      (by positivity : 0 < N*(Q:ℝ)^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hNM
      (show 0 ≤ R^2*(Q:ℝ)^2 by positivity)]
  have hlowRaw : Dlow*(2*(Vcurv+delta)*Dlow+1) ≤ Clow*K := by
    have hsecond : ((c/(32*σ))*E^2)*(R^2/(Q:ℝ)^2) ≤ ((c/(32*σ))*E^2)*K :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    have hthird : E*(R^2/(Q:ℝ)) ≤ E*K := mul_le_mul_of_nonneg_left hbase hE
    calc
      _ = ((3*J/σ)*E^2*K)+((c/(32*σ))*E^2)*(R^2/(Q:ℝ)^2)+
          E*(R^2/(Q:ℝ)) := by
        dsimp only [Vcurv,delta,Dlow,E,K]
        field_simp
        ring
      _ ≤ ((3*J/σ)*E^2*K)+((c/(32*σ))*E^2)*K+E*K :=
        add_le_add (add_le_add le_rfl hsecond) hthird
      _ = _ := by dsimp only [Clow,E]; ring
  have hlow : Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
      Clow*K*(2+Real.log (Dupper+1)) := by
    apply hlowRaw.trans
    exact le_mul_of_one_le_right (by dsimp only [Clow]; positivity) hlog
  convert add_le_add hhigh hlow using 1
  dsimp only [K]
  ring

example
    (Q Acut : ℕ) {σ c J M N R B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : 2 ≤ Acut) (hAQ : Acut ≤ Q) (hB : 0 ≤ B)
    (hNQ : N*(Q:ℝ) ≤ M) :
    let Vcurv := 3*J*M/(2*σ*N*R^2)
    let delta := c/(64*σ*R^2)
    let Dlow := B*R^2/(c*(Q:ℝ))
    let Dhigh := 64*σ*R^2/(c*((Q/Acut+1:ℕ):ℝ))
    let Dupper := 64*σ*R^2/(c*((Q:ℝ)/Acut))
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(B/c)^2+B/c
    (4*Vcurv*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1)))+
      Dlow*(2*(Vcurv+delta)*Dlow+1) ≤
        ((Acut:ℝ)^2*Ctail+Clow)*(M*R^2/(N*(Q:ℝ)^2))*
          (2+Real.log (Dupper+1)) :=
  HuxleyBoundaryCoverScratch.huxley_anchor_complement_quadratic_density_scale Q Acut (σ:=σ) (c:=c) (J:=J) (M:=M) (N:=N) (R:=R) (B:=B) hσ hc hJ hM hN hR hA hAQ hB hNQ


#print axioms huxley_anchor_complement_quadratic_density_scale


/-- Constructed fixed-probe bands with the quadratic source density.
All denominators come from the actual source curvature; no band-count
certificate or reference-dependent band choice is supplied. -/
private theorem positive_difference_two_probe_dyadic_quadratic_density
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ)
    (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc M (2*M))
    (hNQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*σ*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c
    let Cerror := (Acut:ℝ)^2*Ctail+Clow
    let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (64*σ*R^2/(c*((Q k:ℝ)/Acut))+1))
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ),
      (∀ j i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k ≤ kmax, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ Density k) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ Density kmax := by
  classical
  intro f h t delta Q Ctail Clow Cerror Density
  obtain ⟨anchor,band,hanchor,hband,htransfer,hcounts,htail⟩ :=
    positive_difference_two_probe_dyadic_band_card S F N Qbase kmax Acut base Bmajor
      hσ hc hJ hη hηmax hy hreg hbound htests hnegative hT hM hN hR hscale
      hAcut hAQ hBmajor hpoints
  let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
  let Cost := fun q : ℕ =>
    let Dlow := Bmajor*R^2/(c*(q:ℝ))
    let Dhigh := 64*σ*R^2/(c*((q/Acut+1:ℕ):ℝ))
    4*Vbound*Dhigh^2+3*Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(Vbound+delta)*Dlow+1)
  have hcost k (hk : k ≤ kmax) : 2*Cost (Q k) ≤ Density k := by
    have hqA : Acut ≤ Q k :=
      hAQ.trans (Nat.le_mul_of_pos_right Qbase (pow_pos (by decide : 0 < (2:ℕ)) k))
    have hqmax : Q k ≤ Q kmax :=
      Nat.mul_le_mul_left Qbase (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hk)
    have hNQ : (N:ℝ)*(Q k:ℝ) ≤ M :=
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hqmax) (Nat.cast_nonneg N)).trans hNQmax
    have hh := huxley_anchor_complement_quadratic_density_scale (Q k) Acut
      hσ hc hJ hM (Nat.cast_pos.mpr hN) hR hAcut hqA hBmajor hNQ
    change Cost (Q k) ≤ Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (64*σ*R^2/(c*((Q k:ℝ)/Acut))+1)) at hh
    calc
      _ ≤ 2*(Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
          (2+Real.log (64*σ*R^2/(c*((Q k:ℝ)/Acut))+1))) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by dsimp only [Density]; ring
  refine ⟨anchor,band,hanchor,?_⟩
  intro Good
  exact ⟨hband,htransfer,fun k hk => (hcounts k).trans (hcost k hk),
    htail.trans (hcost kmax le_rfl)⟩

example
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ)
    (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i, base i+(N:ℝ)*j∈Icc M (2*M))
    (hNQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*σ*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c
    let Cerror := (Acut:ℝ)^2*Ctail+Clow
    let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (64*σ*R^2/(c*((Q k:ℝ)/Acut))+1))
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ),
      (∀ j i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k ≤ kmax, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ Density k) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ Density kmax :=
  HuxleyBoundaryCoverScratch.positive_difference_two_probe_dyadic_quadratic_density S F N Qbase kmax Acut base Bmajor (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (R:=R) hσ hc hJ hη hηmax hy hreg hbound htests hnegative hT hM hN hR hscale hAcut hAQ hBmajor hpoints hNQmax


#print axioms positive_difference_two_probe_dyadic_quadratic_density


/-- The complementary lower-triangular narrowing route consumes the actual
Fourier matrix bound and the narrow numerator ratio. Small physical
curvature and V=1+R^4*H^2/N^2 force the integral upper-right entry to vanish. -/
private theorem fourier_matrix_constructed_lower_triangular_narrowing
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K N R H : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hN : 0 < N)
    (hH : 0 ≤ H) (hHsmall : H ≤ 1/16) (he0 : e 0 ≠ 0)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hcurv : ∀ i, |(e i:ℝ)/q i| ≤ H)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hnum : |((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/((e 0:ℝ)/q 0)-1| ≤ 1/2)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2)) :
    let V := 1+R^4*H^2/N^2
    1 ≤ V ∧ (|Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V) →
      A 0=1 ∧ A 3=1 ∧ A 1=0 ∧ e 0=e 1 ∧ q 1=q 0+A 2*e 0) := by
  intro V
  have hV : 1 ≤ V := by
    dsimp only [V]
    have hh : 0 ≤ R^4*H^2/N^2 := by positivity
    linarith only [hh]
  refine ⟨hV,?_⟩
  intro hnear
  have hcap := (fourier_matrix_narrowed_coordinate_entry_bound q e vinv A
    hq hK hV hN hmesh hband hinv hdet ht hmap hgamma hnear).2
  have hqr i : (0:ℝ) < q i := by exact_mod_cast hq i
  let x := (e 0:ℝ)/q 0
  let y := (e 1:ℝ)/q 1
  let t := (A 2:ℝ)*x+A 3
  have htlo : (1:ℝ)/2 ≤ t := by
    rw [show t=(q 1:ℝ)/q 0 from ht]
    apply (le_div_iff₀ (hqr 0)).mpr
    linarith only [(hband 0).1,(hband 1).2]
  have hthi : t ≤ 2 := by
    rw [show t=(q 1:ℝ)/q 0 from ht]
    apply (div_le_iff₀ (hqr 0)).mpr
    linarith only [(hband 1).1,(hband 0).2]
  have htp : 0 < t := by linarith only [htlo]
  have hdetR : (A 0:ℝ)*A 3-(A 1:ℝ)*A 2=1 := by exact_mod_cast hdet
  have hentry := bourgain_mobius_entry_bounds hdetR htlo hthi hmap (hcurv 0) (hcurv 1)
  have he : (A 0:ℝ)*x+A 1=y*t := (div_eq_iff htp.ne').mp hmap
  have hb : |(A 1:ℝ)| ≤ |(A 2:ℝ)| *H^2+4*H := by
    calc
      _ = |y*t-(A 0:ℝ)*x| := by congr 1; linarith only [he]
      _ ≤ |y*t|+|(A 0:ℝ)*x| := abs_sub _ _
      _ = |y| *t+|(A 0:ℝ)| *|x| := by rw [abs_mul,abs_mul,abs_of_pos htp]
      _ ≤ H*2+(|(A 2:ℝ)| *H+2)*H := by
        exact add_le_add
          (mul_le_mul (hcurv 1) hthi htp.le hH)
          (mul_le_mul hentry.1 (hcurv 0) (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hweighted : |(A 2:ℝ)| *H^2 ≤ R^4*H^2/(6*N^2*V) := by
    convert mul_le_mul_of_nonneg_right hcap (sq_nonneg H) using 1
    ring
  have hgain : R^4*H^2/(6*N^2*V) < 1/6 := by
    apply (div_lt_iff₀ (by positivity : 0 < 6*N^2*V)).mpr
    have heV : N^2*V=N^2+R^4*H^2 := by
      dsimp only [V]
      field_simp
    nlinarith only [heV,sq_pos_of_pos hN]
  have hbzero : A 1=0 := Int.abs_lt_one_iff.mp (by
    exact_mod_cast (show |(A 1:ℝ)| < 1 by
      linarith only [hb,hweighted,hgain,hHsmall]))
  have hx : x ≠ 0 := div_ne_zero (by exact_mod_cast he0) (hqr 0).ne'
  have haNear : |(A 0:ℝ)-1| ≤ 1/2 := by
    have hh := hnum
    change |((A 0:ℝ)*x+A 1)/x-1| ≤ 1/2 at hh
    simpa only [hbzero,Int.cast_zero,add_zero,mul_div_cancel_right₀ _ hx] using hh
  have haInt : A 0-1=0 := Int.abs_lt_one_iff.mp (by
    exact_mod_cast (show |(A 0:ℝ)-1| < 1 by linarith only [haNear]))
  have ha : A 0=1 := by omega
  have hd : A 3=1 := by simpa only [ha,hbzero,one_mul,zero_mul,sub_zero] using hdet
  have hnumEq : (e 0:ℝ)/q 0=(e 1:ℝ)/q 0 := by
    have hh := he
    change (A 0:ℝ)*((e 0:ℝ)/q 0)+A 1=
      ((e 1:ℝ)/q 1)*((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3) at hh
    rw [ht,ha,hbzero,Int.cast_one,Int.cast_zero,one_mul,add_zero] at hh
    convert hh using 1
    field_simp [(hqr 0).ne',(hqr 1).ne']
  have heq : e 0=e 1 := by
    exact_mod_cast (div_left_inj' (hqr 0).ne').mp hnumEq
  have hdenEq : (q 1:ℝ)=(q 0:ℝ)+(A 2:ℝ)*e 0 := by
    have hh := ht
    rw [hd,Int.cast_one] at hh
    have hh' := (eq_div_iff (hqr 0).ne').mp hh
    rw [add_mul,mul_assoc,div_mul_cancel₀ _ (hqr 0).ne',one_mul] at hh'
    linarith only [hh']
  refine ⟨ha,hd,hbzero,heq,?_⟩
  exact_mod_cast hdenEq

example
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K N R H : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hN : 0 < N)
    (hH : 0 ≤ H) (hHsmall : H ≤ 1/16) (he0 : e 0 ≠ 0)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hcurv : ∀ i, |(e i:ℝ)/q i| ≤ H)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hnum : |((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/((e 0:ℝ)/q 0)-1| ≤ 1/2)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2)) :
    let V := 1+R^4*H^2/N^2
    1 ≤ V ∧ (|Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V) →
      A 0=1 ∧ A 3=1 ∧ A 1=0 ∧ e 0=e 1 ∧ q 1=q 0+A 2*e 0) :=
  HuxleyBoundaryCoverScratch.fourier_matrix_constructed_lower_triangular_narrowing q e vinv A (Q:=Q) (K:=K) (N:=N) (R:=R) (H:=H) hq hK hN hH hHsmall he0 hmesh hband hcurv hinv hdet ht hmap hnum hgamma


#print axioms fourier_matrix_constructed_lower_triangular_narrowing


/-- Linked physical version of the lower-triangular route. The Fourier
narrowing cost is derived as 1+Ccurv^2*M^2/N^4 from the ACTUAL phase scale
T*N*R^2=M^3, not paired with an unrelated exponent inequality. -/
private theorem fourier_matrix_constructed_lower_triangular_physical_scale
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K N R M T Ccurv : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hN : 0 < N)
    (hM : 0 < M) (hT : 0 < T) (hR : 0 < R) (hCcurv : 0 ≤ Ccurv)
    (hscale : T*N*R^2=M^3)
    (hHsmall : Ccurv*T/M^2 ≤ 1/16) (he0 : e 0 ≠ 0)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hcurv : ∀ i, |(e i:ℝ)/q i| ≤ Ccurv*T/M^2)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hnum : |((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/((e 0:ℝ)/q 0)-1| ≤ 1/2)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2)) :
    let V := 1+Ccurv^2*M^2/N^4
    1 ≤ V ∧ (|Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V) →
      A 0=1 ∧ A 3=1 ∧ A 1=0 ∧ e 0=e 1 ∧ q 1=q 0+A 2*e 0) := by
  intro V
  have hTvalue : T=M^3/(N*R^2) :=
    (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
  have hVeq : 1+R^4*(Ccurv*T/M^2)^2/N^2=V := by
    rw [hTvalue]
    dsimp only [V]
    field_simp
  have hh := fourier_matrix_constructed_lower_triangular_narrowing q e vinv A
    hq hK hN (by positivity : 0 ≤ Ccurv*T/M^2) hHsmall he0 hmesh hband hcurv
    hinv hdet ht hmap hnum hgamma
  simpa only [hVeq] using hh

example
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K N R M T Ccurv : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hN : 0 < N)
    (hM : 0 < M) (hT : 0 < T) (hR : 0 < R) (hCcurv : 0 ≤ Ccurv)
    (hscale : T*N*R^2=M^3)
    (hHsmall : Ccurv*T/M^2 ≤ 1/16) (he0 : e 0 ≠ 0)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hcurv : ∀ i, |(e i:ℝ)/q i| ≤ Ccurv*T/M^2)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hnum : |((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/((e 0:ℝ)/q 0)-1| ≤ 1/2)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2)) :
    let V := 1+Ccurv^2*M^2/N^4
    1 ≤ V ∧ (|Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V) →
      A 0=1 ∧ A 3=1 ∧ A 1=0 ∧ e 0=e 1 ∧ q 1=q 0+A 2*e 0) :=
  HuxleyBoundaryCoverScratch.fourier_matrix_constructed_lower_triangular_physical_scale q e vinv A (Q:=Q) (K:=K) (N:=N) (R:=R) (M:=M) (T:=T) (Ccurv:=Ccurv) hq hK hN hM hT hR hCcurv hscale hHsmall he0 hmesh hband hcurv hinv hdet ht hmap hnum hgamma


#print axioms fourier_matrix_constructed_lower_triangular_physical_scale

private theorem positive_difference_two_probe_dyadic_root_family
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ)
    (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i,
      base i+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4))
    (hNQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*σ*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c
    let Cerror := (Acut:ℝ)^2*Ctail+Clow
    let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (64*σ*R^2/(c*((Q k:ℝ)/Acut))+1))
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ)
      (za : ℤ → Fin 2 → ℝ),
      (∀ j∈S, ∀ i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      (∀ j∈S, ∀ i, h (za j i)=(anchor j i:ℝ) ∧
        |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M)) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j∈S, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j∈S, ∀ k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k ≤ kmax, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ Density k) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ Density kmax := by
  classical
  intro f h t delta Q Ctail Clow Cerror Density
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hplain j (hj : j∈S) i : t j i∈Icc M (2*M) := by
    have hh := hpoints j hj i
    change M+(N:ℝ)/4 ≤ t j i ∧ t j i ≤ 2*M-(N:ℝ)/4 at hh
    constructor <;> linarith only [hh.1,hh.2,hNp]
  obtain ⟨original,band,horiginal,hband,htransfer,hcounts,htail⟩ :=
    positive_difference_two_probe_dyadic_quadratic_density S F N Qbase kmax Acut
      base Bmajor hσ hc hJ hη hηmax hy hreg hbound htests hnegative
      hT hM hN hR hscale hAcut hAQ hBmajor hplain hNQmax
  have hqbase : 1 ≤ Qbase := by omega
  have hqmax : 1 ≤ Qbase*2^kmax :=
    hqbase.trans (Nat.le_mul_of_pos_right Qbase (pow_pos (by decide) kmax))
  have hqmaxR : (1:ℝ) ≤ (Qbase*2^kmax:ℕ) := by exact_mod_cast hqmax
  have hNM : (N:ℝ) ≤ M := by nlinarith only [hNQmax,hqmaxR,hNp]
  have hnegative4 w (hw : w∈Icc (1/2:ℝ) 3) : iteratedDeriv 4 F w ≤ -(c/4) := by
    linarith only [hnegative w hw,hc]
  have hmul j : (S.filter (fun k => id k=j)).card ≤ 1 := by
    have hh : S.filter (fun k => id k=j) ⊆ {j} :=
      fun k hk => Finset.mem_singleton.mpr (Finset.mem_filter.mp hk).2
    simpa using Finset.card_le_card hh
  have hex i := positive_difference_minimal_curvature_arc_count S F id N 1 (base i)
    hσ (show 0 < c/4 by positivity) hJ hη hηmax hy hreg hbound hnegative4
    hT hM hN hR hNM hscale hmul (fun j hj => hplain j hj i)
  choose a z hdata _hlocal _htails using hex
  let anchor := fun j i => a i j
  let za := fun j i => z i j
  have hdelta : (c/4)/(16*σ*R^2)=delta := by dsimp only [delta]; ring
  have hdata' j (hj : j∈S) i :
      za j i∈Ioo (t j i-(N:ℝ)/4) (t j i+(N:ℝ)/4) ∧
      h (za j i)=(anchor j i:ℝ) ∧
      (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
      ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (anchor j i).den ≤ q.den := by
    simpa only [hdelta] using hdata i j hj
  have hsame j (hj : j∈S) i : (anchor j i).den=(original j i).den :=
    Nat.le_antisymm ((hdata' j hj i).2.2.2 _ (horiginal j i).1)
      ((horiginal j i).2 _ (hdata' j hj i).2.2.1)
  have hroots j (hj : j∈S) i :
      h (za j i)=(anchor j i:ℝ) ∧
      |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M) := by
    have hd := hdata' j hj i
    have hp := hpoints j hj i
    change M+(N:ℝ)/4 ≤ t j i ∧ t j i ≤ 2*M-(N:ℝ)/4 at hp
    have hz : za j i∈Icc M (2*M) := by
      constructor <;> linarith only [hd.1.1,hd.1.2,hp.1,hp.2]
    refine ⟨hd.2.1,?_,hz⟩
    have hnear : |h (za j i)-h (t j i)| ≤ 7*(c/(224*σ))/(2*R^2) := by
      rw [hd.2.1]
      have ha : |(anchor j i:ℝ)-h (t j i)| ≤ delta :=
        abs_le.mpr ⟨by linarith only [hd.2.2.1.1],by linarith only [hd.2.2.1.2]⟩
      convert ha using 1
      dsimp only [delta]
      ring
    have hh := positive_difference_reference_preimage_width F hσ hc hη hηmax hy
      hreg hnegative hT hM hNp hR hscale (hplain j hj i) hz hnear
    convert hh using 1
    field_simp
    ring
  refine ⟨anchor,band,za,fun j hj i => (hdata' j hj i).2.2,hroots,?_⟩
  intro Good
  refine ⟨?_,?_,hcounts,htail⟩
  · intro j hj
    have hh := hband j
    cases he : band j with
    | none =>
        rw [he] at hh
        obtain ⟨i,hi⟩ := hh
        exact ⟨i,by simpa only [Good,hsame j hj i] using hi⟩
    | some k =>
        rw [he] at hh
        obtain ⟨hk,hgood,hprevious⟩ := hh
        refine ⟨hk,fun i => ?_,?_⟩
        · simpa only [Good,hsame j hj i] using hgood i
        · rcases hprevious with hz | ⟨i,hi⟩
          · exact Or.inl hz
          · exact Or.inr ⟨i,by simpa only [Good,hsame j hj i] using hi⟩
  · intro j _hj k hk i q hq hmin
    exact htransfer j k hk i q hq hmin

example
    (S : Finset ℤ) (F : ℝ → ℝ) (N Qbase kmax Acut : ℕ)
    (base : Fin 2 → ℝ) (Bmajor : ℝ)
    {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hAcut : 2 ≤ Acut) (hAQ : Acut ≤ Qbase) (hBmajor : 0 ≤ Bmajor)
    (hpoints : ∀ j∈S, ∀ i,
      base i+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4))
    (hNQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun (j : ℤ) (i : Fin 2) => base i+(N:ℝ)*j
    let delta := c/(64*σ*R^2)
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c
    let Cerror := (Acut:ℝ)^2*Ctail+Clow
    let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (64*σ*R^2/(c*((Q k:ℝ)/Acut))+1))
    ∃ (anchor : ℤ → Fin 2 → ℚ) (band : ℤ → Option ℕ)
      (za : ℤ → Fin 2 → ℝ),
      (∀ j∈S, ∀ i, (anchor j i:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) ∧
        ∀ q : ℚ, (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          (anchor j i).den ≤ q.den) ∧
      (∀ j∈S, ∀ i, h (za j i)=(anchor j i:ℝ) ∧
        |za j i-t j i| ≤ (N:ℝ)/16 ∧ za j i∈Icc M (2*M)) ∧
      let Good := fun j k (i : Fin 2) =>
        Acut*(anchor j i).den ≤ Q k ∧
          Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor j i).den
      (∀ j∈S, match band j with
        | none => ∃ i, ¬Good j kmax i
        | some k => k ≤ kmax ∧ (∀ i, Good j k i) ∧
            (k=0 ∨ ∃ i, ¬Good j (k-1) i)) ∧
      (∀ j∈S, ∀ k, band j=some k → ∀ i, ∀ q : ℚ,
        (q:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
        (∀ r : ℚ, (r:ℝ)∈Ioo (h (t j i)-delta) (h (t j i)+delta) →
          q.den ≤ r.den) →
        Acut*q.den ≤ Q k ∧ Bmajor*R^2 ≤ c*(Q k:ℝ)*q.den) ∧
      (∀ k ≤ kmax, ((S.filter (fun j => band j=some (k+1))).card:ℝ) ≤ Density k) ∧
      ((S.filter (fun j => band j=none)).card:ℝ) ≤ Density kmax :=
  HuxleyBoundaryCoverScratch.positive_difference_two_probe_dyadic_root_family S F N Qbase kmax Acut base Bmajor (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (R:=R) hσ hc hJ hη hηmax hy hreg hbound htests hnegative hT hM hN hR hscale hAcut hAQ hBmajor hpoints hNQmax


#print axioms positive_difference_two_probe_dyadic_root_family

private theorem positive_difference_selected_dyadic_family_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : ι → Finset ℤ) (F : ℝ → ℝ)
      (y : ι → ℝ) (base : Fin 2 → ℤ) (N Qbase kmax Acut : ℕ)
      (Bmajor η T M R : ℝ),
      0 < N → 0 < η → η ≤ 1/8 → (∀ i, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 2 ≤ Acut → Acut ≤ Qbase → 128*σ ≤ Bmajor →
      (∀ i, ∀ j∈S i, ∀ p,
        (base p:ℝ)+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun (j : ℤ) (p : Fin 2) => (base p:ℝ)+(N:ℝ)*j
      let L := fun (j : ℤ) (p : Fin 2) => base p+(N:ℤ)*j+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Q := fun k : ℕ => Qbase*2^k
      let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
      let Clow := (3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c
      let Cerror := (Acut:ℝ)^2*Ctail+Clow
      let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (64*σ*R^2/(c*((Q k:ℝ)/Acut))+1))
      ∃ (anchor : ι → ℤ → Fin 2 → ℚ) (band : ι → ℤ → Option ℕ)
        (za : ι → ℤ → Fin 2 → ℝ),
        (∀ i, ∀ j∈S i, ∀ p,
          (anchor i j p:ℝ)∈Ioo (h i (t j p)-delta) (h i (t j p)+delta) ∧
          ∀ q : ℚ, (q:ℝ)∈Ioo (h i (t j p)-delta) (h i (t j p)+delta) →
            (anchor i j p).den ≤ q.den) ∧
        (∀ i, ∀ j∈S i, ∀ p, h i (za i j p)=(anchor i j p:ℝ) ∧
          |za i j p-t j p| ≤ (N:ℝ)/16 ∧ za i j p∈Icc M (2*M)) ∧
        let Good := fun i j k (p : Fin 2) =>
          Acut*(anchor i j p).den ≤ Q k ∧
            Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor i j p).den
        (∀ i, ∀ j∈S i, match band i j with
          | none => ∃ p, ¬Good i j kmax p
          | some k => k ≤ kmax ∧ (∀ p, Good i j k p) ∧
              (k=0 ∨ ∃ p, ¬Good i j (k-1) p)) ∧
        (∀ i, ∀ k ≤ kmax,
          (((S i).filter (fun j => band i j=some (k+1))).card:ℝ) ≤ Density k) ∧
        (∀ i, (((S i).filter (fun j => band i j=none)).card:ℝ) ≤ Density kmax) ∧
        ∀ k : ℕ, Q k ≤ N →
        ∀ (E : Finset (ι × (ℤ × Fin 2))) (H : ι × (ℤ × Fin 2) → ℕ),
        (∀ i∈E, i.2.1∈S i.1 ∧ band i.1 i.2.1=some k) →
        (∀ i∈E, H i ≤ N) →
        ∃ (r : ι × (ℤ × Fin 2) → ℚ) (z : ι × (ℤ × Fin 2) → ℝ),
        (∀ i∈E, (r i).den ≤ Q k ∧ Q k ≤ 2*(r i).den ∧
          (anchor i.1 i.2.1 i.2.2:ℝ) < r i ∧
          |(r i:ℝ)-(anchor i.1 i.2.1 i.2.2:ℝ)| ≤ delta ∧
          z i∈Icc (za i.1 i.2.1 i.2.2) (za i.1 i.2.1 i.2.2+(N:ℝ)/16) ∧
          h i.1 (z i)=(r i:ℝ)) ∧
        (∀ i∈E, |z i-t i.2.1 i.2.2| ≤ (N:ℝ)/8 ∧
          ∀ a b : ℝ, a+(N:ℝ)/4 ≤ t i.2.1 i.2.2 →
            t i.2.1 i.2.2 ≤ b-(N:ℝ)/4 → z i∈Ioo a b) ∧
        let m := fun i => round (z i)
        let A := fun i => (L i.2.1 i.2.2-m i).toNat
        let q := fun i => (r i).den
        let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
        let ell := fun i => deriv (f i.1) (m i)
        let U₃ := J/(2*σ*(N:ℝ)*R^2)
        (∀ i∈E, |z i-(m i:ℝ)| ≤ 1/2 ∧
          N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2.1 i.2.2) ∧
        ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q k:ℝ)*(N:ℝ)^2 ≤ K₀ →
        ∃ v : ι × (ℤ × Fin 2) → ℤ, (∀ i∈E, (q i:ℤ) ∣ (r i).num*v i-1) ∧
        let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ell i⌋+(p:ℕ) : ℤ)
        let tau := fun i p => ((b i p:ℝ)-(q i:ℝ)*ell i)/2
        let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
        let K := fun i => -2*μ i*(s i)^3
        let x := fun i p =>
          (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*tau i p/2] : Fin 4 → ℝ)
        ∃ mode : ZMod K₀,
          (∑ i∈E, ‖∑ n∈Finset.Ioc (L i.2.1 i.2.2) (L i.2.1 i.2.2+H i),
            (𝐞 (f i.1 n):ℂ)‖) ≤
            C*((1+Real.log K₀)*
              (∑ i∈E, ∑ p : Fin 2,
                (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
                ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*mode))*
                  GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                    (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                      Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
              ∑ i∈E, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hfourier⟩ := positive_difference_dyadic_anchor_source_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro ι S F y base N Qbase kmax Acut Bmajor η T M R
    hN hη hηmax hy hT hM hR hreg hbound htests hnegative hscale
    hAcut hAQ hBmajor hpoints hNQmax hbuffer hfourBudget hquadBudget
    f h t L delta Q Ctail Clow Cerror Density
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hB : 0 ≤ Bmajor := le_trans (by positivity : (0:ℝ) ≤ 128*σ) hBmajor
  choose anchor band za hanchor hroots hband _htransfer hcounts htail using
    fun i => positive_difference_two_probe_dyadic_root_family (S i) F
      N Qbase kmax Acut (fun p => (base p:ℝ)) Bmajor
      hσ hc hJ hη hηmax (hy i) hreg hbound htests hnegative
      hT hM hN hR hscale hAcut hAQ hB (hpoints i) hNQmax
  refine ⟨anchor,band,za,hanchor,hroots,?_⟩
  intro Good
  refine ⟨hband,hcounts,htail,?_⟩
  intro k hQN E H hE hH
  have hgood i (hi : i∈E) : Good i.1 i.2.1 k i.2.2 := by
    have hh := hband i.1 i.2.1 (hE i hi).1
    rw [(hE i hi).2] at hh
    exact hh.2.1 i.2.2
  have hL j p : (L j p:ℝ)-2*(N:ℝ)=t j p := by
    dsimp only [L,t]
    push_cast
    ring
  have hbase i (hi : i∈E) :
      (L i.2.1 i.2.2:ℝ)-2*(N:ℝ)∈Icc M (2*M) := by
    rw [hL]
    have hh := hpoints i.1 i.2.1 (hE i hi).1 i.2.2
    change M+(N:ℝ)/4 ≤ t i.2.1 i.2.2 ∧
      t i.2.1 i.2.2 ≤ 2*M-(N:ℝ)/4 at hh
    constructor <;> linarith only [hh.1,hh.2,hNp]
  have haroot i (hi : i∈E) :
      za i.1 i.2.1 i.2.2∈Ioo ((L i.2.1 i.2.2:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i.2.1 i.2.2:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
      h i.1 (za i.1 i.2.1 i.2.2)=(anchor i.1 i.2.1 i.2.2:ℝ) := by
    have hh := hroots i.1 i.2.1 (hE i hi).1 i.2.2
    refine ⟨?_,hh.1⟩
    rw [hL]
    have hb := abs_le.mp hh.2.1
    constructor <;> linarith only [hb.1,hb.2,hNp]
  obtain ⟨r,z,hr,hout⟩ := hfourier (ι × (ℤ × Fin 2)) E F
    (fun i => y i.1) (fun i => L i.2.1 i.2.2) H
    (fun i => anchor i.1 i.2.1 i.2.2) (fun i => za i.1 i.2.1 i.2.2)
    N (Q k) η T M R (by omega) hH hη hηmax hT hM hR
    (fun i _ => hy i.1) hbase hreg hbound hnegative hscale
    hbuffer hfourBudget hquadBudget hQN
    (fun i hi => (Nat.mul_le_mul_right _ hAcut).trans (hgood i hi).1)
    (fun i hi => (mul_le_mul_of_nonneg_right hBmajor (sq_nonneg R)).trans (hgood i hi).2)
    haroot
  refine ⟨r,z,hr,?_,hout⟩
  intro i hi
  have ha := abs_le.mp (hroots i.1 i.2.1 (hE i hi).1 i.2.2).2.1
  have hz := (hr i hi).2.2.2.2.1
  have hdist : |z i-t i.2.1 i.2.2| ≤ (N:ℝ)/8 := by
    apply abs_le.mpr
    constructor <;> linarith only [ha.1,ha.2,hz.1,hz.2,hNp]
  refine ⟨hdist,?_⟩
  intro a b hleft hright
  have hd := abs_le.mp hdist
  constructor <;> linarith only [hd.1,hd.2,hleft,hright,hNp]

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : ι → Finset ℤ) (F : ℝ → ℝ)
      (y : ι → ℝ) (base : Fin 2 → ℤ) (N Qbase kmax Acut : ℕ)
      (Bmajor η T M R : ℝ),
      0 < N → 0 < η → η ≤ 1/8 → (∀ i, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 2 ≤ Acut → Acut ≤ Qbase → 128*σ ≤ Bmajor →
      (∀ i, ∀ j∈S i, ∀ p,
        (base p:ℝ)+(N:ℝ)*j∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun (j : ℤ) (p : Fin 2) => (base p:ℝ)+(N:ℝ)*j
      let L := fun (j : ℤ) (p : Fin 2) => base p+(N:ℤ)*j+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Q := fun k : ℕ => Qbase*2^k
      let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
      let Clow := (3*J/σ+c/(32*σ))*(Bmajor/c)^2+Bmajor/c
      let Cerror := (Acut:ℝ)^2*Ctail+Clow
      let Density := fun k => 2*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
        (2+Real.log (64*σ*R^2/(c*((Q k:ℝ)/Acut))+1))
      ∃ (anchor : ι → ℤ → Fin 2 → ℚ) (band : ι → ℤ → Option ℕ)
        (za : ι → ℤ → Fin 2 → ℝ),
        (∀ i, ∀ j∈S i, ∀ p,
          (anchor i j p:ℝ)∈Ioo (h i (t j p)-delta) (h i (t j p)+delta) ∧
          ∀ q : ℚ, (q:ℝ)∈Ioo (h i (t j p)-delta) (h i (t j p)+delta) →
            (anchor i j p).den ≤ q.den) ∧
        (∀ i, ∀ j∈S i, ∀ p, h i (za i j p)=(anchor i j p:ℝ) ∧
          |za i j p-t j p| ≤ (N:ℝ)/16 ∧ za i j p∈Icc M (2*M)) ∧
        let Good := fun i j k (p : Fin 2) =>
          Acut*(anchor i j p).den ≤ Q k ∧
            Bmajor*R^2 ≤ c*(Q k:ℝ)*(anchor i j p).den
        (∀ i, ∀ j∈S i, match band i j with
          | none => ∃ p, ¬Good i j kmax p
          | some k => k ≤ kmax ∧ (∀ p, Good i j k p) ∧
              (k=0 ∨ ∃ p, ¬Good i j (k-1) p)) ∧
        (∀ i, ∀ k ≤ kmax,
          (((S i).filter (fun j => band i j=some (k+1))).card:ℝ) ≤ Density k) ∧
        (∀ i, (((S i).filter (fun j => band i j=none)).card:ℝ) ≤ Density kmax) ∧
        ∀ k : ℕ, Q k ≤ N →
        ∀ (E : Finset (ι × (ℤ × Fin 2))) (H : ι × (ℤ × Fin 2) → ℕ),
        (∀ i∈E, i.2.1∈S i.1 ∧ band i.1 i.2.1=some k) →
        (∀ i∈E, H i ≤ N) →
        ∃ (r : ι × (ℤ × Fin 2) → ℚ) (z : ι × (ℤ × Fin 2) → ℝ),
        (∀ i∈E, (r i).den ≤ Q k ∧ Q k ≤ 2*(r i).den ∧
          (anchor i.1 i.2.1 i.2.2:ℝ) < r i ∧
          |(r i:ℝ)-(anchor i.1 i.2.1 i.2.2:ℝ)| ≤ delta ∧
          z i∈Icc (za i.1 i.2.1 i.2.2) (za i.1 i.2.1 i.2.2+(N:ℝ)/16) ∧
          h i.1 (z i)=(r i:ℝ)) ∧
        (∀ i∈E, |z i-t i.2.1 i.2.2| ≤ (N:ℝ)/8 ∧
          ∀ a b : ℝ, a+(N:ℝ)/4 ≤ t i.2.1 i.2.2 →
            t i.2.1 i.2.2 ≤ b-(N:ℝ)/4 → z i∈Ioo a b) ∧
        let m := fun i => round (z i)
        let A := fun i => (L i.2.1 i.2.2-m i).toNat
        let q := fun i => (r i).den
        let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
        let ell := fun i => deriv (f i.1) (m i)
        let U₃ := J/(2*σ*(N:ℝ)*R^2)
        (∀ i∈E, |z i-(m i:ℝ)| ≤ 1/2 ∧
          N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2.1 i.2.2) ∧
        ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q k:ℝ)*(N:ℝ)^2 ≤ K₀ →
        ∃ v : ι × (ℤ × Fin 2) → ℤ, (∀ i∈E, (q i:ℤ) ∣ (r i).num*v i-1) ∧
        let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ell i⌋+(p:ℕ) : ℤ)
        let tau := fun i p => ((b i p:ℝ)-(q i:ℝ)*ell i)/2
        let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
        let K := fun i => -2*μ i*(s i)^3
        let x := fun i p =>
          (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*tau i p/2] : Fin 4 → ℝ)
        ∃ mode : ZMod K₀,
          (∑ i∈E, ‖∑ n∈Finset.Ioc (L i.2.1 i.2.2) (L i.2.1 i.2.2+H i),
            (𝐞 (f i.1 n):ℂ)‖) ≤
            C*((1+Real.log K₀)*
              (∑ i∈E, ∑ p : Fin 2,
                (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
                ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*mode))*
                  GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                    (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                      Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
              ∑ i∈E, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  HuxleyBoundaryCoverScratch.positive_difference_selected_dyadic_family_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ


#print axioms positive_difference_selected_dyadic_family_fourier

private theorem exists_positive_difference_triangular_regime_source_sieve
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧ ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale Rphys Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc T M δ θ a : ℝ},
    (0 < η) →
    (η ≤ 1/8) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (0 < θ) →
    (0 < a) →
    (θ < 1) →
    (θ ≤ 1/(8*(L+3))) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*Rphys^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let ell := fun (i : ℝ × ℤ) => deriv (f (i.1)) (round (z i))
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
      x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let Pall := (V ×ˢ V).filter (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
      (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let h := fun (i : ℝ × ℤ) => iteratedDeriv 2 (f (i.1)) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := iref.1
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((ip.1.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((ip.1.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip = offset jp) ∧
    ∃ Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ)) ∧
      (∀ ij∈Pall,
        Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
        let t := (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/t=h ij.2.1 ∧
        |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |tau ij.1-tau ij.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(Mat ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 2:ℝ)*ell ij.1.1
          let F₂ := ell ij.2.1-2*(Mat ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 0:ℝ)*ell ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(Mat ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          Mat ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (rat ij.2.1).num-(rat ij.1.1).num)) ∧
      (∀ ij∈Pall, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(Mat ij 2:ℝ)| ≤ Rphys^4/(6*(N:ℝ)^2*Vscale)) ∧
      (∀ key, ∀ ij∈Pairs key,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
          |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
          |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0)) ∧
      let TypeOne := fun key => (Pairs key).filter (fun ij =>
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * Uband ≤ L))
      let Rest := fun key => (Pairs key).filter (fun ij => ij∉TypeOne key)
      let Upper := fun key => (Rest key).filter (fun ij => Mat ij 2=0)
      let NonUpper := fun key => (Rest key).filter (fun ij => Mat ij 2≠0)
      let Lower := fun key => (NonUpper key).filter (fun ij => Mat ij 1=0)
      let Large := fun key => (NonUpper key).filter (fun ij => Mat ij 1≠0)
      let Y := S.image Prod.fst
      let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
        ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
      let phaseFiber := fun (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) ab =>
        (P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget
      (∀ key, (((TypeOne key).card:ℝ) ≤
        Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep)) ∧
        (∀ ij∈Pairs key, ij∉TypeOne key →
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
            |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
            |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
          (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧
            8*Uband ≤ |(Mat ij 2:ℝ)| * lambda^2 ∧
            64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| * κ^2*T))) ∧
      (∀ key, ((Pairs key).card:ℝ)=((TypeOne key).card:ℝ)+∑ ab∈Y ×ˢ Y,
        (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
          ((phaseFiber (Large key) ab).card:ℝ))) ∧
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*
              (Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep)+∑ ab∈Y ×ˢ Y,
                (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
                  ((phaseFiber (Large key) ab).card:ℝ)))) ∧
      (Vscale=1+Rphys^4/(6*(N:ℝ)^2) →
        (∀ key, ∀ ij∈Pairs key, Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0) ∧
        (∀ key, Lower key=∅ ∧ Large key=∅)) ∧
      (Uband ≤ 1/16 → Vscale=1+Rphys^4*Uband^2/(N:ℝ)^2 →
        (∀ key, ∀ ij∈Pairs key, Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0) ∧
        (∀ key, Upper key=∅ ∧ Large key=∅)) := by
  classical
  intro κ Ratio L
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ :=
    exists_positive_difference_joint_type_decomposed_source_sieve hσsrc hcsrc hUsrc hE hσ hεloss
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  intro S Fsrc z rat v Nlen Q K₀ N instK Vscale Rphys Jsep Z
    η Tsrc T M δ θ a hη hηmax hTsrc hT hM hδ hscale hQ hθ ha
    hθmax hθaction hy hz hreg hjets htests hden hinv hnegative hMtwo
    hVscale hN hJsep hJM hNM hmesh hgeometry hseparation
    Fmodel hmodel f hlevel hminor hcomplete Hsrc lambda Uband u w chart narrow
    qell V offset color ChartCap NarrowCap Cap
    q μ ell b tau dual x cloud radius Pall Fiber Pairs μ₀ U₀ h D Δ
  obtain ⟨hcard,hcharts,hratios,Mat,hfourier,hglobal,hnarrow,hclass,hrest⟩ :=
    hsource S Fsrc z rat v Nlen Q K₀ N Vscale Rphys Jsep Z
      (η:=η) (Tsrc:=Tsrc) (T:=T) (M:=M) (δ:=δ) (θ:=θ) (a:=a)
      hη hηmax hTsrc hT hM hδ hscale hQ hθ ha hθmax hθaction
      hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale
      hN hJsep hJM hNM hmesh hgeometry hseparation hmodel hlevel hminor hcomplete
  refine ⟨hcard,hcharts,hratios,Mat,hfourier,hglobal,hnarrow,hclass,?_⟩
  intro TypeOne Rest Upper NonUpper Lower Large Y forget phaseFiber
  obtain ⟨htype,hsplit,hfinal⟩ := hrest
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hVp : 0 < Vscale := zero_lt_one.trans_le hVscale
  have hall key ij (hij : ij∈Pairs key) : ij∈Pall := by
    have hp := Finset.mem_filter.mp hij
    have hi := Finset.mem_filter.mp (Finset.mem_product.mp hp.1).1
    have hj := Finset.mem_filter.mp (Finset.mem_product.mp hp.1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi.1,hj.1⟩,hp.2⟩
  refine ⟨htype,hsplit,hfinal,?_,?_⟩
  · intro hchoice
    have hzero key ij (hij : ij∈Pairs key) : Mat ij 2=0 := by
      have hc := (hnarrow ij (hall key ij hij)).2
      have hstrict : Rphys^4/(6*(N:ℝ)^2*Vscale) < 1 := by
        apply (div_lt_one₀ (by positivity : 0 < 6*(N:ℝ)^2*Vscale)).mpr
        have he : 6*(N:ℝ)^2*Vscale=6*(N:ℝ)^2+Rphys^4 := by
          rw [hchoice]
          field_simp
        nlinarith only [he,sq_pos_of_pos hNp]
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast hc.trans_lt hstrict)
    refine ⟨?_,?_⟩
    · intro key ij hij
      rcases hclass key ij hij with hid | hu | hl | hn
      · exact ⟨hid.1,hid.2.2.2,hid.2.2.1⟩
      · exact ⟨hu.1,hu.2.1,hu.2.2.1⟩
      · exact False.elim (hl.2.2.2.1 (hzero key ij hij))
      · exact False.elim (hn.2 (hzero key ij hij))
    · intro key
      have hEmpty : NonUpper key=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ij hij
        have hh := Finset.mem_filter.mp hij
        exact hh.2 (hzero key ij (Finset.mem_filter.mp hh.1).1)
      constructor <;> simp only [Lower,Large,hEmpty,Finset.filter_empty]
  · intro hsmall hchoice
    have hUp : 0 < Uband := by dsimp only [Uband]; positivity
    have hcurv i (hi : i∈S) : |h i| ≤ Uband := by
      have hh := positive_difference_half_curvature_source_bounds Fsrc
        hσsrc hcsrc hUsrc hη hηmax hTsrc hM (hy i hi) (hz i hi)
        hreg hjets htests
      apply hh.2.trans
      simpa only [Uband,mul_assoc] using div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ 3*Usrc/σsrc))
        (by positivity : (0:ℝ) ≤ 2*M^2)
    have hzero key ij (hij : ij∈Pairs key) : Mat ij 1=0 := by
      have hg := hglobal ij (hall key ij hij)
      have hc := (hnarrow ij (hall key ij hij)).2
      have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
      have hi := (Finset.mem_product.mp (Finset.mem_filter.mp hp.1).1).1
      have hj := (Finset.mem_product.mp (Finset.mem_filter.mp hp.2).1).1
      let ta := (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3
      have htlo : (1:ℝ)/2 ≤ ta := hg.2.2.1
      have hthi : ta ≤ 2 := hg.2.2.2.1
      have htp : 0 < ta := by linarith only [htlo]
      have hmap : ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/ta=h ij.2.1 := hg.2.2.2.2.1
      have hdetR : (Mat ij 0:ℝ)*Mat ij 3-(Mat ij 1:ℝ)*Mat ij 2=1 := by
        exact_mod_cast hg.1
      have he := bourgain_mobius_entry_bounds hdetR htlo hthi hmap
        (hcurv _ hi) (hcurv _ hj)
      have hrel := (div_eq_iff htp.ne').mp hmap
      have hb : |(Mat ij 1:ℝ)| ≤ |(Mat ij 2:ℝ)| *Uband^2+4*Uband := by
        calc
          _ = |h ij.2.1*ta-(Mat ij 0:ℝ)*h ij.1.1| := by
            congr 1
            linarith only [hrel]
          _ ≤ |h ij.2.1*ta|+|(Mat ij 0:ℝ)*h ij.1.1| := abs_sub _ _
          _ = |h ij.2.1| *ta+|(Mat ij 0:ℝ)| *|h ij.1.1| := by
            rw [abs_mul,abs_mul,abs_of_pos htp]
          _ ≤ Uband*2+(|(Mat ij 2:ℝ)| *Uband+2)*Uband := by
            exact add_le_add
              (mul_le_mul (hcurv _ hj) hthi htp.le hUp.le)
              (mul_le_mul he.1 (hcurv _ hi) (abs_nonneg _) (by positivity))
          _ = _ := by ring
      have hweighted : |(Mat ij 2:ℝ)| *Uband^2 ≤
          Rphys^4*Uband^2/(6*(N:ℝ)^2*Vscale) := by
        convert mul_le_mul_of_nonneg_right hc (sq_nonneg Uband) using 1
        ring
      have hgain : Rphys^4*Uband^2/(6*(N:ℝ)^2*Vscale) < 1/6 := by
        apply (div_lt_iff₀ (by positivity : 0 < 6*(N:ℝ)^2*Vscale)).mpr
        have heV : (N:ℝ)^2*Vscale=(N:ℝ)^2+Rphys^4*Uband^2 := by
          rw [hchoice]
          field_simp
        nlinarith only [heV,sq_pos_of_pos hNp]
      exact Int.abs_lt_one_iff.mp (by
        exact_mod_cast (show |(Mat ij 1:ℝ)| < 1 by
          linarith only [hb,hweighted,hgain,hsmall]))
    refine ⟨?_,?_⟩
    · intro key ij hij
      rcases hclass key ij hij with hid | hu | hl | hn
      · exact ⟨hid.1,hid.2.2.2,hid.2.1⟩
      · exact False.elim (hu.2.2.2.1 (hzero key ij hij))
      · exact ⟨hl.1,hl.2.1,hl.2.2.1⟩
      · exact False.elim (hn.1 (hzero key ij hij))
    · intro key
      constructor
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ij hij
        have hr := Finset.mem_filter.mp hij
        have hp := (Finset.mem_filter.mp hr.1).1
        have hz := hzero key ij hp
        have hc := hclass key ij hp
        have hnot := (Finset.mem_filter.mp hr.1).2
        apply hnot
        apply Finset.mem_filter.mpr
        refine ⟨hp,Or.inl ?_⟩
        rcases hc with hid | hu | hl | hn
        · exact hid
        · exact False.elim (hu.2.2.2.1 hz)
        · exact False.elim (hl.2.2.2.1 hr.2)
        · exact False.elim (hn.1 hz)
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ij hij
        have hh := Finset.mem_filter.mp hij
        exact hh.2 (hzero key ij
          (Finset.mem_filter.mp (Finset.mem_filter.mp hh.1).1).1)

example
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ C Dtype : ℝ, 0 < C ∧ 0 < Dtype ∧ ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale Rphys Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc T M δ θ a : ℝ},
    (0 < η) →
    (η ≤ 1/8) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (0 < θ) →
    (0 < a) →
    (θ < 1) →
    (θ ≤ 1/(8*(L+3))) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*Rphys^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let ell := fun (i : ℝ × ℤ) => deriv (f (i.1)) (round (z i))
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
      x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let Pall := (V ×ˢ V).filter (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
      (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let h := fun (i : ℝ × ℤ) => iteratedDeriv 2 (f (i.1)) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := iref.1
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((ip.1.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((ip.1.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip = offset jp) ∧
    ∃ Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*((Pairs key).card:ℝ)) ∧
      (∀ ij∈Pall,
        Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
        let t := (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/t=h ij.2.1 ∧
        |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |tau ij.1-tau ij.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(Mat ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 2:ℝ)*ell ij.1.1
          let F₂ := ell ij.2.1-2*(Mat ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 0:ℝ)*ell ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(Mat ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          Mat ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (rat ij.2.1).num-(rat ij.1.1).num)) ∧
      (∀ ij∈Pall, |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2*Vscale) ∧
        |(Mat ij 2:ℝ)| ≤ Rphys^4/(6*(N:ℝ)^2*Vscale)) ∧
      (∀ key, ∀ ij∈Pairs key,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
          |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
          |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0)) ∧
      let TypeOne := fun key => (Pairs key).filter (fun ij =>
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * Uband ≤ L))
      let Rest := fun key => (Pairs key).filter (fun ij => ij∉TypeOne key)
      let Upper := fun key => (Rest key).filter (fun ij => Mat ij 2=0)
      let NonUpper := fun key => (Rest key).filter (fun ij => Mat ij 2≠0)
      let Lower := fun key => (NonUpper key).filter (fun ij => Mat ij 1=0)
      let Large := fun key => (NonUpper key).filter (fun ij => Mat ij 1≠0)
      let Y := S.image Prod.fst
      let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
        ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
      let phaseFiber := fun (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) ab =>
        (P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget
      (∀ key, (((TypeOne key).card:ℝ) ≤
        Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep)) ∧
        (∀ ij∈Pairs key, ij∉TypeOne key →
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
            |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
            |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
          (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧
            8*Uband ≤ |(Mat ij 2:ℝ)| * lambda^2 ∧
            64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| * κ^2*T))) ∧
      (∀ key, ((Pairs key).card:ℝ)=((TypeOne key).card:ℝ)+∑ ab∈Y ×ˢ Y,
        (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
          ((phaseFiber (Large key) ab).card:ℝ))) ∧
      (∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*
              (Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep)+∑ ab∈Y ×ˢ Y,
                (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
                  ((phaseFiber (Large key) ab).card:ℝ)))) ∧
      (Vscale=1+Rphys^4/(6*(N:ℝ)^2) →
        (∀ key, ∀ ij∈Pairs key, Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0) ∧
        (∀ key, Lower key=∅ ∧ Large key=∅)) ∧
      (Uband ≤ 1/16 → Vscale=1+Rphys^4*Uband^2/(N:ℝ)^2 →
        (∀ key, ∀ ij∈Pairs key, Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0) ∧
        (∀ key, Upper key=∅ ∧ Large key=∅)) :=
  HuxleyBoundaryCoverScratch.exists_positive_difference_triangular_regime_source_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hE hσ hεloss


#print axioms exists_positive_difference_triangular_regime_source_sieve

private theorem triangular_integer_family_encoding
    {ι : Type*} (P : Finset ι) (Mat : ι → Fin 4 → ℤ) (isUpper : Bool)
    (hdata : ∀ p∈P, Mat p 0=1 ∧ Mat p 3=1 ∧
      (if isUpper then Mat p 2=0 else Mat p 1=0))
    (hne : ∀ p∈P, Mat p≠(![1,0,0,1] : Fin 4 → ℤ)) :
    ∃ (entry : ι → ℤ) (Canon : ℤ → Fin 4 → ℤ),
      Function.Injective Canon ∧
      (∀ p∈P, Canon (entry p)=Mat p) ∧
      (∀ p∈P, entry p≠0) ∧
      ∀ t, if isUpper then
        Canon t 0=1 ∧ Canon t 2=0 ∧ Canon t 3=1 ∧ Canon t 1=t
      else Canon t 0=1 ∧ Canon t 1=0 ∧ Canon t 3=1 ∧ Canon t 2=t := by
  let entry := fun p => if isUpper then Mat p 1 else Mat p 2
  let Canon := fun t : ℤ =>
    if isUpper then (![1,t,0,1] : Fin 4 → ℤ) else (![1,0,t,1] : Fin 4 → ℤ)
  have hCanon : Function.Injective Canon := by
    intro a b he
    cases hb : isUpper
    · have hh := congrFun he 2
      simpa only [Canon,hb,Bool.false_eq_true,if_false,Matrix.cons_val_two,
        Matrix.cons_val_zero] using hh
    · have hh := congrFun he 1
      simpa only [Canon,hb,if_true,Matrix.cons_val_one,Matrix.cons_val_zero] using hh
  have hMatrix p (hp : p∈P) : Canon (entry p)=Mat p := by
    have hh := hdata p hp
    cases hb : isUpper
    · have hz : Mat p 1=0 := by
        simpa only [hb,Bool.false_eq_true,if_false] using hh.2.2
      have he : Canon (entry p)=(![1,0,Mat p 2,1] : Fin 4 → ℤ) := by
        simp only [Canon,entry,hb,Bool.false_eq_true,if_false]
      rw [he]
      funext i
      fin_cases i
      · exact hh.1.symm
      · exact hz.symm
      · rfl
      · exact hh.2.1.symm
    · have hz : Mat p 2=0 := by simpa only [hb,if_true] using hh.2.2
      have he : Canon (entry p)=(![1,Mat p 1,0,1] : Fin 4 → ℤ) := by
        simp only [Canon,entry,hb,if_true]
      rw [he]
      funext i
      fin_cases i
      · exact hh.1.symm
      · rfl
      · exact hz.symm
      · exact hh.2.1.symm
  refine ⟨entry,Canon,hCanon,hMatrix,?_,?_⟩
  · intro p hp he
    apply hne p hp
    rw [←hMatrix p hp,he]
    dsimp only [Canon]
    split_ifs <;> rfl
  · intro t
    cases hb : isUpper
    · simp only [Canon,hb,Bool.false_eq_true,if_false]
      exact ⟨rfl,rfl,rfl,rfl⟩
    · simp only [Canon,hb,if_true]
      exact ⟨rfl,rfl,rfl,rfl⟩

example
    {ι : Type*} (P : Finset ι) (Mat : ι → Fin 4 → ℤ) (isUpper : Bool)
    (hdata : ∀ p∈P, Mat p 0=1 ∧ Mat p 3=1 ∧
      (if isUpper then Mat p 2=0 else Mat p 1=0))
    (hne : ∀ p∈P, Mat p≠(![1,0,0,1] : Fin 4 → ℤ)) :
    ∃ (entry : ι → ℤ) (Canon : ℤ → Fin 4 → ℤ),
      Function.Injective Canon ∧
      (∀ p∈P, Canon (entry p)=Mat p) ∧
      (∀ p∈P, entry p≠0) ∧
      ∀ t, if isUpper then
        Canon t 0=1 ∧ Canon t 2=0 ∧ Canon t 3=1 ∧ Canon t 1=t
      else Canon t 0=1 ∧ Canon t 1=0 ∧ Canon t 3=1 ∧ Canon t 2=t :=
  HuxleyBoundaryCoverScratch.triangular_integer_family_encoding (ι:=ι) P Mat isUpper hdata hne

#print axioms triangular_integer_family_encoding

private theorem eventually_positive_difference_indexed_triangular_source_mass
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ {σ Jref εloss E θ : ℝ}, 0 < σ → 0 ≤ Jref → 0 < εloss →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ) (chartKey : ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*yp i))/(σsrc*η)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ t∈P, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ t∈P, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (∀ p∈P, Mat p 0=1 ∧ Mat p 3=1 ∧
      (if isUpper then Mat p 2=0 else Mat p 1=0)) →
    (∀ p∈P, Mat p≠(![1,0,0,1] : Fin 4 → ℤ)) →
    (P.card:ℝ) ≤ (if isUpper then Kupper else Klower)*T^εloss := by
  classical
  obtain ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hmassFn⟩ :=
    eventually_positive_difference_global_triangular_source_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,CU,CL,DU,DL,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro σ Jref εloss E θ hσ hJref hεloss
  filter_upwards [hmassFn (E:=E) (θ:=θ) hσ hJref hεloss] with T hmass
  intro Fsrc η ya yb Tsrc chartKey Uref Refs Gaps Bselect P Mat gap
    N za zb AlenA AlenB Za Zb Q K₀ inst rat vinv parity anchor e r v s
    δ M R base Bcut A W x xlocal
    hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hbase hgapMem hgeometryA hgeometryB hregime
    lambda yp F chartColor hchartColor
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap
    hQN hNM hUR hrHeight hsHeight heHeight hvHeight
    ε sourceColor hsourceColor f hlevel q mu ell b cround tau dual cloud radius
    hcolor hnear κ Cphys c J B hsmall hNR hRN hNcube hminscale
    hMatdet hMatt hMatmap hMatgamma H hNtwo hL hU hanchor hcut hcount
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
    Kupper Klower isUpper hdata hne
  obtain ⟨entry,Canon,hCanon,hMatrix,hEntry,hTri⟩ :=
    triangular_integer_family_encoding P Mat isUpper hdata hne
  have hh := hmass Fsrc η ya yb Tsrc (fun _ => chartKey) Uref Refs Gaps
    (Bselect:=Bselect) P entry Canon gap N za zb AlenA AlenB Za Zb Q K₀
    rat vinv parity anchor e r v s (δ:=δ) (M:=M) (R:=R) (base:=base) (Bcut:=Bcut) A (W:=W)
    hCanon hη hηsmall hya hyb hreg hjets htests hTsrc hMtwo hsourceScale
    hEntry hbase hgapMem hgeometryA hgeometryB hregime hchartColor
    hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hden hθ hθmax
    hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNM hUR
    hrHeight hsHeight heHeight hvHeight hsourceColor hlevel hcolor hnear
    hsmall hNR hRN hNcube hminscale
    (by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      rw [hMatrix p hp]
      exact hMatdet p hp)
    (by
      intro p hp
      rw [hMatrix p hp]
      exact hMatt p hp)
    (by
      intro p hp
      rw [hMatrix p hp]
      exact hMatmap p hp)
    (by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      rw [hMatrix p hp]
      exact hMatgamma p hp)
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize
  by_cases hb : isUpper=true
  · have hout := hh.1 (by
      intro t _ht
      simpa only [hb,if_true] using hTri t)
    simpa only [hb,if_true] using hout
  · have hout := hh.2 (by
      intro t _ht
      simpa only [hb,if_false] using hTri t)
    simpa only [hb,if_false] using hout

example
    {σsrc csrc Usrc : ℝ} (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc) :
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ, 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ {σ Jref εloss E θ : ℝ}, 0 < σ → 0 ≤ Jref → 0 < εloss →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (η ya yb Tsrc : ℝ) (chartKey : ℤ × ℤ × ℤ)
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
    (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ)
    (gap : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℝ × ℝ)
    (N : ℕ) (za zb : ℤ → ℝ) (AlenA AlenB : ℤ → ℕ) (Za Zb : ℤ)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℚ) (vinv : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → ℤ)
    (parity : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 2 → Fin 2) (anchor : ((ℤ × Fin 2) × (ℤ × Fin 2)) → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {δ M R base Bcut : ℝ}
    (A : Fin 2 → ℤ) {W : Fin 2 → ℝ},
    let x := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) => (![za ij.1.1,zb ij.2.1] : Fin 2 → ℝ)
    let xlocal := fun ij i => x ij i-(A i:ℝ)
    0 < η → η ≤ η₀ →
    ya∈Icc (1:ℝ) 2 → yb∈Icc (1:ℝ) 2 →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    0 < Tsrc → 2 ≤ M → Tsrc ≤ E*T →
    (∀ ij∈P, base ≤ za ij.1.1-(A 0:ℝ)) →
    (∀ ij∈P, gap ij∈Gaps) →
    (∀ ij∈P, N ≤ AlenA ij.1.1 ∧ AlenA ij.1.1 ≤ 3*N ∧
      round (za ij.1.1)+(AlenA ij.1.1:ℤ)=Za+(N:ℤ)*ij.1.1+2*(N:ℤ)) →
    (∀ ij∈P, N ≤ AlenB ij.2.1 ∧ AlenB ij.2.1 ≤ 3*N ∧
      round (zb ij.2.1)+(AlenB ij.2.1:ℤ)=Zb+(N:ℤ)*ij.2.1+2*(N:ℤ)) →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let yp : Fin 2 → ℝ := ![ya,yb]
    let F := fun (i : Fin 2) u =>
      (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)
    let chartColor := fun ij i =>
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rat ij i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rat ij i:ℝ)⁻¹)/a⌋)
    (∀ ij∈P, ∀ i, chartColor ij i=chartKey) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ) →
    (0 < T) →
    (0 < M) →
    (0 < (N:ℝ)) →
    (1 ≤ R) →
    (R ≤ M) →
    (0 < Q) →
    (T*(N:ℝ)*R^2=M^3) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i, M ≤ A i) →
    (∀ i, A i+W i ≤ 2*M) →
    (∀ ij∈P, ∀ i, xlocal ij i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, (rat ij i).den ≤ Q ∧ Q ≤ 2*(rat ij i).den) →
    (0 < θ) →
    (θ ≤ 1/24) →
    (∀ ij∈P, ∀ i, ((rat ij i).den:ℤ) ∣ (rat ij i).num*vinv ij i-1) →
    (∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) →
    (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ ij∈P, ∀ i, xlocal ij i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1 ≤ Uref) →
    (2+168/modelPhaseThirdLower σ ≤ Bselect) →
    (7*Bcut ≤ modelPhaseThirdLower σ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ ij∈P, (rat ij 0:ℝ)∈Icc (gap ij).1 (gap ij).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((v ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let sourceColor := fun ij i => (⌊((rat ij i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((rat ij i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ ij∈P, sourceColor ij 0=sourceColor ij 1) →
    let f := fun (i : Fin 2) w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*yp i))/(σsrc*η)
    (∀ ij∈P, ∀ i, iteratedDeriv 2 (f i) (x ij i)/2=(rat ij i:ℝ)) →
    let q := fun ij i => (rat ij i).den
    let mu := fun ij i => iteratedDeriv 3 (f i) (round (x ij i))/6
    let ell := fun ij i => deriv (f i) (round (x ij i))
    let b := fun ij i => (⌊(q ij i:ℝ)*ell ij i⌋+(parity ij i:ℕ) : ℤ)
    let cround := fun ij i => round ((q ij i:ℝ)*ell ij i)
    let tau := fun ij i => ((b ij i:ℝ)-(q ij i:ℝ)*ell ij i)/2
    let dual := fun ij i => -2*mu ij i*(Real.sqrt (2/(3*mu ij i*(q ij i:ℝ))))^3
    let cloud := fun ij i => (![Int.fract (-(vinv ij i:ℝ)*b ij i/q ij i),
      Int.fract (-(vinv ij i:ℝ)/q ij i),dual ij i/Real.sqrt K₀,
      (3*dual ij i*tau ij i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ ij∈P, b ij 0-cround ij 0=b ij 1-cround ij 1) →
    (∀ ij∈P, ∀ a, |cloud ij 0 a-cloud ij 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 →
    R ≤ (N:ℝ) →
    (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    (∀ t∈P, Mat t 0*Mat t 3-Mat t 1*Mat t 2=1) →
    (∀ ij∈P, (Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3=(q ij 1:ℝ)/q ij 0) →
    (∀ ij∈P, ((Mat ij 0:ℝ)*(rat ij 0:ℝ)+Mat ij 1)/
      ((Mat ij 2:ℝ)*(rat ij 0:ℝ)+Mat ij 3)=(rat ij 1:ℝ)) →
    (∀ t∈P, |(Mat t 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ ij∈P, ∀ i, xlocal ij i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, ∀ i, xlocal ij i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ ij∈P, |(anchor ij:ℝ)-(rat ij 0:ℝ)| ≤ ε) →
    (∀ ij∈P, 256*((anchor ij).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ ij∈P, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor ij).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (∀ p∈P, Mat p 0=1 ∧ Mat p 3=1 ∧
      (if isUpper then Mat p 2=0 else Mat p 1=0)) →
    (∀ p∈P, Mat p≠(![1,0,0,1] : Fin 4 → ℤ)) →
    (P.card:ℝ) ≤ (if isUpper then Kupper else Klower)*T^εloss :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_indexed_triangular_source_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) hσsrc hcsrc hUsrc

#print axioms eventually_positive_difference_indexed_triangular_source_mass

private theorem eventually_positive_difference_actual_triangular_phase_mass
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (2 ≤ M) →
    (0 < N) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Y := S.image Prod.fst
    let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
      x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    ∀ (key : (ℤ × ℤ × ℤ) × (ℤ × ℤ) × ℤ) (ab : ℝ × ℝ), ab∈Y ×ˢ Y →
    ∀ (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
      (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ),
    (∀ p∈P, (ab.1,p.1.1)∈S ∧ (ab.2,p.2.1)∈S) →
    (∀ p∈P, color ((ab.1,p.1.1),p.1.2)=key ∧ color ((ab.2,p.2.1),p.2.2)=key) →
    (∀ p∈P, ∀ d,
      |cloud ((ab.1,p.1.1),p.1.2) d-cloud ((ab.2,p.2.1),p.2.2) d| ≤ 2*radius d) →
    (∀ p∈P, Mat p 0*Mat p 3-Mat p 1*Mat p 2=1) →
    (∀ p∈P, (Mat p 2:ℝ)*(rat (ab.1,p.1.1):ℝ)+Mat p 3=
      ((rat (ab.2,p.2.1)).den:ℝ)/(rat (ab.1,p.1.1)).den) →
    (∀ p∈P, ((Mat p 0:ℝ)*(rat (ab.1,p.1.1):ℝ)+Mat p 1)/
      ((Mat p 2:ℝ)*(rat (ab.1,p.1.1):ℝ)+Mat p 3)=(rat (ab.2,p.2.1):ℝ)) →
    (∀ p∈P, |(Mat p 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    ∀ isUpper : Bool,
    (∀ p∈P, Mat p 0=1 ∧ Mat p 3=1 ∧
      (if isUpper then Mat p 2=0 else Mat p 1=0)) →
    (∀ p∈P, Mat p≠(![1,0,0,1] : Fin 4 → ℤ)) →
    (P.card:ℝ) ≤ (if isUpper then Kupper else Klower)*T^εloss := by
  classical
  intro κ
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hcountFn⟩ :=
    eventually_positive_difference_indexed_triangular_source_mass hσsrc hcsrc hUsrc
  refine ⟨η₀,a,Cupper,Clower,Dupper,Dlower,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,?_⟩
  intro Jref θ hJref hθ hθmax
  filter_upwards [hcountFn (E:=E) (θ:=θ) hσ hJref hεloss] with T hboundFn
  intro S Fsrc z rat v Nlen Q K₀ N instK R Z
    η Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    hη hηsmall hTsrc hT hM hδ hsourceScale hQ
    hy hreg hjets htests hden hinv hMtwo hN
    hmesh hgeometry Fmodel hmodel f hlevel
    hregime hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hL hU ε hanchor hcut hcount
    lambda u w chart narrow qell offset color
    q μ b tau dual x
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
    Kupper Klower Y cloud radius key ab hab P Mat
    hSdata hColors hNear hdet ht hmap hgamma isUpper htri hNonidentity
  have hY y (hym : y∈Y) :
      y∈Icc (1:ℝ) 2 ∧ M ≤ A y ∧ A y+W y ≤ 2*M ∧
      Expdb.IsApproximateModelPhaseFunction
        (fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hym
    exact ⟨hy i hi,hA i hi,hW i hi,hmodel i hi⟩
  let yp : Fin 2 → ℝ := ![ab.1,ab.2]
  let ip := fun p : (ℤ × Fin 2) × (ℤ × Fin 2) =>
    (![((ab.1,p.1.1),p.1.2),((ab.2,p.2.1),p.2.2)] : Fin 2 → (ℝ × ℤ) × Fin 2)
  let xp := fun p : (ℤ × Fin 2) × (ℤ × Fin 2) =>
    (![z (ab.1,p.1.1),z (ab.2,p.2.1)] : Fin 2 → ℝ)
  let fp := fun i => f (yp i)
  let Ap := fun i => A (yp i)
  let Wp := fun i => W (yp i)
  let rp := fun p i => rat (ip p i).1
  let vp := fun p i => v (ip p i).1
  let pp := fun p i => (ip p i).2

  let qp := fun p i => (rp p i).den
  let mup := fun p i => iteratedDeriv 3 (fp i) (round (xp p i))/6
  let ellp := fun p i => deriv (fp i) (round (xp p i))
  let bp := fun p i => (⌊(qp p i:ℝ)*ellp p i⌋+(pp p i:ℕ) : ℤ)
  let crp := fun p i => round ((qp p i:ℝ)*ellp p i)
  let taup := fun p i => ((bp p i:ℝ)-(qp p i:ℝ)*ellp p i)/2
  let dualp := fun p i => -2*mup p i*(Real.sqrt (2/(3*mup p i*(qp p i:ℝ))))^3
  let cloudp := fun p i => (![Int.fract (-(vp p i:ℝ)*bp p i/qp p i),
    Int.fract (-(vp p i:ℝ)/qp p i),dualp p i/Real.sqrt K₀,
    (3*dualp p i*taup p i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
  have hS p (hp : p∈P) i : (ip p i).1∈S := by
    fin_cases i
    · exact (hSdata p hp).1
    · exact (hSdata p hp).2
  have hColor p (hp : p∈P) i : color (ip p i)=key := by
    fin_cases i
    · exact (hColors p hp).1
    · exact (hColors p hp).2

  have hCloudEq p (i : Fin 2) : cloudp p i=cloud (ip p i) := by
    fin_cases i <;> rfl
  have hOffsetEq p (i : Fin 2) : bp p i-crp p i=offset (ip p i) := by
    fin_cases i <;> rfl
  have hLevelPair p (hp : p∈P) (i : Fin 2) :
      iteratedDeriv 2 (fp i) (xp p i)/2=(rp p i:ℝ) := by
    fin_cases i
    · exact hlevel (ab.1,p.1.1) (hSdata p hp).1
    · exact hlevel (ab.2,p.2.1) (hSdata p hp).2
  have hOffsetPair p (hp : p∈P) : bp p 0-crp p 0=bp p 1-crp p 1 := by
    rw [hOffsetEq p 0,hOffsetEq p 1]
    exact congrArg (fun cc => cc.2.2) ((hColor p hp 0).trans (hColor p hp 1).symm)
  have hNearPair p (hp : p∈P) d :
      |cloudp p 0 d-cloudp p 1 d| ≤ 2*radius d := by
    rw [hCloudEq p 0,hCloudEq p 1]
    exact hNear p hp d
  have hLoc p i : xp p i-(Ap i:ℝ)=xlocal (ip p i).1 := by fin_cases i <;> rfl
  have hWp p i : Wp i=W (ip p i).1.1 := by fin_cases i <;> rfl
  have hChartColor p (hp : p∈P) i :
      (⌊yp i/a⌋,⌊((2*M^2/Tsrc)*(rp p i:ℝ))/a⌋,
        ⌊((Tsrc/(2*M^2))*(rp p i:ℝ)⁻¹)/a⌋)=key.1 := by
    fin_cases i
    · exact congrArg Prod.fst (hColor p hp (0 : Fin 2))
    · exact congrArg Prod.fst (hColor p hp (1 : Fin 2))
  have hYa := hY ab.1 (Finset.mem_product.mp hab).1
  have hYb := hY ab.2 (Finset.mem_product.mp hab).2
  have hAp i : M ≤ Ap i := by
    fin_cases i
    · exact hYa.2.1
    · exact hYb.2.1
  have hWpair i : (Ap i:ℝ)+Wp i ≤ 2*M := by
    fin_cases i
    · exact hYa.2.2.1
    · exact hYb.2.2.1
  have hFp i : Expdb.IsApproximateModelPhaseFunction
      (fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*yp i))/(σsrc*η)) σ 4 δ := by
    fin_cases i
    · exact hYa.2.2.2
    · exact hYb.2.2.2
  have hh : (P.card:ℝ) ≤ (if isUpper then Kupper else Klower)*T^εloss := by
    exact hboundFn Fsrc η ab.1 ab.2 Tsrc key.1 Uref Refs Gaps
      (Bselect:=Bselect) P Mat (fun p => gap (ab.1,p.1.1)) N
      (fun n => z (ab.1,n)) (fun n => z (ab.2,n))
      (fun n => Nlen (ab.1,n)) (fun n => Nlen (ab.2,n)) (Z ab.1) (Z ab.2)
      Q K₀ rp vp pp (fun p => anchor (ab.1,p.1.1)) e r vRef s
      (δ:=δ) (M:=M) (R:=R) (base:=0) (Bcut:=Bcut) Ap (W:=Wp)
      hη hηsmall hYa.1 hYb.1 hreg hjets htests hTsrc hMtwo hsourceScale
      (fun p hp => by
        change 0 ≤ xp p 0-(Ap 0:ℝ)
        rw [hLoc p 0]
        exact le_of_lt (lt_trans (by norm_num) (hx _ (hS p hp 0)).1))
      (fun p hp => hgapMem _ (hS p hp 0))
      (fun p hp => hgeometry _ (hS p hp 0))
      (fun p hp => hgeometry _ (hS p hp 1))
      hregime hChartColor hδ hFp hT hM (Nat.cast_pos.mpr hN) hR hRM hQ
      hscale hmesh hAp hWpair
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p i,hWp p i]
        exact hx _ (hS p hp i))
      (fun p hp i => hden _ (hS p hp i))
      hθ hθmax (fun p hp i => hinv _ (hS p hp i))
      hchart horientation hBcut hs hrefSet hparentSet hsep
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p i,hWp p i]
        exact hwideL _ (hS p hp i))
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p i,hWp p i]
        exact hwideU _ (hS p hp i))
      hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen (fun p hp => hfamilyGap _ (hS p hp 0))
      hgap hQN hNsqM hUR hrHeight hsHeight heHeight hvHeight
      (fun p hp => congrArg (fun cc => cc.2.1) ((hColor p hp 0).trans (hColor p hp 1).symm))
      hLevelPair hOffsetPair hNearPair
      hsmall hNR hRN hNcube hminscale
      hdet
      ht
      hmap
      hgamma
      hNtwo
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)-H∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p i,hWp p i]
        exact hL _ (hS p hp i))
      (fun p hp i => by
        change xp p i-(Ap i:ℝ)+H∈Ioo (1/2:ℝ) (Wp i-1/2)
        rw [hLoc p i,hWp p i]
        exact hU _ (hS p hp i))
      (fun p hp => hanchor _ (hS p hp 0))
      (fun p hp => hcut _ (hS p hp 0))
      (fun p hp => hcount _ (hS p hp 0))
      hsize hD hΔ hBsize
      isUpper htri hNonidentity
  exact hh

example
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    ∃ η₀ a Cupper Clower Dupper Dlower : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (R : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (2 ≤ M) →
    (0 < N) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Y := S.image Prod.fst
    let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
      x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    ∀ (key : (ℤ × ℤ × ℤ) × (ℤ × ℤ) × ℤ) (ab : ℝ × ℝ), ab∈Y ×ˢ Y →
    ∀ (P : Finset ((ℤ × Fin 2) × (ℤ × Fin 2)))
      (Mat : ((ℤ × Fin 2) × (ℤ × Fin 2)) → Fin 4 → ℤ),
    (∀ p∈P, (ab.1,p.1.1)∈S ∧ (ab.2,p.2.1)∈S) →
    (∀ p∈P, color ((ab.1,p.1.1),p.1.2)=key ∧ color ((ab.2,p.2.1),p.2.2)=key) →
    (∀ p∈P, ∀ d,
      |cloud ((ab.1,p.1.1),p.1.2) d-cloud ((ab.2,p.2.1),p.2.2) d| ≤ 2*radius d) →
    (∀ p∈P, Mat p 0*Mat p 3-Mat p 1*Mat p 2=1) →
    (∀ p∈P, (Mat p 2:ℝ)*(rat (ab.1,p.1.1):ℝ)+Mat p 3=
      ((rat (ab.2,p.2.1)).den:ℝ)/(rat (ab.1,p.1.1)).den) →
    (∀ p∈P, ((Mat p 0:ℝ)*(rat (ab.1,p.1.1):ℝ)+Mat p 1)/
      ((Mat p 2:ℝ)*(rat (ab.1,p.1.1):ℝ)+Mat p 3)=(rat (ab.2,p.2.1):ℝ)) →
    (∀ p∈P, |(Mat p 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    ∀ isUpper : Bool,
    (∀ p∈P, Mat p 0=1 ∧ Mat p 3=1 ∧
      (if isUpper then Mat p 2=0 else Mat p 1=0)) →
    (∀ p∈P, Mat p≠(![1,0,0,1] : Fin 4 → ℤ)) →
    (P.card:ℝ) ≤ (if isUpper then Kupper else Klower)*T^εloss :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_actual_triangular_phase_mass (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss

#print axioms eventually_positive_difference_actual_triangular_phase_mass

private theorem eventually_positive_difference_triangular_actual_family_source_sieve
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    let Ktri := if isUpper then Kupper else Klower
    let Y := S.image Prod.fst
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*
            (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*Vscale*Ktri*T^εloss)
 := by
  classical
  intro κ Ratio L
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hcountFn⟩ :=
    eventually_positive_difference_actual_triangular_phase_mass (E:=E) hσsrc hcsrc hUsrc hσ hεloss
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ :=
    TaoTrudgianYang2025.HuxleyRationalPhase.exists_positive_difference_triangular_regime_source_sieve hσsrc hcsrc hUsrc hE hσ hεloss
  refine ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro Jref θ hJref hθ hθmax hθaction
  filter_upwards [hcountFn (Jref:=Jref) (θ:=θ) hJref hθ hθmax] with T hboundFn
  intro S Fsrc z rat v Nlen Q K₀ N instK Vscale R Jsep Z
    η Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    hη hηsmall hTsrc hT hM hδ hsourceScale hQ
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN
    hJsep hJM hNM hmesh hgeometry hseparation Fmodel hmodel f hlevel hminor hcomplete
    hregime hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hL hU ε hanchor hcut hcount
    lambda Uband u w chart narrow qell V offset color ChartCap NarrowCap Cap
    q μ b tau dual x Fiber μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
    Kupper Klower isUpper hchoice Ktri Y
  have hηmax := hηsmall.trans hηcap
  have hθlt : θ < 1 := lt_of_le_of_lt hθmax (by norm_num)
  have hmodel₂ i (hi : i∈S) :=
    approximateModelPhase_mono (hmodel i hi) (by norm_num : 2 ≤ 4) le_rfl
  obtain ⟨hcard,hcharts,hratios,Mat,hfourier,hglobal,hnarrow,hclass,htype,hsplit,hstrong,hUpperRegime,hLowerRegime⟩ :=
    hsource S Fsrc z rat v Nlen Q K₀ N Vscale R Jsep Z
      (η:=η) (Tsrc:=Tsrc) (T:=T) (M:=M) (δ:=δ) (θ:=θ) (a:=a)
      hη hηmax hTsrc hT hM hδ hsourceScale hQ hθ ha hθlt hθaction
      hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN hJsep hJM hNM
      hmesh hgeometry hseparation hmodel₂ hlevel hminor hcomplete
  let cloud := fun ip => (![Int.fract (x ip 0),Int.fract (x ip 1),
    x ip 2/Real.sqrt K₀,x ip 3/Real.sqrt K₀] : Fin 4 → ℝ)
  let radius : Fin 4 → ℝ :=
    ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
  let wideRadius : Fin 4 → ℝ :=
    ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
  let Pall := (V ×ˢ V).filter (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
  let Pairs := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
    (fun ij => ∀ d, |cloud ij.1 d-cloud ij.2 d| ≤ 2*radius d)
  let TypeOne := fun key => (Pairs key).filter (fun ij =>
    (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
    (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * Uband ≤ L))
  let Rest := fun key => (Pairs key).filter (fun ij => ij∉TypeOne key)
  let Upper := fun key => (Rest key).filter (fun ij => Mat ij 2=0)
  let NonUpper := fun key => (Rest key).filter (fun ij => Mat ij 2≠0)
  let Lower := fun key => (NonUpper key).filter (fun ij => Mat ij 1=0)
  let Large := fun key => (NonUpper key).filter (fun ij => Mat ij 1≠0)
  let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
    ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
  let phaseFiber := fun (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (ab : ℝ × ℝ) =>
    (P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget

  change ∀ k : ZMod K₀,
        (∑ ip∈V, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x ip d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
            ∑ key∈V.image color,((Fiber key).card:ℝ)^10*
              (Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+∑ ab∈Y ×ˢ Y,
                (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
                  ((phaseFiber (Large key) ab).card:ℝ))) at hstrong
  have hPairData key ij (hij : ij∈Pairs key) :
      ij.1∈V ∧ ij.2∈V ∧ color ij.1=key ∧ color ij.2=key ∧ ij∈Pall := by
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have h1 := Finset.mem_filter.mp hp.1
    have h2 := Finset.mem_filter.mp hp.2
    exact ⟨h1.1,h2.1,h1.2,h2.2,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1.1,h2.1⟩,
        (Finset.mem_filter.mp hij).2⟩⟩
  have hMatData ij (hij : ij∈Pall) :
      Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
      (Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3=(q ij.2.1:ℝ)/q ij.1.1 ∧
      ((Mat ij 0:ℝ)*(rat ij.1.1:ℝ)+Mat ij 1)/
        ((Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3)=(rat ij.2.1:ℝ) ∧
      |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) := by
    have hg := hglobal ij hij
    have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
    have hl1 := hlevel ij.1.1 (Finset.mem_product.mp hp.1).1
    have hl2 := hlevel ij.2.1 (Finset.mem_product.mp hp.2).1
    have ht : (Mat ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 3=
        (q ij.2.1:ℝ)/q ij.1.1 := hg.2.1
    have hm : ((Mat ij 0:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 1)/
        ((Mat ij 2:ℝ)*(iteratedDeriv 2 (f ij.1.1.1) (z ij.1.1)/2)+Mat ij 3)=
        iteratedDeriv 2 (f ij.2.1.1) (z ij.2.1)/2 := hg.2.2.2.2.1
    rw [hl1] at ht
    rw [hl1,hl2] at hm
    exact ⟨hg.1,ht,hm,hg.2.2.2.2.2.1⟩
  have hRadius d : radius d ≤ wideRadius d := by
    have hKpos : (0:ℝ) < K₀ := by exact_mod_cast NeZero.pos K₀
    fin_cases d
    · exact le_rfl
    · change 1/(12*(K₀:ℝ)^2*Vscale) ≤ 1/(12*(K₀:ℝ)^2)
      apply one_div_le_one_div_of_le (by positivity)
      calc
        12*(K₀:ℝ)^2=12*(K₀:ℝ)^2*1 := by ring
        _ ≤ 12*(K₀:ℝ)^2*Vscale :=
          mul_le_mul_of_nonneg_left hVscale (by positivity)
    · exact le_rfl
    · exact le_rfl
  let Selected := fun key => if isUpper then Upper key else Lower key
  have hSelected key ij (hij : ij∈Selected key) : ij∈Rest key := by
    change ij∈(if isUpper then Upper key else Lower key) at hij
    split_ifs at hij
    · exact (Finset.mem_filter.mp hij).1
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1
  have hRegime key ij (hij : ij∈Pairs key) :
      Mat ij 0=1 ∧ Mat ij 3=1 ∧
        (if isUpper then Mat ij 2=0 else Mat ij 1=0) := by
    by_cases hb : isUpper=true
    · have hh : Vscale=1+R^4/(6*(N:ℝ)^2) := by
        simpa only [hb,if_true] using hchoice
      simpa only [hb,if_true] using (hUpperRegime hh).1 key ij hij
    · have hh : Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2 := by
        simpa only [hb,if_false] using hchoice
      simpa only [hb,if_false] using
        (hLowerRegime hh.1 hh.2).1 key ij hij
  have hEmpty key :
      (if isUpper then Lower key=∅ ∧ Large key=∅ else Upper key=∅ ∧ Large key=∅) := by
    by_cases hb : isUpper=true
    · have hh : Vscale=1+R^4/(6*(N:ℝ)^2) := by
        simpa only [hb,if_true] using hchoice
      simpa only [hb,if_true] using (hUpperRegime hh).2 key
    · have hh : Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2 := by
        simpa only [hb,if_false] using hchoice
      simpa only [hb,if_false] using (hLowerRegime hh.1 hh.2).2 key
  have hphaseBound key ab (hab : ab∈Y ×ˢ Y) :
      ((phaseFiber (Selected key) ab).card:ℝ) ≤ Ktri*T^εloss := by
    let P := phaseFiber (Selected key) ab
    let embed := fun p : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      (((ab.1,p.1.1),p.1.2),((ab.2,p.2.1),p.2.2))
    have hMem p (hp : p∈P) : embed p∈Selected key := by
      obtain ⟨ij,hij,he⟩ := Finset.mem_image.mp hp
      have hd := Finset.mem_filter.mp hij
      have hback : embed (forget ij)=ij := by
        rcases ij with ⟨⟨⟨ya,na⟩,pa⟩,⟨⟨yb,nb⟩,pb⟩⟩
        have hh := hd.2
        dsimp only at hh
        rcases hh with ⟨rfl,rfl⟩
        rfl
      rw [←he,hback]
      exact hd.1
    have hRest p (hp : p∈P) : embed p∈Rest key := hSelected key _ (hMem p hp)
    have hPairs p (hp : p∈P) : embed p∈Pairs key :=
      (Finset.mem_filter.mp (hRest p hp)).1
    have hNonidentity p (hp : p∈P) :
        Mat (embed p)≠(![1,0,0,1] : Fin 4 → ℤ) := by
      intro hm
      apply (Finset.mem_filter.mp (hRest p hp)).2
      apply Finset.mem_filter.mpr
      refine ⟨hPairs p hp,Or.inl ?_⟩
      rw [hm]
      exact ⟨rfl,rfl,rfl,rfl⟩
    have hh := hboundFn S Fsrc z rat v Nlen Q K₀ N R Z
      (η:=η) (Tsrc:=Tsrc) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      Uref Refs Gaps A W gap anchor e r vRef s
      hη hηsmall hTsrc hT hM hδ hsourceScale hQ
      hy hreg hjets htests hden hinv hMtwo hN hmesh hgeometry hmodel hlevel
      hregime hR hRM hscale hA hW hx hgapMem
      hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
      hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
      hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
      hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize
      key ab hab P (fun p => Mat (embed p))
      (fun p hp => by
        have hd := hPairData key _ (hPairs p hp)
        exact ⟨(Finset.mem_product.mp hd.1).1,(Finset.mem_product.mp hd.2.1).1⟩)
      (fun p hp => by
        have hd := hPairData key _ (hPairs p hp)
        exact ⟨hd.2.2.1,hd.2.2.2.1⟩)
      (fun p hp d => ((Finset.mem_filter.mp (hPairs p hp)).2 d).trans
        (mul_le_mul_of_nonneg_left (hRadius d) (by norm_num)))
      (fun p hp => (hMatData _ (hPairData key _ (hPairs p hp)).2.2.2.2).1)
      (fun p hp => (hMatData _ (hPairData key _ (hPairs p hp)).2.2.2.2).2.1)
      (fun p hp => (hMatData _ (hPairData key _ (hPairs p hp)).2.2.2.2).2.2.1)
      (fun p hp => (hMatData _ (hPairData key _ (hPairs p hp)).2.2.2.2).2.2.2)
      isUpper (fun p hp => hRegime key _ (hPairs p hp)) hNonidentity
    exact hh
  let typeMass := Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)
  let residual := fun key => ∑ ab∈Y ×ˢ Y,
    (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
      ((phaseFiber (Large key) ab).card:ℝ))
  let totalMass := (Y.card:ℝ)^2*Vscale*Ktri*T^εloss
  have hResidual key : Vscale*residual key ≤ totalMass := by
    dsimp only [residual]
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _ab∈Y ×ˢ Y, Vscale*(Ktri*T^εloss) := by
        apply Finset.sum_le_sum
        intro ab hab
        have he : ((phaseFiber (Upper key) ab).card:ℝ)+
            ((phaseFiber (Lower key) ab).card:ℝ)+((phaseFiber (Large key) ab).card:ℝ)=
            ((phaseFiber (Selected key) ab).card:ℝ) := by
          have hh := hEmpty key
          by_cases hb : isUpper=true
          · have hz : Lower key=∅ ∧ Large key=∅ := by simpa only [hb,if_true] using hh
            simp only [hz.1,hz.2,Selected,hb,if_true,phaseFiber,
              Finset.filter_empty,Finset.image_empty,Finset.card_empty,Nat.cast_zero,
              add_zero]
          · have hz : Upper key=∅ ∧ Large key=∅ := by
              simpa only [hb,if_false] using hh
            simp only [hz.1,hz.2,Selected,hb,Bool.false_eq_true,if_false,phaseFiber,
              Finset.filter_empty,Finset.image_empty,Finset.card_empty,Nat.cast_zero,
              zero_add,add_zero]
        rw [he]
        exact mul_le_mul_of_nonneg_left (hphaseBound key ab hab)
          (zero_le_one.trans hVscale)
      _ = totalMass := by
        simp only [Finset.sum_const,Finset.card_product,nsmul_eq_mul,Nat.cast_mul,totalMass]
        ring
  have hLinear :
      Vscale*(∑ key∈V.image color,((Fiber key).card:ℝ)^10*(typeMass+residual key))=
        ∑ key∈V.image color,((Fiber key).card:ℝ)^10*(Vscale*typeMass+Vscale*residual key) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro key _
    ring
  refine ⟨hcard,?_⟩
  intro k
  have hCap : 0 ≤ Cap := (Nat.cast_nonneg _).trans hcard
  calc
    _ ≤ C*Vscale*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color,((Fiber key).card:ℝ)^10*(typeMass+residual key) :=
      hstrong k
    _ = C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        (Vscale*∑ key∈V.image color,((Fiber key).card:ℝ)^10*(typeMass+residual key)) := by ac_rfl
    _ = C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color,((Fiber key).card:ℝ)^10*(Vscale*typeMass+Vscale*residual key) := by
      rw [hLinear]
    _ ≤ C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
        ∑ key∈V.image color,((Fiber key).card:ℝ)^10*
          (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+totalMass) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (pow_nonneg hCap 11))
      apply Finset.sum_le_sum
      intro key _
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) 10)
      have he : Vscale*typeMass=Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep) := by
        simp only [typeMass,mul_assoc]
      rw [he]
      exact add_le_add le_rfl (hResidual key)


example
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let Fiber := fun key => V.filter (fun ip => color ip=key)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    let Ktri := if isUpper then Kupper else Klower
    let Y := S.image Prod.fst
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*
          ∑ key∈V.image color, ((Fiber key).card:ℝ)^10*
            (Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
              (Y.card:ℝ)^2*Vscale*Ktri*T^εloss)
 :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_triangular_actual_family_source_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hE hσ hεloss


#print axioms eventually_positive_difference_triangular_actual_family_source_sieve


private theorem actual_color_tenth_weight_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) :
    (∑ key∈V.image color, ((V.filter (fun i => color i=key)).card:ℝ)^10) ≤
      (V.card:ℝ)^10 := by
  have hcard :
      (∑ key∈V.image color, ((V.filter (fun i => color i=key)).card:ℝ))=(V.card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image color V).symm
  calc
    _ = ∑ key∈V.image color,
        ((V.filter (fun i => color i=key)).card:ℝ)*
          ((V.filter (fun i => color i=key)).card:ℝ)^9 := by
      apply Finset.sum_congr rfl
      intro key _
      rw [pow_succ']
    _ ≤ ∑ key∈V.image color,
        ((V.filter (fun i => color i=key)).card:ℝ)*(V.card:ℝ)^9 := by
      apply Finset.sum_le_sum
      intro key _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast Finset.card_filter_le V (fun i => color i=key)
    _ = (V.card:ℝ)^10 := by
      rw [←Finset.sum_mul,hcard]
      ring

private theorem actual_color_tenth_weight_absorption
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) {X C B : ℝ}
    (hX : 0 ≤ X)
    (hbound : X ≤ C*(∑ key∈V.image color,
      ((V.filter (fun i => color i=key)).card:ℝ)^10*B)) :
    X ≤ C*(V.card:ℝ)^10*B := by
  classical
  by_cases hV : V=∅
  · simpa only [hV,Finset.image_empty,Finset.sum_empty,Finset.card_empty,Nat.cast_zero,
      zero_pow (by decide : (10:ℕ)≠0),mul_zero,zero_mul] using hbound
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hV
    have hf : 0 < (V.filter (fun j => color j=color i)).card :=
      Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
    have hweight : 0 < ∑ key∈V.image color,
        ((V.filter (fun j => color j=key)).card:ℝ)^10 :=
      lt_of_lt_of_le (pow_pos (Nat.cast_pos.mpr hf) 10)
        (Finset.single_le_sum
          (f:=fun key => ((V.filter (fun j => color j=key)).card:ℝ)^10)
          (fun key _ => pow_nonneg (Nat.cast_nonneg _) 10)
          (Finset.mem_image_of_mem color hi))
    have hbound' : X ≤ (C*B)*(∑ key∈V.image color,
        ((V.filter (fun i => color i=key)).card:ℝ)^10) := by
      calc
        X ≤ _ := hbound
        _ = _ := by rw [←Finset.sum_mul]; ac_rfl
    have hCB : 0 ≤ C*B := nonneg_of_mul_nonneg_left (hX.trans hbound') hweight
    calc
      X ≤ _ := hbound'
      _ ≤ (C*B)*(V.card:ℝ)^10 :=
        mul_le_mul_of_nonneg_left (actual_color_tenth_weight_bound V color) hCB
      _ = _ := by ac_rfl


private theorem cubic_completion_weight_bound
    {Q q μ₀ μ N A : ℝ}
    (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : Q ≤ 2*q) (hμ : μ₀ ≤ μ) (hNA : N ≤ A) :
    Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤ Real.sqrt (4/(Q*(μ₀*N))) := by
  have hq : 0 < q := by linarith only [hQ,hQq]
  have hμp := hμ₀.trans_le hμ
  have hAp := hN.trans_le hNA
  have hμA := mul_pos hμp hAp
  have hμN : μ₀*N ≤ μ*A := mul_le_mul hμ hNA hN.le hμp.le
  have hden := mul_pos hQ (mul_pos hμ₀ hN)
  have hright : 0 ≤ 4/(Q*(μ₀*N)) := div_nonneg (by norm_num) hden.le
  apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hq.le (Real.sqrt_nonneg _)))
    (Real.sqrt_nonneg _)).mp
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*q),
    Real.sq_sqrt hμA.le,Real.sq_sqrt hright]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hq 2) hμA) hden).mpr
  have hm := mul_le_mul hQq hμN (mul_nonneg hμ₀.le hN.le) (by positivity : 0 ≤ 2*q)
  have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*q)
  nlinarith only [hh]

private theorem cubic_completion_weighted_twelfth
    {ι : Type*} (S : Finset ι) (q μ A : ι → ℝ) (z : ι → ℂ)
    {Q μ₀ N : ℝ} (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : ∀ i∈S, Q ≤ 2*q i) (hμ : ∀ i∈S, μ₀ ≤ μ i)
    (hNA : ∀ i∈S, N ≤ A i) :
    (∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖)^12 ≤
      (4/(Q*(μ₀*N)))^6*(∑ i∈S,‖z i‖)^12 := by
  let B := 4/(Q*(μ₀*N))
  have hB : 0 ≤ B := div_nonneg (by norm_num) (mul_nonneg hQ.le (mul_nonneg hμ₀.le hN.le))
  have hweight i (hi : i∈S) :
      Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)) ≤ Real.sqrt B :=
    cubic_completion_weight_bound hQ hμ₀ hN (hQq i hi) (hμ i hi) (hNA i hi)
  have hweightNonneg i (hi : i∈S) :
      0 ≤ Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)) := by
    have hq : 0 ≤ q i := by linarith only [hQ,hQq i hi]
    exact div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hq (Real.sqrt_nonneg _))
  have hs : (∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖) ≤
      Real.sqrt B*(∑ i∈S,‖z i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (hweight i hi) (norm_nonneg _)
  have hs0 : 0 ≤ ∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖ :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hweightNonneg i hi) (norm_nonneg _))
  have hp := pow_le_pow_left₀ hs0 hs 12
  have hpow : (Real.sqrt B)^12=B^6 := by
    rw [show (12:ℕ)=2*6 by norm_num,pow_mul,Real.sq_sqrt hB]
  rw [mul_pow,hpow] at hp
  exact hp

private theorem eventually_positive_difference_triangular_selected_family_weighted_sieve
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    let Ktri := if isUpper then Kupper else Klower
    let Y := S.image Prod.fst
    let dualValue := fun (k : ZMod K₀) (ip : (ℝ × ℤ) × Fin 2) =>
      ∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)
    let Scale := C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11
    let Mass := Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Vscale*Ktri*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖dualValue k ip‖)^12 ≤ Scale*(2*(S.card:ℝ))^10*Mass ∧
      (∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/
        ((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*‖dualValue k ip‖)^12 ≤
        ((48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)))^6*
          Scale*(2*(S.card:ℝ))^10*Mass := by
  classical
  intro κ Ratio L
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
      hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hsource⟩ :=
    eventually_positive_difference_triangular_actual_family_source_sieve hσsrc hcsrc hUsrc hE hσ hεloss
  refine ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro Jref θ hJref hθ hθmax hθaction
  filter_upwards [hsource hJref hθ hθmax hθaction] with T hfamily
  intro S Fsrc z rat v Nlen Q K₀ N instK Vscale R Jsep Z
    η Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    hη hηsmall hTsrc hT hM hδ hsourceScale hQ
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN
    hJsep hJM hNM hmesh hgeometry hseparation Fmodel hmodel f hlevel hminor hcomplete
    hregime hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hL hU ε hanchor hcut hcount
    lambda Uband u w chart narrow qell V offset color ChartCap NarrowCap Cap
    q μ b tau dual x μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
    Kupper Klower isUpper hchoice Ktri Y dualValue Scale Mass

  obtain ⟨hcard,hweighted⟩ := hfamily S Fsrc z rat v Nlen Q K₀ N Vscale R Jsep Z
    (η:=η) (Tsrc:=Tsrc) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref Refs Gaps A W gap anchor e r vRef s
    hη hηsmall hTsrc hT hM hδ hsourceScale hQ
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN
    hJsep hJM hNM hmesh hgeometry hseparation hmodel hlevel hminor hcomplete
    hregime hR hRM hscale hA hW hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize isUpper hchoice
  have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hμ₀ : 0 < μ₀ := by dsimp only [μ₀]; positivity
  have hVcard : (V.card:ℝ)=2*(S.card:ℝ) := by
    simp only [V,Finset.card_product,Finset.card_univ,Fintype.card_fin,Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  have hμbounds i (hi : i∈S) : μ₀ ≤ μ i := by
    have hb := positive_difference_rounded_cubic_scales Fsrc (T:=Tsrc) (N:=M^3/Tsrc) (R:=1)
      hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) (hy i hi) hreg hjets hnegative hMtwo
      (by positivity) (by norm_num) (hz i hi) (by field_simp)
    have hlo : csrc/(12*σsrc*(M^3/Tsrc)*(1:ℝ)^2)=μ₀ := by
      dsimp only [μ₀]
      field_simp
    rw [hlo] at hb
    exact hb.1
  have hWeightScale :
      4/((Q:ℝ)*(μ₀*(N:ℝ)))=(48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)) := by
    dsimp only [μ₀]
    rw [←hscale]
    field_simp
    ring
  refine ⟨hcard,?_⟩
  intro k
  have hplain : (∑ ip∈V, ‖dualValue k ip‖)^12 ≤
      Scale*(2*(S.card:ℝ))^10*Mass := by
    have hh := actual_color_tenth_weight_absorption V color
      (pow_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) 12) (hweighted k)
    change (∑ ip∈V, ‖dualValue k ip‖)^12 ≤ Scale*(V.card:ℝ)^10*Mass at hh
    rwa [hVcard] at hh
  refine ⟨hplain,?_⟩
  have hc := cubic_completion_weighted_twelfth V
    (fun ip => (q ip.1:ℝ)) (fun ip => μ ip.1) (fun ip => (Nlen ip.1:ℝ)) (dualValue k)
    (Nat.cast_pos.mpr hQ) hμ₀ hNpos
    (fun ip hip => by
      change (Q:ℝ) ≤ 2*((rat ip.1).den:ℝ)
      exact_mod_cast (hden ip.1 (Finset.mem_product.mp hip).1).2)
    (fun ip hip => hμbounds ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => by
      change (N:ℝ) ≤ (Nlen ip.1:ℝ)
      exact_mod_cast (hgeometry ip.1 (Finset.mem_product.mp hip).1).1)
  rw [hWeightScale] at hc
  calc
    _ ≤ ((48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)))^6*
        (∑ ip∈V, ‖dualValue k ip‖)^12 := hc
    _ ≤ ((48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)))^6*
        (Scale*(2*(S.card:ℝ))^10*Mass) :=
      mul_le_mul_of_nonneg_left hplain (by positivity)
    _ = _ := by ac_rfl


private theorem eventually_positive_difference_selected_family_weighted_sieve
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    Vscale=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    let Y := S.image Prod.fst
    let dualValue := fun (k : ZMod K₀) (ip : (ℝ × ℤ) × Fin 2) =>
      ∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)
    let Scale := C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11
    let Mass := Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖dualValue k ip‖)^12 ≤ Scale*(2*(S.card:ℝ))^10*Mass ∧
      (∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/
        ((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*‖dualValue k ip‖)^12 ≤
        ((48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)))^6*
          Scale*(2*(S.card:ℝ))^10*Mass := by
  classical
  intro κ Ratio L
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
      hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hsource⟩ :=
    eventually_positive_difference_actual_family_source_sieve hσsrc hcsrc hUsrc hE hσ hεloss
  refine ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro Jref θ hJref hθ hθmax hθaction
  filter_upwards [hsource hJref hθ hθmax hθaction] with T hfamily
  intro S Fsrc z rat v Nlen Q K₀ N instK Vscale R Jsep Z
    η Tsrc M δ Bcut Bselect Uref Refs Gaps A W gap anchor e r vRef s
    hη hηsmall hTsrc hT hM hδ hsourceScale hQ
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN
    hJsep hJM hNM hmesh hgeometry hseparation Fmodel hmodel f hlevel hminor hcomplete
    hregime hR hRM hscale hA hW xlocal hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight Cphys c J B hsmall hNR hRN hNcube hminscale
    H hNtwo hL hU ε hanchor hcut hcount
    lambda Uband u w chart narrow qell V offset color ChartCap NarrowCap Cap
    q μ b tau dual x μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge hvchoice hUlo Y dualValue Scale Mass

  obtain ⟨hcard,hweighted⟩ := hfamily S Fsrc z rat v Nlen Q K₀ N Vscale R Jsep Z
    (η:=η) (Tsrc:=Tsrc) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
    Uref Refs Gaps A W gap anchor e r vRef s
    hη hηsmall hTsrc hT hM hδ hsourceScale hQ
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hN
    hJsep hJM hNM hmesh hgeometry hseparation hmodel hlevel hminor hcomplete
    hregime hR hRM hscale hA hW hx hgapMem
    hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
    hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
    hselectedUpper hscaleTen hfamilyGap hgap hQN hNsqM hUR
    hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hvchoice hUlo
  have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hμ₀ : 0 < μ₀ := by dsimp only [μ₀]; positivity
  have hVcard : (V.card:ℝ)=2*(S.card:ℝ) := by
    simp only [V,Finset.card_product,Finset.card_univ,Fintype.card_fin,Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  have hμbounds i (hi : i∈S) : μ₀ ≤ μ i := by
    have hb := positive_difference_rounded_cubic_scales Fsrc (T:=Tsrc) (N:=M^3/Tsrc) (R:=1)
      hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) (hy i hi) hreg hjets hnegative hMtwo
      (by positivity) (by norm_num) (hz i hi) (by field_simp)
    have hlo : csrc/(12*σsrc*(M^3/Tsrc)*(1:ℝ)^2)=μ₀ := by
      dsimp only [μ₀]
      field_simp
    rw [hlo] at hb
    exact hb.1
  have hWeightScale :
      4/((Q:ℝ)*(μ₀*(N:ℝ)))=(48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)) := by
    dsimp only [μ₀]
    rw [←hscale]
    field_simp
    ring
  refine ⟨hcard,?_⟩
  intro k
  have hplain : (∑ ip∈V, ‖dualValue k ip‖)^12 ≤
      Scale*(2*(S.card:ℝ))^10*Mass := by
    have hh := actual_color_tenth_weight_absorption V color
      (pow_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) 12) (hweighted k)
    change (∑ ip∈V, ‖dualValue k ip‖)^12 ≤ Scale*(V.card:ℝ)^10*Mass at hh
    rwa [hVcard] at hh
  refine ⟨hplain,?_⟩
  have hc := cubic_completion_weighted_twelfth V
    (fun ip => (q ip.1:ℝ)) (fun ip => μ ip.1) (fun ip => (Nlen ip.1:ℝ)) (dualValue k)
    (Nat.cast_pos.mpr hQ) hμ₀ hNpos
    (fun ip hip => by
      change (Q:ℝ) ≤ 2*((rat ip.1).den:ℝ)
      exact_mod_cast (hden ip.1 (Finset.mem_product.mp hip).1).2)
    (fun ip hip => hμbounds ip.1 (Finset.mem_product.mp hip).1)
    (fun ip hip => by
      change (N:ℝ) ≤ (Nlen ip.1:ℝ)
      exact_mod_cast (hgeometry ip.1 (Finset.mem_product.mp hip).1).1)
  rw [hWeightScale] at hc
  calc
    _ ≤ ((48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)))^6*
        (∑ ip∈V, ‖dualValue k ip‖)^12 := hc
    _ ≤ ((48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)))^6*
        (Scale*(2*(S.card:ℝ))^10*Mass) :=
      mul_le_mul_of_nonneg_left hplain (by positivity)
    _ = _ := by ac_rfl


example
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) :
    (∑ key∈V.image color, ((V.filter (fun i => color i=key)).card:ℝ)^10) ≤
      (V.card:ℝ)^10 :=
  HuxleyBoundaryCoverScratch.actual_color_tenth_weight_bound (α:=α) (β:=β) V color

example
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) {X C B : ℝ}
    (hX : 0 ≤ X)
    (hbound : X ≤ C*(∑ key∈V.image color,
      ((V.filter (fun i => color i=key)).card:ℝ)^10*B)) :
    X ≤ C*(V.card:ℝ)^10*B :=
  HuxleyBoundaryCoverScratch.actual_color_tenth_weight_absorption (α:=α) (β:=β) V color (X:=X) (C:=C) (B:=B) hX hbound

example
    {Q q μ₀ μ N A : ℝ}
    (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : Q ≤ 2*q) (hμ : μ₀ ≤ μ) (hNA : N ≤ A) :
    Real.sqrt (2*q)/(q*Real.sqrt (μ*A)) ≤ Real.sqrt (4/(Q*(μ₀*N))) :=
  HuxleyBoundaryCoverScratch.cubic_completion_weight_bound (Q:=Q) (q:=q) (μ₀:=μ₀) (μ:=μ) (N:=N) (A:=A) hQ hμ₀ hN hQq hμ hNA

example
    {ι : Type*} (S : Finset ι) (q μ A : ι → ℝ) (z : ι → ℂ)
    {Q μ₀ N : ℝ} (hQ : 0 < Q) (hμ₀ : 0 < μ₀) (hN : 0 < N)
    (hQq : ∀ i∈S, Q ≤ 2*q i) (hμ : ∀ i∈S, μ₀ ≤ μ i)
    (hNA : ∀ i∈S, N ≤ A i) :
    (∑ i∈S, (Real.sqrt (2*q i)/(q i*Real.sqrt (μ i*A i)))*‖z i‖)^12 ≤
      (4/(Q*(μ₀*N)))^6*(∑ i∈S,‖z i‖)^12 :=
  HuxleyBoundaryCoverScratch.cubic_completion_weighted_twelfth (ι:=ι) S q μ A z (Q:=Q) (μ₀:=μ₀) (N:=N) hQ hμ₀ hN hQq hμ hNA

example
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    let Ktri := if isUpper then Kupper else Klower
    let Y := S.image Prod.fst
    let dualValue := fun (k : ZMod K₀) (ip : (ℝ × ℤ) × Fin 2) =>
      ∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)
    let Scale := C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11
    let Mass := Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*Vscale*Ktri*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖dualValue k ip‖)^12 ≤ Scale*(2*(S.card:ℝ))^10*Mass ∧
      (∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/
        ((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*‖dualValue k ip‖)^12 ≤
        ((48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)))^6*
          Scale*(2*(S.card:ℝ))^10*Mass :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_triangular_selected_family_weighted_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hE hσ hεloss

example
    {σsrc csrc Usrc E σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hεloss : 0 < εloss) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    ∃ η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {Jref θ : ℝ}, 0 ≤ Jref → 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (S : Finset (ℝ × ℤ)) (Fsrc : ℝ → ℝ)
    (z : (ℝ × ℤ) → ℝ) (rat : (ℝ × ℤ) → ℚ) (v : (ℝ × ℤ) → ℤ) (Nlen : (ℝ × ℤ) → ℕ)
    (Q K₀ N : ℕ) [NeZero K₀] (Vscale R Jsep : ℝ) (Z : ℝ → ℤ)
    {η Tsrc M δ Bcut Bselect : ℝ}
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ))
    (A : ℝ → ℤ) (W : ℝ → ℝ) (gap : (ℝ × ℤ) → ℝ × ℝ)
    (anchor : (ℝ × ℤ) → ℚ) (e r vRef s : ℝ × ℝ → ℤ),
    (0 < η) →
    (η ≤ η₀) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (∀ i∈S, i.1∈Icc (1:ℝ) 2) →
    (∀ i∈S, z i∈Icc M (2*M)) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) →
    (∀ i∈S, ((rat i).den:ℤ) ∣ (rat i).num*v i-1) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (2 ≤ M) →
    (1 ≤ Vscale) →
    (0 < N) →
    (0 < Jsep) → (Jsep ≤ M) → ((N:ℝ) ≤ M) →
    ((Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2) →
    (∀ i∈S, N ≤ Nlen i ∧ Nlen i ≤ 3*N ∧
      round (z i)+(Nlen i:ℤ)=Z i.1+(N:ℤ)*i.2+2*(N:ℤ)) →
    (∀ i∈S, ∀ j∈S, i.1≠j.1 → 1 ≤ Jsep*|i.1-j.1|) →
    let Fmodel := fun (i : ℝ × ℤ) u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*i.1))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 4 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (i.1)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (i.1)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (i.1)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →

    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    (1 ≤ R) → (R ≤ M) → (T*(N:ℝ)*R^2=M^3) →
    (∀ i∈S, M ≤ A i.1) → (∀ i∈S, A i.1+W i.1 ≤ 2*M) →
    let xlocal := fun i : ℝ × ℤ => z i-(A i.1:ℝ)
    (∀ i∈S, xlocal i∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, gap i∈Gaps) →
    (∀ ab∈Gaps, (vRef ab)*(r ab)-(e ab)*(s ab)=1) →
    (∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2)) →
    (0 < Bcut) → (∀ ab∈Gaps, (s ab) ≠ 0) →
    (∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs) →
    (∀ ab∈Gaps, ((vRef ab):ℝ)/(s ab)∈Refs) →
    (∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|) →
    (∀ i∈S, xlocal i-(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+(56*(Uref:ℝ)/κ)*(N:ℝ)∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (1 ≤ Uref) →
    (2+168/κ ≤ Bselect) → (7*Bcut ≤ κ*Bselect) →
    (Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2) →
    (∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ)) →
    (∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2)) →
    (R ≤ (Q:ℝ)) →
    ((Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect) →
    ((N:ℝ)^10 ≤ M^3*R^7) →
    (∀ i∈S, (rat i:ℝ)∈Icc (gap i).1 (gap i).2) →
    (∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) →
    (Q:ℝ) ≤ (N:ℝ) → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    (∀ ab∈Gaps, |((r ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((s ab):ℝ)| ≤ 4*R^2/(Uref:ℝ)) →
    (∀ ab∈Gaps, |((e ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    (∀ ab∈Gaps, |((vRef ab):ℝ)| ≤
      (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ))) →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let H := (N:ℝ)/(Cphys+2)
    2 ≤ (N:ℝ) →
    (∀ i∈S, xlocal i-H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    (∀ i∈S, xlocal i+H∈Ioo (1/2:ℝ) (W i.1-1/2)) →
    let ε := κ/(16*(Cphys+2)*R^2)
    (∀ i∈S, |(anchor i:ℝ)-(rat i:ℝ)| ≤ ε) →
    (∀ i∈S, 256*((anchor i).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ i∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor i).den) →
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun (i : ℝ × ℤ) => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun (i : ℝ × ℤ) => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun (i : ℝ × ℤ) => (⌊i.1/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun (i : ℝ × ℤ) =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun (i : ℝ × ℤ) => ((rat i).den:ℝ)*deriv (f (i.1)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : (ℝ × ℤ) × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : (ℝ × ℤ) × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun (i : ℝ × ℤ) => (rat i).den
    let μ := fun (i : ℝ × ℤ) => iteratedDeriv 3 (f (i.1)) (round (z i))/6
    let b := fun ip : (ℝ × ℤ) × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : (ℝ × ℤ) × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun (i : ℝ × ℤ) => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![-(v ip.1:ℝ)*b ip/q ip.1,-(v ip.1:ℝ)/q ip.1,
        dual ip.1,3*dual ip.1*tau ip/2] : Fin 4 → ℝ)
    let μ₀ := csrc*Tsrc/(12*σsrc*M^3)
    let U₀ := Usrc*Tsrc/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*E^2/Lunit^2+Dupper*(B+1)*E^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    Vscale=(Uref:ℝ)^((3:ℝ)/2) →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    let Y := S.image Prod.fst
    let dualValue := fun (k : ZMod K₀) (ip : (ℝ × ℤ) × Fin 2) =>
      ∑ j : ZMod K₀, ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x ip d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)
    let Scale := C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11
    let Mass := Vscale*Dtype*(Y.card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
      (Y.card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss
    ((V.image color).card:ℝ) ≤ Cap ∧
    ∀ k : ZMod K₀,
      (∑ ip∈V, ‖dualValue k ip‖)^12 ≤ Scale*(2*(S.card:ℝ))^10*Mass ∧
      (∑ ip∈V, (Real.sqrt (2*(q ip.1:ℝ))/
        ((q ip.1:ℝ)*Real.sqrt (μ ip.1*(Nlen ip.1:ℝ))))*‖dualValue k ip‖)^12 ≤
        ((48*σsrc/csrc)*(T/Tsrc)*(R^2/(Q:ℝ)))^6*
          Scale*(2*(S.card:ℝ))^10*Mass :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_selected_family_weighted_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hE hσ hεloss


#print axioms actual_color_tenth_weight_bound
#print axioms actual_color_tenth_weight_absorption
#print axioms cubic_completion_weight_bound
#print axioms cubic_completion_weighted_twelfth
#print axioms eventually_positive_difference_triangular_selected_family_weighted_sieve
#print axioms eventually_positive_difference_selected_family_weighted_sieve

private theorem actual_source_dyadic_cubic_admissibility
    (F : ℝ → ℝ) {σ c J η y z T M R : ℝ} {N Q A K₀ : ℕ} {a r : ℚ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 1 ≤ N) (hR : 0 < R) (hz : z ∈ Icc M (2*M))
    (hphase : T*(N:ℝ)*R^2 = M^3)
    (hQN : Q ≤ N) (hden : r.den ≤ Q) (hhalf : Q ≤ 2*r.den)
    (hcut : 2*a.den ≤ Q) (hmajor : 128*σ*R^2 ≤ c*(Q:ℝ)*a.den)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hmesh : 63*(J/(2*σ*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let μ := iteratedDeriv 3 f (round z)/6
    1 ≤ A ∧ r.den ≤ A ∧ 1 ≤ μ*(r.den:ℝ)^2*A ∧
      7*(μ*(r.den:ℝ)*(A:ℝ)^2) ≤ K₀ := by
  intro f μ
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hμ := positive_difference_rounded_cubic_scales F hσ hc hJ hη hηmax hy
    hf hbound hnegative hM hNp hR hz hphase
  let lambda := c/(12*σ*(N:ℝ)*R^2)
  let U₃ := J/(2*σ*(N:ℝ)*R^2)
  have hμbounds : lambda ≤ μ ∧ μ ≤ U₃ := hμ
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hU₃ : 0 < U₃ := by dsimp only [U₃]; positivity
  have hcutR : 2*(a.den:ℝ) ≤ Q := by exact_mod_cast hcut
  have hqR : (Q:ℝ) ≤ 2*(r.den:ℝ) := by exact_mod_cast hhalf
  have haq : (a.den:ℝ) ≤ r.den := by linarith only [hcutR,hqR]
  have hprod : c*(Q:ℝ)*a.den ≤ 2*c*(r.den:ℝ)^2 := by
    calc
      _ ≤ c*(2*(r.den:ℝ))*(r.den:ℝ) := by gcongr
      _ = _ := by ring
  have hbudget : 12*σ*R^2 ≤ c*(r.den:ℝ)^2 := by
    have hpositive : 0 < σ*R^2 := by positivity
    nlinarith only [hmajor,hprod,hpositive]
  have hbase : 1 ≤ lambda*(r.den:ℝ)^2*N := by
    have heq : lambda*(r.den:ℝ)^2*N = c*(r.den:ℝ)^2/(12*σ*R^2) := by
      dsimp only [lambda]
      field_simp
    rw [heq]
    exact (one_le_div (by positivity : 0 < 12*σ*R^2)).mpr hbudget
  have hAlowR : (N:ℝ) ≤ A := by exact_mod_cast hAlow
  have hAhighR : (A:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hAhigh
  have hdenR : (r.den:ℝ) ≤ Q := by exact_mod_cast hden
  have hμnonneg : 0 ≤ μ := hlambda.le.trans hμbounds.1
  refine ⟨hN.trans hAlow,hden.trans (hQN.trans hAlow),hbase.trans ?_,?_⟩
  · exact mul_le_mul (mul_le_mul_of_nonneg_right hμbounds.1 (sq_nonneg _))
      hAlowR hNp.le (mul_nonneg hμnonneg (sq_nonneg _))
  · calc
      7*(μ*(r.den:ℝ)*(A:ℝ)^2) ≤ 7*(U₃*(Q:ℝ)*(3*(N:ℝ))^2) := by
        gcongr
        exact hμbounds.2
      _ = 63*U₃*(Q:ℝ)*(N:ℝ)^2 := by ring
      _ ≤ K₀ := hmesh

private theorem cubic_completion_point_error
    {σ c N R A μ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hN : 1 ≤ N) (hR : 0 < R)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hμ : c/(12*σ*N*R^2) ≤ μ) :
    Real.sqrt A*Real.log (2*A)+1/(μ*A^2) ≤
      Real.sqrt (3*N)*Real.log (6*N)+12*σ*R^2/(c*N) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hAp : 0 < A := hNp.trans_le hAlow
  have hμp : 0 < μ := (div_pos hc (by positivity)).trans_le hμ
  have hlog : Real.sqrt A*Real.log (2*A) ≤ Real.sqrt (3*N)*Real.log (6*N) := by
    apply mul_le_mul (Real.sqrt_le_sqrt hAhigh)
      (Real.log_le_log (by positivity) (by linarith only [hAhigh]))
      (Real.log_nonneg (by linarith only [hAlow,hN])) (Real.sqrt_nonneg _)
  have hden : c*N/(12*σ*R^2) ≤ μ*A^2 := by
    calc
      _ = (c/(12*σ*N*R^2))*N^2 := by field_simp
      _ ≤ _ := mul_le_mul hμ (pow_le_pow_left₀ hNp.le hAlow 2) (sq_nonneg _) hμp.le
  have hrecip := one_div_le_one_div_of_le (show 0 < c*N/(12*σ*R^2) by positivity) hden
  have he : 1/(c*N/(12*σ*R^2)) = 12*σ*R^2/(c*N) := by field_simp
  rw [he] at hrecip
  exact add_le_add hlog hrecip

private theorem actual_source_grid_completion_error
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (z : ℝ × ℤ → ℝ) (A : ℝ × ℤ → ℕ)
    {σ c J η T M R s : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hN : 1 ≤ N) (hM : 2 ≤ M) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2 = M^3)
    (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2)
    (hlabels : ∀ i ∈ S, i.1 ∈ Y)
    (hgrid : ∀ i ∈ S, M ≤ s+(N:ℝ)*i.2 ∧ s+(N:ℝ)*i.2 ≤ 2*M)
    (hz : ∀ i ∈ S, z i ∈ Icc M (2*M))
    (hA : ∀ i ∈ S, N ≤ A i ∧ A i ≤ 3*N)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    let f := fun i w => T*(F (w/M)-F (w/M+η*i.1))/(σ*η)
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    (S.card:ℝ) ≤ (Y.card:ℝ)*(M/(N:ℝ)+1) ∧
    (∑ i ∈ S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ≤
      (Y.card:ℝ)*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σ*R^2/(c*(N:ℝ))) := by
  classical
  intro f μ
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNreal : (1:ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨I,hI,_hIlow,hIhigh⟩ := physical_grid_interval_card (N:=(N:ℝ)) (Z:=s)
    (x:=M) (z:=2*M) hNp (by linarith only [hM])
  have hsub : S⊆Y ×ˢ I := by
    intro i hi
    refine Finset.mem_product.mpr ⟨hlabels i hi,(hI i.2).mpr ?_⟩
    simpa only [mul_comm (i.2:ℝ) (N:ℝ)] using hgrid i hi
  have hcardRaw : (S.card:ℝ) ≤ (Y.card:ℝ)*(I.card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product Y I)
  have hcard : (S.card:ℝ) ≤ (Y.card:ℝ)*(M/(N:ℝ)+1) := by
    have hIbound : (I.card:ℝ) ≤ M/(N:ℝ)+1 := by
      convert hIhigh using 1
      ring
    exact hcardRaw.trans (mul_le_mul_of_nonneg_left hIbound (Nat.cast_nonneg _))
  refine ⟨hcard,?_⟩
  let ErrorBound := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σ*R^2/(c*(N:ℝ))
  have hError : 0 ≤ ErrorBound := add_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith only [hNreal])))
    (by positivity)
  have hpoint i (hi : i ∈ S) :
      Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2) ≤ ErrorBound := by
    have hcubic := positive_difference_rounded_cubic_scales F hσ hc hJ hη hηmax
      (hy i.1 (hlabels i hi)) hf hbound hnegative hM hNp hR (hz i hi) hphase
    exact cubic_completion_point_error hσ hc hNreal hR
      (by exact_mod_cast (hA i hi).1) (by exact_mod_cast (hA i hi).2) hcubic.1
  calc
    _ ≤ ∑ _i ∈ S,ErrorBound := Finset.sum_le_sum hpoint
    _ = (S.card:ℝ)*ErrorBound := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hError


private theorem eventually_positive_difference_selected_reference_core_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    3*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∃ Refs : Finset ℝ,
      (∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → (Uref:ℝ)/(4*R^2) ≤ |a-b|) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
        b-a ≤ 7*(Uref:ℝ)/(2*R^2)) ∧
      (∀ y ∈ Y, ∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h y M ∧ h y (2*M) ≤ u) ∧
      (∀ y ∈ Y, ∀ q ∈ Refs, q ∈ Icc (h y M) (h y (2*M)) →
        ∃ z ∈ Icc M (2*M), h y z = q) ∧
      ∀ (sgrid : ℤ) (Hlen : ℝ → ℤ → ℕ), (∀ y ∈ Y, ∀ k, Hlen y k ≤ N) →
      let Lgrid := fun k : ℤ => sgrid+(N:ℤ)*k+2*(N:ℤ)
      let Good : ℝ × ℤ → Prop := fun p =>
        ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
            h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
              (sgrid:ℝ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4
      ∀ (Pcore : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → ℚ) (za : (ℝ × ℤ) → ℝ),
      (∀ p ∈ Pcore, p.1 ∈ Y ∧ Good p) →
      (∀ p ∈ Pcore, |za p-((sgrid:ℝ)+(N:ℝ)*p.2)| ≤ (N:ℝ)/16 ∧
        h p.1 (za p)=(anchor p:ℝ)) →
      (∀ p ∈ Pcore, 768*(anchor p).den ≤ Q) →
      (∀ p ∈ Pcore, (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p).den) →
      (∑ p ∈ Pcore, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
        (𝐞 (f p.1 n):ℂ)‖)^12 ≤
        2^11*((Csrc*Error)^12+
          (Csrc*(1+Real.log K₀))^12*FamilyBound Pcore) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,hCsrc,hsource⟩ :=
    positive_difference_dyadic_anchor_source_fourier hσsrc hcsrc hUsrc
  obtain ⟨_Cref,_hCref,hRefConstructor⟩ :=
    positive_difference_constructed_reference_family_uniform_grid_fourier hσsrc hcsrc hUsrc
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
      hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hphysical⟩ :=
    eventually_positive_difference_selected_family_weighted_sieve
      hσsrc hcsrc hUsrc (by norm_num : (0:ℝ) < 1) hσ hεloss
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  let Jref := σ*Usrc/σsrc
  have hJref : 0 ≤ Jref := by dsimp only [Jref]; positivity
  have hθaction' :
      θ ≤ 1/(8*((max (8*(18*Usrc^2*1/(σsrc*csrc*κ))^2)
        (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*1/κ^2))+3)) := by
    simpa only [mul_one] using hθaction
  filter_upwards [hphysical hJref hθ hθmax hθaction'] with T hfamily
  intro Fsrc Y Q K₀ N Uref instK R Jsep η M δ Bcut Bselect
    hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
    hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
    hselectedUpper hUlo hscaleTen hQN hNsqM hUR hstrongRQ hNRM
    Cphys c J B hsmall hNR hRN hNcube hminscale
    Vscale lambda Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge Buffer Error FamilyBound f h
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hN : 0 < N := by omega
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hMtwo : 2 ≤ M := by nlinarith only [hNreal,hNsqM]
  have hM : 0 < M := by linarith only [hMtwo]
  have hNM : (N:ℝ) ≤ M := by nlinarith only [hNreal,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hQbig : 768 ≤ Q := by
    have hh : (768:ℝ) ≤ Q := by linarith only [hR,hstrongRQ]
    exact_mod_cast hh
  have hQ : 0 < Q := by omega
  have hQtwo : 2 ≤ Q := by omega
  have hRQ : R ≤ (Q:ℝ) := by nlinarith only [hR,hstrongRQ]
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hVscale : 1 ≤ Vscale :=
    Real.one_le_rpow (by exact_mod_cast hUref) (by norm_num)
  have hsourceData := hRefConstructor Fsrc Y N η T M R (Uref:ℝ)
    (by omega) hη (hηsmall.trans hηcap) hy hT hM hRp hUp hUR
    hreg hjets htests hnegative hscale hpad hquartic hquad hUlarge
  obtain ⟨Href,hHref,hHrefHeight,Refs,hseed,hhull,henclose,hpoints,hheights,
    hcurv,hlabels,hRefSep,hcover,hroots,hgaps,hcharts,_hrest⟩ := hsourceData
  have hencloseCurv y (hyY : y ∈ Y) : ∃ l ∈ Refs, ∃ u ∈ Refs,
      l ≤ h y M ∧ h y (2*M) ≤ u := by
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
    have hleft := abs_le.mp (hcurv y (hy y hyY) M ⟨le_rfl,by linarith only [hM]⟩)
    have hright := abs_le.mp (hcurv y (hy y hyY) (2*M) ⟨by linarith only [hM],le_rfl⟩)
    exact ⟨l,hl,u,hu,hlo.trans hleft.1,hright.2.trans hhi⟩
  refine ⟨Refs,(fun a ha b hb hab => (hRefSep a ha b hb hab).le),
    (fun a ha b hb hab hadj => (hgaps a ha b hb hab hadj).2.1),
    hencloseCurv,(fun y hyY => hroots y (hy y hyY)),?_⟩

  intro sgrid Hlen hHlen Lgrid CoreGood P anchor za hCoreData hAnchors hCuts hCounts
  have hlabelsP p (hp : p∈P) : p.1∈Y := (hCoreData p hp).1
  have hchoose (p : ℝ × ℤ) : ∃ (ab : ℝ × ℝ) (zl zu : ℝ), p∈P →
      ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      (∀ t∈Refs,¬(ab.1 < t ∧ t < ab.2)) ∧
      zl∈Icc M (2*M) ∧ zu∈Icc M (2*M) ∧ h p.1 zl=ab.1 ∧ h p.1 zu=ab.2 ∧
      M+Buffer ≤ zl ∧ zu ≤ 2*M-Buffer ∧
      zl+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
      (sgrid:ℝ)+(N:ℝ)*p.2 ≤ zu-(N:ℝ)/4 := by
    by_cases hp : p∈P
    · obtain ⟨a,ha,b,hb,hab,hadj,zl,zu,hzl,hzu,hza,hzb,hleft,hright,htleft,htright⟩ :=
        (hCoreData p hp).2
      exact ⟨(a,b),zl,zu,fun _ =>
        ⟨ha,hb,hab,hadj,hzl,hzu,hza,hzb,hleft,hright,htleft,htright⟩⟩
    · exact ⟨(0,0),0,0,fun hh => (hp hh).elim⟩
  choose gap zl zu hchosen using hchoose
  have hbracket p (hp : p∈P) :
      zl p∈Icc M (2*M) ∧ zu p∈Icc M (2*M) ∧
      h p.1 (zl p)=(gap p).1 ∧ h p.1 (zu p)=(gap p).2 ∧
      M+Buffer ≤ zl p ∧ zu p ≤ 2*M-Buffer ∧
      zl p+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
      (sgrid:ℝ)+(N:ℝ)*p.2 ≤ zu p-(N:ℝ)/4 := (hchosen p hp).2.2.2.2
  have hgridP p (hp : p∈P) :
      M ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧ (sgrid:ℝ)+(N:ℝ)*p.2 ≤ 2*M := by
    have hb := hbracket p hp
    exact ⟨by linarith only [hb.1.1,hb.2.2.2.2.2.2.1,hNp],
      by linarith only [hb.2.1.2,hb.2.2.2.2.2.2.2,hNp]⟩
  have hLgrid (p : ℝ × ℤ) : (Lgrid p.2:ℝ)-2*(N:ℝ)=(sgrid:ℝ)+(N:ℝ)*p.2 := by
    dsimp only [Lgrid]
    push_cast
    ring
  have hsourceCut p (hp : p∈P) : 2*(anchor p).den ≤ Q :=
    (Nat.mul_le_mul_right _ (show 2 ≤ 768 by decide)).trans (hCuts p hp)
  have hsourceCount p (hp : p∈P) : 128*σsrc*R^2 ≤ csrc*(Q:ℝ)*(anchor p).den := by
    exact (mul_le_mul_of_nonneg_right
      (by linarith only [hσsrc] : 128*σsrc ≤ 24576*σsrc) (sq_nonneg R)).trans (hCounts p hp)
  obtain ⟨rat,z,hrat,hround,hfourier⟩ :=
    hsource (ℝ × ℤ) P Fsrc Prod.fst (fun p => Lgrid p.2) (fun p => Hlen p.1 p.2)
      anchor za N Q η T M R (by omega)
      (fun p hp => hHlen p.1 (hlabelsP p hp) p.2)
      hη (hηsmall.trans hηcap) hT hM hRp
      (fun p hp => hy p.1 (hlabelsP p hp))
      (fun p hp => by rw [hLgrid p]; exact hgridP p hp)
      hreg hjets hnegative hscale hpad hquartic hquad hQN hsourceCut hsourceCount
      (fun p hp => by
        rw [hLgrid p]
        have ha := abs_le.mp (hAnchors p hp).1
        exact ⟨⟨by linarith only [ha.1,hNp],by linarith only [ha.2,hNp]⟩,
          (hAnchors p hp).2⟩)
  let Nlen := fun p => (Lgrid p.2-round (z p)).toNat
  obtain ⟨v,hinv,k0,hsourceBound⟩ := hfourier K₀ hsourceMesh
  have hden p (hp : p∈P) : (rat p).den ≤ Q ∧ Q ≤ 2*(rat p).den :=
    ⟨(hrat p hp).1,(hrat p hp).2.1⟩
  have hlevel p (hp : p∈P) : iteratedDeriv 2 (f p.1) (z p)/2=(rat p:ℝ) :=
    (hrat p hp).2.2.2.2.2
  have hgeomP p (hp : p∈P) :
      N ≤ Nlen p ∧ Nlen p ≤ 3*N ∧
      round (z p)+(Nlen p:ℤ)=sgrid+(N:ℤ)*p.2+2*(N:ℤ) :=
    ⟨(hround p hp).2.1,(hround p hp).2.2.1,(hround p hp).2.2.2⟩
  have hclose p (hp : p∈P) :
      |z p-((sgrid:ℝ)+(N:ℝ)*p.2)| ≤ (N:ℝ)/8 := by
    have hz := (hrat p hp).2.2.2.2.1
    have ha := abs_le.mp (hAnchors p hp).1
    exact abs_le.mpr ⟨by linarith only [hz.1,ha.1,hNp],
      by linarith only [hz.2,ha.2]⟩
  have hzin p (hp : p∈P) : zl p < z p ∧ z p < zu p := by
    have hb := hbracket p hp
    have hz := abs_le.mp (hclose p hp)
    exact ⟨by linarith only [hb.2.2.2.2.2.2.1,hz.1,hNp],
      by linarith only [hb.2.2.2.2.2.2.2,hz.2,hNp]⟩
  have hbuffer p (hp : p∈P) : M+Buffer ≤ z p ∧ z p ≤ 2*M-Buffer := by
    have hb := hbracket p hp
    exact ⟨hb.2.2.2.2.1.trans (hzin p hp).1.le,
      (hzin p hp).2.le.trans hb.2.2.2.2.2.1⟩
  have hz p (hp : p∈P) : z p∈Icc M (2*M) := by
    have hh := hbuffer p hp
    exact ⟨by linarith only [hh.1,hBuffer],by linarith only [hh.2,hBuffer]⟩
  have hminor p (hp : p∈P) :
      1 ≤ Nlen p ∧ (rat p).den ≤ Nlen p ∧
        1 ≤ (iteratedDeriv 3 (f p.1) (round (z p))/6)*((rat p).den:ℝ)^2*Nlen p ∧
      7*((iteratedDeriv 3 (f p.1) (round (z p))/6)*
        ((rat p).den:ℝ)*(Nlen p:ℝ)^2) ≤ K₀ :=
    actual_source_dyadic_cubic_admissibility Fsrc
      hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) (hy p.1 (hlabelsP p hp))
      hreg hjets hnegative hMtwo (by omega) hRp (hz p hp) hscale hQN
      (hden p hp).1 (hden p hp).2 (hsourceCut p hp) (hsourceCount p hp)
      (hgeomP p hp).1 (hgeomP p hp).2.1 hsourceMesh
  let Gaps := (Refs ×ˢ Refs).filter (fun ab =>
    ab.1 < ab.2 ∧ ∀ t ∈ Refs,¬(ab.1 < t ∧ t < ab.2))
  have hgapData ab (hab : ab ∈ Gaps) :
      ab.1 ∈ Refs ∧ ab.2 ∈ Refs ∧ ab.1 < ab.2 ∧ ∀ t ∈ Refs,¬(ab.1 < t ∧ t < ab.2) := by
    have hh := Finset.mem_filter.mp hab
    exact ⟨(Finset.mem_product.mp hh.1).1,(Finset.mem_product.mp hh.1).2,hh.2⟩
  have hgapMem p (hp : p∈P) : gap p∈Gaps := by
    have hh := hchosen p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hh.1,hh.2.1⟩,hh.2.2.1,hh.2.2.2.1⟩
  have hchartChoice (ab : ℝ × ℝ) : ∃ e r v s : ℤ, ab ∈ Gaps →
      v*r-e*s = 1 ∧ ((0 < r ∧ (e:ℝ)/r = ab.1) ∨ (r < 0 ∧ (e:ℝ)/r = ab.2)) ∧
      s ≠ 0 ∧ (e:ℝ)/r ∈ Refs ∧ (v:ℝ)/s ∈ Refs ∧ R^2 ≤ (r:ℝ)^2*(Uref:ℝ) ∧
      |(r:ℝ)| < 4*R^2/(Uref:ℝ) ∧ |(s:ℝ)| < 4*R^2/(Uref:ℝ) ∧
      |(e:ℝ)| ≤ (3*Usrc*T/(2*σsrc*M^2)+1)*(4*R^2/(Uref:ℝ)) ∧
      |(v:ℝ)| ≤ (3*Usrc*T/(2*σsrc*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    by_cases hab : ab ∈ Gaps
    · have hh := hgapData ab hab
      obtain ⟨e,r,v,s,he⟩ := hcharts ab.1 hh.1 ab.2 hh.2.1 hh.2.2.1 hh.2.2.2
      exact ⟨e,r,v,s,fun _ => he⟩
    · exact ⟨0,0,0,0,fun hh => (hab hh).elim⟩
  choose e rRef vRef sRef hchartData using hchartChoice
  have hchart ab (hab : ab ∈ Gaps) : vRef ab*rRef ab-e ab*sRef ab = 1 :=
    (hchartData ab hab).1
  have horientation ab (hab : ab ∈ Gaps) :
      ((0:ℝ) < rRef ab ∧ (e ab:ℝ)/rRef ab = ab.1) ∨
        ((rRef ab:ℝ) < 0 ∧ (e ab:ℝ)/rRef ab = ab.2) := by
    rcases (hchartData ab hab).2.1 with hh | hh
    · exact Or.inl ⟨by exact_mod_cast hh.1,hh.2⟩
    · exact Or.inr ⟨by exact_mod_cast hh.1,hh.2⟩
  have hs ab (hab : ab ∈ Gaps) : sRef ab ≠ 0 := (hchartData ab hab).2.2.1
  have hrefSet ab (hab : ab ∈ Gaps) : (e ab:ℝ)/rRef ab ∈ Refs :=
    (hchartData ab hab).2.2.2.1
  have hparentSet ab (hab : ab ∈ Gaps) : (vRef ab:ℝ)/sRef ab ∈ Refs :=
    (hchartData ab hab).2.2.2.2.1
  have hreferenceDen ab (hab : ab ∈ Gaps) : R^2 ≤ (rRef ab:ℝ)^2*(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.1
  have hrHeight ab (hab : ab ∈ Gaps) : |(rRef ab:ℝ)| ≤ 4*R^2/(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.2.1.le
  have hsHeight ab (hab : ab ∈ Gaps) : |(sRef ab:ℝ)| ≤ 4*R^2/(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.2.2.1.le
  have hheightEq : 3*Usrc*T/(2*σsrc*M^2) = 3*Jref*T/(2*σ*M^2) := by
    dsimp only [Jref]
    field_simp
  have heHeight ab (hab : ab ∈ Gaps) :
      |(e ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    rw [←hheightEq]
    exact (hchartData ab hab).2.2.2.2.2.2.2.2.1
  have hvHeight ab (hab : ab ∈ Gaps) :
      |(vRef ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    rw [←hheightEq]
    exact (hchartData ab hab).2.2.2.2.2.2.2.2.2
  have hgapWidth ab (hab : ab ∈ Gaps) : ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2) := by
    have hh := hgapData ab hab
    exact (hgaps ab.1 hh.1 ab.2 hh.2.1 hh.2.2.1 hh.2.2.2).2.1
  have hsep u (hu : u ∈ Refs) v (hv : v ∈ Refs) (huv : u ≠ v) :
      ((Uref:ℝ)/R^2)/4 < |u-v| := by
    convert hRefSep u hu v hv huv using 1
    ring
  have hwide w (hw : w ∈ Icc M (2*M)) : w ∈ Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hw.1,hw.2,hM]

  have hfamilyGap p (hp : p∈P) : (rat p:ℝ)∈Icc (gap p).1 (gap p).2 := by
    have hb := hbracket p hp
    have hm := positive_difference_physical_curvature_strictMono Fsrc
      hσsrc hcsrc hη (hηsmall.trans hηcap) (hy p.1 (hlabelsP p hp))
      hreg hnegative hT hM
    have hl := hm (hwide _ hb.1) (hwide _ (hz p hp)) (hzin p hp).1
    have hu := hm (hwide _ (hz p hp)) (hwide _ hb.2.1) (hzin p hp).2
    change h p.1 (zl p) < h p.1 (z p) at hl
    change h p.1 (z p) < h p.1 (zu p) at hu
    have hlp : h p.1 (z p)=(rat p:ℝ) := hlevel p hp
    rw [hb.2.2.1,hlp] at hl
    rw [hb.2.2.2.1,hlp] at hu
    exact ⟨hl.le,hu.le⟩
  let Aphase := fun _y : ℝ => (⌈M⌉:ℤ)
  let Wphase := fun _y : ℝ => 2*M-(⌈M⌉:ℤ)
  let xlocal := fun p : ℝ × ℤ => z p-(Aphase p.1:ℝ)
  let Wide := (56*(Uref:ℝ)/κ)*(N:ℝ)
  let Hshort := (N:ℝ)/(Cphys+2)
  have hWide : 0 ≤ Wide := by dsimp only [Wide]; positivity
  have hHshort : 0 ≤ Hshort := by dsimp only [Hshort]; positivity
  have hlocal p (hp : p∈P) (d : ℝ) (hd : |d|+2 ≤ Buffer) :
      xlocal p+d∈Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hb := hbuffer p hp
    have hdabs := abs_le.mp (show |d| ≤ Buffer-2 by linarith only [hd])
    have hceil := Int.ceil_lt_add_one M
    dsimp only [xlocal,Aphase,Wphase]
    exact ⟨by linarith only [hb.1,hdabs.1,hceil],
      by linarith only [hb.2,hdabs.2]⟩
  have hx p (hp : p ∈ P) : xlocal p ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal p hp 0 (by
      change |(0:ℝ)|+2 ≤ Wide+Hshort+2
      rw [abs_zero]
      linarith only [hWide,hHshort])
    simpa only [add_zero] using hh
  have hwideL p (hp : p ∈ P) : xlocal p-Wide ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal p hp (-Wide) (by
      change |-Wide|+2 ≤ Wide+Hshort+2
      rw [abs_neg,abs_of_nonneg hWide]
      linarith only [hHshort])
    simpa only [sub_eq_add_neg] using hh
  have hwideU p (hp : p ∈ P) : xlocal p+Wide ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) :=
    hlocal p hp Wide (by
      change |Wide|+2 ≤ Wide+Hshort+2
      rw [abs_of_nonneg hWide]
      linarith only [hHshort])
  have hL p (hp : p ∈ P) : xlocal p-Hshort ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal p hp (-Hshort) (by
      change |-Hshort|+2 ≤ Wide+Hshort+2
      rw [abs_neg,abs_of_nonneg hHshort]
      linarith only [hWide])
    simpa only [sub_eq_add_neg] using hh
  have hU p (hp : p ∈ P) : xlocal p+Hshort ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) :=
    hlocal p hp Hshort (by
      change |Hshort|+2 ≤ Wide+Hshort+2
      rw [abs_of_nonneg hHshort]
      linarith only [hWide])
  let ε := κ/(16*(Cphys+2)*R^2)
  have htol : csrc/(64*σsrc*R^2) ≤ ε := by
    have hb : csrc ≤ 4*κ*σsrc/(Cphys+2) := by
      convert hanchorBudget using 1
      dsimp only [Cphys]
      ring
    calc
      csrc/(64*σsrc*R^2) ≤ (4*κ*σsrc/(Cphys+2))/(64*σsrc*R^2) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = ε := by dsimp only [ε]; field_simp; ring
  have hanchor p (hp : p ∈ P) : |(anchor p:ℝ)-(rat p:ℝ)| ≤ ε := by
    rw [abs_sub_comm]
    exact ((hrat p hp).2.2.2.1).trans htol
  have hcut p (hp : p∈P) : 256*((anchor p).den:ℝ) ≤ (Q:ℝ)/3 := by
    have hh : 768*((anchor p).den:ℝ) ≤ Q := by exact_mod_cast hCuts p hp
    linarith only [hh]
  have hcount p (hp : p∈P) : 256 ≤ 2*ε*((Q:ℝ)/3)*(anchor p).den := by
    calc
      (256:ℝ) ≤ csrc*(Q:ℝ)*(anchor p).den/(96*σsrc*R^2) := by
        apply (le_div_iff₀ (by positivity : (0:ℝ) < 96*σsrc*R^2)).mpr
        nlinarith only [hCounts p hp]
      _ = 2*(csrc/(64*σsrc*R^2))*((Q:ℝ)/3)*(anchor p).den := by field_simp; ring
      _ ≤ 2*ε*((Q:ℝ)/3)*(anchor p).den := by gcongr
  have hmodel p (hp : p ∈ P) : Expdb.IsApproximateModelPhaseFunction
      (fun u => (T/T)*(Fsrc u-Fsrc (u+η*p.1))/(σsrc*η)) σ 4 δ := by
    simpa only [div_self hT.ne',one_mul] using hmodels p.1 (hlabelsP p hp)
  have hseparation p (hp : p ∈ P) q (hq : q ∈ P) (hpq : p.1 ≠ q.1) :
      1 ≤ Jsep*|p.1-q.1| := hsepY p.1 (hlabelsP p hp) q.1 (hlabelsP q hq) hpq
  obtain ⟨hcolor,hvalues⟩ :=
    hfamily P Fsrc z rat v Nlen Q K₀ N Vscale R Jsep (fun _ => sgrid)
      (η:=η) (Tsrc:=T) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      Uref Refs Gaps Aphase Wphase gap anchor e rRef vRef sRef
      hη hηsmall hT hT hM hδ (by simp only [one_mul,le_refl]) hQ
      (fun p hp => hy p.1 (hlabelsP p hp)) hz hreg hjets htests hden hinv hnegative
      hMtwo hVscale hN hJsep hJM hNM hmesh hgeomP hseparation hmodel hlevel
      (fun p hp => ⟨(hminor p hp).1,(hminor p hp).2.1,(hminor p hp).2.2.1⟩)
      (fun p hp => (hminor p hp).2.2.2)
      hregime hR hRM hscale (fun _ _ => Int.le_ceil M)
      (fun _ _ => by dsimp only [Aphase,Wphase]; linarith only)
      hx hgapMem hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
      hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen hfamilyGap hgapData (by exact_mod_cast hQN) hNsqM hUR
      hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
      hNreal hL hU hanchor hcut hcount hsize hD hΔ hBsize rfl hUlo

  let q0 := fun p => (rat p).den
  let mu0 := fun p => iteratedDeriv 3 (f p.1) (round (z p))/6
  let ell0 := fun p => deriv (f p.1) (round (z p))
  let b0 := fun p (j : Fin 2) => (⌊(q0 p:ℝ)*ell0 p⌋+(j:ℕ) : ℤ)
  let tau0 := fun p j => ((b0 p j:ℝ)-(q0 p:ℝ)*ell0 p)/2
  let dual0 := fun p => -2*mu0 p*(Real.sqrt (2/(3*mu0 p*(q0 p:ℝ))))^3
  let x0 := fun p j =>
    (![-(v p:ℝ)*b0 p j/q0 p,-(v p:ℝ)/q0 p,
      dual0 p,3*dual0 p*tau0 p j/2] : Fin 4 → ℝ)
  let FourierNorm := fun p j =>
    ‖∑ k : ZMod K₀, ZMod.stdAddChar (-(k*k0))*
      GafniTao.fordAdditiveCharacter (∑ d,x0 p j d*
        (![(k.val+1:ℝ),(k.val+1:ℝ)^2,(k.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (k.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let Wpoint := fun p j => (Real.sqrt (2*(q0 p:ℝ))/
    ((q0 p:ℝ)*Real.sqrt (mu0 p*(Nlen p:ℝ))))*FourierNorm p j
  let Wsum := ∑ p∈P, ∑ j : Fin 2,Wpoint p j
  have hW12 : Wsum^12 ≤ FamilyBound P := by
    have hw := (hvalues k0).2
    convert hw using 1
    · congr 1
      exact (Finset.sum_product P (Finset.univ : Finset (Fin 2))
        (fun pj => Wpoint pj.1 pj.2)).symm
    · simp only [FamilyBound,κ,Cphys,c,J,B,Vscale,lambda,Uband,ChartCap,NarrowCap,Cap,
        μ₀,U₀,Δtype,C₂,C₃,Ct,Cc,Kres,Lunit,Gamma,Cthird,AupperConst,BupperConst,
        AlowerConst,BlowerConst,DupperConst,DlowerConst,CostUpper,CostLower,
        Cpack,Cfirst,Cgap,Cmain,Ctail,Kupper,Klower,Klarge,mul_one,one_pow,
        div_self hT.ne',mul_pow,mul_assoc]
  let RawError := ∑ p∈P,(Real.sqrt (Nlen p)*Real.log (2*(Nlen p:ℝ))+
    1/(mu0 p*(Nlen p:ℝ)^2))
  have hError : RawError ≤ Error :=
    (actual_source_grid_completion_error P Y Fsrc z Nlen
      (s:=(sgrid:ℝ)) hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap)
      (by omega) hMtwo hRp hscale hy hlabelsP hgridP hz
      (fun p hp => ⟨(hgeomP p hp).1,(hgeomP p hp).2.1⟩)
      hreg hjets hnegative).2
  have hKpos : 0 < K₀ := NeZero.pos K₀
  have hlogK : 0 ≤ 1+Real.log K₀ :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hKpos))
  have hWsum : 0 ≤ Wsum := by
    apply Finset.sum_nonneg
    intro p _hp
    apply Finset.sum_nonneg
    intro j _hj
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))) (norm_nonneg _)
  have hCsrcpos : 0 ≤ Csrc := zero_le_one.trans hCsrc
  have hErrorNN : 0 ≤ Error := by
    have hlogN : 0 ≤ Real.log (6*(N:ℝ)) :=
      Real.log_nonneg (by linarith only [hNreal])
    clear * - hM hNp hσsrc hcsrc hRp hlogN
    dsimp only [Error]
    positivity
  let Orig := ∑ p∈P, ‖∑ n∈Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
    (𝐞 (f p.1 n):ℂ)‖
  have hOrig : 0 ≤ Orig := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  change Orig ≤ Csrc*((1+Real.log K₀)*Wsum+RawError) at hsourceBound
  let Aterm := Csrc*Error
  let Bterm := (Csrc*(1+Real.log K₀))*Wsum
  have hAterm : 0 ≤ Aterm := mul_nonneg hCsrcpos hErrorNN
  have hBterm : 0 ≤ Bterm := mul_nonneg (mul_nonneg hCsrcpos hlogK) hWsum
  have hOrigSum : Orig ≤ Aterm+Bterm := by
    calc
      Orig ≤ Csrc*((1+Real.log K₀)*Wsum+Error) :=
        hsourceBound.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hError) hCsrcpos)
      _ = Aterm+Bterm := by dsimp only [Aterm,Bterm]; ring
  have hBpower : Bterm^12 ≤ (Csrc*(1+Real.log K₀))^12*FamilyBound P := by
    dsimp only [Bterm]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hW12 (pow_nonneg (mul_nonneg hCsrcpos hlogK) 12)
  calc
    Orig^12 ≤ (Aterm+Bterm)^12 := pow_le_pow_left₀ hOrig hOrigSum 12
    _ ≤ 2^11*(Aterm^12+Bterm^12) := add_pow_le hAterm hBterm 12
    _ ≤ 2^11*(Aterm^12+(Csrc*(1+Real.log K₀))^12*FamilyBound P) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hBpower) (by positivity)


example
    (F : ℝ → ℝ) {σ c J η y z T M R : ℝ} {N Q A K₀ : ℕ} {a r : ℚ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y ∈ Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 1 ≤ N) (hR : 0 < R) (hz : z ∈ Icc M (2*M))
    (hphase : T*(N:ℝ)*R^2 = M^3)
    (hQN : Q ≤ N) (hden : r.den ≤ Q) (hhalf : Q ≤ 2*r.den)
    (hcut : 2*a.den ≤ Q) (hmajor : 128*σ*R^2 ≤ c*(Q:ℝ)*a.den)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hmesh : 63*(J/(2*σ*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let μ := iteratedDeriv 3 f (round z)/6
    1 ≤ A ∧ r.den ≤ A ∧ 1 ≤ μ*(r.den:ℝ)^2*A ∧
      7*(μ*(r.den:ℝ)*(A:ℝ)^2) ≤ K₀ :=
  HuxleyBoundaryCoverScratch.actual_source_dyadic_cubic_admissibility F (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (z:=z) (T:=T) (M:=M) (R:=R) (N:=N) (Q:=Q) (A:=A) (K₀:=K₀) (a:=a) (r:=r) hσ hc hJ hη hηmax hy hf hbound hnegative hM hN hR hz hphase hQN hden hhalf hcut hmajor hAlow hAhigh hmesh

example
    {σ c N R A μ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hN : 1 ≤ N) (hR : 0 < R)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hμ : c/(12*σ*N*R^2) ≤ μ) :
    Real.sqrt A*Real.log (2*A)+1/(μ*A^2) ≤
      Real.sqrt (3*N)*Real.log (6*N)+12*σ*R^2/(c*N) :=
  HuxleyBoundaryCoverScratch.cubic_completion_point_error (σ:=σ) (c:=c) (N:=N) (R:=R) (A:=A) (μ:=μ) hσ hc hN hR hAlow hAhigh hμ

example
    (S : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (z : ℝ × ℤ → ℝ) (A : ℝ × ℤ → ℕ)
    {σ c J η T M R s : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hN : 1 ≤ N) (hM : 2 ≤ M) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2 = M^3)
    (hy : ∀ y ∈ Y, y ∈ Icc (1:ℝ) 2)
    (hlabels : ∀ i ∈ S, i.1 ∈ Y)
    (hgrid : ∀ i ∈ S, M ≤ s+(N:ℝ)*i.2 ∧ s+(N:ℝ)*i.2 ≤ 2*M)
    (hz : ∀ i ∈ S, z i ∈ Icc M (2*M))
    (hA : ∀ i ∈ S, N ≤ A i ∧ A i ≤ 3*N)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) :
    let f := fun i w => T*(F (w/M)-F (w/M+η*i.1))/(σ*η)
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    (S.card:ℝ) ≤ (Y.card:ℝ)*(M/(N:ℝ)+1) ∧
    (∑ i ∈ S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ≤
      (Y.card:ℝ)*(M/(N:ℝ)+1)*
        (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σ*R^2/(c*(N:ℝ))) :=
  HuxleyBoundaryCoverScratch.actual_source_grid_completion_error S Y F z A (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (R:=R) (s:=s) (N:=N) hσ hc hJ hη hηmax hN hM hR hphase hy hlabels hgrid hz hA hf hbound hnegative

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    3*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∃ Refs : Finset ℝ,
      (∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → (Uref:ℝ)/(4*R^2) ≤ |a-b|) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
        b-a ≤ 7*(Uref:ℝ)/(2*R^2)) ∧
      (∀ y ∈ Y, ∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h y M ∧ h y (2*M) ≤ u) ∧
      (∀ y ∈ Y, ∀ q ∈ Refs, q ∈ Icc (h y M) (h y (2*M)) →
        ∃ z ∈ Icc M (2*M), h y z = q) ∧
      ∀ (sgrid : ℤ) (Hlen : ℝ → ℤ → ℕ), (∀ y ∈ Y, ∀ k, Hlen y k ≤ N) →
      let Lgrid := fun k : ℤ => sgrid+(N:ℤ)*k+2*(N:ℤ)
      let Good : ℝ × ℤ → Prop := fun p =>
        ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
            h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
              (sgrid:ℝ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4
      ∀ (Pcore : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → ℚ) (za : (ℝ × ℤ) → ℝ),
      (∀ p ∈ Pcore, p.1 ∈ Y ∧ Good p) →
      (∀ p ∈ Pcore, |za p-((sgrid:ℝ)+(N:ℝ)*p.2)| ≤ (N:ℝ)/16 ∧
        h p.1 (za p)=(anchor p:ℝ)) →
      (∀ p ∈ Pcore, 768*(anchor p).den ≤ Q) →
      (∀ p ∈ Pcore, (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p).den) →
      (∑ p ∈ Pcore, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
        (𝐞 (f p.1 n):ℂ)‖)^12 ≤
        2^11*((Csrc*Error)^12+
          (Csrc*(1+Real.log K₀))^12*FamilyBound Pcore) :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_selected_reference_core_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget


#print axioms actual_source_dyadic_cubic_admissibility
#print axioms cubic_completion_point_error
#print axioms actual_source_grid_completion_error
#print axioms eventually_positive_difference_selected_reference_core_physical_sieve

private theorem eventually_positive_difference_triangular_selected_reference_core_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep Vscale : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    3*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then Kupper else Klower)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∃ Refs : Finset ℝ,
      (∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → (Uref:ℝ)/(4*R^2) ≤ |a-b|) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
        b-a ≤ 7*(Uref:ℝ)/(2*R^2)) ∧
      (∀ y ∈ Y, ∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h y M ∧ h y (2*M) ≤ u) ∧
      (∀ y ∈ Y, ∀ q ∈ Refs, q ∈ Icc (h y M) (h y (2*M)) →
        ∃ z ∈ Icc M (2*M), h y z = q) ∧
      ∀ (sgrid : ℤ) (Hlen : ℝ → ℤ → ℕ), (∀ y ∈ Y, ∀ k, Hlen y k ≤ N) →
      let Lgrid := fun k : ℤ => sgrid+(N:ℤ)*k+2*(N:ℤ)
      let Good : ℝ × ℤ → Prop := fun p =>
        ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
            h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
              (sgrid:ℝ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4
      ∀ (Pcore : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → ℚ) (za : (ℝ × ℤ) → ℝ),
      (∀ p ∈ Pcore, p.1 ∈ Y ∧ Good p) →
      (∀ p ∈ Pcore, |za p-((sgrid:ℝ)+(N:ℝ)*p.2)| ≤ (N:ℝ)/16 ∧
        h p.1 (za p)=(anchor p:ℝ)) →
      (∀ p ∈ Pcore, 768*(anchor p).den ≤ Q) →
      (∀ p ∈ Pcore, (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p).den) →
      (∑ p ∈ Pcore, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
        (𝐞 (f p.1 n):ℂ)‖)^12 ≤
        2^11*((Csrc*Error)^12+
          (Csrc*(1+Real.log K₀))^12*FamilyBound Pcore) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,hCsrc,hsource⟩ :=
    positive_difference_dyadic_anchor_source_fourier hσsrc hcsrc hUsrc
  obtain ⟨_Cref,_hCref,hRefConstructor⟩ :=
    positive_difference_constructed_reference_family_uniform_grid_fourier hσsrc hcsrc hUsrc
  obtain ⟨η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
      hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hphysical⟩ :=
    eventually_positive_difference_triangular_selected_family_weighted_sieve
      hσsrc hcsrc hUsrc (by norm_num : (0:ℝ) < 1) hσ hεloss
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  let Jref := σ*Usrc/σsrc
  have hJref : 0 ≤ Jref := by dsimp only [Jref]; positivity
  have hθaction' :
      θ ≤ 1/(8*((max (8*(18*Usrc^2*1/(σsrc*csrc*κ))^2)
        (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*1/κ^2))+3)) := by
    simpa only [mul_one] using hθaction
  filter_upwards [hphysical hJref hθ hθmax hθaction'] with T hfamily
  intro Fsrc Y Q K₀ N Uref instK R Jsep Vscale η M δ Bcut Bselect
    hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
    hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
    hselectedUpper hscaleTen hQN hNsqM hUR hstrongRQ hNRM
    Cphys c J B hsmall hNR hRN hNcube hminscale
    Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
    Kupper Klower isUpper hchoice Buffer Error FamilyBound f h
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hN : 0 < N := by omega
  have hNreal : (2:ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hMtwo : 2 ≤ M := by nlinarith only [hNreal,hNsqM]
  have hM : 0 < M := by linarith only [hMtwo]
  have hNM : (N:ℝ) ≤ M := by nlinarith only [hNreal,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hQbig : 768 ≤ Q := by
    have hh : (768:ℝ) ≤ Q := by linarith only [hR,hstrongRQ]
    exact_mod_cast hh
  have hQ : 0 < Q := by omega
  have hQtwo : 2 ≤ Q := by omega
  have hRQ : R ≤ (Q:ℝ) := by nlinarith only [hR,hstrongRQ]
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hsourceData := hRefConstructor Fsrc Y N η T M R (Uref:ℝ)
    (by omega) hη (hηsmall.trans hηcap) hy hT hM hRp hUp hUR
    hreg hjets htests hnegative hscale hpad hquartic hquad hUlarge
  obtain ⟨Href,hHref,hHrefHeight,Refs,hseed,hhull,henclose,hpoints,hheights,
    hcurv,hlabels,hRefSep,hcover,hroots,hgaps,hcharts,_hrest⟩ := hsourceData
  have hencloseCurv y (hyY : y ∈ Y) : ∃ l ∈ Refs, ∃ u ∈ Refs,
      l ≤ h y M ∧ h y (2*M) ≤ u := by
    obtain ⟨l,hl,u,hu,hlo,hhi⟩ := henclose
    have hleft := abs_le.mp (hcurv y (hy y hyY) M ⟨le_rfl,by linarith only [hM]⟩)
    have hright := abs_le.mp (hcurv y (hy y hyY) (2*M) ⟨by linarith only [hM],le_rfl⟩)
    exact ⟨l,hl,u,hu,hlo.trans hleft.1,hright.2.trans hhi⟩
  refine ⟨Refs,(fun a ha b hb hab => (hRefSep a ha b hb hab).le),
    (fun a ha b hb hab hadj => (hgaps a ha b hb hab hadj).2.1),
    hencloseCurv,(fun y hyY => hroots y (hy y hyY)),?_⟩

  intro sgrid Hlen hHlen Lgrid CoreGood P anchor za hCoreData hAnchors hCuts hCounts
  have hlabelsP p (hp : p∈P) : p.1∈Y := (hCoreData p hp).1
  have hchoose (p : ℝ × ℤ) : ∃ (ab : ℝ × ℝ) (zl zu : ℝ), p∈P →
      ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      (∀ t∈Refs,¬(ab.1 < t ∧ t < ab.2)) ∧
      zl∈Icc M (2*M) ∧ zu∈Icc M (2*M) ∧ h p.1 zl=ab.1 ∧ h p.1 zu=ab.2 ∧
      M+Buffer ≤ zl ∧ zu ≤ 2*M-Buffer ∧
      zl+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
      (sgrid:ℝ)+(N:ℝ)*p.2 ≤ zu-(N:ℝ)/4 := by
    by_cases hp : p∈P
    · obtain ⟨a,ha,b,hb,hab,hadj,zl,zu,hzl,hzu,hza,hzb,hleft,hright,htleft,htright⟩ :=
        (hCoreData p hp).2
      exact ⟨(a,b),zl,zu,fun _ =>
        ⟨ha,hb,hab,hadj,hzl,hzu,hza,hzb,hleft,hright,htleft,htright⟩⟩
    · exact ⟨(0,0),0,0,fun hh => (hp hh).elim⟩
  choose gap zl zu hchosen using hchoose
  have hbracket p (hp : p∈P) :
      zl p∈Icc M (2*M) ∧ zu p∈Icc M (2*M) ∧
      h p.1 (zl p)=(gap p).1 ∧ h p.1 (zu p)=(gap p).2 ∧
      M+Buffer ≤ zl p ∧ zu p ≤ 2*M-Buffer ∧
      zl p+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
      (sgrid:ℝ)+(N:ℝ)*p.2 ≤ zu p-(N:ℝ)/4 := (hchosen p hp).2.2.2.2
  have hgridP p (hp : p∈P) :
      M ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧ (sgrid:ℝ)+(N:ℝ)*p.2 ≤ 2*M := by
    have hb := hbracket p hp
    exact ⟨by linarith only [hb.1.1,hb.2.2.2.2.2.2.1,hNp],
      by linarith only [hb.2.1.2,hb.2.2.2.2.2.2.2,hNp]⟩
  have hLgrid (p : ℝ × ℤ) : (Lgrid p.2:ℝ)-2*(N:ℝ)=(sgrid:ℝ)+(N:ℝ)*p.2 := by
    dsimp only [Lgrid]
    push_cast
    ring
  have hsourceCut p (hp : p∈P) : 2*(anchor p).den ≤ Q :=
    (Nat.mul_le_mul_right _ (show 2 ≤ 768 by decide)).trans (hCuts p hp)
  have hsourceCount p (hp : p∈P) : 128*σsrc*R^2 ≤ csrc*(Q:ℝ)*(anchor p).den := by
    exact (mul_le_mul_of_nonneg_right
      (by linarith only [hσsrc] : 128*σsrc ≤ 24576*σsrc) (sq_nonneg R)).trans (hCounts p hp)
  obtain ⟨rat,z,hrat,hround,hfourier⟩ :=
    hsource (ℝ × ℤ) P Fsrc Prod.fst (fun p => Lgrid p.2) (fun p => Hlen p.1 p.2)
      anchor za N Q η T M R (by omega)
      (fun p hp => hHlen p.1 (hlabelsP p hp) p.2)
      hη (hηsmall.trans hηcap) hT hM hRp
      (fun p hp => hy p.1 (hlabelsP p hp))
      (fun p hp => by rw [hLgrid p]; exact hgridP p hp)
      hreg hjets hnegative hscale hpad hquartic hquad hQN hsourceCut hsourceCount
      (fun p hp => by
        rw [hLgrid p]
        have ha := abs_le.mp (hAnchors p hp).1
        exact ⟨⟨by linarith only [ha.1,hNp],by linarith only [ha.2,hNp]⟩,
          (hAnchors p hp).2⟩)
  let Nlen := fun p => (Lgrid p.2-round (z p)).toNat
  obtain ⟨v,hinv,k0,hsourceBound⟩ := hfourier K₀ hsourceMesh
  have hden p (hp : p∈P) : (rat p).den ≤ Q ∧ Q ≤ 2*(rat p).den :=
    ⟨(hrat p hp).1,(hrat p hp).2.1⟩
  have hlevel p (hp : p∈P) : iteratedDeriv 2 (f p.1) (z p)/2=(rat p:ℝ) :=
    (hrat p hp).2.2.2.2.2
  have hgeomP p (hp : p∈P) :
      N ≤ Nlen p ∧ Nlen p ≤ 3*N ∧
      round (z p)+(Nlen p:ℤ)=sgrid+(N:ℤ)*p.2+2*(N:ℤ) :=
    ⟨(hround p hp).2.1,(hround p hp).2.2.1,(hround p hp).2.2.2⟩
  have hclose p (hp : p∈P) :
      |z p-((sgrid:ℝ)+(N:ℝ)*p.2)| ≤ (N:ℝ)/8 := by
    have hz := (hrat p hp).2.2.2.2.1
    have ha := abs_le.mp (hAnchors p hp).1
    exact abs_le.mpr ⟨by linarith only [hz.1,ha.1,hNp],
      by linarith only [hz.2,ha.2]⟩
  have hzin p (hp : p∈P) : zl p < z p ∧ z p < zu p := by
    have hb := hbracket p hp
    have hz := abs_le.mp (hclose p hp)
    exact ⟨by linarith only [hb.2.2.2.2.2.2.1,hz.1,hNp],
      by linarith only [hb.2.2.2.2.2.2.2,hz.2,hNp]⟩
  have hbuffer p (hp : p∈P) : M+Buffer ≤ z p ∧ z p ≤ 2*M-Buffer := by
    have hb := hbracket p hp
    exact ⟨hb.2.2.2.2.1.trans (hzin p hp).1.le,
      (hzin p hp).2.le.trans hb.2.2.2.2.2.1⟩
  have hz p (hp : p∈P) : z p∈Icc M (2*M) := by
    have hh := hbuffer p hp
    exact ⟨by linarith only [hh.1,hBuffer],by linarith only [hh.2,hBuffer]⟩
  have hminor p (hp : p∈P) :
      1 ≤ Nlen p ∧ (rat p).den ≤ Nlen p ∧
        1 ≤ (iteratedDeriv 3 (f p.1) (round (z p))/6)*((rat p).den:ℝ)^2*Nlen p ∧
      7*((iteratedDeriv 3 (f p.1) (round (z p))/6)*
        ((rat p).den:ℝ)*(Nlen p:ℝ)^2) ≤ K₀ :=
    actual_source_dyadic_cubic_admissibility Fsrc
      hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) (hy p.1 (hlabelsP p hp))
      hreg hjets hnegative hMtwo (by omega) hRp (hz p hp) hscale hQN
      (hden p hp).1 (hden p hp).2 (hsourceCut p hp) (hsourceCount p hp)
      (hgeomP p hp).1 (hgeomP p hp).2.1 hsourceMesh
  let Gaps := (Refs ×ˢ Refs).filter (fun ab =>
    ab.1 < ab.2 ∧ ∀ t ∈ Refs,¬(ab.1 < t ∧ t < ab.2))
  have hgapData ab (hab : ab ∈ Gaps) :
      ab.1 ∈ Refs ∧ ab.2 ∈ Refs ∧ ab.1 < ab.2 ∧ ∀ t ∈ Refs,¬(ab.1 < t ∧ t < ab.2) := by
    have hh := Finset.mem_filter.mp hab
    exact ⟨(Finset.mem_product.mp hh.1).1,(Finset.mem_product.mp hh.1).2,hh.2⟩
  have hgapMem p (hp : p∈P) : gap p∈Gaps := by
    have hh := hchosen p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hh.1,hh.2.1⟩,hh.2.2.1,hh.2.2.2.1⟩
  have hchartChoice (ab : ℝ × ℝ) : ∃ e r v s : ℤ, ab ∈ Gaps →
      v*r-e*s = 1 ∧ ((0 < r ∧ (e:ℝ)/r = ab.1) ∨ (r < 0 ∧ (e:ℝ)/r = ab.2)) ∧
      s ≠ 0 ∧ (e:ℝ)/r ∈ Refs ∧ (v:ℝ)/s ∈ Refs ∧ R^2 ≤ (r:ℝ)^2*(Uref:ℝ) ∧
      |(r:ℝ)| < 4*R^2/(Uref:ℝ) ∧ |(s:ℝ)| < 4*R^2/(Uref:ℝ) ∧
      |(e:ℝ)| ≤ (3*Usrc*T/(2*σsrc*M^2)+1)*(4*R^2/(Uref:ℝ)) ∧
      |(v:ℝ)| ≤ (3*Usrc*T/(2*σsrc*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    by_cases hab : ab ∈ Gaps
    · have hh := hgapData ab hab
      obtain ⟨e,r,v,s,he⟩ := hcharts ab.1 hh.1 ab.2 hh.2.1 hh.2.2.1 hh.2.2.2
      exact ⟨e,r,v,s,fun _ => he⟩
    · exact ⟨0,0,0,0,fun hh => (hab hh).elim⟩
  choose e rRef vRef sRef hchartData using hchartChoice
  have hchart ab (hab : ab ∈ Gaps) : vRef ab*rRef ab-e ab*sRef ab = 1 :=
    (hchartData ab hab).1
  have horientation ab (hab : ab ∈ Gaps) :
      ((0:ℝ) < rRef ab ∧ (e ab:ℝ)/rRef ab = ab.1) ∨
        ((rRef ab:ℝ) < 0 ∧ (e ab:ℝ)/rRef ab = ab.2) := by
    rcases (hchartData ab hab).2.1 with hh | hh
    · exact Or.inl ⟨by exact_mod_cast hh.1,hh.2⟩
    · exact Or.inr ⟨by exact_mod_cast hh.1,hh.2⟩
  have hs ab (hab : ab ∈ Gaps) : sRef ab ≠ 0 := (hchartData ab hab).2.2.1
  have hrefSet ab (hab : ab ∈ Gaps) : (e ab:ℝ)/rRef ab ∈ Refs :=
    (hchartData ab hab).2.2.2.1
  have hparentSet ab (hab : ab ∈ Gaps) : (vRef ab:ℝ)/sRef ab ∈ Refs :=
    (hchartData ab hab).2.2.2.2.1
  have hreferenceDen ab (hab : ab ∈ Gaps) : R^2 ≤ (rRef ab:ℝ)^2*(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.1
  have hrHeight ab (hab : ab ∈ Gaps) : |(rRef ab:ℝ)| ≤ 4*R^2/(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.2.1.le
  have hsHeight ab (hab : ab ∈ Gaps) : |(sRef ab:ℝ)| ≤ 4*R^2/(Uref:ℝ) :=
    (hchartData ab hab).2.2.2.2.2.2.2.1.le
  have hheightEq : 3*Usrc*T/(2*σsrc*M^2) = 3*Jref*T/(2*σ*M^2) := by
    dsimp only [Jref]
    field_simp
  have heHeight ab (hab : ab ∈ Gaps) :
      |(e ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    rw [←hheightEq]
    exact (hchartData ab hab).2.2.2.2.2.2.2.2.1
  have hvHeight ab (hab : ab ∈ Gaps) :
      |(vRef ab:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/(Uref:ℝ)) := by
    rw [←hheightEq]
    exact (hchartData ab hab).2.2.2.2.2.2.2.2.2
  have hgapWidth ab (hab : ab ∈ Gaps) : ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2) := by
    have hh := hgapData ab hab
    exact (hgaps ab.1 hh.1 ab.2 hh.2.1 hh.2.2.1 hh.2.2.2).2.1
  have hsep u (hu : u ∈ Refs) v (hv : v ∈ Refs) (huv : u ≠ v) :
      ((Uref:ℝ)/R^2)/4 < |u-v| := by
    convert hRefSep u hu v hv huv using 1
    ring
  have hwide w (hw : w ∈ Icc M (2*M)) : w ∈ Icc (3*M/4) (9*M/4) := by
    constructor <;> linarith only [hw.1,hw.2,hM]

  have hfamilyGap p (hp : p∈P) : (rat p:ℝ)∈Icc (gap p).1 (gap p).2 := by
    have hb := hbracket p hp
    have hm := positive_difference_physical_curvature_strictMono Fsrc
      hσsrc hcsrc hη (hηsmall.trans hηcap) (hy p.1 (hlabelsP p hp))
      hreg hnegative hT hM
    have hl := hm (hwide _ hb.1) (hwide _ (hz p hp)) (hzin p hp).1
    have hu := hm (hwide _ (hz p hp)) (hwide _ hb.2.1) (hzin p hp).2
    change h p.1 (zl p) < h p.1 (z p) at hl
    change h p.1 (z p) < h p.1 (zu p) at hu
    have hlp : h p.1 (z p)=(rat p:ℝ) := hlevel p hp
    rw [hb.2.2.1,hlp] at hl
    rw [hb.2.2.2.1,hlp] at hu
    exact ⟨hl.le,hu.le⟩
  let Aphase := fun _y : ℝ => (⌈M⌉:ℤ)
  let Wphase := fun _y : ℝ => 2*M-(⌈M⌉:ℤ)
  let xlocal := fun p : ℝ × ℤ => z p-(Aphase p.1:ℝ)
  let Wide := (56*(Uref:ℝ)/κ)*(N:ℝ)
  let Hshort := (N:ℝ)/(Cphys+2)
  have hWide : 0 ≤ Wide := by dsimp only [Wide]; positivity
  have hHshort : 0 ≤ Hshort := by dsimp only [Hshort]; positivity
  have hlocal p (hp : p∈P) (d : ℝ) (hd : |d|+2 ≤ Buffer) :
      xlocal p+d∈Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hb := hbuffer p hp
    have hdabs := abs_le.mp (show |d| ≤ Buffer-2 by linarith only [hd])
    have hceil := Int.ceil_lt_add_one M
    dsimp only [xlocal,Aphase,Wphase]
    exact ⟨by linarith only [hb.1,hdabs.1,hceil],
      by linarith only [hb.2,hdabs.2]⟩
  have hx p (hp : p ∈ P) : xlocal p ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal p hp 0 (by
      change |(0:ℝ)|+2 ≤ Wide+Hshort+2
      rw [abs_zero]
      linarith only [hWide,hHshort])
    simpa only [add_zero] using hh
  have hwideL p (hp : p ∈ P) : xlocal p-Wide ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal p hp (-Wide) (by
      change |-Wide|+2 ≤ Wide+Hshort+2
      rw [abs_neg,abs_of_nonneg hWide]
      linarith only [hHshort])
    simpa only [sub_eq_add_neg] using hh
  have hwideU p (hp : p ∈ P) : xlocal p+Wide ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) :=
    hlocal p hp Wide (by
      change |Wide|+2 ≤ Wide+Hshort+2
      rw [abs_of_nonneg hWide]
      linarith only [hHshort])
  have hL p (hp : p ∈ P) : xlocal p-Hshort ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) := by
    have hh := hlocal p hp (-Hshort) (by
      change |-Hshort|+2 ≤ Wide+Hshort+2
      rw [abs_neg,abs_of_nonneg hHshort]
      linarith only [hWide])
    simpa only [sub_eq_add_neg] using hh
  have hU p (hp : p ∈ P) : xlocal p+Hshort ∈ Ioo (1/2:ℝ) (Wphase p.1-1/2) :=
    hlocal p hp Hshort (by
      change |Hshort|+2 ≤ Wide+Hshort+2
      rw [abs_of_nonneg hHshort]
      linarith only [hWide])
  let ε := κ/(16*(Cphys+2)*R^2)
  have htol : csrc/(64*σsrc*R^2) ≤ ε := by
    have hb : csrc ≤ 4*κ*σsrc/(Cphys+2) := by
      convert hanchorBudget using 1
      dsimp only [Cphys]
      ring
    calc
      csrc/(64*σsrc*R^2) ≤ (4*κ*σsrc/(Cphys+2))/(64*σsrc*R^2) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = ε := by dsimp only [ε]; field_simp; ring
  have hanchor p (hp : p ∈ P) : |(anchor p:ℝ)-(rat p:ℝ)| ≤ ε := by
    rw [abs_sub_comm]
    exact ((hrat p hp).2.2.2.1).trans htol
  have hcut p (hp : p∈P) : 256*((anchor p).den:ℝ) ≤ (Q:ℝ)/3 := by
    have hh : 768*((anchor p).den:ℝ) ≤ Q := by exact_mod_cast hCuts p hp
    linarith only [hh]
  have hcount p (hp : p∈P) : 256 ≤ 2*ε*((Q:ℝ)/3)*(anchor p).den := by
    calc
      (256:ℝ) ≤ csrc*(Q:ℝ)*(anchor p).den/(96*σsrc*R^2) := by
        apply (le_div_iff₀ (by positivity : (0:ℝ) < 96*σsrc*R^2)).mpr
        nlinarith only [hCounts p hp]
      _ = 2*(csrc/(64*σsrc*R^2))*((Q:ℝ)/3)*(anchor p).den := by field_simp; ring
      _ ≤ 2*ε*((Q:ℝ)/3)*(anchor p).den := by gcongr
  have hmodel p (hp : p ∈ P) : Expdb.IsApproximateModelPhaseFunction
      (fun u => (T/T)*(Fsrc u-Fsrc (u+η*p.1))/(σsrc*η)) σ 4 δ := by
    simpa only [div_self hT.ne',one_mul] using hmodels p.1 (hlabelsP p hp)
  have hseparation p (hp : p ∈ P) q (hq : q ∈ P) (hpq : p.1 ≠ q.1) :
      1 ≤ Jsep*|p.1-q.1| := hsepY p.1 (hlabelsP p hp) q.1 (hlabelsP q hq) hpq
  obtain ⟨hcolor,hvalues⟩ :=
    hfamily P Fsrc z rat v Nlen Q K₀ N Vscale R Jsep (fun _ => sgrid)
      (η:=η) (Tsrc:=T) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
      Uref Refs Gaps Aphase Wphase gap anchor e rRef vRef sRef
      hη hηsmall hT hT hM hδ (by simp only [one_mul,le_refl]) hQ
      (fun p hp => hy p.1 (hlabelsP p hp)) hz hreg hjets htests hden hinv hnegative
      hMtwo hVscale hN hJsep hJM hNM hmesh hgeomP hseparation hmodel hlevel
      (fun p hp => ⟨(hminor p hp).1,(hminor p hp).2.1,(hminor p hp).2.2.1⟩)
      (fun p hp => (hminor p hp).2.2.2)
      hregime hR hRM hscale (fun _ _ => Int.le_ceil M)
      (fun _ _ => by dsimp only [Aphase,Wphase]; linarith only)
      hx hgapMem hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref
      hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ
      hselectedUpper hscaleTen hfamilyGap hgapData (by exact_mod_cast hQN) hNsqM hUR
      hrHeight hsHeight heHeight hvHeight hsmall hNR hRN hNcube hminscale
      hNreal hL hU hanchor hcut hcount hsize hD hΔ hBsize isUpper
      (by simpa only [Uband,mul_one] using hchoice)

  let q0 := fun p => (rat p).den
  let mu0 := fun p => iteratedDeriv 3 (f p.1) (round (z p))/6
  let ell0 := fun p => deriv (f p.1) (round (z p))
  let b0 := fun p (j : Fin 2) => (⌊(q0 p:ℝ)*ell0 p⌋+(j:ℕ) : ℤ)
  let tau0 := fun p j => ((b0 p j:ℝ)-(q0 p:ℝ)*ell0 p)/2
  let dual0 := fun p => -2*mu0 p*(Real.sqrt (2/(3*mu0 p*(q0 p:ℝ))))^3
  let x0 := fun p j =>
    (![-(v p:ℝ)*b0 p j/q0 p,-(v p:ℝ)/q0 p,
      dual0 p,3*dual0 p*tau0 p j/2] : Fin 4 → ℝ)
  let FourierNorm := fun p j =>
    ‖∑ k : ZMod K₀, ZMod.stdAddChar (-(k*k0))*
      GafniTao.fordAdditiveCharacter (∑ d,x0 p j d*
        (![(k.val+1:ℝ),(k.val+1:ℝ)^2,(k.val+1:ℝ)^((3:ℝ)/2),
          Real.sqrt (k.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let Wpoint := fun p j => (Real.sqrt (2*(q0 p:ℝ))/
    ((q0 p:ℝ)*Real.sqrt (mu0 p*(Nlen p:ℝ))))*FourierNorm p j
  let Wsum := ∑ p∈P, ∑ j : Fin 2,Wpoint p j
  have hW12 : Wsum^12 ≤ FamilyBound P := by
    have hw := (hvalues k0).2
    convert hw using 1
    · congr 1
      exact (Finset.sum_product P (Finset.univ : Finset (Fin 2))
        (fun pj => Wpoint pj.1 pj.2)).symm
    · simp only [FamilyBound,κ,Cphys,c,J,B,ChartCap,NarrowCap,Cap,
        μ₀,U₀,Δtype,C₂,C₃,Ct,Cc,Kres,Lunit,Gamma,Cthird,AupperConst,BupperConst,
        AlowerConst,BlowerConst,DupperConst,DlowerConst,CostUpper,CostLower,
        Kupper,Klower,mul_one,one_pow,
        div_self hT.ne',mul_pow,mul_assoc]
  let RawError := ∑ p∈P,(Real.sqrt (Nlen p)*Real.log (2*(Nlen p:ℝ))+
    1/(mu0 p*(Nlen p:ℝ)^2))
  have hError : RawError ≤ Error :=
    (actual_source_grid_completion_error P Y Fsrc z Nlen
      (s:=(sgrid:ℝ)) hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap)
      (by omega) hMtwo hRp hscale hy hlabelsP hgridP hz
      (fun p hp => ⟨(hgeomP p hp).1,(hgeomP p hp).2.1⟩)
      hreg hjets hnegative).2
  have hKpos : 0 < K₀ := NeZero.pos K₀
  have hlogK : 0 ≤ 1+Real.log K₀ :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hKpos))
  have hWsum : 0 ≤ Wsum := by
    apply Finset.sum_nonneg
    intro p _hp
    apply Finset.sum_nonneg
    intro j _hj
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))) (norm_nonneg _)
  have hCsrcpos : 0 ≤ Csrc := zero_le_one.trans hCsrc
  have hErrorNN : 0 ≤ Error := by
    have hlogN : 0 ≤ Real.log (6*(N:ℝ)) :=
      Real.log_nonneg (by linarith only [hNreal])
    clear * - hM hNp hσsrc hcsrc hRp hlogN
    dsimp only [Error]
    positivity
  let Orig := ∑ p∈P, ‖∑ n∈Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
    (𝐞 (f p.1 n):ℂ)‖
  have hOrig : 0 ≤ Orig := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  change Orig ≤ Csrc*((1+Real.log K₀)*Wsum+RawError) at hsourceBound
  let Aterm := Csrc*Error
  let Bterm := (Csrc*(1+Real.log K₀))*Wsum
  have hAterm : 0 ≤ Aterm := mul_nonneg hCsrcpos hErrorNN
  have hBterm : 0 ≤ Bterm := mul_nonneg (mul_nonneg hCsrcpos hlogK) hWsum
  have hOrigSum : Orig ≤ Aterm+Bterm := by
    calc
      Orig ≤ Csrc*((1+Real.log K₀)*Wsum+Error) :=
        hsourceBound.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hError) hCsrcpos)
      _ = Aterm+Bterm := by dsimp only [Aterm,Bterm]; ring
  have hBpower : Bterm^12 ≤ (Csrc*(1+Real.log K₀))^12*FamilyBound P := by
    dsimp only [Bterm]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hW12 (pow_nonneg (mul_nonneg hCsrcpos hlogK) 12)
  calc
    Orig^12 ≤ (Aterm+Bterm)^12 := pow_le_pow_left₀ hOrig hOrigSum 12
    _ ≤ 2^11*(Aterm^12+Bterm^12) := add_pow_le hAterm hBterm 12
    _ ≤ 2^11*(Aterm^12+(Csrc*(1+Real.log K₀))^12*FamilyBound P) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hBpower) (by positivity)


example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep Vscale : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    3*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then Kupper else Klower)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∃ Refs : Finset ℝ,
      (∀ a ∈ Refs, ∀ b ∈ Refs, a ≠ b → (Uref:ℝ)/(4*R^2) ≤ |a-b|) ∧
      (∀ a ∈ Refs, ∀ b ∈ Refs, a < b → (∀ q ∈ Refs,¬(a < q ∧ q < b)) →
        b-a ≤ 7*(Uref:ℝ)/(2*R^2)) ∧
      (∀ y ∈ Y, ∃ l ∈ Refs, ∃ u ∈ Refs, l ≤ h y M ∧ h y (2*M) ≤ u) ∧
      (∀ y ∈ Y, ∀ q ∈ Refs, q ∈ Icc (h y M) (h y (2*M)) →
        ∃ z ∈ Icc M (2*M), h y z = q) ∧
      ∀ (sgrid : ℤ) (Hlen : ℝ → ℤ → ℕ), (∀ y ∈ Y, ∀ k, Hlen y k ≤ N) →
      let Lgrid := fun k : ℤ => sgrid+(N:ℤ)*k+2*(N:ℤ)
      let Good : ℝ × ℤ → Prop := fun p =>
        ∃ a ∈ Refs, ∃ b ∈ Refs, a < b ∧ (∀ q ∈ Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁ ∈ Icc M (2*M) ∧ z₂ ∈ Icc M (2*M) ∧
            h p.1 z₁ = a ∧ h p.1 z₂ = b ∧ M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (sgrid:ℝ)+(N:ℝ)*p.2 ∧
              (sgrid:ℝ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4
      ∀ (Pcore : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → ℚ) (za : (ℝ × ℤ) → ℝ),
      (∀ p ∈ Pcore, p.1 ∈ Y ∧ Good p) →
      (∀ p ∈ Pcore, |za p-((sgrid:ℝ)+(N:ℝ)*p.2)| ≤ (N:ℝ)/16 ∧
        h p.1 (za p)=(anchor p:ℝ)) →
      (∀ p ∈ Pcore, 768*(anchor p).den ≤ Q) →
      (∀ p ∈ Pcore, (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p).den) →
      (∑ p ∈ Pcore, ‖∑ n ∈ Finset.Ioc (Lgrid p.2) (Lgrid p.2+Hlen p.1 p.2),
        (𝐞 (f p.1 n):ℂ)‖)^12 ≤
        2^11*((Csrc*Error)^12+
          (Csrc*(1+Real.log K₀))^12*FamilyBound Pcore) :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_triangular_selected_reference_core_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget


#print axioms eventually_positive_difference_triangular_selected_reference_core_physical_sieve

private theorem eight_grid_selected_anchor_transport {α : Type*}
    (Chunks Dcover : Finset (α × ℤ)) (n N Q : ℕ)
    (hNlink : N=8*n) (h : α → ℝ → ℝ) (σ c R : ℝ)
    (anchor : (α × ℤ) → Fin 2 → ℚ) (za : (α × ℤ) → Fin 2 → ℝ)
    (hDsub : Dcover ⊆ Chunks ∪ Chunks.image (fun p => (p.1,p.2-6)))
    (hanchors : ∀ p∈Chunks, ∀ i : Fin 2,
      |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
        else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
      h p.1 (za p i)=(anchor p i:ℝ) ∧
      768*(anchor p i).den ≤ Q ∧
      (24576*σ)*R^2 ≤ c*(Q:ℝ)*(anchor p i).den) :
    let Grid := fun r : ℤ =>
      (Dcover.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    ∃ (a : ℤ → (α × ℤ) → ℚ) (z : ℤ → (α × ℤ) → ℝ),
      Dcover.card ≤ 2*Chunks.card ∧
      (∀ r, (Grid r).card ≤ 2*Chunks.card) ∧
      (∀ r, (Grid r).image Prod.fst ⊆ Chunks.image Prod.fst) ∧
      (∀ r, ∀ p∈Grid r,
        |z r p-((r*(n:ℤ):ℤ)+(N:ℝ)*p.2)| ≤ (N:ℝ)/16 ∧
        h p.1 (z r p)=(a r p:ℝ) ∧
        768*(a r p).den ≤ Q ∧
        (24576*σ)*R^2 ≤ c*(Q:ℝ)*(a r p).den) := by
  classical
  intro Grid
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hDcard : Dcover.card ≤ 2*Chunks.card := by
    calc
      Dcover.card ≤ (Chunks ∪ Chunks.image (fun p => (p.1,p.2-6))).card :=
        Finset.card_le_card hDsub
      _ ≤ Chunks.card+(Chunks.image (fun p => (p.1,p.2-6))).card :=
        Finset.card_union_le _ _
      _ ≤ Chunks.card+Chunks.card := Nat.add_le_add_left Finset.card_image_le _
      _ = _ := by omega
  have hphase q (hq : q∈Dcover) : q.1∈Chunks.image Prod.fst := by
    rcases Finset.mem_union.mp (hDsub hq) with hh | hh
    · exact Finset.mem_image.mpr ⟨q,hh,rfl⟩
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
      exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hex (r : ℤ) (p : α × ℤ) : ∃ a : ℚ, ∃ z : ℝ, p∈Grid r →
      |z-((r*(n:ℤ):ℤ)+(N:ℝ)*p.2)| ≤ (N:ℝ)/16 ∧
        h p.1 z=(a:ℝ) ∧ 768*a.den ≤ Q ∧ (24576*σ)*R^2 ≤ c*(Q:ℝ)*a.den := by
    by_cases hp : p∈Grid r
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqD,hqmod⟩ := Finset.mem_filter.mp hq
      have hdecomp : (q.2:ℝ)=(r:ℝ)+8*((q.2/8-2:ℤ):ℝ)+16 := by
        exact_mod_cast (show q.2=r+8*(q.2/8-2)+16 by omega)
      have htEq : ((r*(n:ℤ):ℤ):ℝ)+(N:ℝ)*((q.2/8-2:ℤ):ℝ)=
          (n:ℝ)*q.2-2*(N:ℝ) := by
        rw [hNreal,hdecomp]
        push_cast
        ring
      rcases Finset.mem_union.mp (hDsub hqD) with hh | hh
      · refine ⟨anchor q 0,za q 0,fun _ => ?_⟩
        simpa only [htEq,ite_true] using hanchors q hh 0
      · obtain ⟨b,hb,hbq⟩ := Finset.mem_image.mp hh
        have hbphase : b.1=q.1 := by
          simpa only using congrArg (fun p : α × ℤ => p.1) hbq
        have hbindex : b.2-6=q.2 := by
          simpa only using congrArg (fun p : α × ℤ => p.2) hbq
        have hprobe : (n:ℝ)*q.2-2*(N:ℝ)=(n:ℝ)*b.2-11*(N:ℝ)/4 := by
          rw [←hbindex,hNreal]
          push_cast
          ring
        refine ⟨anchor b 1,za b 1,fun _ => ?_⟩
        simpa only [htEq,hprobe,show (1:Fin 2)≠0 by decide,ite_false,hbphase]
          using hanchors b hb 1
    · exact ⟨0,0,fun hh => (hp hh).elim⟩
  choose a z haz using hex
  refine ⟨a,z,hDcard,?_,?_,fun r p hp => haz r p hp⟩
  · intro r
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans hDcard)
  · intro r y hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact hphase q (Finset.mem_filter.mp hq).1

private theorem eventually_positive_difference_selected_eight_grid_chunk_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    12*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∀ n : ℕ, N=8*n →
    ∀ (Chunks : Finset (ℝ × ℤ))
      (anchor : (ℝ × ℤ) → Fin 2 → ℚ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
    (∀ p∈Chunks, p.1∈Y) →
    (∀ p∈Chunks, (n:ℝ)*p.2∈
      Icc (M+Buffer+(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)+4*(N:ℝ))
        (2*M-Buffer-(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)-(N:ℝ))) →
    (∀ p∈Chunks, ∀ i : Fin 2,
      |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
        else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
      h p.1 (za p i)=(anchor p i:ℝ) ∧
      768*(anchor p i).den ≤ Q ∧
      (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p i).den) →
    ∃ Dcover : Finset (ℝ × ℤ),
      Dcover ⊆ Chunks ∪ Chunks.image (fun p => (p.1,p.2-6)) ∧
      Dcover.card ≤ 2*Chunks.card ∧
      let Grid := fun r : ℤ =>
        (Dcover.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ r, (Grid r).card ≤ 2*Chunks.card) ∧
      (∀ r, (Grid r).image Prod.fst ⊆ Chunks.image Prod.fst) ∧
      (∑ p∈Chunks, ‖∑ k∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤
        (4:ℝ)^12*(8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,
          (2^11*((Csrc*Error)^12+
            (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    TaoTrudgianYang2025.HuxleyRationalPhase.eventually_positive_difference_selected_reference_core_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y Q K₀ N Uref instK R Jsep η M δ Bcut Bselect
    hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
    hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
    hselectedUpper hUlo hscaleTen hQN hNsqM hUR hstrongRQ hNRM
    Cphys c J B hsmall hNR hRN hNcube hminscale
    Vscale lambda Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower Cpack Cfirst Cgap Cmain Ctail
    Kupper Klower Klarge Buffer Error FamilyBound f h
    n hNlink Chunks anchor za hChunks hDeep hAnchors
  have hUlarge₃ : 3*Usrc ≤ σsrc*(Uref:ℝ) := by linarith only [hUlarge,hUsrc]
  obtain ⟨Refs,hRefSep,hRefGap,henclose,hroots,hgrid⟩ :=
    hcoreT Fsrc Y Q K₀ N Uref R Jsep  (η:=η) (M:=M) (δ:=δ)
      (Bcut:=Bcut) (Bselect:=Bselect)
      hη hηsmall hT hNtwo hR hRM  hδzero hδ hJsep hJM hy hsepY
      hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge₃
      hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
      hselectedUpper hUlo hscaleTen hQN hNsqM hUR hstrongRQ hNRM
      hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize 
  have hn : 0 < n := by omega
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hNint : (N:ℤ)=8*(n:ℤ) := by exact_mod_cast hNlink
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNpos,hNsqM]
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hscale' : T*(8*(n:ℝ))*R^2=M^3 := by rw [←hNreal]; exact hscale
  obtain ⟨H,hH,hcover⟩ := positive_difference_eight_grid_chunk_cover Fsrc Y Refs n
    hn hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) hy hreg hjets hnegative
    hT hM hRpos hscale' hRefSep hRefGap hUlarge hBuffer henclose hroots
  obtain ⟨Dcover,hDsub,hDgood,hChunksBound⟩ :=
    hcover Chunks hChunks (by simpa only [←hNreal] using hDeep)
  obtain ⟨aGrid,zGrid,hDcard,hGridCardBound,hGridPhase,hGridAnchors⟩ :=
    eight_grid_selected_anchor_transport Chunks Dcover n N Q hNlink h σsrc csrc R
      anchor za hDsub hAnchors
  refine ⟨Dcover,hDsub,hDcard,?_⟩
  intro Grid
  refine ⟨hGridCardBound,hGridPhase,?_⟩
  let X := fun r : ℤ => ∑ p∈Grid r,
    ‖∑ k∈Finset.Ioc ((n:ℤ)*(r+8*p.2+16))
      ((n:ℤ)*(r+8*p.2+16)+(H p.1 ((n:ℤ)*(r+8*p.2+16)):ℤ)),
        (𝐞 (f p.1 k):ℂ)‖
  let CoreBound := fun r : ℤ => 2^11*((Csrc*Error)^12+
    (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))
  have hDphase q (hq : q∈Dcover) : q.1∈Y := by
    rcases Finset.mem_union.mp (hDsub hq) with hh | hh
    · exact hChunks q hh
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
      exact hChunks p hp
  have hLgrid (r k : ℤ) :
      r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ)=(n:ℤ)*(r+8*k+16) := by
    rw [hNint]
    ring
  have hXbound (r : ℤ) : (X r)^12 ≤ CoreBound r := by
    let Hgrid := fun y k => H y (r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ))
    have hHgrid y (_hy : y∈Y) k : Hgrid y k ≤ N := by
      rw [hNlink]
      exact hH y _
    have hGoodGrid : ∀ p∈Grid r, p.1∈Y ∧
        ∃ a∈Refs, ∃ b∈Refs, a < b ∧ (∀ q∈Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁∈Icc M (2*M) ∧ z₂∈Icc M (2*M) ∧
            iteratedDeriv 2 (f p.1) z₁/2=a ∧ iteratedDeriv 2 (f p.1) z₂/2=b ∧
            M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ∧
              (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqD,hqmod⟩ := Finset.mem_filter.mp hq
      refine ⟨hDphase q hqD,?_⟩
      have hdecomp : (q.2:ℝ)=(r:ℝ)+8*((q.2/8-2:ℤ):ℝ)+16 := by
        exact_mod_cast (show q.2=r+8*(q.2/8-2)+16 by omega)
      have htEq : ((r*(n:ℤ):ℤ):ℝ)+(N:ℝ)*((q.2/8-2:ℤ):ℝ)=
          (n:ℝ)*q.2-2*(N:ℝ) := by
        rw [hNreal,hdecomp]
        push_cast
        ring
      dsimp only
      rw [htEq,hNreal]
      exact hDgood q hqD
    have hh := hgrid (r*(n:ℤ)) Hgrid hHgrid (Grid r) (aGrid r) (zGrid r)
      hGoodGrid
      (fun p hp => ⟨(hGridAnchors r p hp).1,(hGridAnchors r p hp).2.1⟩)
      (fun p hp => (hGridAnchors r p hp).2.2.1)
      (fun p hp => (hGridAnchors r p hp).2.2.2)
    change (∑ p∈Grid r,
      ‖∑ k∈Finset.Ioc (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ))
        (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)+(Hgrid p.1 p.2:ℤ)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤ CoreBound r at hh
    simpa only [X,Hgrid,hLgrid] using hh
  let Grids := Finset.Ico (0:ℤ) 8
  have hXnonneg r : 0 ≤ X r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hGridCard : Grids.card=8 := by decide
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Grids
    (f:=X) (p:=(12:ℝ)) (by norm_num) (fun r _ => hXnonneg r)
  have hh : (∑ r∈Grids,X r)^12 ≤ (8:ℝ)^11*∑ r∈Grids,(X r)^12 := by
    simpa only [hGridCard,Nat.cast_ofNat,
      show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hs : (∑ r∈Grids,(X r)^12) ≤ ∑ r∈Grids,CoreBound r :=
    Finset.sum_le_sum (fun r _ => hXbound r)
  calc
    _ ≤ (4*∑ r∈Grids,X r)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hChunksBound 12
    _ = (4:ℝ)^12*(∑ r∈Grids,X r)^12 := mul_pow _ _ _
    _ ≤ (4:ℝ)^12*((8:ℝ)^11*∑ r∈Grids,CoreBound r) :=
      mul_le_mul_of_nonneg_left
        (hh.trans (mul_le_mul_of_nonneg_left hs (by norm_num))) (by norm_num)
    _ = _ := by rw [mul_assoc]

private theorem eventually_positive_difference_triangular_selected_eight_grid_chunk_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep Vscale : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    12*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then Kupper else Klower)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∀ n : ℕ, N=8*n →
    ∀ (Chunks : Finset (ℝ × ℤ))
      (anchor : (ℝ × ℤ) → Fin 2 → ℚ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
    (∀ p∈Chunks, p.1∈Y) →
    (∀ p∈Chunks, (n:ℝ)*p.2∈
      Icc (M+Buffer+(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)+4*(N:ℝ))
        (2*M-Buffer-(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)-(N:ℝ))) →
    (∀ p∈Chunks, ∀ i : Fin 2,
      |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
        else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
      h p.1 (za p i)=(anchor p i:ℝ) ∧
      768*(anchor p i).den ≤ Q ∧
      (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p i).den) →
    ∃ Dcover : Finset (ℝ × ℤ),
      Dcover ⊆ Chunks ∪ Chunks.image (fun p => (p.1,p.2-6)) ∧
      Dcover.card ≤ 2*Chunks.card ∧
      let Grid := fun r : ℤ =>
        (Dcover.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ r, (Grid r).card ≤ 2*Chunks.card) ∧
      (∀ r, (Grid r).image Prod.fst ⊆ Chunks.image Prod.fst) ∧
      (∑ p∈Chunks, ‖∑ k∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤
        (4:ℝ)^12*(8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,
          (2^11*((Csrc*Error)^12+
            (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    TaoTrudgianYang2025.HuxleyRationalPhase.eventually_positive_difference_triangular_selected_reference_core_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y Q K₀ N Uref instK R Jsep Vscale η M δ Bcut Bselect
    hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
    hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
    hselectedUpper hscaleTen hQN hNsqM hUR hstrongRQ hNRM
    Cphys c J B hsmall hNR hRN hNcube hminscale
    Uband ChartCap NarrowCap Cap μ₀ U₀ Δtype
    C₂ C₃ Ct Cc Δ Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Lunit Gamma Cthird AupperConst BupperConst AlowerConst BlowerConst
    DupperConst DlowerConst CostUpper CostLower
    Kupper Klower isUpper hchoice Buffer Error FamilyBound f h
    n hNlink Chunks anchor za hChunks hDeep hAnchors
  have hUlarge₃ : 3*Usrc ≤ σsrc*(Uref:ℝ) := by linarith only [hUlarge,hUsrc]
  obtain ⟨Refs,hRefSep,hRefGap,henclose,hroots,hgrid⟩ :=
    hcoreT Fsrc Y Q K₀ N Uref R Jsep Vscale (η:=η) (M:=M) (δ:=δ)
      (Bcut:=Bcut) (Bselect:=Bselect)
      hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
      hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge₃
      hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
      hselectedUpper  hscaleTen hQN hNsqM hUR hstrongRQ hNRM
      hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize isUpper hchoice
  have hn : 0 < n := by omega
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hNint : (N:ℤ)=8*(n:ℤ) := by exact_mod_cast hNlink
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNpos,hNsqM]
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer : 0 ≤ Buffer := by dsimp only [Buffer]; positivity
  have hscale' : T*(8*(n:ℝ))*R^2=M^3 := by rw [←hNreal]; exact hscale
  obtain ⟨H,hH,hcover⟩ := positive_difference_eight_grid_chunk_cover Fsrc Y Refs n
    hn hσsrc hcsrc hUsrc hη (hηsmall.trans hηcap) hy hreg hjets hnegative
    hT hM hRpos hscale' hRefSep hRefGap hUlarge hBuffer henclose hroots
  obtain ⟨Dcover,hDsub,hDgood,hChunksBound⟩ :=
    hcover Chunks hChunks (by simpa only [←hNreal] using hDeep)
  obtain ⟨aGrid,zGrid,hDcard,hGridCardBound,hGridPhase,hGridAnchors⟩ :=
    eight_grid_selected_anchor_transport Chunks Dcover n N Q hNlink h σsrc csrc R
      anchor za hDsub hAnchors
  refine ⟨Dcover,hDsub,hDcard,?_⟩
  intro Grid
  refine ⟨hGridCardBound,hGridPhase,?_⟩
  let X := fun r : ℤ => ∑ p∈Grid r,
    ‖∑ k∈Finset.Ioc ((n:ℤ)*(r+8*p.2+16))
      ((n:ℤ)*(r+8*p.2+16)+(H p.1 ((n:ℤ)*(r+8*p.2+16)):ℤ)),
        (𝐞 (f p.1 k):ℂ)‖
  let CoreBound := fun r : ℤ => 2^11*((Csrc*Error)^12+
    (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))
  have hDphase q (hq : q∈Dcover) : q.1∈Y := by
    rcases Finset.mem_union.mp (hDsub hq) with hh | hh
    · exact hChunks q hh
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
      exact hChunks p hp
  have hLgrid (r k : ℤ) :
      r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ)=(n:ℤ)*(r+8*k+16) := by
    rw [hNint]
    ring
  have hXbound (r : ℤ) : (X r)^12 ≤ CoreBound r := by
    let Hgrid := fun y k => H y (r*(n:ℤ)+(N:ℤ)*k+2*(N:ℤ))
    have hHgrid y (_hy : y∈Y) k : Hgrid y k ≤ N := by
      rw [hNlink]
      exact hH y _
    have hGoodGrid : ∀ p∈Grid r, p.1∈Y ∧
        ∃ a∈Refs, ∃ b∈Refs, a < b ∧ (∀ q∈Refs,¬(a < q ∧ q < b)) ∧
          ∃ z₁ z₂ : ℝ, z₁∈Icc M (2*M) ∧ z₂∈Icc M (2*M) ∧
            iteratedDeriv 2 (f p.1) z₁/2=a ∧ iteratedDeriv 2 (f p.1) z₂/2=b ∧
            M+Buffer ≤ z₁ ∧ z₂ ≤ 2*M-Buffer ∧
            z₁+(N:ℝ)/4 ≤ (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ∧
              (r*(n:ℤ):ℤ)+(N:ℝ)*p.2 ≤ z₂-(N:ℝ)/4 := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqD,hqmod⟩ := Finset.mem_filter.mp hq
      refine ⟨hDphase q hqD,?_⟩
      have hdecomp : (q.2:ℝ)=(r:ℝ)+8*((q.2/8-2:ℤ):ℝ)+16 := by
        exact_mod_cast (show q.2=r+8*(q.2/8-2)+16 by omega)
      have htEq : ((r*(n:ℤ):ℤ):ℝ)+(N:ℝ)*((q.2/8-2:ℤ):ℝ)=
          (n:ℝ)*q.2-2*(N:ℝ) := by
        rw [hNreal,hdecomp]
        push_cast
        ring
      dsimp only
      rw [htEq,hNreal]
      exact hDgood q hqD
    have hh := hgrid (r*(n:ℤ)) Hgrid hHgrid (Grid r) (aGrid r) (zGrid r)
      hGoodGrid
      (fun p hp => ⟨(hGridAnchors r p hp).1,(hGridAnchors r p hp).2.1⟩)
      (fun p hp => (hGridAnchors r p hp).2.2.1)
      (fun p hp => (hGridAnchors r p hp).2.2.2)
    change (∑ p∈Grid r,
      ‖∑ k∈Finset.Ioc (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ))
        (r*(n:ℤ)+(N:ℤ)*p.2+2*(N:ℤ)+(Hgrid p.1 p.2:ℤ)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤ CoreBound r at hh
    simpa only [X,Hgrid,hLgrid] using hh
  let Grids := Finset.Ico (0:ℤ) 8
  have hXnonneg r : 0 ≤ X r := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hGridCard : Grids.card=8 := by decide
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Grids
    (f:=X) (p:=(12:ℝ)) (by norm_num) (fun r _ => hXnonneg r)
  have hh : (∑ r∈Grids,X r)^12 ≤ (8:ℝ)^11*∑ r∈Grids,(X r)^12 := by
    simpa only [hGridCard,Nat.cast_ofNat,
      show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hs : (∑ r∈Grids,(X r)^12) ≤ ∑ r∈Grids,CoreBound r :=
    Finset.sum_le_sum (fun r _ => hXbound r)
  calc
    _ ≤ (4*∑ r∈Grids,X r)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hChunksBound 12
    _ = (4:ℝ)^12*(∑ r∈Grids,X r)^12 := mul_pow _ _ _
    _ ≤ (4:ℝ)^12*((8:ℝ)^11*∑ r∈Grids,CoreBound r) :=
      mul_le_mul_of_nonneg_left
        (hh.trans (mul_le_mul_of_nonneg_left hs (by norm_num))) (by norm_num)
    _ = _ := by rw [mul_assoc]

example {α : Type*}
    (Chunks Dcover : Finset (α × ℤ)) (n N Q : ℕ)
    (hNlink : N=8*n) (h : α → ℝ → ℝ) (σ c R : ℝ)
    (anchor : (α × ℤ) → Fin 2 → ℚ) (za : (α × ℤ) → Fin 2 → ℝ)
    (hDsub : Dcover ⊆ Chunks ∪ Chunks.image (fun p => (p.1,p.2-6)))
    (hanchors : ∀ p∈Chunks, ∀ i : Fin 2,
      |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
        else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
      h p.1 (za p i)=(anchor p i:ℝ) ∧
      768*(anchor p i).den ≤ Q ∧
      (24576*σ)*R^2 ≤ c*(Q:ℝ)*(anchor p i).den) :
    let Grid := fun r : ℤ =>
      (Dcover.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
    ∃ (a : ℤ → (α × ℤ) → ℚ) (z : ℤ → (α × ℤ) → ℝ),
      Dcover.card ≤ 2*Chunks.card ∧
      (∀ r, (Grid r).card ≤ 2*Chunks.card) ∧
      (∀ r, (Grid r).image Prod.fst ⊆ Chunks.image Prod.fst) ∧
      (∀ r, ∀ p∈Grid r,
        |z r p-((r*(n:ℤ):ℤ)+(N:ℝ)*p.2)| ≤ (N:ℝ)/16 ∧
        h p.1 (z r p)=(a r p:ℝ) ∧
        768*(a r p).den ≤ Q ∧
        (24576*σ)*R^2 ≤ c*(Q:ℝ)*(a r p).den) :=
  HuxleyBoundaryCoverScratch.eight_grid_selected_anchor_transport (α:=α) Chunks Dcover n N Q hNlink h σ c R anchor za hDsub hanchors

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    12*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Uref:ℝ) →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Vscale := (Uref:ℝ)^((3:ℝ)/2)
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := 2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
      (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)

    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*(Vscale*(Kupper+Klower)+Klarge)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∀ n : ℕ, N=8*n →
    ∀ (Chunks : Finset (ℝ × ℤ))
      (anchor : (ℝ × ℤ) → Fin 2 → ℚ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
    (∀ p∈Chunks, p.1∈Y) →
    (∀ p∈Chunks, (n:ℝ)*p.2∈
      Icc (M+Buffer+(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)+4*(N:ℝ))
        (2*M-Buffer-(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)-(N:ℝ))) →
    (∀ p∈Chunks, ∀ i : Fin 2,
      |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
        else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
      h p.1 (za p i)=(anchor p i:ℝ) ∧
      768*(anchor p i).den ≤ Q ∧
      (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p i).den) →
    ∃ Dcover : Finset (ℝ × ℤ),
      Dcover ⊆ Chunks ∪ Chunks.image (fun p => (p.1,p.2-6)) ∧
      Dcover.card ≤ 2*Chunks.card ∧
      let Grid := fun r : ℤ =>
        (Dcover.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ r, (Grid r).card ≤ 2*Chunks.card) ∧
      (∀ r, (Grid r).image Prod.fst ⊆ Chunks.image Prod.fst) ∧
      (∑ p∈Chunks, ‖∑ k∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤
        (4:ℝ)^12*(8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,
          (2^11*((Csrc*Error)^12+
            (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))) :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_selected_eight_grid_chunk_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (Q K₀ N Uref : ℕ) [NeZero K₀] (R Jsep Vscale : ℝ) {η M δ Bcut Bselect : ℝ},
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y ∈ Y, y ∈ Icc (1:ℝ) 2) →
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) →
    (∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y ∈ Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2 = M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    12*Usrc ≤ σsrc*(Uref:ℝ) →
    63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
    (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    1 ≤ Uref → 0 < Bcut →
    2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    Bselect^2*(Uref:ℝ)^3*R^2 ≤ (N:ℝ)^2 →
    (Uref:ℝ) ≤ ((N:ℝ)/(Q:ℝ))^((2:ℝ)/3)/Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 →
    Q ≤ N → (N:ℝ)^2 ≤ M → (Uref:ℝ) ≤ R^2 →
    768*R ≤ (Q:ℝ) → (N:ℝ)*R ≤ M →
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*(N:ℝ) →
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let Δtype := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let CostUpper := M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := 240*CostUpper*
      (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := 240*CostLower*
      (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    ∀ isUpper : Bool,
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    let Buffer := (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let FamilyBound := fun (P : Finset (ℝ × ℤ)) =>
      (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
        C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
          (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δtype*Jsep)+
            ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then Kupper else Klower)*T^εloss)
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    ∀ n : ℕ, N=8*n →
    ∀ (Chunks : Finset (ℝ × ℤ))
      (anchor : (ℝ × ℤ) → Fin 2 → ℚ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
    (∀ p∈Chunks, p.1∈Y) →
    (∀ p∈Chunks, (n:ℝ)*p.2∈
      Icc (M+Buffer+(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)+4*(N:ℝ))
        (2*M-Buffer-(14*σsrc/csrc)*(Uref:ℝ)*(N:ℝ)-(N:ℝ))) →
    (∀ p∈Chunks, ∀ i : Fin 2,
      |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
        else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
      h p.1 (za p i)=(anchor p i:ℝ) ∧
      768*(anchor p i).den ≤ Q ∧
      (24576*σsrc)*R^2 ≤ csrc*(Q:ℝ)*(anchor p i).den) →
    ∃ Dcover : Finset (ℝ × ℤ),
      Dcover ⊆ Chunks ∪ Chunks.image (fun p => (p.1,p.2-6)) ∧
      Dcover.card ≤ 2*Chunks.card ∧
      let Grid := fun r : ℤ =>
        (Dcover.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ r, (Grid r).card ≤ 2*Chunks.card) ∧
      (∀ r, (Grid r).image Prod.fst ⊆ Chunks.image Prod.fst) ∧
      (∑ p∈Chunks, ‖∑ k∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
        (𝐞 (f p.1 k):ℂ)‖)^12 ≤
        (4:ℝ)^12*(8:ℝ)^11*∑ r∈Finset.Ico (0:ℤ) 8,
          (2^11*((Csrc*Error)^12+
            (Csrc*(1+Real.log K₀))^12*FamilyBound (Grid r))) :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_triangular_selected_eight_grid_chunk_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget


#print axioms HuxleyBoundaryCoverScratch.eight_grid_selected_anchor_transport
#print axioms HuxleyBoundaryCoverScratch.eventually_positive_difference_selected_eight_grid_chunk_physical_sieve
#print axioms HuxleyBoundaryCoverScratch.eventually_positive_difference_triangular_selected_eight_grid_chunk_physical_sieve

private theorem positive_difference_chunk_grid_dyadic_bands
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hn : 0 < n) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2) (hphase : ∀ p∈Chunks, p.1∈Y)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase)
    (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    (∀ p∈Chunks, ∀ i, probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*((3072*σ)/c)^2+(3072*σ)/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σ*R^2/(c*((Q k:ℝ)/768))+1))
    ∃ (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
        (Y.card:ℝ)*Density kmax := by
  classical
  intro f h probe hpoints Q Ctail Clow Cerror Density
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hnN : (n:ℝ) ≤ N := by rw [hNreal]; linarith only [hnp]
  let Rfine := Real.sqrt 8*R
  have hRfine : 0 < Rfine := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hR
  have hRsq : Rfine^2=8*R^2 := by
    dsimp only [Rfine]
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8)]
  have hscaleFine : T*(n:ℝ)*Rfine^2=M^3 := by
    rw [hRsq]
    rw [hNreal] at hscale
    nlinarith only [hscale]
  have hQfine : (n:ℝ)*(Qbase*2^kmax:ℕ) ≤ M :=
    (mul_le_mul_of_nonneg_right hnN (Nat.cast_nonneg _)).trans hQmax
  let Sy := fun y => (Chunks.filter (fun p => p.1=y)).image Prod.snd
  have hSy y j : j∈Sy y ↔ (y,j)∈Chunks := by
    constructor
    · intro hj
      obtain ⟨p,hp,hpj⟩ := Finset.mem_image.mp hj
      have heq : p=(y,j) := Prod.ext (Finset.mem_filter.mp hp).2 hpj
      exact heq ▸ (Finset.mem_filter.mp hp).1
    · intro hj
      exact Finset.mem_image.mpr ⟨(y,j),Finset.mem_filter.mpr ⟨hj,rfl⟩,rfl⟩
  let base := fun i : Fin 2 => if i=0 then -2*(N:ℝ) else -11*(N:ℝ)/4
  have hprobe y j i : base i+(n:ℝ)*j=probe (y,j) i := by
    dsimp only [base,probe]
    split_ifs <;> ring
  let FineDensity := fun k => 2*Cerror*(M*Rfine^2/((n:ℝ)*(Q k:ℝ)^2))*
    (2+Real.log (64*σ*Rfine^2/(c*((Q k:ℝ)/768))+1))
  have hDensity k : FineDensity k=Density k := by
    dsimp only [FineDensity,Density]
    rw [hRsq,hNreal]
    have he : 64*σ*(8*R^2)=512*σ*R^2 := by ring
    rw [he]
    ring
  have hex (y : ℝ) : ∃ (a : ℤ → Fin 2 → ℚ) (b : ℤ → Option ℕ)
      (z : ℤ → Fin 2 → ℝ), y∈Y →
      (∀ j∈Sy y, ∀ i, h y (z j i)=(a j i:ℝ) ∧
        |z j i-probe (y,j) i| ≤ (N:ℝ)/16 ∧ z j i∈Icc M (2*M)) ∧
      (∀ j∈Sy y, match b j with
        | none => ∃ i, ¬(768*(a j i).den ≤ Q kmax ∧
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(a j i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(a j i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(a j i).den)) ∧
      (∀ k ≤ kmax, (((Sy y).filter (fun j => b j=some (k+1))).card:ℝ) ≤ Density k) ∧
      (((Sy y).filter (fun j => b j=none)).card:ℝ) ≤ Density kmax := by
    by_cases hyY : y∈Y
    · have hpointsFine j (hj : j∈Sy y) i :
          base i+(n:ℝ)*j∈Icc (M+(n:ℝ)/4) (2*M-(n:ℝ)/4) := by
        rw [hprobe y j i]
        have hh := hpoints (y,j) ((hSy y j).mp hj) i
        constructor <;> linarith only [hh.1,hh.2,hnN]
      obtain ⟨a,b,z,_hminimal,hroots,hband,_htransfer,hcounts,htail⟩ :=
        positive_difference_two_probe_dyadic_root_family (Sy y) F n Qbase kmax 768
          base (3072*σ) hσ hc hJ hη hηmax (hy y hyY)
          hreg hbound htests hnegative hT hM hn hRfine hscaleFine
          (by norm_num) hQbase (by positivity) hpointsFine hQfine
      refine ⟨a,b,z,fun _ => ⟨?_,?_,?_,?_⟩⟩
      · intro j hj i
        have hh := hroots j hj i
        change h y (z j i)=(a j i:ℝ) ∧
          |z j i-(base i+(n:ℝ)*j)| ≤ (n:ℝ)/16 ∧ z j i∈Icc M (2*M) at hh
        rw [hprobe y j i] at hh
        exact ⟨hh.1,hh.2.1.trans (div_le_div_of_nonneg_right hnN (by norm_num)),hh.2.2⟩
      · intro j hj
        have hh := hband j hj
        have hB : (3072*σ)*Rfine^2=(24576*σ)*R^2 := by rw [hRsq]; ring
        dsimp only at hh
        rw [hB] at hh
        cases hb : b j with
        | none => simpa only [hb] using hh
        | some k =>
          rw [hb] at hh
          exact ⟨hh.1,hh.2.1⟩
      · intro k hk
        have hh := hcounts k hk
        change _ ≤ FineDensity k at hh
        exact hh.trans_eq (hDensity k)
      · change _ ≤ FineDensity kmax at htail
        exact htail.trans_eq (hDensity kmax)
    · exact ⟨fun _ _ => 0,fun _ => none,fun _ _ => 0,fun hh => (hyY hh).elim⟩
  choose a b z hdata using hex
  let anchor := fun p : ℝ × ℤ => a p.1 p.2
  let band := fun p : ℝ × ℤ => b p.1 p.2
  let za := fun p : ℝ × ℤ => z p.1 p.2
  have hcount (label : Option ℕ) (Bound : ℝ)
      (hlocal : ∀ y∈Y, (((Sy y).filter (fun j => b y j=label)).card:ℝ) ≤ Bound) :
      ((Chunks.filter (fun p => band p=label)).card:ℝ) ≤ (Y.card:ℝ)*Bound := by
    let E := Chunks.filter (fun p => band p=label)
    let Ey := fun y => (E.filter (fun p => p.1=y)).image Prod.snd
    have hEq y : Ey y=(Sy y).filter (fun j => b y j=label) := by
      ext j
      constructor
      · intro hj
        obtain ⟨p,hp,hpj⟩ := Finset.mem_image.mp hj
        obtain ⟨hpE,hpy⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpC,hpb⟩ := Finset.mem_filter.mp hpE
        have heq : p=(y,j) := Prod.ext hpy hpj
        subst p
        exact Finset.mem_filter.mpr ⟨(hSy y j).mpr hpC,hpb⟩
      · intro hj
        obtain ⟨hjS,hjb⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_image.mpr ⟨(y,j),
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(hSy y j).mp hjS,hjb⟩,rfl⟩,rfl⟩
    have hcard y : (Ey y).card=(E.filter (fun p => p.1=y)).card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq hpq
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans
        (Finset.mem_filter.mp hq).2.symm) hpq
    have hmaps : ∀ p∈E, p.1∈Y := fun p hp => hphase p (Finset.mem_filter.mp hp).1
    have hsum : (∑ y∈Y,((Ey y).card:ℝ))=E.card := by
      simp_rw [hcard]
      have hh := Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1:ℝ))
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
    change (E.card:ℝ) ≤ _
    rw [←hsum]
    calc
      _ ≤ ∑ _y∈Y,Bound := Finset.sum_le_sum (fun y hyY => by rw [hEq]; exact hlocal y hyY)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  refine ⟨anchor,band,za,?_,?_,?_,?_⟩
  · intro p hp i
    exact (hdata p.1 (hphase p hp)).1 p.2 ((hSy p.1 p.2).mpr hp) i
  · intro p hp
    exact (hdata p.1 (hphase p hp)).2.1 p.2 ((hSy p.1 p.2).mpr hp)
  · intro k hk
    exact hcount (some (k+1)) (Density k) (fun y hyY => (hdata y hyY).2.2.1 k hk)
  · exact hcount none (Density kmax) (fun y hyY => (hdata y hyY).2.2.2)

example
    (Chunks : Finset (ℝ × ℤ)) (Y : Finset ℝ) (F : ℝ → ℝ)
    (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {σ c J η T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hn : 0 < n) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2) (hphase : ∀ p∈Chunks, p.1∈Y)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase)
    (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    (∀ p∈Chunks, ∀ i, probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4)) →
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*((3072*σ)/c)^2+(3072*σ)/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σ*R^2/(c*((Q k:ℝ)/768))+1))
    ∃ (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
        (Y.card:ℝ)*Density kmax :=
  HuxleyBoundaryCoverScratch.positive_difference_chunk_grid_dyadic_bands Chunks Y F n N Qbase kmax hNlink (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (R:=R) hσ hc hJ hn hη hηmax hy hphase hT hM hR hreg hbound htests hnegative hscale hQbase hQmax


#print axioms HuxleyBoundaryCoverScratch.positive_difference_chunk_grid_dyadic_bands

private theorem integer_chunk_dyadic_band_power
    {α : Type*} (Chunks : Finset (α × ℤ)) (v : α → ℤ → ℂ)
    (n kmax : ℕ) (band : (α × ℤ) → Option ℕ)
    (hv : ∀ y k, ‖v y k‖ ≤ 1)
    (hband : ∀ p∈Chunks, ∀ k, band p=some k → k ≤ kmax) :
    (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12 ≤
      ((kmax:ℝ)+2)^11*
        (((n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ))^12+
          ∑ k∈Finset.range (kmax+1),
            (∑ p∈Chunks.filter (fun p => band p=some k),
              ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12) := by
  classical
  let Labels := insert none ((Finset.range (kmax+1)).image some)
  let Chunk := fun p : α × ℤ =>
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖
  let W := fun label => ∑ p∈Chunks.filter (fun p => band p=label),Chunk p
  have hW label : 0 ≤ W label := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hmaps : ∀ p∈Chunks, band p∈Labels := by
    intro p hp
    cases hb : band p with
    | none => exact Finset.mem_insert_self _ _
    | some k =>
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by
        have hh := hband p hp k hb
        omega),rfl⟩
  have hsum : (∑ label∈Labels,W label)=∑ p∈Chunks,Chunk p :=
    Finset.sum_fiberwise_of_maps_to hmaps Chunk
  have hcardLabels : Labels.card=kmax+2 := by
    have hnone : (none : Option ℕ)∉(Finset.range (kmax+1)).image some := by simp
    change (insert none ((Finset.range (kmax+1)).image some)).card=kmax+2
    rw [Finset.card_insert_of_notMem hnone,
      Finset.card_image_of_injective _ (Option.some_injective _),Finset.card_range]
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Labels
    (f:=W) (p:=(12:ℝ)) (by norm_num) (fun label _ => hW label)
  have hpower : (∑ p∈Chunks,Chunk p)^12 ≤
      ((kmax:ℝ)+2)^11*∑ label∈Labels,(W label)^12 := by
    simpa only [hsum,hcardLabels,Nat.cast_add,Nat.cast_ofNat,
      show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hchunk p : Chunk p ≤ (n:ℝ) := by
    have hcard : (Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1))).card=n := by
      rw [Int.card_Ioc,show (n:ℤ)*(p.2+1)-(n:ℤ)*p.2=(n:ℤ) by ring]
      simp only [Int.toNat_natCast]
    calc
      Chunk p ≤ ∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),‖v p.1 j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(1:ℝ) :=
        Finset.sum_le_sum (fun j _ => hv p.1 j)
      _ = _ := by simp only [Finset.sum_const,hcard,nsmul_eq_mul,mul_one]
  have hterminal : W none ≤ (n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ) := by
    calc
      W none ≤ ∑ _p∈Chunks.filter (fun p => band p=none),(n:ℝ) :=
        Finset.sum_le_sum (fun p _ => hchunk p)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hlabelSum : (∑ label∈Labels,(W label)^12)=
      (W none)^12+∑ k∈Finset.range (kmax+1),(W (some k))^12 := by
    rw [Finset.sum_insert (by simp)]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Option.some_injective _ hab
  calc
    _ ≤ ((kmax:ℝ)+2)^11*∑ label∈Labels,(W label)^12 := hpower
    _ = ((kmax:ℝ)+2)^11*((W none)^12+
        ∑ k∈Finset.range (kmax+1),(W (some k))^12) := by rw [hlabelSum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (hW none) hterminal 12) le_rfl) (by positivity)

example
    {α : Type*} (Chunks : Finset (α × ℤ)) (v : α → ℤ → ℂ)
    (n kmax : ℕ) (band : (α × ℤ) → Option ℕ)
    (hv : ∀ y k, ‖v y k‖ ≤ 1)
    (hband : ∀ p∈Chunks, ∀ k, band p=some k → k ≤ kmax) :
    (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12 ≤
      ((kmax:ℝ)+2)^11*
        (((n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ))^12+
          ∑ k∈Finset.range (kmax+1),
            (∑ p∈Chunks.filter (fun p => band p=some k),
              ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)^12) :=
  HuxleyBoundaryCoverScratch.integer_chunk_dyadic_band_power (α:=α) Chunks v n kmax band hv hband


#print axioms HuxleyBoundaryCoverScratch.integer_chunk_dyadic_band_power

private theorem integer_subinterval_trimmed_chunk_selection
    (n : ℕ) (hn : 0 < n) {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    B-A ≤ Budget ∨
      ∃ a b : ℤ, a₀ ≤ a ∧ b ≤ b₀ ∧ A ≤ (n:ℤ)*a ∧ a ≤ b ∧
        (n:ℤ)*b ≤ B ∧ ((n:ℤ)*a-A)+(B-(n:ℤ)*b) ≤ Budget := by
  intro Budget
  have hnz : (0:ℤ) < n := by exact_mod_cast hn
  have hceil : A < (n:ℤ)*(A/(n:ℤ)+1) ∧ (n:ℤ)*(A/(n:ℤ)+1) ≤ A+n := by
    have hzero := Int.emod_nonneg A hnz.ne'
    have hupper := Int.emod_lt_of_pos A hnz
    have heq := Int.mul_ediv_add_emod A (n:ℤ)
    constructor <;> nlinarith only [hzero,hupper,heq]
  have hfloor : (n:ℤ)*(B/(n:ℤ)) ≤ B ∧ B ≤ (n:ℤ)*(B/(n:ℤ))+n := by
    have hzero := Int.emod_nonneg B hnz.ne'
    have hupper := Int.emod_lt_of_pos B hnz
    have heq := Int.mul_ediv_add_emod B (n:ℤ)
    constructor <;> linarith only [hzero,hupper,heq]
  let a := max a₀ (A/(n:ℤ)+1)
  let b := min b₀ (B/(n:ℤ))
  have ha : A ≤ (n:ℤ)*a :=
    hceil.1.le.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hnz.le)
  have hb : (n:ℤ)*b ≤ B :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hnz.le).trans hfloor.1
  have hleft : (n:ℤ)*a-A ≤ (n:ℤ)*a₀-A₀+n := by
    rcases le_total a₀ (A/(n:ℤ)+1) with hh | hh
    · rw [show a=A/(n:ℤ)+1 from max_eq_right hh]
      linarith only [hceil.2,ha₀]
    · rw [show a=a₀ from max_eq_left hh]
      linarith only [hA,hnz]
  have hright : B-(n:ℤ)*b ≤ B₀-(n:ℤ)*b₀+n := by
    rcases le_total b₀ (B/(n:ℤ)) with hh | hh
    · rw [show b=b₀ from min_eq_left hh]
      linarith only [hB,hnz]
    · rw [show b=B/(n:ℤ) from min_eq_right hh]
      linarith only [hfloor.2,hb₀]
  have hbudget : ((n:ℤ)*a-A)+(B-(n:ℤ)*b) ≤ Budget := by
    dsimp only [Budget]
    linarith only [hleft,hright]
  by_cases hab : a ≤ b
  · exact Or.inr ⟨a,b,le_max_left _ _,min_le_left _ _,ha,hab,hb,hbudget⟩
  · left
    have horder : (n:ℤ)*b ≤ (n:ℤ)*a :=
      mul_le_mul_of_nonneg_left (le_of_not_ge hab) hnz.le
    linarith only [hbudget,horder]

example
    (n : ℕ) (hn : 0 < n) {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    B-A ≤ Budget ∨
      ∃ a b : ℤ, a₀ ≤ a ∧ b ≤ b₀ ∧ A ≤ (n:ℤ)*a ∧ a ≤ b ∧
        (n:ℤ)*b ≤ B ∧ ((n:ℤ)*a-A)+(B-(n:ℤ)*b) ≤ Budget :=
  HuxleyBoundaryCoverScratch.integer_subinterval_trimmed_chunk_selection n hn (A₀:=A₀) (B₀:=B₀) (a₀:=a₀) (b₀:=b₀) (A:=A) (B:=B) ha₀ hb₀ hA hB


#print axioms HuxleyBoundaryCoverScratch.integer_subinterval_trimmed_chunk_selection

private theorem integer_subinterval_trimmed_chunks {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (hab : A ≤ B)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc A B, ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) := by
  classical
  intro Budget
  rcases integer_subinterval_trimmed_chunk_selection n hn ha₀ hb₀ hA hB with
    hshort | ⟨a,b,haa,hbb,ha,hab',hb,hcost⟩
  · refine ⟨∅,Finset.empty_subset _,?_⟩
    have hcard : ((Finset.Ioc A B).card:ℝ)=((B-A:ℤ):ℝ) := by
      exact_mod_cast (show ((Finset.Ioc A B).card:ℤ)=B-A by
        rw [Int.card_Ioc,Int.toNat_of_nonneg (sub_nonneg.mpr hab)])
    have hone y (hyY : y∈Y) : ‖∑ j∈Finset.Ioc A B,v y j‖ ≤ (Budget:ℝ) := by
      calc
        _ ≤ ∑ j∈Finset.Ioc A B,‖v y j‖ := norm_sum_le _ _
        _ ≤ ∑ _j∈Finset.Ioc A B,(1:ℝ) := Finset.sum_le_sum (fun j hj => hv y hyY j hj)
        _ = ((B-A:ℤ):ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hcard]
        _ ≤ (Budget:ℝ) := by exact_mod_cast hshort
    have hh := Finset.sum_le_sum hone
    simpa only [Finset.sum_empty,zero_add,Finset.sum_const,nsmul_eq_mul] using hh
  · let Chunks := Y ×ˢ Finset.Ico a b
    refine ⟨Chunks,?_,?_⟩
    · intro p hp
      obtain ⟨hpY,hpI⟩ := Finset.mem_product.mp hp
      obtain ⟨hpa,hpb⟩ := Finset.mem_Ico.mp hpI
      exact Finset.mem_product.mpr ⟨hpY,Finset.mem_Ico.mpr
        ⟨haa.trans hpa,hpb.trans_le hbb⟩⟩
    · have hh := Finset.sum_le_sum (fun y hyY =>
        integer_whole_sum_le_chunks_and_endpoints (v y) n ha hab' hb (hv y hyY))
      have hmid : (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,v y j‖) ≤
          (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
            (Y.card:ℝ)*((((n:ℤ)*a-A)+(B-(n:ℤ)*b):ℤ):ℝ) := by
        convert hh using 1
        simp only [Chunks,Finset.sum_product,Finset.sum_add_distrib,Finset.sum_const,
          nsmul_eq_mul,Int.cast_add]
        ring
      exact hmid.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hcost) (Nat.cast_nonneg _)))

example {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ A B : ℤ}
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (hab : A ≤ B)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc A B, ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) :=
  HuxleyBoundaryCoverScratch.integer_subinterval_trimmed_chunks (α:=α) Y v n hn (A₀:=A₀) (B₀:=B₀) (a₀:=a₀) (b₀:=b₀) (A:=A) (B:=B) ha₀ hb₀ hA hB hab hv


#print axioms HuxleyBoundaryCoverScratch.integer_subinterval_trimmed_chunks

private theorem positive_difference_subinterval_dyadic_band_reduction
    (Y : Finset ℝ) (F : ℝ → ℝ) (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {σ c J η T M R Buffer Width : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hn : 0 < n) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase) (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M)
    (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(N:ℝ) ≤ M)
    (A B : ℤ) (hA : ⌈M⌉ ≤ A) (hab : A ≤ B) (hB : B ≤ ⌊2*M⌋) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*((3072*σ)/c)^2+(3072*σ)/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σ*R^2/(c*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ))
    ∃ (Chunks : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, p.1∈Y) ∧
      (∀ p∈Chunks, (n:ℝ)*p.2∈
        Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ))) ∧
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            ∑ k∈Finset.range (kmax+1),
              (∑ p∈Chunks.filter (fun p => band p=some k),
                ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
                  (𝐞 (f p.1 j):ℂ)‖)^12)+Endpoint^12) := by
  classical
  intro f h probe Q Ctail Clow Cerror Density Endpoint
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hNp : (0:ℝ) < N := by rw [hNreal]; positivity
  obtain ⟨a₀,b₀,ha₀,hab₀,hb₀,hdeep₀,hend₀⟩ :=
    eight_grid_endpoint_selection n hn hBuffer hWidth (by
      simpa only [←hNreal] using hroom)
  let v := fun y j : ℝ => (𝐞 (f y j):ℂ)
  obtain ⟨Chunks,hChunks,hwhole⟩ :=
    integer_subinterval_trimmed_chunks Y (fun y j => v y j) n hn ha₀ hb₀ hA hB hab
      (fun _ _ _ _ => by simp [v])
  have hphase p (hp : p∈Chunks) : p.1∈Y := (Finset.mem_product.mp (hChunks hp)).1
  have hdeep p (hp : p∈Chunks) : (n:ℝ)*p.2∈
      Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ)) := by
    simpa only [←hNreal] using hdeep₀ p.2 (Finset.mem_product.mp (hChunks hp)).2
  have hpoints p (hp : p∈Chunks) i :
      probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4) := by
    have hh := hdeep p hp
    dsimp only [probe]
    split_ifs <;> constructor <;> linarith only [hh.1,hh.2,hBuffer,hWidth,hNp]
  obtain ⟨anchor,band,za,hroots,hbands,hcounts,htail⟩ :=
    positive_difference_chunk_grid_dyadic_bands Chunks Y F n N Qbase kmax hNlink
      hσ hc hJ hn hη hηmax hy hphase hT hM hR hreg hbound htests hnegative
      hscale hQbase hQmax hpoints
  have hleft : M ≤ (n:ℝ)*a₀ :=
    (Int.le_ceil M).trans (by exact_mod_cast ha₀)
  have hright : (n:ℝ)*b₀ ≤ 2*M :=
    (by exact_mod_cast hb₀ : (n:ℝ)*b₀ ≤ (⌊2*M⌋:ℤ)).trans (Int.floor_le (2*M))
  have hcardI : ((Finset.Ico a₀ b₀).card:ℝ)=((b₀-a₀:ℤ):ℝ) := by
    exact_mod_cast (show ((Finset.Ico a₀ b₀).card:ℤ)=b₀-a₀ by
      rw [Int.card_Ico,Int.toNat_of_nonneg (sub_nonneg.mpr hab₀)])
  have hcardIle : ((Finset.Ico a₀ b₀).card:ℝ) ≤ 8*M/(N:ℝ) := by
    apply (le_div_iff₀ hNp).mpr
    rw [hcardI,hNreal]
    push_cast
    nlinarith only [hleft,hright]
  have hcardChunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) := by
    have hh : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*((Finset.Ico a₀ b₀).card:ℝ) := by
      exact_mod_cast (show Chunks.card ≤ Y.card*(Finset.Ico a₀ b₀).card by
        simpa only [Finset.card_product] using Finset.card_le_card hChunks)
    exact hh.trans (mul_le_mul_of_nonneg_left hcardIle (Nat.cast_nonneg _))
  refine ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,?_⟩
  have hbudget :
      ((((n:ℤ)*a₀-⌈M⌉)+(⌊2*M⌋-(n:ℤ)*b₀)+2*(n:ℤ):ℤ):ℝ) ≤
        2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ) := by
    have hh := hend₀
    rw [←hNreal] at hh
    push_cast at hh ⊢
    linarith only [hh]
  let Mass := ∑ p∈Chunks,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  have hmass : 0 ≤ Mass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hEndpoint : 0 ≤ Endpoint := by dsimp only [Endpoint]; positivity
  have hwhole' : (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,(𝐞 (f y j):ℂ)‖) ≤ Mass+Endpoint :=
    hwhole.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)))
  have hbandMax p (hp : p∈Chunks) k (hk : band p=some k) : k ≤ kmax := by
    have hh := hbands p hp
    rw [hk] at hh
    exact hh.1
  have hpower := integer_chunk_dyadic_band_power Chunks (fun y j => v y j) n kmax band
    (fun _ _ => by simp [v]) hbandMax
  have htailLe : (n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
      (n:ℝ)*(Y.card:ℝ)*Density kmax := by
    have htail' : ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
        (Y.card:ℝ)*Density kmax := htail
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail' hnp.le
  have hpower' : Mass^12 ≤ ((kmax:ℝ)+2)^11*
      (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
        ∑ k∈Finset.range (kmax+1),
          (∑ p∈Chunks.filter (fun p => band p=some k),
            ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖)^12) :=
    hpower.trans (mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (by positivity) htailLe 12) le_rfl) (by positivity))
  calc
    _ ≤ (Mass+Endpoint)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hwhole' 12
    _ ≤ 2^11*(Mass^12+Endpoint^12) := add_pow_le hmass hEndpoint 12
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hpower' le_rfl) (by norm_num)

example
    (Y : Finset ℝ) (F : ℝ → ℝ) (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {σ c J η T M R Buffer Width : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hn : 0 < n) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase) (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M)
    (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(N:ℝ) ≤ M)
    (A B : ℤ) (hA : ⌈M⌉ ≤ A) (hab : A ≤ B) (hB : B ≤ ⌊2*M⌋) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*((3072*σ)/c)^2+(3072*σ)/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σ*R^2/(c*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ))
    ∃ (Chunks : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, p.1∈Y) ∧
      (∀ p∈Chunks, (n:ℝ)*p.2∈
        Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ))) ∧
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A B,(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            ∑ k∈Finset.range (kmax+1),
              (∑ p∈Chunks.filter (fun p => band p=some k),
                ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
                  (𝐞 (f p.1 j):ℂ)‖)^12)+Endpoint^12) :=
  HuxleyBoundaryCoverScratch.positive_difference_subinterval_dyadic_band_reduction Y F n N Qbase kmax hNlink (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (R:=R) (Buffer:=Buffer) (Width:=Width) hσ hc hJ hn hη hηmax hy hT hM hR hreg hbound htests hnegative hscale hQbase hQmax hBuffer hWidth hroom A B hA hab hB


#print axioms HuxleyBoundaryCoverScratch.positive_difference_subinterval_dyadic_band_reduction
private theorem eventually_positive_difference_selected_band_subinterval_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Vscale := fun k : ℕ =>
      let Uref := Usel k
      (Uref:ℝ)^((3:ℝ)/2)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := fun k : ℕ =>
      let Q := Q k
      2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*((Vscale k)*((Kupper k)+(Klower k))+(Klarge k))*T^εloss)
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℤ, ⌈M⌉ ≤ A → A ≤ Bint → Bint ≤ ⌊2*M⌋ →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A Bint,(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    eventually_positive_difference_selected_eight_grid_chunk_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y n N Qbase kmax Kmesh Usel R Jsep η M δ Bcut Bselect
    hK hNlink hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hregime
    hBcut hBselectSize hcutMargin hscaleTen hNsqM hNRM Q
    Cphys c J B lambda Uband ChartCap NarrowCap Cap μ₀ U₀ C₂ C₃ Ct Cc
    Ccurv Kres Esize Dbase Tbase Lunit Gamma Cthird
    AupperConst BupperConst AlowerConst BlowerConst DupperConst DlowerConst
    Cpack Cfirst Cgap Cmain Ctail Error f
    Vscale Δtype Δ D CostUpper CostLower Kupper Klower Klarge Buffer Width FamilyBound
    hsmall hNR hRN hNcube hsize hBsize hvalid hUmax hroom
    CtailBand ClowBand CerrorBand Density Endpoint A Bint hA hab hB
  have hn : 0 < n := by omega
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNp,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer0 : 0 ≤ Buffer 0 := by dsimp only [Buffer]; positivity
  have hWidth0 : 0 ≤ Width 0 := by dsimp only [Width]; positivity
  have hQbase : 768 ≤ Qbase := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hh : (768:ℝ) ≤ Q 0 := by nlinarith only [hstrong,hR]
    have hz : 768 ≤ Q 0 := by exact_mod_cast hh
    simpa only [Q,pow_zero,mul_one] using hz
  have hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M := by
    obtain ⟨_,_,_,_,_,_,_,hQN,_,_,_,_,_⟩ := hvalid kmax le_rfl
    have hh : (Q kmax:ℝ) ≤ N := by exact_mod_cast hQN
    calc
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ (N:ℝ)*(N:ℝ) :=
        mul_le_mul_of_nonneg_left hh hNp.le
      _ = (N:ℝ)^2 := by ring
      _ ≤ M := hNsqM
  obtain ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,
      hReduction⟩ :=
    positive_difference_subinterval_dyadic_band_reduction Y Fsrc n N Qbase kmax hNlink
      hσsrc hcsrc hUsrc hn hη (hηsmall.trans hηcap) hy hT hM hRp
      hreg hjets htests hnegative hscale hQbase hQmax hBuffer0 hWidth0 hroom
      A Bint hA hab hB
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let GridOf := fun (Dp : Finset (ℝ × ℤ)) (r : ℤ) =>
    (Dp.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let BandSum := fun k => ∑ p∈Selected k,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  let CoreSum := fun k Dp => ∑ r∈Finset.Ico (0:ℤ) 8,
    (2^11*((Csrc*Error)^12+
      (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (GridOf Dp r)))
  have hBufferMono k (hk : k ≤ kmax) : Buffer k ≤ Buffer 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hκ.le)
        (Nat.cast_nonneg _)) le_rfl) le_rfl
  have hWidthMono k (hk : k ≤ kmax) : Width k ≤ Width 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 14*σsrc/csrc)) (Nat.cast_nonneg _)
  have hchoose (k : ℕ) : ∃ Dp : Finset (ℝ × ℤ), k ≤ kmax →
      Dp ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
      Dp.card ≤ 2*(Selected k).card ∧
      (∀ r, (GridOf Dp r).card ≤ 2*(Selected k).card) ∧
      (∀ r, (GridOf Dp r).image Prod.fst ⊆ Y) ∧
      (BandSum k)^12 ≤ (4:ℝ)^12*(8:ℝ)^11*CoreSum k Dp := by
    by_cases hk : k ≤ kmax
    · obtain ⟨hUlarge,hsourceMesh,hmesh,hUref,hselectedWrap,hUupper,hUlower,
        hQN,hUR,hstrongRQ,hminscale,hD,hΔ⟩ := hvalid k hk
      letI : NeZero (Kmesh k) := ⟨Nat.ne_of_gt (hK k)⟩
      have hSelY p (hp : p∈Selected k) : p.1∈Y := hphase p (Finset.mem_filter.mp hp).1
      have hSelDeep p (hp : p∈Selected k) :
          (n:ℝ)*p.2∈Icc (M+Buffer k+Width k+4*(N:ℝ))
            (2*M-Buffer k-Width k-(N:ℝ)) := by
        have hh := hdeep p (Finset.mem_filter.mp hp).1
        have hbuf := hBufferMono k hk
        have hwid := hWidthMono k hk
        constructor <;> linarith only [hh.1,hh.2,hbuf,hwid]
      have hSelAnchors p (hp : p∈Selected k) (i : Fin 2) :
          |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
            else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
          iteratedDeriv 2 (f p.1) (za p i)/2=(anchor p i:ℝ) ∧
          768*(anchor p i).den ≤ Q k ∧
          (24576*σsrc)*R^2 ≤ csrc*(Q k:ℝ)*(anchor p i).den := by
        obtain ⟨hpC,hpk⟩ := Finset.mem_filter.mp hp
        have hr := hroots p hpC i
        have hb := hbands p hpC
        rw [hpk] at hb
        exact ⟨hr.2.1,hr.1,(hb.2 i).1,(hb.2 i).2⟩
      obtain ⟨Dp,hDsub,hDcard,hGcard,hGphase,hBandBound⟩ :=
        hcoreT Fsrc Y (Q k) (Kmesh k) N (Usel k) R Jsep
          (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
          hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
          hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
          hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
          hUupper hUlower hscaleTen hQN hNsqM hUR hstrongRQ hNRM
          hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize
          n hNlink (Selected k) anchor za hSelY hSelDeep hSelAnchors
      have hPhaseY r : (GridOf Dp r).image Prod.fst ⊆ Y := by
        intro y hyGrid
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hGphase r hyGrid)
        exact hSelY p hp
      exact ⟨Dp,fun _ => ⟨hDsub,hDcard,hGcard,hPhaseY,hBandBound⟩⟩
    · exact ⟨∅,fun hh => (hk hh).elim⟩
  choose Dcover hDcover using hchoose
  refine ⟨Chunks,band,Dcover,hcardChunks,hcounts,htail,?_⟩
  intro SelectedOut Grid
  refine ⟨fun k hk => ⟨(hDcover k hk).1,(hDcover k hk).2.1,
    (hDcover k hk).2.2.1,(hDcover k hk).2.2.2.1⟩,?_⟩
  have hsum : (∑ k∈Finset.range (kmax+1),(BandSum k)^12) ≤
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),CoreSum k (Dcover k) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1), (4:ℝ)^12*(8:ℝ)^11*CoreSum k (Dcover k) :=
        Finset.sum_le_sum (fun k hk => (hDcover k (by
          have hh := Finset.mem_range.mp hk
          omega)).2.2.2.2)
      _ = _ := by rw [Finset.mul_sum]
  exact hReduction.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity))
      le_rfl) (by norm_num))

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Vscale := fun k : ℕ =>
      let Uref := Usel k
      (Uref:ℝ)^((3:ℝ)/2)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := fun k : ℕ =>
      let Q := Q k
      2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*((Vscale k)*((Kupper k)+(Klower k))+(Klarge k))*T^εloss)
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℤ, ⌈M⌉ ≤ A → A ≤ Bint → Bint ≤ ⌊2*M⌋ →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A Bint,(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_selected_band_subinterval_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget


#print axioms HuxleyBoundaryCoverScratch.eventually_positive_difference_selected_band_subinterval_physical_sieve
private theorem eventually_positive_difference_triangular_selected_band_subinterval_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep Vscale : ℝ) (isUpper : Bool) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then (Kupper k) else (Klower k))*T^εloss)
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℤ, ⌈M⌉ ≤ A → A ≤ Bint → Bint ≤ ⌊2*M⌋ →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A Bint,(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    eventually_positive_difference_triangular_selected_eight_grid_chunk_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y n N Qbase kmax Kmesh Usel R Jsep Vscale isUpper η M δ Bcut Bselect
    hK hNlink hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hregime
    hBcut hBselectSize hcutMargin hscaleTen hNsqM hNRM Q
    Cphys c J B Uband ChartCap NarrowCap Cap μ₀ U₀ C₂ C₃ Ct Cc
    Ccurv Kres Esize Dbase Tbase Lunit Gamma Cthird
    AupperConst BupperConst AlowerConst BlowerConst DupperConst DlowerConst
    Error f
    Δtype Δ D CostUpper CostLower Kupper Klower Buffer Width FamilyBound
    hchoice hsmall hNR hRN hNcube hsize hBsize hvalid hUmax hroom
    CtailBand ClowBand CerrorBand Density Endpoint A Bint hA hab hB
  have hn : 0 < n := by omega
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNp,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer0 : 0 ≤ Buffer 0 := by dsimp only [Buffer]; positivity
  have hWidth0 : 0 ≤ Width 0 := by dsimp only [Width]; positivity
  have hQbase : 768 ≤ Qbase := by
    obtain ⟨_,_,_,_,_,_,_,_,hstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hh : (768:ℝ) ≤ Q 0 := by nlinarith only [hstrong,hR]
    have hz : 768 ≤ Q 0 := by exact_mod_cast hh
    simpa only [Q,pow_zero,mul_one] using hz
  have hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M := by
    obtain ⟨_,_,_,_,_,_,hQN,_,_,_,_,_⟩ := hvalid kmax le_rfl
    have hh : (Q kmax:ℝ) ≤ N := by exact_mod_cast hQN
    calc
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ (N:ℝ)*(N:ℝ) :=
        mul_le_mul_of_nonneg_left hh hNp.le
      _ = (N:ℝ)^2 := by ring
      _ ≤ M := hNsqM
  obtain ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,
      hReduction⟩ :=
    positive_difference_subinterval_dyadic_band_reduction Y Fsrc n N Qbase kmax hNlink
      hσsrc hcsrc hUsrc hn hη (hηsmall.trans hηcap) hy hT hM hRp
      hreg hjets htests hnegative hscale hQbase hQmax hBuffer0 hWidth0 hroom
      A Bint hA hab hB
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let GridOf := fun (Dp : Finset (ℝ × ℤ)) (r : ℤ) =>
    (Dp.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let BandSum := fun k => ∑ p∈Selected k,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  let CoreSum := fun k Dp => ∑ r∈Finset.Ico (0:ℤ) 8,
    (2^11*((Csrc*Error)^12+
      (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (GridOf Dp r)))
  have hBufferMono k (hk : k ≤ kmax) : Buffer k ≤ Buffer 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hκ.le)
        (Nat.cast_nonneg _)) le_rfl) le_rfl
  have hWidthMono k (hk : k ≤ kmax) : Width k ≤ Width 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 14*σsrc/csrc)) (Nat.cast_nonneg _)
  have hchoose (k : ℕ) : ∃ Dp : Finset (ℝ × ℤ), k ≤ kmax →
      Dp ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
      Dp.card ≤ 2*(Selected k).card ∧
      (∀ r, (GridOf Dp r).card ≤ 2*(Selected k).card) ∧
      (∀ r, (GridOf Dp r).image Prod.fst ⊆ Y) ∧
      (BandSum k)^12 ≤ (4:ℝ)^12*(8:ℝ)^11*CoreSum k Dp := by
    by_cases hk : k ≤ kmax
    · obtain ⟨hUlarge,hsourceMesh,hmesh,hUref,hselectedWrap,hUupper,
        hQN,hUR,hstrongRQ,hminscale,hD,hΔ⟩ := hvalid k hk
      letI : NeZero (Kmesh k) := ⟨Nat.ne_of_gt (hK k)⟩
      have hSelY p (hp : p∈Selected k) : p.1∈Y := hphase p (Finset.mem_filter.mp hp).1
      have hSelDeep p (hp : p∈Selected k) :
          (n:ℝ)*p.2∈Icc (M+Buffer k+Width k+4*(N:ℝ))
            (2*M-Buffer k-Width k-(N:ℝ)) := by
        have hh := hdeep p (Finset.mem_filter.mp hp).1
        have hbuf := hBufferMono k hk
        have hwid := hWidthMono k hk
        constructor <;> linarith only [hh.1,hh.2,hbuf,hwid]
      have hSelAnchors p (hp : p∈Selected k) (i : Fin 2) :
          |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
            else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
          iteratedDeriv 2 (f p.1) (za p i)/2=(anchor p i:ℝ) ∧
          768*(anchor p i).den ≤ Q k ∧
          (24576*σsrc)*R^2 ≤ csrc*(Q k:ℝ)*(anchor p i).den := by
        obtain ⟨hpC,hpk⟩ := Finset.mem_filter.mp hp
        have hr := hroots p hpC i
        have hb := hbands p hpC
        rw [hpk] at hb
        exact ⟨hr.2.1,hr.1,(hb.2 i).1,(hb.2 i).2⟩
      obtain ⟨Dp,hDsub,hDcard,hGcard,hGphase,hBandBound⟩ :=
        hcoreT Fsrc Y (Q k) (Kmesh k) N (Usel k) R Jsep Vscale
          (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
          hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
          hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
          hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
          hUupper hscaleTen hQN hNsqM hUR hstrongRQ hNRM
          hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize isUpper hchoice
          n hNlink (Selected k) anchor za hSelY hSelDeep hSelAnchors
      have hPhaseY r : (GridOf Dp r).image Prod.fst ⊆ Y := by
        intro y hyGrid
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hGphase r hyGrid)
        exact hSelY p hp
      exact ⟨Dp,fun _ => ⟨hDsub,hDcard,hGcard,hPhaseY,hBandBound⟩⟩
    · exact ⟨∅,fun hh => (hk hh).elim⟩
  choose Dcover hDcover using hchoose
  refine ⟨Chunks,band,Dcover,hcardChunks,hcounts,htail,?_⟩
  intro SelectedOut Grid
  refine ⟨fun k hk => ⟨(hDcover k hk).1,(hDcover k hk).2.1,
    (hDcover k hk).2.2.1,(hDcover k hk).2.2.2.1⟩,?_⟩
  have hsum : (∑ k∈Finset.range (kmax+1),(BandSum k)^12) ≤
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),CoreSum k (Dcover k) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1), (4:ℝ)^12*(8:ℝ)^11*CoreSum k (Dcover k) :=
        Finset.sum_le_sum (fun k hk => (hDcover k (by
          have hh := Finset.mem_range.mp hk
          omega)).2.2.2.2)
      _ = _ := by rw [Finset.mul_sum]
  exact hReduction.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity))
      le_rfl) (by norm_num))

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep Vscale : ℝ) (isUpper : Bool) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then (Kupper k) else (Klower k))*T^εloss)
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℤ, ⌈M⌉ ≤ A → A ≤ Bint → Bint ≤ ⌊2*M⌋ →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc A Bint,(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_triangular_selected_band_subinterval_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget


#print axioms HuxleyBoundaryCoverScratch.eventually_positive_difference_triangular_selected_band_subinterval_physical_sieve
private theorem integer_phase_subinterval_trimmed_chunks {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ : ℤ} (A B : α → ℤ)
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : ∀ y∈Y, A₀ ≤ A y) (hB : ∀ y∈Y, B y ≤ B₀)
    (hab : ∀ y∈Y, A y ≤ B y)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc (A y) (B y), ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) := by
  classical
  intro Budget
  let Chunk := fun p : α × ℤ =>
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖
  have hex (y : α) : ∃ Cy : Finset (α × ℤ), y∈Y →
      Cy ⊆ {y} ×ˢ Finset.Ico a₀ b₀ ∧
      ‖∑ j∈Finset.Ioc (A y) (B y),v y j‖ ≤ (∑ p∈Cy,Chunk p)+(Budget:ℝ) := by
    by_cases hy : y∈Y
    · obtain ⟨Cy,hCy,hbound⟩ :=
        integer_subinterval_trimmed_chunks {y} v n hn ha₀ hb₀
          (hA y hy) (hB y hy) (hab y hy) (by
            intro z hz j hj
            have heq : z=y := Finset.mem_singleton.mp hz
            subst z
            exact hv y hy j hj)
      exact ⟨Cy,fun _ => ⟨hCy,by
        simpa only [Finset.sum_singleton,Finset.card_singleton,Nat.cast_one,one_mul]
          using hbound⟩⟩
    · exact ⟨∅,fun hh => (hy hh).elim⟩
  choose Cy hCy using hex
  have hphase y (hy : y∈Y) p (hp : p∈Cy y) : p.1=y :=
    Finset.mem_singleton.mp (Finset.mem_product.mp ((hCy y hy).1 hp)).1
  have hdisj : ∀ y∈Y, ∀ z∈Y, y≠z → Disjoint (Cy y) (Cy z) := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact hyz ((hphase y hy p hp).symm.trans (hphase z hz p hq))
  refine ⟨Y.biUnion Cy,?_,?_⟩
  · intro p hp
    obtain ⟨y,hy,hpy⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hfirst,hsecond⟩ := Finset.mem_product.mp ((hCy y hy).1 hpy)
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_singleton.mp hfirst).symm ▸ hy,hsecond⟩
  · have hh := Finset.sum_le_sum (fun y hy => (hCy y hy).2)
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
    rw [Finset.sum_biUnion hdisj]
    exact hh



private theorem positive_difference_phase_subinterval_dyadic_band_reduction
    (Y : Finset ℝ) (F : ℝ → ℝ) (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {σ c J η T M R Buffer Width : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hn : 0 < n) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase) (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M)
    (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(N:ℝ) ≤ M)
    (A B : ℝ → ℤ) (hA : ∀ y∈Y, ⌈M⌉ ≤ A y)
    (hab : ∀ y∈Y, A y ≤ B y) (hB : ∀ y∈Y, B y ≤ ⌊2*M⌋) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*((3072*σ)/c)^2+(3072*σ)/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σ*R^2/(c*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ))
    ∃ (Chunks : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, p.1∈Y) ∧
      (∀ p∈Chunks, (n:ℝ)*p.2∈
        Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ))) ∧
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            ∑ k∈Finset.range (kmax+1),
              (∑ p∈Chunks.filter (fun p => band p=some k),
                ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
                  (𝐞 (f p.1 j):ℂ)‖)^12)+Endpoint^12) := by
  classical
  intro f h probe Q Ctail Clow Cerror Density Endpoint
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hNreal : (N:ℝ)=8*(n:ℝ) := by exact_mod_cast hNlink
  have hNp : (0:ℝ) < N := by rw [hNreal]; positivity
  obtain ⟨a₀,b₀,ha₀,hab₀,hb₀,hdeep₀,hend₀⟩ :=
    eight_grid_endpoint_selection n hn hBuffer hWidth (by
      simpa only [←hNreal] using hroom)
  let v := fun y j : ℝ => (𝐞 (f y j):ℂ)
  obtain ⟨Chunks,hChunks,hwhole⟩ :=
    integer_phase_subinterval_trimmed_chunks Y (fun y j => v y j) n hn A B ha₀ hb₀ hA hB hab
      (fun _ _ _ _ => by simp [v])
  have hphase p (hp : p∈Chunks) : p.1∈Y := (Finset.mem_product.mp (hChunks hp)).1
  have hdeep p (hp : p∈Chunks) : (n:ℝ)*p.2∈
      Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ)) := by
    simpa only [←hNreal] using hdeep₀ p.2 (Finset.mem_product.mp (hChunks hp)).2
  have hpoints p (hp : p∈Chunks) i :
      probe p i∈Icc (M+(N:ℝ)/4) (2*M-(N:ℝ)/4) := by
    have hh := hdeep p hp
    dsimp only [probe]
    split_ifs <;> constructor <;> linarith only [hh.1,hh.2,hBuffer,hWidth,hNp]
  obtain ⟨anchor,band,za,hroots,hbands,hcounts,htail⟩ :=
    positive_difference_chunk_grid_dyadic_bands Chunks Y F n N Qbase kmax hNlink
      hσ hc hJ hn hη hηmax hy hphase hT hM hR hreg hbound htests hnegative
      hscale hQbase hQmax hpoints
  have hleft : M ≤ (n:ℝ)*a₀ :=
    (Int.le_ceil M).trans (by exact_mod_cast ha₀)
  have hright : (n:ℝ)*b₀ ≤ 2*M :=
    (by exact_mod_cast hb₀ : (n:ℝ)*b₀ ≤ (⌊2*M⌋:ℤ)).trans (Int.floor_le (2*M))
  have hcardI : ((Finset.Ico a₀ b₀).card:ℝ)=((b₀-a₀:ℤ):ℝ) := by
    exact_mod_cast (show ((Finset.Ico a₀ b₀).card:ℤ)=b₀-a₀ by
      rw [Int.card_Ico,Int.toNat_of_nonneg (sub_nonneg.mpr hab₀)])
  have hcardIle : ((Finset.Ico a₀ b₀).card:ℝ) ≤ 8*M/(N:ℝ) := by
    apply (le_div_iff₀ hNp).mpr
    rw [hcardI,hNreal]
    push_cast
    nlinarith only [hleft,hright]
  have hcardChunks : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) := by
    have hh : (Chunks.card:ℝ) ≤ (Y.card:ℝ)*((Finset.Ico a₀ b₀).card:ℝ) := by
      exact_mod_cast (show Chunks.card ≤ Y.card*(Finset.Ico a₀ b₀).card by
        simpa only [Finset.card_product] using Finset.card_le_card hChunks)
    exact hh.trans (mul_le_mul_of_nonneg_left hcardIle (Nat.cast_nonneg _))
  refine ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,?_⟩
  have hbudget :
      ((((n:ℤ)*a₀-⌈M⌉)+(⌊2*M⌋-(n:ℤ)*b₀)+2*(n:ℤ):ℤ):ℝ) ≤
        2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ) := by
    have hh := hend₀
    rw [←hNreal] at hh
    push_cast at hh ⊢
    linarith only [hh]
  let Mass := ∑ p∈Chunks,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  have hmass : 0 ≤ Mass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hEndpoint : 0 ≤ Endpoint := by dsimp only [Endpoint]; positivity
  have hwhole' : (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),(𝐞 (f y j):ℂ)‖) ≤ Mass+Endpoint :=
    hwhole.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)))
  have hbandMax p (hp : p∈Chunks) k (hk : band p=some k) : k ≤ kmax := by
    have hh := hbands p hp
    rw [hk] at hh
    exact hh.1
  have hpower := integer_chunk_dyadic_band_power Chunks (fun y j => v y j) n kmax band
    (fun _ _ => by simp [v]) hbandMax
  have htailLe : (n:ℝ)*((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
      (n:ℝ)*(Y.card:ℝ)*Density kmax := by
    have htail' : ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤
        (Y.card:ℝ)*Density kmax := htail
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail' hnp.le
  have hpower' : Mass^12 ≤ ((kmax:ℝ)+2)^11*
      (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
        ∑ k∈Finset.range (kmax+1),
          (∑ p∈Chunks.filter (fun p => band p=some k),
            ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖)^12) :=
    hpower.trans (mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (by positivity) htailLe 12) le_rfl) (by positivity))
  calc
    _ ≤ (Mass+Endpoint)^12 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hwhole' 12
    _ ≤ 2^11*(Mass^12+Endpoint^12) := add_pow_le hmass hEndpoint 12
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hpower' le_rfl) (by norm_num)


private theorem eventually_positive_difference_selected_band_phase_subinterval_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Vscale := fun k : ℕ =>
      let Uref := Usel k
      (Uref:ℝ)^((3:ℝ)/2)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := fun k : ℕ =>
      let Q := Q k
      2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*((Vscale k)*((Kupper k)+(Klower k))+(Klarge k))*T^εloss)
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    eventually_positive_difference_selected_eight_grid_chunk_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y n N Qbase kmax Kmesh Usel R Jsep η M δ Bcut Bselect
    hK hNlink hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hregime
    hBcut hBselectSize hcutMargin hscaleTen hNsqM hNRM Q
    Cphys c J B lambda Uband ChartCap NarrowCap Cap μ₀ U₀ C₂ C₃ Ct Cc
    Ccurv Kres Esize Dbase Tbase Lunit Gamma Cthird
    AupperConst BupperConst AlowerConst BlowerConst DupperConst DlowerConst
    Cpack Cfirst Cgap Cmain Ctail Error f
    Vscale Δtype Δ D CostUpper CostLower Kupper Klower Klarge Buffer Width FamilyBound
    hsmall hNR hRN hNcube hsize hBsize hvalid hUmax hroom
    CtailBand ClowBand CerrorBand Density Endpoint A Bint hA hab hB
  have hn : 0 < n := by omega
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNp,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer0 : 0 ≤ Buffer 0 := by dsimp only [Buffer]; positivity
  have hWidth0 : 0 ≤ Width 0 := by dsimp only [Width]; positivity
  have hQbase : 768 ≤ Qbase := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hh : (768:ℝ) ≤ Q 0 := by nlinarith only [hstrong,hR]
    have hz : 768 ≤ Q 0 := by exact_mod_cast hh
    simpa only [Q,pow_zero,mul_one] using hz
  have hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M := by
    obtain ⟨_,_,_,_,_,_,_,hQN,_,_,_,_,_⟩ := hvalid kmax le_rfl
    have hh : (Q kmax:ℝ) ≤ N := by exact_mod_cast hQN
    calc
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ (N:ℝ)*(N:ℝ) :=
        mul_le_mul_of_nonneg_left hh hNp.le
      _ = (N:ℝ)^2 := by ring
      _ ≤ M := hNsqM
  obtain ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,
      hReduction⟩ :=
    positive_difference_phase_subinterval_dyadic_band_reduction Y Fsrc n N Qbase kmax hNlink
      hσsrc hcsrc hUsrc hn hη (hηsmall.trans hηcap) hy hT hM hRp
      hreg hjets htests hnegative hscale hQbase hQmax hBuffer0 hWidth0 hroom
      A Bint hA hab hB
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let GridOf := fun (Dp : Finset (ℝ × ℤ)) (r : ℤ) =>
    (Dp.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let BandSum := fun k => ∑ p∈Selected k,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  let CoreSum := fun k Dp => ∑ r∈Finset.Ico (0:ℤ) 8,
    (2^11*((Csrc*Error)^12+
      (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (GridOf Dp r)))
  have hBufferMono k (hk : k ≤ kmax) : Buffer k ≤ Buffer 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hκ.le)
        (Nat.cast_nonneg _)) le_rfl) le_rfl
  have hWidthMono k (hk : k ≤ kmax) : Width k ≤ Width 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 14*σsrc/csrc)) (Nat.cast_nonneg _)
  have hchoose (k : ℕ) : ∃ Dp : Finset (ℝ × ℤ), k ≤ kmax →
      Dp ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
      Dp.card ≤ 2*(Selected k).card ∧
      (∀ r, (GridOf Dp r).card ≤ 2*(Selected k).card) ∧
      (∀ r, (GridOf Dp r).image Prod.fst ⊆ Y) ∧
      (BandSum k)^12 ≤ (4:ℝ)^12*(8:ℝ)^11*CoreSum k Dp := by
    by_cases hk : k ≤ kmax
    · obtain ⟨hUlarge,hsourceMesh,hmesh,hUref,hselectedWrap,hUupper,hUlower,
        hQN,hUR,hstrongRQ,hminscale,hD,hΔ⟩ := hvalid k hk
      letI : NeZero (Kmesh k) := ⟨Nat.ne_of_gt (hK k)⟩
      have hSelY p (hp : p∈Selected k) : p.1∈Y := hphase p (Finset.mem_filter.mp hp).1
      have hSelDeep p (hp : p∈Selected k) :
          (n:ℝ)*p.2∈Icc (M+Buffer k+Width k+4*(N:ℝ))
            (2*M-Buffer k-Width k-(N:ℝ)) := by
        have hh := hdeep p (Finset.mem_filter.mp hp).1
        have hbuf := hBufferMono k hk
        have hwid := hWidthMono k hk
        constructor <;> linarith only [hh.1,hh.2,hbuf,hwid]
      have hSelAnchors p (hp : p∈Selected k) (i : Fin 2) :
          |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
            else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
          iteratedDeriv 2 (f p.1) (za p i)/2=(anchor p i:ℝ) ∧
          768*(anchor p i).den ≤ Q k ∧
          (24576*σsrc)*R^2 ≤ csrc*(Q k:ℝ)*(anchor p i).den := by
        obtain ⟨hpC,hpk⟩ := Finset.mem_filter.mp hp
        have hr := hroots p hpC i
        have hb := hbands p hpC
        rw [hpk] at hb
        exact ⟨hr.2.1,hr.1,(hb.2 i).1,(hb.2 i).2⟩
      obtain ⟨Dp,hDsub,hDcard,hGcard,hGphase,hBandBound⟩ :=
        hcoreT Fsrc Y (Q k) (Kmesh k) N (Usel k) R Jsep
          (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
          hη hηsmall hT hNtwo hR hRM hδzero hδ hJsep hJM hy hsepY
          hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
          hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
          hUupper hUlower hscaleTen hQN hNsqM hUR hstrongRQ hNRM
          hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize
          n hNlink (Selected k) anchor za hSelY hSelDeep hSelAnchors
      have hPhaseY r : (GridOf Dp r).image Prod.fst ⊆ Y := by
        intro y hyGrid
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hGphase r hyGrid)
        exact hSelY p hp
      exact ⟨Dp,fun _ => ⟨hDsub,hDcard,hGcard,hPhaseY,hBandBound⟩⟩
    · exact ⟨∅,fun hh => (hk hh).elim⟩
  choose Dcover hDcover using hchoose
  refine ⟨Chunks,band,Dcover,hcardChunks,hcounts,htail,?_⟩
  intro SelectedOut Grid
  refine ⟨fun k hk => ⟨(hDcover k hk).1,(hDcover k hk).2.1,
    (hDcover k hk).2.2.1,(hDcover k hk).2.2.2.1⟩,?_⟩
  have hsum : (∑ k∈Finset.range (kmax+1),(BandSum k)^12) ≤
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),CoreSum k (Dcover k) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1), (4:ℝ)^12*(8:ℝ)^11*CoreSum k (Dcover k) :=
        Finset.sum_le_sum (fun k hk => (hDcover k (by
          have hh := Finset.mem_range.mp hk
          omega)).2.2.2.2)
      _ = _ := by rw [Finset.mul_sum]
  exact hReduction.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity))
      le_rfl) (by norm_num))


private theorem eventually_positive_difference_triangular_selected_band_phase_subinterval_physical_sieve
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep Vscale : ℝ) (isUpper : Bool) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then (Kupper k) else (Klower k))*T^εloss)
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) := by

  classical
  intro κ Ratio L
  obtain ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,hcore⟩ :=
    eventually_positive_difference_triangular_selected_eight_grid_chunk_physical_sieve
      hσsrc hcsrc hUsrc hσ hεloss hanchorBudget
  refine ⟨Csrc,η₀,a,Cupper,Clower,Dupper,Dlower,C,Dtype,
    hCsrc,hη₀,hηcap,ha,hCU,hCL,hDU,hDL,hC,hDtype,?_⟩
  intro θ hθ hθmax hθaction
  filter_upwards [hcore hθ hθmax hθaction] with T hcoreT
  intro Fsrc Y n N Qbase kmax Kmesh Usel R Jsep Vscale isUpper η M δ Bcut Bselect
    hK hNlink hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
    hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hregime
    hBcut hBselectSize hcutMargin hscaleTen hNsqM hNRM Q
    Cphys c J B Uband ChartCap NarrowCap Cap μ₀ U₀ C₂ C₃ Ct Cc
    Ccurv Kres Esize Dbase Tbase Lunit Gamma Cthird
    AupperConst BupperConst AlowerConst BlowerConst DupperConst DlowerConst
    Error f
    Δtype Δ D CostUpper CostLower Kupper Klower Buffer Width FamilyBound
    hchoice hsmall hNR hRN hNcube hsize hBsize hvalid hUmax hroom
    CtailBand ClowBand CerrorBand Density Endpoint A Bint hA hab hB
  have hn : 0 < n := by omega
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < M := by nlinarith only [hNp,hNsqM]
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hBuffer0 : 0 ≤ Buffer 0 := by dsimp only [Buffer]; positivity
  have hWidth0 : 0 ≤ Width 0 := by dsimp only [Width]; positivity
  have hQbase : 768 ≤ Qbase := by
    obtain ⟨_,_,_,_,_,_,_,_,hstrong,_,_,_⟩ := hvalid 0 (Nat.zero_le _)
    have hh : (768:ℝ) ≤ Q 0 := by nlinarith only [hstrong,hR]
    have hz : 768 ≤ Q 0 := by exact_mod_cast hh
    simpa only [Q,pow_zero,mul_one] using hz
  have hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M := by
    obtain ⟨_,_,_,_,_,_,hQN,_,_,_,_,_⟩ := hvalid kmax le_rfl
    have hh : (Q kmax:ℝ) ≤ N := by exact_mod_cast hQN
    calc
      (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ (N:ℝ)*(N:ℝ) :=
        mul_le_mul_of_nonneg_left hh hNp.le
      _ = (N:ℝ)^2 := by ring
      _ ≤ M := hNsqM
  obtain ⟨Chunks,anchor,band,za,hphase,hdeep,hcardChunks,hroots,hbands,hcounts,htail,
      hReduction⟩ :=
    positive_difference_phase_subinterval_dyadic_band_reduction Y Fsrc n N Qbase kmax hNlink
      hσsrc hcsrc hUsrc hn hη (hηsmall.trans hηcap) hy hT hM hRp
      hreg hjets htests hnegative hscale hQbase hQmax hBuffer0 hWidth0 hroom
      A Bint hA hab hB
  let Selected := fun k => Chunks.filter (fun p => band p=some k)
  let GridOf := fun (Dp : Finset (ℝ × ℤ)) (r : ℤ) =>
    (Dp.filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
  let BandSum := fun k => ∑ p∈Selected k,
    ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),(𝐞 (f p.1 j):ℂ)‖
  let CoreSum := fun k Dp => ∑ r∈Finset.Ico (0:ℤ) 8,
    (2^11*((Csrc*Error)^12+
      (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (GridOf Dp r)))
  have hBufferMono k (hk : k ≤ kmax) : Buffer k ≤ Buffer 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hκ.le)
        (Nat.cast_nonneg _)) le_rfl) le_rfl
  have hWidthMono k (hk : k ≤ kmax) : Width k ≤ Width 0 := by
    have hu : (Usel k:ℝ) ≤ Usel 0 := by exact_mod_cast hUmax k hk
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 14*σsrc/csrc)) (Nat.cast_nonneg _)
  have hchoose (k : ℕ) : ∃ Dp : Finset (ℝ × ℤ), k ≤ kmax →
      Dp ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
      Dp.card ≤ 2*(Selected k).card ∧
      (∀ r, (GridOf Dp r).card ≤ 2*(Selected k).card) ∧
      (∀ r, (GridOf Dp r).image Prod.fst ⊆ Y) ∧
      (BandSum k)^12 ≤ (4:ℝ)^12*(8:ℝ)^11*CoreSum k Dp := by
    by_cases hk : k ≤ kmax
    · obtain ⟨hUlarge,hsourceMesh,hmesh,hUref,hselectedWrap,hUupper,
        hQN,hUR,hstrongRQ,hminscale,hD,hΔ⟩ := hvalid k hk
      letI : NeZero (Kmesh k) := ⟨Nat.ne_of_gt (hK k)⟩
      have hSelY p (hp : p∈Selected k) : p.1∈Y := hphase p (Finset.mem_filter.mp hp).1
      have hSelDeep p (hp : p∈Selected k) :
          (n:ℝ)*p.2∈Icc (M+Buffer k+Width k+4*(N:ℝ))
            (2*M-Buffer k-Width k-(N:ℝ)) := by
        have hh := hdeep p (Finset.mem_filter.mp hp).1
        have hbuf := hBufferMono k hk
        have hwid := hWidthMono k hk
        constructor <;> linarith only [hh.1,hh.2,hbuf,hwid]
      have hSelAnchors p (hp : p∈Selected k) (i : Fin 2) :
          |za p i-(if i=0 then (n:ℝ)*p.2-2*(N:ℝ)
            else (n:ℝ)*p.2-11*(N:ℝ)/4)| ≤ (N:ℝ)/16 ∧
          iteratedDeriv 2 (f p.1) (za p i)/2=(anchor p i:ℝ) ∧
          768*(anchor p i).den ≤ Q k ∧
          (24576*σsrc)*R^2 ≤ csrc*(Q k:ℝ)*(anchor p i).den := by
        obtain ⟨hpC,hpk⟩ := Finset.mem_filter.mp hp
        have hr := hroots p hpC i
        have hb := hbands p hpC
        rw [hpk] at hb
        exact ⟨hr.2.1,hr.1,(hb.2 i).1,(hb.2 i).2⟩
      obtain ⟨Dp,hDsub,hDcard,hGcard,hGphase,hBandBound⟩ :=
        hcoreT Fsrc Y (Q k) (Kmesh k) N (Usel k) R Jsep Vscale
          (η:=η) (M:=M) (δ:=δ) (Bcut:=Bcut) (Bselect:=Bselect)
          hη hηsmall hT hNtwo hR hRM hVscale hδzero hδ hJsep hJM hy hsepY
          hreg hjets htests hnegative hmodels hscale hpad hquartic hquad hUlarge
          hsourceMesh hmesh hregime hUref hBcut hBselectSize hcutMargin hselectedWrap
          hUupper hscaleTen hQN hNsqM hUR hstrongRQ hNRM
          hsmall hNR hRN hNcube hminscale hsize hD hΔ hBsize isUpper hchoice
          n hNlink (Selected k) anchor za hSelY hSelDeep hSelAnchors
      have hPhaseY r : (GridOf Dp r).image Prod.fst ⊆ Y := by
        intro y hyGrid
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hGphase r hyGrid)
        exact hSelY p hp
      exact ⟨Dp,fun _ => ⟨hDsub,hDcard,hGcard,hPhaseY,hBandBound⟩⟩
    · exact ⟨∅,fun hh => (hk hh).elim⟩
  choose Dcover hDcover using hchoose
  refine ⟨Chunks,band,Dcover,hcardChunks,hcounts,htail,?_⟩
  intro SelectedOut Grid
  refine ⟨fun k hk => ⟨(hDcover k hk).1,(hDcover k hk).2.1,
    (hDcover k hk).2.2.1,(hDcover k hk).2.2.2.1⟩,?_⟩
  have hsum : (∑ k∈Finset.range (kmax+1),(BandSum k)^12) ≤
      (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),CoreSum k (Dcover k) := by
    calc
      _ ≤ ∑ k∈Finset.range (kmax+1), (4:ℝ)^12*(8:ℝ)^11*CoreSum k (Dcover k) :=
        Finset.sum_le_sum (fun k hk => (hDcover k (by
          have hh := Finset.mem_range.mp hk
          omega)).2.2.2.2)
      _ = _ := by rw [Finset.mul_sum]
  exact hReduction.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (by positivity))
      le_rfl) (by norm_num))


example {α : Type*}
    (Y : Finset α) (v : α → ℤ → ℂ) (n : ℕ) (hn : 0 < n)
    {A₀ B₀ a₀ b₀ : ℤ} (A B : α → ℤ)
    (ha₀ : A₀ ≤ (n:ℤ)*a₀) (hb₀ : (n:ℤ)*b₀ ≤ B₀)
    (hA : ∀ y∈Y, A₀ ≤ A y) (hB : ∀ y∈Y, B y ≤ B₀)
    (hab : ∀ y∈Y, A y ≤ B y)
    (hv : ∀ y∈Y, ∀ j∈Finset.Ioc (A y) (B y), ‖v y j‖ ≤ 1) :
    let Budget : ℤ := ((n:ℤ)*a₀-A₀)+(B₀-(n:ℤ)*b₀)+2*(n:ℤ)
    ∃ Chunks : Finset (α × ℤ), Chunks ⊆ Y ×ˢ Finset.Ico a₀ b₀ ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),v y j‖) ≤
        (∑ p∈Chunks, ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),v p.1 j‖)+
          (Y.card:ℝ)*(Budget:ℝ) :=
  HuxleyBoundaryCoverScratch.integer_phase_subinterval_trimmed_chunks (α:=α) Y v n hn (A₀:=A₀) (B₀:=B₀) (a₀:=a₀) (b₀:=b₀) A B ha₀ hb₀ hA hB hab hv

example
    (Y : Finset ℝ) (F : ℝ → ℝ) (n N Qbase kmax : ℕ) (hNlink : N=8*n)
    {σ c J η T M R Buffer Width : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hn : 0 < n) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : ∀ y∈Y, y∈Icc (1:ℝ) 2)
    (hT : 0 < T) (hM : 0 < M) (hR : 0 < R)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hscale : T*(N:ℝ)*R^2=M^3)
    (hQbase : 768 ≤ Qbase) (hQmax : (N:ℝ)*(Qbase*2^kmax:ℕ) ≤ M)
    (hBuffer : 0 ≤ Buffer) (hWidth : 0 ≤ Width)
    (hroom : 2*(Buffer+Width)+6*(N:ℝ) ≤ M)
    (A B : ℝ → ℤ) (hA : ∀ y∈Y, ⌈M⌉ ≤ A y)
    (hab : ∀ y∈Y, A y ≤ B y) (hB : ∀ y∈Y, B y ≤ ⌊2*M⌋) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let probe := fun (p : ℝ × ℤ) (i : Fin 2) =>
      if i=0 then (n:ℝ)*p.2-2*(N:ℝ) else (n:ℝ)*p.2-11*(N:ℝ)/4
    let Q := fun k : ℕ => Qbase*2^k
    let Ctail := (6*J/σ)*(64*σ/c)^2+192*σ/c
    let Clow := (3*J/σ+c/(32*σ))*((3072*σ)/c)^2+(3072*σ)/c
    let Cerror := (768:ℝ)^2*Ctail+Clow
    let Density := fun k => 128*Cerror*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σ*R^2/(c*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer+2*Width+6*(N:ℝ)+2*(n:ℝ))
    ∃ (Chunks : Finset (ℝ × ℤ)) (anchor : (ℝ × ℤ) → Fin 2 → ℚ)
      (band : (ℝ × ℤ) → Option ℕ) (za : (ℝ × ℤ) → Fin 2 → ℝ),
      (∀ p∈Chunks, p.1∈Y) ∧
      (∀ p∈Chunks, (n:ℝ)*p.2∈
        Icc (M+Buffer+Width+4*(N:ℝ)) (2*M-Buffer-Width-(N:ℝ))) ∧
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ p∈Chunks, ∀ i,
        h p.1 (za p i)=(anchor p i:ℝ) ∧
        |za p i-probe p i| ≤ (N:ℝ)/16 ∧ za p i∈Icc M (2*M)) ∧
      (∀ p∈Chunks, match band p with
        | none => ∃ i, ¬(768*(anchor p i).den ≤ Q kmax ∧
            (24576*σ)*R^2 ≤ c*(Q kmax:ℝ)*(anchor p i).den)
        | some k => k ≤ kmax ∧
            (∀ i, 768*(anchor p i).den ≤ Q k ∧
              (24576*σ)*R^2 ≤ c*(Q k:ℝ)*(anchor p i).den)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (B y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            ∑ k∈Finset.range (kmax+1),
              (∑ p∈Chunks.filter (fun p => band p=some k),
                ‖∑ j∈Finset.Ioc ((n:ℤ)*p.2) ((n:ℤ)*(p.2+1)),
                  (𝐞 (f p.1 j):ℂ)‖)^12)+Endpoint^12) :=
  HuxleyBoundaryCoverScratch.positive_difference_phase_subinterval_dyadic_band_reduction Y F n N Qbase kmax hNlink (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (R:=R) (Buffer:=Buffer) (Width:=Width) hσ hc hJ hn hη hηmax hy hT hM hR hreg hbound htests hnegative hscale hQbase hQmax hBuffer hWidth hroom A B hA hab hB

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep : ℝ) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Vscale := fun k : ℕ =>
      let Uref := Usel k
      (Uref:ℝ)^((3:ℝ)/2)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Klarge := fun k : ℕ =>
      let Q := Q k
      2*Bselect*60*588*(Uband/lambda)^2*Uband^2*(R^8/(N:ℝ)^4)*
        (Cmain+Ctail)*((Q:ℝ)/(N:ℝ))^((2:ℝ)/3)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            ((Vscale k)*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*((Vscale k)*((Kupper k)+(Klower k))+(Klarge k))*T^εloss)
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/(2*Bselect) ≤ (Usel k:ℝ) ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_selected_band_phase_subinterval_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget

example
    {σsrc csrc Usrc σ εloss : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hσ : 0 < σ) (hεloss : 0 < εloss)
    (hanchorBudget : csrc ≤ 4*modelPhaseThirdLower σ*σsrc/(σ*(σ+1)+3)) :
    let κ := modelPhaseThirdLower σ
    let Ratio := 18*Usrc^2/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)/κ^2)
    ∃ Csrc η₀ a Cupper Clower Dupper Dlower C Dtype : ℝ,
      1 ≤ Csrc ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      0 < Cupper ∧ 0 < Clower ∧ 0 < Dupper ∧ 0 < Dlower ∧ 0 < C ∧ 0 < Dtype ∧
    ∀ {θ : ℝ}, 0 < θ → θ ≤ 1/24 → θ ≤ 1/(8*(L+3)) →
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (Fsrc : ℝ → ℝ) (Y : Finset ℝ)
      (n N Qbase kmax : ℕ) (Kmesh Usel : ℕ → ℕ)
      (R Jsep Vscale : ℝ) (isUpper : Bool) {η M δ Bcut Bselect : ℝ},
    (∀ k, 0 < Kmesh k) → N=8*n →
    0 < η → η ≤ η₀ → 0 < T → 2 ≤ N →
    1 ≤ R → R ≤ M → 1 ≤ Vscale → 0 ≤ δ → δ ≤ min κ 1 →
    0 < Jsep → Jsep ≤ M →
    (∀ y∈Y, y∈Icc (1:ℝ) 2) →
    (∀ y∈Y, ∀ z∈Y, y≠z → 1 ≤ Jsep*|y-z|) →
    (∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j ≤ 6, |iteratedDeriv (j+1) Fsrc w| ≤ Usrc) →
    (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) →
    (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 Fsrc w ≤ -csrc) →
    (∀ y∈Y, Expdb.IsApproximateModelPhaseFunction
      (fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)) σ 4 δ) →
    T*(N:ℝ)*R^2=M^3 →
    7*(N:ℝ)+2 ≤ M/4 →
    (3*Usrc/σsrc)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
    (3*Usrc/(4*σsrc))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
    (N:ℝ)^4 ≤ M*R^3*(Real.log T)^((3:ℝ)/2) →
    0 < Bcut → 2+168/κ ≤ Bselect → 7*Bcut ≤ κ*Bselect →
    (N:ℝ)^10 ≤ M^3*R^7 → (N:ℝ)^2 ≤ M → (N:ℝ)*R ≤ M →
    let Q := fun k : ℕ => Qbase*2^k
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let Uband := (3*Usrc/σsrc)*T/(2*M^2)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2/(σsrc*csrc*κ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    let μ₀ := csrc*T/(12*σsrc*M^3)
    let U₀ := Usrc*T/(2*σsrc*M^3)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let AupperConst := 2*Cupper*(Cthird+1)*1^2/(κ*Lunit^3)
    let BupperConst := Cupper*(Cthird+1)*1^2/Lunit^2+Dupper*(B+1)*1^2/4
    let AlowerConst := 8*Clower*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*Clower*(Cthird+1)/Lunit^2+Dlower*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*1/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    let Error := (Y.card:ℝ)*(M/(N:ℝ)+1)*
      (Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+12*σsrc*R^2/(csrc*(N:ℝ)))
    let f := fun y w => T*(Fsrc (w/M)-Fsrc (w/M+η*y))/(σsrc*η)
    let Δtype := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
    let Δ := fun k : ℕ =>
      let Q := Q k
      (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/(N:ℝ)
    let D := fun k : ℕ =>
      let Q := Q k
      (Δ k)+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/(N:ℝ)
    let CostUpper := fun k : ℕ =>
      let Uref := Usel k
      M^2/((N:ℝ)^4*(Uref:ℝ))
    let CostLower := fun k : ℕ =>
      let Uref := Usel k
      R^4/((N:ℝ)^2*(Uref:ℝ))
    let Kupper := fun k : ℕ =>
      240*(CostUpper k)*
        (9*(AupperConst*DupperConst^2)^((3:ℝ)⁻¹)+2*BupperConst+(3/2:ℝ)*DupperConst)
    let Klower := fun k : ℕ =>
      240*(CostLower k)*
        (9*(AlowerConst*DlowerConst^2)^((3:ℝ)⁻¹)+2*BlowerConst+(3/2:ℝ)*DlowerConst)
    let Buffer := fun k : ℕ =>
      let Uref := Usel k
      (56*(Uref:ℝ)/κ)*(N:ℝ)+(N:ℝ)/(Cphys+2)+2
    let Width := fun k : ℕ => (14*σsrc/csrc)*(Usel k:ℝ)*(N:ℝ)
    let FamilyBound := fun k : ℕ =>
      let Q := Q k
      let K₀ := Kmesh k
      fun (P : Finset (ℝ × ℤ)) =>
        (48*σsrc/csrc)^6*(R^2/(Q:ℝ))^6*
          C*(K₀:ℝ)^((12:ℝ)+εloss)*Cap^11*(2*(P.card:ℝ))^10*
            (Vscale*Dtype*((P.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+(Δtype k)*Jsep)+
              ((P.image Prod.fst).card:ℝ)^2*Vscale*(if isUpper then (Kupper k) else (Klower k))*T^εloss)
    (if isUpper then Vscale=1+R^4/(6*(N:ℝ)^2)
      else Uband ≤ 1/16 ∧ Vscale=1+R^4*Uband^2/(N:ℝ)^2) →
    B*R^2/(N:ℝ)^2 ≤ 1/2 →
    (N:ℝ) ≤ R^2 → R ≤ (N:ℝ) → (N:ℝ)^3 ≤ M*R^2 →
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    61*Ccurv*Cphys ≤ Bcut →
    (∀ k ≤ kmax,
      12*Usrc ≤ σsrc*(Usel k:ℝ) ∧
      63*(Usrc/(2*σsrc*(N:ℝ)*R^2))*(Q k:ℝ)*(N:ℝ)^2 ≤ Kmesh k ∧
      (Q k:ℝ)*(N:ℝ) ≤ (Kmesh k:ℝ)*R^2 ∧
      1 ≤ Usel k ∧
      Bselect^2*(Usel k:ℝ)^3*R^2 ≤ (N:ℝ)^2 ∧
      (Usel k:ℝ) ≤ ((N:ℝ)/(Q k:ℝ))^((2:ℝ)/3)/Bselect ∧
      Q k ≤ N ∧ (Usel k:ℝ) ≤ R^2 ∧
      768*R ≤ (Q k:ℝ) ∧ 2*R^2 ≤ (Q k:ℝ)*(N:ℝ) ∧
      D k ≤ 1/2 ∧ Δ k < 1/2) →
    (∀ k ≤ kmax, Usel k ≤ Usel 0) →
    2*(Buffer 0+Width 0)+6*(N:ℝ) ≤ M →
    let CtailBand := (6*Usrc/σsrc)*(64*σsrc/csrc)^2+192*σsrc/csrc
    let ClowBand := (3*Usrc/σsrc+csrc/(32*σsrc))*((3072*σsrc)/csrc)^2+(3072*σsrc)/csrc
    let CerrorBand := (768:ℝ)^2*CtailBand+ClowBand
    let Density := fun k => 128*CerrorBand*(M*R^2/((N:ℝ)*(Q k:ℝ)^2))*
      (2+Real.log (512*σsrc*R^2/(csrc*((Q k:ℝ)/768))+1))
    let Endpoint := (Y.card:ℝ)*(2*Buffer 0+2*Width 0+6*(N:ℝ)+2*(n:ℝ))
    ∀ A Bint : ℝ → ℤ, (∀ y∈Y, ⌈M⌉ ≤ A y) →
    (∀ y∈Y, A y ≤ Bint y) → (∀ y∈Y, Bint y ≤ ⌊2*M⌋) →
    ∃ (Chunks : Finset (ℝ × ℤ)) (band : (ℝ × ℤ) → Option ℕ)
      (Dcover : ℕ → Finset (ℝ × ℤ)),
      (Chunks.card:ℝ) ≤ (Y.card:ℝ)*(8*M/(N:ℝ)) ∧
      (∀ k ≤ kmax, ((Chunks.filter (fun p => band p=some (k+1))).card:ℝ) ≤
        (Y.card:ℝ)*Density k) ∧
      ((Chunks.filter (fun p => band p=none)).card:ℝ) ≤ (Y.card:ℝ)*Density kmax ∧
      let Selected := fun k => Chunks.filter (fun p => band p=some k)
      let Grid := fun (k : ℕ) (r : ℤ) =>
        ((Dcover k).filter (fun p => p.2%8=r)).image (fun p => (p.1,p.2/8-2))
      (∀ k ≤ kmax,
        Dcover k ⊆ Selected k ∪ (Selected k).image (fun p => (p.1,p.2-6)) ∧
        (Dcover k).card ≤ 2*(Selected k).card ∧
        (∀ r, (Grid k r).card ≤ 2*(Selected k).card) ∧
        (∀ r, (Grid k r).image Prod.fst ⊆ Y)) ∧
      (∑ y∈Y, ‖∑ j∈Finset.Ioc (A y) (Bint y),(𝐞 (f y j):ℂ)‖)^12 ≤
        2^11*(((kmax:ℝ)+2)^11*
          (((n:ℝ)*(Y.card:ℝ)*Density kmax)^12+
            (4:ℝ)^12*(8:ℝ)^11*∑ k∈Finset.range (kmax+1),
              ∑ r∈Finset.Ico (0:ℤ) 8,
                (2^11*((Csrc*Error)^12+
                  (Csrc*(1+Real.log (Kmesh k)))^12*FamilyBound k (Grid k r))))+
            Endpoint^12) :=
  HuxleyBoundaryCoverScratch.eventually_positive_difference_triangular_selected_band_phase_subinterval_physical_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hσ hεloss hanchorBudget

#print axioms HuxleyBoundaryCoverScratch.integer_phase_subinterval_trimmed_chunks
#print axioms HuxleyBoundaryCoverScratch.positive_difference_phase_subinterval_dyadic_band_reduction
#print axioms HuxleyBoundaryCoverScratch.eventually_positive_difference_selected_band_phase_subinterval_physical_sieve
#print axioms HuxleyBoundaryCoverScratch.eventually_positive_difference_triangular_selected_band_phase_subinterval_physical_sieve

end HuxleyBoundaryCoverScratch
#print axioms HuxleyBoundaryCoverScratch.two_probes_avoid_separated_set
#print axioms HuxleyBoundaryCoverScratch.positive_difference_two_safe_block_starts
#print axioms HuxleyBoundaryCoverScratch.coarse_boundary_exponent_floor

#print axioms HuxleyBoundaryCoverScratch.finite_reference_safe_start_buffered_bracket

#print axioms HuxleyBoundaryCoverScratch.positive_difference_two_buffered_block_starts

#print axioms HuxleyBoundaryCoverScratch.finite_prefix_maximizers
#print axioms HuxleyBoundaryCoverScratch.integer_subinterval_le_two_prefixes
#print axioms HuxleyBoundaryCoverScratch.two_start_chunk_cover

#print axioms HuxleyBoundaryCoverScratch.eight_grid_sum_reindex

#print axioms HuxleyBoundaryCoverScratch.integer_chunk_partition
#print axioms HuxleyBoundaryCoverScratch.integer_whole_sum_le_chunks_and_endpoints

#print axioms HuxleyBoundaryCoverScratch.positive_difference_eight_grid_chunk_cover

#print axioms HuxleyBoundaryCoverScratch.eight_grid_endpoint_selection

#print axioms HuxleyBoundaryCoverScratch.direct_monomial_majorant_floor
#print axioms HuxleyBoundaryCoverScratch.direct_monomial_majorant_misses_third_row

#print axioms HuxleyBoundaryCoverScratch.positive_difference_actual_anchor_family_band_card

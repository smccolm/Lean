import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical

namespace HuxleyAnchorComplementScratch

private theorem bourgain_bounded_denominator_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (r : ι → ℚ)
    (Q B : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (hlevel : ∀ i∈S, |(r i:ℝ)| ≤ X)
    (hden : ∀ i∈S, (r i).den ≤ Q)
    (hmul : ∀ a : ℚ, (S.filter (fun i => r i=a)).card ≤ B) :
    (S.card:ℝ) ≤ B*(Q:ℝ)*(2*X*Q+1) := by
  classical
  have hnum i (hi : i∈S) : |((r i).num:ℝ)| ≤ X*Q := by
    have hd : (0:ℝ) < (r i).den := Nat.cast_pos.mpr (r i).pos
    have hv := hlevel i hi
    rw [Rat.cast_def,abs_div,abs_of_pos hd] at hv
    exact ((div_le_iff₀ hd).mp hv).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hden i hi)) hX)
  have hfiber (q : ℕ) :
      ((S.filter (fun i => (r i).den=q)).card:ℝ) ≤ (2*X*Q+1)*B := by
    let T := S.filter (fun i => (r i).den=q)
    let W := T.image (fun i => (r i).num)
    have hW : (W.card:ℝ) ≤ 2*X*Q+1 := by
      have hh := integer_card_le_of_abs_sub_le W (a:=0) (B:=X*Q)
        (by positivity) (by
          intro p hp
          obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
          simpa only [sub_zero] using hnum i (Finset.mem_filter.mp hi).1)
      convert hh using 1
      ring
    have hpcount p : (T.filter (fun i => (r i).num=p)).card ≤ B := by
      apply (Finset.card_le_card (show T.filter (fun i => (r i).num=p) ⊆
        S.filter (fun i => r i=(p:ℚ)/q) from ?_)).trans (hmul ((p:ℚ)/q))
      intro i hi
      obtain ⟨hiT,hn⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiS,hd⟩ := Finset.mem_filter.mp hiT
      refine Finset.mem_filter.mpr ⟨hiS,?_⟩
      rw [←Rat.num_div_den (r i),hn,hd]
    calc
      _ = ∑ p∈W,((T.filter (fun i => (r i).num=p)).card:ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image (fun i => (r i).num) T
      _ ≤ ∑ _p∈W,(B:ℝ) := Finset.sum_le_sum (fun p _ => Nat.cast_le.mpr (hpcount p))
      _ = (W.card:ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hW (Nat.cast_nonneg B)
  have hcard : S.card=∑ q∈Finset.Icc 1 Q,(S.filter (fun i => (r i).den=q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi =>
      Finset.mem_Icc.mpr ⟨(r i).pos,hden i hi⟩)
  calc
    _ = ∑ q∈Finset.Icc 1 Q,((S.filter (fun i => (r i).den=q)).card:ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _q∈Finset.Icc 1 Q,(2*X*Q+1)*(B:ℝ) := Finset.sum_le_sum (fun q _ => hfiber q)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
      ring


private theorem positive_difference_near_anchor_injective
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    (∀ i∈S, |(anchor i:ℝ)-h (t i)| ≤ c/(64*σ*R^2)) →
    Set.InjOn anchor (S : Set ℤ) := by
  intro f h t hnear i hi j hj he
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hcurv : |h (t i)-h (t j)| ≤ 7*(c/(112*σ))/(2*R^2) := by
    calc
      _ = |(h (t i)-(anchor i:ℝ))+((anchor j:ℝ)-h (t j))| := by rw [he]; congr 1; ring
      _ ≤ |h (t i)-(anchor i:ℝ)|+|(anchor j:ℝ)-h (t j)| := abs_add_le _ _
      _ ≤ c/(64*σ*R^2)+c/(64*σ*R^2) := by
        rw [abs_sub_comm (h (t i)) (anchor i:ℝ)]
        exact add_le_add (hnear i hi) (hnear j hj)
      _ = _ := by ring
  have hwidth := positive_difference_reference_preimage_width F
    hσ hc hη hηmax hy hf hnegative hT hM hNp hR hphase
    (hpoints i hi) (hpoints j hj) (by simpa only [abs_sub_comm] using hcurv)
  have hw : |t j-t i| ≤ (N:ℝ)/8 := by
    convert hwidth using 1
    field_simp
    ring
  have heq : |t j-t i|=(N:ℝ)*|((j-i:ℤ):ℝ)| := by
    rw [←abs_of_pos hNp,←abs_mul]
    congr 1
    dsimp only [t]
    push_cast
    ring
  rw [heq] at hw
  have hdiff : |((j-i:ℤ):ℝ)| < 1 := by nlinarith only [hw,hNp]
  have hz : j-i=0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hdiff)
  exact (sub_eq_zero.mp hz).symm


/-- Both failures of the source anchor regime have derived counts.
The supplied anchors are actual minimum-denominator witnesses; their
denominators are identified with the existing sparse-tail construction.
Neither a complement-cardinality nor a rational-fiber bound is assumed. -/
theorem positive_difference_minimal_anchor_complement_count
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hNM : (N:ℝ) ≤ M) (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈S, (anchor i:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) → (anchor i).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
    let Cost := 4*(Vbound+1)*Dhigh^2+Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(Vbound+delta)*Dlow+1)
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost := by
  classical
  intro f h t delta Vbound hanchors Q Acut Bmajor hAcut hAQ hBmajor
    Bad Dlow Khigh Dhigh Cost
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQ : 0 < Q := by omega
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hApos : 0 < Acut := by omega
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hV : 0 ≤ Vbound := by dsimp only [Vbound]; positivity
  have hDlow : 0 ≤ Dlow := by dsimp only [Dlow]; positivity
  have hnear i (hi : i∈S) : |(anchor i:ℝ)-h (t i)| ≤ delta := by
    have hh := (hanchors i hi).1
    exact abs_le.mpr ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  have hinj := positive_difference_near_anchor_injective S F anchor N s
    hσ hc hη hηmax hy hf hnegative hT hM hN hR hphase hpoints hnear
  have hmul n : (S.filter (fun i => id i=n)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ((Finset.mem_filter.mp hi).2).trans ((Finset.mem_filter.mp hj).2).symm
  have hc4 : 0 < c/4 := by positivity
  have hneg4 w (hw : w∈Icc (1/2:ℝ) 3) : iteratedDeriv 4 F w ≤ -(c/4) := by
    linarith only [hnegative w hw,hc]
  obtain ⟨aNew,zNew,hNew,_hLocal,hTail⟩ :=
    positive_difference_minimal_curvature_arc_count S F id N 1 s
      hσ hc4 hJ hη hηmax hy hf hbound hneg4 hT hM hN hR hNM hphase hmul hpoints
  have heps : (c/4)/(16*σ*R^2)=delta := by dsimp only [delta]; ring
  rw [heps] at hNew
  have hdeneq i (hi : i∈S) : (anchor i).den=(aNew i).den := by
    exact Nat.le_antisymm
      ((hanchors i hi).2 (aNew i) (hNew i hi).2.2.1)
      ((hNew i hi).2.2.2 (anchor i) (hanchors i hi).1)
  have hK : 2 ≤ Khigh := by
    have hh : 1 ≤ Q/Acut := (Nat.le_div_iff_mul_le hApos).mpr (by simpa only [one_mul] using hAQ)
    dsimp only [Khigh]
    omega
  let High := S.filter (fun i => Khigh ≤ (anchor i).den)
  have hhigh : (High.card:ℝ) ≤ 4*(Vbound+1)*Dhigh^2+Dhigh*(2+Real.log (Dhigh+1)) := by
    have he : High=S.filter (fun i => Khigh ≤ (aNew i).den) :=
      Finset.filter_congr (fun i hi => by rw [hdeneq i hi])
    rw [he]
    have hh := hTail Khigh hK
    have hd : 16*σ*R^2/((c/4)*(Khigh:ℝ))=Dhigh := by dsimp only [Dhigh]; ring
    simpa only [hd,Nat.cast_one,one_mul] using hh
  have hscale2 : T/M^2=M/((N:ℝ)*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hphase]
  have hvalues i (hi : i∈S) : |(anchor i:ℝ)| ≤ Vbound+delta := by
    have hh := (positive_difference_half_curvature_source_bounds F
      hσ hc hJ hη hηmax hT hM hy (hpoints i hi) hf hbound htests).2
    have he : (3*J/σ)*T/(2*M^2)=Vbound := by
      calc
        _ = (3*J/(2*σ))*(T/M^2) := by ring
        _ = Vbound := by rw [hscale2]; dsimp only [Vbound]; ring
    rw [he] at hh
    calc
      |(anchor i:ℝ)| = |((anchor i:ℝ)-h (t i))+h (t i)| := by rw [sub_add_cancel]
      _ ≤ |(anchor i:ℝ)-h (t i)|+|h (t i)| := abs_add_le _ _
      _ ≤ delta+Vbound := add_le_add (hnear i hi) hh
      _ = Vbound+delta := by ring
  let Low := S.filter (fun i => c*(Q:ℝ)*(anchor i).den < Bmajor*R^2)
  have hlowden i (hi : i∈Low) : (anchor i).den ≤ ⌊Dlow⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ (mul_pos hc hQr)).mpr
    have hh := (Finset.mem_filter.mp hi).2
    nlinarith only [hh]
  have hlow : (Low.card:ℝ) ≤ Dlow*(2*(Vbound+delta)*Dlow+1) := by
    have hcount := bourgain_bounded_denominator_count Low anchor ⌊Dlow⌋₊ 1
      (add_nonneg hV hdelta.le) (fun i hi => hvalues i (Finset.mem_filter.mp hi).1) hlowden
      (by
        intro a
        apply Finset.card_le_one.mpr
        intro i hi j hj
        obtain ⟨hiL,hia⟩ := Finset.mem_filter.mp hi
        obtain ⟨hjL,hja⟩ := Finset.mem_filter.mp hj
        exact hinj (Finset.mem_filter.mp hiL).1 (Finset.mem_filter.mp hjL).1 (hia.trans hja.symm))
    simp only [Nat.cast_one,one_mul] at hcount
    apply hcount.trans
    have hfloor : (⌊Dlow⌋₊:ℝ) ≤ Dlow := Nat.floor_le hDlow
    gcongr
  have hsub : Bad⊆High∪Low := by
    intro i hi
    obtain ⟨hiS,hbad⟩ := Finset.mem_filter.mp hi
    rcases not_and_or.mp hbad with hlarge | hsmall
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hiS,?_⟩
      have hh : Q/Acut < (anchor i).den :=
        (Nat.div_lt_iff_lt_mul hApos).mpr (by simpa only [mul_comm] using lt_of_not_ge hlarge)
      exact Nat.succ_le_of_lt hh
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiS,lt_of_not_ge hsmall⟩)
  have hcard : (Bad.card:ℝ) ≤ Cost := by
    have hh : (Bad.card:ℝ) ≤ (High.card:ℝ)+(Low.card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact hh.trans (add_le_add hhigh hlow)
  refine ⟨hcard,?_⟩
  intro H hH
  calc
    (∑ i∈Bad,(H i:ℝ)) ≤ ∑ _i∈Bad,(N:ℝ) := Finset.sum_le_sum (fun i hi =>
      Nat.cast_le.mpr (hH i (Finset.mem_filter.mp hi).1))
    _ = (N:ℝ)*(Bad.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ (N:ℝ)*Cost := mul_le_mul_of_nonneg_left hcard hNp.le

/-- The original interior-gap Fourier witnesses now carry a derived,
explicit bound for the entire rejected-anchor contribution. The source
sum, rational roots and single common Fourier mode are unchanged. -/
theorem positive_difference_interior_gap_controlled_complement_fourier
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (N : ℕ) (s : ℤ) (H : ℤ → ℕ)
      (η y T M R U x₁ x₂ : ℝ),
      1 ≤ N → (∀ k, H k ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U → x₁∈Icc M (2*M) → x₂∈Icc M (2*M) →
      let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun w => iteratedDeriv 2 f w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      U/(4*R^2) ≤ h x₂-h x₁ → h x₂-h x₁ ≤ 7*U/(2*R^2) →
      ∃ S : Finset ℤ, ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
        (∀ k : ℤ, k∈S ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈S, za k∈Ioo x₁ x₂ ∧ h (za k)=(anchor k:ℝ) ∧
          (anchor k:ℝ)∈Ioo (h x₁) (h x₂) ∧
          (anchor k:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) → (anchor k).den ≤ a.den) ∧
        (∀ k∈S, |za k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          ((S.filter (fun k => Q ≤ (anchor k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      let Dlow := 128*σ*R^2/(c*(Q:ℝ))
      let Khigh := Q/2+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Cost := 4*(Vbound+1)*Dhigh^2+Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ((S.filter (fun i => ¬ Good i)).card:ℝ) ≤ Cost ∧
      ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 f (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo x₁ x₂) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 f (m i)/6
      let ℓ := fun i => deriv f (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
          C*((N:ℝ)*Cost+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) := by
  classical
  obtain ⟨C,hC,hentry⟩ := positive_difference_interior_gap_dyadic_source_fourier hσ hc hJ
  refine ⟨C,hC,?_⟩
  intro F N s H η y T M R U x₁ x₂ hN hH hη hηmax hy hT hM hR hU
    hf hbound htests hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
    f h t L delta Vbound hgaplow hgapup
  obtain ⟨S,anchor,za,hmem,hdata,hdist,hcardlow,hcardup,htail,hfourier⟩ :=
    hentry F N s H η y T M R U x₁ x₂ hN hH hη hηmax hy hT hM hR hU
      hf hbound hnegative hphase hbuffer hfourBudget hquadBudget hUlarge hx₁ hx₂
      hgaplow hgapup
  refine ⟨S,anchor,za,hmem,hdata,hdist,hcardlow,hcardup,htail,?_⟩
  intro Q hQ hQN Good G Dlow Khigh Dhigh Cost
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNM : (N:ℝ) ≤ M := by linarith only [hbuffer,hNp]
  have hpoints i (hi : i∈S) : t i∈Icc M (2*M) := by
    have hh := (hmem i).mp hi
    constructor <;> linarith only [hh.1,hh.2,hx₁.1,hx₂.2,hNp]
  have hanchors i (hi : i∈S) := (hdata i hi).2.2.2
  have hb := positive_difference_minimal_anchor_complement_count S F anchor N (s:ℝ)
    hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM
    (show 0 < N by omega) hR hNM hphase hpoints hanchors
    Q 2 (128*σ) (by norm_num) hQ (by positivity)
  obtain ⟨r,z,hr,hzg,hcenter,hcompletion⟩ := hfourier Q hQN
  refine ⟨hb.1,r,z,hr,hzg,hcenter,?_⟩
  dsimp only
  intro K₀ _ hK₀
  obtain ⟨v,hv,k,hfour⟩ := hcompletion K₀ hK₀
  refine ⟨v,hv,k,hfour.trans ?_⟩
  have hweight := hb.2 H (fun i _ => hH i)
  gcongr

example
    (S : Finset ℤ) (F : ℝ → ℝ) (anchor : ℤ → ℚ)
    (N : ℕ) (s : ℝ) {σ c J η y T M R : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hNM : (N:ℝ) ≤ M) (hphase : T*(N:ℝ)*R^2=M^3)
    (hpoints : ∀ i∈S, s+(N:ℝ)*i∈Icc M (2*M)) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun w => iteratedDeriv 2 f w/2
    let t := fun i : ℤ => s+(N:ℝ)*i
    let delta := c/(64*σ*R^2)
    let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
    (∀ i∈S, (anchor i:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) ∧
      ∀ a : ℚ, (a:ℝ)∈Ioo (h (t i)-delta) (h (t i)+delta) → (anchor i).den ≤ a.den) →
    ∀ (Q Acut : ℕ) (Bmajor : ℝ), 2 ≤ Acut → Acut ≤ Q → 0 ≤ Bmajor →
    let Bad := S.filter (fun i => ¬ (Acut*(anchor i).den ≤ Q ∧
      Bmajor*R^2 ≤ c*(Q:ℝ)*(anchor i).den))
    let Dlow := Bmajor*R^2/(c*(Q:ℝ))
    let Khigh := Q/Acut+1
    let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
    let Cost := 4*(Vbound+1)*Dhigh^2+Dhigh*(2+Real.log (Dhigh+1))+
      Dlow*(2*(Vbound+delta)*Dlow+1)
    (Bad.card:ℝ) ≤ Cost ∧
      ∀ H : ℤ → ℕ, (∀ i∈S, H i ≤ N) →
        (∑ i∈Bad,(H i:ℝ)) ≤ (N:ℝ)*Cost :=
  HuxleyAnchorComplementScratch.positive_difference_minimal_anchor_complement_count S F anchor N s (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (T:=T) (M:=M) (R:=R) hσ hc hJ hη hηmax hy hf hbound htests hnegative hT hM hN hR hNM hphase hpoints

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (N : ℕ) (s : ℤ) (H : ℤ → ℕ)
      (η y T M R U x₁ x₂ : ℝ),
      1 ≤ N → (∀ k, H k ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U → x₁∈Icc M (2*M) → x₂∈Icc M (2*M) →
      let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun w => iteratedDeriv 2 f w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      U/(4*R^2) ≤ h x₂-h x₁ → h x₂-h x₁ ≤ 7*U/(2*R^2) →
      ∃ S : Finset ℤ, ∃ (anchor : ℤ → ℚ) (za : ℤ → ℝ),
        (∀ k : ℤ, k∈S ↔ x₁+(N:ℝ)/4 ≤ t k ∧ t k ≤ x₂-(N:ℝ)/4) ∧
        (∀ k∈S, za k∈Ioo x₁ x₂ ∧ h (za k)=(anchor k:ℝ) ∧
          (anchor k:ℝ)∈Ioo (h x₁) (h x₂) ∧
          (anchor k:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo (h (t k)-delta) (h (t k)+delta) → (anchor k).den ≤ a.den) ∧
        (∀ k∈S, |za k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          ((S.filter (fun k => Q ≤ (anchor k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1))) ∧
      ∀ Q : ℕ, 2 ≤ Q → Q ≤ N →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      let Dlow := 128*σ*R^2/(c*(Q:ℝ))
      let Khigh := Q/2+1
      let Dhigh := 64*σ*R^2/(c*(Khigh:ℝ))
      let Cost := 4*(Vbound+1)*Dhigh^2+Dhigh*(2+Real.log (Dhigh+1))+
        Dlow*(2*(Vbound+delta)*Dlow+1)
      ((S.filter (fun i => ¬ Good i)).card:ℝ) ≤ Cost ∧
      ∃ (r : ℤ → ℚ) (z : ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 f (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo x₁ x₂) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 f (m i)/6
      let ℓ := fun i => deriv f (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f n):ℂ)‖) ≤
          C*((N:ℝ)*Cost+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  HuxleyAnchorComplementScratch.positive_difference_interior_gap_controlled_complement_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms positive_difference_interior_gap_controlled_complement_fourier
#print axioms positive_difference_minimal_anchor_complement_count
#print axioms bourgain_bounded_denominator_count
#print axioms positive_difference_near_anchor_injective

end HuxleyAnchorComplementScratch

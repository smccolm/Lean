import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyJointTypeDecomposedScratch

private theorem actual_phase_pair_forget_card
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (ya yb : ℝ) :
    let Fiber := P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let embed := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      (((ya,ij.1.1),ij.1.2),((yb,ij.2.1),ij.2.2))
    (Fiber.image forget).card=Fiber.card ∧
      ∀ ij, ij∈Fiber.image forget ↔ embed ij∈P := by
  classical
  intro Fiber forget embed
  have hback ij (hij : ij∈Fiber) : embed (forget ij)=ij := by
    rcases ij with ⟨⟨⟨a,n⟩,ip⟩,⟨⟨b,m⟩,jp⟩⟩
    have he := (Finset.mem_filter.mp hij).2
    dsimp only at he
    rcases he with ⟨rfl,rfl⟩
    rfl
  constructor
  · apply Finset.card_image_of_injOn
    intro ij hij kl hkl he
    exact (hback ij hij).symm.trans ((congrArg embed he).trans (hback kl hkl))
  · intro ij
    constructor
    · intro hij
      obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hij
      rw [hback kl hkl]
      exact (Finset.mem_filter.mp hkl).1
    · intro hij
      exact Finset.mem_image.mpr ⟨embed ij,Finset.mem_filter.mpr ⟨hij,by constructor <;> rfl⟩,rfl⟩

private theorem actual_phase_pair_sum_card
    (S : Finset (ℝ × ℤ))
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (hP : ∀ ij∈P, ij.1.1∈S ∧ ij.2.1∈S) :
    let Y := S.image Prod.fst
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    (P.card:ℝ)=∑ ab∈Y ×ˢ Y,
      (((P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget).card:ℝ) := by
  classical
  intro Y forget
  let phase := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
    (ij.1.1.1,ij.2.1.1)
  have hmaps : Set.MapsTo phase (P : Set _) (Y ×ˢ Y : Finset _) := by
    intro ij hij
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst (hP ij hij).1,
       Finset.mem_image_of_mem Prod.fst (hP ij hij).2⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have heq ab : (P.filter (fun ij => phase ij=ab)).card=
      ((P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget).card := by
    rw [(actual_phase_pair_forget_card P ab.1 ab.2).1]
    congr 1
    rcases ab with ⟨ya,yb⟩
    ext ij
    simp only [Finset.mem_filter,phase,Prod.mk.injEq]
  rw [Finset.sum_congr rfl (fun ab _ => heq ab)] at hcard
  exact_mod_cast hcard


private theorem actual_type_one_phase_pair_partition
    (S : Finset (ℝ × ℤ))
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (small : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Prop)
    [DecidablePred small]
    (hP : ∀ ij∈P, ij.1.1∈S ∧ ij.2.1∈S) :
    let TypeOne := P.filter small
    let Rest := P.filter (fun ij => ¬small ij)
    let Upper := Rest.filter (fun ij => Mat ij 2=0)
    let NonUpper := Rest.filter (fun ij => Mat ij 2≠0)
    let Lower := NonUpper.filter (fun ij => Mat ij 1=0)
    let Large := NonUpper.filter (fun ij => Mat ij 1≠0)
    let Y := S.image Prod.fst
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let phaseFiber := fun (E : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) ab =>
      (E.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget
    (P.card:ℝ)=(TypeOne.card:ℝ)+∑ ab∈Y ×ˢ Y,
      (((phaseFiber Upper ab).card:ℝ)+((phaseFiber Lower ab).card:ℝ)+
        ((phaseFiber Large ab).card:ℝ)) := by
  classical
  intro TypeOne Rest Upper NonUpper Lower Large Y forget phaseFiber
  have hfirst : TypeOne.card+Rest.card=P.card :=
    Finset.card_filter_add_card_filter_not small
  have hsecond : Upper.card+NonUpper.card=Rest.card :=
    Finset.card_filter_add_card_filter_not (fun ij => Mat ij 2=0)
  have hthird : Lower.card+Large.card=NonUpper.card :=
    Finset.card_filter_add_card_filter_not (fun ij => Mat ij 1=0)
  have hsum : (P.card:ℝ)=(TypeOne.card:ℝ)+
      ((Upper.card:ℝ)+(Lower.card:ℝ)+(Large.card:ℝ)) := by
    exact_mod_cast (by omega : P.card=TypeOne.card+(Upper.card+Lower.card+Large.card))
  have hUpper := actual_phase_pair_sum_card S Upper (fun ij hij =>
    hP ij (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1)
  have hLower := actual_phase_pair_sum_card S Lower (fun ij hij =>
    hP ij (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1).1)
  have hLarge := actual_phase_pair_sum_card S Large (fun ij hij =>
    hP ij (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1).1)
  rw [hsum,hUpper,hLower,hLarge]
  simp only [Finset.sum_add_distrib]
  rfl


/-- The actual SAME-matrix source sieve with its Type-I contribution inserted
and the remaining Type-II/III mass reindexed by exact phase-pair fibers. -/
theorem exists_positive_difference_joint_type_decomposed_source_sieve
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
                  ((phaseFiber (Large key) ab).card:ℝ)))) := by
  classical
  intro κ Ratio L
  obtain ⟨C,Dtype,hC,hDtype,hsource⟩ :=
    exists_positive_difference_joint_type_one_source_sieve hσsrc hcsrc hUsrc hE hσ hεloss
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  intro S Fsrc z rat v Nlen Q K₀ N instK Vscale Rphys Jsep Z
    η Tsrc T M δ θ a hη hηmax hTsrc hT hM hδ hscale hQ hθ ha
    hθmax hθaction hy hz hreg hjets htests hden hinv hnegative hMtwo
    hVscale hN hJsep hJM hNM hmesh hgeometry hseparation
    Fmodel hmodel f hlevel hminor hcomplete Hsrc lambda Uband u w chart narrow
    qell V offset color ChartCap NarrowCap Cap
    q μ ell b tau dual x cloud radius Pall Fiber Pairs μ₀ U₀ h D Δ
  obtain ⟨hcard,hcharts,hratios,Mat,hfourier,hglobal,hnarrow,hclass,htype⟩ :=
    hsource S Fsrc z rat v Nlen Q K₀ N Vscale Rphys Jsep Z
      (η:=η) (Tsrc:=Tsrc) (T:=T) (M:=M) (δ:=δ) (θ:=θ) (a:=a)
      hη hηmax hTsrc hT hM hδ hscale hQ hθ ha hθmax hθaction
      hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale
      hN hJsep hJM hNM hmesh hgeometry hseparation hmodel hlevel hminor hcomplete
  refine ⟨hcard,hcharts,hratios,Mat,hfourier,hglobal,hnarrow,hclass,?_⟩
  intro TypeOne Rest Upper NonUpper Lower Large Y forget phaseFiber
  have hsplit key : ((Pairs key).card:ℝ)=((TypeOne key).card:ℝ)+∑ ab∈Y ×ˢ Y,
      (((phaseFiber (Upper key) ab).card:ℝ)+((phaseFiber (Lower key) ab).card:ℝ)+
        ((phaseFiber (Large key) ab).card:ℝ)) := by
    have hP ij (hij : ij∈Pairs key) : ij.1.1∈S ∧ ij.2.1∈S := by
      have hp := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
      exact ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hp.1).1).1,
        (Finset.mem_product.mp (Finset.mem_filter.mp hp.2).1).1⟩
    have hh := actual_type_one_phase_pair_partition S (Pairs key) Mat
      (fun ij => ij∈TypeOne key) hP
    have hsmall' : (Pairs key).filter (fun ij => ij∈TypeOne key)=TypeOne key := by
      ext ij
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
    change ((Pairs key).card:ℝ)=
      (((Pairs key).filter (fun ij => ij∈TypeOne key)).card:ℝ)+_ at hh
    rw [hsmall'] at hh
    exact hh
  refine ⟨htype,hsplit,?_⟩
  intro k
  have hCap : 0 ≤ Cap := (Nat.cast_nonneg _).trans hcard
  have hVs : 0 ≤ Vscale := zero_le_one.trans hVscale
  apply (hfourier k).trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hVs)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hCap 11))
  apply Finset.sum_le_sum
  intro key _
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg (Fiber key).card) 10)
  rw [hsplit]
  exact add_le_add (htype key).1 le_rfl


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
                  ((phaseFiber (Large key) ab).card:ℝ)))) :=
  HuxleyJointTypeDecomposedScratch.exists_positive_difference_joint_type_decomposed_source_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hE hσ hεloss


#print axioms actual_phase_pair_forget_card
#print axioms actual_phase_pair_sum_card
#print axioms actual_type_one_phase_pair_partition
#print axioms exists_positive_difference_joint_type_decomposed_source_sieve

end HuxleyJointTypeDecomposedScratch

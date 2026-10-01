import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyJointTypeOneSourceScratch

universe huxleyNarrowV

private theorem huxley_narrowed_sieve_frequency_scale {N t η ζ Vscale : ℝ}
    (hN : 1≤N) (ht : t∈Icc 1 N) (hη : 0<η) (hζ : 0<ζ) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let U : Fin 4 → ℝ := ![t,t^2,(1/η)*(t/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt (t/N)]
    ∀ d, a d*|U d| ≤ 1/12 := by
  have hNp : 0<N := by linarith
  have hVp : 0<Vscale := zero_lt_one.trans_le hV
  have ht0 : 0≤t := by linarith [ht.1]
  have hv0 : 0≤t/N := div_nonneg ht0 hNp.le
  have hv1 : t/N≤1 := (div_le_one hNp).mpr ht.2
  have hp : (t/N)^((3:ℝ)/2) ≤ 1 := Real.rpow_le_one hv0 hv1 (by norm_num)
  have hroot : Real.sqrt (t/N) ≤ 1 := Real.sqrt_le_one.mpr hv1
  dsimp only
  intro d
  fin_cases d
  · change (1/(12*N))*|t|≤1/12
    rw [abs_of_nonneg ht0]
    have hh := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0≤1/(12*N))
    exact hh.trans_eq (by field_simp)
  · change (1/(12*N^2*Vscale))*|t^2|≤1/12
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : t^2≤N^2 := pow_le_pow_left₀ ht0 ht.2 2
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤1/(12*N^2*Vscale))
    calc
      _ ≤ (1/(12*N^2*Vscale))*N^2 := hh
      _ = 1/(12*Vscale) := by field_simp
      _ ≤ 1/12 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  · change (η/12)*|(1/η)*(t/N)^((3:ℝ)/2)|≤1/12
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = (1/12)*(t/N)^((3:ℝ)/2) := by field_simp
      _ ≤ _ := by nlinarith
  · change (ζ/12)*|(1/ζ)*Real.sqrt (t/N)|≤1/12
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = (1/12)*Real.sqrt (t/N) := by field_simp
      _ ≤ _ := by nlinarith

private theorem huxley_narrowed_sieve_box_scale {N η ζ Vscale : ℝ}
    (hN : 1≤N) (hη : η∈Ioc 0 1) (hζ : ζ∈Ioc 0 1) (hV : 1≤Vscale) :
    let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
    let δ : Fin 4 → ℝ := ![1,1,2,2]
    (∀ d, 0<a d) ∧
    (∀ d, 1/(δ d+2*a d) ≤ (![1,1,1/2,1/2] : Fin 4 → ℝ) d) ∧
    16777216*(∏ d, (δ d+2*a d))/(∏ d, a d) ≤
      (16777216*36*12^4)*N^3*Vscale/(η*ζ) := by
  dsimp only
  let a : Fin 4 → ℝ := ![1/(12*N),1/(12*N^2*Vscale),η/12,ζ/12]
  let δ : Fin 4 → ℝ := ![1,1,2,2]
  have hNp : 0<N := by linarith
  have hVp : 0<Vscale := zero_lt_one.trans_le hV
  have hηp := hη.1
  have hζp := hζ.1
  have ha d : 0<a d := by
    fin_cases d <;> norm_num [a,Matrix.cons_val_succ] <;> positivity
  refine ⟨ha,?_,?_⟩
  · intro d
    have hb : 0 < δ d := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ]
    have hh : 1/(δ d+2*a d) ≤ 1/(δ d) :=
      one_div_le_one_div_of_le hb (by linarith [ha d])
    convert hh using 1
    fin_cases d <;> norm_num [δ,Matrix.cons_val_succ]
  · have ha1 d : a d≤1/12 := by
      fin_cases d
      · change 1/(12*N)≤1/12
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      · change 1/(12*N^2*Vscale)≤1/12
        have hNsq : (1:ℝ) ≤ N^2 := by nlinarith
        have hNV : (1:ℝ) ≤ N^2*Vscale :=
          one_mul (1:ℝ) ▸ mul_le_mul hNsq hV zero_le_one (sq_nonneg N)
        exact one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hNV])
      · change η/12≤1/12
        exact div_le_div_of_nonneg_right hη.2 (by norm_num)
      · change ζ/12≤1/12
        exact div_le_div_of_nonneg_right hζ.2 (by norm_num)
    have hD : (∏ d, (δ d+2*a d)) ≤ 36 := by
      have hb := Finset.prod_le_prod
        (fun d (_:d∈(Finset.univ:Finset (Fin 4))) => (by
          have hd : 0≤δ d := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ]
          linarith [ha d] : 0≤δ d+2*a d))
        (g := (![2,2,3,3] : Fin 4 → ℝ))
        (fun d _ => by
          have hh := ha1 d
          calc
            δ d+2*a d ≤ δ d+1 := by linarith
            _ ≤ _ := by fin_cases d <;> norm_num [δ,Matrix.cons_val_succ])
      norm_num [Fin.prod_univ_succ] at hb ⊢
      exact hb
    have hprod : (∏ d, a d) = η*ζ/(12^4*N^3*Vscale) := by
      norm_num [a,Fin.prod_univ_succ]
      field_simp
      ring
    have hp : 0<∏ d, a d := Finset.prod_pos (fun d _ => ha d)
    calc
      _ ≤ 16777216*36/(∏ d, a d) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD (by norm_num)) hp.le
      _ = _ := by rw [hprod]; field_simp


private theorem huxley_narrowed_sieve_final_scale
    {N η ζ Vscale L C B a p ε : ℝ}
    (hN : 0<N) (hη : 0<η) (hζ : 0<ζ) :
    (a*p)*((L*N^3*Vscale/(η*ζ))*
      (C*η*ζ*N^((9:ℝ)+ε)*B^12)) =
    (L*C)*Vscale*N^((12:ℝ)+ε)*a*B^12*p := by
  have hpow : N^3*N^((9:ℝ)+ε)=N^((12:ℝ)+ε) := by
    rw [←Real.rpow_ofNat,←Real.rpow_add hN]
    congr 1
    ring
  rw [←hpow]
  field_simp

/-- Narrowing the inverse-coordinate tolerance by Vscale costs exactly one
factor Vscale in the source-sum twelfth-power bound. The original finite
arrays and all multiplicities are retained; first spacing is proved. -/
private theorem exists_huxleySourceCurve_narrowed_double_sieve {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (N : ℕ), 1≤N → ∀ (η ζ Vscale : ℝ),
      η∈Icc (1/(N:ℝ)^2) 1 → ζ∈Icc (1/(N:ℝ)) 1 → 1≤Vscale →
      ∀ (ι κ : Type huxleyNarrowV) (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
        (m : κ → ℤ) (x : ι → Fin 4 → ℝ) (B : ℝ),
        0≤B → (∀ j∈T,1 ≤ m j ∧ m j≤N) →
        (∀ j∈T,‖w j‖≤1) →
        (∀ q : ℤ,((T.filter (fun j => m j=q)).card:ℝ)≤B) →
        (∀ i∈S,x i∈Icc ![0,0,-1,-1] (fun _ => 1)) →
        let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
          (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
        let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2*Vscale),η/12,ζ/12]
        (∑ i∈S,‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
          C*Vscale*(N:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*B^12*
            (((S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hcount⟩ := exists_bourgainSourceCurve_six_tuple_first_spacing.{huxleyNarrowV} hε
  let L : ℝ := 16777216*36*12^4
  refine ⟨L*C,by dsimp [L]; positivity,?_⟩
  intro N hN η ζ Vscale hη hζ hV ι κ S T w m x B hB hm hw hmass hx
  dsimp only
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith
  have hηp : 0<η := lt_of_lt_of_le (by positivity) hη.1
  have hζp : 0<ζ := lt_of_lt_of_le (by positivity) hζ.1
  let a : Fin 4 → ℝ := ![1/(12*(N:ℝ)),1/(12*(N:ℝ)^2*Vscale),η/12,ζ/12]
  let D : Fin 4 → ℝ := ![1,1,2,2]
  let c : Fin 4 → ℝ := ![0,0,-1,-1]
  let U := fun j => ![(m j:ℝ),(m j:ℝ)^2,
    (1/η)*((m j:ℝ)/N)^((3:ℝ)/2),(1/ζ)*Real.sqrt ((m j:ℝ)/N)]
  let V := Fintype.piFinset (fun _ : Fin 6 => T)
  let y := fun (j : Fin 6 → κ) d => ∑ k, U (j k) d
  let P := (S ×ˢ S).filter (fun ij => ∀ d, |x ij.1 d-x ij.2 d|≤2*a d)
  let Q := (V ×ˢ V).filter (fun ij => ∀ d, |y ij.1 d-y ij.2 d|≤1/(D d+2*a d))
  let K := 16777216*(∏ d,(D d+2*a d))/(∏ d,a d)
  obtain ⟨ha,hthreshold,hscale⟩ :=
    huxley_narrowed_sieve_box_scale hNr ⟨hηp,hη.2⟩ ⟨hζp,hζ.2⟩ hV
  have hD d : 0<D d := by fin_cases d <;> norm_num [D,Matrix.cons_val_succ]
  have hU j (hj : j∈T) : ∀ d,a d*|U j d|≤1/12 :=
    huxley_narrowed_sieve_frequency_scale hNr
      (by exact ⟨by exact_mod_cast (hm j hj).1,by exact_mod_cast (hm j hj).2⟩) hηp hζp hV
  have hx' i (hi : i∈S) d : x i d∈Icc (c d) (c d+D d) := by
    refine ⟨(hx i hi).1 d,?_⟩
    have hh := (hx i hi).2 d
    fin_cases d <;> norm_num [c,D,Matrix.cons_val_succ] <;> exact hh
  have hs := bourgain_four_dimensional_sixth_power_sieve S T w x U ha hD hw hx' hU
  change (∑ i∈S,‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*x i d)‖)^12 ≤
    (S.card:ℝ)^10*K*(P.card:ℝ)*(Q.card:ℝ) at hs
  have hfirst := hcount N hN η ζ hη hζ κ T m B hB hm hmass
  change (((V ×ˢ V).filter (fun ij => ∀ d,
      |y ij.1 d-y ij.2 d|≤(![1,1,1/2,1/2] : Fin 4 → ℝ) d)).card:ℝ) ≤
    C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12 at hfirst
  have hsub : Q ⊆ (V ×ˢ V).filter (fun ij => ∀ d,
      |y ij.1 d-y ij.2 d|≤(![1,1,1/2,1/2] : Fin 4 → ℝ) d) := by
    intro ij hij
    obtain ⟨hij,hnear⟩ := Finset.mem_filter.mp hij
    exact Finset.mem_filter.mpr ⟨hij,fun d => (hnear d).trans (hthreshold d)⟩
  have hQ : (Q.card:ℝ) ≤ C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12 :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hfirst
  have hK : 0≤K := by
    dsimp only [K]
    exact div_nonneg (mul_nonneg (by norm_num)
      (Finset.prod_nonneg (fun d _ => by linarith [hD d,ha d])))
      (Finset.prod_nonneg (fun d _ => (ha d).le))
  have hR : 0≤C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12 := by positivity
  have hCouter : 0≤(S.card:ℝ)^10*(P.card:ℝ) := by positivity
  have hbound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hscale hR) hCouter
  calc
    _ ≤ (S.card:ℝ)^10*K*(P.card:ℝ)*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12) :=
      hs.trans (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = ((S.card:ℝ)^10*(P.card:ℝ))*(K*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := by ring
    _ ≤ ((S.card:ℝ)^10*(P.card:ℝ))*
        ((L*(N:ℝ)^3*Vscale/(η*ζ))*(C*η*ζ*(N:ℝ)^((9:ℝ)+ε)*B^12)) := hbound
    _ = _ := huxley_narrowed_sieve_final_scale hNp hηp hζp

private theorem huxley_completed_phase_normalize
    {M : ℕ} (hM : 0 < M) (x : Fin 4 → ℝ) (n : ℤ) (hn : 0 ≤ n) :
    GafniTao.fordAdditiveCharacter (∑ d,x d*
      (![(n:ℝ),(n:ℝ)^2,(n:ℝ)^((3:ℝ)/2),Real.sqrt (n:ℝ)] : Fin 4 → ℝ) d)=
    GafniTao.fordAdditiveCharacter (∑ d,
      (![(n:ℝ),(n:ℝ)^2,(M:ℝ)^2*((n:ℝ)/M)^((3:ℝ)/2),
        (M:ℝ)*Real.sqrt ((n:ℝ)/M)] : Fin 4 → ℝ) d*
      (![Int.fract (x 0),Int.fract (x 1),x 2/Real.sqrt M,x 3/Real.sqrt M] : Fin 4 → ℝ) d) := by
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hnr : (0:ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  have hsq := Real.sq_sqrt hMr.le
  have hp : (M:ℝ)^((3:ℝ)/2)=(M:ℝ)*Real.sqrt M := by
    rw [show (3:ℝ)/2=1+1/2 by norm_num,Real.rpow_add hMr]
    simp only [Real.rpow_one,Real.sqrt_eq_rpow]
  have hthird : (M:ℝ)^2*((n:ℝ)/M)^((3:ℝ)/2)*(x 2/Real.sqrt M)=
      x 2*(n:ℝ)^((3:ℝ)/2) := by
    rw [Real.div_rpow hnr hMr.le,hp]
    field_simp
    rw [hsq]
    ring
  have hfourth : (M:ℝ)*Real.sqrt ((n:ℝ)/M)*(x 3/Real.sqrt M)=
      x 3*Real.sqrt (n:ℝ) := by
    rw [Real.sqrt_div hnr]
    field_simp
    rw [hsq]
    ring
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero]
  rw [hthird,hfourth]
  simp only [GafniTao.fordAdditiveCharacter_add]
  have he1 : GafniTao.fordAdditiveCharacter (x 0*(n:ℝ))=
      GafniTao.fordAdditiveCharacter ((n:ℝ)*Int.fract (x 0)) := by
    simpa only [mul_comm] using (sargos_character_integer_fract n (x 0)).symm
  have he2 : GafniTao.fordAdditiveCharacter (x 1*(n:ℝ)^2)=
      GafniTao.fordAdditiveCharacter ((n:ℝ)^2*Int.fract (x 1)) := by
    have hh := sargos_character_integer_fract (n^2) (x 1)
    push_cast at hh
    simpa only [mul_comm] using hh.symm
  change GafniTao.fordAdditiveCharacter (x 0*(n:ℝ))*
      (GafniTao.fordAdditiveCharacter (x 1*(n:ℝ)^2)*
        (GafniTao.fordAdditiveCharacter (x 2*(n:ℝ)^((3:ℝ)/2))*
          GafniTao.fordAdditiveCharacter (x 3*Real.sqrt (n:ℝ))))=
    GafniTao.fordAdditiveCharacter ((n:ℝ)*Int.fract (x 0))*
      (GafniTao.fordAdditiveCharacter ((n:ℝ)^2*Int.fract (x 1))*
        (GafniTao.fordAdditiveCharacter (x 2*(n:ℝ)^((3:ℝ)/2))*
          GafniTao.fordAdditiveCharacter (x 3*Real.sqrt (n:ℝ))))
  rw [he1,he2]


private theorem huxley_completed_narrowed_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (M : ℕ) [NeZero M] (Vscale : ℝ), 1≤Vscale → ∀ (ι : Type huxleyNarrowV) (S : Finset ι)
      (x : ι → Fin 4 → ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt M ∧ |x i 3| ≤ Real.sqrt M) →
      let y := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt M,x i 3/Real.sqrt M] : Fin 4 → ℝ)
      let a : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2*Vscale),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      ∀ k : ZMod M,
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
        C*Vscale*(M:ℝ)^((12:ℝ)+ε)*(S.card:ℝ)^10*
          (((S ×ˢ S).filter (fun ij => ∀ d,|y ij.1 d-y ij.2 d| ≤ 2*a d)).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_huxleySourceCurve_narrowed_double_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro M inst Vscale hV ι S x hx y a k
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMr
  let T : Finset (ULift.{huxleyNarrowV} (ZMod M)) := Finset.univ
  let m := fun j : ULift.{huxleyNarrowV} (ZMod M) => (j.down.val:ℤ)+1
  let w := fun j : ULift.{huxleyNarrowV} (ZMod M) => ZMod.stdAddChar (-(j.down*k))
  have hm j (_hj : j∈T) : 1 ≤ m j ∧ m j ≤ M := by
    dsimp only [m]
    have hj := j.down.val_lt
    constructor <;> omega
  have hmass (q : ℤ) : (((T.filter (fun j => m j=q)).card):ℝ) ≤ 1 := by
    have hh : (T.filter (fun j => m j=q)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj j' hj'
      apply ULift.ext
      apply ZMod.val_injective M
      have hjm := (Finset.mem_filter.mp hj).2
      have hjm' := (Finset.mem_filter.mp hj').2
      dsimp only [m] at hjm hjm'
      omega
    exact_mod_cast hh
  have hy i (hi : i∈S) : y i∈Icc ![0,0,-1,-1] (fun _ => 1) := by
    have h2 : |x i 2/Real.sqrt M| ≤ 1 := by
      rw [abs_div,abs_of_pos hsqrt]
      exact (div_le_one hsqrt).mpr (hx i hi).1
    have h3 : |x i 3/Real.sqrt M| ≤ 1 := by
      rw [abs_div,abs_of_pos hsqrt]
      exact (div_le_one hsqrt).mpr (hx i hi).2
    refine ⟨?_,?_⟩
    · intro d
      fin_cases d
      · exact Int.fract_nonneg _
      · exact Int.fract_nonneg _
      · exact (abs_le.mp h2).1
      · exact (abs_le.mp h3).1
    · intro d
      fin_cases d
      · exact (Int.fract_lt_one _).le
      · exact (Int.fract_lt_one _).le
      · exact (abs_le.mp h2).2
      · exact (abs_le.mp h3).2
  have hη : 1/(M:ℝ)^2∈Icc (1/(M:ℝ)^2) 1 := by
    refine ⟨le_rfl,?_⟩
    exact (div_le_one (by positivity)).mpr (by nlinarith only [hM1])
  have hζ : 1/(M:ℝ)∈Icc (1/(M:ℝ)) 1 := by
    exact ⟨le_rfl,(div_le_one hMr).mpr hM1⟩
  have hh := hsource M (by omega) (1/(M:ℝ)^2) (1/(M:ℝ))
    Vscale hη hζ hV ι (ULift.{huxleyNarrowV} (ZMod M)) S T w m y 1 (by norm_num) hm
    (fun j _ => (sargos_stdAddChar_norm _).le) hmass hy
  simp only [one_div_one_div,one_pow,mul_one] at hh
  let U := fun j : ULift.{huxleyNarrowV} (ZMod M) =>
    (![(m j:ℝ),(m j:ℝ)^2,(M:ℝ)^2*((m j:ℝ)/M)^((3:ℝ)/2),
      (M:ℝ)*Real.sqrt ((m j:ℝ)/M)] : Fin 4 → ℝ)
  have he :
      (∑ i∈S, ‖∑ j : ZMod M,ZMod.stdAddChar (-(j*k))*
        GafniTao.fordAdditiveCharacter (∑ d,x i d*
          (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
            Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)=
      ∑ i∈S, ‖∑ j∈T,w j*GafniTao.fordAdditiveCharacter (∑ d,U j d*y i d)‖ := by
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    calc
      _ = ∑ j : ULift.{huxleyNarrowV} (ZMod M),w j*
          GafniTao.fordAdditiveCharacter (∑ d,x i d*
            (![(m j:ℝ),(m j:ℝ)^2,(m j:ℝ)^((3:ℝ)/2),
              Real.sqrt (m j:ℝ)] : Fin 4 → ℝ) d) := by
        apply Fintype.sum_equiv Equiv.ulift.symm
        intro j
        simp [w,m,Equiv.ulift]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        congr 1
        exact huxley_completed_phase_normalize hM (x i) (m j) (by dsimp only [m]; omega)
  rw [he]
  exact hh


private theorem huxley_dual_physical_scale {μ q N : ℝ}
    (hμ : 0<μ) (hq : 0<q) (hN : 0<N) (hqN : q≤N)
    (hscale : 1≤μ*q^2*N) :
    1≤μ*q*N^2 ∧
    |-2*μ*(Real.sqrt (2/(3*μ*q)))^3|/Real.sqrt (μ*q*N^2) ≤ 2 := by
  have hA : 1≤μ*q*N^2 := by
    have hh := mul_le_mul_of_nonneg_left hqN (by positivity : 0≤μ*q*N)
    nlinarith
  refine ⟨hA,?_⟩
  have hs := Real.sq_sqrt (by positivity : 0≤2/(3*μ*q))
  have ht := Real.sq_sqrt (by positivity : 0≤μ*q*N^2)
  have hs0 := Real.sqrt_nonneg (2/(3*μ*q))
  have ht0 := Real.sqrt_pos.mpr (by positivity : 0<μ*q*N^2)
  have hden : 0<3*μ*q := by positivity
  have hs' : (Real.sqrt (2/(3*μ*q)))^2*(3*μ*q)=2 :=
    (eq_div_iff hden.ne').mp hs
  rw [abs_mul,abs_mul,abs_of_nonpos (by norm_num : (-2:ℝ)≤0),
    abs_of_pos hμ,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ ht0).mpr
  have hh : (μ*q^2*N)^2≥1 := by nlinarith
  have he : (μ*(Real.sqrt (2/(3*μ*q)))^3)^2*(27*μ*q^3)=8 := by
    nlinarith [show ((Real.sqrt (2/(3*μ*q)))^2*(3*μ*q))^3=8 by rw [hs']; norm_num]
  have hcomp : (μ*(Real.sqrt (2/(3*μ*q)))^3)^2 ≤ μ*q*N^2 := by
    apply (mul_le_mul_iff_left₀ (show 0<27*μ*q^3 by positivity)).mp
    rw [he]
    nlinarith
  nlinarith [show 0≤μ*(Real.sqrt (2/(3*μ*q)))^3 by positivity]

private theorem huxley_actual_dual_source_box
    {M q N : ℕ} [NeZero M] (hq : 0 < q) (hN : 1 ≤ N) (hqN : q ≤ N)
    {μ ℓ : ℝ} (hμ : 0 < μ) (hscale : 1 ≤ μ*(q:ℝ)^2*N)
    (hM : 7*(μ*(q:ℝ)*(N:ℝ)^2) ≤ M) (r : ℤ) (p : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let K := -2*μ*(Real.sqrt (2/(3*μ*(q:ℝ))))^3
    let x : Fin 4 → ℝ := ![-(r:ℝ)*b/q,-(r:ℝ)/q,K,3*K*τ/2]
    |x 2| ≤ Real.sqrt M ∧ |x 3| ≤ Real.sqrt M := by
  intro b τ K x
  let A := μ*(q:ℝ)*(N:ℝ)^2
  have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hNr : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hqNr : (q:ℝ) ≤ N := by exact_mod_cast hqN
  obtain ⟨hA,hK⟩ := huxley_dual_physical_scale hμ hqr hNr hqNr hscale
  change 1 ≤ A at hA
  change |K|/Real.sqrt A ≤ 2 at hK
  have hA0 : 0 < A := by linarith only [hA]
  have hKA : |K| ≤ 2*Real.sqrt A := (div_le_iff₀ (Real.sqrt_pos.mpr hA0)).mp hK
  have hKA2 : |K|^2 ≤ 4*A := by
    nlinarith [Real.sq_sqrt hA0.le,Real.sqrt_nonneg A,abs_nonneg K]
  have hMr : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hKM : |K| ≤ Real.sqrt M := by
    change 7*A ≤ M at hM
    nlinarith [Real.sq_sqrt hMr,Real.sqrt_nonneg (M:ℝ),abs_nonneg K]
  have hp0 : (0:ℝ) ≤ p.val := Nat.cast_nonneg _
  have hp1 : (p.val:ℝ) ≤ 1 := by exact_mod_cast (by omega : p.val ≤ 1)
  have ht : |τ| ≤ 1/2 := by
    have hlo := Int.floor_le ((q:ℝ)*ℓ)
    have hhi := Int.lt_floor_add_one ((q:ℝ)*ℓ)
    dsimp only [τ,b]
    rw [Int.cast_add,Int.cast_natCast]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  constructor
  · exact hKM
  · change |3*K*τ/2| ≤ Real.sqrt M
    rw [abs_div,abs_mul,abs_mul]
    norm_num
    have hh := mul_le_mul_of_nonneg_left ht (abs_nonneg K)
    nlinarith [Real.sqrt_nonneg (M:ℝ)]

/-- Coloring is applied to the actual completed sums before second spacing.
Every color retains its own original pair set and multiplicity. -/
private theorem huxley_completed_colored_source_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (K₀ : ℕ) [NeZero K₀] (Vscale : ℝ), 1 ≤ Vscale →
      ∀ (ι : Type huxleyNarrowV) (S : Finset ι) (x : ι → Fin 4 → ℝ)
      {κ : Type*} [DecidableEq κ] (color : ι → κ) (Cap : ℝ),
      (∀ i∈S, |x i 2| ≤ Real.sqrt K₀ ∧ |x i 3| ≤ Real.sqrt K₀) →
      ((S.image color).card:ℝ) ≤ Cap →
      let w := fun i => (![Int.fract (x i 0),Int.fract (x i 1),
        x i 2/Real.sqrt K₀,x i 3/Real.sqrt K₀] : Fin 4 → ℝ)
      let radius : Fin 4 → ℝ :=
        ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2*Vscale),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
      let Fiber := fun key => S.filter (fun i => color i=key)
      let P := fun key => ((Fiber key) ×ˢ (Fiber key)).filter
        (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
      ∀ k : ZMod K₀,
        (∑ i∈S, ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
          GafniTao.fordAdditiveCharacter (∑ d,x i d*
            (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
              Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)^12 ≤
          C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*Cap^11*
            ∑ key∈S.image color,((Fiber key).card:ℝ)^10*((P key).card:ℝ) := by
  classical
  obtain ⟨C,hC,hsieve⟩ := huxley_completed_narrowed_source_sieve.{huxleyNarrowV} hε
  refine ⟨C,hC,?_⟩
  intro K₀ inst Vscale hV ι S x κ instKey color Cap hx hcap w radius Fiber P k
  let mass := fun i => ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
    GafniTao.fordAdditiveCharacter (∑ d,x i d*
      (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
        Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖
  let Keys := S.image color
  let g := fun key => ∑ i∈Fiber key,mass i
  have hmass i : 0 ≤ mass i := norm_nonneg _
  have hg key : 0 ≤ g key := Finset.sum_nonneg (fun i _ => hmass i)
  have he : (∑ key∈Keys,g key)=∑ i∈S,mass i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem color hi) mass
  have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Keys
    (f:=g) (p:=(12:ℝ)) (by norm_num) (fun key _ => hg key)
  have hh : (∑ key∈Keys,g key)^12 ≤
      (Keys.card:ℝ)^11*∑ key∈Keys,(g key)^12 := by
    simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
  have hcost : (∑ i∈S,mass i)^12 ≤ Cap^11*∑ key∈Keys,(g key)^12 := by
    rw [←he]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcap 11)
      (Finset.sum_nonneg (fun key _ => pow_nonneg (hg key) 12)))
  have hfiber key : (g key)^12 ≤
      C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*((Fiber key).card:ℝ)^10*((P key).card:ℝ) := by
    exact hsieve K₀ Vscale hV ι (Fiber key) x
      (fun i hi => hx i (Finset.mem_filter.mp hi).1) k
  have hCap : 0 ≤ Cap := (Nat.cast_nonneg (S.image color).card).trans hcap
  change (∑ i∈S,mass i)^12 ≤ _
  calc
    _ ≤ Cap^11*∑ key∈Keys,(g key)^12 := hcost
    _ ≤ Cap^11*∑ key∈Keys,
        (C*Vscale*(K₀:ℝ)^((12:ℝ)+ε)*((Fiber key).card:ℝ)^10*((P key).card:ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun key _ => hfiber key))
        (pow_nonneg hCap 11)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key _
      ring



/-- The model third derivative prevents the actual normalized source
amplitude from degenerating. No lower comparison between Tsrc and T
is assumed. -/
private theorem positive_difference_approximate_model_source_amplitude
    (Fsrc : ℝ → ℝ) {σsrc Usrc η y Tsrc T σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
      modelPhaseThirdLower σ*σsrc*T/(3*Usrc) ≤ Tsrc := by
  intro F hF
  let G := fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)
  have hFu : F=fun u => (Tsrc/T)*G u := by
    funext u
    dsimp only [F,G]
    ring
  have hd : iteratedDeriv 3 F (3/2)=
      (Tsrc/T)*iteratedDeriv 3 G (3/2) := by
    rw [hFu,iteratedDeriv_const_mul_field]
  have hlow : modelPhaseThirdLower σ ≤ iteratedDeriv 3 F (3/2) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      (approximateModelPhase_thirdDeriv_bounds hσ hδ hF
        (by norm_num : (3/2:ℝ)∈Ioo (1:ℝ) 2)).1
  have hu := positive_jets_difference_mixed_upper Fsrc hσsrc hUsrc hη hηmax
    (by norm_num : (3/2:ℝ)∈Icc (3/4:ℝ) (9/4))
    (show y∈Icc (1/2:ℝ) 3 from
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩)
    hreg hjets 3 0 (by norm_num) (by norm_num)
  simp only [iteratedDeriv_zero] at hu
  have hupper : |iteratedDeriv 3 F (3/2)| ≤ (Tsrc/T)*(3*Usrc/σsrc) := by
    rw [hd,abs_mul,abs_of_pos (div_pos hTsrc hT)]
    exact mul_le_mul_of_nonneg_left hu (div_pos hTsrc hT).le
  have hh := hlow.trans ((le_abs_self _).trans hupper)
  have he : (Tsrc/T)*(3*Usrc/σsrc)=3*Usrc*Tsrc/(σsrc*T) := by ring
  rw [he] at hh
  have hc := (le_div_iff₀ (mul_pos hσsrc hT)).mp hh
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 3) hUsrc)).mpr
  nlinarith only [hc]

/-- The same source and model phases yield a physical curvature band
scaled by T, with the Tsrc lower comparison derived from their jets. -/
private theorem positive_difference_model_normalized_curvature_band
    (Fsrc : ℝ → ℝ) {σsrc csrc Usrc η y₀ Tsrc T E M σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy₀ : y₀∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hM : 0 < M) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hscale : Tsrc ≤ E*T)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y₀))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
    let f := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    ∀ y∈Icc (1:ℝ) 2, ∀ z∈Icc M (2*M),
      csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2) ≤
        |iteratedDeriv 2 (f y) z/2| ∧
      |iteratedDeriv 2 (f y) z/2| ≤ (3*Usrc/σsrc)*E*T/(2*M^2) := by
  intro F hF f y hy z hz
  have hsource := positive_difference_approximate_model_source_amplitude Fsrc
    hσsrc hUsrc hη hηmax hy₀ hTsrc hT hσ hδ hreg hjets hF
  have hh := positive_difference_half_curvature_source_bounds Fsrc
    hσsrc hcsrc hUsrc hη hηmax hTsrc hM hy hz hreg hjets htests
  constructor
  · apply le_trans _ hh.1
    calc
      _ = (csrc/(4*σsrc*M^2))*(modelPhaseThirdLower σ*σsrc*T/(3*Usrc)) := by
        field_simp
        ring
      _ ≤ (csrc/(4*σsrc*M^2))*Tsrc :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  · apply hh.2.trans
    simpa only [mul_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ 3*Usrc/σsrc))
      (by positivity : (0:ℝ) ≤ 2*M^2)


/-- The literal source points and Fourier parity labels carry a single
joint coloring. Source curvature is derived from the actual normalized model;
both source charts, narrow rational ratios and parity offsets survive together. -/
theorem positive_difference_actual_source_joint_twelfth_partition
    {ι : Type*} (S : Finset ι) (Fsrc : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) (Q : ℕ)
    {σsrc csrc Usrc η Tsrc T M E σ δ θ a : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hM : 0 < M)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hscale : Tsrc ≤ E*T) (hQ : 0 < Q) (hθ : 0 < θ) (ha : 0 < a)
    (hy : ∀ i∈S, y i∈Icc (1:ℝ) 2)
    (hz : ∀ i∈S, z i∈Icc M (2*M))
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|)
    (hden : ∀ i∈S, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den) :
    let Fmodel := fun i u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y i))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let u := fun i => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun i => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun i =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun i => ((rat i).den:ℝ)*deriv (f (y i)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : ι × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : ι × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((y ip.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y ip.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip=offset jp) ∧
    ∀ coeff : ι × Fin 2 → ℂ, ‖∑ ip∈V,coeff ip‖^12 ≤
      Cap^11*∑ key∈V.image color,
        ‖∑ ip∈V.filter (fun ip => color ip=key),coeff ip‖^12 := by
  classical
  intro Fmodel hmodel f hlevel Hsrc lambda u w chart narrow qell V offset color ChartCap NarrowCap Cap
  have hκ : 0 < modelPhaseThirdLower σ := modelPhaseThirdLower_pos hσ
  have hE : 0 < E := (mul_pos_iff_of_pos_right hT).mp (hTsrc.trans_le hscale)
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
  have hband i (hi : i∈S) : lambda ≤ |(rat i:ℝ)| ∧ |(rat i:ℝ)| ≤ Uband := by
    have hb := positive_difference_model_normalized_curvature_band Fsrc
      hσsrc hcsrc hUsrc hη hηmax (hy i hi) hTsrc hT hM hσ hδ hscale
      hreg hjets htests (hmodel i hi)
    rw [←hlevel i hi]
    exact hb (y i) (hy i hi) (z i) (hz i hi)
  have hchart := positive_difference_source_chart_twelfth_partition S Fsrc y z rat
    hσsrc hcsrc hUsrc hη hηmax hTsrc hM ha hy hz hreg hjets htests hlevel
  have hnarrow := rational_narrow_band_twelfth_partition S rat Q
    (U:=Uband) hQ hlambda (by dsimp only [Uband]; positivity) hθ hband hden
  have hNcap : (4/θ+3)*(4*Uband/(lambda*θ)+3)=NarrowCap := by
    dsimp only [Uband,lambda,NarrowCap]
    field_simp
    ring
  dsimp only at hnarrow
  rw [hNcap] at hnarrow
  have hoffset := fourier_parity_round_partition S qell
  have hV (ip : ι × Fin 2) (hip : ip∈V) : ip.1∈S := (Finset.mem_product.mp hip).1
  have hsub : V.image color ⊆
      (S.image chart) ×ˢ ((S.image narrow) ×ˢ (V.image offset)) := by
    intro key hkey
    obtain ⟨ip,hip,rfl⟩ := Finset.mem_image.mp hkey
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem chart (hV ip hip),
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem narrow (hV ip hip),
        Finset.mem_image_of_mem offset hip⟩⟩
  have hCnon : 0 ≤ ChartCap := by dsimp only [ChartCap]; positivity
  have hNnon : 0 ≤ NarrowCap := by dsimp only [NarrowCap]; positivity
  have hcard : ((V.image color).card:ℝ) ≤ Cap := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product,Finset.card_product] at hh
    have hreal : ((V.image color).card:ℝ) ≤
        ((S.image chart).card:ℝ)*(((S.image narrow).card:ℝ)*((V.image offset).card:ℝ)) := by
      exact_mod_cast hh
    have ho : ((V.image offset).card:ℝ) ≤ 3 := by exact_mod_cast hoffset.2.1
    apply hreal.trans
    calc
      _ ≤ ChartCap*(NarrowCap*3) := mul_le_mul hchart.1
        (mul_le_mul hnarrow.1 ho (Nat.cast_nonneg _) hNnon)
        (by positivity) hCnon
      _ = Cap := by dsimp only [Cap]; ring
  refine ⟨hcard,?_,?_,?_⟩
  · intro key hkey
    obtain ⟨ip,hip,he⟩ := Finset.mem_image.mp hkey
    have hk : key.1∈S.image chart := by
      rw [←he]
      exact Finset.mem_image_of_mem chart (hV ip hip)
    obtain ⟨iref,hiref,hkeyref,hxcenter,hycenter,hlocal⟩ := hchart.2.1 key.1 hk
    refine ⟨iref,hiref,hkeyref,hxcenter,hycenter,?_⟩
    intro jp hjp hjkey
    exact hlocal jp.1 (hV jp hjp) (congrArg Prod.fst hjkey)
  · intro ip hip jp hjp he
    have hn := hnarrow.2.1 ip.1 (hV ip hip) jp.1 (hV jp hjp)
      (congrArg (fun k : (ℤ × ℤ × ℤ) × (ℤ × ℤ) × ℤ => k.2.1) he)
    exact ⟨hn.1,hn.2,congrArg (fun k : (ℤ × ℤ × ℤ) × (ℤ × ℤ) × ℤ => k.2.2) he⟩
  · intro coeff
    let Keys := V.image color
    let g := fun key => ∑ ip∈V.filter (fun ip => color ip=key),coeff ip
    have he : (∑ key∈Keys,g key)=∑ ip∈V,coeff ip :=
      Finset.sum_fiberwise_of_maps_to (fun ip hip => Finset.mem_image_of_mem color hip) coeff
    have hnorm : ‖∑ ip∈V,coeff ip‖ ≤ ∑ key∈Keys,‖g key‖ := by
      rw [←he]
      exact norm_sum_le _ _
    have hp := pow_le_pow_left₀ (norm_nonneg _) hnorm 12
    have hholder := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Keys
      (f:=fun key => ‖g key‖) (p:=(12:ℝ)) (by norm_num) (fun _ _ => norm_nonneg _)
    have hh : (∑ key∈Keys,‖g key‖)^12 ≤ (Keys.card:ℝ)^11*∑ key∈Keys,‖g key‖^12 := by
      simpa only [show (12:ℝ)-1=11 by norm_num,Real.rpow_ofNat] using hholder
    exact (hp.trans hh).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 11)
      (Finset.sum_nonneg (fun _ _ => by positivity)))


/-- The source-derived joint coloring enters the actual narrowed completed
Fourier sieve. One global matrix family is retained, with the same denominator
ratios, homographies, cubic errors, strips and narrowed lower-left bounds.
Color fibers retain their literal original point/pair counts. -/
theorem exists_positive_difference_actual_joint_source_sieve
    {εloss : ℝ} (hεloss : 0 < εloss) :
    ∃ C > (0:ℝ),
    ∀ {ι : Type huxleyNarrowV} [DecidableEq ι], ∀ (S : Finset ι) (Fsrc : ℝ → ℝ)
    (y z : ι → ℝ) (rat : ι → ℚ) (v : ι → ℤ) (Nlen : ι → ℕ)
    (Q K₀ : ℕ) [NeZero K₀] (Vscale Nphys Rphys : ℝ)
    {σsrc csrc Usrc η Tsrc T M E σ δ θ a : ℝ},
    (0 < σsrc) →
    (0 < csrc) →
    (0 < Usrc) →
    (0 < η) →
    (η ≤ 1/8) →
    (0 < Tsrc) →
    (0 < T) →
    (0 < M) →
    (0 < σ) →
    (δ ≤ min (modelPhaseThirdLower σ) 1) →
    (Tsrc ≤ E*T) →
    (0 < Q) →
    (0 < θ) →
    (0 < a) →
    (θ < 1) →
    (∀ i∈S, y i∈Icc (1:ℝ) 2) →
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
    (0 < Nphys) →
    ((Q:ℝ)*Nphys ≤ (K₀:ℝ)*Rphys^2) →
    let Fmodel := fun i u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y i))/(σsrc*η)
    (∀ i∈S, Expdb.IsApproximateModelPhaseFunction (Fmodel i) σ 2 δ) →
    let f := fun p w => Tsrc*(Fsrc (w/M)-Fsrc (w/M+η*p))/(σsrc*η)
    (∀ i∈S, iteratedDeriv 2 (f (y i)) (z i)/2=(rat i:ℝ)) →
    (∀ i∈S, 1 ≤ Nlen i ∧ (rat i).den ≤ Nlen i ∧
      1 ≤ (iteratedDeriv 3 (f (y i)) (round (z i))/6)*((rat i).den:ℝ)^2*Nlen i) →
    (∀ i∈S, 7*((iteratedDeriv 3 (f (y i)) (round (z i))/6)*
      ((rat i).den:ℝ)*(Nlen i:ℝ)^2) ≤ K₀) →
    let Hsrc := fun p : ℝ × ℝ =>
      (iteratedDeriv 2 Fsrc p.2-iteratedDeriv 2 Fsrc (p.2+η*p.1))/(σsrc*η)
    let lambda := csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let u := fun i => (2*M^2/Tsrc)*(rat i:ℝ)
    let w := fun i => (Tsrc/(2*M^2))*(rat i:ℝ)⁻¹
    let chart := fun i => (⌊y i/a⌋,⌊u i/a⌋,⌊w i/a⌋)
    let narrow := fun i =>
      (⌊((rat i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
       ⌊((rat i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    let qell := fun i => ((rat i).den:ℝ)*deriv (f (y i)) (round (z i))
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let offset := fun ip : ι × Fin 2 => ⌊qell ip.1⌋+(ip.2:ℕ)-round (qell ip.1)
    let color := fun ip : ι × Fin 2 => (chart ip.1,narrow ip.1,offset ip)
    let ChartCap := (4/a+3)*((6*Usrc/σsrc)/a+3)*((4*σsrc/csrc)/a+3)
    let NarrowCap := (4/θ+3)*(72*Usrc^2*E/(σsrc*csrc*modelPhaseThirdLower σ*θ)+3)
    let Cap := 3*ChartCap*NarrowCap

    let q := fun i => (rat i).den
    let μ := fun i => iteratedDeriv 3 (f (y i)) (round (z i))/6
    let ell := fun i => deriv (f (y i)) (round (z i))
    let b := fun ip : ι × Fin 2 => (⌊qell ip.1⌋+(ip.2:ℕ) : ℤ)
    let tau := fun ip : ι × Fin 2 => ((b ip:ℝ)-qell ip.1)/2
    let dual := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun ip : ι × Fin 2 =>
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
    let h := fun i => iteratedDeriv 2 (f (y i)) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ((V.image color).card:ℝ) ≤ Cap ∧
    (∀ key∈V.image color, ∃ iref∈S, chart iref=key.1 ∧
      let xcenter := z iref/M
      let ycenter := y iref
      xcenter∈Icc (1:ℝ) 2 ∧ ycenter∈Icc (1:ℝ) 2 ∧
      ∀ ip∈V, color ip=key →
        ‖((y ip.1,u ip.1):ℝ × ℝ)-(ycenter,Hsrc (ycenter,xcenter))‖ < a ∧
        ‖((y ip.1,w ip.1):ℝ × ℝ)-(ycenter,(Hsrc (ycenter,xcenter))⁻¹)‖ < a) ∧
    (∀ ip∈V, ∀ jp∈V, color ip=color jp →
      |((rat jp.1).den:ℝ)/(rat ip.1).den-1| ≤ θ ∧
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip=offset jp) ∧
    ∃ Mat : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
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
        |(Mat ij 2:ℝ)| ≤ Rphys^4/(6*Nphys^2*Vscale)) ∧
      (∀ key, ∀ ij∈Pairs key,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
          |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
        (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
          |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0)) := by
  classical
  obtain ⟨C,hC,hcolored⟩ := huxley_completed_colored_source_sieve.{huxleyNarrowV} hεloss
  obtain ⟨_,_,hmatrices⟩ := exists_source_arc_fourier_narrowed_sieve_matrices.{huxleyNarrowV} hεloss
  refine ⟨C,hC,?_⟩
  intro ι inst S Fsrc y z rat v Nlen Q K₀ instK Vscale Nphys Rphys
    σsrc csrc Usrc η Tsrc T M E σ δ θ a
    hσsrc hcsrc hUsrc hη hηmax hTsrc hT hM hσ hδ hscale hQ hθ ha hθmax
    hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hNphys hmesh
    Fmodel hmodel f hlevel hminor hcomplete Hsrc lambda Uband u w chart narrow
    qell V offset color ChartCap NarrowCap Cap
    q μ ell b tau dual x cloud radius Pall Fiber Pairs μ₀ U₀ h D
  have hjoint := positive_difference_actual_source_joint_twelfth_partition S Fsrc y z rat Q
    hσsrc hcsrc hUsrc hη hηmax hTsrc hT hM hσ hδ hscale hQ hθ ha
    hy hz hreg hjets htests hden hmodel hlevel
  have hμ₀ : 0 < μ₀ := by dsimp only [μ₀]; positivity
  have hμbounds i (hi : i∈S) : μ₀ ≤ μ i ∧ μ i ≤ U₀ := by
    have hb := positive_difference_rounded_cubic_scales Fsrc (T:=Tsrc) (N:=M^3/Tsrc) (R:=1)
      hσsrc hcsrc hUsrc hη hηmax (hy i hi) hreg hjets hnegative hMtwo
      (by positivity) (by norm_num) (hz i hi) (by field_simp)
    have hlo : csrc/(12*σsrc*(M^3/Tsrc)*(1:ℝ)^2)=μ₀ := by
      dsimp only [μ₀]
      field_simp
    have hhi : Usrc/(2*σsrc*(M^3/Tsrc)*(1:ℝ)^2)=U₀ := by
      dsimp only [U₀]
      field_simp
    rw [hlo,hhi] at hb
    exact hb
  obtain ⟨Mat,_hglobalSum,hglobal,hnarrow⟩ := hmatrices ι S (fun i => f (y i)) z rat v
    Q K₀ μ₀ U₀ hμ₀ hμbounds hlevel hden hinv Nlen Vscale Nphys Rphys
    hVscale hNphys hmesh hminor hcomplete
  have hbox ip (hip : ip∈V) :
      |x ip 2| ≤ Real.sqrt K₀ ∧ |x ip 3| ≤ Real.sqrt K₀ := by
    have hi := (Finset.mem_product.mp hip).1
    exact huxley_actual_dual_source_box (rat ip.1).pos
      (hminor ip.1 hi).1 (hminor ip.1 hi).2.1
      (hμ₀.trans_le (hμbounds ip.1 hi).1) (hminor ip.1 hi).2.2
      (hcomplete ip.1 hi) (v ip.1) ip.2
  refine ⟨hjoint.1,hjoint.2.1,hjoint.2.2.1,Mat,?_,hglobal,hnarrow,?_⟩
  · intro k
    exact hcolored K₀ Vscale hVscale (ι × Fin 2) V x color Cap hbox hjoint.1 k
  · intro key ij hij
    have hp := Finset.mem_filter.mp hij
    have hi := Finset.mem_filter.mp (Finset.mem_product.mp hp.1).1
    have hj := Finset.mem_filter.mp (Finset.mem_product.mp hp.1).2
    have hiall := (Finset.mem_product.mp hi.1).1
    have hjall := (Finset.mem_product.mp hj.1).1
    have hijall : ij∈Pall := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hi.1,hj.1⟩,hp.2⟩
    have hsides := hjoint.2.2.1 ij.1 hi.1 ij.2 hj.1 (hi.2.trans hj.2.symm)
    obtain ⟨hdet,ht,_htlo,_hthi,hmap,_hrest⟩ := hglobal ij hijall
    simp only [hlevel ij.1.1 hiall,hlevel ij.2.1 hjall] at ht hmap
    have hlambda : 0 < lambda := by
      have hκ := modelPhaseThirdLower_pos hσ
      dsimp only [lambda]
      positivity
    have hband := positive_difference_model_normalized_curvature_band Fsrc
      hσsrc hcsrc hUsrc hη hηmax (hy ij.1.1 hiall) hTsrc hT hM hσ hδ hscale
      hreg hjets htests (hmodel ij.1.1 hiall)
    have hcurv : lambda ≤ |(rat ij.1.1:ℝ)| ∧ |(rat ij.1.1:ℝ)| ≤ Uband := by
      rw [←hlevel ij.1.1 hiall]
      exact hband _ (hy ij.1.1 hiall) _ (hz ij.1.1 hiall)
    have hx : (rat ij.1.1:ℝ)≠0 := abs_pos.mp (hlambda.trans_le hcurv.1)
    have htpos : 0 < (Mat ij 2:ℝ)*(rat ij.1.1:ℝ)+Mat ij 3 := by
      rw [ht]
      exact div_pos (by exact_mod_cast (rat ij.2.1).pos)
        (by exact_mod_cast (rat ij.1.1).pos)
    have hnumeq : ((Mat ij 0:ℝ)*(rat ij.1.1:ℝ)+Mat ij 1)/(rat ij.1.1:ℝ)=
        ((rat ij.2.1).num:ℝ)/(rat ij.1.1).num := by
      rw [(div_eq_iff htpos.ne').mp hmap,ht]
      simp only [Rat.cast_def]
      field_simp
    exact narrow_band_matrix_translation_cases (Mat ij 0) (Mat ij 1) (Mat ij 2) (Mat ij 3)
      hlambda hcurv.1 hcurv.2 hθ.le hθmax hdet
      (by rw [ht]; exact hsides.1) (by rw [hnumeq]; exact hsides.2.1)


private theorem positive_difference_family_bounded_action_source_scale_at_action
    {σ c U L : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P, Mat ij 1 ≠ 0 ∧ Mat ij 2 ≠ 0) →
      (∀ ij∈P, |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨K,C,hK,hC,hcount⟩ := positive_difference_family_bounded_action_pair_count hσ hc hU
  let B := max 1 (max (3*U/σ) (2*σ/c))
  let CMat := (2*(L+3)^2+1)*(2*L+5)^2*(L+3)^2
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hCMat : 0 < CMat := by dsimp only [CMat]; positivity
  refine ⟨60*K*(1+40*C*B)*CMat,by positivity,?_⟩
  intro P Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM hpoints hgeometryA hgeometryB hsep hdet hnontri haction
    f h μ t hmap hden hnum hthird
  classical
  have hMp : 0 < M := by linarith only [hM]
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hh := hcount P Mat F z Alen N Z η Δ J T M L hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hL hpoints hgeometryB hsep hdet hnontri haction hmap hden hnum hthird
  have hfirst := rounded_offset_family_point_count (P.image Prod.fst) z Alen N Z hMp.le hN
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact (hpoints ij hij).1.2)
    (by
      intro ip hip
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hip
      exact hgeometryA ij hij)
  rw [Finset.image_image] at hfirst
  let I := ((P.image (fun ij => ij.1.1.1)).card:ℝ)
  have hI : 0 ≤ I := by dsimp only [I]; positivity
  have hscale : 1 ≤ M/(N:ℝ) := (le_div_iff₀ hNp).mpr (by simpa only [one_mul] using hNM)
  have hfirst' : ((P.image Prod.fst).card:ℝ) ≤ 10*(M/(N:ℝ))*I := by
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_right _ hI
    linarith only [hscale]
  have hJM' : J/M ≤ 1 := (div_le_iff₀ hMp).mpr (by simpa only [one_mul] using hJM)
  have hfactor : 1+8*C*B*(Δ+5/M)*J ≤ (1+40*C*B)*(1+Δ*J) := by
    calc
      _ = 1+8*C*B*(Δ*J+5*(J/M)) := by ring
      _ ≤ 1+8*C*B*(Δ*J+5) := by
        gcongr
        nlinarith only [hJM']
      _ ≤ _ := by
        have hp : 0 ≤ (32*C*B+1)*(Δ*J) := by positivity
        nlinarith only [hp]
  calc
    (P.card:ℝ) ≤ 6*K*(1+8*C*B*(Δ+5/M)*J)*CMat*((P.image Prod.fst).card:ℝ) := hh
    _ ≤ 6*K*((1+40*C*B)*(1+Δ*J))*CMat*(10*(M/(N:ℝ))*I) := by
      gcongr
    _ = _ := by ring

private theorem positive_difference_family_type_one_source_scale_at_action
    {σ c U L : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hU : 0 < U) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
        (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
        (F : ℝ → ℝ) (z : ℝ → ℤ → ℝ) (Alen : ℝ → ℤ → ℕ)
        (N : ℕ) (Z : ℝ → ℤ) (η Δ J T M : ℝ),
      0 < η → η ≤ 1/8 →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ U) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ j,
        c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
          (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      0 < T → 2 ≤ M → 0 < N → 0 ≤ Δ → 0 < J → (N:ℝ) ≤ M → J ≤ M →
      (∀ ij∈P,
        (ij.1.1.1∈Icc (1:ℝ) 2 ∧ z ij.1.1.1 ij.1.1.2∈Icc M (2*M)) ∧
        (ij.2.1.1∈Icc (1:ℝ) 2 ∧ z ij.2.1.1 ij.2.1.2∈Icc M (2*M))) →
      (∀ ij∈P, N ≤ Alen ij.1.1.1 ij.1.1.2 ∧ Alen ij.1.1.1 ij.1.1.2 ≤ 3*N ∧
        round (z ij.1.1.1 ij.1.1.2)+(Alen ij.1.1.1 ij.1.1.2:ℤ)=
          Z ij.1.1.1+(N:ℤ)*ij.1.1.2+2*(N:ℤ)) →
      (∀ ij∈P, N ≤ Alen ij.2.1.1 ij.2.1.2 ∧ Alen ij.2.1.1 ij.2.1.2 ≤ 3*N ∧
        round (z ij.2.1.1 ij.2.1.2)+(Alen ij.2.1.1 ij.2.1.2:ℤ)=
          Z ij.2.1.1+(N:ℤ)*ij.2.1.2+2*(N:ℤ)) →
      (∀ ij∈P, ∀ kl∈P, ij.2.1.1 ≠ kl.2.1.1 → 1 ≤ J*|ij.2.1.1-kl.2.1.1|) →
      (∀ ij∈P, Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1) →
      (∀ ij∈P,
        (Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
        (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L)) →
      let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
      let h := fun y w => iteratedDeriv 2 (f y) w/2
      let μ := fun y w => iteratedDeriv 3 (f y) (round w)/6
      let t := fun ij => (Mat ij 2:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 3
      (∀ ij∈P, ((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/t ij=
        h ij.2.1.1 (z ij.2.1.1 ij.2.1.2)) →
      (∀ ij∈P, |t ij-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |((Mat ij 0:ℝ)*h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)+Mat ij 1)/
        h ij.1.1.1 (z ij.1.1.1 ij.1.1.2)-1| ≤ 1/(8*(L+3))) →
      (∀ ij∈P, |μ ij.2.1.1 (z ij.2.1.1 ij.2.1.2)/
        μ ij.1.1.1 (z ij.1.1.1 ij.1.1.2)*(t ij)^3-1| ≤ Δ) →
      (P.card:ℝ) ≤ D*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
        (M/(N:ℝ))*(1+Δ*J) := by
  obtain ⟨D₀,hD₀,hzero⟩ := positive_difference_family_identity_source_scale hσ hc hU
  obtain ⟨D₁,hD₁,hnonzero⟩ := positive_difference_family_bounded_action_source_scale_at_action hσ hc hU hL
  refine ⟨D₀+D₁,add_pos hD₀ hD₁,?_⟩
  intro P Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM hpoints hgeometryA hgeometryB hsep hdet hbranch
    f h μ t hmap hden hnum hthird
  classical
  let P₀ := P.filter (fun ij => Mat ij 1=0)
  let P₁ := P.filter (fun ij => Mat ij 1≠0)
  have hlo ij (hij : ij∈P₀) : ij∈P ∧ Mat ij 1=0 := Finset.mem_filter.mp hij
  have hhi ij (hij : ij∈P₁) : ij∈P ∧ Mat ij 1≠0 := Finset.mem_filter.mp hij
  have hform ij (hij : ij∈P₀) :
      Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1 := by
    rcases hbranch ij (hlo ij hij).1 with ha | ha
    · exact ha
    · exact False.elim (ha.1 (hlo ij hij).2)
  have hnontri ij (hij : ij∈P₁) :
      Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * ((3*U/σ)*T/(2*M^2)) ≤ L :=
    (hbranch ij (hhi ij hij).1).resolve_left (fun ha => (hhi ij hij).2 ha.2.1)
  have h₀ := hzero P₀ F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM
    (fun ij hij => hpoints ij (hlo ij hij).1)
    (fun ij hij => hgeometryA ij (hlo ij hij).1)
    (fun ij hij => hgeometryB ij (hlo ij hij).1)
    (fun ij hij kl hkl hne => hsep ij (hlo ij hij).1 kl (hlo kl hkl).1 hne)
    (by
      intro ij hij
      have ha := hform ij hij
      have hh := (hmap ij (hlo ij hij).1).symm
      dsimp only [t] at hh
      simpa only [ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,Int.cast_zero,Int.cast_one,
        zero_mul,one_mul,zero_add,add_zero,div_one] using hh)
    (by
      intro ij hij
      have ha := hform ij hij
      have hh := hthird ij (hlo ij hij).1
      dsimp only [t] at hh
      simpa only [ha.2.2.1,ha.2.2.2,Int.cast_zero,Int.cast_one,zero_mul,zero_add,one_pow,mul_one]
        using hh)
  have h₁ := hnonzero P₁ Mat F z Alen N Z η Δ J T M hη hηmax hf hbound htests hnegative
    hT hM hN hΔ hJ hNM hJM
    (fun ij hij => hpoints ij (hhi ij hij).1)
    (fun ij hij => hgeometryA ij (hhi ij hij).1)
    (fun ij hij => hgeometryB ij (hhi ij hij).1)
    (fun ij hij kl hkl hne => hsep ij (hhi ij hij).1 kl (hhi kl hkl).1 hne)
    (fun ij hij => hdet ij (hhi ij hij).1)
    (fun ij hij => ⟨(hnontri ij hij).1,(hnontri ij hij).2.1⟩)
    (fun ij hij => (hnontri ij hij).2.2)
    (fun ij hij => hmap ij (hhi ij hij).1)
    (fun ij hij => hden ij (hhi ij hij).1)
    (fun ij hij => hnum ij (hhi ij hij).1)
    (fun ij hij => hthird ij (hhi ij hij).1)
  have hI₀ : ((P₀.image (fun ij => ij.1.1.1)).card:ℝ) ≤
      ((P.image (fun ij => ij.1.1.1)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image
      (Finset.filter_subset (fun ij => Mat ij 1=0) P))
  have hI₁ : ((P₁.image (fun ij => ij.1.1.1)).card:ℝ) ≤
      ((P.image (fun ij => ij.1.1.1)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image
      (Finset.filter_subset (fun ij => Mat ij 1≠0) P))
  have hMp : 0 < M := by linarith only [hM]
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have h₀' : (P₀.card:ℝ) ≤ D₀*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
      (M/(N:ℝ))*(1+Δ*J) := h₀.trans (by gcongr)
  have h₁' : (P₁.card:ℝ) ≤ D₁*((P.image (fun ij => ij.1.1.1)).card:ℝ)*
      (M/(N:ℝ))*(1+Δ*J) := h₁.trans (by gcongr)
  have he : P.card=P₀.card+P₁.card := by
    exact (Finset.card_filter_add_card_filter_not (s:=P) (fun ij => Mat ij 1=0)).symm
  have heR : (P.card:ℝ)=(P₀.card:ℝ)+(P₁.card:ℝ) := by exact_mod_cast he
  rw [heR]
  calc
    _ ≤ D₀*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J)+
        D₁*((P.image (fun ij => ij.1.1.1)).card:ℝ)*(M/(N:ℝ))*(1+Δ*J) := add_le_add h₀' h₁'
    _ = _ := by ring

private theorem source_model_large_action_threshold
    {σsrc csrc Usrc E σ δ T M gamma : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hE : 0 < E) (hσ : 0 < σ) (hT : 0 < T) (hM : 0 < M)
    (hδ : δ ≤ 1) :
    let κ := modelPhaseThirdLower σ
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let Ratio := 18*Usrc^2*E/(σsrc*csrc*κ)
    let L := max (8*Ratio^2)
      (32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2)
    0 ≤ L ∧
      (L < |gamma| *Uband →
        8*Uband ≤ |gamma| *lambda^2 ∧
        64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |gamma| *κ^2*T) := by
  intro κ lambda Uband Ratio L
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hUband : 0 < Uband := by dsimp only [Uband]; positivity
  have hratio : Uband/lambda=Ratio := by
    dsimp only [Uband,lambda,Ratio]
    field_simp
    ring
  have hfirst : 8*Uband^2/lambda^2 ≤ L := by
    calc
      _ = 8*Ratio^2 := by rw [←hratio]; ring
      _ ≤ _ := le_max_left _ _
  have hsecond : 64*(modelPhaseJetCoefficient σ 3+1)*M^2*Uband/(κ^2*T) ≤ L := by
    calc
      _ = 32*(modelPhaseJetCoefficient σ 3+1)*(3*Usrc/σsrc)*E/κ^2 := by
        dsimp only [Uband]
        field_simp
        ring
      _ ≤ _ := le_max_right _ _
  refine ⟨(by dsimp only [L]; exact (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)),?_⟩
  intro hlarge
  constructor
  · have hh := (div_le_iff₀ (sq_pos_of_pos hlambda)).mp (hfirst.trans hlarge.le)
    apply (mul_le_mul_iff_right₀ hUband).mp
    nlinarith only [hh]
  · have hh := (div_le_iff₀ (by positivity : 0 < κ^2*T)).mp (hsecond.trans hlarge.le)
    have hbound : 64*(modelPhaseJetCoefficient σ 3+1)*M^2 ≤ |gamma| *κ^2*T := by
      apply (mul_le_mul_iff_right₀ hUband).mp
      nlinarith only [hh]
    apply le_trans _ hbound
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδ) (by norm_num : (0:ℝ) ≤ 64))
      (sq_nonneg M)


/-- The SAME joint-colored source sieve now carries a linear Type-1 family count.
The fixed source cutoff also discharges both Type-3 large-entry gates on the
nontriangular complement; no matrix or pair-count certificate is assumed. -/
theorem exists_positive_difference_joint_type_one_source_sieve
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
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip=offset jp) ∧
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
      ∀ key, (((TypeOne key).card:ℝ) ≤
        Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep)) ∧
        (∀ ij∈Pairs key, ij∉TypeOne key →
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
            |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
            |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
          (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧
            8*Uband ≤ |(Mat ij 2:ℝ)| * lambda^2 ∧
            64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| * κ^2*T)) := by
  classical
  intro κ Ratio L
  have hL : 0 ≤ L := by
    change 0 ≤ max (8*Ratio^2) _
    exact (by positivity : (0:ℝ) ≤ 8*Ratio^2).trans (le_max_left _ _)
  obtain ⟨C,hC,hsource⟩ := exists_positive_difference_actual_joint_source_sieve hεloss
  obtain ⟨Dtype,hDtype,hcount⟩ :=
    positive_difference_family_type_one_source_scale_at_action hσsrc hcsrc hUsrc hL
  refine ⟨C,Dtype,hC,hDtype,?_⟩
  intro S Fsrc z rat v Nlen Q K₀ N instK Vscale Rphys Jsep Z
    η Tsrc T M δ θ a hη hηmax hTsrc hT hM hδ hscale hQ hθ ha
    hθmax hθaction hy hz hreg hjets htests hden hinv hnegative hMtwo
    hVscale hN hJsep hJM hNM hmesh hgeometry hseparation
    Fmodel hmodel f hlevel hminor hcomplete Hsrc lambda Uband u w chart narrow
    qell V offset color ChartCap NarrowCap Cap
    q μ ell b tau dual x cloud radius Pall Fiber Pairs μ₀ U₀ h D Δ
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨hcard,hcharts,hratios,Mat,hfourier,hglobal,hnarrow,hclass⟩ :=
    hsource S Fsrc Prod.fst z rat v Nlen Q K₀ Vscale (N:ℝ) Rphys
      (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (η:=η) (Tsrc:=Tsrc) (T:=T)
      (M:=M) (E:=E) (σ:=σ) (δ:=δ) (θ:=θ) (a:=a)
      hσsrc hcsrc hUsrc hη hηmax hTsrc hT hM hσ hδ hscale hQ hθ ha hθmax
      hy hz hreg hjets htests hden hinv hnegative hMtwo hVscale hNp hmesh
      hmodel hlevel hminor hcomplete
  refine ⟨hcard,hcharts,hratios,Mat,hfourier,hglobal,hnarrow,hclass,?_⟩
  intro TypeOne key
  constructor
  · let P₁ := TypeOne key
    have hmem ij (hij : ij∈P₁) :
        ij∈Pairs key ∧
        ((Mat ij 0=1 ∧ Mat ij 1=0 ∧ Mat ij 2=0 ∧ Mat ij 3=1) ∨
          (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧ |(Mat ij 2:ℝ)| * Uband ≤ L)) :=
      Finset.mem_filter.mp hij
    have hboth ij (hij : ij∈P₁) :
        ij.1.1∈S ∧ ij.2.1∈S := by
      have hp := Finset.mem_product.mp (Finset.mem_filter.mp (hmem ij hij).1).1
      exact ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hp.1).1).1,
        (Finset.mem_product.mp (Finset.mem_filter.mp hp.2).1).1⟩
    have hall ij (hij : ij∈P₁) : ij∈Pall := by
      have hp := Finset.mem_filter.mp (hmem ij hij).1
      have hi := Finset.mem_filter.mp (Finset.mem_product.mp hp.1).1
      have hj := Finset.mem_filter.mp (Finset.mem_product.mp hp.1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi.1,hj.1⟩,hp.2⟩
    have hsame ij (hij : ij∈P₁) :
        |((rat ij.2.1).den:ℝ)/(rat ij.1.1).den-1| ≤ θ ∧
        |((rat ij.2.1).num:ℝ)/(rat ij.1.1).num-1| ≤ θ := by
      have hp := Finset.mem_product.mp (Finset.mem_filter.mp (hmem ij hij).1).1
      have hi := Finset.mem_filter.mp hp.1
      have hj := Finset.mem_filter.mp hp.2
      have hh := hratios ij.1 hi.1 ij.2 hj.1 (hi.2.trans hj.2.symm)
      exact ⟨hh.1,hh.2.1⟩
    have hheight : (3*Usrc/σsrc)*Tsrc/(2*M^2) ≤ Uband := by
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ 3*Usrc/σsrc))
        (by positivity : (0:ℝ) ≤ 2*M^2)
      simpa only [Uband,mul_assoc] using hh
    have hnum ij (hij : ij∈P₁) :
        |((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/h ij.1.1-1| ≤ θ := by
      obtain ⟨_hdet,ht,htlo,_hthi,hmap,_hrest⟩ := hglobal ij (hall ij hij)
      have ht' : (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3 =
          (q ij.2.1:ℝ)/q ij.1.1 := ht
      have htlo' : (1/2:ℝ) ≤ (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3 := htlo
      have hmap' : ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/
          ((Mat ij 2:ℝ)*h ij.1.1+Mat ij 3) = h ij.2.1 := hmap
      have htpos : 0 < (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3 :=
        (by norm_num : (0:ℝ) < 1/2).trans_le htlo'
      have hnumeq : ((Mat ij 0:ℝ)*h ij.1.1+Mat ij 1)/h ij.1.1=
          ((rat ij.2.1).num:ℝ)/(rat ij.1.1).num := by
        rw [(div_eq_iff htpos.ne').mp hmap',ht']
        simp only [h,hlevel ij.1.1 (hboth ij hij).1,hlevel ij.2.1 (hboth ij hij).2,
          q,Rat.cast_def]
        field_simp
      rw [hnumeq]
      exact (hsame ij hij).2
    have hΔ : 0 ≤ Δ := by dsimp only [Δ,U₀,μ₀]; positivity
    have hh := hcount P₁ Mat Fsrc (fun a n => z (a,n)) (fun a n => Nlen (a,n))
      N Z η Δ Jsep Tsrc M hη hηmax hreg hjets htests hnegative
      hTsrc hMtwo hN hΔ hJsep hNM hJM
      (fun ij hij => ⟨⟨hy _ (hboth ij hij).1,hz _ (hboth ij hij).1⟩,
        ⟨hy _ (hboth ij hij).2,hz _ (hboth ij hij).2⟩⟩)
      (fun ij hij => hgeometry _ (hboth ij hij).1)
      (fun ij hij => hgeometry _ (hboth ij hij).2)
      (fun ij hij kl hkl hne => hseparation _ (hboth ij hij).2 _ (hboth kl hkl).2 hne)
      (fun ij hij => (hglobal ij (hall ij hij)).1)
      (by
        intro ij hij
        rcases (hmem ij hij).2 with hid | hact
        · exact Or.inl hid
        · exact Or.inr ⟨hact.1,hact.2.1,
            (mul_le_mul_of_nonneg_left hheight (abs_nonneg _)).trans hact.2.2⟩)
      (fun ij hij => (hglobal ij (hall ij hij)).2.2.2.2.1)
      (by
        intro ij hij
        change |(Mat ij 2:ℝ)*h ij.1.1+Mat ij 3-1| ≤ 1/(8*(L+3))
        have ht : (Mat ij 2:ℝ)*h ij.1.1+Mat ij 3 =
            (q ij.2.1:ℝ)/q ij.1.1 := (hglobal ij (hall ij hij)).2.1
        rw [ht]
        exact (hsame ij hij).1.trans hθaction)
      (fun ij hij => (hnum ij hij).trans hθaction)
      (fun ij hij => (hglobal ij (hall ij hij)).2.2.2.2.2.2.1)
    have hsub : P₁.image (fun ij => ij.1.1.1) ⊆ S.image Prod.fst := by
      intro y hy
      obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image_of_mem Prod.fst (hboth ij hij).1
    have hI : ((P₁.image (fun ij => ij.1.1.1)).card:ℝ) ≤ ((S.image Prod.fst).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hh.trans (by gcongr)
  · intro ij hij hnot
    rcases hclass key ij hij with hid | hu | hl | hn
    · exact False.elim (hnot (Finset.mem_filter.mpr ⟨hij,Or.inl hid⟩))
    · exact Or.inl hu
    · exact Or.inr (Or.inl hl)
    · have hlarge : L < |(Mat ij 2:ℝ)| * Uband := by
        by_contra hle
        exact hnot (Finset.mem_filter.mpr ⟨hij,Or.inr ⟨hn.1,hn.2,le_of_not_gt hle⟩⟩)
      have hbounds := (source_model_large_action_threshold (gamma:=(Mat ij 2:ℝ))
        hσsrc hcsrc hUsrc hE hσ hT hM (hδ.trans (min_le_right _ _))).2 hlarge
      exact Or.inr (Or.inr ⟨hn.1,hn.2,hbounds.1,hbounds.2⟩)


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
      |((rat jp.1).num:ℝ)/(rat ip.1).num-1| ≤ θ ∧ offset ip=offset jp) ∧
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
      ∀ key, (((TypeOne key).card:ℝ) ≤
        Dtype*((S.image Prod.fst).card:ℝ)*(M/(N:ℝ))*(1+Δ*Jsep)) ∧
        (∀ ij∈Pairs key, ij∉TypeOne key →
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 2=0 ∧ Mat ij 1≠0 ∧
            |(Mat ij 1:ℝ)| ≤ θ*Uband) ∨
          (Mat ij 0=1 ∧ Mat ij 3=1 ∧ Mat ij 1=0 ∧ Mat ij 2≠0 ∧
            |(Mat ij 2:ℝ)| ≤ θ/lambda) ∨
          (Mat ij 1≠0 ∧ Mat ij 2≠0 ∧
            8*Uband ≤ |(Mat ij 2:ℝ)| * lambda^2 ∧
            64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(Mat ij 2:ℝ)| * κ^2*T)) :=
  HuxleyJointTypeOneSourceScratch.exists_positive_difference_joint_type_one_source_sieve (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (E:=E) (σ:=σ) (εloss:=εloss) hσsrc hcsrc hUsrc hE hσ hεloss


#print axioms positive_difference_family_bounded_action_source_scale_at_action
#print axioms positive_difference_family_type_one_source_scale_at_action
#print axioms source_model_large_action_threshold
#print axioms exists_positive_difference_joint_type_one_source_sieve

end HuxleyJointTypeOneSourceScratch

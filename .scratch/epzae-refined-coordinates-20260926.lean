import TaoTrudgianYang2025.ParabolaBilinearLocalization
import TaoTrudgianYang2025.ContinuousSecondDerivativeRange
import TaoTrudgianYang2025.FiniteSmoothThirdDerivative
import TaoTrudgianYang2025.IntegerFourierTails
import GafniTao.HeathBrownKernelFourier

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025.RefinedPrototype

private theorem fourth_coordinate_shift_error {K K' τ τ' κ δ₃ δ₄ : ℝ}
    (hκ : 0 < κ) (hK : κ ≤ |K|) (hτ' : |τ'| ≤ 1/2)
    (hthree : |K-K'| ≤ δ₃)
    (hfour : |3*K*τ/2-3*K'*τ'/2| ≤ δ₄) :
    |τ-τ'| ≤ (2*δ₄/3+δ₃/2)/κ := by
  have he : |K*τ-K'*τ'| ≤ 2*δ₄/3 := by
    have hh : |3*K*τ/2-3*K'*τ'/2| = (3/2)*|K*τ-K'*τ'| := by
      rw [show 3*K*τ/2-3*K'*τ'/2=(3/2)*(K*τ-K'*τ') by ring,abs_mul]
      norm_num
    rw [hh] at hfour
    linarith
  have hδ₃ : 0 ≤ δ₃ := (abs_nonneg _).trans hthree
  have hprod : |(K'-K)*τ'| ≤ δ₃/2 := by
    rw [abs_mul,abs_sub_comm]
    have hh := mul_le_mul hthree hτ' (abs_nonneg _) hδ₃
    nlinarith only [hh]
  have ht : |K| * |τ-τ'| ≤ 2*δ₄/3+δ₃/2 := by
    calc
      _ = |(K*τ-K'*τ')+(K'-K)*τ'| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ |K*τ-K'*τ'|+|(K'-K)*τ'| := abs_add_le _ _
      _ ≤ _ := add_le_add he hprod
  apply (le_div_iff₀ hκ).mpr
  have hh := mul_le_mul_of_nonneg_right hK (abs_nonneg (τ-τ'))
  nlinarith only [ht,hh]

private theorem joint_linear_resonance
    (R R' b b' : ℤ) {q q' ℓ ℓ' τ τ' D δ₁ δ₂ : ℝ}
    (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hτ' : |τ'| ≤ 1/2) (hg : |(R:ℝ)/q| ≤ 1)
    (hb : (b:ℝ)-q*ℓ=2*τ) (hb' : (b':ℝ)-q'*ℓ'=2*τ')
    (htau : |τ-τ'| ≤ D)
    (hfirst : |Int.fract (-(R:ℝ)*b/q)-Int.fract (-(R':ℝ)*b'/q')| ≤ δ₁)
    (hsecond : |(R:ℝ)/q-(R':ℝ)/q'| ≤ δ₂) :
    ∃ u v : ℤ, |q*ℓ-q'*ℓ'-(u:ℝ)| ≤ 2*D ∧
      |-(R:ℝ)*ℓ+(R':ℝ)*ℓ'-(v:ℝ)| ≤ δ₁+2*D+δ₂ := by
  let v : ℤ := ⌊-(R:ℝ)*b/q⌋-⌊-(R':ℝ)*b'/q'⌋
  have hraw : |-(R:ℝ)*b/q+(R':ℝ)*b'/q'-(v:ℝ)| ≤ δ₁ := by
    convert hfirst using 1
    dsimp only [v,Int.fract]
    push_cast
    congr 1
    ring
  refine ⟨b-b',v,?_,?_⟩
  · have he : q*ℓ-q'*ℓ'-((b-b':ℤ):ℝ) = -2*(τ-τ') := by
      push_cast
      linarith only [hb,hb']
    rw [he,abs_mul]
    norm_num
    linarith only [htau]
  · have hD : 0 ≤ D := (abs_nonneg _).trans htau
    have hδ₂ : 0 ≤ δ₂ := (abs_nonneg _).trans hsecond
    have herror : |2*((R:ℝ)/q)*(τ-τ')+
        2*((R:ℝ)/q-(R':ℝ)/q')*τ'| ≤ 2*D+δ₂ := by
      have h1 : |2*((R:ℝ)/q)*(τ-τ')| ≤ 2*D := by
        rw [abs_mul,abs_mul]
        norm_num
        have hh := mul_le_mul hg htau (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
        nlinarith only [hh]
      have h2 : |2*((R:ℝ)/q-(R':ℝ)/q')*τ'| ≤ δ₂ := by
        rw [abs_mul,abs_mul]
        norm_num
        have hh := mul_le_mul hsecond hτ' (abs_nonneg _) hδ₂
        nlinarith only [hh]
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    have he : -(R:ℝ)*ℓ+(R':ℝ)*ℓ'-(v:ℝ) =
        (-(R:ℝ)*b/q+(R':ℝ)*b'/q'-(v:ℝ))+
          (2*((R:ℝ)/q)*(τ-τ')+2*((R:ℝ)/q-(R':ℝ)/q')*τ') := by
      have hbq := (div_eq_iff hq).mpr (by linarith only [hb] : (b:ℝ)-2*τ=ℓ*q)
      have hbq' := (div_eq_iff hq').mpr (by linarith only [hb'] : (b':ℝ)-2*τ'=ℓ'*q')
      rw [← hbq,← hbq']
      ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith only [hraw,herror])

#print axioms fourth_coordinate_shift_error
#print axioms joint_linear_resonance

private theorem canonical_inverse_coordinate (r : ℤ) (q : ℕ) (hq : 0 < q) :
    ∃ R : ℤ, (q:ℤ) ∣ R-r ∧ (R:ℝ)/q=-Int.fract (-(r:ℝ)/q) ∧
      |(R:ℝ)/q| ≤ 1 ∧ ∀ b : ℤ,
        Int.fract (-(R:ℝ)*b/q)=Int.fract (-(r:ℝ)*b/q) := by
  let t : ℤ := ⌊-(r:ℝ)/q⌋
  let R : ℤ := r+(q:ℤ)*t
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : (R:ℝ)/q=-Int.fract (-(r:ℝ)/q) := by
    dsimp only [R,t,Int.fract]
    push_cast
    field_simp
    ring
  refine ⟨R,⟨t,by dsimp [R]; ring⟩,he,?_,?_⟩
  · rw [he,abs_neg,abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  · intro b
    have hb : -(R:ℝ)*b/q=-(r:ℝ)*b/q-((t*b:ℤ):ℝ) := by
      dsimp only [R]
      push_cast
      field_simp
      ring
    rw [hb,Int.fract_sub_intCast]

private theorem four_coordinate_integer_constraints
    (q q' : ℕ) (r r' b b' : ℤ)
    {ℓ ℓ' K K' τ τ' κ δ₁ δ₂ δ₃ δ₄ : ℝ}
    (hq : 0 < q) (hq' : 0 < q')
    (hκ : 0 < κ) (hK : κ ≤ |K|) (hτ' : |τ'| ≤ 1/2)
    (hb : (b:ℝ)-(q:ℝ)*ℓ=2*τ) (hb' : (b':ℝ)-(q':ℝ)*ℓ'=2*τ')
    (hfirst : |Int.fract (-(r:ℝ)*b/q)-Int.fract (-(r':ℝ)*b'/q')| ≤ δ₁)
    (hsecond : |Int.fract (-(r:ℝ)/q)-Int.fract (-(r':ℝ)/q')| ≤ δ₂)
    (hthree : |K-K'| ≤ δ₃) (hfour : |3*K*τ/2-3*K'*τ'/2| ≤ δ₄) :
    let D := (2*δ₄/3+δ₃/2)/κ
    ∃ R R' u v : ℤ, (q:ℤ) ∣ R-r ∧ (q':ℤ) ∣ R'-r' ∧
      |(((q':ℤ)*R-(q:ℤ)*R':ℤ):ℝ)| ≤ δ₂*(q:ℝ)*q' ∧
      |(q:ℝ)*ℓ-(q':ℝ)*ℓ'-(u:ℝ)| ≤ 2*D ∧
      |-(R:ℝ)*ℓ+(R':ℝ)*ℓ'-(v:ℝ)| ≤ δ₁+2*D+δ₂ := by
  intro D
  obtain ⟨R,hRd,hR,hRabs,hRb⟩ := canonical_inverse_coordinate r q hq
  obtain ⟨R',hR'd,hR',hR'abs,hR'b⟩ := canonical_inverse_coordinate r' q' hq'
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq'r : (q':ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
  have htau : |τ-τ'| ≤ D := fourth_coordinate_shift_error hκ hK hτ' hthree hfour
  have hsecond' : |(R:ℝ)/q-(R':ℝ)/q'| ≤ δ₂ := by
    rw [hR,hR',neg_sub_neg,abs_sub_comm]
    exact hsecond
  obtain ⟨u,v,hu,hv⟩ := joint_linear_resonance R R' b b' (δ₁ := δ₁) hqr hq'r hτ' hRabs
    hb hb' htau (by rw [hRb,hR'b]; exact hfirst) hsecond'
  refine ⟨R,R',u,v,hRd,hR'd,?_,hu,hv⟩
  have he : (((q':ℤ)*R-(q:ℤ)*R':ℤ):ℝ) =
      (q:ℝ)*q'*((R:ℝ)/q-(R':ℝ)/q') := by
    push_cast
    field_simp
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (q:ℝ)*q')]
  have hh := mul_le_mul_of_nonneg_left hsecond' (by positivity : 0 ≤ (q:ℝ)*q')
  nlinarith only [hh]

#print axioms canonical_inverse_coordinate
#print axioms four_coordinate_integer_constraints

private theorem dual_coefficient_lower
    {μ U q Q : ℝ} (hμ : 0 < μ) (hq : 0 < q)
    (hμU : μ ≤ U) (hqQ : q ≤ Q) :
    1/Real.sqrt (U*Q^3) ≤ |-2*μ*(Real.sqrt (2/(3*μ*q)))^3| := by
  let K := -2*μ*(Real.sqrt (2/(3*μ*q)))^3
  have hU : 0 < U := hμ.trans_le hμU
  have hQ : 0 < Q := hq.trans_le hqQ
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ 2/(3*μ*q))
  have hKsq : K^2*(μ*q^3)=32/27 := by
    dsimp only [K]
    calc
      _ = 4*μ^2*((Real.sqrt (2/(3*μ*q)))^2)^3*(μ*q^3) := by ring
      _ = 4*μ^2*(2/(3*μ*q))^3*(μ*q^3) := by rw [hroot]
      _ = _ := by field_simp; ring
  have hscale : μ*q^3 ≤ U*Q^3 := by gcongr
  have hsq : (abs K*Real.sqrt (U*Q^3))^2 ≥ 32/27 := by
    rw [mul_pow,sq_abs,Real.sq_sqrt (by positivity : 0 ≤ U*Q^3)]
    exact hKsq ▸ mul_le_mul_of_nonneg_left hscale (sq_nonneg K)
  have hpos : 0 ≤ abs K*Real.sqrt (U*Q^3) := by positivity
  have hone : 1 ≤ abs K*Real.sqrt (U*Q^3) := by nlinarith only [hsq,hpos]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity : 0 < U*Q^3))).mpr hone

private theorem actual_four_coordinate_constraints
    (M q q' Q : ℕ) [NeZero M] (a' r r' : ℤ)
    (hq : 0 < q) (hq' : 0 < q') (hqQ : q ≤ Q)
    (har' : (q':ℤ) ∣ a'*r'-1)
    {μ μ' U ℓ ℓ' : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ') (hμU : μ ≤ U)
    (p p' : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let b' : ℤ := ⌊(q':ℝ)*ℓ'⌋+(p':ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let τ' := ((b':ℝ)-(q':ℝ)*ℓ')/2
    let K := -2*μ*(Real.sqrt (2/(3*μ*(q:ℝ))))^3
    let K' := -2*μ'*(Real.sqrt (2/(3*μ'*(q':ℝ))))^3
    let y : Fin 4 → ℝ := ![Int.fract (-(r:ℝ)*b/q),Int.fract (-(r:ℝ)/q),
      K/Real.sqrt M,(3*K*τ/2)/Real.sqrt M]
    let y' : Fin 4 → ℝ := ![Int.fract (-(r':ℝ)*b'/q'),Int.fract (-(r':ℝ)/q'),
      K'/Real.sqrt M,(3*K'*τ'/2)/Real.sqrt M]
    let window : Fin 4 → ℝ :=
      ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
    let D := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
      Real.sqrt (U*(Q:ℝ)^3)
    (∀ d, |y d-y' d| ≤ 2*window d) →
    |τ-τ'| ≤ D ∧ ∃ R R' u v : ℤ, (q:ℤ) ∣ R-r ∧ (q':ℤ) ∣ R'-r' ∧
      |(((q':ℤ)*R-(q:ℤ)*R':ℤ):ℝ)| ≤ (q:ℝ)*q'/(6*(M:ℝ)^2) ∧
      |(q:ℝ)*ℓ-(q':ℝ)*ℓ'-(u:ℝ)| ≤ 2*D ∧
      |-(R:ℝ)*ℓ+(R':ℝ)*ℓ'-(v:ℝ)| ≤ 1/(6*(M:ℝ))+2*D+1/(6*(M:ℝ)^2) := by
  intro b b' τ τ' K K' y y' window D hnear
  have hMr : (0:ℝ) < M := by exact_mod_cast NeZero.pos M
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hqQr : (q:ℝ) ≤ Q := by exact_mod_cast hqQ
  have hQ : (0:ℝ) < Q := hqr.trans_le hqQr
  have hU : 0 < U := hμ.trans_le hμU
  have hs : 0 < Real.sqrt (U*(Q:ℝ)^3) := Real.sqrt_pos.mpr (by positivity)
  have hsM : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hMr
  let κ := 1/Real.sqrt (U*(Q:ℝ)^3)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hK : κ ≤ |K| := dual_coefficient_lower hμ hqr hμU hqQr
  haveI : NeZero q' := ⟨hq'.ne'⟩
  have hτ' : |τ'| ≤ 1/2 :=
    (bourgain_cubic_dual_phase_coordinates q' a' r' har' hμ' ℓ' p').1
  have hfirst : |Int.fract (-(r:ℝ)*b/q)-Int.fract (-(r':ℝ)*b'/q')| ≤ 1/(6*(M:ℝ)) := by
    have hh := hnear 0
    change _ ≤ 2*(1/(12*(M:ℝ))) at hh
    convert hh using 1
    ring
  have hsecond : |Int.fract (-(r:ℝ)/q)-Int.fract (-(r':ℝ)/q')| ≤ 1/(6*(M:ℝ)^2) := by
    have hh := hnear 1
    change _ ≤ 2*(1/(12*(M:ℝ)^2)) at hh
    convert hh using 1
    ring
  have hthird : |K-K'| ≤ Real.sqrt M/(6*(M:ℝ)^2) := by
    have hh := hnear 2
    change |K/Real.sqrt M-K'/Real.sqrt M| ≤ 2*((1/(M:ℝ)^2)/12) at hh
    rw [← sub_div,abs_div,abs_of_pos hsM] at hh
    have hr := (div_le_iff₀ hsM).mp hh
    convert hr using 1
    ring
  have hfourth : |3*K*τ/2-3*K'*τ'/2| ≤ Real.sqrt M/(6*(M:ℝ)) := by
    have hh := hnear 3
    change |(3*K*τ/2)/Real.sqrt M-(3*K'*τ'/2)/Real.sqrt M| ≤ 2*((1/(M:ℝ))/12) at hh
    rw [← sub_div,abs_div,abs_of_pos hsM] at hh
    have hr := (div_le_iff₀ hsM).mp hh
    convert hr using 1
    ring
  have heD : (2*(Real.sqrt M/(6*(M:ℝ)))/3+(Real.sqrt M/(6*(M:ℝ)^2))/2)/κ=D := by
    dsimp only [D,κ]
    field_simp
    ring
  have htau := fourth_coordinate_shift_error hκ hK hτ' hthird hfourth
  rw [heD] at htau
  refine ⟨htau,?_⟩
  obtain ⟨R,R',u,v,hRd,hR'd,hgamma,hu,hv⟩ :=
    four_coordinate_integer_constraints q q' r r' b b' (ℓ := ℓ) (ℓ' := ℓ') hq hq' hκ hK hτ'
      (by dsimp only [τ]; ring) (by dsimp only [τ']; ring)
      hfirst hsecond hthird hfourth
  rw [heD] at hu hv
  refine ⟨R,R',u,v,hRd,hR'd,?_,hu,hv⟩
  convert hgamma using 1
  ring

private theorem affine_lattice_strip
    (R R' B' a' b b' : ℤ) {q q' ℓ ℓ' τ τ' D δ₁ : ℝ}
    (hq : 0 < q) (hq' : 0 < q')
    (hinv' : (a':ℝ)*R'-(B':ℝ)*q'=1)
    (hτ : |τ| ≤ 1/2)
    (hb : (b:ℝ)-q*ℓ=2*τ) (hb' : (b':ℝ)-q'*ℓ'=2*τ')
    (htau : |τ-τ'| ≤ D)
    (hfirst : |Int.fract (-(R:ℝ)*b/q)-Int.fract (-(R':ℝ)*b'/q')| ≤ δ₁)
    (d d' : ℤ) (hd : (d:ℝ)=q) (hd' : (d':ℝ)=q') :
    let γ : ℤ := d'*R-d*R'
    let α : ℤ := a'*R-B'*d
    ∃ e₁ e₂ : ℤ,
      |(γ:ℝ)*ℓ-e₁| ≤ q'*δ₁+|(γ:ℝ)|/q ∧
      |(ℓ'-(α:ℝ)*ℓ-e₂)+((a':ℝ)/q')*((γ:ℝ)*ℓ-e₁)| ≤ 2*D/q' := by
  intro γ α
  let w : ℤ := ⌊-(R:ℝ)*b/q⌋-⌊-(R':ℝ)*b'/q'⌋
  let E := -(R:ℝ)*b/q+(R':ℝ)*b'/q'-(w:ℝ)
  have hE : |E| ≤ δ₁ := by
    convert hfirst using 1
    dsimp only [E,w,Int.fract]
    push_cast
    congr 1
    ring
  let e₁ : ℤ := R'*(b'-b)-d'*w
  let e₂ : ℤ := a'*w+B'*(b-b')
  have hγ : (γ:ℝ)=q'*(R:ℝ)-q*(R':ℝ) := by
    dsimp only [γ]
    push_cast
    rw [hd,hd']
  have he₁ : (γ:ℝ)*ℓ-e₁ = -q'*E-2*(γ:ℝ)*τ/q := by
    dsimp only [e₁,E]
    push_cast
    rw [hd',hγ]
    field_simp
    linear_combination -(q'*(R:ℝ)-q*(R':ℝ))*hb
  refine ⟨e₁,e₂,?_,?_⟩
  · have hsmall : |2*(γ:ℝ)*τ/q| ≤ |(γ:ℝ)|/q := by
      rw [abs_div,abs_mul,abs_mul,abs_of_pos hq]
      norm_num
      apply div_le_div_of_nonneg_right _ hq.le
      nlinarith only [mul_le_mul_of_nonneg_left hτ (abs_nonneg (γ:ℝ))]
    rw [he₁]
    calc
      _ ≤ |-q'*E|+|2*(γ:ℝ)*τ/q| := abs_sub _ _
      _ = q'*|E|+|2*(γ:ℝ)*τ/q| := by rw [abs_mul,abs_neg,abs_of_pos hq']
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hE hq'.le) hsmall
  · have he : (ℓ'-(α:ℝ)*ℓ-e₂)+((a':ℝ)/q')*((γ:ℝ)*ℓ-e₁)=2*(τ-τ')/q' := by
      dsimp only [α,γ,e₁,e₂]
      push_cast
      rw [hd,hd']
      field_simp
      nlinarith only [hinv',hb,hb',
        congrArg (fun x : ℝ => (b:ℝ)*x) hinv',
        congrArg (fun x : ℝ => (b':ℝ)*x) hinv',
        congrArg (fun x : ℝ => q*ℓ*x) hinv']
    rw [he,abs_div,abs_mul,abs_of_pos hq']
    norm_num
    exact div_le_div_of_nonneg_right (by linarith only [htau]) hq'.le

private theorem rational_strip_unique
    (a q u v u' v' : ℤ) (hq : 0 < q) (hcop : IsCoprime q a)
    (hwidth : |u-u'| < q)
    (hthin : |((v:ℝ)-(a:ℝ)/q*u)-((v':ℝ)-(a:ℝ)/q*u')| < 1/(q:ℝ)) :
    u=u' ∧ v=v' := by
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hid : ((q*(v-v')-a*(u-u'):ℤ):ℝ) =
      (q:ℝ)*(((v:ℝ)-(a:ℝ)/q*u)-((v':ℝ)-(a:ℝ)/q*u')) := by
    push_cast
    field_simp
    ring
  have hsmall : |q*(v-v')-a*(u-u')| < (1:ℤ) := by
    have hr : |(((q*(v-v')-a*(u-u'):ℤ):ℝ))| < 1 := by
      rw [hid,abs_mul,abs_of_pos hqr]
      have hh := mul_lt_mul_of_pos_left hthin hqr
      have he : (q:ℝ)*(1/(q:ℝ))=1 := by field_simp
      exact he ▸ hh
    exact_mod_cast hr
  have he : q*(v-v')-a*(u-u')=0 := Int.abs_lt_one_iff.mp hsmall
  have hdiv : q ∣ a*(u-u') := by
    rw [← sub_eq_zero.mp he]
    exact dvd_mul_right q (v-v')
  have hu : u-u'=0 := Int.eq_zero_of_abs_lt_dvd (hcop.dvd_of_dvd_mul_left hdiv) hwidth
  have hv : v-v'=0 := by
    rw [hu,mul_zero,sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hq.ne'
  exact ⟨sub_eq_zero.mp hu,sub_eq_zero.mp hv⟩

private theorem inverse_curvature_derivative
    (f : ℝ → ℝ) {A B L : ℝ} (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    (∀ x∈Ioo A B, c (h x)=x) ∧
    ∀ v∈h '' Ioo A B,
      h (c v)=v ∧ c v∈Ioo A B ∧
      HasDerivAt c (2/iteratedDeriv 3 f (c v)) v ∧
      HasDerivAt (fun u => deriv f (c u)/2)
        (2*v/iteratedDeriv 3 f (c v)) v := by
  intro h c
  have hd x (hx : x∈Ioo A B) : HasDerivAt h (iteratedDeriv 3 f x/2) x := by
    have hc := contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf x hx)
    simpa only [h,iteratedDeriv_succ] using
      (hc.differentiableAt (by norm_num)).hasDerivAt.div_const 2
  have hs : StrictMonoOn h (Ioo A B) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo A B)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x∈Ioo A B := by simpa only [interior_Ioo] using hx
      rw [(hd x hx').deriv]
      have hh := hthree x hx'
      linarith only [hh,hL]
  have hleft x (hx : x∈Ioo A B) : c (h x)=x := hs.injOn.leftInvOn_invFunOn hx
  refine ⟨hleft,?_⟩
  intro v hv
  have hcI : c v∈Ioo A B := Function.invFunOn_mem hv
  have he : h (c v)=v := Function.invFunOn_eq hv
  have hcder : HasDerivAt c (2/iteratedDeriv 3 f (c v)) v := by
    obtain ⟨x,hx,rfl⟩ := hv
    rw [hleft x hx]
    have hc := (contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf x hx)).div_const 2
    have hsd := hc.hasStrictDerivAt (by norm_num)
    change HasStrictDerivAt h (deriv h x) x at hsd
    rw [(hd x hx).deriv] at hsd
    have hi : HasStrictDerivAt c (iteratedDeriv 3 f x/2)⁻¹ (h x) := by
      apply hsd.to_local_left_inverse (by have hh := hthree x hx; linarith only [hh,hL])
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hleft y hy
    convert hi.hasDerivAt using 1
    simp only [inv_div]
  refine ⟨he,hcI,hcder,?_⟩
  have hd' : HasDerivAt (deriv f) (iteratedDeriv 2 f (c v)) (c v) := by
    have hh := (contDiffAt_iteratedDeriv_finite (n:=3) (j:=1) (hf _ hcI)).differentiableAt (by norm_num)
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hh.hasDerivAt
  have hh := (hd'.comp v hcder).div_const 2
  convert hh using 1
  change iteratedDeriv 2 f (c v)/2=v at he
  calc
    _ = 2*(iteratedDeriv 2 f (c v)/2)/iteratedDeriv 3 f (c v) :=
      congrArg (fun t : ℝ => 2*t/iteratedDeriv 3 f (c v)) he.symm
    _ = _ := by ring

private theorem resonance_displacement_derivative
    (f : ℝ → ℝ) {A B L : ℝ} (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x)
    (a b g d : ℝ) (hdet : a*d-b*g=1) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let ell := fun x => deriv f (c x)/2
    let t := fun x => g*x+d
    let w := fun x => (a*x+b)/t x
    let F₁ := fun x => c (w x)-d*c x-g*ell x
    let F₂ := fun x => ell (w x)-b*c x-a*ell x
    ∀ x : ℝ, x∈h '' Ioo A B → w x∈h '' Ioo A B → t x ≠ 0 →
      let R := iteratedDeriv 3 f (c (w x))*(t x)^3-iteratedDeriv 3 f (c x)
      let V := -2*R/(iteratedDeriv 3 f (c x)*iteratedDeriv 3 f (c (w x))*(t x)^2)
      HasDerivAt F₁ V x ∧ HasDerivAt F₂ (w x*V) x := by
  intro h c ell t w F₁ F₂ x hx hw ht R V
  have hp := inverse_curvature_derivative f hL hf hthree
  have hc := hp.2 x hx
  have hc' := hp.2 (w x) hw
  have hfx : 0 < iteratedDeriv 3 f (c x) := hL.trans_le (hthree _ hc.2.1)
  have hfy : 0 < iteratedDeriv 3 f (c (w x)) := hL.trans_le (hthree _ hc'.2.1)
  have hwder : HasDerivAt w (1/(t x)^2) x := by
    have hh := (((hasDerivAt_id x).const_mul a).add_const b).div
      (((hasDerivAt_id x).const_mul g).add_const d) ht
    simp only [mul_one,id_eq] at hh
    convert hh using 1
    congr 1
    nlinarith only [hdet]
  have h₁ := (((hc'.2.2.1.comp x hwder).sub (hc.2.2.1.const_mul d)).sub
    (hc.2.2.2.const_mul g))
  have h₂ := (((hc'.2.2.2.comp x hwder).sub (hc.2.2.1.const_mul b)).sub
    (hc.2.2.2.const_mul a))
  change HasDerivAt F₁
    (2/iteratedDeriv 3 f (c (w x))*(1/(t x)^2)-d*(2/iteratedDeriv 3 f (c x))-
      g*(2*x/iteratedDeriv 3 f (c x))) x at h₁
  change HasDerivAt F₂
    (2*w x/iteratedDeriv 3 f (c (w x))*(1/(t x)^2)-b*(2/iteratedDeriv 3 f (c x))-
      a*(2*x/iteratedDeriv 3 f (c x))) x at h₂
  constructor
  · convert h₁ using 1
    dsimp only [V,R]
    field_simp [ht,hfx.ne',hfy.ne']
    dsimp only [t]
    ring
  · convert h₂ using 1
    dsimp only [V,R]
    field_simp [ht,hfx.ne',hfy.ne']
    have hwt : w x*t x=a*x+b := by dsimp only [w]; field_simp
    linear_combination -iteratedDeriv 3 f (c (w x))*(t x)^2*hwt

private theorem displacement_scalar_bound {L X Y t R E : ℝ}
    (hL : 0 < L) (hX : L ≤ X) (hY : L ≤ Y) (ht : 1/2 ≤ t)
    (hR : |R| ≤ E) :
    |-2*R/(X*Y*t^2)| ≤ 8*E/L^2 := by
  have hXp : 0 < X := hL.trans_le hX
  have hYp : 0 < Y := hL.trans_le hY
  have htp : 0 < t := by linarith only [ht]
  have hE : 0 ≤ E := (abs_nonneg _).trans hR
  have hden : L^2/4 ≤ X*Y*t^2 := by
    have hxy : L^2 ≤ X*Y := by nlinarith only [mul_le_mul hX hY hL.le hXp.le]
    have hts : (1:ℝ)/4 ≤ t^2 := by nlinarith only [ht]
    nlinarith only [mul_le_mul hxy hts (by norm_num : (0:ℝ) ≤ 1/4) (mul_nonneg hXp.le hYp.le)]
  rw [abs_div,abs_mul,abs_of_pos (by positivity : 0 < X*Y*t^2)]
  norm_num
  calc
    _ ≤ (2*E)/(L^2/4) := div_le_div₀ (by positivity) (by linarith only [hR])
      (by positivity : 0 < L^2/4) hden
    _ = _ := by field_simp; ring

private theorem resonance_displacement_short_box
    (f : ℝ → ℝ) {A B L l r E : ℝ} (hL : 0 < L) (hlr : l ≤ r)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x)
    (a b g d : ℝ) (hdet : a*d-b*g=1) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let ell := fun x => deriv f (c x)/2
    let t := fun x => g*x+d
    let w := fun x => (a*x+b)/t x
    let F₁ := fun x => c (w x)-d*c x-g*ell x
    let F₂ := fun x => ell (w x)-b*c x-a*ell x
    (∀ x∈Icc l r, x∈h '' Ioo A B ∧ w x∈h '' Ioo A B ∧ 1/2 ≤ t x) →
    (∀ x∈Icc l r,
      |iteratedDeriv 3 f (c (w x))*(t x)^3-iteratedDeriv 3 f (c x)| ≤ E) →
    ∀ x∈Icc l r, ∀ y∈Icc l r,
      |F₁ x-F₁ y| ≤ (8*E/L^2)*|x-y| ∧
      |(F₂ x-w l*F₁ x)-(F₂ y-w l*F₁ y)| ≤
        (32*E*(r-l)/L^2)*|x-y| := by
  intro h c ell t w F₁ F₂ hdomain hres x hx y hy
  let V := fun z => -2*(iteratedDeriv 3 f (c (w z))*(t z)^3-iteratedDeriv 3 f (c z))/
    (iteratedDeriv 3 f (c z)*iteratedDeriv 3 f (c (w z))*(t z)^2)
  have hE : 0 ≤ E := (abs_nonneg _).trans (hres l ⟨le_rfl,hlr⟩)
  have hV z (hz : z∈Icc l r) : |V z| ≤ 8*E/L^2 := by
    apply displacement_scalar_bound hL
      (hthree _ (Function.invFunOn_mem (hdomain z hz).1))
      (hthree _ (Function.invFunOn_mem (hdomain z hz).2.1))
      (hdomain z hz).2.2 (hres z hz)
  have hder z (hz : z∈Icc l r) : HasDerivAt F₁ (V z) z ∧ HasDerivAt F₂ (w z*V z) z :=
    resonance_displacement_derivative f hL hf hthree a b g d hdet z
      (hdomain z hz).1 (hdomain z hz).2.1 (by have hh := (hdomain z hz).2.2; linarith only [hh])
  have hwder z (hz : z∈Icc l r) : HasDerivAt w (1/(t z)^2) z := by
    have ht : t z ≠ 0 := by have hh := (hdomain z hz).2.2; linarith only [hh]
    have hh := (((hasDerivAt_id z).const_mul a).add_const b).div
      (((hasDerivAt_id z).const_mul g).add_const d) ht
    simp only [mul_one,id_eq] at hh
    convert hh using 1
    congr 1
    nlinarith only [hdet]
  have hwbound z (hz : z∈Icc l r) : ‖1/(t z)^2‖ ≤ (4:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/(t z)^2)]
    have ht := (hdomain z hz).2.2
    apply (div_le_iff₀ (sq_pos_of_ne_zero (by linarith only [ht]))).mpr
    nlinarith only [ht]
  have hwl z (hz : z∈Icc l r) : |w z-w l| ≤ 4*(r-l) := by
    have hh := (convex_Icc l r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hwder u hu).hasDerivWithinAt) hwbound hz ⟨le_rfl,hlr⟩
    simp only [Real.norm_eq_abs,abs_sub_comm (w l),abs_sub_comm l] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1)] at hh
    exact hh.trans (by linarith only [hz.2])
  constructor
  · have hh := (convex_Icc l r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hder z hz).1.hasDerivWithinAt)
      (fun z hz => by simpa only [Real.norm_eq_abs] using hV z hz) hy hx
    simpa only [Real.norm_eq_abs] using hh
  · have hdiff z (hz : z∈Icc l r) :
        HasDerivAt (fun z => F₂ z-w l*F₁ z) ((w z-w l)*V z) z := by
      convert (hder z hz).2.sub ((hder z hz).1.const_mul (w l)) using 1
      ring
    have hh := (convex_Icc l r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (C:=32*E*(r-l)/L^2) (fun z hz => (hdiff z hz).hasDerivWithinAt)
      (fun z hz => by
        rw [Real.norm_eq_abs,abs_mul]
        have hm := mul_le_mul (hwl z hz) (hV z hz) (abs_nonneg _) (by positivity : 0 ≤ 4*(r-l))
        convert hm using 1
        ring) hy hx
    simpa only [Real.norm_eq_abs] using hh

private theorem inverse_lift_fract (q : ℕ) (hq : 0 < q) (r R b : ℤ)
    (hR : (q:ℤ) ∣ R-r) :
    Int.fract (-(R:ℝ)*b/q)=Int.fract (-(r:ℝ)*b/q) := by
  obtain ⟨t,ht⟩ := hR
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hR' : (R:ℝ)=(r:ℝ)+(q:ℝ)*t := by exact_mod_cast (by linarith only [ht] : R=r+(q:ℤ)*t)
  have he : -(R:ℝ)*b/q=-(r:ℝ)*b/q-((t*b:ℤ):ℝ) := by
    rw [hR']
    push_cast
    field_simp
    ring
  rw [he,Int.fract_sub_intCast]

private theorem actual_source_affine_lattice_strip
    (M q q' Q : ℕ) [NeZero M] (a a' r r' m n : ℤ)
    (hq : 0 < q) (hq' : 0 < q') (hqQ : q ≤ Q)
    (har : (q:ℤ) ∣ a*r-1) (har' : (q':ℤ) ∣ a'*r'-1)
    {μ μ' U ℓ ℓ' : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ') (hμU : μ ≤ U)
    (p p' : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let b' : ℤ := ⌊(q':ℝ)*ℓ'⌋+(p':ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let τ' := ((b':ℝ)-(q':ℝ)*ℓ')/2
    let K := -2*μ*(Real.sqrt (2/(3*μ*(q:ℝ))))^3
    let K' := -2*μ'*(Real.sqrt (2/(3*μ'*(q':ℝ))))^3
    let y : Fin 4 → ℝ := ![Int.fract (-(r:ℝ)*b/q),Int.fract (-(r:ℝ)/q),
      K/Real.sqrt M,(3*K*τ/2)/Real.sqrt M]
    let y' : Fin 4 → ℝ := ![Int.fract (-(r':ℝ)*b'/q'),Int.fract (-(r':ℝ)/q'),
      K'/Real.sqrt M,(3*K'*τ'/2)/Real.sqrt M]
    let window : Fin 4 → ℝ :=
      ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
    let D := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
      Real.sqrt (U*(Q:ℝ)^3)
    (∀ d, |y d-y' d| ≤ 2*window d) →
    ∃ α β γ δ e₁ e₂ : ℤ,
      α*δ-β*γ=1 ∧ α*a+β*q=a' ∧ γ*a+δ*q=q' ∧
      |(γ:ℝ)| ≤ (q:ℝ)*q'/(6*(M:ℝ)^2) ∧
      let F₁ := 2*(n:ℝ)-2*(δ:ℝ)*m-(γ:ℝ)*ℓ
      let F₂ := ℓ'-2*(β:ℝ)*m-(α:ℝ)*ℓ
      |F₁-e₁| ≤ (q':ℝ)/(6*(M:ℝ))+|(γ:ℝ)|/q ∧
      |(F₂-e₂)-((a':ℝ)/q')*(F₁-e₁)| ≤ 2*D/q' := by
  intro b b' τ τ' K K' y y' window D hnear
  obtain ⟨htau,R,R',u,v,hRd,hR'd,hgamma,_hu,_hv⟩ :=
    actual_four_coordinate_constraints M q q' Q a' r r' hq hq' hqQ har' hμ hμ' hμU p p' hnear
  have hinv : (q:ℤ) ∣ a*R-1 := by
    convert dvd_add har (dvd_mul_of_dvd_right hRd a) using 1
    ring
  have hinv' : (q':ℤ) ∣ a'*R'-1 := by
    convert dvd_add har' (dvd_mul_of_dvd_right hR'd a') using 1
    ring
  obtain ⟨B,hB⟩ := hinv
  obtain ⟨B',hB'⟩ := hinv'
  have hBez : a*R-B*q=1 := by nlinarith only [hB]
  have hBez' : a'*R'-B'*q'=1 := by nlinarith only [hB']
  let α := a'*R-B'*(q:ℤ)
  let β := B'*a-a'*B
  let γ := (q':ℤ)*R-R'*(q:ℤ)
  let δ := R'*a-(q':ℤ)*B
  have hdet : α*δ-β*γ=1 := by
    dsimp only [α,β,γ,δ]
    calc
      _ = (a*R-B*(q:ℤ))*(a'*R'-B'*(q':ℤ)) := by ring
      _ = 1 := by rw [hBez,hBez']; norm_num
  have ha : α*a+β*q=a' := by
    dsimp only [α,β]
    nlinarith only [congrArg (fun z : ℤ => a'*z) hBez]
  have hqmap : γ*a+δ*q=q' := by
    dsimp only [γ,δ]
    nlinarith only [congrArg (fun z : ℤ => (q':ℤ)*z) hBez]
  have hγ : |(γ:ℝ)| ≤ (q:ℝ)*q'/(6*(M:ℝ)^2) := by
    simpa only [γ,mul_comm R' (q:ℤ)] using hgamma
  have hfirst : |Int.fract (-(R:ℝ)*b/q)-Int.fract (-(R':ℝ)*b'/q')| ≤ 1/(6*(M:ℝ)) := by
    rw [inverse_lift_fract q hq r R b hRd,inverse_lift_fract q' hq' r' R' b' hR'd]
    have hh := hnear 0
    change _ ≤ 2*(1/(12*(M:ℝ))) at hh
    convert hh using 1
    ring
  haveI : NeZero q := ⟨hq.ne'⟩
  have hτ : |τ| ≤ 1/2 := (bourgain_cubic_dual_phase_coordinates q a r har hμ ℓ p).1
  obtain ⟨v₁,v₂,h₁,h₂⟩ := affine_lattice_strip R R' B' a' b b'
    (ℓ := ℓ) (ℓ' := ℓ') (by exact_mod_cast hq) (by exact_mod_cast hq')
    (by exact_mod_cast hBez') hτ (by dsimp only [τ]; ring) (by ring)
    htau hfirst (q:ℤ) (q':ℤ) (by simp) (by simp)
  rw [← mul_comm R' (q:ℤ)] at h₁ h₂
  change |(γ:ℝ)*ℓ-v₁| ≤ _ at h₁
  change |(ℓ'-(α:ℝ)*ℓ-v₂)+((a':ℝ)/q')*((γ:ℝ)*ℓ-v₁)| ≤ _ at h₂
  refine ⟨α,β,γ,δ,2*n-2*δ*m-v₁,v₂-2*β*m,hdet,ha,hqmap,hγ,?_⟩
  dsimp only
  push_cast
  constructor
  · convert h₁ using 1
    · rw [← abs_neg]
      congr 1
      ring
    · ring
  · convert h₂ using 1
    congr 1
    ring

private theorem rounded_first_derivative_error
    (f : ℝ → ℝ) {x m U : ℝ}
    (hf : ∀ z∈uIcc x m, ContDiffAt ℝ 3 f z)
    (hb : ∀ z∈uIcc x m, |iteratedDeriv 3 f z| ≤ 6*U)
    (hm : |m-x| ≤ 1/2) :
    |iteratedDeriv 1 f m-iteratedDeriv 1 f x-
      iteratedDeriv 2 f x*(m-x)| ≤ 3*U/4 := by
  have hU : 0 ≤ U := by have hh := hb x left_mem_uIcc; linarith only [abs_nonneg (iteratedDeriv 3 f x),hh]
  have ht := abs_finiteTaylorPolynomial_remainder_le_finite
    (f:=iteratedDeriv 1 f) (a:=x) (x:=m) (M:=6*U) 1
    (fun z hz => contDiffAt_iteratedDeriv_finite (n:=2) (j:=1) (hf z hz))
    (fun z hz => by simpa only [iteratedDeriv_real_comp_order] using hb z hz)
  have hpoly : finiteTaylorPolynomial (iteratedDeriv 1 f) 1 x m =
      iteratedDeriv 1 f x+iteratedDeriv 2 f x*(m-x) := by
    simp [finiteTaylorPolynomial,taylor_within_apply,iteratedDeriv_succ]
    ring
  rw [hpoly] at ht
  have hs : |m-x|^2 ≤ (1:ℝ)/4 := by nlinarith only [hm,abs_nonneg (m-x)]
  have hh := mul_le_mul_of_nonneg_left hs hU
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.cast_ofNat] at ht
  calc
    _ = |iteratedDeriv 1 f m-(iteratedDeriv 1 f x+
      iteratedDeriv 2 f x*(m-x))| := by congr 1; ring
    _ ≤ _ := ht
    _ ≤ _ := by nlinarith only [hh]

private theorem rounded_displacement_strip
    (f : ℝ → ℝ) {x y m n U a b c d v w t : ℝ}
    (hf : ∀ z∈uIcc x m ∪ uIcc y n, ContDiffAt ℝ 3 f z)
    (hb : ∀ z∈uIcc x m ∪ uIcc y n, |iteratedDeriv 3 f z| ≤ 6*U)
    (hm : |m-x| ≤ 1/2) (hn : |n-y| ≤ 1/2)
    (hv : iteratedDeriv 2 f x=2*v) (hw : iteratedDeriv 2 f y=2*w)
    (hdet : a*d-b*c=1) (ht : t=c*v+d) (hmap : w*t=a*v+b)
    (htlo : 1/2 ≤ t) (hthi : t ≤ 2) :
    let F₁ := 2*n-2*d*m-c*iteratedDeriv 1 f m
    let F₂ := iteratedDeriv 1 f n-2*b*m-a*iteratedDeriv 1 f m
    let G₁ := 2*y-2*d*x-c*iteratedDeriv 1 f x
    let G₂ := iteratedDeriv 1 f y-2*b*x-a*iteratedDeriv 1 f x
    |F₁-G₁| ≤ 3+3*|c| *U/4 ∧
    |(F₂-G₂)-w*(F₁-G₁)| ≤ 9*U/4 := by
  intro F₁ F₂ G₁ G₂
  let e := iteratedDeriv 1 f m-iteratedDeriv 1 f x-2*v*(m-x)
  let e' := iteratedDeriv 1 f n-iteratedDeriv 1 f y-2*w*(n-y)
  have he : |e| ≤ 3*U/4 := by
    simpa only [e,hv] using rounded_first_derivative_error f
      (fun z hz => hf z (Or.inl hz)) (fun z hz => hb z (Or.inl hz)) hm
  have he' : |e'| ≤ 3*U/4 := by
    simpa only [e',hw] using rounded_first_derivative_error f
      (fun z hz => hf z (Or.inr hz)) (fun z hz => hb z (Or.inr hz)) hn
  have hU : 0 ≤ U := by linarith only [he,abs_nonneg e]
  have htpos : 0 < t := by linarith only [htlo]
  have hid : a-w*c=1/t := by
    apply (eq_div_iff htpos.ne').mpr
    calc
      _ = a*(c*v+d)-c*(w*t) := by rw [ht]; ring
      _ = 1 := by rw [hmap]; nlinarith only [hdet]
  have hrecip : |a-w*c| ≤ 2 := by
    rw [hid,abs_of_pos (one_div_pos.mpr htpos)]
    apply (div_le_iff₀ htpos).mpr
    linarith only [htlo]
  constructor
  · have hid₁ : F₁-G₁=2*(n-y)-2*t*(m-x)-c*e := by
      dsimp only [F₁,G₁,e]
      rw [ht]
      ring
    rw [hid₁]
    calc
      _ ≤ |2*(n-y)|+|2*t*(m-x)|+|c*e| := by
        have h₁ := abs_sub (2*(n-y)-2*t*(m-x)) (c*e)
        have h₂ := abs_sub (2*(n-y)) (2*t*(m-x))
        linarith only [h₁,h₂]
      _ = 2*|n-y|+2*t*|m-x|+|c| *|e| := by
        simp only [abs_mul,abs_of_pos htpos,abs_of_pos (by norm_num : (0:ℝ)<2)]
      _ ≤ 2*(1/2)+2*2*(1/2)+|c| *(3*U/4) := by gcongr
      _ = _ := by ring
  · have hid₂ : (F₂-G₂)-w*(F₁-G₁)=e'-(a-w*c)*e := by
      dsimp only [F₂,G₂,F₁,G₁,e,e']
      have hh : w*(c*v+d)=a*v+b := by rwa [←ht]
      linear_combination 2*(m-x)*hh
    rw [hid₂]
    calc
      _ ≤ |e'|+|(a-w*c)*e| := abs_sub _ _
      _ = |e'|+|a-w*c| *|e| := by rw [abs_mul]
      _ ≤ 3*U/4+2*(3*U/4) := by gcongr
      _ = _ := by ring

private theorem legendre_resonance_of_integer_strip
    (f : ℝ → ℝ) (a a' q q' α β γ δ e₁ e₂ : ℤ) {x y W : ℝ}
    (hq' : 0 < q') (hdet : α*δ-β*γ=1)
    (ha : α*a+β*q=a') (hqmap : γ*a+δ*q=q') :
    let G₁ := 2*y-2*(δ:ℝ)*x-(γ:ℝ)*deriv f x
    let G₂ := deriv f y-2*(β:ℝ)*x-(α:ℝ)*deriv f x
    |(G₂-e₂)-((a':ℝ)/q')*(G₁-e₁)| ≤ W →
    ∃ e : ℤ, |((q':ℝ)*deriv f y-2*(a':ℝ)*y)-
      ((q:ℝ)*deriv f x-2*(a:ℝ)*x)-e| ≤ (q':ℝ)*W := by
  intro G₁ G₂ hstrip
  have h₁ : q'*α-a'*γ=q := by
    rw [←ha,←hqmap]
    linear_combination q*hdet
  have h₂ : q'*β-a'*δ=-a := by
    rw [←ha,←hqmap]
    linear_combination -a*hdet
  have h₁R : (q':ℝ)*α-(a':ℝ)*γ=q := by exact_mod_cast h₁
  have h₂R : (q':ℝ)*β-(a':ℝ)*δ=-(a:ℝ) := by exact_mod_cast h₂
  have hqpos : 0 < (q':ℝ) := by exact_mod_cast hq'
  refine ⟨q'*e₂-a'*e₁,?_⟩
  have he : ((q':ℝ)*deriv f y-2*(a':ℝ)*y)-
      ((q:ℝ)*deriv f x-2*(a:ℝ)*x)-((q'*e₂-a'*e₁:ℤ):ℝ) =
      (q':ℝ)*((G₂-e₂)-((a':ℝ)/q')*(G₁-e₁)) := by
    dsimp only [G₁,G₂]
    push_cast
    field_simp
    linear_combination deriv f x*h₁R+2*x*h₂R
  rw [he,abs_mul,abs_of_pos hqpos]
  exact mul_le_mul_of_nonneg_left hstrip hqpos.le

#print axioms legendre_resonance_of_integer_strip

private theorem actual_source_resonance_curve_strip
    (f : ℝ → ℝ) (M q q' Q : ℕ) [NeZero M]
    (a a' r r' m n : ℤ) {x y U : ℝ}
    (hq : 0 < q) (hq' : 0 < q') (hqQ : q ≤ Q)
    (hqratio : q ≤ 2*q') (hqratio' : q' ≤ 2*q)
    (har : (q:ℤ) ∣ a*r-1) (har' : (q':ℤ) ∣ a'*r'-1)
    (hf : ∀ z∈uIcc x (m:ℝ) ∪ uIcc y (n:ℝ), ContDiffAt ℝ 3 f z)
    (hb : ∀ z∈uIcc x (m:ℝ) ∪ uIcc y (n:ℝ), |iteratedDeriv 3 f z| ≤ 6*U)
    (hm : |(m:ℝ)-x| ≤ 1/2) (hn : |(n:ℝ)-y| ≤ 1/2)
    (hμ : 0 < iteratedDeriv 3 f m) (hμ' : 0 < iteratedDeriv 3 f n)
    (hx : iteratedDeriv 2 f x/2=(a:ℝ)/q)
    (hy : iteratedDeriv 2 f y/2=(a':ℝ)/q')
    (p p' : Fin 2) :
    let μ := iteratedDeriv 3 f m/6
    let μ' := iteratedDeriv 3 f n/6
    let ℓ := iteratedDeriv 1 f m
    let ℓ' := iteratedDeriv 1 f n
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let b' : ℤ := ⌊(q':ℝ)*ℓ'⌋+(p':ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let τ' := ((b':ℝ)-(q':ℝ)*ℓ')/2
    let K := -2*μ*(Real.sqrt (2/(3*μ*(q:ℝ))))^3
    let K' := -2*μ'*(Real.sqrt (2/(3*μ'*(q':ℝ))))^3
    let Y : Fin 4 → ℝ := ![Int.fract (-(r:ℝ)*b/q),Int.fract (-(r:ℝ)/q),
      K/Real.sqrt M,(3*K*τ/2)/Real.sqrt M]
    let Y' : Fin 4 → ℝ := ![Int.fract (-(r':ℝ)*b'/q'),Int.fract (-(r':ℝ)/q'),
      K'/Real.sqrt M,(3*K'*τ'/2)/Real.sqrt M]
    let window : Fin 4 → ℝ :=
      ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
    let D := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
      Real.sqrt (U*(Q:ℝ)^3)
    (∀ j, |Y j-Y' j| ≤ 2*window j) →
    ∃ α β γ δ e₁ e₂ : ℤ,
      α*δ-β*γ=1 ∧ α*a+β*q=a' ∧ γ*a+δ*q=q' ∧
      |(γ:ℝ)| ≤ (q:ℝ)*q'/(6*(M:ℝ)^2) ∧
      let G₁ := 2*y-2*(δ:ℝ)*x-(γ:ℝ)*iteratedDeriv 1 f x
      let G₂ := iteratedDeriv 1 f y-2*(β:ℝ)*x-(α:ℝ)*iteratedDeriv 1 f x
      |G₁-e₁| ≤ (q':ℝ)/(6*(M:ℝ))+|(γ:ℝ)|/q+3+3*|(γ:ℝ)| *U/4 ∧
      |(G₂-e₂)-((a':ℝ)/q')*(G₁-e₁)| ≤ 2*D/q'+9*U/4 ∧
      ∃ e : ℤ, |((q':ℝ)*deriv f y-2*(a':ℝ)*y)-
        ((q:ℝ)*deriv f x-2*(a:ℝ)*x)-e| ≤ 2*D+9*(q':ℝ)*U/4 := by
  intro μ μ' ℓ ℓ' b b' τ τ' K K' Y Y' window D hnear
  have hμU : μ ≤ U := by
    have hh := (le_abs_self _).trans (hb m (Or.inl right_mem_uIcc))
    dsimp only [μ]
    linarith only [hh]
  obtain ⟨α,β,γ,δ,e₁,e₂,hdet,ha,hden,hγ,h₁,h₂⟩ :=
    actual_source_affine_lattice_strip M q q' Q a a' r r' m n hq hq' hqQ har har'
      (by dsimp only [μ]; positivity) (by dsimp only [μ']; positivity) hμU p p' hnear
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq'r : 0 < (q':ℝ) := by exact_mod_cast hq'
  have hdetR : (α:ℝ)*δ-(β:ℝ)*γ=1 := by exact_mod_cast hdet
  have haR : (α:ℝ)*a+(β:ℝ)*q=a' := by exact_mod_cast ha
  have hdenR : (γ:ℝ)*a+(δ:ℝ)*q=q' := by exact_mod_cast hden
  let v := (a:ℝ)/q
  let w := (a':ℝ)/q'
  let t := (q':ℝ)/q
  have ht : t=(γ:ℝ)*v+δ := by
    dsimp only [t,v]
    field_simp
    nlinarith only [hdenR]
  have hmap : w*t=(α:ℝ)*v+β := by
    dsimp only [w,t,v]
    field_simp
    nlinarith only [haR]
  have htlo : (1:ℝ)/2 ≤ t := by
    apply (le_div_iff₀ hqr).mpr
    have hh : (q:ℝ) ≤ 2*q' := by exact_mod_cast hqratio
    linarith only [hh]
  have hthi : t ≤ 2 := by
    apply (div_le_iff₀ hqr).mpr
    exact_mod_cast hqratio'
  have hround := rounded_displacement_strip f hf hb hm hn
    (by change iteratedDeriv 2 f x=2*((a:ℝ)/q); linarith only [hx])
    (by change iteratedDeriv 2 f y=2*((a':ℝ)/q'); linarith only [hy])
    hdetR ht hmap htlo hthi
  let F₁ := 2*(n:ℝ)-2*(δ:ℝ)*m-(γ:ℝ)*ℓ
  let F₂ := ℓ'-2*(β:ℝ)*m-(α:ℝ)*ℓ
  let G₁ := 2*y-2*(δ:ℝ)*x-(γ:ℝ)*iteratedDeriv 1 f x
  let G₂ := iteratedDeriv 1 f y-2*(β:ℝ)*x-(α:ℝ)*iteratedDeriv 1 f x
  change |F₁-G₁| ≤ 3+3*|(γ:ℝ)| *U/4 ∧
    |(F₂-G₂)-w*(F₁-G₁)| ≤ 9*U/4 at hround
  change |F₁-e₁| ≤ _ at h₁
  change |(F₂-e₂)-w*(F₁-e₁)| ≤ _ at h₂
  have hG₂ : |(G₂-e₂)-w*(G₁-e₁)| ≤ 2*D/q'+9*U/4 := by
    calc
      _ = |((F₂-e₂)-w*(F₁-e₁))-((F₂-G₂)-w*(F₁-G₁))| := by congr 1; ring
      _ ≤ |(F₂-e₂)-w*(F₁-e₁)|+|(F₂-G₂)-w*(F₁-G₁)| := abs_sub _ _
      _ ≤ _ := add_le_add h₂ hround.2
  refine ⟨α,β,γ,δ,e₁,e₂,hdet,ha,hden,hγ,?_,hG₂,?_⟩
  · change |G₁-e₁| ≤ _
    calc
      _ = |(F₁-e₁)-(F₁-G₁)| := by congr 1; ring
      _ ≤ |F₁-e₁|+|F₁-G₁| := abs_sub _ _
      _ ≤ _ := by linarith only [h₁,hround.1]
  · obtain ⟨e,he⟩ := legendre_resonance_of_integer_strip f a a' q q' α β γ δ e₁ e₂
      (by exact_mod_cast hq') hdet ha hden
      (by simpa only [G₁,G₂,w,iteratedDeriv_one,Int.cast_natCast] using hG₂)
    refine ⟨e,?_⟩
    simp only [Int.cast_natCast] at he
    exact he.trans_eq (by field_simp)

private theorem short_curve_integer_label_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F G w : ι → ℝ) (u v : ι → ℤ) (a q : ℤ)
    {H W J A B : ℝ} (hq : 0 < q) (hcop : IsCoprime q a)
    (hJ : 0 ≤ J)
    (hfirst : ∀ i∈S, |F i-u i| ≤ H)
    (hsecond : ∀ i∈S, |(G i-v i)-w i*(F i-u i)| ≤ W)
    (htilt : ∀ i∈S, |w i-(a:ℝ)/q| ≤ J)
    (hvariation : ∀ i∈S, ∀ j∈S, |F i-F j| ≤ A ∧
      |(G i-((a:ℝ)/q)*F i)-(G j-((a:ℝ)/q)*F j)| ≤ B)
    (hwidth : A+2*H < (q:ℝ))
    (hheight : B+2*(W+J*H) < 1/(q:ℝ)) :
    (S.image (fun i => (u i,v i))).card ≤ 1 := by
  classical
  let θ := (a:ℝ)/q
  have htrans i (hi : i∈S) : |(G i-v i)-θ*(F i-u i)| ≤ W+J*H := by
    calc
      _ = |((G i-v i)-w i*(F i-u i))+(w i-θ)*(F i-u i)| := by congr 1; ring
      _ ≤ |(G i-v i)-w i*(F i-u i)|+|(w i-θ)*(F i-u i)| := abs_add_le _ _
      _ = |(G i-v i)-w i*(F i-u i)|+|w i-θ| *|F i-u i| := by rw [abs_mul]
      _ ≤ W+J*H := add_le_add (hsecond i hi)
        (mul_le_mul (htilt i hi) (hfirst i hi) (abs_nonneg _) hJ)
  have heq i (hi : i∈S) j (hj : j∈S) : u i=u j ∧ v i=v j := by
    apply rational_strip_unique a q (u i) (v i) (u j) (v j) hq hcop
    · have hh : |(u i:ℝ)-u j| ≤ A+2*H := by
        calc
          _ = |(F i-F j)-(F i-u i)+(F j-u j)| := by congr 1; ring
          _ ≤ |(F i-F j)-(F i-u i)|+|F j-u j| := abs_add_le _ _
          _ ≤ (|F i-F j|+|F i-u i|)+|F j-u j| := by
            have ht := abs_sub (F i-F j) (F i-u i)
            linarith only [ht]
          _ ≤ A+2*H := by linarith only [(hvariation i hi j hj).1,hfirst i hi,hfirst j hj]
      exact_mod_cast hh.trans_lt hwidth
    · have hh : |((v i:ℝ)-θ*u i)-((v j:ℝ)-θ*u j)| ≤ B+2*(W+J*H) := by
        calc
          _ = |((G i-θ*F i)-(G j-θ*F j))-
              ((G i-v i)-θ*(F i-u i))+((G j-v j)-θ*(F j-u j))| := by congr 1; ring
          _ ≤ |((G i-θ*F i)-(G j-θ*F j))-((G i-v i)-θ*(F i-u i))|+
              |(G j-v j)-θ*(F j-u j)| := abs_add_le _ _
          _ ≤ (|(G i-θ*F i)-(G j-θ*F j)|+|(G i-v i)-θ*(F i-u i)|)+
              |(G j-v j)-θ*(F j-u j)| := by
            have ht := abs_sub ((G i-θ*F i)-(G j-θ*F j)) ((G i-v i)-θ*(F i-u i))
            linarith only [ht]
          _ ≤ B+2*(W+J*H) := by linarith only [(hvariation i hi j hj).2,htrans i hi,htrans j hj]
      exact hh.trans_lt hheight
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  obtain ⟨i,hi⟩ := hS
  have hsub : S.image (fun j => (u j,v j)) ⊆ {(u i,v i)} := by
    intro z hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_singleton.mpr (Prod.ext (heq j hj i hi).1 (heq j hj i hi).2)
  simpa only [Finset.card_singleton] using Finset.card_le_card hsub

private theorem source_resonance_residual_interval
    (f : ℝ → ℝ) {A B L l r : ℝ} (hL : 0 < L) (hlr : l ≤ r)
    (hf : ∀ z∈Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z∈Ioo A B, L ≤ iteratedDeriv 3 f z)
    (hfour : ∀ z∈Ioo A B, |iteratedDeriv 4 f z| ≤ L^2/16)
    (a b γ d : ℝ) (hdet : a*d-b*γ=1) (hγ : 1 ≤ |γ|) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let g := fun v => iteratedDeriv 3 f (c v)
    let t := fun v => γ*v+d
    let w := fun v => (a*v+b)/t v
    let R := fun v => g (w v)*(t v)^3-g v
    (∀ v∈Icc l r, v∈h '' Ioo A B ∧ w v∈h '' Ioo A B ∧ 1/2 ≤ t v ∧ t v ≤ 2) →
    ∀ v∈Icc l r, |R v| ≤ max |R l| |R r| := by
  intro h c g t w R hdom
  let gp := fun v => 2*iteratedDeriv 4 f (c v)/iteratedDeriv 3 f (c v)
  have hp := inverse_curvature_derivative f hL hf hthree
  have hg v (hv : v∈h '' Ioo A B) :
      HasDerivAt g (gp v) v ∧ L ≤ g v ∧ |gp v| ≤ L/8 := by
    have hc := hp.2 v hv
    have hpos : 0 < iteratedDeriv 3 f (c v) := hL.trans_le (hthree _ hc.2.1)
    refine ⟨?_,hthree _ hc.2.1,?_⟩
    · have hd := (contDiffAt_iteratedDeriv_finite (n:=1) (j:=3)
        (hf _ hc.2.1)).differentiableAt_one.hasDerivAt
      rw [←iteratedDeriv_succ] at hd
      convert hd.comp v hc.2.2.1 using 1
      dsimp only [gp]
      ring
    · dsimp only [gp]
      rw [abs_div,abs_mul,abs_of_pos hpos,abs_of_pos (by norm_num : (0:ℝ)<2)]
      apply (div_le_iff₀ hpos).mpr
      have hs := mul_le_mul_of_nonneg_left (hthree _ hc.2.1) hL.le
      nlinarith only [hs,hfour _ hc.2.1]
  let Rp := fun v => gp (w v)*t v+3*γ*g (w v)*(t v)^2-gp v
  have hder v (hv : v∈Icc l r) : HasDerivAt R (Rp v) v := by
    have ht : t v ≠ 0 := by have hh := (hdom v hv).2.2.1; linarith only [hh]
    have htd := ((hasDerivAt_id v).const_mul γ).add_const d
    have hwd : HasDerivAt w (1/(t v)^2) v := by
      have hd := (((hasDerivAt_id v).const_mul a).add_const b).div htd ht
      simp only [mul_one,id_eq] at hd
      convert hd using 1
      congr 1
      nlinarith only [hdet]
    have hd := ((((hg _ (hdom v hv).2.1).1.comp v hwd).mul (htd.pow 3)).sub
      (hg _ (hdom v hv).1).1)
    simp only [mul_one] at hd
    convert hd using 1
    dsimp only [Rp]
    change gp (w v)*t v+3*γ*g (w v)*t v^2-gp v =
      gp (w v)*(1/(t v)^2)*(t v)^3+g (w v)*(3*(t v)^2*γ)-gp v
    field_simp
  have herr v (hv : v∈Icc l r) : |gp (w v)*t v-gp v| ≤ 3*L/8 := by
    have ht0 : 0 ≤ t v := by have hh := (hdom v hv).2.2.1; linarith only [hh]
    calc
      _ ≤ |gp (w v)*t v|+|gp v| := abs_sub _ _
      _ = |gp (w v)| *t v+|gp v| := by rw [abs_mul,abs_of_nonneg ht0]
      _ ≤ (L/8)*2+L/8 := by
        gcongr
        · exact (hg _ (hdom v hv).2.1).2.2
        · exact (hdom v hv).2.2.2
        · exact (hg _ (hdom v hv).1).2.2
      _ = _ := by ring
  have hmain v (hv : v∈Icc l r) : 3*L/4 ≤ 3*g (w v)*(t v)^2 := by
    have hsq : (1:ℝ)/4 ≤ (t v)^2 := by nlinarith only [(hdom v hv).2.2.1]
    have hh := mul_le_mul (hg _ (hdom v hv).2.1).2.1 hsq
      (by norm_num : (0:ℝ) ≤ 1/4) (hL.le.trans (hg _ (hdom v hv).2.1).2.1)
    nlinarith only [hh]
  have hmono : MonotoneOn R (Icc l r) ∨ AntitoneOn R (Icc l r) := by
    rcases le_total 0 γ with hpos | hneg
    · left
      have hγ1 : 1 ≤ γ := by rwa [abs_of_nonneg hpos] at hγ
      apply monotoneOn_of_deriv_nonneg (convex_Icc l r)
      · exact fun v hv => (hder v hv).continuousAt.continuousWithinAt
      · exact fun v hv => (hder v (interior_subset hv)).differentiableAt.differentiableWithinAt
      · intro v hv
        have hv' := interior_subset hv
        rw [(hder v hv').deriv]
        have hm := hmain v hv'
        have he := (abs_le.mp (herr v hv')).1
        have hh := mul_le_mul_of_nonneg_right hγ1 (show 0 ≤ 3*g (w v)*(t v)^2 by linarith only [hm,hL])
        dsimp only [Rp]
        nlinarith only [hm,he,hh,hL]
    · right
      have hγ1 : γ ≤ -1 := by rw [abs_of_nonpos hneg] at hγ; linarith only [hγ]
      apply antitoneOn_of_deriv_nonpos (convex_Icc l r)
      · exact fun v hv => (hder v hv).continuousAt.continuousWithinAt
      · exact fun v hv => (hder v (interior_subset hv)).differentiableAt.differentiableWithinAt
      · intro v hv
        have hv' := interior_subset hv
        rw [(hder v hv').deriv]
        have hm := hmain v hv'
        have he := (abs_le.mp (herr v hv')).2
        have hh := mul_le_mul_of_nonneg_right hγ1 (show 0 ≤ 3*g (w v)*(t v)^2 by linarith only [hm,hL])
        dsimp only [Rp]
        nlinarith only [hm,he,hh,hL]
  intro v hv
  have hleft : -max |R l| |R r| ≤ R l :=
    (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
  have hright : R r ≤ max |R l| |R r| := (le_abs_self _).trans (le_max_right _ _)
  have hleft' : R l ≤ max |R l| |R r| := (le_abs_self _).trans (le_max_left _ _)
  have hright' : -max |R l| |R r| ≤ R r :=
    (neg_le_neg (le_max_right _ _)).trans (neg_abs_le _)
  rcases hmono with hmono | hmono
  · exact abs_le.mpr ⟨hleft.trans (hmono ⟨le_rfl,hlr⟩ hv hv.1),
      (hmono hv ⟨hlr,le_rfl⟩ hv.2).trans hright⟩
  · exact abs_le.mpr ⟨hright'.trans (hmono hv ⟨hlr,le_rfl⟩ hv.2),
      (hmono ⟨le_rfl,hlr⟩ hv hv.1).trans hleft'⟩

private theorem source_resonance_short_block_label_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ℝ → ℝ) (z : ι → ℝ) (u v : ι → ℤ)
    {A B L l r E H W : ℝ} (hL : 0 < L) (hlr : l ≤ r)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x)
    (hfour : ∀ x∈Ioo A B, |iteratedDeriv 4 f x| ≤ L^2/16)
    (a b γ d : ℝ) (hdet : a*d-b*γ=1) (hγ : 1 ≤ |γ|)
    (p₀ q₀ : ℤ) (hq₀ : 0 < q₀) (hcop : IsCoprime q₀ p₀)
    (hz : ∀ i∈S, z i∈Icc l r) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let t := fun x => γ*x+d
    let w := fun x => (a*x+b)/t x
    let F := fun x => 2*c (w x)-2*d*c x-γ*deriv f (c x)
    let G := fun x => deriv f (c (w x))-2*b*c x-a*deriv f (c x)
    let R := fun x => iteratedDeriv 3 f (c (w x))*(t x)^3-iteratedDeriv 3 f (c x)
    (∀ x∈Icc l r, x∈h '' Ioo A B ∧ w x∈h '' Ioo A B ∧ 1/2 ≤ t x ∧ t x ≤ 2) →
    w l=(p₀:ℝ)/q₀ →
    |R l| ≤ E → |R r| ≤ E →
    (∀ i∈S, |F (z i)-u i| ≤ H) →
    (∀ i∈S, |(G (z i)-v i)-w (z i)*(F (z i)-u i)| ≤ W) →
    16*E*(r-l)/L^2+2*H < (q₀:ℝ) →
    64*E*(r-l)^2/L^2+2*(W+4*(r-l)*H) < 1/(q₀:ℝ) →
    (S.image (fun i => (u i,v i))).card ≤ 1 := by
  intro h c t w F G R hdom hbase hleft hright hfirst hsecond hwidth hheight
  have hE : 0 ≤ E := (abs_nonneg _).trans hleft
  have hres x (hx : x∈Icc l r) : |R x| ≤ E :=
    (source_resonance_residual_interval f hL hlr hf hthree hfour a b γ d hdet hγ hdom x hx).trans
      (max_le hleft hright)
  have hwder x (hx : x∈Icc l r) : HasDerivAt w (1/(t x)^2) x := by
    have ht : t x ≠ 0 := by have hh := (hdom x hx).2.2.1; linarith only [hh]
    have hh := (((hasDerivAt_id x).const_mul a).add_const b).div
      (((hasDerivAt_id x).const_mul γ).add_const d) ht
    simp only [mul_one,id_eq] at hh
    convert hh using 1
    congr 1
    nlinarith only [hdet]
  have hwbound x (hx : x∈Icc l r) : ‖1/(t x)^2‖ ≤ (4:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/(t x)^2)]
    have ht := (hdom x hx).2.2.1
    apply (div_le_iff₀ (sq_pos_of_ne_zero (by linarith only [ht]))).mpr
    nlinarith only [ht]
  have htilt i (hi : i∈S) : |w (z i)-(p₀:ℝ)/q₀| ≤ 4*(r-l) := by
    rw [←hbase]
    have hh := (convex_Icc l r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hwder x hx).hasDerivWithinAt) hwbound (hz i hi) ⟨le_rfl,hlr⟩
    simp only [Real.norm_eq_abs,abs_sub_comm (w l),abs_sub_comm l] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr (hz i hi).1)] at hh
    exact hh.trans (by linarith only [(hz i hi).2])
  apply short_curve_integer_label_count S (fun i => F (z i)) (fun i => G (z i))
    (fun i => w (z i)) u v p₀ q₀ hq₀ hcop
    (by positivity : 0 ≤ 4*(r-l)) hfirst hsecond htilt ?_ hwidth hheight
  intro i hi j hj
  have hh := resonance_displacement_short_box f hL hlr hf hthree a b γ d hdet
    (fun x hx => ⟨(hdom x hx).1,(hdom x hx).2.1,(hdom x hx).2.2.1⟩) hres
    (z i) (hz i hi) (z j) (hz j hj)
  have hdiff : |z i-z j| ≤ r-l := abs_le.mpr ⟨by linarith only [(hz i hi).1,(hz j hj).2],
    by linarith only [(hz i hi).2,(hz j hj).1]⟩
  let F₁ := fun x => c (w x)-d*c x-γ*(deriv f (c x)/2)
  let F₂ := fun x => deriv f (c (w x))/2-b*c x-a*(deriv f (c x)/2)
  change |F₁ (z i)-F₁ (z j)| ≤ _ ∧
    |(F₂ (z i)-w l*F₁ (z i))-(F₂ (z j)-w l*F₁ (z j))| ≤ _ at hh
  constructor
  · have he : F (z i)-F (z j)=2*(F₁ (z i)-F₁ (z j)) := by dsimp only [F,F₁]; ring
    rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hb := hh.1.trans (mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 8*E/L^2))
    convert mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2) using 1
    ring
  · rw [←hbase]
    have he : (G (z i)-w l*F (z i))-(G (z j)-w l*F (z j))=
        2*((F₂ (z i)-w l*F₁ (z i))-(F₂ (z j)-w l*F₁ (z j))) := by
      dsimp only [G,F,F₁,F₂]
      ring
    rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hb := hh.2.trans (mul_le_mul_of_nonneg_left hdiff
      (by positivity : 0 ≤ 32*E*(r-l)/L^2))
    convert mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2) using 1
    ring

private theorem shifted_legendre_phase_derivatives
    (f : ℝ → ℝ) {A B L : ℝ} (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x)
    {q k z : ℝ} (hq : q ≠ 0) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let Φ := fun v => deriv f (c v)-2*v*c v
    let Ψ := fun s => q*(Φ (s/q+k)-Φ (s/q))
    let Ψp := fun s => -2*(c (s/q+k)-c (s/q))
    z/q∈h '' Ioo A B → z/q+k∈h '' Ioo A B →
    HasDerivAt Ψ (Ψp z) z ∧
    HasDerivAt Ψp
      (4*(iteratedDeriv 3 f (c (z/q+k))-iteratedDeriv 3 f (c (z/q)))/
        (q*iteratedDeriv 3 f (c (z/q))*iteratedDeriv 3 f (c (z/q+k)))) z := by
  intro h c Φ Ψ Ψp hz hzk
  have hp := inverse_curvature_derivative f hL hf hthree
  have hΦ v (hv : v∈h '' Ioo A B) : HasDerivAt Φ (-2*c v) v := by
    have hc := hp.2 v hv
    have hd := ((hc.2.2.2.sub ((hasDerivAt_id v).mul hc.2.2.1)).const_mul 2)
    change HasDerivAt (fun s => 2*(deriv f (c s)/2-s*c s))
      (2*(2*v/iteratedDeriv 3 f (c v)-(1*c v+v*(2/iteratedDeriv 3 f (c v))))) v at hd
    convert hd using 1
    · funext s
      dsimp only [Φ]
      ring
    · ring
  have hscale : HasDerivAt (fun s : ℝ => s/q) (1/q) z := (hasDerivAt_id z).div_const q
  have hscale' : HasDerivAt (fun s : ℝ => s/q+k) (1/q) z := hscale.add_const k
  have hcx := hp.2 (z/q) hz
  have hcy := hp.2 (z/q+k) hzk
  have hxpos : 0 < iteratedDeriv 3 f (c (z/q)) := hL.trans_le (hthree _ hcx.2.1)
  have hypos : 0 < iteratedDeriv 3 f (c (z/q+k)) := hL.trans_le (hthree _ hcy.2.1)
  constructor
  · have hh := (((hΦ _ hzk).comp z hscale').sub ((hΦ _ hz).comp z hscale)).const_mul q
    convert hh using 1
    dsimp only [Ψp]
    field_simp
    ring
  · have hh := ((hcy.2.2.1.comp z hscale').sub (hcx.2.2.1.comp z hscale)).const_mul (-2)
    let X := iteratedDeriv 3 f (c (z/q))
    let Y := iteratedDeriv 3 f (c (z/q+k))
    change 0 < X at hxpos
    change 0 < Y at hypos
    change HasDerivAt Ψp (-2*(2/Y*(1/q)-2/X*(1/q))) z at hh
    change HasDerivAt Ψp (4*(Y-X)/(q*X*Y)) z
    convert hh using 1
    field_simp [hxpos.ne',hypos.ne']
    ring

#print axioms shifted_legendre_phase_derivatives

-- Exact residual for the tested borrowed-window/old-triangular budget.
-- Exact residual for the tested borrowed-window/old-triangular budget.
private theorem shifted_legendre_negative_curvature_bounds
    (f : ℝ → ℝ) {A B L U F lam x y q k : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hq : 0 < q)
    (hxy : x < y) (hx : x∈Ioo A B) (hy : y∈Ioo A B)
    (hf : ∀ z∈Ioo A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z∈Ioo A B, L ≤ iteratedDeriv 3 f z ∧ iteratedDeriv 3 f z ≤ 6*U)
    (hfour : ∀ z∈Ioo A B, -F ≤ iteratedDeriv 4 f z ∧ iteratedDeriv 4 f z ≤ -lam)
    (hlevel : iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2=k) :
    -(8*F*k/(q*L^3)) ≤
      4*(iteratedDeriv 3 f y-iteratedDeriv 3 f x)/
        (q*iteratedDeriv 3 f x*iteratedDeriv 3 f y) ∧
    4*(iteratedDeriv 3 f y-iteratedDeriv 3 f x)/
        (q*iteratedDeriv 3 f x*iteratedDeriv 3 f y) ≤
      -(lam*k/(27*q*U^3)) := by
  have hsub z (hz : z∈Icc x y) : z∈Ioo A B := ⟨hx.1.trans_le hz.1,hz.2.trans_lt hy.2⟩
  have hd₂ z (hz : z∈Icc x y) :
      HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f z) z := by
    have hh := (contDiffAt_iteratedDeriv_finite (n:=2) (j:=2)
      (hf z (hsub z hz))).differentiableAt (by norm_num)
    simpa only [iteratedDeriv_succ] using hh.hasDerivAt
  have hd₃ z (hz : z∈Icc x y) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f z) z := by
    have hh := (contDiffAt_iteratedDeriv_finite (n:=1) (j:=3)
      (hf z (hsub z hz))).differentiableAt_one
    simpa only [iteratedDeriv_succ] using hh.hasDerivAt
  obtain ⟨s,hs,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 2 f) (iteratedDeriv 3 f) hxy
    (fun z hz => (hd₂ z hz).continuousAt.continuousWithinAt)
    (fun z hz => hd₂ z ⟨hz.1.le,hz.2.le⟩)
  have hΔ : 0 < y-x := sub_pos.mpr hxy
  have he₂ : iteratedDeriv 3 f s*(y-x)=2*k := by
    have hh := (eq_div_iff hΔ.ne').mp he
    nlinarith only [hh,hlevel]
  have hsI := hsub s ⟨hs.1.le,hs.2.le⟩
  have hgaplo : L*(y-x) ≤ 2*k := by
    rw [←he₂]
    exact mul_le_mul_of_nonneg_right (hthree s hsI).1 hΔ.le
  have hgaphi : 2*k ≤ 6*U*(y-x) := by
    rw [←he₂]
    exact mul_le_mul_of_nonneg_right (hthree s hsI).2 hΔ.le
  have hk : 0 < k := by have hh := mul_pos hL hΔ; linarith only [hh,hgaplo]
  have hU : 0 < U := by
    have hh := hthree x hx
    linarith only [hh.1,hh.2,hL]
  have hF : 0 < F := by have hh := hfour x hx; linarith only [hh.1,hh.2,hlam]
  obtain ⟨s',hs',he'⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f) (iteratedDeriv 4 f) hxy
    (fun z hz => (hd₃ z hz).continuousAt.continuousWithinAt)
    (fun z hz => hd₃ z ⟨hz.1.le,hz.2.le⟩)
  have he₃ := (eq_div_iff hΔ.ne').mp he'
  have hs'I := hsub s' ⟨hs'.1.le,hs'.2.le⟩
  let X := iteratedDeriv 3 f x
  let Y := iteratedDeriv 3 f y
  have hX : 0 < X := hL.trans_le (hthree x hx).1
  have hY : 0 < Y := hL.trans_le (hthree y hy).1
  have hdlo : lam*(y-x) ≤ X-Y := by
    have hh := mul_le_mul_of_nonneg_right (hfour s' hs'I).2 hΔ.le
    dsimp only [X,Y]
    nlinarith only [hh,he₃]
  have hdhi : X-Y ≤ F*(y-x) := by
    have hh := mul_le_mul_of_nonneg_right (hfour s' hs'I).1 hΔ.le
    dsimp only [X,Y]
    nlinarith only [hh,he₃]
  have hnlo : lam*k/(3*U) ≤ X-Y := by
    apply (div_le_iff₀ (by positivity : 0 < 3*U)).mpr
    have hh := mul_le_mul_of_nonneg_left hgaphi hlam.le
    have hh' := mul_le_mul_of_nonneg_left hdlo hU.le
    nlinarith only [hh,hh']
  have hnhi : X-Y ≤ 2*F*k/L := by
    apply (le_div_iff₀ hL).mpr
    have hh := mul_le_mul_of_nonneg_left hgaplo hF.le
    have hh' := mul_le_mul_of_nonneg_left hdhi hL.le
    nlinarith only [hh,hh']
  have hdenlo : q*L^2 ≤ q*X*Y := by
    have hh := mul_le_mul (hthree x hx).1 (hthree y hy).1 hL.le hX.le
    have hh' := mul_le_mul_of_nonneg_left hh hq.le
    nlinarith only [hh']
  have hdenhi : q*X*Y ≤ 36*q*U^2 := by
    have hh := mul_le_mul (hthree x hx).2 (hthree y hy).2 hY.le (by positivity : 0 ≤ 6*U)
    have hh' := mul_le_mul_of_nonneg_left hh hq.le
    nlinarith only [hh']
  have hlow : lam*k/(27*q*U^3) ≤ 4*(X-Y)/(q*X*Y) := by
    calc
      _ = (4*(lam*k/(3*U)))/(36*q*U^2) := by field_simp; ring
      _ ≤ 4*(X-Y)/(q*X*Y) := div_le_div₀
        (by have hh := mul_pos hlam hΔ; linarith only [hh,hdlo])
        (mul_le_mul_of_nonneg_left hnlo (by norm_num)) (by positivity) hdenhi
  have hhigh : 4*(X-Y)/(q*X*Y) ≤ 8*F*k/(q*L^3) := by
    calc
      _ ≤ (4*(2*F*k/L))/(q*L^2) := div_le_div₀
        (by positivity)
        (mul_le_mul_of_nonneg_left hnhi (by norm_num)) (by positivity) hdenlo
      _ = _ := by field_simp; ring
  change -(8*F*k/(q*L^3)) ≤ 4*(Y-X)/(q*X*Y) ∧
    4*(Y-X)/(q*X*Y) ≤ -(lam*k/(27*q*U^3))
  have heq : 4*(Y-X)/(q*X*Y)= -(4*(X-Y)/(q*X*Y)) := by ring
  rw [heq]
  constructor <;> linarith only [hlow,hhigh]

#print axioms shifted_legendre_negative_curvature_bounds

private theorem second_derivative_all_positive_frequencies
    (F F' F'' : ℝ → ℝ) (A : ℝ) (N : ℕ) {C μ r : ℝ}
    (hC : 1 ≤ C) (hμ : 0 < μ) (hr : 0 < r)
    (hF : ∀ x∈Icc A (A+N), HasDerivAt F (F' x) x)
    (hF' : ∀ x∈Icc A (A+N), HasDerivAt F' (F'' x) x)
    (hlo : ∀ x∈Icc A (A+N), -(C*μ) ≤ F'' x)
    (hhi : ∀ x∈Icc A (A+N), F'' x ≤ -μ) :
    ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter (r*F (A+n))‖ ≤
      12*(C*N*Real.sqrt (r*μ)+2/Real.sqrt (r*μ)) := by
  by_cases hsmall : r*μ ≤ 1
  · apply continuous_second_derivative_negative_range_bound
      (fun x => r*F x) (fun x => r*F' x) (fun x => r*F'' x) A N
      (by linarith only [hC]) (mul_pos hr hμ) hsmall
      (fun x hx => (hF x hx).const_mul r) (fun x hx => (hF' x hx).const_mul r)
    · intro x hx
      have hh := mul_le_mul_of_nonneg_left (hlo x hx) hr.le
      nlinarith only [hh]
    · intro x hx
      have hh := mul_le_mul_of_nonneg_left (hhi x hx) hr.le
      nlinarith only [hh]
  · have hsqrt : 1 ≤ Real.sqrt (r*μ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (le_of_lt (lt_of_not_ge hsmall))
    have htriv : ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter (r*F (A+n))‖ ≤ N := by
      calc
        _ ≤ ∑ n∈Finset.range N, ‖GafniTao.fordAdditiveCharacter (r*F (A+n))‖ := norm_sum_le _ _
        _ = _ := by simp [GafniTao.fordAdditiveCharacter,Complex.norm_exp]
    have hprod : 1 ≤ C*Real.sqrt (r*μ) := by nlinarith only [mul_le_mul hC hsqrt (by norm_num) (by linarith only [hC])]
    have hN := mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg N : (0:ℝ) ≤ N)
    have hinv : 0 ≤ 2/Real.sqrt (r*μ) := by positivity
    nlinarith only [htriv,hN,hinv,(Nat.cast_nonneg N : (0:ℝ) ≤ N)]

#print axioms second_derivative_all_positive_frequencies


private theorem shifted_legendre_second_derivative_sum
    (f : ℝ → ℝ) {A B L U F lam q k a₀ r : ℝ} (N : ℕ)
    (hL : 0 < L) (hU : 0 < U) (hF : 0 < F)
    (hlam : 0 < lam) (hq : 0 < q) (hk : 0 < k) (hr : 0 < r)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hfour : ∀ x∈Ioo A B, -F ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ -lam) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let Φ := fun v => deriv f (c v)-2*v*c v
    let Ψ := fun s => q*(Φ (s/q+k)-Φ (s/q))
    let μ := lam*k/(27*q*U^3)
    let C := 216*F*U^3/(lam*L^3)
    (∀ s∈Icc a₀ (a₀+N), s/q∈h '' Ioo A B ∧ s/q+k∈h '' Ioo A B) →
    ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter (r*Ψ (a₀+n))‖ ≤
      12*(C*N*Real.sqrt (r*μ)+2/Real.sqrt (r*μ)) := by
  intro h c Φ Ψ μ C hdom
  let Ψp := fun s => -2*(c (s/q+k)-c (s/q))
  let Ψpp := fun s => 4*(iteratedDeriv 3 f (c (s/q+k))-iteratedDeriv 3 f (c (s/q)))/
    (q*iteratedDeriv 3 f (c (s/q))*iteratedDeriv 3 f (c (s/q+k)))
  have hp := inverse_curvature_derivative f hL hf (fun x hx => (hthree x hx).1)
  have hhder x (hx : x∈Ioo A B) : HasDerivAt h (iteratedDeriv 3 f x/2) x := by
    have hd := (contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf x hx)).differentiableAt (by norm_num)
    simpa only [h,iteratedDeriv_succ] using hd.hasDerivAt.div_const 2
  have hmono : StrictMonoOn h (Ioo A B) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo A B)
    · exact fun x hx => (hhder x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x∈Ioo A B := by simpa only [interior_Ioo] using hx
      rw [(hhder x hx').deriv]
      have hh := (hthree x hx').1
      linarith only [hh,hL]
  have hd s (hs : s∈Icc a₀ (a₀+N)) :
      HasDerivAt Ψ (Ψp s) s ∧ HasDerivAt Ψp (Ψpp s) s :=
    shifted_legendre_phase_derivatives f hL hf (fun x hx => (hthree x hx).1)
      hq.ne' (hdom s hs).1 (hdom s hs).2
  have hb s (hs : s∈Icc a₀ (a₀+N)) : -(C*μ) ≤ Ψpp s ∧ Ψpp s ≤ -μ := by
    have hx := hp.2 (s/q) (hdom s hs).1
    have hy := hp.2 (s/q+k) (hdom s hs).2
    change h (c (s/q))=s/q ∧ _ at hx
    change h (c (s/q+k))=s/q+k ∧ _ at hy
    have hxy : c (s/q) < c (s/q+k) := by
      by_contra hnot
      have hh := hmono.monotoneOn hy.2.1 hx.2.1 (le_of_not_gt hnot)
      rw [hx.1,hy.1] at hh
      linarith only [hh,hk]
    have hlevel : iteratedDeriv 2 f (c (s/q+k))/2-iteratedDeriv 2 f (c (s/q))/2=k := by
      change h (c (s/q+k))-h (c (s/q))=k
      rw [hx.1,hy.1]
      ring
    have hh := shifted_legendre_negative_curvature_bounds f hL hlam hq hxy hx.2.1 hy.2.1
      hf hthree hfour hlevel
    have hCμ : C*μ=8*F*k/(q*L^3) := by dsimp only [C,μ]; field_simp; ring
    rw [hCμ]
    exact hh
  have hC1 : 1 ≤ C := by
    have hpt := (hp.2 (a₀/q) (hdom a₀ ⟨le_rfl,le_add_of_nonneg_right (Nat.cast_nonneg N)⟩).1).2.1
    have ht := hthree _ hpt
    have hf4 := hfour _ hpt
    have hLU : L ≤ 6*U := ht.1.trans ht.2
    have hcube := pow_le_pow_left₀ hL.le hLU 3
    have hmul := mul_le_mul_of_nonneg_left hcube hlam.le
    have hFmul := mul_le_mul_of_nonneg_right (show lam ≤ F by linarith only [hf4.1,hf4.2])
      (show 0 ≤ 216*U^3 by positivity)
    apply (le_div_iff₀ (by positivity : 0 < lam*L^3)).mpr
    nlinarith only [hmul,hFmul]
  exact second_derivative_all_positive_frequencies Ψ Ψp Ψpp a₀ N
    hC1 (by dsimp only [μ]; positivity) hr
    (fun s hs => (hd s hs).1) (fun s hs => (hd s hs).2)
    (fun s hs => (hb s hs).1) (fun s hs => (hb s hs).2)

#print axioms shifted_legendre_second_derivative_sum

private theorem finite_near_integer_count_fourier
    {ι : Type*} [DecidableEq ι] (S T : Finset ι) (φ : ι → ℝ)
    {B : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2) (hTS : T ⊆ S)
    (hnear : ∀ i∈T, ∃ e : ℤ, |φ i-(e:ℝ)| ≤ B/2) :
    (T.card:ℝ) ≤ 2*∑' r : ℤ, GafniTao.heathBrownHatFourierCoefficient B r *
      ‖∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)‖ := by
  let c := GafniTao.heathBrownHatFourierCoefficient B
  let Z := fun r : ℤ => ∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)
  have hc r : 0 ≤ c r := GafniTao.heathBrownHatFourierCoefficient_nonneg hB.le r
  have hcS : Summable c := by
    have hh := GafniTao.summable_norm_heathBrownHatFourierTerm hB 0
    simpa only [mul_zero, GafniTao.fordAdditiveCharacter, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (GafniTao.heathBrownHatFourierCoefficient_nonneg hB.le _)] using hh
  have hZ r : ‖Z r‖ ≤ (S.card:ℝ) := by
    calc
      _ ≤ ∑ i∈S, ‖GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)‖ := norm_sum_le _ _
      _ = _ := by
        simp [GafniTao.fordAdditiveCharacter, Complex.norm_exp]
  have habs : Summable (fun r => c r * ‖Z r‖) :=
    (hcS.mul_right (S.card:ℝ)).of_nonneg_of_le
      (fun r => mul_nonneg (hc r) (norm_nonneg _))
      (fun r => mul_le_mul_of_nonneg_left (hZ r) (hc r))
  have hnorm r : ‖(c r:ℂ)*Z r‖=c r*‖Z r‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc r)]
  have hseries : HasSum (fun r : ℤ => (c r:ℂ)*Z r)
      (∑ i∈S, (GafniTao.heathBrownHat B (φ i):ℂ)) := by
    simpa only [c,Z,Finset.mul_sum] using
      hasSum_sum (s:=S) (fun i _hi => GafniTao.hasSum_heathBrownHatFourierSeries hB hBHalf (φ i))
  have hsumpos : 0 ≤ ∑ i∈S, GafniTao.heathBrownHat B (φ i) :=
    Finset.sum_nonneg (fun i _hi => GafniTao.heathBrownHat_nonneg B (φ i))
  have hupper : (∑ i∈S, GafniTao.heathBrownHat B (φ i)) ≤
      ∑' r : ℤ, c r*‖Z r‖ := by
    have hh := norm_tsum_le_tsum_norm (habs.congr (fun r => (hnorm r).symm))
    rw [hseries.tsum_eq] at hh
    simpa only [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hsumpos,hnorm] using hh
  have hlower : (T.card:ℝ)/2 ≤ ∑ i∈S, GafniTao.heathBrownHat B (φ i) := by
    calc
      _ = ∑ _i∈T, (1/2:ℝ) := by simp; ring
      _ ≤ ∑ i∈T, GafniTao.heathBrownHat B (φ i) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨e,he⟩ := hnear i hi
        apply GafniTao.one_half_le_heathBrownHat hB
        exact (round_le (φ i) e).trans he
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hTS
        (fun i _hi _hnot => GafniTao.heathBrownHat_nonneg B (φ i))
  change (T.card:ℝ) ≤ 2*∑' r : ℤ, c r*‖Z r‖
  linarith only [hlower,hupper]

#print axioms finite_near_integer_count_fourier

private theorem inverse_curvature_ratio_derivatives
    (f : ℝ → ℝ) {A B L v : ℝ} (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 5 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    v∈h '' Ioo A B →
    HasDerivAt (fun u => 1/iteratedDeriv 3 f (c u))
      (-2*iteratedDeriv 4 f (c v)/(iteratedDeriv 3 f (c v))^3) v ∧
    HasDerivAt (fun u => iteratedDeriv 4 f (c u)/(iteratedDeriv 3 f (c u))^3)
      (-2*(3*(iteratedDeriv 4 f (c v))^2-
        iteratedDeriv 3 f (c v)*iteratedDeriv 5 f (c v))/
        (iteratedDeriv 3 f (c v))^5) v := by
  intro h c hv
  have hp := (inverse_curvature_derivative f hL
    (fun x hx => (hf x hx).of_le (by norm_num)) hthree).2 v hv
  have hg := hasDerivAt_iteratedDeriv_finite (j:=3) (by norm_num : 3 < 5) (hf _ hp.2.1)
  have hh := hasDerivAt_iteratedDeriv_finite (j:=4) (by norm_num : 4 < 5) (hf _ hp.2.1)
  have hdg := hg.comp v hp.2.2.1
  have hdh := hh.comp v hp.2.2.1
  let X := iteratedDeriv 3 f (c v)
  let Y := iteratedDeriv 4 f (c v)
  let Z := iteratedDeriv 5 f (c v)
  have hX : 0 < X := hL.trans_le (hthree _ hp.2.1)
  change HasDerivAt (fun u => iteratedDeriv 3 f (c u)) (Y*(2/X)) v at hdg
  change HasDerivAt (fun u => iteratedDeriv 4 f (c u)) (Z*(2/X)) v at hdh
  constructor
  · have hd := hdg.inv hX.ne'
    change HasDerivAt (fun u => (iteratedDeriv 3 f (c u))⁻¹) (-(Y*(2/X))/X^2) v at hd
    change HasDerivAt (fun u => 1/iteratedDeriv 3 f (c u)) (-2*Y/X^3) v
    convert hd using 1
    · funext u
      exact one_div _
    · field_simp
  · have hd := hdh.div (hdg.pow 3) (pow_ne_zero 3 hX.ne')
    change HasDerivAt (fun u => iteratedDeriv 4 f (c u)/(iteratedDeriv 3 f (c u))^3)
      ((Z*(2/X)*X^3-Y*(3*X^2*(Y*(2/X))))/(X^3)^2) v at hd
    change HasDerivAt (fun u => iteratedDeriv 4 f (c u)/(iteratedDeriv 3 f (c u))^3)
      (-2*(3*Y^2-X*Z)/X^5) v
    convert hd using 1
    field_simp
    ring

#print axioms inverse_curvature_ratio_derivatives

private theorem shifted_legendre_third_derivative
    (f : ℝ → ℝ) {A B L q k z : ℝ} (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 5 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let J := fun v => iteratedDeriv 4 f (c v)/(iteratedDeriv 3 f (c v))^3
    let Ψpp := fun s => 4/q*(1/iteratedDeriv 3 f (c (s/q))-
      1/iteratedDeriv 3 f (c (s/q+k)))
    z/q∈h '' Ioo A B → z/q+k∈h '' Ioo A B →
    HasDerivAt Ψpp (8/q^2*(J (z/q+k)-J (z/q))) z := by
  intro h c J Ψpp hz hzk
  have hx := (inverse_curvature_ratio_derivatives f hL hf hthree hz).1
  have hy := (inverse_curvature_ratio_derivatives f hL hf hthree hzk).1
  have hs : HasDerivAt (fun s : ℝ => s/q) (1/q) z := (hasDerivAt_id z).div_const q
  have hd := ((hx.comp z hs).sub (hy.comp z (hs.add_const k))).const_mul (4/q)
  convert hd using 1
  dsimp only [J]
  ring

#print axioms shifted_legendre_third_derivative

private theorem shifted_legendre_third_curvature_bounds
    (f : ℝ → ℝ) {A B L U dlo dhi v k q : ℝ}
    (hL : 0 < L) (hdlo : 0 < dlo) (hq : 0 < q) (hk : 0 < k)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 5 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hcomb : ∀ x∈Ioo A B,
      dlo ≤ 3*(iteratedDeriv 4 f x)^2-iteratedDeriv 3 f x*iteratedDeriv 5 f x ∧
      3*(iteratedDeriv 4 f x)^2-iteratedDeriv 3 f x*iteratedDeriv 5 f x ≤ dhi) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let J := fun u => iteratedDeriv 4 f (c u)/(iteratedDeriv 3 f (c u))^3
    v∈h '' Ioo A B → v+k∈h '' Ioo A B →
    -(16*dhi*k/(q^2*L^5)) ≤ 8/q^2*(J (v+k)-J v) ∧
    8/q^2*(J (v+k)-J v) ≤ -(dlo*k/(486*q^2*U^5)) := by
  intro h c J hv hvk
  have hp := inverse_curvature_derivative f hL
    (fun x hx => (hf x hx).of_le (by norm_num)) (fun x hx => (hthree x hx).1)
  have hcont : ContinuousOn h (Ioo A B) := by
    intro x hx
    exact ((contDiffAt_iteratedDeriv_finite (n:=3) (j:=2) (hf x hx)).continuousAt.div_const 2).continuousWithinAt
  have hinterval : Icc v (v+k) ⊆ h '' Ioo A B := by
    obtain ⟨x,hx,he⟩ := hv
    obtain ⟨y,hy,he'⟩ := hvk
    rw [←he',←he]
    exact isPreconnected_Ioo.intermediate_value hx hy hcont
  let D := fun u => -2*(3*(iteratedDeriv 4 f (c u))^2-
    iteratedDeriv 3 f (c u)*iteratedDeriv 5 f (c u))/(iteratedDeriv 3 f (c u))^5
  have hd u (hu : u∈Icc v (v+k)) : HasDerivAt J (D u) u :=
    (inverse_curvature_ratio_derivatives f hL hf (fun x hx => (hthree x hx).1)
      (hinterval hu)).2
  obtain ⟨s,hs,he⟩ := exists_hasDerivAt_eq_slope J D (by linarith only [hk] : v < v+k)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => hd u ⟨hu.1.le,hu.2.le⟩)
  have hsI := (hp.2 s (hinterval ⟨hs.1.le,hs.2.le⟩)).2.1
  let X := iteratedDeriv 3 f (c s)
  let E := 3*(iteratedDeriv 4 f (c s))^2-iteratedDeriv 3 f (c s)*iteratedDeriv 5 f (c s)
  have hX : 0 < X := hL.trans_le (hthree _ hsI).1
  have hU : 0 < U := by have hh := hthree _ hsI; linarith only [hh.1,hh.2,hL]
  have hE : 0 < E := hdlo.trans_le (hcomb _ hsI).1
  have hnumlo : dlo/((6*U)^5) ≤ E/X^5 :=
    div_le_div₀ hE.le (hcomb _ hsI).1 (by positivity)
      (pow_le_pow_left₀ hX.le (hthree _ hsI).2 5)
  have hnumhi : E/X^5 ≤ dhi/L^5 :=
    div_le_div₀ (hE.le.trans (hcomb _ hsI).2) (hcomb _ hsI).2 (by positivity)
      (pow_le_pow_left₀ hL.le (hthree _ hsI).1 5)
  have he' : J (v+k)-J v=(-2*E/X^5)*k := by
    have hh := (eq_div_iff (by linarith only [hk] : v+k-v ≠ 0)).mp he
    change (-2*E/X^5)*(v+k-v)=J (v+k)-J v at hh
    nlinarith only [hh]
  rw [he']
  have hlo := mul_le_mul_of_nonneg_left hnumlo (by positivity : 0 ≤ 16*k/q^2)
  have hhi := mul_le_mul_of_nonneg_left hnumhi (by positivity : 0 ≤ 16*k/q^2)
  have hlo' : dlo*k/(486*q^2*U^5) ≤ (16*k/q^2)*(E/X^5) := by
    convert hlo using 1
    ring
  have hhi' : (16*k/q^2)*(E/X^5) ≤ 16*dhi*k/(q^2*L^5) := by
    convert hhi using 1
    ring
  rw [show 8/q^2*(-2*E/X^5*k)= -((16*k/q^2)*(E/X^5)) by ring]
  exact ⟨neg_le_neg hhi',neg_le_neg hlo'⟩

#print axioms shifted_legendre_third_curvature_bounds

private theorem shifted_legendre_third_derivative_sum
    (f : ℝ → ℝ) {A B L U dlo dhi q k a₀ r : ℝ} (N : ℕ)
    (hL : 0 < L) (hU : 0 < U) (hdlo : 0 < dlo)
    (hq : 0 < q) (hk : 0 < k) (hr : 0 < r)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 5 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hcomb : ∀ x∈Ioo A B,
      dlo ≤ 3*(iteratedDeriv 4 f x)^2-iteratedDeriv 3 f x*iteratedDeriv 5 f x ∧
      3*(iteratedDeriv 4 f x)^2-iteratedDeriv 3 f x*iteratedDeriv 5 f x ≤ dhi) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let Φ := fun v => deriv f (c v)-2*v*c v
    let Ψ := fun s => q*(Φ (s/q+k)-Φ (s/q))
    let μ := dlo*k/(486*q^2*U^5)
    let C := 7776*dhi*U^5/(dlo*L^5)
    (∀ s∈Icc a₀ (a₀+N), s/q∈h '' Ioo A B ∧ s/q+k∈h '' Ioo A B) →
    ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter (r*Ψ (a₀+n))‖ ≤
      20*C*((N:ℝ)*(r*μ)^((1:ℝ)/6)+Real.sqrt N*(r*μ)^(-(1:ℝ)/6)) := by
  intro h c Φ Ψ μ C hdom
  let Ψp := fun s => -2*(c (s/q+k)-c (s/q))
  let Ψpp := fun s => 4/q*(1/iteratedDeriv 3 f (c (s/q))-
    1/iteratedDeriv 3 f (c (s/q+k)))
  let J := fun v => iteratedDeriv 4 f (c v)/(iteratedDeriv 3 f (c v))^3
  let Ψppp := fun s => 8/q^2*(J (s/q+k)-J (s/q))
  have hf4 x (hx : x∈Ioo A B) : ContDiffAt ℝ 4 f x := (hf x hx).of_le (by norm_num)
  have hp := inverse_curvature_derivative f hL hf4 (fun x hx => (hthree x hx).1)
  have hd s (hs : s∈Icc a₀ (a₀+N)) :
      HasDerivAt Ψ (Ψp s) s ∧ HasDerivAt Ψp (Ψpp s) s ∧ HasDerivAt Ψpp (Ψppp s) s := by
    have hh := shifted_legendre_phase_derivatives f hL hf4 (fun x hx => (hthree x hx).1)
      hq.ne' (hdom s hs).1 (hdom s hs).2
    refine ⟨hh.1,?_,shifted_legendre_third_derivative f hL hf (fun x hx => (hthree x hx).1)
      (hdom s hs).1 (hdom s hs).2⟩
    let X := iteratedDeriv 3 f (c (s/q))
    let Y := iteratedDeriv 3 f (c (s/q+k))
    have hX : 0 < X := hL.trans_le (hthree _ (hp.2 _ (hdom s hs).1).2.1).1
    have hY : 0 < Y := hL.trans_le (hthree _ (hp.2 _ (hdom s hs).2).2.1).1
    have hh' : HasDerivAt Ψp (4*(Y-X)/(q*X*Y)) s := hh.2
    change HasDerivAt Ψp (4/q*(1/X-1/Y)) s
    convert hh' using 1
    field_simp
  have hb s (hs : s∈Icc a₀ (a₀+N)) : -(C*μ) ≤ Ψppp s ∧ Ψppp s ≤ -μ := by
    have hh := shifted_legendre_third_curvature_bounds f hL hdlo hq hk hf hthree hcomb
      (hdom s hs).1 (hdom s hs).2
    have hCμ : C*μ=16*dhi*k/(q^2*L^5) := by dsimp only [C,μ]; field_simp; ring
    rw [hCμ]
    exact hh
  have hC1 : 1 ≤ C := by
    have hpt := (hp.2 (a₀/q)
      (hdom a₀ ⟨le_rfl,le_add_of_nonneg_right (Nat.cast_nonneg N)⟩).1).2.1
    have ht := hthree _ hpt
    have hc := hcomb _ hpt
    have hp5 := pow_le_pow_left₀ hL.le (ht.1.trans ht.2) 5
    have hm := mul_le_mul_of_nonneg_left hp5 hdlo.le
    have hm' := mul_le_mul_of_nonneg_right (hc.1.trans hc.2) (by positivity : 0 ≤ 7776*U^5)
    apply (le_div_iff₀ (by positivity : 0 < dlo*L^5)).mpr
    nlinarith only [hm,hm']
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  by_cases hsmall : r*μ ≤ 1
  · apply continuous_third_derivative_negative_bound
      (fun s => r*Ψ s) (fun s => r*Ψp s) (fun s => r*Ψpp s) (fun s => r*Ψppp s) a₀ N
      hC1 (mul_pos hr hμ) hsmall
      (fun s hs => (hd s hs).1.const_mul r) (fun s hs => (hd s hs).2.1.const_mul r)
      (fun s hs => (hd s hs).2.2.const_mul r)
    · intro s hs
      have hh := mul_le_mul_of_nonneg_left (hb s hs).1 hr.le
      nlinarith only [hh]
    · intro s hs
      have hh := mul_le_mul_of_nonneg_left (hb s hs).2 hr.le
      nlinarith only [hh]
  · have hpow : 1 ≤ (r*μ)^((1:ℝ)/6) := Real.one_le_rpow
      (le_of_lt (lt_of_not_ge hsmall)) (by norm_num)
    have htriv : ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter (r*Ψ (a₀+n))‖ ≤ N := by
      calc
        _ ≤ ∑ n∈Finset.range N, ‖GafniTao.fordAdditiveCharacter (r*Ψ (a₀+n))‖ := norm_sum_le _ _
        _ = _ := by simp [GafniTao.fordAdditiveCharacter,Complex.norm_exp]
    have hfirst := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N : (0:ℝ) ≤ N)
    have hsec : 0 ≤ Real.sqrt N*(r*μ)^(-(1:ℝ)/6) := by positivity
    have htotal : (N:ℝ) ≤ (N:ℝ)*(r*μ)^((1:ℝ)/6)+Real.sqrt N*(r*μ)^(-(1:ℝ)/6) := by
      nlinarith only [hfirst,hsec]
    have hscale := mul_le_mul_of_nonneg_right hC1 ((Nat.cast_nonneg N).trans htotal)
    nlinarith only [htriv,htotal,hscale,(Nat.cast_nonneg N : (0:ℝ) ≤ N)]

#print axioms shifted_legendre_third_derivative_sum

private theorem integer_rpow_tail
    {p : ℝ} (hp : p < -1) {R : ℕ} (hR : 0 < R) :
    let g := fun r : ℤ => if R < r.natAbs then |(r:ℝ)|^p else 0
    Summable g ∧ (∑' r : ℤ, g r) ≤ 2*(R:ℝ)^(p+1)/(-p-1) := by
  intro g
  let f := fun n : ℕ => if R < n then (n:ℝ)^p else 0
  have hf : Summable f := by
    apply ((Real.summable_nat_rpow.mpr hp).indicator {n | R < n}).congr
    intro n
    by_cases hn : R < n <;> simp [f,hn]
  have hg : Summable g := by
    have hs : Summable (fun r : ℤ => |(r:ℝ)|^p) := by
      simpa only [neg_neg] using Real.summable_abs_int_rpow (by linarith only [hp] : 1 < -p)
    apply (hs.indicator {r | R < r.natAbs}).congr
    intro r
    by_cases hr : R < r.natAbs <;> simp [g,hr]
  have hfinite : ∑ n∈Finset.range (R+1), f n=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hh := Finset.mem_range.mp hn
    simp only [f,if_neg (by omega : ¬ R < n)]
  have hshift := hf.sum_add_tsum_nat_add (R+1)
  rw [hfinite,zero_add] at hshift
  have hfun : (fun j : ℕ => f (j+(R+1)))=(fun j => ((j+R+1:ℕ):ℝ)^p) := by
    funext j
    simp only [f,if_pos (by omega : R < j+(R+1)),Nat.add_assoc]
  rw [hfun] at hshift
  have hnat : (∑' n : ℕ, f n) ≤ (R:ℝ)^(p+1)/(-p-1) := by
    rw [←hshift]
    exact tsum_nat_rpow_tail_le hp hR
  have hpS := hg.comp_injective (show Function.Injective (fun n : ℕ => (n:ℤ)) from Nat.cast_injective)
  have hmS := hg.comp_injective
    (show Function.Injective (fun n : ℕ => -((n:ℤ)+1)) from by
      intro a b he
      simp only [neg_inj,add_left_inj] at he
      exact_mod_cast he)
  have hplus : (fun n : ℕ => g n)=f := by
    funext n
    simp only [g,f,Int.natAbs_natCast,Int.cast_natCast,Nat.abs_cast]
  have hminus : (fun n : ℕ => g (-((n:ℤ)+1)))=(fun n => f (n+1)) := by
    funext n
    change g (-((n+1:ℕ):ℤ))=f (n+1)
    simp only [g,f,Int.natAbs_neg,Int.natAbs_natCast,Int.cast_neg,Int.cast_natCast,abs_neg,Nat.abs_cast]
  have hz : f 0=0 := by simp [f]
  have hshiftOne : (∑' n : ℕ, f (n+1))=∑' n : ℕ, f n := by
    simpa only [hz,zero_add] using hf.tsum_eq_zero_add.symm
  refine ⟨hg,?_⟩
  rw [tsum_of_nat_of_neg_add_one hpS hmS,hplus,hminus,hshiftOne]
  calc
    _ ≤ (R:ℝ)^(p+1)/(-p-1)+(R:ℝ)^(p+1)/(-p-1) := add_le_add hnat hnat
    _ = _ := by ring

#print axioms integer_rpow_tail

private theorem hat_fourier_mass_and_decay
    {B : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2) :
    HasSum (GafniTao.heathBrownHatFourierCoefficient B) 1 ∧
    ∀ r : ℤ, r ≠ 0 → GafniTao.heathBrownHatFourierCoefficient B r ≤ 1/(B*(r:ℝ)^2) := by
  constructor
  · apply Complex.hasSum_ofReal.mp
    have hh := GafniTao.hasSum_heathBrownHatFourierSeries hB hBHalf 0
    simpa [GafniTao.fordAdditiveCharacter,GafniTao.heathBrownHat,
      GafniTao.heathBrownDistanceToInteger] using hh
  · intro r hr
    have hrR : (r:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hr
    have he := GafniTao.heathBrownHatFourierCoefficient_eq_fordTent hB r
    rw [GafniTao.fordTentFourierCoefficient_of_ne_zero hB.ne' hr] at he
    have heR : GafniTao.heathBrownHatFourierCoefficient B r=
        (Real.sin (Real.pi*(r:ℝ)*B))^2/(Real.pi^2*B*(r:ℝ)^2) :=
      Complex.ofReal_injective he
    rw [heR]
    have hsin : (Real.sin (Real.pi*(r:ℝ)*B))^2 ≤ 1 := by
      nlinarith only [Real.neg_one_le_sin (Real.pi*(r:ℝ)*B),
        Real.sin_le_one (Real.pi*(r:ℝ)*B)]
    have hpi : 1 ≤ Real.pi^2 := by nlinarith only [Real.pi_gt_three]
    exact div_le_div₀ (by norm_num) hsin (by positivity)
      (by have hh := mul_le_mul_of_nonneg_right hpi (by positivity : 0 ≤ B*(r:ℝ)^2)
          nlinarith only [hh])

#print axioms hat_fourier_mass_and_decay

private theorem hat_fourier_positive_moment
    {B p : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2)
    (hp : 0 ≤ p) (hp1 : p < 1) {R : ℕ} (hR : 0 < R) :
    let c := GafniTao.heathBrownHatFourierCoefficient B
    Summable (fun r : ℤ => c r*|(r:ℝ)|^p) ∧
    (∑' r : ℤ, c r*|(r:ℝ)|^p) ≤ (R:ℝ)^p+
      (2/B)*(R:ℝ)^(p-1)/(1-p) := by
  intro c
  let g := fun r : ℤ => if R < r.natAbs then |(r:ℝ)|^(p-2) else 0
  have htail := integer_rpow_tail (p:=p-2) (by linarith only [hp1]) hR
  have hmass := (hat_fourier_mass_and_decay hB hBHalf).1
  have hc r : 0 ≤ c r := GafniTao.heathBrownHatFourierCoefficient_nonneg hB.le r
  have hmajor : Summable (fun r : ℤ => c r*(R:ℝ)^p+(1/B)*g r) :=
    (hmass.summable.mul_right _).add (htail.1.mul_left _)
  have hpoint r : c r*|(r:ℝ)|^p ≤ c r*(R:ℝ)^p+(1/B)*g r := by
    by_cases hr : R < r.natAbs
    · have hr0 : r ≠ 0 := by intro he; subst r; simp at hr
      have hx : 0 < |(r:ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hr0)
      have hdecay := (hat_fourier_mass_and_decay hB hBHalf).2 r hr0
      have heq : 1/(B*(r:ℝ)^2)*|(r:ℝ)|^p=(1/B)*|(r:ℝ)|^(p-2) := by
        rw [Real.rpow_sub hx,Real.rpow_two,sq_abs]
        ring
      have hh := mul_le_mul_of_nonneg_right hdecay (Real.rpow_nonneg (abs_nonneg (r:ℝ)) p)
      rw [heq] at hh
      change c r*|(r:ℝ)|^p ≤ c r*(R:ℝ)^p+(1/B)*(if R < r.natAbs then |(r:ℝ)|^(p-2) else 0)
      rw [if_pos hr]
      exact hh.trans (le_add_of_nonneg_left (mul_nonneg (hc r) (by positivity)))
    · have hle : |(r:ℝ)| ≤ (R:ℝ) := by
        have hh : r.natAbs ≤ R := Nat.le_of_not_gt hr
        have hh' : (r.natAbs:ℝ) ≤ R := by exact_mod_cast hh
        simpa only [Nat.cast_natAbs,Int.cast_abs] using hh'
      change c r*|(r:ℝ)|^p ≤ c r*(R:ℝ)^p+(1/B)*(if R < r.natAbs then |(r:ℝ)|^(p-2) else 0)
      rw [if_neg hr,mul_zero,add_zero]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hle hp) (hc r)
  have hsum : Summable (fun r : ℤ => c r*|(r:ℝ)|^p) :=
    hmajor.of_nonneg_of_le (fun r => mul_nonneg (hc r) (by positivity)) hpoint
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' r : ℤ, (c r*(R:ℝ)^p+(1/B)*g r) := Summable.tsum_le_tsum hpoint hsum hmajor
    _ = (R:ℝ)^p+(1/B)*(∑' r : ℤ, g r) := by
      rw [Summable.tsum_add (hmass.summable.mul_right _) (htail.1.mul_left _),
        tsum_mul_right,tsum_mul_left,hmass.tsum_eq,one_mul]
    _ ≤ (R:ℝ)^p+(1/B)*(2*(R:ℝ)^((p-2)+1)/(-(p-2)-1)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left htail.2 (by positivity : 0 ≤ 1/B))
    _ = _ := by
      rw [show p-2+1=p-1 by ring,show -(p-2)-1=1-p by ring]
      ring

#print axioms hat_fourier_positive_moment

private theorem hat_fourier_sixth_moment
    {B : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2) :
    let c := GafniTao.heathBrownHatFourierCoefficient B
    Summable (fun r : ℤ => c r*|(r:ℝ)|^((1:ℝ)/6)) ∧
    (∑' r : ℤ, c r*|(r:ℝ)|^((1:ℝ)/6)) ≤ 5*B^(-(1:ℝ)/6) := by
  intro c
  let R : ℕ := ⌈1/B⌉₊
  have hRlo : 1/B ≤ (R:ℝ) := Nat.le_ceil _
  have hR : 0 < R := by
    have hh : (0:ℝ) < R := (one_div_pos.mpr hB).trans_le hRlo
    exact_mod_cast hh
  have hRhi : (R:ℝ) ≤ 2/B := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 1/B by positivity)
    change (R:ℝ) < 1/B+1 at hh
    have hB1 : B ≤ 1 := by linarith only [hBHalf]
    have h1 : 1 ≤ 1/B := (le_div_iff₀ hB).mpr (by simpa only [one_mul] using hB1)
    calc
      _ ≤ 1/B+1/B := hh.le.trans (add_le_add le_rfl h1)
      _ = _ := by ring
  have hm := hat_fourier_positive_moment hB hBHalf (by norm_num : (0:ℝ) ≤ 1/6)
    (by norm_num : (1:ℝ)/6 < 1) hR
  have hhead : (R:ℝ)^((1:ℝ)/6) ≤ 2*B^(-(1:ℝ)/6) := by
    calc
      _ ≤ (2/B)^((1:ℝ)/6) := Real.rpow_le_rpow (Nat.cast_nonneg R) hRhi (by norm_num)
      _ = (2:ℝ)^((1:ℝ)/6)*B^(-(1:ℝ)/6) := by
        rw [show -(1:ℝ)/6 = -((1:ℝ)/6) by ring,
          Real.div_rpow (by norm_num) hB.le,Real.rpow_neg hB.le]
        ring
      _ ≤ _ := by
        have hh : (2:ℝ)^((1:ℝ)/6) ≤ 2 := by
          simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (1:ℝ)/6 ≤ 1))
        exact mul_le_mul_of_nonneg_right hh (by positivity)
  have htailpow : (R:ℝ)^((1:ℝ)/6-1) ≤ B^((5:ℝ)/6) := by
    calc
      _ ≤ (1/B)^((1:ℝ)/6-1) := Real.rpow_le_rpow_of_nonpos
        (one_div_pos.mpr hB) hRlo (by norm_num)
      _ = _ := by
        rw [one_div,Real.inv_rpow hB.le,←Real.rpow_neg hB.le]
        norm_num
  have htail : (2/B)*(R:ℝ)^((1:ℝ)/6-1)/(1-(1:ℝ)/6) ≤
      (12/5:ℝ)*B^(-(1:ℝ)/6) := by
    calc
      _ ≤ (2/B)*B^((5:ℝ)/6)/(1-(1:ℝ)/6) := by gcongr
      _ = _ := by
        have he : B^((5:ℝ)/6)/B=B^(-(1:ℝ)/6) := by
          rw [←Real.rpow_sub_one hB.ne']
          norm_num
        calc
          _ = (12/5:ℝ)*(B^((5:ℝ)/6)/B) := by ring
          _ = _ := by rw [he]
  refine ⟨hm.1,?_⟩
  have hb := hm.2.trans (add_le_add hhead htail)
  have hpos : 0 ≤ B^(-(1:ℝ)/6) := by positivity
  linarith only [hb,hpos]

#print axioms hat_fourier_sixth_moment

private theorem finite_near_integer_count_sixth
    {ι : Type*} [DecidableEq ι] (S T : Finset ι) (φ : ι → ℝ)
    {B A D : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hTS : T ⊆ S)
    (hnear : ∀ i∈T, ∃ e : ℤ, |φ i-(e:ℝ)| ≤ B/2)
    (hfreq : ∀ r : ℤ, r ≠ 0 →
      ‖∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)‖ ≤ A*|(r:ℝ)|^((1:ℝ)/6)+D) :
    (T.card:ℝ) ≤ 2*B*S.card+10*A*B^(-(1:ℝ)/6)+2*D := by
  let c := GafniTao.heathBrownHatFourierCoefficient B
  let Z := fun r : ℤ => ∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)
  let e := fun r : ℤ => if r=0 then B*(S.card:ℝ) else 0
  have hc r : 0 ≤ c r := GafniTao.heathBrownHatFourierCoefficient_nonneg hB.le r
  have hm := hat_fourier_sixth_moment hB hBHalf
  have hmass := (hat_fourier_mass_and_decay hB hBHalf).1
  have he : HasSum e (B*(S.card:ℝ)) := hasSum_ite_eq _ _
  have hmajor : Summable (fun r : ℤ => e r+A*(c r*|(r:ℝ)|^((1:ℝ)/6))+D*c r) :=
    (he.summable.add (hm.1.mul_left A)).add (hmass.summable.mul_left D)
  have hpoint r : c r*‖Z r‖ ≤ e r+A*(c r*|(r:ℝ)|^((1:ℝ)/6))+D*c r := by
    by_cases hr : r=0
    · subst r
      have hZ : Z 0=(S.card:ℂ) := by simp [Z,GafniTao.fordAdditiveCharacter]
      rw [hZ]
      simp only [c,GafniTao.heathBrownHatFourierCoefficient_zero,
        Complex.norm_natCast,Int.cast_zero,abs_zero,
        Real.zero_rpow (by norm_num : (1:ℝ)/6 ≠ 0),mul_zero,add_zero,e,if_pos rfl]
      exact le_add_of_nonneg_right (mul_nonneg hD hB.le)
    · have hh := mul_le_mul_of_nonneg_left (hfreq r hr) (hc r)
      change c r*‖Z r‖ ≤ _ at hh
      change c r*‖Z r‖ ≤ (if r=0 then B*(S.card:ℝ) else 0)+
        A*(c r*|(r:ℝ)|^((1:ℝ)/6))+D*c r
      rw [if_neg hr,zero_add]
      convert hh using 1
      ring
  have hs : Summable (fun r : ℤ => c r*‖Z r‖) :=
    hmajor.of_nonneg_of_le (fun r => mul_nonneg (hc r) (norm_nonneg _)) hpoint
  have hupper : (∑' r : ℤ, c r*‖Z r‖) ≤ B*S.card+5*A*B^(-(1:ℝ)/6)+D := by
    calc
      _ ≤ ∑' r : ℤ, (e r+A*(c r*|(r:ℝ)|^((1:ℝ)/6))+D*c r) :=
        Summable.tsum_le_tsum hpoint hs hmajor
      _ = B*S.card+A*(∑' r : ℤ, c r*|(r:ℝ)|^((1:ℝ)/6))+D := by
        rw [Summable.tsum_add (he.summable.add (hm.1.mul_left A)) (hmass.summable.mul_left D),
          Summable.tsum_add he.summable (hm.1.mul_left A),tsum_mul_left,tsum_mul_left,
          he.tsum_eq,hmass.tsum_eq,mul_one]
      _ ≤ B*S.card+A*(5*B^(-(1:ℝ)/6))+D :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm.2 hA)) le_rfl
      _ = _ := by ring
  have hcount := finite_near_integer_count_fourier S T φ hB hBHalf hTS hnear
  change (T.card:ℝ) ≤ 2*∑' r : ℤ, c r*‖Z r‖ at hcount
  linarith only [hcount,hupper]

#print axioms finite_near_integer_count_sixth

private theorem shifted_legendre_near_integer_count
    (f : ℝ → ℝ) {A B L U dlo dhi q k a₀ W : ℝ} (N : ℕ) (T : Finset ℕ)
    (hL : 0 < L) (hU : 0 < U) (hdlo : 0 < dlo)
    (hq : 0 < q) (hk : 0 < k) (hW : 0 < W) (hWHalf : W ≤ 1/2)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 5 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hcomb : ∀ x∈Ioo A B,
      dlo ≤ 3*(iteratedDeriv 4 f x)^2-iteratedDeriv 3 f x*iteratedDeriv 5 f x ∧
      3*(iteratedDeriv 4 f x)^2-iteratedDeriv 3 f x*iteratedDeriv 5 f x ≤ dhi) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let Φ := fun v => deriv f (c v)-2*v*c v
    let Ψ := fun s => q*(Φ (s/q+k)-Φ (s/q))
    let μ := dlo*k/(486*q^2*U^5)
    let C := 7776*dhi*U^5/(dlo*L^5)
    (∀ s∈Icc a₀ (a₀+N), s/q∈h '' Ioo A B ∧ s/q+k∈h '' Ioo A B) →
    T ⊆ Finset.range N →
    (∀ n∈T, ∃ e : ℤ, |Ψ (a₀+n)-(e:ℝ)| ≤ W/2) →
    (T.card:ℝ) ≤ 2*W*N+
      200*C*N*μ^((1:ℝ)/6)*W^(-(1:ℝ)/6)+40*C*Real.sqrt N*μ^(-(1:ℝ)/6) := by
  intro h c Φ Ψ μ C hdom hT hnear
  have hp := inverse_curvature_derivative f hL
    (fun x hx => (hf x hx).of_le (by norm_num)) (fun x hx => (hthree x hx).1)
  have hpt := (hp.2 (a₀/q)
    (hdom a₀ ⟨le_rfl,le_add_of_nonneg_right (Nat.cast_nonneg N)⟩).1).2.1
  have hdhi : 0 < dhi := hdlo.trans_le ((hcomb _ hpt).1.trans (hcomb _ hpt).2)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  let E := 20*C*(N:ℝ)*μ^((1:ℝ)/6)
  let D := 20*C*Real.sqrt N*μ^(-(1:ℝ)/6)
  have hfreq r (hr : r ≠ (0:ℤ)) :
      ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter ((r:ℝ)*Ψ (a₀+n))‖ ≤
        E*|(r:ℝ)|^((1:ℝ)/6)+D := by
    have hrabs : 0 < |(r:ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hr)
    have hrone : 1 ≤ |(r:ℝ)| := by
      have hh : (1:ℤ) ≤ |r| := Int.one_le_abs hr
      exact_mod_cast hh
    have hb := shifted_legendre_third_derivative_sum f N hL hU hdlo hq hk hrabs
      hf hthree hcomb hdom
    change ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter (|(r:ℝ)| * Ψ (a₀+n))‖ ≤
      20*C*((N:ℝ)*(|(r:ℝ)| * μ)^((1:ℝ)/6)+Real.sqrt N*(|(r:ℝ)| * μ)^(-(1:ℝ)/6)) at hb
    have hsign :
        ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter ((r:ℝ)*Ψ (a₀+n))‖ =
        ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter (|(r:ℝ)| * Ψ (a₀+n))‖ := by
      by_cases hnon : 0 ≤ (r:ℝ)
      · rw [abs_of_nonneg hnon]
      · rw [abs_of_neg (lt_of_not_ge hnon)]
        simp only [neg_mul]
        exact (norm_sum_fordAdditiveCharacter_neg_phase (fun s => (r:ℝ)*Ψ s) a₀ N).symm
    rw [hsign]
    apply hb.trans
    rw [Real.mul_rpow hrabs.le hμ.le,Real.mul_rpow hrabs.le hμ.le]
    have hneg := Real.rpow_le_one_of_one_le_of_nonpos hrone (by norm_num : -(1:ℝ)/6 ≤ 0)
    calc
      _ ≤ 20*C*((N:ℝ)*(|(r:ℝ)|^((1:ℝ)/6)*μ^((1:ℝ)/6))+
          Real.sqrt N*(1*μ^(-(1:ℝ)/6))) := by gcongr
      _ = _ := by dsimp only [E,D]; ring
  have hh := finite_near_integer_count_sixth (Finset.range N) T (fun n => Ψ (a₀+n))
    hW hWHalf (show 0 ≤ E by dsimp only [E]; positivity)
    (show 0 ≤ D by dsimp only [D]; positivity) hT hnear hfreq
  simp only [Finset.card_range,E,D] at hh
  convert hh using 1
  ring

#print axioms shifted_legendre_near_integer_count

private theorem model_reference_combination
    (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    3*(iteratedDeriv 3 (Expdb.modelPhase σ) u)^2-
      iteratedDeriv 2 (Expdb.modelPhase σ) u*iteratedDeriv 4 (Expdb.modelPhase σ) u =
      (σ+2)*(2*σ+3)*(iteratedDeriv 2 (Expdb.modelPhase σ) u/u)^2 := by
  have hd (j : ℕ) : iteratedDeriv j (Expdb.modelPhase σ) u=
      (descPochhammer ℝ j).eval (-σ)*u^(-σ-j) := by
    change iteratedDeriv j (fun x : ℝ => x^(-σ)) u = _
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const (-σ) u j
  have h2 : (descPochhammer ℝ 2).eval (-σ)=σ*(σ+1) := by
    simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,Finset.prod_range_zero,
      Nat.cast_zero,Nat.cast_one]
    ring
  have h3 : (descPochhammer ℝ 3).eval (-σ)= -σ*(σ+1)*(σ+2) := by
    simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,Finset.prod_range_zero,
      Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
    ring
  have h4 : (descPochhammer ℝ 4).eval (-σ)=σ*(σ+1)*(σ+2)*(σ+3) := by
    simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,Finset.prod_range_zero,
      Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
    ring
  have hpow3 : u^(-σ-(3:ℕ))=u^(-σ-(2:ℕ))/u := by
    rw [←Real.rpow_sub_one hu.ne']
    congr 1
    norm_num
    ring
  have hpow4 : u^(-σ-(4:ℕ))=u^(-σ-(2:ℕ))/u^2 := by
    rw [←Real.rpow_two u,←Real.rpow_sub hu]
    congr 1
    norm_num
    ring
  rw [hd 2,hd 3,hd 4,h2,h3,h4,hpow3,hpow4]
  ring

#print axioms model_reference_combination

private theorem derivative_combination_perturbation
    {x y z x₀ y₀ z₀ δ X Y Z : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : |x-x₀| ≤ δ) (hy : |y-y₀| ≤ δ) (hz : |z-z₀| ≤ δ)
    (hx₀ : |x₀| ≤ X) (hy₀ : |y₀| ≤ Y) (hz₀ : |z₀| ≤ Z) :
    |(3*y^2-x*z)-(3*y₀^2-x₀*z₀)| ≤ δ*(6*Y+X+Z+4) := by
  have hY : 0 ≤ Y := (abs_nonneg _).trans hy₀
  have hZ : 0 ≤ Z := (abs_nonneg _).trans hz₀
  have hX : 0 ≤ X := (abs_nonneg _).trans hx₀
  have hyplus : |y+y₀| ≤ 2*Y+δ := by
    calc
      _ = |(y-y₀)+2*y₀| := by congr 1; ring
      _ ≤ |y-y₀|+|2*y₀| := abs_add_le _ _
      _ ≤ δ+2*Y := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; gcongr
      _ = _ := by ring
  have hzbound : |z| ≤ Z+δ := by
    calc
      _ = |(z-z₀)+z₀| := by rw [sub_add_cancel]
      _ ≤ |z-z₀|+|z₀| := abs_add_le _ _
      _ ≤ δ+Z := add_le_add hz hz₀
      _ = _ := by ring
  have hsq : |y^2-y₀^2| ≤ δ*(2*Y+δ) := by
    rw [sq_sub_sq,abs_mul]
    rw [mul_comm |y+y₀| |y-y₀|]
    exact mul_le_mul hy hyplus (abs_nonneg _) hδ
  have hprod : |x*z-x₀*z₀| ≤ δ*(Z+δ)+X*δ := by
    calc
      _ = |(x-x₀)*z+x₀*(z-z₀)| := by congr 1; ring
      _ ≤ |(x-x₀)*z|+|x₀*(z-z₀)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul,abs_mul]; gcongr
  calc
    _ = |3*(y^2-y₀^2)-(x*z-x₀*z₀)| := by congr 1; ring
    _ ≤ |3*(y^2-y₀^2)|+|x*z-x₀*z₀| := abs_sub _ _
    _ ≤ 3*(δ*(2*Y+δ))+(δ*(Z+δ)+X*δ) := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)]
      gcongr
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hδ1 hδ]

#print axioms derivative_combination_perturbation

private theorem model_fifth_combination_bounds
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ dlo dhi : ℝ, 0 < δ ∧ 0 < dlo ∧ 0 < dhi ∧
      ∀ F : ℝ → ℝ, Expdb.IsApproximateModelPhaseFunction F σ 4 δ →
      ∀ u∈Ioo (1:ℝ) 2,
        dlo ≤ 3*(iteratedDeriv 4 F u)^2-iteratedDeriv 3 F u*iteratedDeriv 5 F u ∧
        3*(iteratedDeriv 4 F u)^2-iteratedDeriv 3 F u*iteratedDeriv 5 F u ≤ dhi := by
  let X := modelPhaseJetCoefficient σ 2
  let Y := modelPhaseJetCoefficient σ 3
  let Z := modelPhaseJetCoefficient σ 4
  let H := 6*Y+X+Z+4
  let L := modelPhaseJetLower σ 2
  let K := (σ+2)*(2*σ+3)
  let d := K*L^2
  let R := 3*Y^2+X*Z
  let δ := min 1 (d/(2*H))
  have hX : 0 ≤ X := modelPhaseJetCoefficient_nonneg _ _
  have hY : 0 ≤ Y := modelPhaseJetCoefficient_nonneg _ _
  have hZ : 0 ≤ Z := modelPhaseJetCoefficient_nonneg _ _
  have hH : 0 < H := by dsimp only [H]; positivity
  have hL : 0 < L := modelPhaseJetLower_pos hσ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδH : δ*H ≤ d/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*H)).mp (min_le_right 1 (d/(2*H)))
    change δ*(2*H) ≤ d at hh
    nlinarith only [hh]
  refine ⟨δ,d/2,R+d/2,hδ,by positivity,by positivity,?_⟩
  intro F hF u hu
  let x₀ := iteratedDeriv 2 (Expdb.modelPhase σ) u
  let y₀ := iteratedDeriv 3 (Expdb.modelPhase σ) u
  let z₀ := iteratedDeriv 4 (Expdb.modelPhase σ) u
  have hx₀ : |x₀| ≤ X := iteratedDeriv_modelPhase_abs_le hσ.le hu 2
  have hy₀ : |y₀| ≤ Y := iteratedDeriv_modelPhase_abs_le hσ.le hu 3
  have hz₀ : |z₀| ≤ Z := iteratedDeriv_modelPhase_abs_le hσ.le hu 4
  have hsign : modelPhaseJetSign σ 2=1 := by
    have he : (descPochhammer ℝ 2).eval (-σ)=σ*(σ+1) := by
      simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,
        Finset.prod_range_zero,Nat.cast_zero,Nat.cast_one]
      ring
    unfold modelPhaseJetSign
    rw [he,if_pos (by positivity)]
  have hxlower : 2*L ≤ x₀ := by
    have hh := (modelPhase_signed_referenceJet_bounds hσ hu 2).1
    rwa [hsign,one_mul] at hh
  have hratio : L ≤ x₀/u := by
    apply (le_div_iff₀ (zero_lt_one.trans hu.1)).mpr
    have hh := mul_le_mul_of_nonneg_right hu.2.le hL.le
    nlinarith only [hh,hxlower]
  have hreflo : d ≤ 3*y₀^2-x₀*z₀ := by
    have he := model_reference_combination σ (zero_lt_one.trans hu.1)
    change 3*y₀^2-x₀*z₀=K*(x₀/u)^2 at he
    rw [he]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hratio 2) hK.le
  have hrefhi : 3*y₀^2-x₀*z₀ ≤ R := by
    calc
      _ ≤ |3*y₀^2-x₀*z₀| := le_abs_self _
      _ ≤ |3*y₀^2|+|x₀*z₀| := abs_sub _ _
      _ = 3*|y₀|^2+|x₀| * |z₀| := by rw [abs_mul,abs_mul,abs_pow]; norm_num
      _ ≤ _ := by dsimp only [R]; gcongr
  have herr := derivative_combination_perturbation hδ.le hδ1
    (approximateModelPhase_iteratedDeriv_error hF hu 2 (by norm_num))
    (approximateModelPhase_iteratedDeriv_error hF hu 3 (by norm_num))
    (approximateModelPhase_iteratedDeriv_error hF hu 4 le_rfl) hx₀ hy₀ hz₀
  change |(3*(iteratedDeriv 4 F u)^2-iteratedDeriv 3 F u*iteratedDeriv 5 F u)-
    (3*y₀^2-x₀*z₀)| ≤ δ*H at herr
  have he := abs_le.mp (herr.trans hδH)
  constructor <;> linarith only [he.1,he.2,hreflo,hrefhi]

#print axioms model_fifth_combination_bounds

private theorem physical_model_fifth_derivative_data
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ c u dlo dhi : ℝ, 0 < δ ∧ 0 < c ∧ 0 < u ∧ 0 < dlo ∧ 0 < dhi ∧
      ∀ (F : ℝ → ℝ) (T P : ℝ), 0 < T → 0 < P →
      Expdb.IsApproximateModelPhaseFunction F σ 4 δ →
      let f := fun x => T*F (x/P)
      (∀ x∈Ioo P (2*P), ContDiffAt ℝ 5 f x) ∧
      (∀ x∈Ioo P (2*P),
        c*T/P^3 ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*(u*T/P^3)) ∧
      (∀ x∈Ioo P (2*P),
        dlo*T^2/P^8 ≤ 3*(iteratedDeriv 4 f x)^2-iteratedDeriv 3 f x*iteratedDeriv 5 f x ∧
        3*(iteratedDeriv 4 f x)^2-iteratedDeriv 3 f x*iteratedDeriv 5 f x ≤ dhi*T^2/P^8) := by
  obtain ⟨δ₀,dlo,dhi,hδ₀,hdlo,hdhi,hcomb⟩ := model_fifth_combination_bounds hσ
  let c := modelPhaseJetLower σ 2
  let u := (modelPhaseJetCoefficient σ 2+1)/6
  let δ := min δ₀ (min c 1)
  have hc : 0 < c := modelPhaseJetLower_pos hσ 2
  have hu : 0 < u := by dsimp only [u]; have hh := modelPhaseJetCoefficient_nonneg σ 2; positivity
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hc (by norm_num))
  refine ⟨δ,c,u,dlo,dhi,hδ,hc,hu,hdlo,hdhi,?_⟩
  intro F T P hT hP hF f
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left δ₀ (min c 1))
  have hpoint x (hx : x∈Ioo P (2*P)) : x/P∈Ioo (1:ℝ) 2 := by
    constructor
    · exact (lt_div_iff₀ hP).mpr (by simpa only [one_mul] using hx.1)
    · exact (div_lt_iff₀ hP).mpr hx.2
  have hfc x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ ∞ F (x/P) :=
    approximateModelPhase_contDiffAt hF (hpoint x hx)
  have hfd x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ ∞ f x := by
    dsimp only [f]
    exact contDiffAt_const.mul ((hfc x hx).comp x (by fun_prop))
  have hd x (hx : x∈Ioo P (2*P)) (n : ℕ) :
      iteratedDeriv n f x=T/P^n*iteratedDeriv n F (x/P) := by
    have hh : ∀ y∈Ioo P (2*P), ContDiffAt ℝ ∞ F (P⁻¹*y+0) := by
      intro y hy
      simpa only [add_zero,div_eq_mul_inv,mul_comm] using hfc y hy
    have ha := sargos_iteratedDeriv_comp_affine_local hh hx n
    simp only [add_zero] at ha
    have he : (fun y => F (y/P))=(fun y => F (P⁻¹*y)) := by
      funext y
      rw [div_eq_mul_inv,mul_comm]
    dsimp only [f]
    rw [iteratedDeriv_const_mul_field,he,ha,inv_pow]
    simp only [div_eq_mul_inv,mul_assoc,mul_comm P⁻¹ x]
  have hsign : modelPhaseJetSign σ 2=1 := by
    have he : (descPochhammer ℝ 2).eval (-σ)=σ*(σ+1) := by
      simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,
        Finset.prod_range_zero,Nat.cast_zero,Nat.cast_one]
      ring
    unfold modelPhaseJetSign
    rw [he,if_pos (by positivity)]
  refine ⟨fun x hx => (hfd x hx).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 5),?_,?_⟩
  · intro x hx
    have hh := approximateModelPhase_signedJet_bounds hσ hF (hpoint x hx) 2 (by norm_num)
      (min_le_right δ₀ (min c 1))
    rw [hsign,one_mul] at hh
    rw [hd x hx 3]
    constructor
    · convert mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ T/P^3 by positivity) using 1
      ring
    · convert mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ T/P^3 by positivity) using 1
      dsimp only [u]
      ring
  · intro x hx
    have hh := hcomb F hF₀ (x/P) (hpoint x hx)
    rw [hd x hx 3,hd x hx 4,hd x hx 5]
    have he : 3*(T/P^4*iteratedDeriv 4 F (x/P))^2-
        (T/P^3*iteratedDeriv 3 F (x/P))*(T/P^5*iteratedDeriv 5 F (x/P)) =
        (T^2/P^8)*(3*(iteratedDeriv 4 F (x/P))^2-
          iteratedDeriv 3 F (x/P)*iteratedDeriv 5 F (x/P)) := by ring
    rw [he]
    constructor
    · convert mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ T^2/P^8 by positivity) using 1
      ring
    · convert mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ T^2/P^8 by positivity) using 1
      ring

#print axioms physical_model_fifth_derivative_data

private theorem physical_model_legendre_near_integer_count
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ m C : ℝ, 0 < δ ∧ 0 < m ∧ 0 < C ∧
      ∀ (F : ℝ → ℝ) (T P q k a₀ W : ℝ) (N : ℕ) (I : Finset ℕ),
      0 < T → 0 < P → 0 < q → 0 < k → 0 < W → W ≤ 1/2 →
      Expdb.IsApproximateModelPhaseFunction F σ 4 δ →
      let f := fun x => T*F (x/P)
      let h := fun x => iteratedDeriv 2 f x/2
      let c := Function.invFunOn h (Ioo P (2*P))
      let Φ := fun v => deriv f (c v)-2*v*c v
      let Ψ := fun s => q*(Φ (s/q+k)-Φ (s/q))
      let μ := m*k*P^7/(q^2*T^3)
      (∀ s∈Icc a₀ (a₀+N), s/q∈h '' Ioo P (2*P) ∧ s/q+k∈h '' Ioo P (2*P)) →
      I ⊆ Finset.range N →
      (∀ n∈I, ∃ e : ℤ, |Ψ (a₀+n)-(e:ℝ)| ≤ W/2) →
      (I.card:ℝ) ≤ 2*W*N+
        200*C*N*μ^((1:ℝ)/6)*W^(-(1:ℝ)/6)+40*C*Real.sqrt N*μ^(-(1:ℝ)/6) := by
  obtain ⟨δ,c,u,dlo,dhi,hδ,hc,hu,hdlo,hdhi,hdata⟩ := physical_model_fifth_derivative_data hσ
  let m := dlo/(486*u^5)
  let C := 7776*dhi*u^5/(dlo*c^5)
  refine ⟨δ,m,C,hδ,by dsimp only [m]; positivity,by dsimp only [C]; positivity,?_⟩
  intro F T P q k a₀ W N I hT hP hq hk hW hWHalf hF f h ci Φ Ψ μ hdom hI hnear
  have hd := hdata F T P hT hP hF
  have hb := shifted_legendre_near_integer_count f N I
    (L:=c*T/P^3) (U:=u*T/P^3) (dlo:=dlo*T^2/P^8) (dhi:=dhi*T^2/P^8)
    (by positivity) (by positivity) (by positivity) hq hk hW hWHalf
    hd.1 hd.2.1 hd.2.2 hdom hI hnear
  have hμeq : (dlo*T^2/P^8)*k/(486*q^2*(u*T/P^3)^5)=μ := by
    dsimp only [μ,m]
    field_simp
  have hCeq : 7776*(dhi*T^2/P^8)*(u*T/P^3)^5/
      ((dlo*T^2/P^8)*(c*T/P^3)^5)=C := by
    dsimp only [C]
    field_simp
  change (I.card:ℝ) ≤ 2*W*N+
    200*(7776*(dhi*T^2/P^8)*(u*T/P^3)^5/((dlo*T^2/P^8)*(c*T/P^3)^5))*N*
      ((dlo*T^2/P^8)*k/(486*q^2*(u*T/P^3)^5))^((1:ℝ)/6)*W^(-(1:ℝ)/6)+
    40*(7776*(dhi*T^2/P^8)*(u*T/P^3)^5/((dlo*T^2/P^8)*(c*T/P^3)^5))*Real.sqrt N*
      ((dlo*T^2/P^8)*k/(486*q^2*(u*T/P^3)^5))^(-(1:ℝ)/6) at hb
  rwa [hμeq,hCeq] at hb

#print axioms physical_model_legendre_near_integer_count

private theorem physical_model_legendre_count_optimized
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ m K : ℝ, 0 < δ ∧ 0 < m ∧ 0 < K ∧
      ∀ (F : ℝ → ℝ) (T P q k a₀ η : ℝ) (N : ℕ) (I : Finset ℕ),
      0 < T → 0 < P → 0 < q → 0 < k → 0 ≤ η →
      Expdb.IsApproximateModelPhaseFunction F σ 4 δ →
      let f := fun x => T*F (x/P)
      let h := fun x => iteratedDeriv 2 f x/2
      let c := Function.invFunOn h (Ioo P (2*P))
      let Φ := fun v => deriv f (c v)-2*v*c v
      let Ψ := fun s => q*(Φ (s/q+k)-Φ (s/q))
      let μ := m*k*P^7/(q^2*T^3)
      (∀ s∈Icc a₀ (a₀+N), s/q∈h '' Ioo P (2*P) ∧ s/q+k∈h '' Ioo P (2*P)) →
      I ⊆ Finset.range N →
      (∀ n∈I, ∃ e : ℤ, |Ψ (a₀+n)-(e:ℝ)| ≤ η) →
      (I.card:ℝ) ≤ K*((N:ℝ)*(η+μ^((1:ℝ)/7))+Real.sqrt N*μ^(-(1:ℝ)/6)) := by
  obtain ⟨δ,m,C,hδ,hm,hC,hsource⟩ := physical_model_legendre_near_integer_count hσ
  let K := 4+240*C
  refine ⟨δ,m,K,hδ,hm,by dsimp only [K]; positivity,?_⟩
  intro F T P q k a₀ η N I hT hP hq hk hη hF f h c Φ Ψ μ hdom hI hnear
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  let b := μ^((1:ℝ)/7)
  let S := Real.sqrt N*μ^(-(1:ℝ)/6)
  let W := 2*max η b
  have hb : 0 < b := Real.rpow_pos_of_pos hμ _
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hW : 0 < W := by dsimp only [W]; have hh := hb.trans_le (le_max_right η b); positivity
  have hmax : max η b ≤ η+b := max_le (le_add_of_nonneg_right hb.le) (le_add_of_nonneg_left hη)
  have hKW : 4 ≤ K := by dsimp only [K]; linarith only [hC]
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have htotal : 0 ≤ (N:ℝ)*(η+b)+S := by positivity
  by_cases hsmall : W ≤ 1/2
  · have hne' n (hn : n∈I) : ∃ e : ℤ, |Ψ (a₀+n)-(e:ℝ)| ≤ W/2 := by
      obtain ⟨e,he⟩ := hnear n hn
      refine ⟨e,he.trans ?_⟩
      dsimp only [W]
      linarith only [le_max_left η b]
    have hh₀ := hsource F T P q k a₀ W N I hT hP hq hk hW hsmall hF hdom hI hne'
    have hh : (I.card:ℝ) ≤ 2*W*N+200*C*N*μ^((1:ℝ)/6)*W^(-(1:ℝ)/6)+40*C*S := by
      simpa only [S,μ,mul_assoc] using hh₀
    have hbW : b ≤ W := by
      have hm' := le_max_right η b
      dsimp only [W]
      linarith only [hm',hb]
    have hwgt : μ^((1:ℝ)/6)*W^(-(1:ℝ)/6) ≤ b := by
      calc
        _ ≤ μ^((1:ℝ)/6)*b^(-(1:ℝ)/6) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hb hbW (by norm_num)) (by positivity)
        _ = _ := by
          dsimp only [b]
          rw [←Real.rpow_mul hμ.le,←Real.rpow_add hμ]
          norm_num
    have hvol : 2*W*(N:ℝ) ≤ 4*(N:ℝ)*(η+b) := by
      have hh' := mul_le_mul_of_nonneg_right hmax hN
      dsimp only [W]
      nlinarith only [hh']
    have hmid := mul_le_mul_of_nonneg_left hwgt (by positivity : 0 ≤ 200*C*(N:ℝ))
    have hupper : (I.card:ℝ) ≤ 4*(N:ℝ)*(η+b)+200*C*(N:ℝ)*b+40*C*S := by
      nlinarith only [hh,hvol,hmid]
    change (I.card:ℝ) ≤ K*((N:ℝ)*(η+b)+S)
    apply hupper.trans
    dsimp only [K]
    nlinarith only [mul_nonneg hC.le (mul_nonneg hN hη),
      mul_nonneg hC.le (mul_nonneg hN hb.le),mul_nonneg hC.le hS,hS]
  · have hlarge : 1 ≤ 4*(η+b) := by
      dsimp only [W] at hsmall
      linarith only [hmax,lt_of_not_ge hsmall]
    have hi : (I.card:ℝ) ≤ N := by exact_mod_cast (Finset.card_le_card hI).trans_eq (Finset.card_range N)
    have hh := mul_le_mul_of_nonneg_left hlarge hN
    have hh' := mul_le_mul_of_nonneg_right hKW htotal
    change (I.card:ℝ) ≤ K*((N:ℝ)*(η+b)+S)
    nlinarith only [hi,hh,hh',hS]

#print axioms physical_model_legendre_count_optimized

private theorem physical_model_legendre_integer_set_count
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ m K : ℝ, 0 < δ ∧ 0 < m ∧ 0 < K ∧
      ∀ (F : ℝ → ℝ) (T P q k η V : ℝ) (J : Finset ℤ),
      0 < T → 0 < P → 0 < q → 0 < k → 0 ≤ η → 0 ≤ V →
      Expdb.IsApproximateModelPhaseFunction F σ 4 δ →
      let f := fun x => T*F (x/P)
      let h := fun x => iteratedDeriv 2 f x/2
      let c := Function.invFunOn h (Ioo P (2*P))
      let Φ := fun v => deriv f (c v)-2*v*c v
      let Ψ := fun s => q*(Φ (s/q+k)-Φ (s/q))
      let μ := m*k*P^7/(q^2*T^3)
      (∀ a∈J, (a:ℝ)/q∈h '' Ioo P (2*P) ∧ (a:ℝ)/q+k∈h '' Ioo P (2*P)) →
      (∀ a∈J, ∀ b∈J, (a:ℝ)-b ≤ V) →
      (∀ a∈J, ∃ e : ℤ, |Ψ a-(e:ℝ)| ≤ η) →
      (J.card:ℝ) ≤ 1+K*(V*(η+μ^((1:ℝ)/7))+Real.sqrt V*μ^(-(1:ℝ)/6)) := by
  obtain ⟨δ,m,K,hδ,hm,hK,hsource⟩ := physical_model_legendre_count_optimized hσ
  refine ⟨δ,m,K,hδ,hm,hK,?_⟩
  intro F T P q k η V J hT hP hq hk hη hV hF f h c Φ Ψ μ hdom hspan hnear
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  by_cases hJ : J.Nonempty
  · let a₀ := J.min' hJ
    let a₁ := J.max' hJ
    let N := (a₁-a₀).toNat
    let I := (J.erase a₁).image (fun a => (a-a₀).toNat)
    have ha₀ : a₀∈J := Finset.min'_mem J hJ
    have ha₁ : a₁∈J := Finset.max'_mem J hJ
    have hlo a (ha : a∈J) : a₀ ≤ a := Finset.min'_le J a ha
    have hhi a (ha : a∈J) : a ≤ a₁ := Finset.le_max' J a ha
    have hNcast : (N:ℤ)=a₁-a₀ := Int.toNat_of_nonneg (sub_nonneg.mpr (hlo a₁ ha₁))
    have hNreal : (a₀:ℝ)+(N:ℝ)=(a₁:ℝ) := by
      have hh : (N:ℝ)=(a₁:ℝ)-a₀ := by exact_mod_cast hNcast
      linarith only [hh]
    have hI : I ⊆ Finset.range N := by
      intro n hn
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
      have haJ := (Finset.mem_erase.mp ha).2
      have hne := (Finset.mem_erase.mp ha).1
      have hl := hlo a haJ
      have hh := hhi a haJ
      apply Finset.mem_range.mpr
      dsimp only [N]
      omega
    have hinj : Set.InjOn (fun a : ℤ => (a-a₀).toNat) (↑(J.erase a₁):Set ℤ) := by
      intro a ha b hb he
      have haJ := (Finset.mem_erase.mp ha).2
      have hbJ := (Finset.mem_erase.mp hb).2
      have hl := hlo a haJ
      have hl' := hlo b hbJ
      change (a-a₀).toNat=(b-a₀).toNat at he
      omega
    have hcard : I.card+1=J.card := by
      rw [show I.card=(J.erase a₁).card from Finset.card_image_of_injOn hinj]
      exact Finset.card_erase_add_one ha₁
    have hcont : ContinuousOn h (Ioo P (2*P)) := by
      intro x hx
      have hu : x/P∈Ioo (1:ℝ) 2 := ⟨
        (lt_div_iff₀ hP).mpr (by simpa only [one_mul] using hx.1),
        (div_lt_iff₀ hP).mpr hx.2⟩
      have hfc : ContDiffAt ℝ ∞ f x := by
        dsimp only [f]
        exact contDiffAt_const.mul ((approximateModelPhase_contDiffAt hF hu).comp x (by fun_prop))
      exact ((contDiffAt_iteratedDeriv_infty hfc 2).continuousAt.div_const 2).continuousWithinAt
    have hinterval {v w : ℝ} (hv : v∈h '' Ioo P (2*P)) (hw : w∈h '' Ioo P (2*P)) :
        Icc v w ⊆ h '' Ioo P (2*P) := by
      obtain ⟨x,hx,he⟩ := hv
      obtain ⟨y,hy,he'⟩ := hw
      simpa only [he,he'] using isPreconnected_Ioo.intermediate_value hx hy hcont
    have hdomI s (hs : s∈Icc (a₀:ℝ) ((a₀:ℝ)+N)) :
        s/q∈h '' Ioo P (2*P) ∧ s/q+k∈h '' Ioo P (2*P) := by
      rw [hNreal] at hs
      have hsl := div_le_div_of_nonneg_right hs.1 hq.le
      have hsr := div_le_div_of_nonneg_right hs.2 hq.le
      exact ⟨hinterval (hdom a₀ ha₀).1 (hdom a₁ ha₁).1 ⟨hsl,hsr⟩,
        hinterval (hdom a₀ ha₀).2 (hdom a₁ ha₁).2
          ⟨add_le_add hsl le_rfl,add_le_add hsr le_rfl⟩⟩
    have hnearI n (hn : n∈I) : ∃ e : ℤ, |Ψ ((a₀:ℝ)+n)-(e:ℝ)| ≤ η := by
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
      have haJ := (Finset.mem_erase.mp ha).2
      have he : (a₀:ℝ)+((a-a₀).toNat:ℝ)=(a:ℝ) := by
        have hh := Int.toNat_of_nonneg (sub_nonneg.mpr (hlo a haJ))
        have hh' : ((a-a₀).toNat:ℝ)=(a:ℝ)-a₀ := by exact_mod_cast hh
        linarith only [hh']
      rw [he]
      exact hnear a haJ
    have hb := hsource F T P q k (a₀:ℝ) η N I hT hP hq hk hη hF hdomI hI hnearI
    have hNV : (N:ℝ) ≤ V := by
      have hh := hspan a₁ ha₁ a₀ ha₀
      linarith only [hh,hNreal]
    have hb' : (I.card:ℝ) ≤ K*(V*(η+μ^((1:ℝ)/7))+Real.sqrt V*μ^(-(1:ℝ)/6)) := by
      apply hb.trans
      gcongr
    have hcR : (I.card:ℝ)+1=J.card := by exact_mod_cast hcard
    linarith only [hb',hcR]
  · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms physical_model_legendre_integer_set_count

private theorem physical_model_fixed_shift_pair_count
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ m K : ℝ, 0 < δ ∧ 0 < m ∧ 0 < K ∧
      ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
        (F : ℝ → ℝ) (z : ι → ℝ) (center block label : ι → ℤ)
        (H Bmul : ℕ) (s : ℤ) (T P q k η V : ℝ),
      0 < H → 0 < T → 0 < P → 0 < q → 0 < k → 0 ≤ η → 0 ≤ V →
      Expdb.IsApproximateModelPhaseFunction F σ 4 δ →
      (∀ i∈S, z i∈Ioo P (2*P)) →
      (∀ i∈S, |z i-center i| ≤ 1/2) →
      (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
        s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
      (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
      R ⊆ S ×ˢ S →
      let f := fun x => T*F (x/P)
      let h := fun x => iteratedDeriv 2 f x/2
      let μ := m*k*P^7/(q^2*T^3)
      (∀ ij∈R, h (z ij.1)=(label ij.1:ℝ)/q ∧ h (z ij.2)=(label ij.1:ℝ)/q+k) →
      (∀ ij∈R, ∀ uv∈R, (label ij.1:ℝ)-label uv.1 ≤ V) →
      (∀ ij∈R, ∃ e : ℤ, |(q*deriv f (z ij.2)-2*q*h (z ij.2)*z ij.2)-
        (q*deriv f (z ij.1)-2*q*h (z ij.1)*z ij.1)-(e:ℝ)| ≤ η) →
      (R.card:ℝ) ≤ (4*(Bmul:ℝ))^2*
        (1+K*(V*(η+μ^((1:ℝ)/7))+Real.sqrt V*μ^(-(1:ℝ)/6))) := by
  obtain ⟨δ₀,m,K,hδ₀,hm,hK,hcount⟩ := physical_model_legendre_integer_set_count hσ
  obtain ⟨δ₁,c,u,dlo,dhi,hδ₁,hc,hu,hdlo,hdhi,hdata⟩ := physical_model_fifth_derivative_data hσ
  refine ⟨min δ₀ δ₁,m,K,lt_min hδ₀ hδ₁,hm,hK,?_⟩
  intro ι inst S R F z center block label H Bmul s T P q k η V
    hH hT hP hq hk hη hV hF hz hround hspan hmul hRS f h μ hlevel hwidth hnear
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left δ₀ δ₁)
  have hF₁ := approximateModelPhase_mono hF le_rfl (min_le_right δ₀ δ₁)
  have hd := hdata F T P hT hP hF₁
  have hL : 0 < c*T/P^3 := by positivity
  have hf4 x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ 4 f x := (hd.1 x hx).of_le (by norm_num)
  have hp := inverse_curvature_derivative f hL hf4 (fun x hx => (hd.2.1 x hx).1)
  have hmulLevel := bourgain_curvature_level_block_multiplicity S f z center block H Bmul s
    hH hL hf4 (fun x hx => (hd.2.1 x hx).1) hz hround hspan hmul
  have hRmem ij (hij : ij∈R) : ij.1∈S ∧ ij.2∈S := Finset.mem_product.mp (hRS hij)
  let J := R.image (fun ij => label ij.1)
  let ci := Function.invFunOn h (Ioo P (2*P))
  let Φ := fun v => deriv f (ci v)-2*v*ci v
  let Ψ := fun a => q*(Φ (a/q+k)-Φ (a/q))
  have hdomJ a (ha : a∈J) : (a:ℝ)/q∈h '' Ioo P (2*P) ∧ (a:ℝ)/q+k∈h '' Ioo P (2*P) := by
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨⟨z ij.1,hz _ (hRmem ij hij).1,(hlevel ij hij).1⟩,
      ⟨z ij.2,hz _ (hRmem ij hij).2,(hlevel ij hij).2⟩⟩
  have hwidthJ a (ha : a∈J) b (hb : b∈J) : (a:ℝ)-b ≤ V := by
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨uv,huv,rfl⟩ := Finset.mem_image.mp hb
    exact hwidth ij hij uv huv
  have hnearJ a (ha : a∈J) : ∃ e : ℤ, |Ψ a-(e:ℝ)| ≤ η := by
    obtain ⟨ij,hij,rfl⟩ := Finset.mem_image.mp ha
    have hi := (hRmem ij hij).1
    have hj := (hRmem ij hij).2
    have hci : ci ((label ij.1:ℝ)/q)=z ij.1 := by
      rw [←(hlevel ij hij).1]
      exact hp.1 _ (hz _ hi)
    have hcj : ci ((label ij.1:ℝ)/q+k)=z ij.2 := by
      rw [←(hlevel ij hij).2]
      exact hp.1 _ (hz _ hj)
    have he : Ψ (label ij.1)=
        (q*deriv f (z ij.2)-2*q*h (z ij.2)*z ij.2)-
        (q*deriv f (z ij.1)-2*q*h (z ij.1)*z ij.1) := by
      dsimp only [Ψ,Φ]
      rw [hci,hcj,(hlevel ij hij).1,(hlevel ij hij).2]
      ring
    rw [he]
    exact hnear ij hij
  have hJ := hcount F T P q k η V J hT hP hq hk hη hV hF₀ hdomJ hwidthJ hnearJ
  have hfiber a : (R.filter (fun ij => label ij.1=a)).card ≤ (4*Bmul)^2 := by
    have hsub : R.filter (fun ij => label ij.1=a) ⊆
        (S.filter (fun i => h (z i)=(a:ℝ)/q)) ×ˢ
          (S.filter (fun j => h (z j)=(a:ℝ)/q+k)) := by
      intro ij hij
      obtain ⟨hij,he⟩ := Finset.mem_filter.mp hij
      have hl := hlevel ij hij
      rw [he] at hl
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨(hRmem ij hij).1,hl.1⟩,
        Finset.mem_filter.mpr ⟨(hRmem ij hij).2,hl.2⟩⟩
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ = _ := Finset.card_product _ _
      _ ≤ (4*Bmul)*(4*Bmul) := Nat.mul_le_mul (hmulLevel _) (hmulLevel _)
      _ = _ := by ring
  have hcard : (R.card:ℝ)=∑ a∈J,((R.filter (fun ij => label ij.1=a)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun (ij : ι × ι) hij =>
      Finset.mem_image_of_mem (fun (uv : ι × ι) => label uv.1) hij)
  calc
    _ = _ := hcard
    _ ≤ ∑ _a∈J,(4*(Bmul:ℝ))^2 := Finset.sum_le_sum (fun a _ha => by exact_mod_cast hfiber a)
    _ = (4*(Bmul:ℝ))^2*(J.card:ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ (sq_nonneg _)

#print axioms physical_model_fixed_shift_pair_count

private theorem physical_model_four_coordinate_fixed_shift_count
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ m K u : ℝ, 0 < δ ∧ 0 < m ∧ 0 < K ∧ 0 < u ∧
      ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
        (F : ℝ → ℝ) (z : ι → ℝ) (center block label inverse : ι → ℤ)
        (parity : ι → Fin 2) (H Bmul M q Q : ℕ) [NeZero M] (s : ℤ) (T P k : ℝ),
      0 < H → 0 < T → 0 < P → 0 < q → q ≤ Q → 0 < k →
      Expdb.IsApproximateModelPhaseFunction F σ 4 δ →
      (∀ i∈S, z i∈Ioo P (2*P)) →
      (∀ i∈S, (center i:ℝ)∈Ioo P (2*P)) →
      (∀ i∈S, |z i-center i| ≤ 1/2) →
      (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
        s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
      (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
      (∀ i∈S, (q:ℤ) ∣ label i*inverse i-1) →
      R ⊆ S ×ˢ S →
      let f := fun x => T*F (x/P)
      let h := fun x => iteratedDeriv 2 f x/2
      let U := u*T/P^3
      let V := 3*(q:ℝ)*U*P
      let D := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
        Real.sqrt (U*(Q:ℝ)^3)
      let η := 2*D+9*(q:ℝ)*U/4
      let μ := m*k*P^7/((q:ℝ)^2*T^3)
      let mu := fun i => iteratedDeriv 3 f (center i)/6
      let ell := fun i => iteratedDeriv 1 f (center i)
      let b := fun i => (⌊(q:ℝ)*ell i⌋:ℤ)+(parity i:ℕ)
      let tau := fun i => ((b i:ℝ)-(q:ℝ)*ell i)/2
      let coeff := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q:ℝ))))^3
      let Y := fun i => (![Int.fract (-(inverse i:ℝ)*b i/q),Int.fract (-(inverse i:ℝ)/q),
        coeff i/Real.sqrt M,(3*coeff i*tau i/2)/Real.sqrt M] : Fin 4 → ℝ)
      let window : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      (∀ i∈S, h (z i)=(label i:ℝ)/q) →
      (∀ ij∈R, h (z ij.2)=h (z ij.1)+k) →
      (∀ ij∈R, ∀ j, |Y ij.1 j-Y ij.2 j| ≤ 2*window j) →
      (R.card:ℝ) ≤ (4*(Bmul:ℝ))^2*
        (1+K*(V*(η+μ^((1:ℝ)/7))+Real.sqrt V*μ^(-(1:ℝ)/6))) := by
  obtain ⟨δ₀,m,K,hδ₀,hm,hK,hcount⟩ := physical_model_fixed_shift_pair_count hσ
  obtain ⟨δ₁,c,u,dlo,dhi,hδ₁,hc,hu,hdlo,hdhi,hdata⟩ := physical_model_fifth_derivative_data hσ
  refine ⟨min δ₀ δ₁,m,K,u,lt_min hδ₀ hδ₁,hm,hK,hu,?_⟩
  intro ι inst S R F z center block label inverse parity H Bmul M q Q instM s T P k
    hH hT hP hq hqQ hk hF hz hcenter hround hspan hmul hinverse hRS
    f h U V D η μ mu ell b tau coeff Y window hlevel hshift hnear
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left δ₀ δ₁)
  have hF₁ := approximateModelPhase_mono hF le_rfl (min_le_right δ₀ δ₁)
  have hd := hdata F T P hT hP hF₁
  have hU : 0 < U := by dsimp only [U]; positivity
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hRmem ij (hij : ij∈R) : ij.1∈S ∧ ij.2∈S := Finset.mem_product.mp (hRS hij)
  have hf3 x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ 3 f x := (hd.1 x hx).of_le (by norm_num)
  have hf4 x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ 4 f x := (hd.1 x hx).of_le (by norm_num)
  have hthree x (hx : x∈Ioo P (2*P)) : 0 < iteratedDeriv 3 f x ∧
      iteratedDeriv 3 f x ≤ 6*U := by
    exact ⟨lt_of_lt_of_le (by positivity : 0 < c*T/P^3) (hd.2.1 x hx).1,
      (hd.2.1 x hx).2⟩
  have hsegment i (hi : i∈S) : uIcc (z i) (center i:ℝ) ⊆ Ioo P (2*P) := by
    intro x hx
    have hl := lt_min (hz i hi).1 (hcenter i hi).1
    have hr := max_lt (hz i hi).2 (hcenter i hi).2
    exact ⟨hl.trans_le hx.1,hx.2.trans_lt hr⟩
  have hhder x (hx : x∈Ioo P (2*P)) :
      HasDerivWithinAt h (iteratedDeriv 3 f x/2) (Ioo P (2*P)) x := by
    have hh := contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf4 x hx)
    simpa only [h,iteratedDeriv_succ] using
      ((hh.differentiableAt (by norm_num)).hasDerivAt.div_const 2).hasDerivWithinAt
  have hwidth ij (hij : ij∈R) uv (huv : uv∈R) :
      (label ij.1:ℝ)-label uv.1 ≤ V := by
    have hi := hz _ (hRmem ij hij).1
    have hj := hz _ (hRmem uv huv).1
    have hb := (convex_Ioo P (2*P)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (C:=3*U) hhder (by
        intro x hx
        rw [Real.norm_eq_abs,abs_of_pos (div_pos (hthree x hx).1 (by norm_num))]
        linarith only [(hthree x hx).2]) hj hi
    rw [Real.norm_eq_abs,Real.norm_eq_abs] at hb
    have hdistance : |z ij.1-z uv.1| ≤ P := abs_le.mpr (by constructor <;> linarith only [hi.1,hi.2,hj.1,hj.2])
    have he : (label ij.1:ℝ)-label uv.1=(q:ℝ)*(h (z ij.1)-h (z uv.1)) := by
      rw [hlevel _ (hRmem ij hij).1,hlevel _ (hRmem uv huv).1]
      field_simp
    rw [he]
    calc
      _ ≤ (q:ℝ)*|h (z ij.1)-h (z uv.1)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hqr.le
      _ ≤ (q:ℝ)*(3*U*P) := mul_le_mul_of_nonneg_left
        (hb.trans (mul_le_mul_of_nonneg_left hdistance (by positivity))) hqr.le
      _ = V := by dsimp only [V]; ring
  have hscalar ij (hij : ij∈R) : ∃ e : ℤ,
      |((q:ℝ)*deriv f (z ij.2)-2*(q:ℝ)*h (z ij.2)*z ij.2)-
        ((q:ℝ)*deriv f (z ij.1)-2*(q:ℝ)*h (z ij.1)*z ij.1)-(e:ℝ)| ≤ η := by
    have hi := (hRmem ij hij).1
    have hj := (hRmem ij hij).2
    have hseg : uIcc (z ij.1) (center ij.1:ℝ) ∪ uIcc (z ij.2) (center ij.2:ℝ) ⊆
        Ioo P (2*P) := union_subset (hsegment _ hi) (hsegment _ hj)
    obtain ⟨α,β,γ,d,e₁,e₂,_hdet,_ha,_hden,_hγ,_hfirst,_hsecond,e,he⟩ :=
      actual_source_resonance_curve_strip f M q q Q (label ij.1) (label ij.2)
        (inverse ij.1) (inverse ij.2) (center ij.1) (center ij.2) hq hq hqQ
        (by omega) (by omega) (hinverse _ hi) (hinverse _ hj)
        (fun x hx => hf3 x (hseg hx))
        (fun x hx => by rw [abs_of_pos (hthree x (hseg hx)).1]; exact (hthree x (hseg hx)).2)
        (by simpa only [abs_sub_comm] using hround _ hi)
        (by simpa only [abs_sub_comm] using hround _ hj)
        (hthree _ (hcenter _ hi)).1 (hthree _ (hcenter _ hj)).1
        (hlevel _ hi) (hlevel _ hj) (parity ij.1) (parity ij.2) (hnear ij hij)
    refine ⟨e,?_⟩
    have heq i (hiS : i∈S) : 2*(q:ℝ)*h (z i)*z i=2*(label i:ℝ)*z i := by
      rw [hlevel i hiS]
      field_simp
    rw [heq _ hi,heq _ hj]
    exact he
  exact hcount S R F z center block label H Bmul s T P q k η V hH hT hP hqr hk
    (by dsimp only [η,D]; positivity) (by dsimp only [V]; positivity)
    hF₀ hz hround hspan hmul hRS
    (fun ij hij => ⟨hlevel _ (hRmem ij hij).1,
      (hshift ij hij).trans (by rw [hlevel _ (hRmem ij hij).1])⟩) hwidth hscalar

#print axioms physical_model_four_coordinate_fixed_shift_count

private theorem source_four_coordinate_integer_shift_bound
    (f : ℝ → ℝ) (M q q' Q : ℕ) [NeZero M]
    (a a' r r' m n : ℤ) {A B x y U lam : ℝ}
    (hq : 0 < q) (hq' : 0 < q') (hqQ : q ≤ Q) (hqQ' : q' ≤ Q)
    (hthin : (Q:ℝ)^2 < 6*(M:ℝ)^2) (hlam : 0 < lam) (hU : 0 < U)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 4 f t)
    (hthree : ∀ t∈Ioo A B, 0 < iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U)
    (hfour : ∀ t∈Ioo A B, lam ≤ |iteratedDeriv 4 f t|)
    (hx : x∈Ioo A B) (hy : y∈Ioo A B)
    (hm : (m:ℝ)∈Ioo A B) (hn : (n:ℝ)∈Ioo A B)
    (hround : |x-m| ≤ 1/2) (hround' : |y-n| ≤ 1/2)
    (har : (q:ℤ) ∣ a*r-1) (har' : (q':ℤ) ∣ a'*r'-1)
    (hlevel : iteratedDeriv 2 f x/2=(a:ℝ)/q)
    (hlevel' : iteratedDeriv 2 f y/2=(a':ℝ)/q')
    (hinverse : |Int.fract (-(r:ℝ)/q)-Int.fract (-(r':ℝ)/q')| ≤ 1/(6*(M:ℝ)^2)) :
    let mu := iteratedDeriv 3 f m/6
    let nu := iteratedDeriv 3 f n/6
    let K := fun (t d : ℝ) => -2*t*(Real.sqrt (2/(3*t*d)))^3
    let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
    |K mu q/Real.sqrt M-K nu q'/Real.sqrt M| ≤ 1/(6*(M:ℝ)^2) →
    q=q' ∧ ∃ k : ℤ, iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2=(k:ℝ) ∧
      |(k:ℝ)| ≤ 3*U*(rho+1) := by
  intro mu nu K rho hdual
  have hMr : 0 < (M:ℝ) := by exact_mod_cast NeZero.pos M
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hqQr : (q:ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqQ'r : (q':ℝ) ≤ Q := by exact_mod_cast hqQ'
  have hsM : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hMr
  have hsmall : (1/(6*(M:ℝ)^2))*(q:ℝ)*q' < 1 := by
    have hh : (q:ℝ)*q' < 6*(M:ℝ)^2 :=
      (mul_le_mul hqQr hqQ'r (by positivity) (by positivity)).trans_lt
        (by simpa only [pow_two] using hthin)
    have he : (1/(6*(M:ℝ)^2))*(q:ℝ)*q'=((q:ℝ)*q')/(6*(M:ℝ)^2) := by ring
    rw [he]
    exact (div_lt_one (by positivity)).mpr hh
  have hdual' : |K mu q-K nu q'| ≤ Real.sqrt M/(6*(M:ℝ)^2) := by
    rw [←sub_div,abs_div,abs_of_pos hsM] at hdual
    have hh := (div_le_iff₀ hsM).mp hdual
    exact hh.trans_eq (by ring)
  have hsub : Icc (min (m:ℝ) n) (max (m:ℝ) n) ⊆ Ioo A B := by
    intro t ht
    exact ⟨(lt_min hm.1 hn.1).trans_le ht.1,ht.2.trans_lt (max_lt hm.2 hn.2)⟩
  have hmu : 0 < mu := by dsimp only [mu]; positivity [(hthree m hm).1]
  have hnu : 0 < nu := by dsimp only [nu]; positivity [(hthree n hn).1]
  have hmuU : mu ≤ U := by dsimp only [mu]; linarith only [(hthree m hm).2]
  have hnuU : nu ≤ U := by dsimp only [nu]; linarith only [(hthree n hn).2]
  obtain ⟨heq,hdiv,hdist⟩ := bourgain_upper_triangular_source_spacing f hlam m n
    (show (m:ℝ)∈Icc (min (m:ℝ) n) (max (m:ℝ) n) from ⟨min_le_left _ _,le_max_left _ _⟩)
    (show (n:ℝ)∈Icc (min (m:ℝ) n) (max (m:ℝ) n) from ⟨min_le_right _ _,le_max_right _ _⟩)
    (fun t ht => hf t (hsub ht)) (fun t ht => hfour t (hsub ht))
    a a' r r' q q' hq hq' har har' hinverse hsmall hmu hmuU hnu hnuU hdual'
  have hdist' : |(m:ℝ)-n| ≤ rho := by
    apply hdist.trans
    dsimp only [rho]
    gcongr
  have hxy : |y-x| ≤ rho+1 := by
    calc
      _ = |(y-n)+((n:ℝ)-m)+((m:ℝ)-x)| := by congr 1; ring
      _ ≤ |y-n|+|(n:ℝ)-m|+|(m:ℝ)-x| := abs_add_three _ _ _
      _ ≤ 1/2+rho+1/2 := by
        rw [abs_sub_comm (n:ℝ) (m:ℝ),abs_sub_comm (m:ℝ) x]
        exact add_le_add (add_le_add hround' hdist') hround
      _ = _ := by ring
  have hd t (ht : t∈Ioo A B) :
      HasDerivWithinAt (fun t => iteratedDeriv 2 f t/2)
        (iteratedDeriv 3 f t/2) (Ioo A B) t := by
    have hh := contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf t ht)
    simpa only [iteratedDeriv_succ] using
      ((hh.differentiableAt (by norm_num)).hasDerivAt.div_const 2).hasDerivWithinAt
  have hleveldist := (convex_Ioo A B).norm_image_sub_le_of_norm_hasDerivWithin_le (C:=3*U) hd
    (by
      intro t ht
      rw [Real.norm_eq_abs,abs_of_pos (div_pos (hthree t ht).1 (by norm_num))]
      linarith only [(hthree t ht).2]) hx hy
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at hleveldist
  obtain ⟨k,hk⟩ := hdiv
  refine ⟨heq,k,?_,?_⟩
  · rw [hlevel,hlevel',←heq]
    have hkR : (a':ℝ)-a=(q:ℝ)*k := by exact_mod_cast hk
    field_simp
    nlinarith only [hkR]
  · have hkR : (a':ℝ)-a=(q:ℝ)*k := by exact_mod_cast hk
    have he : iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2=(k:ℝ) := by
      rw [hlevel,hlevel',←heq]
      field_simp
      nlinarith only [hkR]
    rw [he] at hleveldist
    exact hleveldist.trans (mul_le_mul_of_nonneg_left hxy (by positivity))

#print axioms source_four_coordinate_integer_shift_bound

private theorem physical_model_four_coordinate_band_count
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ m K u : ℝ, 0 < δ ∧ 0 < m ∧ 0 < K ∧ 0 < u ∧
      ∀ {ι : Type*} [DecidableEq ι] (S : Finset ι)
        (F : ℝ → ℝ) (z : ι → ℝ) (center block label inverse : ι → ℤ)
        (q : ι → ℕ) (parity : ι → Fin 2) (H Bmul M Q : ℕ) [NeZero M]
        (s : ℤ) (T P lam : ℝ),
      0 < H → 0 < T → 0 < P → 0 < Q → 0 < lam →
      (Q:ℝ)^2 < 6*(M:ℝ)^2 →
      Expdb.IsApproximateModelPhaseFunction F σ 4 δ →
      (∀ i∈S, z i∈Ioo P (2*P)) →
      (∀ i∈S, (center i:ℝ)∈Ioo P (2*P)) →
      (∀ i∈S, |z i-center i| ≤ 1/2) →
      (∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
        s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ)) →
      (∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul) →
      (∀ i∈S, 0 < q i ∧ q i ≤ Q ∧ Q ≤ 2*q i) →
      (∀ i∈S, (q i:ℤ) ∣ label i*inverse i-1) →
      let f := fun x => T*F (x/P)
      let h := fun x => iteratedDeriv 2 f x/2
      let U := u*T/P^3
      let V := 3*(Q:ℝ)*U*P
      let D := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
        Real.sqrt (U*(Q:ℝ)^3)
      let η := 2*D+9*(Q:ℝ)*U/4
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
      let Lshift := 3*U*(rho+1)
      let μlo := m*P^7/((Q:ℝ)^2*T^3)
      let μhi := 4*m*Lshift*P^7/((Q:ℝ)^2*T^3)
      let mu := fun i => iteratedDeriv 3 f (center i)/6
      let ell := fun i => iteratedDeriv 1 f (center i)
      let b := fun i => (⌊(q i:ℝ)*ell i⌋:ℤ)+(parity i:ℕ)
      let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
      let coeff := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
      let Y := fun i => (![Int.fract (-(inverse i:ℝ)*b i/q i),Int.fract (-(inverse i:ℝ)/q i),
        coeff i/Real.sqrt M,(3*coeff i*tau i/2)/Real.sqrt M] : Fin 4 → ℝ)
      let window : Fin 4 → ℝ :=
        ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
      let R := (S ×ˢ S).filter (fun ij => ∀ j, |Y ij.1 j-Y ij.2 j| ≤ 2*window j)
      (∀ i∈S, h (z i)=(label i:ℝ)/q i) →
      (∀ x∈Ioo P (2*P), lam ≤ |iteratedDeriv 4 f x|) →
      (R.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card+
        2*(Q:ℝ)*Lshift*(4*(Bmul:ℝ))^2*
          (1+K*(V*(η+μhi^((1:ℝ)/7))+Real.sqrt V*μlo^(-(1:ℝ)/6))) := by
  classical
  obtain ⟨δ₀,m,K,u₀,hδ₀,hm,hK,hu₀,hcount⟩ := physical_model_four_coordinate_fixed_shift_count hσ
  obtain ⟨δ₁,c,u₁,dlo,dhi,hδ₁,hc,hu₁,hdlo,hdhi,hdata⟩ := physical_model_fifth_derivative_data hσ
  refine ⟨min δ₀ δ₁,m,K,max u₀ u₁,lt_min hδ₀ hδ₁,hm,hK,lt_max_of_lt_left hu₀,?_⟩
  intro ι inst S F z center block label inverse q parity H Bmul M Q instM s T P lam
    hH hT hP hQ hlam hthin hF hz hcenter hround hspan hmul hq hinverse
    f h U V D η rho Lshift μlo μhi mu ell b tau coeff Y window R hlevel hfour
  have hF₀ := approximateModelPhase_mono hF le_rfl (min_le_left δ₀ δ₁)
  have hF₁ := approximateModelPhase_mono hF le_rfl (min_le_right δ₀ δ₁)
  have hd := hdata F T P hT hP hF₁
  have hU : 0 < U := by dsimp only [U]; positivity
  have hQr : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hMr : 0 < (M:ℝ) := by exact_mod_cast NeZero.pos M
  have hL : 0 < Lshift := by dsimp only [Lshift,rho]; positivity
  have hμlo : 0 < μlo := by dsimp only [μlo]; positivity
  have hμhi : 0 < μhi := by dsimp only [μhi]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hη : 0 ≤ η := by dsimp only [η,D]; positivity
  have hUU : u₀*T/P^3 ≤ U := by dsimp only [U]; gcongr; exact le_max_left _ _
  have hf4 x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ 4 f x := (hd.1 x hx).of_le (by norm_num)
  have hthree x (hx : x∈Ioo P (2*P)) : 0 < iteratedDeriv 3 f x ∧
      iteratedDeriv 3 f x ≤ 6*U := by
    refine ⟨lt_of_lt_of_le (by positivity : 0 < c*T/P^3) (hd.2.1 x hx).1,?_⟩
    apply (hd.2.1 x hx).2.trans
    dsimp only [U]
    gcongr
    exact le_max_right _ _
  have hRmem ij (hij : ij∈R) : ij.1∈S ∧ ij.2∈S :=
    Finset.mem_product.mp (Finset.mem_filter.mp hij).1
  have hRnear ij (hij : ij∈R) : ∀ j, |Y ij.1 j-Y ij.2 j| ≤ 2*window j :=
    (Finset.mem_filter.mp hij).2
  have hRsym ij (hij : ij∈R) : ij.swap∈R := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(hRmem ij hij).2,(hRmem ij hij).1⟩,?_⟩
    intro j
    change |Y ij.2 j-Y ij.1 j| ≤ 2*window j
    rw [abs_sub_comm]
    exact hRnear ij hij j
  have hshift ij (hij : ij∈R) :
      q ij.1=q ij.2 ∧ ∃ d : ℤ, h (z ij.2)-h (z ij.1)=(d:ℝ) ∧ |(d:ℝ)| ≤ Lshift := by
    have hi := (hRmem ij hij).1
    have hj := (hRmem ij hij).2
    apply source_four_coordinate_integer_shift_bound f M (q ij.1) (q ij.2) Q
      (label ij.1) (label ij.2) (inverse ij.1) (inverse ij.2) (center ij.1) (center ij.2)
      (hq _ hi).1 (hq _ hj).1 (hq _ hi).2.1 (hq _ hj).2.1 hthin hlam hU
      hf4 hthree hfour (hz _ hi) (hz _ hj) (hcenter _ hi) (hcenter _ hj)
      (hround _ hi) (hround _ hj) (hinverse _ hi) (hinverse _ hj)
      (hlevel _ hi) (hlevel _ hj)
    · have hh := hRnear ij hij 1
      change _ ≤ 2*(1/(12*(M:ℝ)^2)) at hh
      convert hh using 1
      ring
    · have hh := hRnear ij hij 2
      change _ ≤ 2*((1/(M:ℝ)^2)/12) at hh
      convert hh using 1
      ring
  let Z := R.filter (fun ij => h (z ij.1)=h (z ij.2))
  let Rp := R.filter (fun ij => h (z ij.1)<h (z ij.2))
  have hpmem ij (hij : ij∈Rp) : ij∈R ∧ h (z ij.1)<h (z ij.2) := Finset.mem_filter.mp hij
  have hRsplit : R ⊆ Z ∪ (Rp ∪ Rp.image Prod.swap) := by
    intro ij hij
    rcases lt_trichotomy (h (z ij.1)) (h (z ij.2)) with hh | hh | hh
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hij,hh⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hij,hh⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨ij.swap,Finset.mem_filter.mpr ⟨hRsym ij hij,hh⟩,Prod.swap_swap ij⟩
  have hsplit : R.card ≤ Z.card+2*Rp.card := by
    have hh := (Finset.card_le_card hRsplit).trans (Finset.card_union_le _ _)
    have hh' := Finset.card_union_le Rp (Rp.image Prod.swap)
    have he : (Rp.image Prod.swap).card=Rp.card := Finset.card_image_of_injective _ Prod.swap_injective
    omega
  have hmulLevel := bourgain_curvature_level_block_multiplicity S f z center block H Bmul s
    hH (by positivity : 0 < c*T/P^3) hf4 (fun x hx => (hd.2.1 x hx).1)
    hz hround hspan hmul
  have hZfiber i : (Z.filter (fun ij => ij.1=i)).card ≤ 4*Bmul := by
    have hsub : Z.filter (fun ij => ij.1=i) ⊆ {i} ×ˢ (S.filter (fun j => h (z j)=h (z i))) := by
      intro ij hij
      obtain ⟨hij,he⟩ := Finset.mem_filter.mp hij
      obtain ⟨hij,hh⟩ := Finset.mem_filter.mp hij
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr he,
        Finset.mem_filter.mpr ⟨(hRmem ij hij).2,by rw [←he]; exact hh.symm⟩⟩
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ = (S.filter (fun j => h (z j)=h (z i))).card := by simp only [Finset.card_product,Finset.card_singleton,one_mul]
      _ ≤ _ := hmulLevel _
  have hZ : (Z.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card := by
    have he : (Z.card:ℝ)=∑ i∈S,((Z.filter (fun ij => ij.1=i)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun (ij : ι × ι) hij =>
        (hRmem ij (Finset.mem_filter.mp hij).1).1)
    rw [he]
    calc
      _ ≤ ∑ _i∈S,4*(Bmul:ℝ) := Finset.sum_le_sum (fun i _hi => by exact_mod_cast hZfiber i)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hex (ij : ι × ι) : ∃ d : ℕ, ij∈Rp →
      0 < d ∧ h (z ij.2)=h (z ij.1)+(d:ℝ) ∧ (d:ℝ) ≤ Lshift := by
    by_cases hij : ij∈Rp
    · obtain ⟨_heq,d,he,hd⟩ := hshift ij (hpmem ij hij).1
      have hdr : 0 < (d:ℝ) := by linarith only [he,(hpmem ij hij).2]
      have hdi : 0 < d := by exact_mod_cast hdr
      have hdcast : (d.toNat:ℝ)=(d:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hdi.le
      refine ⟨d.toNat,fun _ => ⟨by omega,?_,?_⟩⟩
      · rw [hdcast]; linarith only [he]
      · rw [hdcast]; exact (le_abs_self _).trans hd
    · exact ⟨0,fun hh => False.elim (hij hh)⟩
  choose shift hshiftNat using hex
  let J := Finset.Icc 1 Q ×ˢ Finset.Icc 1 ⌊Lshift⌋₊
  let index := fun ij : ι × ι => (q ij.1,shift ij)
  have hindex ij (hij : ij∈Rp) : index ij∈J := by
    have hqij := hq ij.1 (hRmem ij (hpmem ij hij).1).1
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hqij.1,hqij.2.1⟩,
      Finset.mem_Icc.mpr ⟨(hshiftNat ij hij).1,Nat.le_floor (hshiftNat ij hij).2.2⟩⟩
  let Bound := (4*(Bmul:ℝ))^2*
    (1+K*(V*(η+μhi^((1:ℝ)/7))+Real.sqrt V*μlo^(-(1:ℝ)/6)))
  have hBound : 0 ≤ Bound := by dsimp only [Bound]; positivity
  have hfiber (v : ℕ × ℕ) (hv : v∈J) :
      ((Rp.filter (fun ij => index ij=v)).card:ℝ) ≤ Bound := by
    let E := Rp.filter (fun ij => index ij=v)
    let Sq := S.filter (fun i => q i=v.1)
    have hvmem := Finset.mem_product.mp hv
    have hvq := Finset.mem_Icc.mp hvmem.1
    have hvk := Finset.mem_Icc.mp hvmem.2
    have hvr : 0 < (v.1:ℝ) := by exact_mod_cast hvq.1
    have hkr : 0 < (v.2:ℝ) := by exact_mod_cast hvk.1
    have hkr1 : (1:ℝ) ≤ v.2 := by exact_mod_cast hvk.1
    have hvqR : (v.1:ℝ) ≤ Q := by exact_mod_cast hvq.2
    have hvkR : (v.2:ℝ) ≤ Lshift := (Nat.cast_le.mpr hvk.2).trans (Nat.floor_le hL.le)
    have hEmem ij (hij : ij∈E) : ij∈Rp ∧ q ij.1=v.1 ∧ shift ij=v.2 := by
      obtain ⟨hh,he⟩ := Finset.mem_filter.mp hij
      exact ⟨hh,congrArg Prod.fst he,congrArg Prod.snd he⟩
    have hSq i (hi : i∈Sq) : i∈S ∧ q i=v.1 := Finset.mem_filter.mp hi
    have hEq ij (hij : ij∈E) : ij.1∈Sq ∧ ij.2∈Sq := by
      have hp := (hEmem ij hij).1
      have hmemb := hRmem ij (hpmem ij hp).1
      have he := (hshift ij (hpmem ij hp).1).1
      exact ⟨Finset.mem_filter.mpr ⟨hmemb.1,(hEmem ij hij).2.1⟩,
        Finset.mem_filter.mpr ⟨hmemb.2,he.symm.trans (hEmem ij hij).2.1⟩⟩
    by_cases hE : E.Nonempty
    · obtain ⟨ij,hij⟩ := hE
      have hqlo : (Q:ℝ) ≤ 2*(v.1:ℝ) := by
        have hh := (hq ij.1 (hSq _ (hEq ij hij).1).1).2.2
        rw [(hEmem ij hij).2.1] at hh
        exact_mod_cast hh
      have hcounts := hcount Sq E F z center block label inverse parity H Bmul M v.1 Q s T P v.2
        hH hT hP hvq.1 hvq.2 hkr hF₀
        (fun i hi => hz i (hSq i hi).1) (fun i hi => hcenter i (hSq i hi).1)
        (fun i hi => hround i (hSq i hi).1) (fun i hi => hspan i (hSq i hi).1)
        (fun j => (Finset.card_le_card (by
          intro i hi
          obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨(hSq i hi).1,he⟩)).trans (hmul j))
        (fun i hi => by rw [←(hSq i hi).2]; exact hinverse i (hSq i hi).1)
        (fun ij hij => Finset.mem_product.mpr (hEq ij hij))
        (fun i hi => by rw [←(hSq i hi).2]; exact hlevel i (hSq i hi).1)
        (fun ij hij => by
          have hh := (hshiftNat ij (hEmem ij hij).1).2.1
          rw [(hEmem ij hij).2.2] at hh
          exact hh)
        (fun ij hij j => by
          have hh := hRnear ij (hpmem ij (hEmem ij hij).1).1 j
          dsimp only [Y,b,tau,coeff] at hh ⊢
          rw [(hSq _ (hEq ij hij).1).2,(hSq _ (hEq ij hij).2).2] at hh
          exact hh)
      let μ := m*(v.2:ℝ)*P^7/((v.1:ℝ)^2*T^3)
      have hμ : 0 < μ := by dsimp only [μ]; positivity
      have hμlower : μlo ≤ μ := by
        dsimp only [μlo,μ]
        calc
          _ ≤ m*(v.2:ℝ)*P^7/((Q:ℝ)^2*T^3) := by
            gcongr
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hkr1 hm.le
          _ ≤ _ := by gcongr
      have hμupper : μ ≤ μhi := by
        have hq2 : (Q:ℝ)^2 ≤ 4*(v.1:ℝ)^2 := by nlinarith only [sq_nonneg ((Q:ℝ)-2*v.1),hqlo,hQr,hvr]
        dsimp only [μ,μhi]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have hh := mul_le_mul hvkR hq2 (sq_nonneg (Q:ℝ)) hL.le
        nlinarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ m*P^7*T^3 by positivity)]
      have hVsmall : 3*(v.1:ℝ)*(u₀*T/P^3)*P ≤ V := by dsimp only [V]; gcongr
      have hηsmall : 2*((Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
          Real.sqrt ((u₀*T/P^3)*(Q:ℝ)^3))+9*(v.1:ℝ)*(u₀*T/P^3)/4 ≤ η := by
        dsimp only [η,D]
        gcongr
      apply hcounts.trans
      change _ ≤ Bound
      dsimp only [Bound]
      have hnegpow : μ^(-(1:ℝ)/6) ≤ μlo^(-(1:ℝ)/6) :=
        Real.rpow_le_rpow_of_nonpos hμlo hμlower (by norm_num)
      gcongr
    · have he : E=∅ := Finset.not_nonempty_iff_eq_empty.mp hE
      change (E.card:ℝ) ≤ Bound
      rw [he,Finset.card_empty,Nat.cast_zero]
      exact hBound
  have hJcard : (J.card:ℝ) ≤ (Q:ℝ)*Lshift := by
    have he : J.card=Q*⌊Lshift⌋₊ := by simp only [J,Finset.card_product,Nat.card_Icc,Nat.add_sub_cancel]
    rw [he,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hL.le) hQr.le
  have hRp : (Rp.card:ℝ) ≤ (Q:ℝ)*Lshift*Bound := by
    have he : (Rp.card:ℝ)=∑ v∈J,((Rp.filter (fun ij => index ij=v)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hindex
    rw [he]
    calc
      _ ≤ ∑ _v∈J,Bound := Finset.sum_le_sum hfiber
      _ = (J.card:ℝ)*Bound := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hJcard hBound
  have hsplitR : (R.card:ℝ) ≤ (Z.card:ℝ)+2*Rp.card := by exact_mod_cast hsplit
  have hh := hsplitR.trans (add_le_add hZ (mul_le_mul_of_nonneg_left hRp (by norm_num)))
  exact hh.trans_eq (by dsimp only [Bound]; ring)

#print axioms physical_model_four_coordinate_band_count

-- These exact affine budgets are not a substitute for the linked physical bounds.
private theorem refined_frozen_exponent_budget {α q : ℝ}
    (hlo : (7:ℝ)/17 ≤ α) (hhi : α ≤ 3/7) (hq : q ≤ (3*α-1)/4) :
    let n := (3*α-1)/2
    let k := (3-7*α)/2
    let z := 1-2*α+2*q
    let v := q+1-2*α
    let elo := 7*α-2*q-3
    let ehi := k+elo
    let pref := 6*n+6*q+10*z+13*(n-2*q)
    let target := 13/84+α/2
    pref+z ≤ 12*target ∧
    pref+q+k ≤ 12*target ∧
    pref+q+k+v+(q-n) ≤ 12*target ∧
    pref+q+k+v+ehi/7 ≤ 12*target ∧
    pref+q+k+v/2-elo/6 ≤ 12*target ∧
    z+n/2 ≤ target := by
  dsimp only
  constructor
  · linarith only [hlo,hhi,hq]
  constructor
  · linarith only [hlo,hhi,hq]
  constructor
  · linarith only [hlo,hhi,hq]
  constructor
  · linarith only [hlo,hhi,hq]
  constructor
  · linarith only [hlo,hhi,hq]
  · linarith only [hlo,hhi,hq]

private theorem refined_minor_exponent_budget {α q : ℝ}
    (hlo : (7:ℝ)/17 ≤ α) (hhi : α ≤ 3/7) (hq : (3*α-1)/4 ≤ q) :
    let n := (3*α-1)/2
    let k := (3-7*α)/2
    let y := α-2*q
    let v := q+1-2*α
    let elo := 7*α-2*q-3
    let ehi := k+elo
    let pref := 6*n+6*q+10*y
    let target := 13/84+α/2
    pref+y ≤ 12*target ∧
    pref+q+k ≤ 12*target ∧
    pref+q+k+v+(q-n) ≤ 12*target ∧
    pref+q+k+v+ehi/7 ≤ 12*target ∧
    pref+q+k+v/2-elo/6 ≤ 12*target ∧
    y+n/2 ≤ target := by
  dsimp only
  constructor
  · linarith only [hlo,hhi,hq]
  constructor
  · linarith only [hlo,hhi,hq]
  constructor
  · linarith only [hlo,hhi,hq]
  constructor
  · linarith only [hlo,hhi,hq]
  constructor
  · linarith only [hlo,hhi,hq]
  · linarith only [hlo,hhi,hq]

#print axioms refined_frozen_exponent_budget
#print axioms refined_minor_exponent_budget

private theorem actual_source_triangular_derivative_resonance
    (M q q' Q : ℕ) [NeZero M] (a a' r r' : ℤ)
    (hq : 0 < q) (hq' : 0 < q') (hqQ : q ≤ Q) (hqQ' : q' ≤ Q)
    (hthin : (Q:ℝ)^2 < 6*(M:ℝ)^2)
    (har : (q:ℤ) ∣ a*r-1) (har' : (q':ℤ) ∣ a'*r'-1)
    {μ μ' U ℓ ℓ' : ℝ} (hμ : 0 < μ) (hμ' : 0 < μ') (hμU : μ ≤ U)
    (p p' : Fin 2) :
    let b : ℤ := ⌊(q:ℝ)*ℓ⌋+(p:ℕ)
    let b' : ℤ := ⌊(q':ℝ)*ℓ'⌋+(p':ℕ)
    let τ := ((b:ℝ)-(q:ℝ)*ℓ)/2
    let τ' := ((b':ℝ)-(q':ℝ)*ℓ')/2
    let K := -2*μ*(Real.sqrt (2/(3*μ*(q:ℝ))))^3
    let K' := -2*μ'*(Real.sqrt (2/(3*μ'*(q':ℝ))))^3
    let Y : Fin 4 → ℝ := ![Int.fract (-(r:ℝ)*b/q),Int.fract (-(r:ℝ)/q),
      K/Real.sqrt M,(3*K*τ/2)/Real.sqrt M]
    let Y' : Fin 4 → ℝ := ![Int.fract (-(r':ℝ)*b'/q'),Int.fract (-(r':ℝ)/q'),
      K'/Real.sqrt M,(3*K'*τ'/2)/Real.sqrt M]
    let window : Fin 4 → ℝ :=
      ![1/(12*(M:ℝ)),1/(12*(M:ℝ)^2),(1/(M:ℝ)^2)/12,(1/(M:ℝ))/12]
    let D := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
      Real.sqrt (U*(Q:ℝ)^3)
    (∀ j, |Y j-Y' j| ≤ 2*window j) →
    q=q' ∧ ∃ k e : ℤ, a'=a+k*(q:ℤ) ∧ |ℓ'-ℓ-(e:ℝ)| ≤ 2*D/q := by
  intro b b' τ τ' K K' Y Y' window D hnear
  obtain ⟨α,β,γ,d,e₁,e₂,hdet,ha,hden,hγ,hfirst,hsecond⟩ :=
    actual_source_affine_lattice_strip M q q' Q a a' r r' 0 0 hq hq' hqQ
      har har' hμ hμ' hμU p p' hnear
  have hMr : 0 < (M:ℝ) := by exact_mod_cast NeZero.pos M
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hq'r : 0 < (q':ℝ) := by exact_mod_cast hq'
  have hqQr : (q:ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqQ'r : (q':ℝ) ≤ Q := by exact_mod_cast hqQ'
  have hsmall : (q:ℝ)*q'/(6*(M:ℝ)^2) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    have hh : (q:ℝ)*q' ≤ (Q:ℝ)^2 := by
      rw [pow_two]
      exact mul_le_mul hqQr hqQ'r hq'r.le (hqr.trans_le hqQr).le
    exact hh.trans_lt hthin
  have hg : γ=0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hγ.trans_lt hsmall)
  rw [hg,mul_zero,sub_zero] at hdet
  rw [hg,zero_mul,zero_add] at hden
  have hqi : (0:ℤ) < q := by exact_mod_cast hq
  have hq'i : (0:ℤ) < q' := by exact_mod_cast hq'
  have hdpos : 0 < d := by nlinarith only [hden,hqi,hq'i]
  have hapos : 0 < α := by nlinarith only [hdet,hdpos]
  have hd1 : d=1 := by nlinarith only [hdet,hdpos,hapos]
  have ha1 : α=1 := by nlinarith only [hdet,hd1]
  have heq : q=q' := by
    rw [hd1,one_mul] at hden
    exact_mod_cast hden
  have hQthin : (Q:ℝ) < 6*(M:ℝ) := by
    by_contra hnot
    have hh : 6*(M:ℝ) ≤ Q := le_of_not_gt hnot
    have hs := sq_nonneg ((Q:ℝ)-6*(M:ℝ))
    nlinarith only [hthin,hh,hs,sq_pos_of_pos hMr]
  have hqthin : (q':ℝ)/(6*(M:ℝ)) < 1 :=
    (div_lt_one (by positivity)).mpr (hqQ'r.trans_lt hQthin)
  have he₁ : e₁=0 := by
    simp only [hg,Int.cast_zero,mul_zero,zero_mul,sub_self,zero_sub,abs_neg,abs_zero,zero_div,add_zero] at hfirst
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast hfirst.trans_lt hqthin)
  refine ⟨heq,β,e₂,?_,?_⟩
  · rw [ha1,one_mul] at ha
    exact ha.symm
  · simp only [hg,ha1,he₁,Int.cast_zero,Int.cast_one,mul_zero,zero_mul,one_mul,
      sub_zero,sub_self] at hsecond
    rw [←heq] at hsecond
    exact hsecond

#print axioms actual_source_triangular_derivative_resonance

-- Displacement, rather than the rational curvature label, is the integer
-- variable in the second route.  These are the actual source curve and jets.
private theorem triangular_resonance_parametric_jets
    (f : ℝ → ℝ) {A B L k v : ℝ} (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 5 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let J := fun t => iteratedDeriv 4 f (c t)/(iteratedDeriv 3 f (c t))^3
    let D := fun t => c (t+k)-c t
    let D₁ := fun t => 2*(1/iteratedDeriv 3 f (c (t+k))-1/iteratedDeriv 3 f (c t))
    let D₂ := fun t => -4*(J (t+k)-J t)
    let E := fun t => deriv f (c (t+k))-deriv f (c t)-2*k*c t
    v∈h '' Ioo A B → v+k∈h '' Ioo A B →
    HasDerivAt D (D₁ v) v ∧ HasDerivAt D₁ (D₂ v) v ∧
      HasDerivAt E (2*(v+k)*D₁ v) v := by
  intro h c J D D₁ D₂ E hv hvk
  have hp := inverse_curvature_derivative f hL
    (fun x hx => (hf x hx).of_le (by norm_num)) hthree
  have hc := hp.2 v hv
  have hc' := hp.2 (v+k) hvk
  have hs : HasDerivAt (fun t : ℝ => t+k) 1 v := (hasDerivAt_id v).add_const k
  constructor
  · convert (hc'.2.2.1.comp v hs).sub hc.2.2.1 using 1
    dsimp only [D₁]
    ring
  constructor
  · have hx := (inverse_curvature_ratio_derivatives f hL hf hthree hv).1
    have hy := (inverse_curvature_ratio_derivatives f hL hf hthree hvk).1
    convert ((hy.comp v hs).sub hx).const_mul 2 using 1
    dsimp only [D₂,J]
    ring
  · have hx := hc.2.2.2.const_mul 2
    have hy := (hc'.2.2.2.comp v hs).const_mul 2
    have he := (hy.sub hx).sub (hc.2.2.1.const_mul (2*k))
    convert he using 1
    · funext t
      change deriv f (c (t+k))-deriv f (c t)-2*k*c t =
        (2*(deriv f (c (t+k))/2)-2*(deriv f (c t)/2))-2*k*c t
      ring
    · dsimp only [D₁]
      ring

#print axioms triangular_resonance_parametric_jets

private theorem monotone_parametric_curve_inverse_jets
    (D D₁ D₂ E : ℝ → ℝ) {a b k : ℝ}
    (hD : ∀ t∈Ioo a b, HasDerivAt D (D₁ t) t)
    (hD₁ : ∀ t∈Ioo a b, HasDerivAt D₁ (D₂ t) t)
    (hE : ∀ t∈Ioo a b, HasDerivAt E (2*(t+k)*D₁ t) t)
    (hpos : ∀ t∈Ioo a b, 0 < D₁ t) :
    let c := Function.invFunOn D (Ioo a b)
    let G := fun z => E (c z)
    let G₁ := fun z => 2*(c z+k)
    let G₂ := fun z => 2/D₁ (c z)
    (∀ t∈Ioo a b, c (D t)=t) ∧
    ∀ z∈D '' Ioo a b, D (c z)=z ∧ c z∈Ioo a b ∧
      HasDerivAt G (G₁ z) z ∧ HasDerivAt G₁ (G₂ z) z ∧
      HasDerivAt G₂ (-2*D₂ (c z)/(D₁ (c z))^3) z := by
  intro c G G₁ G₂
  have hmono : StrictMonoOn D (Ioo a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo a b)
    · exact fun t ht => (hD t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t∈Ioo a b := by simpa only [interior_Ioo] using ht
      rw [(hD t ht').deriv]
      exact hpos t ht'
  have hleft t (ht : t∈Ioo a b) : c (D t)=t := hmono.injOn.leftInvOn_invFunOn ht
  refine ⟨hleft,?_⟩
  intro z hz
  have hcI : c z∈Ioo a b := Function.invFunOn_mem hz
  have heq : D (c z)=z := Function.invFunOn_eq hz
  have hn : D₁ (c z) ≠ 0 := (hpos _ hcI).ne'
  have hc : HasDerivAt c (D₁ (c z))⁻¹ z := by
    have hstrict : HasStrictDerivAt D (D₁ (c z)) (c z) :=
      hasStrictDerivAt_of_hasDerivAt_of_continuousAt
        (by filter_upwards [isOpen_Ioo.mem_nhds hcI] with t ht; exact hD t ht)
        (hD₁ _ hcI).continuousAt
    have hi : HasStrictDerivAt c (D₁ (c z))⁻¹ (D (c z)) := by
      apply hstrict.to_local_left_inverse hn
      filter_upwards [isOpen_Ioo.mem_nhds hcI] with t ht
      exact hleft t ht
    rw [heq] at hi
    exact hi.hasDerivAt
  refine ⟨heq,hcI,?_,?_,?_⟩
  · convert (hE _ hcI).comp z hc using 1
    dsimp only [G₁]
    field_simp
  · convert (hc.add_const k).const_mul 2 using 1
  · have hh := (hasDerivAt_const z (2:ℝ)).div ((hD₁ _ hcI).comp z hc) hn
    convert hh using 1
    dsimp only [Function.comp_apply]
    field_simp
    ring

#print axioms monotone_parametric_curve_inverse_jets

private theorem displacement_curve_exponent_budget
    {α q : ℝ} (hlo : 17/42 ≤ α) (hhi : α ≤ 3/7) :
    let n := (3*α-1)/2
    let target := 13/84+α/2
    let r := max ((1-α)/2)
      (max (2-25*α/6) (max (13/6-9*α/2) (max (5/3-11*α/3) ((3-7*α)/2))))
    (q ≤ n/2 →
      6*n+6*q+10*(1-2*α+2*q)+13*(n-2*q)+r ≤ 12*target) ∧
    (n/2 ≤ q → 6*n+6*q+10*(α-2*q)+r ≤ 12*target) := by
  intro n target r
  have hr : r ≤ 12*target-(17*α+1)/2 := by
    dsimp only [r,target]
    simp only [max_le_iff]
    constructor
    · linarith only [hlo,hhi]
    constructor
    · linarith only [hlo,hhi]
    constructor
    · linarith only [hlo,hhi]
    constructor <;> linarith only [hlo,hhi]
  constructor
  · intro _
    dsimp only [n]
    linarith only [hr]
  · intro hq
    dsimp only [n] at hq ⊢
    linarith only [hr,hq]

#print axioms displacement_curve_exponent_budget

private theorem short_second_derivative_remainder
    (G G₁ G₂ : ℝ → ℝ) {a b C : ℝ}
    (hG : ∀ z∈uIcc a b, HasDerivAt G (G₁ z) z)
    (hG₁ : ∀ z∈uIcc a b, HasDerivAt G₁ (G₂ z) z)
    (hC : ∀ z∈uIcc a b, |G₂ z| ≤ C) (hab : |b-a| ≤ 1) :
    |G b-G a-G₁ a*(b-a)| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC a left_mem_uIcc)
  have hfirst z (hz : z∈uIcc a b) : |G₁ z-G₁ a| ≤ C := by
    have hh := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hG₁ t ht).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hC t ht)
      left_mem_uIcc hz
    simp only [Real.norm_eq_abs] at hh
    exact hh.trans (by
      have hd := (abs_sub_left_of_mem_uIcc hz).trans hab
      nlinarith only [hd,hC0])
  let R := fun z => G z-G a-G₁ a*(z-a)
  have hR z (hz : z∈uIcc a b) : HasDerivAt R (G₁ z-G₁ a) z := by
    convert ((hG z hz).sub_const (G a)).sub
      (((hasDerivAt_id z).sub_const a).const_mul (G₁ a)) using 1
    ring
  have hh := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hR z hz).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hfirst z hz)
    left_mem_uIcc right_mem_uIcc
  have hRa : R a=0 := by dsimp only [R]; ring
  rw [hRa,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs] at hh
  exact hh.trans (by nlinarith only [hab,hC0])

#print axioms short_second_derivative_remainder

private theorem rounded_triangular_curve_near_integer
    (f G G₁ G₂ : ℝ → ℝ) {x y U v C ε : ℝ} (m n k e : ℤ)
    (hf : ∀ z∈uIcc x (m:ℝ) ∪ uIcc y (n:ℝ), ContDiffAt ℝ 3 f z)
    (hb : ∀ z∈uIcc x (m:ℝ) ∪ uIcc y (n:ℝ), |iteratedDeriv 3 f z| ≤ 6*U)
    (hm : |(m:ℝ)-x| ≤ 1/2) (hn : |(n:ℝ)-y| ≤ 1/2)
    (hx : iteratedDeriv 2 f x=2*v)
    (hy : iteratedDeriv 2 f y=2*(v+k))
    (hnear : |iteratedDeriv 1 f n-iteratedDeriv 1 f m-(e:ℝ)| ≤ ε)
    (hvalue : G (y-x)=iteratedDeriv 1 f y-iteratedDeriv 1 f x-2*(k:ℝ)*x)
    (hslope : G₁ (y-x)=2*(v+k))
    (hG : ∀ z∈uIcc (y-x) ((n:ℝ)-m), HasDerivAt G (G₁ z) z)
    (hG₁ : ∀ z∈uIcc (y-x) ((n:ℝ)-m), HasDerivAt G₁ (G₂ z) z)
    (hC : ∀ z∈uIcc (y-x) ((n:ℝ)-m), |G₂ z| ≤ C) :
    |G ((n:ℝ)-m)-((e-2*k*m:ℤ):ℝ)| ≤ ε+9*U/4+C := by
  have hround := (rounded_displacement_strip f hf hb hm hn hx hy
    (a:=1) (b:=(k:ℝ)) (c:=0) (d:=1) (t:=1)
    (by norm_num) (by ring) (by ring) (by norm_num) (by norm_num)).2
  have hdist : |((n:ℝ)-m)-(y-x)| ≤ 1 := by
    calc
      _ = |((n:ℝ)-y)-((m:ℝ)-x)| := by congr 1; ring
      _ ≤ |(n:ℝ)-y|+|(m:ℝ)-x| := abs_sub _ _
      _ ≤ 1 := by linarith only [hm,hn]
  have ht := short_second_derivative_remainder G G₁ G₂ hG hG₁ hC hdist
  rw [hvalue,hslope] at ht
  let F := iteratedDeriv 1 f n-iteratedDeriv 1 f m-2*(k:ℝ)*m
  let E := iteratedDeriv 1 f y-iteratedDeriv 1 f x-2*(k:ℝ)*x
  let V := 2*(v+k)*(((n:ℝ)-m)-(y-x))
  have hr : |F-E-V| ≤ 9*U/4 := by
    convert hround using 1
    congr 1
    dsimp only [F,E,V]
    ring
  have ht' : |G ((n:ℝ)-m)-E-V| ≤ C := ht
  have hi : |F-((e-2*k*m:ℤ):ℝ)| ≤ ε := by
    convert hnear using 1
    congr 1
    dsimp only [F]
    push_cast
    ring
  calc
    _ = |(G ((n:ℝ)-m)-E-V)-(F-E-V)+(F-((e-2*k*m:ℤ):ℝ))| := by congr 1; ring
    _ ≤ |G ((n:ℝ)-m)-E-V|+|F-E-V|+|F-((e-2*k*m:ℤ):ℝ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ ε+9*U/4+C := by linarith only [ht',hr,hi]

#print axioms rounded_triangular_curve_near_integer

private theorem hat_fourier_half_moment
    {B : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2) :
    let c := GafniTao.heathBrownHatFourierCoefficient B
    Summable (fun r : ℤ => c r*|(r:ℝ)|^((1:ℝ)/2)) ∧
    (∑' r : ℤ, c r*|(r:ℝ)|^((1:ℝ)/2)) ≤ 6*B^(-(1:ℝ)/2) := by
  intro c
  let R : ℕ := ⌈1/B⌉₊
  have hRlo : 1/B ≤ (R:ℝ) := Nat.le_ceil _
  have hR : 0 < R := by
    have hh : (0:ℝ) < R := (one_div_pos.mpr hB).trans_le hRlo
    exact_mod_cast hh
  have hRhi : (R:ℝ) ≤ 2/B := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 1/B by positivity)
    change (R:ℝ) < 1/B+1 at hh
    have hB1 : B ≤ 1 := by linarith only [hBHalf]
    have h1 : 1 ≤ 1/B := (le_div_iff₀ hB).mpr (by simpa only [one_mul] using hB1)
    calc
      _ ≤ 1/B+1/B := hh.le.trans (add_le_add le_rfl h1)
      _ = _ := by ring
  have hm := hat_fourier_positive_moment hB hBHalf (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 < 1) hR
  have hhead : (R:ℝ)^((1:ℝ)/2) ≤ 2*B^(-(1:ℝ)/2) := by
    calc
      _ ≤ (2/B)^((1:ℝ)/2) := Real.rpow_le_rpow (Nat.cast_nonneg R) hRhi (by norm_num)
      _ = (2:ℝ)^((1:ℝ)/2)*B^(-(1:ℝ)/2) := by
        rw [show -(1:ℝ)/2 = -((1:ℝ)/2) by ring,
          Real.div_rpow (by norm_num) hB.le,Real.rpow_neg hB.le]
        ring
      _ ≤ _ := by
        have hh : (2:ℝ)^((1:ℝ)/2) ≤ 2 := by
          simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (1:ℝ)/2 ≤ 1))
        exact mul_le_mul_of_nonneg_right hh (by positivity)
  have htailpow : (R:ℝ)^((1:ℝ)/2-1) ≤ B^((1:ℝ)/2) := by
    calc
      _ ≤ (1/B)^((1:ℝ)/2-1) := Real.rpow_le_rpow_of_nonpos
        (one_div_pos.mpr hB) hRlo (by norm_num)
      _ = _ := by
        rw [one_div,Real.inv_rpow hB.le,←Real.rpow_neg hB.le]
        norm_num
  have htail : (2/B)*(R:ℝ)^((1:ℝ)/2-1)/(1-(1:ℝ)/2) ≤
      (4:ℝ)*B^(-(1:ℝ)/2) := by
    calc
      _ ≤ (2/B)*B^((1:ℝ)/2)/(1-(1:ℝ)/2) := by gcongr
      _ = _ := by
        have he : B^((1:ℝ)/2)/B=B^(-(1:ℝ)/2) := by
          rw [←Real.rpow_sub_one hB.ne']
          norm_num
        calc
          _ = (4:ℝ)*(B^((1:ℝ)/2)/B) := by ring
          _ = _ := by rw [he]
  refine ⟨hm.1,?_⟩
  have hb := hm.2.trans (add_le_add hhead htail)
  have hpos : 0 ≤ B^(-(1:ℝ)/2) := by positivity
  linarith only [hb,hpos]

#print axioms hat_fourier_half_moment

private theorem finite_near_integer_count_half
    {ι : Type*} [DecidableEq ι] (S T : Finset ι) (φ : ι → ℝ)
    {B A D : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hTS : T ⊆ S)
    (hnear : ∀ i∈T, ∃ e : ℤ, |φ i-(e:ℝ)| ≤ B/2)
    (hfreq : ∀ r : ℤ, r ≠ 0 →
      ‖∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)‖ ≤ A*|(r:ℝ)|^((1:ℝ)/2)+D) :
    (T.card:ℝ) ≤ 2*B*S.card+12*A*B^(-(1:ℝ)/2)+2*D := by
  let c := GafniTao.heathBrownHatFourierCoefficient B
  let Z := fun r : ℤ => ∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)
  let e := fun r : ℤ => if r=0 then B*(S.card:ℝ) else 0
  have hc r : 0 ≤ c r := GafniTao.heathBrownHatFourierCoefficient_nonneg hB.le r
  have hm := hat_fourier_half_moment hB hBHalf
  have hmass := (hat_fourier_mass_and_decay hB hBHalf).1
  have he : HasSum e (B*(S.card:ℝ)) := hasSum_ite_eq _ _
  have hmajor : Summable (fun r : ℤ => e r+A*(c r*|(r:ℝ)|^((1:ℝ)/2))+D*c r) :=
    (he.summable.add (hm.1.mul_left A)).add (hmass.summable.mul_left D)
  have hpoint r : c r*‖Z r‖ ≤ e r+A*(c r*|(r:ℝ)|^((1:ℝ)/2))+D*c r := by
    by_cases hr : r=0
    · subst r
      have hZ : Z 0=(S.card:ℂ) := by simp [Z,GafniTao.fordAdditiveCharacter]
      rw [hZ]
      simp only [c,GafniTao.heathBrownHatFourierCoefficient_zero,
        Complex.norm_natCast,Int.cast_zero,abs_zero,
        Real.zero_rpow (by norm_num : (1:ℝ)/2 ≠ 0),mul_zero,add_zero,e,if_pos rfl]
      exact le_add_of_nonneg_right (mul_nonneg hD hB.le)
    · have hh := mul_le_mul_of_nonneg_left (hfreq r hr) (hc r)
      change c r*‖Z r‖ ≤ _ at hh
      change c r*‖Z r‖ ≤ (if r=0 then B*(S.card:ℝ) else 0)+
        A*(c r*|(r:ℝ)|^((1:ℝ)/2))+D*c r
      rw [if_neg hr,zero_add]
      convert hh using 1
      ring
  have hs : Summable (fun r : ℤ => c r*‖Z r‖) :=
    hmajor.of_nonneg_of_le (fun r => mul_nonneg (hc r) (norm_nonneg _)) hpoint
  have hupper : (∑' r : ℤ, c r*‖Z r‖) ≤ B*S.card+6*A*B^(-(1:ℝ)/2)+D := by
    calc
      _ ≤ ∑' r : ℤ, (e r+A*(c r*|(r:ℝ)|^((1:ℝ)/2))+D*c r) :=
        Summable.tsum_le_tsum hpoint hs hmajor
      _ = B*S.card+A*(∑' r : ℤ, c r*|(r:ℝ)|^((1:ℝ)/2))+D := by
        rw [Summable.tsum_add (he.summable.add (hm.1.mul_left A)) (hmass.summable.mul_left D),
          Summable.tsum_add he.summable (hm.1.mul_left A),tsum_mul_left,tsum_mul_left,
          he.tsum_eq,hmass.tsum_eq,mul_one]
      _ ≤ B*S.card+A*(6*B^(-(1:ℝ)/2))+D :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm.2 hA)) le_rfl
      _ = _ := by ring
  have hcount := finite_near_integer_count_fourier S T φ hB hBHalf hTS hnear
  change (T.card:ℝ) ≤ 2*∑' r : ℤ, c r*‖Z r‖ at hcount
  linarith only [hcount,hupper]

#print axioms finite_near_integer_count_half

private theorem positive_second_derivative_near_integer_count
    (G G₁ G₂ : ℝ → ℝ) (a : ℝ) (N : ℕ) (I : Finset ℕ)
    {C μ W : ℝ} (hC : 1 ≤ C) (hμ : 0 < μ) (hW : 0 < W) (hWhalf : W ≤ 1/2)
    (hG : ∀ z∈Icc a (a+N), HasDerivAt G (G₁ z) z)
    (hG₁ : ∀ z∈Icc a (a+N), HasDerivAt G₁ (G₂ z) z)
    (hlo : ∀ z∈Icc a (a+N), μ ≤ G₂ z)
    (hhi : ∀ z∈Icc a (a+N), G₂ z ≤ C*μ)
    (hI : I ⊆ Finset.range N)
    (hnear : ∀ n∈I, ∃ e : ℤ, |G (a+n)-(e:ℝ)| ≤ W/2) :
    (I.card:ℝ) ≤ 2*W*N+144*C*N*μ^((1:ℝ)/2)*W^(-(1:ℝ)/2)+48*μ^(-(1:ℝ)/2) := by
  let E := 12*C*(N:ℝ)*μ^((1:ℝ)/2)
  let D := 24*μ^(-(1:ℝ)/2)
  have hfreq r (hr : r ≠ (0:ℤ)) :
      ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter ((r:ℝ)*G (a+n))‖ ≤
        E*|(r:ℝ)|^((1:ℝ)/2)+D := by
    have hrabs : 0 < |(r:ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hr)
    have hrone : 1 ≤ |(r:ℝ)| := by exact_mod_cast Int.one_le_abs hr
    have hb₀ := second_derivative_all_positive_frequencies
      (fun z => -G z) (fun z => -G₁ z) (fun z => -G₂ z) a N hC hμ hrabs
      (fun z hz => (hG z hz).neg) (fun z hz => (hG₁ z hz).neg)
      (fun z hz => neg_le_neg (hhi z hz)) (fun z hz => neg_le_neg (hlo z hz))
    have hb : ‖∑ n∈Finset.range N,
        GafniTao.fordAdditiveCharacter (|(r:ℝ)| * G (a+n))‖ ≤
        12*(C*N*Real.sqrt (|(r:ℝ)| *μ)+2/Real.sqrt (|(r:ℝ)| *μ)) := by
      rw [←norm_sum_fordAdditiveCharacter_neg_phase (fun z => |(r:ℝ)| * G z) a N]
      simpa only [mul_neg] using hb₀
    have hsign :
        ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter ((r:ℝ)*G (a+n))‖ =
        ‖∑ n∈Finset.range N, GafniTao.fordAdditiveCharacter (|(r:ℝ)| * G (a+n))‖ := by
      by_cases hnon : 0 ≤ (r:ℝ)
      · rw [abs_of_nonneg hnon]
      · rw [abs_of_neg (lt_of_not_ge hnon)]
        simp only [neg_mul]
        exact (norm_sum_fordAdditiveCharacter_neg_phase (fun z => (r:ℝ)*G z) a N).symm
    have hroot : Real.sqrt μ ≤ Real.sqrt (|(r:ℝ)| *μ) :=
      Real.sqrt_le_sqrt (by nlinarith only [mul_le_mul_of_nonneg_right hrone hμ.le])
    have htail : 2/Real.sqrt (|(r:ℝ)| *μ) ≤ 2/Real.sqrt μ :=
      div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hμ) hroot
    rw [hsign]
    apply hb.trans
    calc
      _ ≤ 12*(C*N*Real.sqrt (|(r:ℝ)| *μ)+2/Real.sqrt μ) := by linarith only [htail]
      _ = _ := by
        rw [Real.sqrt_mul hrabs.le,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow]
        dsimp only [E,D]
        rw [show -(1:ℝ)/2= -((1:ℝ)/2) by ring,Real.rpow_neg hμ.le]
        ring
  have hh := finite_near_integer_count_half (Finset.range N) I (fun n => G (a+n))
    hW hWhalf (by
      dsimp only [E]
      have hCp : 0 < C := by linarith only [hC]
      positivity)
    (by dsimp only [D]; positivity) hI hnear hfreq
  simp only [Finset.card_range,E,D] at hh
  convert hh using 1
  ring

#print axioms positive_second_derivative_near_integer_count

private theorem triangular_displacement_derivative_bounds
    (f : ℝ → ℝ) {A B L U F lam k v : ℝ}
    (hL : 0 < L) (hlam : 0 < lam) (hk : 0 < k)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 4 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hfour : ∀ x∈Ioo A B, -F ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ -lam) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let D₁ := fun t => 2*(1/iteratedDeriv 3 f (c (t+k))-1/iteratedDeriv 3 f (c t))
    v∈h '' Ioo A B → v+k∈h '' Ioo A B →
      lam*k/(54*U^3) ≤ D₁ v ∧ D₁ v ≤ 4*F*k/L^3 := by
  intro h c D₁ hv hvk
  have hp := inverse_curvature_derivative f hL hf (fun x hx => (hthree x hx).1)
  have hx := hp.2 v hv
  have hy := hp.2 (v+k) hvk
  change h (c v)=v ∧ _ at hx
  change h (c (v+k))=v+k ∧ _ at hy
  have hd x (hx' : x∈Ioo A B) : HasDerivAt h (iteratedDeriv 3 f x/2) x := by
    have hh := (contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf x hx')).differentiableAt (by norm_num)
    simpa only [h,iteratedDeriv_succ] using hh.hasDerivAt.div_const 2
  have hmono : StrictMonoOn h (Ioo A B) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo A B)
    · exact fun x hx' => (hd x hx').continuousAt.continuousWithinAt
    · intro x hx'
      have hx'' : x∈Ioo A B := by simpa only [interior_Ioo] using hx'
      rw [(hd x hx'').deriv]
      exact div_pos (hL.trans_le (hthree x hx'').1) (by norm_num)
  have hxy : c v < c (v+k) := by
    by_contra hnot
    have hh := hmono.monotoneOn hy.2.1 hx.2.1 (le_of_not_gt hnot)
    rw [hx.1,hy.1] at hh
    linarith only [hh,hk]
  have hlevel : iteratedDeriv 2 f (c (v+k))/2-iteratedDeriv 2 f (c v)/2=k := by
    change h (c (v+k))-h (c v)=k
    rw [hx.1,hy.1]
    ring
  have hh := shifted_legendre_negative_curvature_bounds f hL hlam
    (q:=1) (by norm_num) hxy hx.2.1 hy.2.1 hf hthree hfour hlevel
  let X := iteratedDeriv 3 f (c v)
  let Y := iteratedDeriv 3 f (c (v+k))
  have hX : 0 < X := hL.trans_le (hthree _ hx.2.1).1
  have hY : 0 < Y := hL.trans_le (hthree _ hy.2.1).1
  have he : 4*(Y-X)/(1*X*Y)= -2*D₁ v := by
    change 4*(Y-X)/(1*X*Y)= -2*(2*(1/Y-1/X))
    field_simp
    ring
  change -(8*F*k/(1*L^3)) ≤ 4*(Y-X)/(1*X*Y) ∧
    4*(Y-X)/(1*X*Y) ≤ -(lam*k/(27*1*U^3)) at hh
  rw [he] at hh
  rw [show 8*F*k/(1*L^3)=2*(4*F*k/L^3) by ring,
    show lam*k/(27*1*U^3)=2*(lam*k/(54*U^3)) by ring] at hh
  constructor <;> nlinarith only [hh.1,hh.2]

#print axioms triangular_displacement_derivative_bounds

private theorem positive_second_derivative_count_optimized
    (G G₁ G₂ : ℝ → ℝ) (a : ℝ) (N : ℕ) (I : Finset ℕ)
    {C μ η : ℝ} (hC : 1 ≤ C) (hμ : 0 < μ) (hη : 0 ≤ η)
    (hG : ∀ z∈Icc a (a+N), HasDerivAt G (G₁ z) z)
    (hG₁ : ∀ z∈Icc a (a+N), HasDerivAt G₁ (G₂ z) z)
    (hlo : ∀ z∈Icc a (a+N), μ ≤ G₂ z)
    (hhi : ∀ z∈Icc a (a+N), G₂ z ≤ C*μ)
    (hI : I ⊆ Finset.range N)
    (hnear : ∀ n∈I, ∃ e : ℤ, |G (a+n)-(e:ℝ)| ≤ η) :
    (I.card:ℝ) ≤ (52+144*C)*((N:ℝ)*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
  let K := 52+144*C
  let b := μ^((1:ℝ)/3)
  let S := μ^(-(1:ℝ)/2)
  let W := 2*max η b
  have hCp : 0 < C := by linarith only [hC]
  have hb : 0 < b := Real.rpow_pos_of_pos hμ _
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hW : 0 < W := by dsimp only [W]; have hh := hb.trans_le (le_max_right η b); positivity
  have hmax : max η b ≤ η+b := max_le (le_add_of_nonneg_right hb.le) (le_add_of_nonneg_left hη)
  have hKW : 4 ≤ K := by dsimp only [K]; linarith only [hC]
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have htotal : 0 ≤ (N:ℝ)*(η+b)+S := by positivity
  by_cases hsmall : W ≤ 1/2
  · have hne' n (hn : n∈I) : ∃ e : ℤ, |G (a+n)-(e:ℝ)| ≤ W/2 := by
      obtain ⟨e,he⟩ := hnear n hn
      refine ⟨e,he.trans ?_⟩
      dsimp only [W]
      linarith only [le_max_left η b]
    have hh := positive_second_derivative_near_integer_count G G₁ G₂ a N I
      hC hμ hW hsmall hG hG₁ hlo hhi hI hne'
    have hbW : b ≤ W := by
      have hm' := le_max_right η b
      dsimp only [W]
      linarith only [hm',hb]
    have hwgt : μ^((1:ℝ)/2)*W^(-(1:ℝ)/2) ≤ b := by
      calc
        _ ≤ μ^((1:ℝ)/2)*b^(-(1:ℝ)/2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hb hbW (by norm_num)) (by positivity)
        _ = _ := by
          dsimp only [b]
          rw [←Real.rpow_mul hμ.le,←Real.rpow_add hμ]
          norm_num
    have hvol : 2*W*(N:ℝ) ≤ 4*(N:ℝ)*(η+b) := by
      have hh' := mul_le_mul_of_nonneg_right hmax hN
      dsimp only [W]
      nlinarith only [hh']
    have hmid := mul_le_mul_of_nonneg_left hwgt (by positivity : 0 ≤ 144*C*(N:ℝ))
    have hupper : (I.card:ℝ) ≤ 4*(N:ℝ)*(η+b)+144*C*(N:ℝ)*b+48*S := by
      change (I.card:ℝ) ≤ 2*W*N+144*C*N*μ^((1:ℝ)/2)*W^(-(1:ℝ)/2)+48*S at hh
      nlinarith only [hh,hvol,hmid]
    change (I.card:ℝ) ≤ K*((N:ℝ)*(η+b)+S)
    apply hupper.trans
    dsimp only [K]
    nlinarith only [mul_nonneg hCp.le (mul_nonneg hN hη),
      mul_nonneg hCp.le hS,mul_nonneg hN hη,mul_nonneg hN hb.le,hS]
  · have hlarge : 1 ≤ 4*(η+b) := by
      dsimp only [W] at hsmall
      linarith only [hmax,lt_of_not_ge hsmall]
    have hi : (I.card:ℝ) ≤ N := by exact_mod_cast (Finset.card_le_card hI).trans_eq (Finset.card_range N)
    have hh := mul_le_mul_of_nonneg_left hlarge hN
    have hh' := mul_le_mul_of_nonneg_right hKW htotal
    change (I.card:ℝ) ≤ K*((N:ℝ)*(η+b)+S)
    nlinarith only [hi,hh,hh',hS]

#print axioms positive_second_derivative_count_optimized

private theorem positive_second_derivative_integer_set_count
    (G G₁ G₂ : ℝ → ℝ) (J : Finset ℤ) {S : Set ℝ} {C μ η V : ℝ}
    (hC : 1 ≤ C) (hμ : 0 < μ) (hη : 0 ≤ η) (hV : 0 ≤ V)
    (hS : S.OrdConnected)
    (hG : ∀ z∈S, HasDerivAt G (G₁ z) z)
    (hG₁ : ∀ z∈S, HasDerivAt G₁ (G₂ z) z)
    (hμlo : ∀ z∈S, μ ≤ G₂ z) (hμhi : ∀ z∈S, G₂ z ≤ C*μ)
    (hdom : ∀ j∈J, (j:ℝ)∈S)
    (hspan : ∀ i∈J, ∀ j∈J, (i:ℝ)-j ≤ V)
    (hnear : ∀ j∈J, ∃ e : ℤ, |G j-(e:ℝ)| ≤ η) :
    (J.card:ℝ) ≤ 1+(52+144*C)*(V*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
  have hCp : 0 < C := by linarith only [hC]
  by_cases hJ : J.Nonempty
  · let a₀ := J.min' hJ
    let a₁ := J.max' hJ
    let N := (a₁-a₀).toNat
    let I := (J.erase a₁).image (fun a => (a-a₀).toNat)
    have ha₀ : a₀∈J := Finset.min'_mem J hJ
    have ha₁ : a₁∈J := Finset.max'_mem J hJ
    have hlo a (ha : a∈J) : a₀ ≤ a := Finset.min'_le J a ha
    have hhi a (ha : a∈J) : a ≤ a₁ := Finset.le_max' J a ha
    have hNcast : (N:ℤ)=a₁-a₀ := Int.toNat_of_nonneg (sub_nonneg.mpr (hlo a₁ ha₁))
    have hNreal : (a₀:ℝ)+(N:ℝ)=(a₁:ℝ) := by
      have hh : (N:ℝ)=(a₁:ℝ)-a₀ := by exact_mod_cast hNcast
      linarith only [hh]
    have hI : I ⊆ Finset.range N := by
      intro n hn
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
      have haJ := (Finset.mem_erase.mp ha).2
      have hne := (Finset.mem_erase.mp ha).1
      have hl := hlo a haJ
      have hh := hhi a haJ
      apply Finset.mem_range.mpr
      dsimp only [N]
      omega
    have hinj : Set.InjOn (fun a : ℤ => (a-a₀).toNat) (↑(J.erase a₁):Set ℤ) := by
      intro a ha b hb he
      have haJ := (Finset.mem_erase.mp ha).2
      have hbJ := (Finset.mem_erase.mp hb).2
      have hl := hlo a haJ
      have hl' := hlo b hbJ
      change (a-a₀).toNat=(b-a₀).toNat at he
      omega
    have hcard : I.card+1=J.card := by
      rw [show I.card=(J.erase a₁).card from Finset.card_image_of_injOn hinj]
      exact Finset.card_erase_add_one ha₁
    have hdomI z (hz : z∈Icc (a₀:ℝ) ((a₀:ℝ)+N)) : z∈S := by
      rw [hNreal] at hz
      exact hS.out (hdom a₀ ha₀) (hdom a₁ ha₁) hz
    have hnearI n (hn : n∈I) : ∃ e : ℤ, |G ((a₀:ℝ)+n)-(e:ℝ)| ≤ η := by
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
      have haJ := (Finset.mem_erase.mp ha).2
      have he : (a₀:ℝ)+((a-a₀).toNat:ℝ)=(a:ℝ) := by
        have hh := Int.toNat_of_nonneg (sub_nonneg.mpr (hlo a haJ))
        have hh' : ((a-a₀).toNat:ℝ)=(a:ℝ)-a₀ := by exact_mod_cast hh
        linarith only [hh']
      rw [he]
      exact hnear a haJ
    have hb := positive_second_derivative_count_optimized G G₁ G₂ (a₀:ℝ) N I hC hμ hη
      (fun z hz => hG z (hdomI z hz)) (fun z hz => hG₁ z (hdomI z hz))
      (fun z hz => hμlo z (hdomI z hz)) (fun z hz => hμhi z (hdomI z hz)) hI hnearI
    have hNV : (N:ℝ) ≤ V := by
      have hh := hspan a₁ ha₁ a₀ ha₀
      linarith only [hh,hNreal]
    have hb' : (I.card:ℝ) ≤ (52+144*C)*(V*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
      apply hb.trans
      gcongr
    have hcR : (I.card:ℝ)+1=J.card := by exact_mod_cast hcard
    linarith only [hb',hcR]
  · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms positive_second_derivative_integer_set_count

private theorem displacement_second_derivative_exponent_budget
    {α q : ℝ} (hlo : 17/42 ≤ α) (hhi : α ≤ 3/7) :
    let n := (3*α-1)/2
    let target := 13/84+α/2
    let r := max ((1-α)/2)
      (max (13/6-9*α/2) (max (5/2-11*α/2) (max (5/4-11*α/4) ((3-7*α)/2))))
    (q ≤ n/2 →
      6*n+6*q+10*(1-2*α+2*q)+13*(n-2*q)+r ≤ 12*target) ∧
    (n/2 ≤ q → 6*n+6*q+10*(α-2*q)+r ≤ 12*target) := by
  intro n target r
  have hr : r ≤ 12*target-(17*α+1)/2 := by
    dsimp only [r,target]
    simp only [max_le_iff]
    constructor
    · linarith only [hlo,hhi]
    constructor
    · linarith only [hlo,hhi]
    constructor
    · linarith only [hlo,hhi]
    constructor <;> linarith only [hlo,hhi]
  constructor
  · intro _
    dsimp only [n]
    linarith only [hr]
  · intro hq
    dsimp only [n] at hq ⊢
    linarith only [hr,hq]

#print axioms displacement_second_derivative_exponent_budget

private theorem triangular_resonance_curve_data
    (f : ℝ → ℝ) {A B L U F lam k a b : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hF : 0 < F) (hlam : 0 < lam) (hk : 0 < k)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 5 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U)
    (hfour : ∀ x∈Ioo A B, -F ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ -lam) :
    let h := fun x => iteratedDeriv 2 f x/2
    let c := Function.invFunOn h (Ioo A B)
    let D := fun t => c (t+k)-c t
    let D₁ := fun t => 2*(1/iteratedDeriv 3 f (c (t+k))-1/iteratedDeriv 3 f (c t))
    let E := fun t => deriv f (c (t+k))-deriv f (c t)-2*k*c t
    let v := Function.invFunOn D (Ioo a b)
    let G := fun z => E (v z)
    let G₁ := fun z => 2*(v z+k)
    let G₂ := fun z => 2/D₁ (v z)
    let μ := L^3/(2*F*k)
    let C := max 1 (216*F*U^3/(lam*L^3))
    (∀ t∈Ioo a b, t∈h '' Ioo A B ∧ t+k∈h '' Ioo A B) →
    (D '' Ioo a b).OrdConnected ∧
    (∀ t∈Ioo a b, v (D t)=t ∧ G (D t)=E t ∧ G₁ (D t)=2*(t+k)) ∧
    ∀ z∈D '' Ioo a b,
      HasDerivAt G (G₁ z) z ∧ HasDerivAt G₁ (G₂ z) z ∧ μ ≤ G₂ z ∧ G₂ z ≤ C*μ := by
  intro h c D D₁ E v G G₁ G₂ μ C hdom
  let J := fun t => iteratedDeriv 4 f (c t)/(iteratedDeriv 3 f (c t))^3
  let D₂ := fun t => -4*(J (t+k)-J t)
  have hjets t (ht : t∈Ioo a b) :
      HasDerivAt D (D₁ t) t ∧ HasDerivAt D₁ (D₂ t) t ∧
        HasDerivAt E (2*(t+k)*D₁ t) t :=
    triangular_resonance_parametric_jets f hL hf (fun x hx => (hthree x hx).1)
      (hdom t ht).1 (hdom t ht).2
  have hbounds t (ht : t∈Ioo a b) :
      lam*k/(54*U^3) ≤ D₁ t ∧ D₁ t ≤ 4*F*k/L^3 :=
    triangular_displacement_derivative_bounds f hL hlam hk
      (fun x hx => (hf x hx).of_le (by norm_num)) hthree hfour
      (hdom t ht).1 (hdom t ht).2
  have hpos t (ht : t∈Ioo a b) : 0 < D₁ t :=
    (by positivity : 0 < lam*k/(54*U^3)).trans_le (hbounds t ht).1
  have hinverse := monotone_parametric_curve_inverse_jets D D₁ D₂ E
    (fun t ht => (hjets t ht).1) (fun t ht => (hjets t ht).2.1)
    (fun t ht => (hjets t ht).2.2) hpos
  refine ⟨?_,?_,?_⟩
  · exact isPreconnected_iff_ordConnected.mp (isPreconnected_Ioo.image D
      (fun t ht => (hjets t ht).1.continuousAt.continuousWithinAt))
  · intro t ht
    have he : v (D t)=t := hinverse.1 t ht
    exact ⟨he,by change E (v (D t))=E t; rw [he],
      by change 2*(v (D t)+k)=2*(t+k); rw [he]⟩
  · intro z hz
    have hi := hinverse.2 z hz
    have hb := hbounds (v z) hi.2.1
    have hp := hpos (v z) hi.2.1
    refine ⟨hi.2.2.1,hi.2.2.2.1,?_,?_⟩
    · have he : μ=2/(4*F*k/L^3) := by dsimp only [μ]; field_simp; ring
      rw [he]
      exact div_le_div_of_nonneg_left (by norm_num) hp hb.2
    · have hupper : G₂ z ≤ 2/(lam*k/(54*U^3)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hb.1
      have he : 2/(lam*k/(54*U^3))=(216*F*U^3/(lam*L^3))*μ := by
        dsimp only [μ]
        field_simp
        ring
      rw [he] at hupper
      exact hupper.trans (mul_le_mul_of_nonneg_right (le_max_right 1 _) (by dsimp only [μ]; positivity))

#print axioms triangular_resonance_curve_data

private theorem triangular_resonance_curve_rounded_point
    (f : ℝ → ℝ) {A B L U F lam a b x y ε : ℝ} (m n k e : ℤ)
    (hL : 0 < L) (hU : 0 < U) (hF : 0 < F) (hlam : 0 < lam) (hk : 0 < k)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 5 f t)
    (hthree : ∀ t∈Ioo A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U)
    (hfour : ∀ t∈Ioo A B, -F ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hx : x∈Ioo A B) (hy : y∈Ioo A B)
    (hmI : (m:ℝ)∈Ioo A B) (hnI : (n:ℝ)∈Ioo A B)
    (hm : |(m:ℝ)-x| ≤ 1/2) (hn : |(n:ℝ)-y| ≤ 1/2)
    (hnear : |iteratedDeriv 1 f n-iteratedDeriv 1 f m-(e:ℝ)| ≤ ε) :
    let h := fun t => iteratedDeriv 2 f t/2
    let c := Function.invFunOn h (Ioo A B)
    let D := fun t => c (t+k)-c t
    let E := fun t => deriv f (c (t+k))-deriv f (c t)-2*(k:ℝ)*c t
    let v := Function.invFunOn D (Ioo a b)
    let G := fun z => E (v z)
    let μ := L^3/(2*F*k)
    let C := max 1 (216*F*U^3/(lam*L^3))
    (∀ t∈Ioo a b, t∈h '' Ioo A B ∧ t+k∈h '' Ioo A B) →
    h y=h x+k → h x∈Ioo a b → (n:ℝ)-m∈D '' Ioo a b →
    |G ((n:ℝ)-m)-((e-2*k*m:ℤ):ℝ)| ≤ ε+9*U/4+C*μ := by
  intro h c D E v G μ C hdom hlevel hxparam hdpoint
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hd := triangular_resonance_curve_data f hL hU hF hlam hkr hf hthree hfour hdom
  let D₁ := fun t => 2*(1/iteratedDeriv 3 f (c (t+k))-1/iteratedDeriv 3 f (c t))
  let G₁ := fun z => 2*(v z+k)
  let G₂ := fun z => 2/D₁ (v z)
  have hp := inverse_curvature_derivative f hL
    (fun t ht => (hf t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1)
  have hcx : c (h x)=x := hp.1 x hx
  have hcy : c (h x+k)=y := by rw [←hlevel]; exact hp.1 y hy
  have hD : D (h x)=y-x := by change c (h x+k)-c (h x)=y-x; rw [hcx,hcy]
  have hleft : v (y-x)=h x := by rw [←hD]; exact (hd.2.1 _ hxparam).1
  have hvalue : G (y-x)=iteratedDeriv 1 f y-iteratedDeriv 1 f x-2*(k:ℝ)*x := by
    change E (v (y-x))= _
    rw [hleft]
    change deriv f (c (h x+k))-deriv f (c (h x))-2*(k:ℝ)*c (h x)= _
    rw [hcx,hcy]
    simp only [iteratedDeriv_one]
  have hslope : G₁ (y-x)=2*(h x+k) := by dsimp only [G₁]; rw [hleft]
  have hpoint : y-x∈D '' Ioo a b := ⟨h x,hxparam,hD⟩
  have hsegment := hd.1.uIcc_subset hpoint hdpoint
  have hroundsegment : uIcc x (m:ℝ) ∪ uIcc y (n:ℝ) ⊆ Ioo A B :=
    union_subset ((convex_Ioo A B).ordConnected.uIcc_subset hx hmI)
      ((convex_Ioo A B).ordConnected.uIcc_subset hy hnI)
  apply rounded_triangular_curve_near_integer f G G₁ G₂ m n k e
    (fun t ht => (hf t (hroundsegment ht)).of_le (by norm_num))
    (fun t ht => by
      rw [abs_of_pos (hL.trans_le (hthree t (hroundsegment ht)).1)]
      exact (hthree t (hroundsegment ht)).2)
    hm hn (v:=h x) (by dsimp only [h]; ring)
    (by rw [←hlevel]; dsimp only [h]; ring)
    hnear hvalue hslope
  · exact fun z hz => (hd.2.2 z (hsegment hz)).1
  · exact fun z hz => (hd.2.2 z (hsegment hz)).2.1
  · intro z hz
    have hb := hd.2.2 z (hsegment hz)
    have hμ : 0 < μ := by dsimp only [μ]; positivity
    rw [abs_of_nonneg (hμ.le.trans hb.2.2.1)]
    exact hb.2.2.2

#print axioms triangular_resonance_curve_rounded_point

private theorem fixed_displacement_level_spacing
    (f : ℝ → ℝ) {A B lam d m n k ε : ℝ}
    (hlam : 0 < lam) (hd : 0 < d)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Ioo A B, iteratedDeriv 4 f t ≤ -lam)
    (hm : m∈Ioo A B) (hmd : m+d∈Ioo A B)
    (hn : n∈Ioo A B) (hnd : n+d∈Ioo A B)
    (hmlevel : |(iteratedDeriv 2 f (m+d)-iteratedDeriv 2 f m)/2-k| ≤ ε)
    (hnlevel : |(iteratedDeriv 2 f (n+d)-iteratedDeriv 2 f n)/2-k| ≤ ε) :
    |m-n| ≤ 4*ε/(lam*d) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hmlevel
  suffices hordered : ∀ u w : ℝ, u∈Ioo A B → u+d∈Ioo A B →
      w∈Ioo A B → w+d∈Ioo A B → u ≤ w →
      |(iteratedDeriv 2 f (u+d)-iteratedDeriv 2 f u)/2-k| ≤ ε →
      |(iteratedDeriv 2 f (w+d)-iteratedDeriv 2 f w)/2-k| ≤ ε →
      w-u ≤ 4*ε/(lam*d) by
    rcases le_total m n with hmn | hnm
    · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hmn)]
      exact hordered m n hm hmd hn hnd hmn hmlevel hnlevel
    · rw [abs_of_nonneg (sub_nonneg.mpr hnm)]
      exact hordered n m hn hnd hm hmd hnm hnlevel hmlevel
  intro u w hu hud hw hwd huw hul hwl
  by_cases heq : u=w
  · subst w
    simp only [sub_self]
    positivity
  have hlt : u < w := lt_of_le_of_ne huw heq
  let g := fun t => (iteratedDeriv 2 f (t+d)-iteratedDeriv 2 f t)/2
  let g₁ := fun t => (iteratedDeriv 3 f (t+d)-iteratedDeriv 3 f t)/2
  have htI t (ht : t∈Icc u w) : t∈Ioo A B ∧ t+d∈Ioo A B := by
    constructor <;> constructor <;> linarith only [hu.1,hw.2,hud.1,hwd.2,ht.1,ht.2]
  have hg t (ht : t∈Icc u w) : HasDerivAt g (g₁ t) t := by
    have h₀ := (contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf t (htI t ht).1)).differentiableAt (by norm_num)
    have h₁ := (contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf (t+d) (htI t ht).2)).differentiableAt (by norm_num)
    have h₀' : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f t) t := by
      simpa only [iteratedDeriv_succ] using h₀.hasDerivAt
    have h₁' : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f (t+d)) (t+d) := by
      simpa only [iteratedDeriv_succ] using h₁.hasDerivAt
    convert ((h₁'.comp t ((hasDerivAt_id t).add_const d)).sub h₀').div_const 2 using 1
    ring
  have hg₁ t (ht : t∈Icc u w) : g₁ t ≤ -(lam*d/2) := by
    have hseg : Icc t (t+d) ⊆ Ioo A B :=
      (convex_Ioo A B).ordConnected.out (htI t ht).1 (htI t ht).2
    have hder z (hz : z∈Icc t (t+d)) :
        HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f z) z := by
      have hh := (contDiffAt_iteratedDeriv_finite (n:=1) (j:=3) (hf z (hseg hz))).differentiableAt (by norm_num)
      simpa only [iteratedDeriv_succ] using hh.hasDerivAt
    obtain ⟨z,hz,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f) (iteratedDeriv 4 f)
      (by linarith only [hd] : t < t+d)
      (fun z hz => (hder z hz).continuousAt.continuousWithinAt)
      (fun z hz => hder z ⟨hz.1.le,hz.2.le⟩)
    have hdiff := (eq_div_iff (by linarith only [hd] : t+d-t ≠ 0)).mp he
    have hbound := mul_le_mul_of_nonneg_right (hfour z (hseg ⟨hz.1.le,hz.2.le⟩)) hd.le
    dsimp only [g₁]
    nlinarith only [hdiff,hbound]
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope g g₁ hlt
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => hg t ⟨ht.1.le,ht.2.le⟩)
  have hdiff := (eq_div_iff (sub_ne_zero.mpr hlt.ne')).mp he
  have hbound := mul_le_mul_of_nonneg_right (hg₁ t ⟨ht.1.le,ht.2.le⟩) (sub_nonneg.mpr huw)
  have hu' : |g u-k| ≤ ε := hul
  have hw' : |g w-k| ≤ ε := hwl
  apply (le_div_iff₀ (mul_pos hlam hd)).mpr
  nlinarith only [hdiff,hbound,(abs_le.mp hu').2,(abs_le.mp hw').1]

#print axioms fixed_displacement_level_spacing

private theorem rounded_curvature_difference_error
    (f : ℝ → ℝ) {x y m n U k : ℝ}
    (hf : ∀ t∈uIcc x m ∪ uIcc y n, ContDiffAt ℝ 3 f t)
    (hb : ∀ t∈uIcc x m ∪ uIcc y n, |iteratedDeriv 3 f t| ≤ 6*U)
    (hm : |m-x| ≤ 1/2) (hn : |n-y| ≤ 1/2)
    (hlevel : iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2=k) :
    |(iteratedDeriv 2 f n-iteratedDeriv 2 f m)/2-k| ≤ 3*U := by
  let h := fun t => iteratedDeriv 2 f t/2
  have hU : 0 ≤ U := by
    have hh := hb x (Or.inl left_mem_uIcc)
    linarith only [hh,abs_nonneg (iteratedDeriv 3 f x)]
  have hd t (ht : t∈uIcc x m ∪ uIcc y n) : HasDerivAt h (iteratedDeriv 3 f t/2) t := by
    have hh := (contDiffAt_iteratedDeriv_finite (n:=1) (j:=2) (hf t ht)).differentiableAt (by norm_num)
    simpa only [h,iteratedDeriv_succ] using hh.hasDerivAt.div_const 2
  have hdB t (ht : t∈uIcc x m ∪ uIcc y n) : ‖iteratedDeriv 3 f t/2‖ ≤ 3*U := by
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := hb t ht
    linarith only [hh]
  have hx := (convex_uIcc x m).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t (Or.inl ht)).hasDerivWithinAt)
    (fun t ht => hdB t (Or.inl ht)) left_mem_uIcc right_mem_uIcc
  have hy := (convex_uIcc y n).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t (Or.inr ht)).hasDerivWithinAt)
    (fun t ht => hdB t (Or.inr ht)) left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs] at hx hy
  have hmx : |h m-h x| ≤ 3*U/2 := hx.trans (by nlinarith only [mul_le_mul_of_nonneg_left hm hU])
  have hny : |h n-h y| ≤ 3*U/2 := hy.trans (by nlinarith only [mul_le_mul_of_nonneg_left hn hU])
  calc
    _ = |(h n-h y)-(h m-h x)| := by rw [←hlevel]; dsimp only [h]; congr 1; ring
    _ ≤ |h n-h y|+|h m-h x| := abs_sub _ _
    _ ≤ _ := by linarith only [hmx,hny]

#print axioms rounded_curvature_difference_error

private theorem block_cloud_card_of_center_interval
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (center block : ι → ℤ)
    (H Bmul : ℕ) (s : ℤ) {c ρ : ℝ} (hH : 0 < H) (hρ : 0 ≤ ρ)
    (hspan : ∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul)
    (hdist : ∀ i∈S, |(center i:ℝ)-c| ≤ ρ) :
    (S.card:ℝ) ≤ Bmul*(3+2*ρ/H) := by
  let W := S.image block
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hW : (W.card:ℝ) ≤ 3+2*ρ/H := by
    have hw := integer_card_le_of_abs_sub_le (a:=(c+2*(H:ℝ)-s)/H) W
      (by positivity : 0 ≤ ρ/H+1) (by
        intro j hj
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
        have he : (block i:ℝ)-(c+2*(H:ℝ)-s)/H=
            ((H:ℝ)*block i-(c+2*(H:ℝ)-s))/H := by field_simp
        rw [he,abs_div,abs_of_pos hHr]
        apply (div_le_iff₀ hHr).mpr
        rw [show (ρ/(H:ℝ)+1)*H=ρ+H by field_simp]
        have hlo : (H:ℝ) ≤ (s:ℝ)+(H:ℝ)*block i-center i := by exact_mod_cast (hspan i hi).1
        have hhi : (s:ℝ)+(H:ℝ)*block i-center i ≤ 3*(H:ℝ) := by exact_mod_cast (hspan i hi).2
        have hd := abs_le.mp (hdist i hi)
        exact abs_le.mpr ⟨by linarith only [hlo,hhi,hd.1,hd.2],by linarith only [hlo,hhi,hd.1,hd.2]⟩)
    convert hw using 1
    ring
  have hc : (S.card:ℝ)=∑ j∈W,((S.filter (fun i => block i=j)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise
      (fun i hi => Finset.mem_image_of_mem block hi)
  calc
    _ = _ := hc
    _ ≤ ∑ j∈W,(Bmul:ℝ) := Finset.sum_le_sum (fun j _ => by exact_mod_cast hmul j)
    _ = (Bmul:ℝ)*W.card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg _)

#print axioms block_cloud_card_of_center_interval

private theorem fixed_displacement_source_pair_fibers
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
    (center block : ι → ℤ) (H Bmul : ℕ) (s : ℤ) (f : ℝ → ℝ)
    {A B lam d k ε : ℝ} (hH : 0 < H) (hlam : 0 < lam) (hd : 0 < d) (hε : 0 ≤ ε)
    (hspan : ∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Ioo A B, iteratedDeriv 4 f t ≤ -lam)
    (hcenter : ∀ i∈S, (center i:ℝ)∈Ioo A B)
    (hRS : R ⊆ S ×ˢ S)
    (hfix : ∀ p∈R, (center p.2:ℝ)-center p.1=d)
    (hlevel : ∀ p∈R,
      |(iteratedDeriv 2 f (center p.2)-iteratedDeriv 2 f (center p.1))/2-k| ≤ ε) :
    (R.card:ℝ) ≤ 3*(Bmul:ℝ)^2*(3+8*ε/(lam*d*H)) := by
  let L := R.image Prod.fst
  have hLS : L ⊆ S := by
    intro i hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_product.mp (hRS hp)).1
  have hsubmul (T : Finset ι) (hTS : T ⊆ S) (j : ℤ) :
      (T.filter (fun i => block i=j)).card ≤ Bmul := by
    apply (Finset.card_le_card ?_).trans (hmul j)
    intro i hi
    obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hTS hi,he⟩
  have hrow i : ((R.filter (fun p => p.1=i)).card:ℝ) ≤ 3*Bmul := by
    let T := (R.filter (fun p => p.1=i)).image Prod.snd
    have hinj : Set.InjOn Prod.snd (↑(R.filter (fun p => p.1=i)):Set (ι × ι)) := by
      intro p hp q hq he
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
    have hTS : T ⊆ S := by
      intro j hj
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_product.mp (hRS (Finset.mem_filter.mp hp).1)).2
    have hdist j (hj : j∈T) : |(center j:ℝ)-((center i:ℝ)+d)| ≤ 0 := by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      have hh := hfix p hp
      rw [he] at hh
      rw [show (center p.2:ℝ)-((center i:ℝ)+d)=0 by linarith only [hh],abs_zero]
    have hb := block_cloud_card_of_center_interval T center block H Bmul s hH le_rfl
      (fun j hj => hspan j (hTS hj)) (hsubmul T hTS) hdist
    have hc : T.card=(R.filter (fun p => p.1=i)).card := Finset.card_image_of_injOn hinj
    rw [hc] at hb
    simpa only [mul_zero,zero_mul,zero_div,add_zero,mul_comm] using hb
  by_cases hR : R.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hR
    let ρ := 4*ε/(lam*d)
    have hdist i (hi : i∈L) : |(center i:ℝ)-center p₀.1| ≤ ρ := by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
      have hpp := Finset.mem_product.mp (hRS hp)
      have hp₀p := Finset.mem_product.mp (hRS hp₀)
      have he : (center p.1:ℝ)+d=center p.2 := by linarith only [hfix p hp]
      have he₀ : (center p₀.1:ℝ)+d=center p₀.2 := by linarith only [hfix p₀ hp₀]
      apply fixed_displacement_level_spacing f hlam hd hf hfour
        (hcenter _ hpp.1) (by rw [he]; exact hcenter _ hpp.2)
        (hcenter _ hp₀p.1) (by rw [he₀]; exact hcenter _ hp₀p.2)
      · simpa only [he] using hlevel p hp
      · simpa only [he₀] using hlevel p₀ hp₀
    have hL := block_cloud_card_of_center_interval L center block H Bmul s hH
      (by dsimp only [ρ]; positivity) (fun i hi => hspan i (hLS hi)) (hsubmul L hLS) hdist
    have hc : (R.card:ℝ)=∑ i∈L,((R.filter (fun p => p.1=i)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun (p : ι × ι) hp => Finset.mem_image_of_mem Prod.fst hp)
    calc
      _ = _ := hc
      _ ≤ ∑ i∈L,3*(Bmul:ℝ) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = 3*(Bmul:ℝ)*L.card := by simp [mul_comm]
      _ ≤ 3*(Bmul:ℝ)*(Bmul*(3+2*ρ/H)) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := by dsimp only [ρ]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hR,Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms fixed_displacement_source_pair_fibers

private theorem rounded_positive_curvature_shift_bounds
    (f : ℝ → ℝ) {A B L U x y m n k : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hk : 6*U ≤ k)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 3 f t)
    (hthree : ∀ t∈Ioo A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U)
    (hx : x∈Ioo A B) (hy : y∈Ioo A B)
    (hm : |m-x| ≤ 1/2) (hn : |n-y| ≤ 1/2)
    (hlevel : iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2=k) :
    k/(6*U) ≤ n-m ∧ n-m ≤ 2*k/L+1 := by
  let h := fun t => iteratedDeriv 2 f t/2
  have hkp : 0 < k := (by positivity : 0 < 6*U).trans_le hk
  have hd t (ht : t∈Ioo A B) : HasDerivAt h (iteratedDeriv 3 f t/2) t := by
    have hh := (contDiffAt_iteratedDeriv_finite (n:=1) (j:=2) (hf t ht)).differentiableAt (by norm_num)
    simpa only [h,iteratedDeriv_succ] using hh.hasDerivAt.div_const 2
  have hmono : StrictMonoOn h (Ioo A B) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo A B)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t∈Ioo A B := by simpa only [interior_Ioo] using ht
      rw [(hd t ht').deriv]
      exact div_pos (hL.trans_le (hthree t ht').1) (by norm_num)
  have hxy : x < y := by
    by_contra hnot
    have hh := hmono.monotoneOn hy hx (le_of_not_gt hnot)
    change h y-h x=k at hlevel
    linarith only [hh,hlevel,hkp]
  have hseg : Icc x y ⊆ Ioo A B := (convex_Ioo A B).ordConnected.out hx hy
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope h (fun t => iteratedDeriv 3 f t/2) hxy
    (fun t ht => (hd t (hseg ht)).continuousAt.continuousWithinAt)
    (fun t ht => hd t (hseg ⟨ht.1.le,ht.2.le⟩))
  have hdiff := (eq_div_iff (sub_ne_zero.mpr hxy.ne')).mp he
  change (iteratedDeriv 3 f t/2)*(y-x)=iteratedDeriv 2 f y/2-iteratedDeriv 2 f x/2 at hdiff
  rw [hlevel] at hdiff
  have hlo := mul_le_mul_of_nonneg_right (hthree t (hseg ⟨ht.1.le,ht.2.le⟩)).1 (sub_nonneg.mpr hxy.le)
  have hhi := mul_le_mul_of_nonneg_right (hthree t (hseg ⟨ht.1.le,ht.2.le⟩)).2 (sub_nonneg.mpr hxy.le)
  have hround : (y-x)-1 ≤ n-m ∧ n-m ≤ (y-x)+1 := by
    exact ⟨by linarith only [(abs_le.mp hm).2,(abs_le.mp hn).1],
      by linarith only [(abs_le.mp hm).1,(abs_le.mp hn).2]⟩
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 6*U)).mpr
    have hh := mul_le_mul_of_nonneg_left hround.1 hU.le
    nlinarith only [hh,hhi,hdiff,hk]
  · have hh : y-x ≤ 2*k/L := (le_div_iff₀ hL).mpr (by nlinarith only [hlo,hdiff])
    linarith only [hh,hround.2]

#print axioms rounded_positive_curvature_shift_bounds

























-- Exact residual for the tested borrowed-window/old-triangular budget.
-- This identity is not an impossibility claim about alternate analytic proofs.
example (α : ℝ) : (67*α+33)/168-(13/84+α/2)=(7-17*α)/168 := by ring

example {α : ℝ} (hα : α < 7/17) : 13/84+α/2 < (67*α+33)/168 := by
  linarith only [hα]

example (α : ℝ) : (5/24+3*α/8)-(13/84+α/2)=(3/7-α)/8 := by ring

example {α : ℝ} (hα : α < 3/7) : 13/84+α/2 < 5/24+3*α/8 := by
  linarith only [hα]

#print axioms source_resonance_short_block_label_count

#print axioms source_resonance_residual_interval

#print axioms short_curve_integer_label_count

#print axioms actual_source_resonance_curve_strip

#print axioms rounded_first_derivative_error
#print axioms rounded_displacement_strip

#print axioms dual_coefficient_lower
#print axioms actual_four_coordinate_constraints
#print axioms affine_lattice_strip
#print axioms rational_strip_unique
#print axioms inverse_curvature_derivative
#print axioms resonance_displacement_derivative
#print axioms displacement_scalar_bound
#print axioms resonance_displacement_short_box
#print axioms inverse_lift_fract
#print axioms actual_source_affine_lattice_strip

end TaoTrudgianYang2025.RefinedPrototype

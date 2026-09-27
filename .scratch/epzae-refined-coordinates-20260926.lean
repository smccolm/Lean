import TaoTrudgianYang2025.ParabolaBilinearLocalization
import TaoTrudgianYang2025.ContinuousSecondDerivativeRange
import TaoTrudgianYang2025.FiniteSmoothThirdDerivative
import TaoTrudgianYang2025.IntegerFourierTails
import GafniTao.HeathBrownKernelFourier
import TaoTrudgianYang2025.RobertSargosDisplacementSums
import TaoTrudgianYang2025.RobertSargosExponentPair

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

private theorem displacement_elementary_twelfth {P U C Y ε r : ℝ}
    (hP : 1 ≤ P) (hU : 0 < U) (hU1 : U ≤ 1) (hY : 0 ≤ Y)
    (hε : 0 ≤ ε) (hr : (2:ℝ)/9 ≤ r)
    (hbound : Y ≤ C*P*U^r*(1+Real.log P)) :
    Y^12 ≤ C^12*P^ε*(1+Real.log P)^24*(P^11*U+P^12*U^((8:ℝ)/3)) := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hlogP := Real.log_nonneg hP
  have hJ : 1 ≤ 1+Real.log P := by linarith only [hlogP]
  have hUexp : U^(r*12) ≤ U^((8:ℝ)/3) :=
    Real.rpow_le_rpow_of_exponent_ge hU hU1 (by linarith only [hr])
  have hPε : 1 ≤ P^ε := Real.one_le_rpow hP hε
  have hJpow := pow_le_pow_right₀ hJ (by norm_num : 12 ≤ 24)
  calc
    _ ≤ (C*P*U^r*(1+Real.log P))^12 := pow_le_pow_left₀ hY hbound 12
    _ = C^12*P^12*U^(r*12)*(1+Real.log P)^12 := by
      rw [mul_pow,mul_pow,mul_pow,←Real.rpow_mul_natCast hU.le]
      norm_num
    _ ≤ C^12*P^12*U^((8:ℝ)/3)*(1+Real.log P)^24 := by gcongr
    _ ≤ C^12*(P^11*U+P^12*U^((8:ℝ)/3))*(1+Real.log P)^24 := by
      have hh : P^12*U^((8:ℝ)/3) ≤ P^11*U+P^12*U^((8:ℝ)/3) :=
        le_add_of_nonneg_left (by positivity)
      calc
        _ = C^12*(P^12*U^((8:ℝ)/3))*(1+Real.log P)^24 := by ring
        _ ≤ _ := by gcongr
    _ ≤ _ := by
      have hh := le_mul_of_one_le_right
        (show 0 ≤ C^12*(P^11*U+P^12*U^((8:ℝ)/3))*(1+Real.log P)^24 by positivity) hPε
      convert hh using 1
      ring

#print axioms displacement_elementary_twelfth

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

private theorem rounded_shift_source_pair_count_of_displacements
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
    (center block : ι → ℤ) (z : ι → ℝ) (H Bmul : ℕ) (s : ℤ)
    (f : ℝ → ℝ) (J : Finset ℤ) {A B L U lam k : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hU : 0 < U) (hlam : 0 < lam) (hk : 6*U ≤ k)
    (hspan : ∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 4 f t)
    (hthree : ∀ t∈Ioo A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U)
    (hfour : ∀ t∈Ioo A B, iteratedDeriv 4 f t ≤ -lam)
    (hcenter : ∀ i∈S, (center i:ℝ)∈Ioo A B)
    (hz : ∀ i∈S, z i∈Ioo A B)
    (hround : ∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2)
    (hRS : R ⊆ S ×ˢ S)
    (hlevel : ∀ p∈R, iteratedDeriv 2 f (z p.2)/2-iteratedDeriv 2 f (z p.1)/2=k)
    (hJ : ∀ p∈R, center p.2-center p.1∈J) :
    (R.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*k*H)))*J.card := by
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hkp : 0 < k := (by positivity : 0 < 6*U).trans_le hk
  have hrounded p (hp : p∈R) :
      |(iteratedDeriv 2 f (center p.2)-iteratedDeriv 2 f (center p.1))/2-k| ≤ 3*U := by
    have hpp := Finset.mem_product.mp (hRS hp)
    have hseg : uIcc (z p.1) (center p.1:ℝ) ∪ uIcc (z p.2) (center p.2:ℝ) ⊆ Ioo A B :=
      union_subset ((convex_Ioo A B).ordConnected.uIcc_subset (hz _ hpp.1) (hcenter _ hpp.1))
        ((convex_Ioo A B).ordConnected.uIcc_subset (hz _ hpp.2) (hcenter _ hpp.2))
    apply rounded_curvature_difference_error f
      (fun t ht => (hf t (hseg ht)).of_le (by norm_num)) ?_
      (hround _ hpp.1) (hround _ hpp.2) (hlevel p hp)
    intro t ht
    rw [abs_of_pos (hL.trans_le (hthree t (hseg ht)).1)]
    exact (hthree t (hseg ht)).2
  have hfiber d : ((R.filter (fun p => center p.2-center p.1=d)).card:ℝ) ≤
      3*(Bmul:ℝ)^2*(3+144*U^2/(lam*k*H)) := by
    let T := R.filter (fun p => center p.2-center p.1=d)
    by_cases hT : T.Nonempty
    · obtain ⟨p,hp⟩ := hT
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      have hpp := Finset.mem_product.mp (hRS hp)
      have hbounds := rounded_positive_curvature_shift_bounds f hL hU hk
        (fun t ht => (hf t ht).of_le (by norm_num)) hthree
        (hz _ hpp.1) (hz _ hpp.2) (hround _ hpp.1) (hround _ hpp.2) (hlevel p hp)
      have hdcast : (center p.2:ℝ)-center p.1=(d:ℝ) := by exact_mod_cast he
      rw [hdcast] at hbounds
      have hd : (0:ℝ) < d := (div_pos hkp (by positivity)).trans_le hbounds.1
      have hb := fixed_displacement_source_pair_fibers S T center block H Bmul s f
        hH hlam hd (by positivity : 0 ≤ 3*U) hspan hmul hf hfour hcenter
        (fun q hq => hRS (Finset.mem_filter.mp hq).1)
        (fun q hq => by exact_mod_cast (Finset.mem_filter.mp hq).2)
        (fun q hq => hrounded q (Finset.mem_filter.mp hq).1)
      have hden : lam*(k/(6*U))*H ≤ lam*(d:ℝ)*H :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbounds.1 hlam.le) hHr.le
      have hfrac : 8*(3*U)/(lam*(d:ℝ)*H) ≤ 144*U^2/(lam*k*H) := by
        calc
          _ ≤ 8*(3*U)/(lam*(k/(6*U))*H) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
          _ = _ := by field_simp; ring
      exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hfrac) (by positivity))
    · change (T.card:ℝ) ≤ _
      rw [Finset.not_nonempty_iff_eq_empty.mp hT,Finset.card_empty,Nat.cast_zero]
      positivity
  have hc : (R.card:ℝ)=∑ d∈J,((R.filter (fun p => center p.2-center p.1=d)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hJ
  calc
    _ = _ := hc
    _ ≤ ∑ _d∈J,3*(Bmul:ℝ)^2*(3+144*U^2/(lam*k*H)) :=
      Finset.sum_le_sum (fun d _ => hfiber d)
    _ = _ := by simp [mul_comm]

#print axioms rounded_shift_source_pair_count_of_displacements

private theorem triangular_interior_fixed_shift_source_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
    (center block : ι → ℤ) (z : ι → ℝ) (H Bmul : ℕ) (s k : ℤ)
    (f : ℝ → ℝ) {A B L U F lam ε a b : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hU : 0 < U) (hF : 0 < F) (hlam : 0 < lam)
    (hk : 0 < k) (hkU : 6*U ≤ k) (hε : 0 ≤ ε)
    (hspan : ∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 5 f t)
    (hthree : ∀ t∈Ioo A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U)
    (hfour : ∀ t∈Ioo A B, -F ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hcenter : ∀ i∈S, (center i:ℝ)∈Ioo A B)
    (hz : ∀ i∈S, z i∈Ioo A B)
    (hround : ∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2)
    (hRS : R ⊆ S ×ˢ S)
    (hlevel : ∀ p∈R, iteratedDeriv 2 f (z p.2)/2-iteratedDeriv 2 f (z p.1)/2=(k:ℝ))
    (hnear : ∀ p∈R, ∃ e : ℤ,
      |iteratedDeriv 1 f (center p.2)-iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ ε) :
    let h := fun t => iteratedDeriv 2 f t/2
    let c := Function.invFunOn h (Ioo A B)
    let D := fun t => c (t+k)-c t
    let μ := L^3/(2*F*k)
    let C := max 1 (216*F*U^3/(lam*L^3))
    (∀ t∈Ioo a b, t∈h '' Ioo A B ∧ t+k∈h '' Ioo A B) →
    (∀ p∈R, h (z p.1)∈Ioo a b) →
    (∀ p∈R, (center p.2:ℝ)-center p.1∈D '' Ioo a b) →
    (R.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*k*H)))*
      (1+(52+144*C)*((2*(k:ℝ)/L+1)*(ε+9*U/4+C*μ+μ^((1:ℝ)/3))+
        μ^(-(1:ℝ)/2))) := by
  intro h c D μ C hdom hparam hinterior
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hC : 1 ≤ C := le_max_left _ _
  have hCp : 0 < C := zero_lt_one.trans_le hC
  let E := fun t => deriv f (c (t+k))-deriv f (c t)-2*(k:ℝ)*c t
  let v := Function.invFunOn D (Ioo a b)
  let G := fun z => E (v z)
  let D₁ := fun t => 2*(1/iteratedDeriv 3 f (c (t+k))-1/iteratedDeriv 3 f (c t))
  let G₁ := fun z => 2*(v z+k)
  let G₂ := fun z => 2/D₁ (v z)
  let J := R.image (fun p => center p.2-center p.1)
  have hdata := triangular_resonance_curve_data f hL hU hF hlam hkr hf hthree hfour hdom
  have hJdom j (hj : j∈J) : (j:ℝ)∈D '' Ioo a b := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    simpa only [Int.cast_sub] using hinterior p hp
  have hJbounds j (hj : j∈J) : (k:ℝ)/(6*U) ≤ j ∧ (j:ℝ) ≤ 2*(k:ℝ)/L+1 := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    have hpp := Finset.mem_product.mp (hRS hp)
    have hb := rounded_positive_curvature_shift_bounds f hL hU hkU
      (fun t ht => (hf t ht).of_le (by norm_num)) hthree
      (hz _ hpp.1) (hz _ hpp.2) (hround _ hpp.1) (hround _ hpp.2) (hlevel p hp)
    simpa only [Int.cast_sub] using hb
  have hJnear j (hj : j∈J) : ∃ e : ℤ, |G j-(e:ℝ)| ≤ ε+9*U/4+C*μ := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    have hpp := Finset.mem_product.mp (hRS hp)
    obtain ⟨e,he⟩ := hnear p hp
    refine ⟨e-2*k*center p.1,?_⟩
    have hb := triangular_resonance_curve_rounded_point f (center p.1) (center p.2) k e
      hL hU hF hlam hk hf hthree hfour (hz _ hpp.1) (hz _ hpp.2)
      (hcenter _ hpp.1) (hcenter _ hpp.2) (hround _ hpp.1) (hround _ hpp.2)
      he hdom (by
        have hh := hlevel p hp
        change h (z p.2)-h (z p.1)=(k:ℝ) at hh
        change h (z p.2)=h (z p.1)+(k:ℝ)
        linarith only [hh])
      (hparam p hp) (hinterior p hp)
    simpa only [Int.cast_sub] using hb
  have hJcard := positive_second_derivative_integer_set_count G G₁ G₂ J hC hμ
    (by positivity : 0 ≤ ε+9*U/4+C*μ) (by positivity : 0 ≤ 2*(k:ℝ)/L+1)
    hdata.1 (fun t ht => (hdata.2.2 t ht).1) (fun t ht => (hdata.2.2 t ht).2.1)
    (fun t ht => (hdata.2.2 t ht).2.2.1) (fun t ht => (hdata.2.2 t ht).2.2.2)
    hJdom (by
      intro i hi j hj
      have hi' := hJbounds i hi
      have hj' := hJbounds j hj
      have hjpos : (0:ℝ) < j := (div_pos hkr (by positivity)).trans_le hj'.1
      linarith only [hi'.2,hjpos]) hJnear
  have hRcard := rounded_shift_source_pair_count_of_displacements S R center block z H Bmul s f J
    hH hL hU hlam hkU hspan hmul (fun t ht => (hf t ht).of_le (by norm_num))
    hthree (fun t ht => (hfour t ht).2) hcenter hz hround hRS hlevel
    (fun p hp => Finset.mem_image_of_mem _ hp)
  exact hRcard.trans (mul_le_mul_of_nonneg_left hJcard (by positivity))

#print axioms triangular_interior_fixed_shift_source_count

private theorem outside_interval_near_integer_card
    (J : Finset ℤ) {S : Set ℝ} (hS : S.OrdConnected)
    (hout : ∀ j∈J, (j:ℝ)∉S)
    (hnear : ∀ j∈J, ∃ x∈S, |(j:ℝ)-x| ≤ 1) : J.card ≤ 2 := by
  classical
  by_cases hJ : J.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hJ
    obtain ⟨x₀,hx₀,_⟩ := hnear j₀ hj₀
    have hleft i (hi : i∈J) j (hj : j∈J) (hj₀ : (j:ℝ) < x₀) (hij : i < j) : False := by
      obtain ⟨x,hx,hd⟩ := hnear i hi
      have hjx : (j:ℝ) < x := by
        by_contra hn
        exact hout j hj (hS.out hx hx₀ ⟨le_of_not_gt hn,hj₀.le⟩)
      have hijR : (i:ℝ)+1 ≤ j := by exact_mod_cast (by omega : i+1 ≤ j)
      linarith only [hjx,hijR,(abs_le.mp hd).1]
    have hright i (hi : i∈J) j (hj : j∈J) (hi₀ : x₀ ≤ (i:ℝ)) (hij : i < j) : False := by
      obtain ⟨x,hx,hd⟩ := hnear j hj
      have hxi : x < (i:ℝ) := by
        by_contra hn
        exact hout i hi (hS.out hx₀ hx ⟨hi₀,le_of_not_gt hn⟩)
      have hijR : (i:ℝ)+1 ≤ j := by exact_mod_cast (by omega : i+1 ≤ j)
      linarith only [hxi,hijR,(abs_le.mp hd).2]
    have hL : (J.filter (fun (j : ℤ) => (j:ℝ)<x₀)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      obtain ⟨hi,hi₀⟩ := Finset.mem_filter.mp hi
      obtain ⟨hj,hj₀⟩ := Finset.mem_filter.mp hj
      rcases lt_trichotomy i j with hij | hij | hji
      · exact (hleft i hi j hj hj₀ hij).elim
      · exact hij
      · exact (hleft j hj i hi hi₀ hji).elim
    have hR : (J.filter (fun (j : ℤ) => ¬(j:ℝ)<x₀)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      obtain ⟨hi,hi₀⟩ := Finset.mem_filter.mp hi
      obtain ⟨hj,hj₀⟩ := Finset.mem_filter.mp hj
      rcases lt_trichotomy i j with hij | hij | hji
      · exact (hright i hi j hj (le_of_not_gt hi₀) hij).elim
      · exact hij
      · exact (hright j hj i hi (le_of_not_gt hj₀) hji).elim
    have hc := Finset.card_filter_add_card_filter_not (s:=J) (fun (j : ℤ) => (j:ℝ)<x₀)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hJ,Finset.card_empty]
    omega

#print axioms outside_interval_near_integer_card

private theorem finite_subset_open_interval
    (J : Finset ℝ) {S : Set ℝ} (hopen : IsOpen S) (hconn : S.OrdConnected)
    (hJS : ∀ x∈J, x∈S) :
    ∃ a b : ℝ, (∀ x∈J, x∈Ioo a b) ∧ Ioo a b ⊆ S := by
  classical
  by_cases hJ : J.Nonempty
  · let l := J.min' hJ
    let u := J.max' hJ
    have hl : l∈J := Finset.min'_mem J hJ
    have hu : u∈J := Finset.max'_mem J hJ
    obtain ⟨a₀,b₀,hl₀,hab₀⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds (hJS l hl))
    obtain ⟨a₁,b₁,hu₁,hab₁⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds (hJS u hu))
    let a := (a₀+l)/2
    let b := (u+b₁)/2
    have hal : a < l := by dsimp only [a]; linarith only [hl₀.1]
    have hub : u < b := by dsimp only [b]; linarith only [hu₁.2]
    have haS : a∈S := hab₀ ⟨by dsimp only [a]; linarith only [hl₀.1],hal.trans hl₀.2⟩
    have hbS : b∈S := hab₁ ⟨hu₁.1.trans hub,by dsimp only [b]; linarith only [hu₁.2]⟩
    refine ⟨a,b,?_,?_⟩
    · intro x hx
      exact ⟨hal.trans_le (Finset.min'_le J x hx),(Finset.le_max' J x hx).trans_lt hub⟩
    · intro x hx
      exact hconn.out haS hbS ⟨hx.1.le,hx.2.le⟩
  · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    refine ⟨0,0,?_,?_⟩
    · simp only [he,Finset.notMem_empty,IsEmpty.forall_iff,implies_true]
    · simp only [Ioo_self,empty_subset]

#print axioms finite_subset_open_interval

private theorem curvature_image_open_interval
    (f : ℝ → ℝ) {A B L : ℝ} (hL : 0 < L)
    (hf : ∀ x∈Ioo A B, ContDiffAt ℝ 3 f x)
    (hthree : ∀ x∈Ioo A B, L ≤ iteratedDeriv 3 f x) :
    let h := fun x => iteratedDeriv 2 f x/2
    IsOpen (h '' Ioo A B) ∧ (h '' Ioo A B).OrdConnected := by
  intro h
  have hc x (hx : x∈Ioo A B) : ContDiffAt ℝ 1 h x :=
    (contDiffAt_iteratedDeriv_finite (n:=1) (j:=2) (hf x hx)).div_const 2
  have hd x (hx : x∈Ioo A B) : HasDerivAt h (iteratedDeriv 3 f x/2) x := by
    have hh := (contDiffAt_iteratedDeriv_finite (n:=1) (j:=2) (hf x hx)).differentiableAt (by norm_num)
    simpa only [h,iteratedDeriv_succ] using hh.hasDerivAt.div_const 2
  constructor
  · apply isOpen_iff_mem_nhds.mpr
    intro v hv
    obtain ⟨x,hx,rfl⟩ := hv
    have hs := (hc x hx).hasStrictDerivAt' (hd x hx) (by norm_num)
    have hmap := hs.map_nhds_eq (ne_of_gt (div_pos (hL.trans_le (hthree x hx)) (by norm_num)))
    rw [←hmap]
    exact Filter.image_mem_map (isOpen_Ioo.mem_nhds hx)
  · exact isPreconnected_iff_ordConnected.mp (isPreconnected_Ioo.image h
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt))

#print axioms curvature_image_open_interval

private theorem triangular_fixed_shift_source_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
    (center block : ι → ℤ) (z : ι → ℝ) (H Bmul : ℕ) (s k : ℤ)
    (f : ℝ → ℝ) {A B L U F lam ε : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hU : 0 < U) (hF : 0 < F) (hlam : 0 < lam)
    (hk : 0 < k) (hkU : 6*U ≤ k) (hε : 0 ≤ ε)
    (hspan : ∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 5 f t)
    (hthree : ∀ t∈Ioo A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U)
    (hfour : ∀ t∈Ioo A B, -F ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hcenter : ∀ i∈S, (center i:ℝ)∈Ioo A B)
    (hz : ∀ i∈S, z i∈Ioo A B)
    (hround : ∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2)
    (hRS : R ⊆ S ×ˢ S)
    (hlevel : ∀ p∈R, iteratedDeriv 2 f (z p.2)/2-iteratedDeriv 2 f (z p.1)/2=(k:ℝ))
    (hnear : ∀ p∈R, ∃ e : ℤ,
      |iteratedDeriv 1 f (center p.2)-iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ ε) :
    let μ := L^3/(2*F*k)
    let C := max 1 (216*F*U^3/(lam*L^3))
    (R.card:ℝ) ≤ (3*(Bmul:ℝ)^2*(3+144*U^2/(lam*k*H)))*
      (3+(52+144*C)*((2*(k:ℝ)/L+1)*(ε+9*U/4+C*μ+μ^((1:ℝ)/3))+
        μ^(-(1:ℝ)/2))) := by
  classical
  intro μ C
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  let h := fun t => iteratedDeriv 2 f t/2
  let Ω := h '' Ioo A B
  let Ωk := Ω ∩ (fun t => t+(k:ℝ)) ⁻¹' Ω
  let V := R.image (fun p => h (z p.1))
  have himage := curvature_image_open_interval f hL
    (fun t ht => (hf t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1)
  have hopen : IsOpen Ωk := himage.1.inter (himage.1.preimage (continuous_id.add_const _))
  have hconn : Ωk.OrdConnected := himage.2.inter (himage.2.preimage_mono (fun _ _ he => add_le_add he le_rfl))
  have hVS v (hv : v∈V) : v∈Ωk := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    have hpp := Finset.mem_product.mp (hRS hp)
    refine ⟨⟨z p.1,hz _ hpp.1,rfl⟩,z p.2,hz _ hpp.2,?_⟩
    have he := hlevel p hp
    change h (z p.2)-h (z p.1)=(k:ℝ) at he
    change h (z p.2)=h (z p.1)+(k:ℝ)
    linarith only [he]
  obtain ⟨a,b,hV,hdom⟩ := finite_subset_open_interval V hopen hconn hVS
  have hparam p (hp : p∈R) : h (z p.1)∈Ioo a b := hV _ (Finset.mem_image_of_mem _ hp)
  let c := Function.invFunOn h (Ioo A B)
  let D := fun t => c (t+k)-c t
  let I := D '' Ioo a b
  let Rgood := R.filter (fun p => (center p.2:ℝ)-center p.1∈I)
  let Rbad := R.filter (fun p => ¬(center p.2:ℝ)-center p.1∈I)
  let J := Rbad.image (fun p => center p.2-center p.1)
  let K := 3*(Bmul:ℝ)^2*(3+144*U^2/(lam*k*H))
  let Q := (52+144*C)*((2*(k:ℝ)/L+1)*(ε+9*U/4+C*μ+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2))
  have hdata := triangular_resonance_curve_data f hL hU hF hlam hkr hf hthree hfour
    (fun t ht => hdom ht)
  have hgood : (Rgood.card:ℝ) ≤ K*(1+Q) :=
    triangular_interior_fixed_shift_source_count S Rgood center block z H Bmul s k f
      hH hL hU hF hlam hk hkU hε hspan hmul hf hthree hfour hcenter hz hround
      (fun p hp => hRS (Finset.mem_filter.mp hp).1)
      (fun p hp => hlevel p (Finset.mem_filter.mp hp).1)
      (fun p hp => hnear p (Finset.mem_filter.mp hp).1)
      (fun t ht => hdom ht) (fun p hp => hparam p (Finset.mem_filter.mp hp).1)
      (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hinverse := inverse_curvature_derivative f hL
    (fun t ht => (hf t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1)
  have hpoint p (hp : p∈R) : z p.2-z p.1∈I := by
    have hpp := Finset.mem_product.mp (hRS hp)
    refine ⟨h (z p.1),hparam p hp,?_⟩
    have he : h (z p.1)+(k:ℝ)=h (z p.2) := by
      have hh := hlevel p hp
      change h (z p.2)-h (z p.1)=(k:ℝ) at hh
      linarith only [hh]
    change c (h (z p.1)+k)-c (h (z p.1))=z p.2-z p.1
    have hcx : c (h (z p.1))=z p.1 := hinverse.1 _ (hz _ hpp.1)
    have hcy : c (h (z p.2))=z p.2 := hinverse.1 _ (hz _ hpp.2)
    rw [he,hcx,hcy]
  have hJ : J.card ≤ 2 := by
    apply outside_interval_near_integer_card J hdata.1
    · intro j hj
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
      simpa only [Int.cast_sub] using (Finset.mem_filter.mp hp).2
    · intro j hj
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
      have hpR := (Finset.mem_filter.mp hp).1
      have hpp := Finset.mem_product.mp (hRS hpR)
      refine ⟨z p.2-z p.1,hpoint p hpR,?_⟩
      simp only [Int.cast_sub]
      exact abs_le.mpr ⟨by linarith only [(abs_le.mp (hround _ hpp.1)).2,(abs_le.mp (hround _ hpp.2)).1],
        by linarith only [(abs_le.mp (hround _ hpp.1)).1,(abs_le.mp (hround _ hpp.2)).2]⟩
  have hbad : (Rbad.card:ℝ) ≤ K*2 := by
    have hb := rounded_shift_source_pair_count_of_displacements S Rbad center block z H Bmul s f J
      hH hL hU hlam hkU hspan hmul (fun t ht => (hf t ht).of_le (by norm_num))
      hthree (fun t ht => (hfour t ht).2) hcenter hz hround
      (fun p hp => hRS (Finset.mem_filter.mp hp).1)
      (fun p hp => hlevel p (Finset.mem_filter.mp hp).1)
      (fun p hp => Finset.mem_image_of_mem _ hp)
    exact hb.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hJ) (by positivity))
  have hc : (R.card:ℝ)=Rgood.card+Rbad.card := by
    have hcNat : Rgood.card+Rbad.card=R.card :=
      Finset.card_filter_add_card_filter_not (s:=R) (fun p => (center p.2:ℝ)-center p.1∈I)
    have hcReal := congrArg (fun n : ℕ => (n:ℝ)) hcNat
    simp only [Nat.cast_add] at hcReal
    exact hcReal.symm
  calc
    _ = (Rgood.card:ℝ)+Rbad.card := hc
    _ ≤ K*(1+Q)+K*2 := add_le_add hgood hbad
    _ = K*(3+Q) := by ring

#print axioms triangular_fixed_shift_source_count

private theorem displacement_curve_uniform_shift_majorant
    {L m C ε k K : ℝ} (hL : 0 < L) (hm : 0 < m) (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (hk : 1 ≤ k) (hkK : k ≤ K) :
    (2*k/L+1)*(ε+C*(m/k)+(m/k)^((1:ℝ)/3))+(m/k)^(-(1:ℝ)/2) ≤
      (2/L+1)*(K*ε+C*m+m^((1:ℝ)/3)*K^((2:ℝ)/3))+
        m^(-(1:ℝ)/2)*K^((1:ℝ)/2) := by
  have hkp : 0 < k := zero_lt_one.trans_le hk
  have hK : 0 < K := hkp.trans_le hkK
  have hwidth : 2*k/L+1 ≤ (2/L+1)*k := by
    calc
      _ ≤ 2*k/L+k := add_le_add le_rfl hk
      _ = _ := by ring
  have hcube : k*(m/k)^((1:ℝ)/3)=m^((1:ℝ)/3)*k^((2:ℝ)/3) := by
    rw [Real.div_rpow hm.le hkp.le,
      show ((2:ℝ)/3)=1-1/3 by ring,Real.rpow_sub hkp,Real.rpow_one]
    ring
  have hhalf : (m/k)^(-(1:ℝ)/2)=m^(-(1:ℝ)/2)*k^((1:ℝ)/2) := by
    rw [Real.div_rpow hm.le hkp.le]
    rw [show (-(1:ℝ)/2)= -((1:ℝ)/2) by ring,Real.rpow_neg hkp.le]
    simp only [div_inv_eq_mul]
  calc
    _ ≤ ((2/L+1)*k)*(ε+C*(m/k)+(m/k)^((1:ℝ)/3))+
        (m/k)^(-(1:ℝ)/2) :=
      add_le_add (mul_le_mul_of_nonneg_right hwidth (by positivity)) le_rfl
    _ = (2/L+1)*(k*ε+C*m+m^((1:ℝ)/3)*k^((2:ℝ)/3))+
        m^(-(1:ℝ)/2)*k^((1:ℝ)/2) := by
      rw [hhalf]
      have he : k*(ε+C*(m/k)+(m/k)^((1:ℝ)/3))=
          k*ε+C*m+m^((1:ℝ)/3)*k^((2:ℝ)/3) := by
        rw [mul_add,mul_add,hcube]
        field_simp
      rw [mul_assoc,he]
    _ ≤ _ := by gcongr

#print axioms displacement_curve_uniform_shift_majorant

private theorem triangular_all_shifts_source_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (R : Finset (ι × ι))
    (center block : ι → ℤ) (z : ι → ℝ) (H Bmul N : ℕ) (s : ℤ)
    (f : ℝ → ℝ) {A B L U F lam ε : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hU : 0 < U) (hF : 0 < F) (hlam : 0 < lam)
    (hUsmall : 6*U ≤ 1) (hε : 0 ≤ ε)
    (hspan : ∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 5 f t)
    (hthree : ∀ t∈Ioo A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U)
    (hfour : ∀ t∈Ioo A B, -F ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hcenter : ∀ i∈S, (center i:ℝ)∈Ioo A B)
    (hz : ∀ i∈S, z i∈Ioo A B)
    (hround : ∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2)
    (hRS : R ⊆ S ×ˢ S) (hsym : ∀ p∈R, p.swap∈R)
    (hshift : ∀ p∈R, ∃ k : ℤ,
      iteratedDeriv 2 f (z p.2)/2-iteratedDeriv 2 f (z p.1)/2=(k:ℝ) ∧ |(k:ℝ)| ≤ N)
    (hnear : ∀ p∈R, ∃ e : ℤ,
      |iteratedDeriv 1 f (center p.2)-iteratedDeriv 1 f (center p.1)-(e:ℝ)| ≤ ε) :
    let m := L^3/(2*F)
    let C := max 1 (216*F*U^3/(lam*L^3))
    let D := 144*U^2/(lam*H)
    let Q := 3+(52+144*C)*((2/L+1)*((N:ℝ)*(ε+9*U/4)+C*m+
      m^((1:ℝ)/3)*(N:ℝ)^((2:ℝ)/3))+m^(-(1:ℝ)/2)*(N:ℝ)^((1:ℝ)/2))
    (R.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card+
      6*(Bmul:ℝ)^2*Q*(3*(N:ℝ)+D*(harmonic N:ℝ)) := by
  classical
  intro m C D Q
  let h := fun x => iteratedDeriv 2 f x/2
  let Z := R.filter (fun p => h (z p.1)=h (z p.2))
  let Rp := R.filter (fun p => h (z p.1)<h (z p.2))
  have hRmem p (hp : p∈R) : p.1∈S ∧ p.2∈S := Finset.mem_product.mp (hRS hp)
  have hpmem p (hp : p∈Rp) : p∈R ∧ h (z p.1)<h (z p.2) := Finset.mem_filter.mp hp
  have hRsplit : R ⊆ Z ∪ (Rp ∪ Rp.image Prod.swap) := by
    intro p hp
    rcases lt_trichotomy (h (z p.1)) (h (z p.2)) with hh | hh | hh
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hh⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hh⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨p.swap,Finset.mem_filter.mpr ⟨hsym p hp,hh⟩,Prod.swap_swap p⟩
  have hsplit : R.card ≤ Z.card+2*Rp.card := by
    have hh := (Finset.card_le_card hRsplit).trans (Finset.card_union_le _ _)
    have hh' := Finset.card_union_le Rp (Rp.image Prod.swap)
    have he : (Rp.image Prod.swap).card=Rp.card := Finset.card_image_of_injective _ Prod.swap_injective
    omega
  have hmulLevel := bourgain_curvature_level_block_multiplicity S f z center block H Bmul s
    hH hL (fun t ht => (hf t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1)
    hz (fun i hi => by simpa only [abs_sub_comm] using hround i hi) hspan hmul
  have hZfiber i : (Z.filter (fun p => p.1=i)).card ≤ 4*Bmul := by
    have hsub : Z.filter (fun p => p.1=i) ⊆ {i} ×ˢ (S.filter (fun j => h (z j)=h (z i))) := by
      intro p hp
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hh⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr he,
        Finset.mem_filter.mpr ⟨(hRmem p hp).2,by rw [←he]; exact hh.symm⟩⟩
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ = (S.filter (fun j => h (z j)=h (z i))).card := by simp only [Finset.card_product,Finset.card_singleton,one_mul]
      _ ≤ _ := hmulLevel _
  have hZ : (Z.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card := by
    have he : (Z.card:ℝ)=∑ i∈S,((Z.filter (fun p => p.1=i)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise
        (fun (p : ι × ι) hp => (hRmem p (Finset.mem_filter.mp hp).1).1)
    rw [he]
    calc
      _ ≤ ∑ _i∈S,4*(Bmul:ℝ) := Finset.sum_le_sum (fun i _ => by exact_mod_cast hZfiber i)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hex (p : ι × ι) : ∃ d : ℕ, p∈Rp →
      0 < d ∧ h (z p.2)-h (z p.1)=(d:ℝ) ∧ d ≤ N := by
    by_cases hp : p∈Rp
    · obtain ⟨d,he,hd⟩ := hshift p (hpmem p hp).1
      change h (z p.2)-h (z p.1)=(d:ℝ) at he
      have hdr : 0 < (d:ℝ) := by linarith only [he,(hpmem p hp).2]
      have hdi : 0 < d := by exact_mod_cast hdr
      have hdcast : (d.toNat:ℝ)=(d:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hdi.le
      refine ⟨d.toNat,fun _ => ⟨by omega,by rw [hdcast]; exact he,?_⟩⟩
      have hh : (d.toNat:ℝ) ≤ N := by rw [hdcast]; exact (le_abs_self _).trans hd
      exact_mod_cast hh
    · exact ⟨0,fun hh => False.elim (hp hh)⟩
  choose shift hshiftNat using hex
  let J := Finset.Icc 1 N
  have hindex p (hp : p∈Rp) : shift p∈J :=
    Finset.mem_Icc.mpr ⟨(hshiftNat p hp).1,(hshiftNat p hp).2.2⟩
  have hm : 0 < m := by dsimp only [m]; positivity
  have hC : 1 ≤ C := le_max_left _ _
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hfiber n (hn : n∈J) :
      ((Rp.filter (fun p => shift p=n)).card:ℝ) ≤
        3*(Bmul:ℝ)^2*Q*(3+D/n) := by
    let E := Rp.filter (fun p => shift p=n)
    have hnmem := Finset.mem_Icc.mp hn
    have hnr : (1:ℝ) ≤ n := by exact_mod_cast hnmem.1
    have hnp : (0:ℝ) < n := zero_lt_one.trans_le hnr
    have hNK : (n:ℝ) ≤ N := by exact_mod_cast hnmem.2
    have hEmem p (hp : p∈E) : p∈Rp ∧ shift p=n := Finset.mem_filter.mp hp
    have hb := triangular_fixed_shift_source_count S E center block z H Bmul s (n:ℤ) f
      hH hL hU hF hlam (by exact_mod_cast hnmem.1)
      (by exact_mod_cast hUsmall.trans hnr) hε hspan hmul hf hthree hfour hcenter hz hround
      (fun p hp => hRS (hpmem p (hEmem p hp).1).1)
      (by
        intro p hp
        have he := (hshiftNat p (hEmem p hp).1).2.1
        rw [(hEmem p hp).2] at he
        simpa only [Int.cast_natCast] using he)
      (fun p hp => hnear p (hpmem p (hEmem p hp).1).1)
    have hμeq : L^3/(2*F*((n:ℤ):ℝ))=m/n := by
      simp only [Int.cast_natCast]
      dsimp only [m]
      ring
    have hDeq : 144*U^2/(lam*((n:ℤ):ℝ)*H)=D/n := by
      simp only [Int.cast_natCast]
      dsimp only [D]
      ring
    rw [hμeq,hDeq] at hb
    simp only [Int.cast_natCast] at hb
    have hmajor := displacement_curve_uniform_shift_majorant hL hm hCp.le
      (by positivity : 0 ≤ ε+9*U/4) hnr hNK
    have hinner : 3+(52+144*C)*((2*(n:ℝ)/L+1)*
        (ε+9*U/4+C*(m/n)+(m/n)^((1:ℝ)/3))+(m/n)^(-(1:ℝ)/2)) ≤ Q :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hmajor (by positivity))
    calc
      _ ≤ _ := hb
      _ ≤ (3*(Bmul:ℝ)^2*(3+D/n))*Q :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = _ := by ring
  have hsum : (∑ n∈J,(3+D/(n:ℝ))) ≤ 3*(N:ℝ)+D*(harmonic N:ℝ) := by
    have hh := sum_positive_displacement_weight_le_harmonic (η:=0) (N:=N) le_rfl
      (by positivity : 0 ≤ D/3)
    simp only [Real.rpow_zero,one_mul] at hh
    calc
      _ = 3*∑ n∈J,(1+(D/3)/(n:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ 3*((N:ℝ)+(D/3)*(harmonic N:ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hRp : (Rp.card:ℝ) ≤ 3*(Bmul:ℝ)^2*Q*(3*(N:ℝ)+D*(harmonic N:ℝ)) := by
    have hc : (Rp.card:ℝ)=∑ n∈J,((Rp.filter (fun p => shift p=n)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hindex
    calc
      _ = _ := hc
      _ ≤ ∑ n∈J,3*(Bmul:ℝ)^2*Q*(3+D/(n:ℝ)) := Finset.sum_le_sum hfiber
      _ = (3*(Bmul:ℝ)^2*Q)*∑ n∈J,(3+D/(n:ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  have hsplitR : (R.card:ℝ) ≤ (Z.card:ℝ)+2*(Rp.card:ℝ) := by exact_mod_cast hsplit
  calc
    _ ≤ _ := hsplitR
    _ ≤ 4*(Bmul:ℝ)*S.card+2*(3*(Bmul:ℝ)^2*Q*(3*(N:ℝ)+D*(harmonic N:ℝ))) :=
      add_le_add hZ (mul_le_mul_of_nonneg_left hRp (by norm_num))
    _ = _ := by ring

#print axioms triangular_all_shifts_source_count

private theorem four_coordinate_displacement_source_count
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (center block label inverse : ι → ℤ) (z : ι → ℝ) (q : ι → ℕ)
    (parity : ι → Fin 2) (H Bmul M Qden : ℕ) [NeZero M] (s : ℤ)
    (f : ℝ → ℝ) {A B L U F lam : ℝ}
    (hH : 0 < H) (hL : 0 < L) (hU : 0 < U) (hF : 0 < F) (hlam : 0 < lam)
    (hQ : 0 < Qden) (hUsmall : 6*U ≤ 1) (hthin : (Qden:ℝ)^2 < 6*(M:ℝ)^2)
    (hspan : ∀ i∈S, (H:ℤ) ≤ s+(H:ℤ)*block i-center i ∧
      s+(H:ℤ)*block i-center i ≤ 3*(H:ℤ))
    (hmul : ∀ j : ℤ, (S.filter (fun i => block i=j)).card ≤ Bmul)
    (hf : ∀ t∈Ioo A B, ContDiffAt ℝ 5 f t)
    (hthree : ∀ t∈Ioo A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U)
    (hfour : ∀ t∈Ioo A B, -F ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hcenter : ∀ i∈S, (center i:ℝ)∈Ioo A B)
    (hz : ∀ i∈S, z i∈Ioo A B)
    (hround : ∀ i∈S, |(center i:ℝ)-z i| ≤ 1/2)
    (hq : ∀ i∈S, 0 < q i ∧ q i ≤ Qden ∧ Qden ≤ 2*q i)
    (hinverse : ∀ i∈S, (q i:ℤ) ∣ label i*inverse i-1)
    (hlevel : ∀ i∈S, iteratedDeriv 2 f (z i)/2=(label i:ℝ)/q i) :
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
    let D₀ : ℝ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*
      Real.sqrt (U*(Qden:ℝ)^3)
    let ε : ℝ := 4*D₀/(Qden:ℝ)
    let rho := (12*U*Real.sqrt (U*(Qden:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
    let N := ⌈3*U*(rho+1)⌉₊
    let m := L^3/(2*F)
    let C := max 1 (216*F*U^3/(lam*L^3))
    let D := 144*U^2/(lam*H)
    let Bound := 3+(52+144*C)*((2/L+1)*((N:ℝ)*(ε+9*U/4)+C*m+
      m^((1:ℝ)/3)*(N:ℝ)^((2:ℝ)/3))+m^(-(1:ℝ)/2)*(N:ℝ)^((1:ℝ)/2))
    (R.card:ℝ) ≤ 4*(Bmul:ℝ)*S.card+
      6*(Bmul:ℝ)^2*Bound*(3*(N:ℝ)+D*(harmonic N:ℝ)) := by
  classical
  intro mu ell b tau coeff Y window R D₀ ε rho N m C D Bound
  have hQr : (0:ℝ) < Qden := by exact_mod_cast hQ
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hRmem p (hp : p∈R) : p.1∈S ∧ p.2∈S :=
    Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  have hRnear p (hp : p∈R) : ∀ j, |Y p.1 j-Y p.2 j| ≤ 2*window j :=
    (Finset.mem_filter.mp hp).2
  have hRsym p (hp : p∈R) : p.swap∈R := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(hRmem p hp).2,(hRmem p hp).1⟩,?_⟩
    intro j
    change |Y p.2 j-Y p.1 j| ≤ 2*window j
    rw [abs_sub_comm]
    exact hRnear p hp j
  have hshift p (hp : p∈R) : ∃ k : ℤ,
      iteratedDeriv 2 f (z p.2)/2-iteratedDeriv 2 f (z p.1)/2=(k:ℝ) ∧ |(k:ℝ)| ≤ N := by
    have hi := (hRmem p hp).1
    have hj := (hRmem p hp).2
    have hh := source_four_coordinate_integer_shift_bound f M (q p.1) (q p.2) Qden
      (label p.1) (label p.2) (inverse p.1) (inverse p.2) (center p.1) (center p.2)
      (hq _ hi).1 (hq _ hj).1 (hq _ hi).2.1 (hq _ hj).2.1 hthin hlam hU
      (fun t ht => (hf t ht).of_le (by norm_num))
      (fun t ht => ⟨hL.trans_le (hthree t ht).1,(hthree t ht).2⟩)
      (fun t ht => by
        have hb := (hfour t ht).2
        rw [abs_of_neg (by linarith only [hb,hlam])]
        linarith only [hb])
      (hz _ hi) (hz _ hj) (hcenter _ hi) (hcenter _ hj)
      (by simpa only [abs_sub_comm] using hround _ hi)
      (by simpa only [abs_sub_comm] using hround _ hj)
      (hinverse _ hi) (hinverse _ hj) (hlevel _ hi) (hlevel _ hj)
      (by
        have hb := hRnear p hp 1
        change _ ≤ 2*(1/(12*(M:ℝ)^2)) at hb
        convert hb using 1
        ring)
      (by
        have hb := hRnear p hp 2
        change _ ≤ 2*((1/(M:ℝ)^2)/12) at hb
        convert hb using 1
        ring)
    obtain ⟨_,k,hk,hb⟩ := hh
    exact ⟨k,hk,hb.trans (Nat.le_ceil _)⟩
  have hnear p (hp : p∈R) : ∃ e : ℤ, |ell p.2-ell p.1-(e:ℝ)| ≤ ε := by
    have hi := (hRmem p hp).1
    have hj := (hRmem p hp).2
    have hmui : 0 < mu p.1 := by
      dsimp only [mu]
      positivity [hL.trans_le (hthree _ (hcenter _ hi)).1]
    have hmuj : 0 < mu p.2 := by
      dsimp only [mu]
      positivity [hL.trans_le (hthree _ (hcenter _ hj)).1]
    have hmuiU : mu p.1 ≤ U := by
      dsimp only [mu]
      linarith only [(hthree _ (hcenter _ hi)).2]
    obtain ⟨_,k,e,_hk,he⟩ := actual_source_triangular_derivative_resonance M (q p.1) (q p.2) Qden
      (label p.1) (label p.2) (inverse p.1) (inverse p.2)
      (hq _ hi).1 (hq _ hj).1 (hq _ hi).2.1 (hq _ hj).2.1 hthin
      (hinverse _ hi) (hinverse _ hj) hmui hmuj hmuiU (parity p.1) (parity p.2)
      (hRnear p hp)
    have hqr : (0:ℝ) < q p.1 := by exact_mod_cast (hq _ hi).1
    have hQq : (Qden:ℝ) ≤ 2*(q p.1:ℝ) := by exact_mod_cast (hq _ hi).2.2
    refine ⟨e,he.trans ?_⟩
    change 2*D₀/(q p.1:ℝ) ≤ 4*D₀/Qden
    apply (div_le_div_iff₀ hqr hQr).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hQq hD₀]
  exact triangular_all_shifts_source_count S R center block z H Bmul N s f
    hH hL hU hF hlam hUsmall hε hspan hmul hf hthree hfour hcenter hz hround
    (fun _ hp => (Finset.mem_filter.mp hp).1) hRsym hshift hnear

#print axioms four_coordinate_displacement_source_count

private theorem model_displacement_derivative_data {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ > (0:ℝ), ∀ (F : ℝ → ℝ) (T P : ℝ), 0 < T → 0 < P →
      Expdb.IsApproximateModelPhaseFunction F σ 3 δ →
      let f := fun x => T*F (x/P)
      (∀ x∈Ioo P (2*P), ContDiffAt ℝ 5 f x) ∧
      (∀ x∈Ioo P (2*P),
        modelPhaseJetLower σ 2*T/P^3 ≤ iteratedDeriv 3 f x ∧
        iteratedDeriv 3 f x ≤ (modelPhaseJetCoefficient σ 2+1)*T/P^3) ∧
      (∀ x∈Ioo P (2*P),
        -((modelPhaseJetCoefficient σ 3+1)*T/P^4) ≤ iteratedDeriv 4 f x ∧
        iteratedDeriv 4 f x ≤ -(modelPhaseJetLower σ 3*T/P^4)) ∧
      (∀ x∈Ioo P (2*P), |iteratedDeriv 2 f x/2| ≤
        (modelPhaseJetCoefficient σ 1+1)*T/P^2/2) := by
  let δ := min 1 (min (modelPhaseJetLower σ 2) (modelPhaseJetLower σ 3))
  have hδ : 0 < δ := lt_min (by norm_num)
    (lt_min (modelPhaseJetLower_pos hσ 2) (modelPhaseJetLower_pos hσ 3))
  refine ⟨δ,hδ,?_⟩
  intro F T P hT hP hF f
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
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ min (modelPhaseJetLower σ 2) 1 :=
    le_min ((min_le_right _ _).trans (min_le_left _ _)) hδ1
  have hδ3 : δ ≤ min (modelPhaseJetLower σ 3) 1 :=
    le_min ((min_le_right _ _).trans (min_le_right _ _)) hδ1
  have hsign2 : modelPhaseJetSign σ 2=1 := by
    have he : (descPochhammer ℝ 2).eval (-σ)=σ*(σ+1) := by
      simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,
        Finset.prod_range_zero,Nat.cast_zero,Nat.cast_one]
      ring
    unfold modelPhaseJetSign
    rw [he,if_pos (by positivity)]
  have hsign3 : modelPhaseJetSign σ 3= -1 := by
    have he : (descPochhammer ℝ 3).eval (-σ)= -(σ*(σ+1)*(σ+2)) := by
      simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,
        Finset.prod_range_zero,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      ring
    unfold modelPhaseJetSign
    have hh : 0 < σ*(σ+1)*(σ+2) := by positivity
    rw [he,if_neg (by linarith only [hh])]
  refine ⟨fun x hx => (hfd x hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 5),?_,?_,?_⟩
  · intro x hx
    have hh := approximateModelPhase_signedJet_bounds hσ hF (hpoint x hx) 2 (by norm_num) hδ2
    rw [hsign2,one_mul] at hh
    rw [hd x hx 3]
    constructor
    · convert mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ T/P^3 by positivity) using 1; ring
    · convert mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ T/P^3 by positivity) using 1; ring
  · intro x hx
    have hh := approximateModelPhase_signedJet_bounds hσ hF (hpoint x hx) 3 le_rfl hδ3
    rw [hsign3,neg_one_mul] at hh
    change modelPhaseJetLower σ 3 ≤ -iteratedDeriv 4 F (x/P) ∧
      -iteratedDeriv 4 F (x/P) ≤ modelPhaseJetCoefficient σ 3+1 at hh
    rw [hd x hx 4]
    have hlo := mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ T/P^4 by positivity)
    have hhi := mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ T/P^4 by positivity)
    constructor
    · convert neg_le_neg hhi using 1 <;> ring
    · convert neg_le_neg hlo using 1 <;> ring
  · intro x hx
    have hh := approximateModelPhase_iteratedDeriv_error hF (hpoint x hx) 1 (by norm_num)
    have hr := iteratedDeriv_modelPhase_abs_le hσ.le (hpoint x hx) 1
    have hb : |iteratedDeriv 2 F (x/P)| ≤ modelPhaseJetCoefficient σ 1+1 := by
      have he := abs_add_le (iteratedDeriv 2 F (x/P)-iteratedDeriv 1 (Expdb.modelPhase σ) (x/P))
        (iteratedDeriv 1 (Expdb.modelPhase σ) (x/P))
      rw [sub_add_cancel] at he
      linarith only [he,hh,hr,hδ1]
    rw [hd x hx 2,abs_div,abs_mul,abs_of_pos (by positivity : 0<T/P^2)]
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right
      (by convert mul_le_mul_of_nonneg_left hb (show 0 ≤ T/P^2 by positivity) using 1; ring)
      (by norm_num)

#print axioms model_displacement_derivative_data

private theorem raw_displacement_window_scales
    {U M Q lam : ℝ} (hU : 0 ≤ U) (hM : 1 ≤ M) (hQ : 0 < Q)
    (hQM : Q ≤ 4*M) (hlam : 0 < lam) :
    let D₀ := (Real.sqrt M/(9*M)+Real.sqrt M/(12*M^2))*Real.sqrt (U*Q^3)
    let rho := (12*U*Real.sqrt (U*Q^3)/lam)*(Real.sqrt M/(6*M^2))
    4*D₀/Q ≤ 4*Real.sqrt U ∧ rho ≤ 16*U*Real.sqrt U/lam := by
  intro D₀ rho
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMp
  have hrootQ : Real.sqrt Q ≤ 2*Real.sqrt M := by
    have hh := Real.sqrt_le_sqrt hQM
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)] at hh
    norm_num at hh
    exact hh
  have hroot : Real.sqrt (U*Q^3) ≤ 2*Q*Real.sqrt U*Real.sqrt M := by
    have he : Real.sqrt (U*Q^3)=Q*Real.sqrt U*Real.sqrt Q := by
      rw [show U*Q^3=Q^2*(U*Q) by ring,Real.sqrt_mul (sq_nonneg Q),
        Real.sqrt_sq_eq_abs,abs_of_pos hQ,Real.sqrt_mul hU]
      ring
    rw [he]
    calc
      _ ≤ (Q*Real.sqrt U)*(2*Real.sqrt M) :=
        mul_le_mul_of_nonneg_left hrootQ (by positivity)
      _ = _ := by ring
  have hcoeff : (Real.sqrt M/(9*M)+Real.sqrt M/(12*M^2))*Real.sqrt M=
      1/9+1/(12*M) := by
    calc
      _ = (Real.sqrt M*Real.sqrt M)*(1/(9*M)+1/(12*M^2)) := by ring
      _ = M*(1/(9*M)+1/(12*M^2)) := by rw [Real.mul_self_sqrt hMp.le]
      _ = _ := by field_simp
  have hsmall : 8*(1/9+1/(12*M)) ≤ (4:ℝ) := by
    have hh : 1/(12*M) ≤ (1:ℝ)/12 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hM])
    linarith only [hh]
  constructor
  · calc
      4*D₀/Q ≤ 4*((Real.sqrt M/(9*M)+Real.sqrt M/(12*M^2))*
          (2*Q*Real.sqrt U*Real.sqrt M))/Q := by
        dsimp only [D₀]
        gcongr
      _ = Real.sqrt U*(8*((Real.sqrt M/(9*M)+Real.sqrt M/(12*M^2))*Real.sqrt M)) := by
        field_simp
        ring
      _ = Real.sqrt U*(8*(1/9+1/(12*M))) := by rw [hcoeff]
      _ ≤ Real.sqrt U*4 := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg U)
      _ = _ := by ring
  · calc
      rho ≤ (12*U*(2*Q*Real.sqrt U*Real.sqrt M)/lam)*(Real.sqrt M/(6*M^2)) := by
        dsimp only [rho]
        gcongr
      _ = (4*U*Q*Real.sqrt U/(lam*M^2))*(Real.sqrt M*Real.sqrt M) := by ring
      _ = (4*U*Q*Real.sqrt U/(lam*M^2))*M := by rw [Real.mul_self_sqrt hMp.le]
      _ = (4*U*Real.sqrt U/lam)*(Q/M) := by field_simp
      _ ≤ (4*U*Real.sqrt U/lam)*4 :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hMp).mpr hQM) (by positivity)
      _ = _ := by ring

#print axioms raw_displacement_window_scales

private theorem displacement_block_scale
    {U : ℝ} (hU : 0 < U) (hsmall : U ≤ 1/3600) :
    let H := ⌊1/(10*Real.sqrt U)⌋₊
    0 < H ∧ 1/12 ≤ (H:ℝ)*Real.sqrt U ∧ (H:ℝ)*Real.sqrt U ≤ 1/10 ∧
      1/144 ≤ U*(H:ℝ)^2 ∧ U*(H:ℝ)^2 ≤ 1/100 ∧
    ∀ Q : ℕ, 1 ≤ Q →
      let M := ⌈63*U*(Q:ℝ)*(H:ℝ)^2⌉₊+1
      (7/16:ℝ)*Q ≤ M ∧ (M:ℝ) ≤ 3*Q ∧ (Q:ℝ)^2 < 6*(M:ℝ)^2 := by
  intro H
  have hs : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU
  have hsq := Real.sq_sqrt hU.le
  have hroot : Real.sqrt U ≤ (1:ℝ)/60 := by nlinarith only [hsq,hsmall,hs.le]
  have he : (1/(10*Real.sqrt U))*Real.sqrt U=(1:ℝ)/10 := by field_simp
  have hlo : 1/12 ≤ (H:ℝ)*Real.sqrt U := by
    have hh := mul_le_mul_of_nonneg_right (Nat.sub_one_lt_floor (1/(10*Real.sqrt U))).le hs.le
    change (1/(10*Real.sqrt U)-1)*Real.sqrt U ≤ (H:ℝ)*Real.sqrt U at hh
    rw [sub_mul,one_mul,he] at hh
    linarith only [hh,hroot]
  have hhi : (H:ℝ)*Real.sqrt U ≤ 1/10 := by
    have hh := mul_le_mul_of_nonneg_right
      (Nat.floor_le (by positivity : 0 ≤ 1/(10*Real.sqrt U))) hs.le
    exact hh.trans_eq he
  have hH : 0 < H := by
    have hh : 0 < (H:ℝ) := by
      by_contra hn
      have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hs.le
      linarith only [hlo,hh]
    exact_mod_cast hh
  have hsquare : ((H:ℝ)*Real.sqrt U)^2=U*(H:ℝ)^2 := by rw [mul_pow,hsq]; ring
  have hlower : 1/144 ≤ U*(H:ℝ)^2 := by
    rw [←hsquare]
    nlinarith only [hlo]
  have hupper : U*(H:ℝ)^2 ≤ 1/100 := by
    rw [←hsquare]
    nlinarith only [hhi,hlo]
  refine ⟨hH,hlo,hhi,hlower,hupper,?_⟩
  intro Q hQ M
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0:ℝ) < Q := zero_lt_one.trans_le hQr
  have hceil := Nat.le_ceil (63*U*(Q:ℝ)*(H:ℝ)^2)
  have hceil' := Nat.ceil_lt_add_one (by positivity : 0 ≤ 63*U*(Q:ℝ)*(H:ℝ)^2)
  have hMcast : (M:ℝ)=(⌈63*U*(Q:ℝ)*(H:ℝ)^2⌉₊:ℝ)+1 := by
    dsimp only [M]
    push_cast
    rfl
  have hMlo : (7/16:ℝ)*Q ≤ M := by
    have hh := mul_le_mul_of_nonneg_right hlower hQp.le
    linarith only [hceil,hMcast,hh]
  have hMhi : (M:ℝ) ≤ 3*Q := by
    have hh := mul_le_mul_of_nonneg_right hupper hQp.le
    linarith only [hceil',hMcast,hh,hQr]
  refine ⟨hMlo,hMhi,?_⟩
  have hMpos : (0:ℝ) < M := (by positivity : 0 < (7/16:ℝ)*Q).trans_le hMlo
  have hsquare' := mul_le_mul hMlo hMlo (by positivity) hMpos.le
  nlinarith only [hsquare',sq_pos_of_pos hQp]

#print axioms displacement_block_scale

-- Prototype copies of three already-proved private source-consumer lemmas.
-- Production integration reuses the originals, without new analytic inputs.
open scoped FourierTransform

private theorem bourgain_integer_source_translation
    (f : ℝ → ℝ) (m : ℤ) (N H : ℕ) :
    (∑ n∈Finset.Ioc (m+N) (m+N+H),(𝐞 (f n):ℂ))=
    ∑ n∈Finset.Ioc (N:ℤ) ((N:ℤ)+H),(𝐞 (f ((m:ℝ)+n)):ℂ) := by
  symm
  apply Finset.sum_bij (fun n _ => m+n)
  · intro n hn
    obtain ⟨hn1,hn2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro n _ n' _ he
    omega
  · intro n hn
    refine ⟨n-m,?_,by omega⟩
    obtain ⟨hn1,hn2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro n _
    simp only [Int.cast_add]

#print axioms bourgain_integer_source_translation

private theorem bourgain_prescribed_source_error_le
    {N W : ℕ} {mu L : ℝ} (hN : 0 < N) (hNW : N ≤ W) (hW : W ≤ 3*N)
    (hL : 0 < L) (hmu : L/6 ≤ mu) :
    Real.sqrt W*Real.log (2*(W:ℝ))+1/(mu*(W:ℝ)^2) ≤
      Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2) := by
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hNW' : (N:ℝ) ≤ W := by exact_mod_cast hNW
  have hW' : (W:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hW
  have hWp : (0:ℝ) < W := hNr.trans_le hNW'
  have hmul : 0 < mu := by linarith only [hL,hmu]
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (2*(W:ℝ)) := Real.log_nonneg (by linarith only [hN1,hNW'])
  have hlogs : Real.log (2*(W:ℝ)) ≤ Real.log (6*(N:ℝ)) :=
    Real.log_le_log (by positivity) (by linarith only [hW'])
  apply add_le_add (mul_le_mul (Real.sqrt_le_sqrt hW') hlogs hlog
    (Real.sqrt_nonneg _))
  have hden : (L/6)*(N:ℝ)^2 ≤ mu*(W:ℝ)^2 :=
    mul_le_mul hmu (pow_le_pow_left₀ hNr.le hNW' 2) (sq_nonneg _) hmul.le
  calc
    _ ≤ 1/((L/6)*(N:ℝ)^2) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by field_simp

#print axioms bourgain_prescribed_source_error_le

private theorem bourgain_frozen_physical_dual_scales
    {L U N Q μ q n : ℝ} (hL : 0<L) (hU : 0<U) (hN : 0<N) (hQ : 0<Q)
    (hμ : L/6≤μ ∧ μ≤U) (hq : Q/2≤q ∧ q≤Q) (hn : N≤n ∧ n≤3*N)
    (hdual : 12≤L*Q*N^2) (hfrozen : 384≤L^2*Q^3*N^3) :
    let H₀ := L*Q*N^2/12
    let V := 756*U/L
    let W := 1+32/(L*Q^2*N)
    let K := -2*μ*(Real.sqrt (2/(3*μ*q)))^3
    1≤H₀ ∧ H₀≤μ*q*n^2 ∧
      7*(μ*q*n^2)≤63*U*Q*N^2 ∧
      7*(μ*q*n^2)≤V*H₀ ∧
      |K|≤H₀*Real.sqrt H₀ ∧ |K|/Real.sqrt H₀≤W := by
  intro H₀ V W K
  have hμp : 0<μ := (by positivity : 0<L/6).trans_le hμ.1
  have hqp : 0<q := (by positivity : 0<Q/2).trans_le hq.1
  have hnp : 0<n := hN.trans_le hn.1
  have hH₀ : 1≤H₀ := by dsimp only [H₀]; linarith only [hdual]
  have hH₀p : 0<H₀ := by linarith only [hH₀]
  have hsH : 0<Real.sqrt H₀ := Real.sqrt_pos.mpr hH₀p
  have hlo : H₀≤μ*q*n^2 := by
    calc
      H₀ = (L/6)*(Q/2)*N^2 := by dsimp only [H₀]; ring
      _ ≤ μ*q*n^2 :=
        mul_le_mul (mul_le_mul hμ.1 hq.1 (by positivity) hμp.le)
          (pow_le_pow_left₀ hN.le hn.1 2) (sq_nonneg _) (by positivity)
  have hhi : 7*(μ*q*n^2)≤63*U*Q*N^2 := by
    calc
      _ ≤ 7*(U*Q*(3*N)^2) := by gcongr <;> linarith only [hμ.2,hq.2,hn.2]
      _ = _ := by ring
  have hVeq : V*H₀=63*U*Q*N^2 := by
    dsimp only [V,H₀]
    field_simp
    ring
  refine ⟨hH₀,hlo,hhi,by rw [hVeq]; exact hhi,?_,?_⟩
  all_goals
    have hroot : (Real.sqrt (2/(3*μ*q)))^2*(3*μ*q)=2 :=
      (eq_div_iff (by positivity : 3*μ*q≠0)).mp (Real.sq_sqrt (by positivity))
    have he : K^2*(27*μ*q^3)=32 := by
      calc
        _ = 4*((Real.sqrt (2/(3*μ*q)))^2*(3*μ*q))^3 := by dsimp only [K]; ring
        _ = _ := by rw [hroot]; norm_num
    let D := (9/16)*L*Q^3
    have hDp : 0<D := by dsimp only [D]; positivity
    have hDle : D≤27*μ*q^3 := by
      have hh := mul_le_mul hμ.1 (pow_le_pow_left₀ (by positivity) hq.1 3)
        (by positivity : 0≤(Q/2)^3) hμp.le
      dsimp only [D]
      nlinarith only [hh]
    have hKD : K^2*D≤32 :=
      (mul_le_mul_of_nonneg_left hDle (sq_nonneg K)).trans_eq he
  · have hbig : 32≤(H₀*Real.sqrt H₀)^2*D := by
      have hx := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤384) hfrozen 2
      have heq : (H₀*Real.sqrt H₀)^2*D=(L^2*Q^3*N^3)^2/3072 := by
        rw [mul_pow,Real.sq_sqrt hH₀p.le]
        dsimp only [H₀,D]
        ring
      rw [heq]
      nlinarith only [hx]
    have hsq : K^2≤(H₀*Real.sqrt H₀)^2 :=
      (mul_le_mul_iff_left₀ hDp).mp (by nlinarith only [hKD,hbig])
    have hpos : 0≤H₀*Real.sqrt H₀ := by positivity
    nlinarith only [hsq,abs_nonneg K,sq_abs K,hpos]
  · let W₀ := 32/(L*Q^2*N)
    have hW₀ : 0<W₀ := by dsimp only [W₀]; positivity
    have heq : (W₀*Real.sqrt H₀)^2*D=48 := by
      rw [mul_pow,Real.sq_sqrt hH₀p.le]
      dsimp only [W₀,H₀,D]
      field_simp
      ring
    have hsq : K^2≤(W₀*Real.sqrt H₀)^2 :=
      (mul_le_mul_iff_left₀ hDp).mp (by nlinarith only [hKD,heq])
    have hpos : 0≤W₀*Real.sqrt H₀ := by positivity
    have hk : |K|≤W₀*Real.sqrt H₀ := by
      nlinarith only [hsq,abs_nonneg K,sq_abs K,hpos]
    have hh := (div_le_iff₀ hsH).mpr hk
    change |K|/Real.sqrt H₀≤1+W₀
    linarith only [hh]

#print axioms bourgain_frozen_physical_dual_scales

private theorem bourgain_curvature_level_difference
    (f : ℝ → ℝ) {A B U x y : ℝ}
    (hf : ∀ z∈Icc A B, ContDiffAt ℝ 4 f z)
    (hthree : ∀ z∈Icc A B, 0 ≤ iteratedDeriv 3 f z ∧ iteratedDeriv 3 f z ≤ 6*U)
    (hx : x∈Icc A B) (hy : y∈Icc A B) :
    |iteratedDeriv 2 f x/2-iteratedDeriv 2 f y/2| ≤ 3*U*|x-y| := by
  have hd z (hz : z∈Icc A B) :
      HasDerivWithinAt (fun z => iteratedDeriv 2 f z/2)
        (iteratedDeriv 3 f z/2) (Icc A B) z := by
    have hh := contDiffAt_iteratedDeriv_finite (n:=2) (j:=2) (hf z hz)
    simpa only [iteratedDeriv_succ] using
      ((hh.differentiableAt (by norm_num)).hasDerivAt.div_const 2).hasDerivWithinAt
  have hb := (convex_Icc A B).norm_image_sub_le_of_norm_hasDerivWithin_le (C:=3*U) hd
    (by
      intro z hz
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hthree z hz).1 (by norm_num))]
      linarith only [(hthree z hz).2]) hx hy
  simpa only [Real.norm_eq_abs,abs_sub_comm y x,
    abs_sub_comm (iteratedDeriv 2 f y/2) (iteratedDeriv 2 f x/2)] using hb

#print axioms bourgain_curvature_level_difference

private theorem fourfold_source_majorant {C X Y E : ℝ}
    (hC : 0 ≤ C) (hE : 0 ≤ E) :
    C*(X*(4*Y)+E) ≤ (4*C)*(X*Y+E) := by
  nlinarith only [mul_nonneg hC hE]

private theorem displacement_prescribed_source_error
    {N W Q q : ℕ} {L mu : ℝ}
    (hN : 0 < N) (hQ : 0 < Q) (hq : 0 < q) (hL : 0 < L)
    (hWlo : N ≤ W) (hWhi : W ≤ 3*N) (hmu : L/6 ≤ mu)
    (hqlo : (Q:ℝ)/2 ≤ q) :
    Real.sqrt W*Real.log (2*(W:ℝ))+1/(mu*(W:ℝ)^2)+
      1/(Real.sqrt (mu*(W:ℝ))*Real.sqrt q) ≤
    Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
      Real.sqrt (12/(L*(N:ℝ)*Q)) := by
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hmup : 0 < mu := by linarith only [hmu,hL]
  have hWr : (N:ℝ) ≤ W := Nat.cast_le.mpr hWlo
  have hWi : (0:ℝ) < W := hNr.trans_le hWr
  have hqi : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have herr := bourgain_prescribed_source_error_le hN hWlo hWhi hL hmu
  have hprod : L*(N:ℝ)*Q/12 ≤ mu*(W:ℝ)*q := by
    have hh := mul_le_mul (mul_le_mul hmu hWr hNr.le hmup.le)
      hqlo (by positivity : 0 ≤ (Q:ℝ)/2) (by positivity : 0 ≤ mu*(W:ℝ))
    nlinarith only [hh]
  have hcap : 1/(Real.sqrt (mu*(W:ℝ))*Real.sqrt q) ≤
      Real.sqrt (12/(L*(N:ℝ)*Q)) := by
    rw [←Real.sqrt_mul (by positivity : 0 ≤ mu*(W:ℝ)),one_div,←Real.sqrt_inv]
    have hh := one_div_le_one_div_of_le (by positivity : 0 < L*(N:ℝ)*Q/12) hprod
    apply Real.sqrt_le_sqrt
    convert hh using 1
    · simp only [one_div]
    · field_simp
  linarith only [herr,hcap]

private theorem displacement_empty_source_bound (C Loss Pair Err Z : ℝ) (hZ : Z=0) :
    0 ≤ (4*C)*(Loss*(2*Z)^10*Pair+(Z*Err)^12) := by
  rw [hZ]
  norm_num

private theorem exists_displacement_frozen_physical_source
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι)
      (f : ℝ → ℝ) (r : ι → ℚ) (z : ι → ℝ) (m k : ι → ℤ)
      (H : ι → ℕ) (N Q Bmul : ℕ) (s : ℤ) (A B L F U lam : ℝ),
      0 < N → 0 < Q → 0 < L → 0 < F → 0 < U → 0 < lam → 6*U ≤ 1 →
      F*(6*(N:ℝ)+1)^4 ≤ 1 → (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 →
      (∀ x∈Icc A B, ContDiffAt ℝ 5 f x) →
      (∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U) →
      (∀ x∈Icc A B, -F ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ -lam) →
      (∀ i∈S, z i∈Ioo A B) →
      (∀ i∈S, Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B) →
      (∀ i∈S, |z i-m i| ≤ 1/2) →
      (∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧ s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ)) →
      (∀ n : ℤ, (S.filter (fun i => k i=n)).card ≤ Bmul) →
      (∀ i∈S, H i ≤ N) →
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N) →
      (∀ i∈S, iteratedDeriv 2 f (z i)/2=(r i:ℝ)) →
      12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
      let Z := (S.card:ℝ)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let Wloss := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let D₀ := (Real.sqrt M/(9*(M:ℝ))+Real.sqrt M/(12*(M:ℝ)^2))*Real.sqrt (U*(Q:ℝ)^3)
      let η : ℝ := 4*D₀/(Q:ℝ)
      let rho := (12*U*Real.sqrt (U*(Q:ℝ)^3)/lam)*(Real.sqrt M/(6*(M:ℝ)^2))
      let K := ⌈3*U*(rho+1)⌉₊
      let mu0 := L^3/(2*F)
      let Cratio := max 1 (216*F*U^3/(lam*L^3))
      let Dweight := 144*U^2/(lam*N)
      let Count := 3+(52+144*Cratio)*((2/L+1)*((K:ℝ)*(η+9*U/4)+Cratio*mu0+
        mu0^((1:ℝ)/3)*(K:ℝ)^((2:ℝ)/3))+mu0^(-(1:ℝ)/2)*(K:ℝ)^((1:ℝ)/2))
      let Pair := 4*(Bmul:ℝ)*Z+6*(Bmul:ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))
      let Loss := (5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
        Real.sqrt (12/(L*(N:ℝ)*Q))
      (Q:ℝ)^2 < 6*(M:ℝ)^2 →
      (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*(Loss*(2*Z)^10*Pair+(Z*Err)^12) := by
  classical
  obtain ⟨C,hC,hsource⟩ := exists_bourgain_C4_frozen_source_second_spacing_reduction hε
  refine ⟨4*C,by positivity,?_⟩
  intro ι instι S f r z m k H N Q Bmul s A B L F U lam
    hN hQ hL hF hU hlam hUsmall hfourSmall hquadSmall hf hthree hfour
    hz hbuffer hround hspan hmul hH hq hlevel hdual hfrozen
    Z M V Wloss d D₀ η rho K mu0 Cratio Dweight Count Pair Loss Err hthin
  have hf₄ x (hx : x∈Icc A B) : ContDiffAt ℝ 4 f x := (hf x hx).of_le (by norm_num)
  have hfourAbs x (hx : x∈Icc A B) : lam ≤ |iteratedDeriv 4 f x| ∧ |iteratedDeriv 4 f x| ≤ F := by
    have hh := hfour x hx
    rw [abs_of_neg (by linarith only [hh.2,hlam])]
    constructor <;> linarith only [hh.1,hh.2]
  let H₀ := L*(Q:ℝ)*(N:ℝ)^2/12
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hcard : (S.card:ℝ) ≤ Z := le_rfl
  let W := fun i => (s+(N:ℤ)*k i-m i).toNat
  let mu := fun i => iteratedDeriv 3 f (m i)/6
  have hW i (hi : i∈S) : N ≤ W i ∧ W i ≤ 3*N ∧ m i+(W i:ℤ)=s+(N:ℤ)*k i := by
    have hh := hspan i hi
    dsimp only [W]
    constructor
    · omega
    · constructor <;> omega
  have hWp i (hi : i∈S) : 1 ≤ W i := (Nat.succ_le_iff.mpr hN).trans (hW i hi).1
  have hWr i (hi : i∈S) : (N:ℝ) ≤ W i ∧ (W i:ℝ) ≤ 3*(N:ℝ) := by
    constructor <;> exact_mod_cast (by first | exact (hW i hi).1 | exact (hW i hi).2.1)
  have hm i (hi : i∈S) : (m i:ℝ)∈Ioo A B := by
    have hrad : 0 < 6*(N:ℝ)+1 := by positivity
    have hlo := (hbuffer i hi (left_mem_Icc.mpr (by linarith only [hrad]))).1
    have hhi := (hbuffer i hi (right_mem_Icc.mpr (by linarith only [hrad]))).2
    constructor <;> linarith only [hlo,hhi,hrad]
  have hmu i (hi : i∈S) : 0 < mu i ∧ L/6 ≤ mu i ∧ mu i ≤ U := by
    have hh := hthree (m i) ⟨(hm i hi).1.le,(hm i hi).2.le⟩
    dsimp only [mu]
    constructor
    · linarith only [hh.1,hL]
    · constructor <;> linarith only [hh.1,hh.2]
  have hbuf i (hi : i∈S) :
      Icc ((m i:ℝ)-(2*(W i:ℝ)+1)) ((m i:ℝ)+(2*(W i:ℝ)+1)) ⊆ Icc A B := by
    intro x hx
    apply hbuffer i hi
    have hw := (hWr i hi).2
    constructor <;> linarith only [hx.1,hx.2,hw]
  have hsmall i (hi : i∈S) :
      F*(2*(W i:ℝ)+1)^4 ≤ 1 ∧ (3*U/2)*(2*(W i:ℝ)+1)^2 ≤ 1 := by
    have hw : 2*(W i:ℝ)+1 ≤ 6*(N:ℝ)+1 := by linarith only [(hWr i hi).2]
    constructor
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 4) hF.le).trans hfourSmall
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hw 2) (by positivity)).trans hquadSmall
  have hcurv i (hi : i∈S) :
      |iteratedDeriv 2 f (m i)/2-((r i).num:ℝ)/(r i).den| ≤ 3*U/2 := by
    have hh := bourgain_curvature_level_difference f hf₄
      (fun x hx => ⟨hL.le.trans (hthree x hx).1,(hthree x hx).2⟩)
      ⟨(hm i hi).1.le,(hm i hi).2.le⟩ ⟨(hz i hi).1.le,(hz i hi).2.le⟩
    rw [hlevel i hi,Rat.cast_def,abs_sub_comm (m i:ℝ) (z i)] at hh
    have hr := mul_le_mul_of_nonneg_left (hround i hi) (show 0 ≤ 3*U by positivity)
    exact hh.trans (by linarith only [hr])
  have hscale i (hi : i∈S) : mu i*(W i:ℝ)^2 ≤ 1 := by
    have ha : (W i:ℝ)^2 ≤ (2*(W i:ℝ)+1)^2 := by
      nlinarith only [show (0:ℝ) ≤ W i from Nat.cast_nonneg _]
    calc
      _ ≤ U*(2*(W i:ℝ)+1)^2 :=
        mul_le_mul (hmu i hi).2.2 ha (sq_nonneg _) hU.le
      _ ≤ (3*U/2)*(2*(W i:ℝ)+1)^2 := by gcongr; linarith only [hU]
      _ ≤ _ := (hsmall i hi).2

  letI : NeZero M := ⟨by dsimp only [M]; omega⟩
  have hM : 63*U*(Q:ℝ)*(N:ℝ)^2≤(M:ℝ) := by
    have hh := Nat.le_ceil (63*U*(Q:ℝ)*(N:ℝ)^2)
    dsimp only [M]
    push_cast
    linarith only [hh]
  have hV : 0≤V := by dsimp only [V]; positivity
  have hWloss : 1≤Wloss := by
    have hp : 0≤32/(L*(Q:ℝ)^2*N) := by positivity
    dsimp only [Wloss]
    linarith only [hp]
  have hd : 0<d := by dsimp only [d]; positivity
  have hphysical i (hi : i∈S) :
      1≤H₀ ∧ H₀≤ mu i*((r i).den:ℝ)*(W i:ℝ)^2 ∧
        7*(mu i*((r i).den:ℝ)*(W i:ℝ)^2)≤63*U*(Q:ℝ)*(N:ℝ)^2 ∧
        7*(mu i*((r i).den:ℝ)*(W i:ℝ)^2)≤V*H₀ ∧
        |-2*mu i*(Real.sqrt (2/(3*mu i*((r i).den:ℝ))))^3|≤H₀*Real.sqrt H₀ ∧
        |-2*mu i*(Real.sqrt (2/(3*mu i*((r i).den:ℝ))))^3|/Real.sqrt H₀≤Wloss := by
    have hQq : (Q:ℝ)/2≤(r i).den := by
      have hh : (Q:ℝ)≤2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
      linarith only [hh]
    exact bourgain_frozen_physical_dual_scales hL hU hNr hQr (hmu i hi).2
      ⟨hQq,Nat.cast_le.mpr (hq i hi).1⟩ (hWr i hi) hdual hfrozen
  have hdscale i (hi : i∈S) : d≤ mu i*((r i).den:ℝ)*W i := by
    have hqr : (Q:ℝ)≤2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
    calc
      d = (L/6)*((Q:ℝ)/2)*N := by dsimp only [d]; ring
      _ ≤ mu i*((r i).den:ℝ)*W i :=
        mul_le_mul (mul_le_mul (hmu i hi).2.1 (by linarith only [hqr])
          (by positivity) (hmu i hi).1.le)
          (hWr i hi).1 hNr.le (mul_nonneg (hmu i hi).1.le (Nat.cast_nonneg _))
  by_cases hS : S.Nonempty
  · obtain ⟨i₀,hi₀⟩ := hS
    have hH₀ := (hphysical i₀ hi₀).1
    have hH₀M : H₀≤(M:ℝ) := by
      have hlow := (hphysical i₀ hi₀).2.1
      have hhigh := (hphysical i₀ hi₀).2.2.1.trans hM
      linarith only [hlow,hhigh,hH₀]
    obtain ⟨rinv,hinv,hbound⟩ := hsource ι S (fun _ => f) (fun i => (m i:ℝ))
      (fun i => (r i).num) (fun i => (r i).den) W H hWp
      (fun i hi => (hH i hi).trans (hW i hi).1) F (3*U/2) hF.le (by positivity)
      (fun i hi => (hsmall i hi).1) (fun i hi => (hsmall i hi).2)
      (fun i hi x hx => hf₄ x (hbuf i hi hx))
      (fun i hi x hx => (hfourAbs x (hbuf i hi hx)).2) hcurv
      (fun i hi => ⟨(r i).pos,((hq i hi).2.2.trans (hW i hi).1),
        (r i).isCoprime_num_den,(hmu i hi).1,hscale i hi⟩)
      M H₀ V Wloss d hH₀ hH₀M hV hWloss hd
      (fun i hi => (hphysical i hi).2.1)
      (fun i hi => (hphysical i hi).2.2.2.2.1)
      (fun i hi => (hphysical i hi).2.2.2.2.2)
      (fun i hi => (hphysical i hi).2.2.1.trans hM)
      (fun i hi => (hphysical i hi).2.2.2.1) hdscale

    let S₂ := S ×ˢ (Finset.univ : Finset (Fin 2))
    have hmul₂ n : (S₂.filter (fun p => k p.1=n)).card ≤ 2*Bmul := by
      have he : S₂.filter (fun p => k p.1=n)=
          (S.filter (fun i => k i=n)) ×ˢ (Finset.univ : Finset (Fin 2)) := by
        ext p
        simp only [S₂,Finset.mem_filter,Finset.mem_product,Finset.mem_univ,and_true]
      rw [he,Finset.card_product,Finset.card_univ,Fintype.card_fin]
      have hh := hmul n
      omega
    have hc₀ := four_coordinate_displacement_source_count S₂
      (fun p => m p.1) (fun p => k p.1) (fun p => (r p.1).num) (fun p => rinv p.1)
      (fun p => z p.1) (fun p => (r p.1).den) Prod.snd N (2*Bmul) M Q s f
      hN hL hU hF hlam hQ hUsmall hthin
      (fun p hp => hspan _ (Finset.mem_product.mp hp).1) hmul₂
      (fun x hx => hf x ⟨hx.1.le,hx.2.le⟩)
      (fun x hx => hthree x ⟨hx.1.le,hx.2.le⟩)
      (fun x hx => hfour x ⟨hx.1.le,hx.2.le⟩)
      (fun p hp => hm _ (Finset.mem_product.mp hp).1)
      (fun p hp => hz _ (Finset.mem_product.mp hp).1)
      (fun p hp => by simpa only [abs_sub_comm] using hround _ (Finset.mem_product.mp hp).1)
      (fun p hp => ⟨(r p.1).pos,(hq _ (Finset.mem_product.mp hp).1).1,
        (hq _ (Finset.mem_product.mp hp).1).2.1⟩)
      (fun p hp => hinv _ (Finset.mem_product.mp hp).1)
      (fun p hp => by simpa only [Rat.cast_def] using hlevel _ (Finset.mem_product.mp hp).1)
    dsimp only at hc₀
    have hPairRewrite : 4*((2*Bmul:ℕ):ℝ)*S₂.card+
        6*((2*Bmul:ℕ):ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ))=4*Pair := by
      dsimp only [Pair,Z,S₂]
      rw [Finset.card_product,Finset.card_univ,Fintype.card_fin]
      push_cast
      ring
    have hc := hc₀
    change _ ≤ 4*((2*Bmul:ℕ):ℝ)*S₂.card+
      6*((2*Bmul:ℕ):ℝ)^2*Count*(3*(K:ℝ)+Dweight*(harmonic K:ℝ)) at hc
    rw [hPairRewrite] at hc
    simp only [iteratedDeriv_one] at hc

    have hErr i (hi : i∈S) :
        Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
          1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den) ≤ Err := by
      have hQq : (Q:ℝ)/2 ≤ (r i).den := by
        have hh : (Q:ℝ) ≤ 2*((r i).den:ℝ) := by exact_mod_cast (hq i hi).2.1
        linarith only [hh]
      exact displacement_prescribed_source_error hN hQ (r i).pos hL
        (hW i hi).1 (hW i hi).2.1 (hmu i hi).2.1 hQq

    have hlog : 0≤Real.log (6*(N:ℝ)) := by
      have hn : (1:ℝ)≤N := by exact_mod_cast hN
      exact Real.log_nonneg (by linarith only [hn])
    have hErr0 : 0≤Err := by dsimp only [Err]; positivity
    let ErrorSum := ∑ i∈S,(Real.sqrt (W i)*Real.log (2*(W i:ℝ))+1/(mu i*(W i:ℝ)^2)+
      1/(Real.sqrt (mu i*(W i:ℝ))*Real.sqrt (r i).den))
    have hErrorSum0 : 0≤ErrorSum := by
      apply Finset.sum_nonneg
      intro i hi
      have hw1 : (1:ℝ)≤W i := by exact_mod_cast hWp i hi
      have hl := Real.log_nonneg (by linarith only [hw1] : 1≤2*(W i:ℝ))
      have hmup := (hmu i hi).1
      positivity
    have herrorSum : ErrorSum≤Z*Err := by
      calc
        _ ≤ ∑ _i∈S,Err := Finset.sum_le_sum hErr
        _ = S.card*Err := by simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard hErr0
    have hLoss : 0≤Loss := by dsimp only [Loss]; positivity
    have hsrc :
        (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)=
        ∑ i∈S, ‖∑ n∈Finset.Ioc (W i:ℤ) ((W i:ℤ)+H i),(𝐞 (f ((m i:ℝ)+n)):ℂ)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [←(hW i hi).2.2,bourgain_integer_source_translation]
    dsimp only at hbound hc
    rw [←hsrc] at hbound
    rw [Finset.card_product,Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at hbound
    rw [mul_comm (S.card:ℝ) 2] at hbound
    have hcweighted := mul_le_mul_of_nonneg_left hc
      (show 0≤Loss*(2*(S.card:ℝ))^10 by positivity)
    change _≤C*(Loss*(2*(S.card:ℝ))^10*_+ErrorSum^12) at hbound
    have hfirst := hbound.trans (mul_le_mul_of_nonneg_left
      (add_le_add hcweighted (le_refl (ErrorSum^12))) hC.le)
    have hfinal := hfirst.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (pow_le_pow_left₀ hErrorSum0 herrorSum 12)) hC.le)
    exact hfinal.trans (fourfold_source_majorant hC.le
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg S.card) hErr0) 12))
  · have hempty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hZ : Z=0 := by simp only [Z,hempty,Finset.card_empty,Nat.cast_zero]
    have hsrcempty :
        (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12=0 := by
      rw [hempty]
      simp only [Finset.sum_empty,zero_pow (by norm_num : (12:ℕ)≠0)]
    rw [hsrcempty]
    exact displacement_empty_source_bound C Loss Pair Err Z hZ

#print axioms exists_displacement_frozen_physical_source

private theorem displacement_physical_cutoff
    {a P U M Q : ℝ} (ha : 0 < a) (hP : 0 < P) (hU : 0 < U)
    (hsmall : U ≤ 1/3600) (hK : 1 ≤ P*U*Real.sqrt U)
    (hM : 1 ≤ M) (hQ : 0 < Q) (hQM : Q ≤ 4*M) :
    let H := ⌊1/(10*Real.sqrt U)⌋₊
    let lam := a*U/P
    let D₀ := (Real.sqrt M/(9*M)+Real.sqrt M/(12*M^2))*Real.sqrt (U*Q^3)
    let rho := (12*U*Real.sqrt (U*Q^3)/lam)*(Real.sqrt M/(6*M^2))
    let N := ⌈3*U*(rho+1)⌉₊
    1 ≤ N ∧ (N:ℝ) ≤ (2+48/a)*(P*U*Real.sqrt U) ∧
      4*D₀/Q ≤ 4*Real.sqrt U ∧
      144*U^2/(lam*H) ≤ (1728/a)*(P*U*Real.sqrt U) := by
  intro H lam D₀ rho N
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hb := raw_displacement_window_scales hU.le hM hQ hQM hlam
  have hrho : 0 ≤ rho := by dsimp only [rho]; positivity
  have harg : 0 < 3*U*(rho+1) := by positivity
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr harg).ne'
  have hNhi : (N:ℝ) ≤ (2+48/a)*(P*U*Real.sqrt U) := by
    have hceil := (Nat.ceil_lt_add_one harg.le).le
    change (N:ℝ) ≤ 3*U*(rho+1)+1 at hceil
    have hmul := mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ 3*U by positivity)
    have he : 3*U*(16*U*Real.sqrt U/lam)=(48/a)*(P*U*Real.sqrt U) := by
      dsimp only [lam]
      field_simp
      norm_num
    change 3*U*rho ≤ 3*U*(16*U*Real.sqrt U/lam) at hmul
    rw [he] at hmul
    nlinarith only [hceil,hmul,hsmall,hK]
  have hblock := displacement_block_scale hU hsmall
  have hHr : (0:ℝ) < H := by exact_mod_cast hblock.1
  have hinv : 1/(H:ℝ) ≤ 12*Real.sqrt U := by
    apply (div_le_iff₀ hHr).mpr
    nlinarith only [hblock.2.1]
  refine ⟨hN,hNhi,hb.1,?_⟩
  calc
    _ = ((144/a)*P*U)*(1/(H:ℝ)) := by dsimp only [lam]; field_simp
    _ ≤ ((144/a)*P*U)*(12*Real.sqrt U) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

#print axioms displacement_physical_cutoff

private theorem displacement_rpow_product {m n P U : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hP : 0 < P) (hU : 0 < U) (r s : ℝ) :
    (m*P*U^2)^r*(n*P*U*Real.sqrt U)^s =
      m^r*n^s*P^(r+s)*U^(2*r+3*s/2) := by
  rw [Real.mul_rpow (by positivity : 0 ≤ m*P) (sq_nonneg U),
    Real.mul_rpow hm.le hP.le, ←Real.rpow_natCast_mul hU.le]
  rw [Real.mul_rpow (by positivity : 0 ≤ n*P*U) (Real.sqrt_nonneg U),
    Real.mul_rpow (by positivity : 0 ≤ n*P) hU.le,
    Real.mul_rpow hn.le hP.le,Real.sqrt_eq_rpow,←Real.rpow_mul hU.le]
  rw [Real.rpow_add hP,
    show 2*r+3*s/2=2*r+(s+(1/2)*s) by ring,
    Real.rpow_add hU,Real.rpow_add hU]
  norm_num only [Nat.cast_ofNat]
  ring

#print axioms displacement_rpow_product

private theorem displacement_count_physical_majorant
    {l m n C P U K η : ℝ}
    (hl : 0 < l) (hm : 0 < m) (hn : 0 < n) (hC : 0 ≤ C)
    (hP : 0 < P) (hU : 0 < U) (hU1 : U ≤ 1)
    (hK : 0 ≤ K) (hKhi : K ≤ n*(P*U*Real.sqrt U))
    (hη : 0 ≤ η) (hηhi : η ≤ 7*Real.sqrt U) :
    let v := 2/l+1
    let a := 7*n+C*m
    let b := m^((1:ℝ)/3)*n^((2:ℝ)/3)
    let c := m^(-(1:ℝ)/2)*n^((1:ℝ)/2)
    3+(52+144*C)*((2/(l*U)+1)*(K*η+C*(m*P*U^2)+
        (m*P*U^2)^((1:ℝ)/3)*K^((2:ℝ)/3))+
        (m*P*U^2)^(-(1:ℝ)/2)*K^((1:ℝ)/2)) ≤
      (3+(52+144*C)*(v*(a+b)+c))*(1+P*U+P*U^((2:ℝ)/3)+U^(-(1:ℝ)/4)) := by
  intro v a b c
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hwidth : 2/(l*U)+1 ≤ v/U := by
    apply (le_div_iff₀ hU).mpr
    dsimp only [v]
    have he : (2/(l*U)+1)*U=2/l+U := by field_simp
    rw [he]
    linarith only [hU1]
  have hmain : K*η+C*(m*P*U^2) ≤ a*P*U^2 := by
    have hh := mul_le_mul hKhi hηhi hη (by positivity : 0 ≤ n*(P*U*Real.sqrt U))
    have he : n*(P*U*Real.sqrt U)*(7*Real.sqrt U)=7*n*P*U^2 := by
      calc
        _ = (7*n*P*U)*(Real.sqrt U)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hU.le]; ring
    rw [he] at hh
    dsimp only [a]
    nlinarith only [hh]
  have hthird : (m*P*U^2)^((1:ℝ)/3)*K^((2:ℝ)/3) ≤ b*P*U^((5:ℝ)/3) := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hK hKhi (by norm_num : (0:ℝ) ≤ 2/3))
      (Real.rpow_nonneg (by positivity : 0 ≤ m*P*U^2) ((1:ℝ)/3))
    have he := displacement_rpow_product hm hn hP hU ((1:ℝ)/3) ((2:ℝ)/3)
    norm_num at he
    convert hh using 1
    rw [show n*(P*U*Real.sqrt U)=n*P*U*Real.sqrt U by ring]
    simpa only [b] using he.symm
  have hhalf : (m*P*U^2)^(-(1:ℝ)/2)*K^((1:ℝ)/2) ≤ c*U^(-(1:ℝ)/4) := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hK hKhi (by norm_num : (0:ℝ) ≤ 1/2))
      (Real.rpow_nonneg (by positivity : 0 ≤ m*P*U^2) (-(1:ℝ)/2))
    have he := displacement_rpow_product hm hn hP hU (-(1:ℝ)/2) ((1:ℝ)/2)
    norm_num at he
    convert hh using 1
    rw [show n*(P*U*Real.sqrt U)=n*P*U*Real.sqrt U by ring]
    simpa only [c,neg_div] using he.symm
  have hinside :
      (2/(l*U)+1)*(K*η+C*(m*P*U^2)+(m*P*U^2)^((1:ℝ)/3)*K^((2:ℝ)/3))+
      (m*P*U^2)^(-(1:ℝ)/2)*K^((1:ℝ)/2) ≤
      v*(a*(P*U)+b*(P*U^((2:ℝ)/3)))+c*U^(-(1:ℝ)/4) := by
    have hrpow : U^((5:ℝ)/3)=U*U^((2:ℝ)/3) := by
      rw [show ((5:ℝ)/3)=1+2/3 by norm_num,Real.rpow_add hU,Real.rpow_one]
    calc
      _ ≤ (v/U)*(a*P*U^2+b*P*U^((5:ℝ)/3))+c*U^(-(1:ℝ)/4) :=
        add_le_add (mul_le_mul hwidth (add_le_add hmain hthird)
          (by positivity) (by positivity)) hhalf
      _ = _ := by rw [hrpow]; field_simp
  let E := 1+P*U+P*U^((2:ℝ)/3)+U^(-(1:ℝ)/4)
  have hterms : 1 ≤ E ∧ P*U ≤ E ∧ P*U^((2:ℝ)/3) ≤ E ∧ U^(-(1:ℝ)/4) ≤ E := by
    have h₁ : 0 ≤ P*U := by positivity
    have h₂ : 0 ≤ P*U^((2:ℝ)/3) := by positivity
    have h₃ : 0 ≤ U^(-(1:ℝ)/4) := by positivity
    dsimp only [E]
    constructor
    · linarith only [h₁,h₂,h₃]
    constructor
    · linarith only [h₂,h₃]
    constructor <;> linarith only [h₁,h₂,h₃]
  have hmajor : v*(a*(P*U)+b*(P*U^((2:ℝ)/3)))+c*U^(-(1:ℝ)/4) ≤ (v*(a+b)+c)*E := by
    calc
      _ ≤ v*(a*E+b*E)+c*E := add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hterms.2.1 ha)
          (mul_le_mul_of_nonneg_left hterms.2.2.1 hb)) hv)
        (mul_le_mul_of_nonneg_left hterms.2.2.2 hc)
      _ = _ := by ring
  calc
    _ ≤ 3+(52+144*C)*((v*(a+b)+c)*E) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hinside.trans hmajor) (by positivity))
    _ ≤ (3+(52+144*C)*(v*(a+b)+c))*E := by
      nlinarith only [hterms.1]

#print axioms displacement_count_physical_majorant

private theorem displacement_harmonic_weight
    {n d P U D : ℝ} {N : ℕ}
    (hn : 1 ≤ n) (hP : 1 ≤ P) (hU : 0 < U) (hU1 : U ≤ 1)
    (hN : 1 ≤ N) (hNhi : (N:ℝ) ≤ n*(P*U*Real.sqrt U))
    (hD : 0 ≤ D) (hDhi : D ≤ d*(P*U*Real.sqrt U)) :
    3*(N:ℝ)+D*(harmonic N:ℝ) ≤
      (3*n+d*(1+Real.log n))*(P*U*Real.sqrt U)*(1+Real.log P) := by
  have hnp : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hPp : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hNp : (0:ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hlogn := Real.log_nonneg hn
  have hlogP := Real.log_nonneg hP
  have hK : P*U*Real.sqrt U ≤ P := by
    have hs : Real.sqrt U ≤ 1 := Real.sqrt_le_one.mpr hU1
    calc
      _ ≤ P*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left hU1 hPp.le) hs
        (Real.sqrt_nonneg U) (by positivity)
      _ = _ := by ring
  have hNle : (N:ℝ) ≤ n*P := hNhi.trans (mul_le_mul_of_nonneg_left hK hnp.le)
  have hharm : (harmonic N:ℝ) ≤ (1+Real.log n)*(1+Real.log P) := by
    have hh := harmonic_le_one_add_log N
    have hl := Real.log_le_log hNp hNle
    rw [Real.log_mul hnp.ne' hPp.ne'] at hl
    nlinarith only [hh,hl,mul_nonneg hlogn hlogP]
  have hfirst : 3*(N:ℝ) ≤ (3*n)*(P*U*Real.sqrt U)*(1+Real.log P) := by
    have hh := mul_le_mul_of_nonneg_left hNhi (show (0:ℝ) ≤ 3 by norm_num)
    have hnext := le_mul_of_one_le_right
      (show 0 ≤ (3*n)*(P*U*Real.sqrt U) by positivity)
      (show 1 ≤ 1+Real.log P by linarith only [hlogP])
    exact (by nlinarith only [hh] : 3*(N:ℝ) ≤ (3*n)*(P*U*Real.sqrt U)).trans hnext
  have hsecond : D*(harmonic N:ℝ) ≤
      (d*(1+Real.log n))*(P*U*Real.sqrt U)*(1+Real.log P) := by
    calc
      _ ≤ D*((1+Real.log n)*(1+Real.log P)) := mul_le_mul_of_nonneg_left hharm hD
      _ ≤ (d*(P*U*Real.sqrt U))*((1+Real.log n)*(1+Real.log P)) :=
        mul_le_mul_of_nonneg_right hDhi (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (3*n)*(P*U*Real.sqrt U)*(1+Real.log P)+
        (d*(1+Real.log n))*(P*U*Real.sqrt U)*(1+Real.log P) := add_le_add hfirst hsecond
    _ = _ := by ring

#print axioms displacement_harmonic_weight

private theorem displacement_physical_count_terms {P U : ℝ} (hU : 0 < U) :
    (1+P*U+P*U^((2:ℝ)/3)+U^(-(1:ℝ)/4))*(P*U*Real.sqrt U) =
      P*U^((3:ℝ)/2)+P^2*U^((5:ℝ)/2)+P^2*U^((13:ℝ)/6)+P*U^((5:ℝ)/4) := by
  have h₁ : U^((3:ℝ)/2)=U*U^((1:ℝ)/2) := by
    rw [show ((3:ℝ)/2)=1+1/2 by norm_num,Real.rpow_add hU,Real.rpow_one]
  have h₂ : U^((5:ℝ)/2)=U^2*U^((1:ℝ)/2) := by
    rw [show ((5:ℝ)/2)=2+1/2 by norm_num,Real.rpow_add hU,Real.rpow_two]
  have h₃ : U^((13:ℝ)/6)=U^((2:ℝ)/3)*(U*U^((1:ℝ)/2)) := by
    rw [show ((13:ℝ)/6)=2/3+3/2 by norm_num,Real.rpow_add hU,h₁]
  have h₄ : U^((5:ℝ)/4)=U^(-(1:ℝ)/4)*(U*U^((1:ℝ)/2)) := by
    rw [show ((5:ℝ)/4)= -1/4+3/2 by norm_num,Real.rpow_add hU,h₁]
  rw [Real.sqrt_eq_rpow,h₁,h₂,h₃,h₄]
  ring

#print axioms displacement_physical_count_terms

private theorem exists_displacement_physical_weighted_count
    {l b a : ℝ} (hl : 0 < l) (hb : 0 < b) (ha : 0 < a) :
    ∃ C > (0:ℝ), ∀ (P U M Q : ℝ),
      0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U*Real.sqrt U →
      1 ≤ M → 0 < Q → Q ≤ 4*M →
      let H := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let F := b*U/P
      let lam := a*U/P
      let D₀ := (Real.sqrt M/(9*M)+Real.sqrt M/(12*M^2))*Real.sqrt (U*Q^3)
      let η := 4*D₀/Q
      let rho := (12*U*Real.sqrt (U*Q^3)/lam)*(Real.sqrt M/(6*M^2))
      let N := ⌈3*U*(rho+1)⌉₊
      let mu := L^3/(2*F)
      let ratio := max 1 (216*F*U^3/(lam*L^3))
      let D := 144*U^2/(lam*H)
      let Count := 3+(52+144*ratio)*((2/L+1)*((N:ℝ)*(η+9*U/4)+ratio*mu+
        mu^((1:ℝ)/3)*(N:ℝ)^((2:ℝ)/3))+mu^(-(1:ℝ)/2)*(N:ℝ)^((1:ℝ)/2))
      Count*(3*(N:ℝ)+D*(harmonic N:ℝ)) ≤
        C*(P*U^((3:ℝ)/2)+P^2*U^((5:ℝ)/2)+P^2*U^((13:ℝ)/6)+P*U^((5:ℝ)/4))*
          (1+Real.log P) := by
  let m := l^3/(2*b)
  let n := 2+48/a
  let R := max 1 (216*b/(a*l^3))
  let d := 1728/a
  let C₁ := 3+(52+144*R)*((2/l+1)*((7*n+R*m)+m^((1:ℝ)/3)*n^((2:ℝ)/3))+
    m^(-(1:ℝ)/2)*n^((1:ℝ)/2))
  let C₂ := 3*n+d*(1+Real.log n)
  have hm : 0 < m := by dsimp only [m]; positivity
  have hn : 1 ≤ n := by
    dsimp only [n]
    have hh : 0 < 48/a := by positivity
    linarith only [hh]
  have hnp : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_left _ _)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 < C₂ := by
    have hnlog := Real.log_nonneg hn
    dsimp only [C₂]
    positivity
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro P U M Q hP hU hUsmall hK hM hQ hQM H L F lam D₀ η rho N mu ratio D Count
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hs : Real.sqrt U ≤ 1 := Real.sqrt_le_one.mpr hU1
  have hUsqrt : U ≤ Real.sqrt U := by
    nlinarith only [Real.sq_sqrt hU.le,hs,Real.sqrt_nonneg U]
  have hP1 : 1 ≤ P := by
    have hh : P*U*Real.sqrt U ≤ P := by
      calc
        _ ≤ P*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left hU1 hP.le) hs
          (Real.sqrt_nonneg U) (by positivity)
        _ = _ := by ring
    exact hK.trans hh
  have hcut := displacement_physical_cutoff ha hP hU hUsmall hK hM hQ hQM
  change 1 ≤ N ∧ (N:ℝ) ≤ n*(P*U*Real.sqrt U) ∧ η ≤ 4*Real.sqrt U ∧
    D ≤ d*(P*U*Real.sqrt U) at hcut
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hH : 0 < H := (displacement_block_scale hU hUsmall).1
  have hHr : (0:ℝ) < H := Nat.cast_pos.mpr hH
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hη : 0 ≤ η := by dsimp only [η,D₀]; positivity
  have hηhi : η+9*U/4 ≤ 7*Real.sqrt U := by
    nlinarith only [hcut.2.2.1,hUsqrt,Real.sqrt_nonneg U]
  have hmu : mu=m*P*U^2 := by dsimp only [mu,m,L,F]; field_simp
  have hratio : ratio=R := by
    dsimp only [ratio,R,L,F,lam]
    congr 1
    field_simp
  have hcount := displacement_count_physical_majorant hl hm hnp hR hP hU hU1
    (Nat.cast_nonneg N) hcut.2.1 (show 0 ≤ η+9*U/4 by positivity) hηhi
  dsimp only at hcount
  have hcount' : Count ≤ C₁*(1+P*U+P*U^((2:ℝ)/3)+U^(-(1:ℝ)/4)) := by
    dsimp only [Count,L]
    rw [hmu,hratio]
    exact hcount
  have hweight := displacement_harmonic_weight hn hP1 hU hU1 hcut.1 hcut.2.1 hD hcut.2.2.2
  change _ ≤ C₂*(P*U*Real.sqrt U)*(1+Real.log P) at hweight
  have hharm0 : 0 ≤ (harmonic N:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i))
  have hweight0 : 0 ≤ 3*(N:ℝ)+D*(harmonic N:ℝ) := by positivity
  have heq := displacement_physical_count_terms (P:=P) hU
  calc
    _ ≤ (C₁*(1+P*U+P*U^((2:ℝ)/3)+U^(-(1:ℝ)/4)))*
        (C₂*(P*U*Real.sqrt U)*(1+Real.log P)) :=
      mul_le_mul hcount' hweight hweight0 (by positivity)
    _ = (C₁*C₂)*((1+P*U+P*U^((2:ℝ)/3)+U^(-(1:ℝ)/4))*(P*U*Real.sqrt U))*(1+Real.log P) := by ring
    _ = _ := by rw [heq]

#print axioms exists_displacement_physical_weighted_count

private theorem displacement_source_constant_absorption {C A X Pair R E : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hpair : Pair ≤ A*R) :
    C*(X*Pair+E) ≤ (C*A)*(X*R+E) := by
  have hh := mul_le_mul_of_nonneg_left hpair hX
  have he := mul_nonneg (sub_nonneg.mpr hA) hE
  calc
    _ ≤ C*(A*(X*R+E)) := mul_le_mul_of_nonneg_left (by nlinarith only [hh,he]) hC
    _ = _ := by ring

private theorem displacement_pair_majorant {c z x y t : ℝ}
    (hc : 0 ≤ c) (hz : 0 ≤ z) (ht : 0 ≤ t) (h : x*y ≤ c*t) :
    4*z+6*x*y ≤ (4+6*c)*(z+t) := by
  nlinarith only [h,mul_nonneg hc hz,ht]

private theorem displacement_taylor_smallness {b P U : ℝ}
    (hb : 0 < b) (hP : 0 < P) (hU : 0 < U) (hUsmall : U ≤ 1/3600)
    (hbPU : b ≤ P*U) :
    let N := ⌊1/(10*Real.sqrt U)⌋₊
    (b*U/P)*(6*(N:ℝ)+1)^4 ≤ 1 ∧ (3*U/2)*(6*(N:ℝ)+1)^2 ≤ 1 := by
  intro N
  have hblock := displacement_block_scale hU hUsmall
  have hN : (1:ℝ) ≤ N := by exact_mod_cast hblock.1
  have hR : 6*(N:ℝ)+1 ≤ 7*(N:ℝ) := by linarith only [hN]
  have hUscale : U*(N:ℝ)^2 ≤ 1/100 := hblock.2.2.2.2.1
  have hratio : b/(P*U) ≤ 1 := (div_le_one (mul_pos hP hU)).mpr hbPU
  constructor
  · calc
      _ ≤ (b*U/P)*(7*(N:ℝ))^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hR 4) (by positivity)
      _ = (b/(P*U))*2401*(U*(N:ℝ)^2)^2 := by field_simp; ring
      _ ≤ 1*2401*((1/100:ℝ)^2) := by gcongr
      _ ≤ _ := by norm_num
  · have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0 ≤ 6*(N:ℝ)+1) hR 2)
      (show 0 ≤ 3*U/2 by positivity)
    nlinarith only [hh,hUscale]

private theorem exists_displacement_scaled_frozen_source
    {ε l b a : ℝ} (hε : 0 < ε) (hl : 0 < l) (hb : 0 < b) (ha : 0 < a) :
    ∃ C > (0:ℝ), ∀ (ι : Type*) [DecidableEq ι] (S : Finset ι)
      (f : ℝ → ℝ) (r : ι → ℚ) (z : ι → ℝ) (m k : ι → ℤ)
      (H : ι → ℕ) (Q : ℕ) (s : ℤ) (A B P U : ℝ),
      0 < Q → 0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U*Real.sqrt U →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let F := b*U/P
      let lam := a*U/P
      b ≤ P*U →
      (∀ x∈Icc A B, ContDiffAt ℝ 5 f x) →
      (∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U) →
      (∀ x∈Icc A B, -F ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ -lam) →
      (∀ i∈S, z i∈Ioo A B) →
      (∀ i∈S, Icc ((m i:ℝ)-(6*(N:ℝ)+1)) ((m i:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B) →
      (∀ i∈S, |z i-m i| ≤ 1/2) →
      (∀ i∈S, (N:ℤ) ≤ s+(N:ℤ)*k i-m i ∧ s+(N:ℤ)*k i-m i ≤ 3*(N:ℤ)) →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ 1) →
      (∀ i∈S, H i ≤ N) →
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N) →
      (∀ i∈S, iteratedDeriv 2 f (z i)/2=(r i:ℝ)) →
      12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
      let Z := (S.card:ℝ)
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let Wloss := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let Loss := (5*Wloss)^11*Wloss^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
        Real.sqrt (12/(L*(N:ℝ)*Q))
      let R := Z+(P*U^((3:ℝ)/2)+P^2*U^((5:ℝ)/2)+P^2*U^((13:ℝ)/6)+P*U^((5:ℝ)/4))*
        (1+Real.log P)
      (∑ i∈S, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*(Loss*(2*Z)^10*R+(Z*Err)^12) := by
  obtain ⟨Cs,hCs,hsource⟩ := exists_displacement_frozen_physical_source hε
  obtain ⟨Cp,hCp,hcount⟩ := exists_displacement_physical_weighted_count hl hb ha
  let Cpair := 4+6*Cp
  have hCpair : 1 ≤ Cpair := by dsimp only [Cpair]; linarith only [hCp]
  refine ⟨Cs*Cpair,mul_pos hCs (lt_of_lt_of_le zero_lt_one hCpair),?_⟩
  intro ι instι S f r z m k H Q s A B P U hQ hP hU hUsmall hK N L F lam
    hbPU hf hthree hfour hz hbuffer hround hspan hmul hH hq hlevel
    hdual hfrozen Z M V Wloss d Loss Err R
  have hblock := displacement_block_scale hU hUsmall
  have hN : 0 < N := hblock.1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hband := hblock.2.2.2.2.2 Q (Nat.one_le_iff_ne_zero.mpr hQ.ne')
  change (7/16)*(Q:ℝ) ≤ (M:ℝ) ∧ (M:ℝ) ≤ 3*(Q:ℝ) ∧ (Q:ℝ)^2 < 6*(M:ℝ)^2 at hband
  have hM : (1:ℝ) ≤ M := by dsimp only [M]; exact_mod_cast (Nat.le_add_left 1 _)
  have hQM : (Q:ℝ) ≤ 4*(M:ℝ) := by nlinarith only [hband.1,hQ1]
  have hsmall := displacement_taylor_smallness hb hP hU hUsmall hbPU
  have hbound := hsource ι S f r z m k H N Q 1 s A B L F U lam
    hN hQ hL hF hU hlam (by linarith only [hUsmall]) hsmall.1 hsmall.2
    hf hthree hfour hz hbuffer hround hspan hmul hH hq hlevel hdual hfrozen hband.2.2
  have hc := hcount P U M Q hP hU hUsmall hK hM (Nat.cast_pos.mpr hQ) hQM
  dsimp only at hbound hc
  let Tails := (P*U^((3:ℝ)/2)+P^2*U^((5:ℝ)/2)+P^2*U^((13:ℝ)/6)+P*U^((5:ℝ)/4))*
    (1+Real.log P)
  have hP1 : 1 ≤ P := by
    have hs : Real.sqrt U ≤ 1 := Real.sqrt_le_one.mpr (by linarith only [hUsmall])
    have hh : P*U*Real.sqrt U ≤ P := by
      calc
        _ ≤ P*1*1 := mul_le_mul
          (mul_le_mul_of_nonneg_left (by linarith only [hUsmall] : U ≤ 1) hP.le) hs
          (Real.sqrt_nonneg U) (by positivity)
        _ = _ := by ring
    exact hK.trans hh
  have hlog := Real.log_nonneg hP1
  have hTails : 0 ≤ Tails := by dsimp only [Tails]; positivity
  rw [mul_assoc Cp] at hc
  change _ ≤ Cp*Tails at hc
  have hpair := displacement_pair_majorant hCp.le (Nat.cast_nonneg S.card) hTails hc
  have hLoss : 0 ≤ Loss := by dsimp only [Loss]; positivity
  have hE : 0 ≤ (Z*Err)^12 := (show Even (12:ℕ) by decide).pow_nonneg _
  have hclose := displacement_source_constant_absorption hCs.le hCpair
    (show 0 ≤ Loss*(2*Z)^10 by positivity) hE hpair
  simp only [Nat.cast_one,mul_one,one_pow] at hbound
  exact hbound.trans hclose

#print axioms exists_displacement_scaled_frozen_source

-- One two-case optimization handles every frozen denominator band; it uses
-- the existing dense and minimum-denominator cardinality bounds together.
private theorem displacement_denominator_elimination
    {v q B Z c : ℝ} (hv : 0 < v) (hq : 0 < q)
    (hZ : 0 ≤ Z) (hc : 0 ≤ c)
    (hlo : Z ≤ B*v^2*q^2) (hhi : Z*q^2 ≤ B) :
    (1+c/(v*q^2))^13*q^6*Z^10 ≤ (1+c)^13*B^10*v^7 := by
  have hd : 0 < v*q^2 := by positivity
  by_cases hsmall : v*q^2 ≤ 1
  · have hw : 1+c/(v*q^2) ≤ (1+c)/(v*q^2) := by
      apply (le_div_iff₀ hd).mpr
      have he : (1+c/(v*q^2))*(v*q^2)=v*q^2+c := by field_simp
      rw [he]
      linarith only [hsmall]
    calc
      _ ≤ ((1+c)/(v*q^2))^13*q^6*(B*v^2*q^2)^10 := by gcongr
      _ = _ := by field_simp
  · have hlarge : 1 ≤ v*q^2 := (lt_of_not_ge hsmall).le
    have hw : 1+c/(v*q^2) ≤ 1+c := by
      have hh : c/(v*q^2) ≤ c := (div_le_self hc hlarge)
      linarith only [hh]
    have hz : Z ≤ B/q^2 := (le_div_iff₀ (sq_pos_of_pos hq)).mpr hhi
    have hp : 1 ≤ v^7*q^14 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hlarge 7
      convert hh using 1 <;> ring
    calc
      _ ≤ (1+c)^13*q^6*(B/q^2)^10 := by gcongr
      _ = ((1+c)^13*B^10)/q^14 := by field_simp
      _ ≤ _ := by
        apply (div_le_iff₀ (pow_pos hq 14)).mpr
        have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (1+c)^13*B^10 by positivity)
        nlinarith only [hh]

#print axioms displacement_denominator_elimination

private theorem exists_displacement_frozen_loss_bound
    {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (U B Z : ℝ) (Q : ℕ),
      0 < U → U ≤ 1/3600 → 0 ≤ Z → 0 < Q →
      Z ≤ B*U*(Q:ℝ)^2 → Z*(Q:ℝ)^2 ≤ B →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let W := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      Loss*(2*Z)^10 ≤ C*B^10*Real.sqrt U*(Q:ℝ)^ε*(1+Real.log Q)^12 := by
  let cw := 384/l
  let cd := 288/l
  let cv := 6*(3+8*Real.pi*(756/l))*(1+Real.log 3)
  let C₀ := (5:ℝ)^11*cv^12*cd^6*(3:ℝ)^((12:ℝ)+ε)*2^10
  have hcw : 0 < cw := by dsimp only [cw]; positivity
  have hcd : 0 < cd := by dsimp only [cd]; positivity
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hcv : 0 < cv := by dsimp only [cv]; positivity
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀*(1+cw)^13,by positivity,?_⟩
  intro U B Z Q hU hUsmall hZ hQ hlo hhi N L M V W d Loss
  let v := Real.sqrt U
  have hv : 0 < v := Real.sqrt_pos.mpr hU
  have hvsq : v^2=U := Real.sq_sqrt hU.le
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hblock := displacement_block_scale hU hUsmall
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr hblock.1
  have hband := hblock.2.2.2.2.2 Q (Nat.one_le_iff_ne_zero.mpr hQ.ne')
  have hMhi : (M:ℝ) ≤ 3*(Q:ℝ) := hband.2.1
  have hM1 : (1:ℝ) ≤ M := by dsimp only [M]; exact_mod_cast (Nat.le_add_left 1 _)
  have hMp : (0:ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hUH : v/12 ≤ U*(N:ℝ) := by
    calc
      _ = v*(1/12) := by ring
      _ ≤ v*((N:ℝ)*v) := mul_le_mul_of_nonneg_left hblock.2.1 hv.le
      _ = v^2*N := by ring
      _ = _ := by rw [hvsq]
  have hden : (l/12)*v*(Q:ℝ)^2 ≤ L*(Q:ℝ)^2*N := by
    have hh := mul_le_mul_of_nonneg_left hUH (show 0 ≤ l*(Q:ℝ)^2 by positivity)
    dsimp only [L]
    nlinarith only [hh]
  have hW : W ≤ 1+cw/(v*(Q:ℝ)^2) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 32)
      (show 0 < (l/12)*v*(Q:ℝ)^2 by positivity) hden
    have he : 32/((l/12)*v*(Q:ℝ)^2)=cw/(v*(Q:ℝ)^2) := by dsimp only [cw]; field_simp; norm_num
    rw [he] at hh
    exact add_le_add le_rfl hh
  have hdlo : (l/144)*v*(Q:ℝ) ≤ d := by
    have hh := mul_le_mul_of_nonneg_left hUH (show 0 ≤ l*(Q:ℝ)/12 by positivity)
    dsimp only [d,L]
    nlinarith only [hh]
  have hdinv : 2/d ≤ cd/(v*(Q:ℝ)) := by
    calc
      _ ≤ 2/((l/144)*v*(Q:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hdlo
      _ = _ := by dsimp only [cd]; field_simp; norm_num
  have hV : V=756/l := by dsimp only [V,L]; field_simp
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlog : 6*(3+8*Real.pi*V)*(1+Real.log M) ≤ cv*(1+Real.log Q) := by
    have hh := Real.log_le_log hMp hMhi
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hQr.ne'] at hh
    have hh' : 1+Real.log M ≤ (1+Real.log 3)*(1+Real.log Q) := by
      nlinarith only [hh,mul_nonneg hlog3 hlogQ]
    rw [hV]
    calc
      _ ≤ (6*(3+8*Real.pi*(756/l)))*((1+Real.log 3)*(1+Real.log Q)) :=
        mul_le_mul_of_nonneg_left hh' (by positivity)
      _ = _ := by dsimp only [cv]; ring
  have hMpow : (M:ℝ)^((12:ℝ)+ε) ≤
      (3:ℝ)^((12:ℝ)+ε)*(Q:ℝ)^12*(Q:ℝ)^ε := by
    calc
      _ ≤ (3*(Q:ℝ))^((12:ℝ)+ε) := Real.rpow_le_rpow hMp.le hMhi (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hQr.le,Real.rpow_add hQr]
        rw [show (Q:ℝ)^(12:ℝ)=(Q:ℝ)^12 from Real.rpow_natCast (Q:ℝ) 12]
        ring
  have hW0 : 0 ≤ W := by dsimp only [W,L]; positivity
  have hd : 0 < d := by dsimp only [d,L]; positivity
  have hV0 : 0 ≤ V := by dsimp only [V,L]; positivity
  have hloss : Loss*(2*Z)^10 ≤
      ((5*(1+cw/(v*(Q:ℝ)^2)))^11*(1+cw/(v*(Q:ℝ)^2))^2*
        (cv*(1+Real.log Q))^12*(cd/(v*(Q:ℝ)))^6*
        ((3:ℝ)^((12:ℝ)+ε)*(Q:ℝ)^12*(Q:ℝ)^ε))*(2*Z)^10 := by
    dsimp only [Loss]
    gcongr
  have hopt := displacement_denominator_elimination hv hQr hZ hcw.le
    (by simpa only [hvsq] using hlo) hhi
  have hfactor : 0 ≤ C₀/(v^6)*(Q:ℝ)^ε*(1+Real.log Q)^12 := by positivity
  have hh := mul_le_mul_of_nonneg_left hopt hfactor
  calc
    _ ≤ _ := hloss
    _ = (C₀/(v^6)*(Q:ℝ)^ε*(1+Real.log Q)^12)*
        ((1+cw/(v*(Q:ℝ)^2))^13*(Q:ℝ)^6*Z^10) := by
      dsimp only [C₀]
      field_simp
    _ ≤ (C₀/(v^6)*(Q:ℝ)^ε*(1+Real.log Q)^12)*((1+cw)^13*B^10*v^7) := hh
    _ = _ := by change _ = (C₀*(1+cw)^13)*B^10*v*(Q:ℝ)^ε*(1+Real.log Q)^12; field_simp

#print axioms exists_displacement_frozen_loss_bound

-- Reuse the production buffered-entry argument with the signed C5 jets above.
-- The next four private helpers are copied verbatim solely for prototype
-- visibility; production integration reuses the original declarations.
private theorem sum_integer_Ioc_join (g : ℤ → ℂ) {a b c : ℤ}
    (hab : a≤b) (hbc : b≤c) :
    (∑ n∈Finset.Ioc a b,g n)+(∑ n∈Finset.Ioc b c,g n)=
      ∑ n∈Finset.Ioc a c,g n := by
  have hd : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [Finset.mem_Ioc] at hn hm
    omega
  rw [←Finset.sum_union hd,Finset.Ioc_union_Ioc_eq_Ioc hab hbc]

private theorem sum_integer_blocks (g : ℤ → ℂ) (a : ℤ) {N u v : ℕ}
    (huv : u≤v) :
    (∑ k∈Finset.Ico u v,∑ n∈Finset.Ioc (a+(N:ℤ)*k)
      (a+(N:ℤ)*((k:ℤ)+1)),g n)=
      ∑ n∈Finset.Ioc (a+(N:ℤ)*u) (a+(N:ℤ)*v),g n := by
  induction v,huv using Nat.le_induction with
  | base => simp
  | succ v hv ih =>
    rw [Finset.sum_Ico_succ_top hv,ih]
    push_cast
    exact sum_integer_Ioc_join g
      (by gcongr)
      (by nlinarith only [Int.natCast_nonneg N])

private theorem norm_sum_integer_Ioc_le (g : ℤ → ℂ) (hg : ∀ n,‖g n‖≤1)
    {a b : ℤ} (hab : a≤b) :
    ‖∑ n∈Finset.Ioc a b,g n‖≤(b:ℝ)-a := by
  calc
    _ ≤ ∑ n∈Finset.Ioc a b,‖g n‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈Finset.Ioc a b,(1:ℝ) := Finset.sum_le_sum (fun n _ => hg n)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Int.card_Ioc]
      exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hab)

private theorem exists_buffered_integer_source_blocks
    (g : ℤ → ℂ) (hg : ∀ n,‖g n‖≤1)
    {a b : ℤ} {P : ℝ} (hab : a≤b) (ha : P≤a) (hb : (b:ℝ)≤2*P)
    (N : ℕ) (hN : 0<N) :
    ∃ S : Finset ℕ,
      (∀ k∈S, Icc ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k-(7*(N:ℝ)+2))
        ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k+(7*(N:ℝ)+2)) ⊆ Icc (P+1/2) (2*P-1/2)) ∧
      (∀ k∈S, a≤a+(N:ℤ)*k ∧ a+(N:ℤ)*k+N≤b) ∧
      ‖∑ n∈Finset.Ioc a b,g n‖≤23*(N:ℝ)+
        ∑ k∈S,‖∑ n∈Finset.Ioc (a+(N:ℤ)*k) (a+(N:ℤ)*k+N),g n‖ := by
  classical
  let q := (b-a).toNat/N
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hcast : ((b-a).toNat:ℤ)=b-a := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  have hlow : (N:ℤ)*q≤b-a := by
    have h := Nat.div_mul_le_self (b-a).toNat N
    have h' : (q:ℤ)*(N:ℤ)≤((b-a).toNat:ℤ) := by exact_mod_cast h
    nlinarith only [h',hcast]
  have hhigh : b-a<(N:ℤ)*((q:ℤ)+1) := by
    have h := Nat.lt_mul_div_succ (b-a).toNat hN
    have h' : ((b-a).toNat:ℤ)<(N:ℤ)*((q:ℤ)+1) := by exact_mod_cast h
    omega
  have hlowR : (N:ℝ)*q≤(b:ℝ)-a := by exact_mod_cast hlow
  have hhighR : (b:ℝ)-a<(N:ℝ)*((q:ℝ)+1) := by exact_mod_cast hhigh
  by_cases hq : 22≤q
  · let S := Finset.Ico 12 (q-10)
    refine ⟨S,?_,?_,?_⟩
    · intro k hk x hx
      obtain ⟨hk₁,hk₂⟩ := Finset.mem_Ico.mp hk
      have hkr : (12:ℝ)≤k := by exact_mod_cast hk₁
      have hkr' : (k:ℝ)+11≤q := by exact_mod_cast (show k+11≤q by omega)
      have hNl := mul_le_mul_of_nonneg_left hkr (le_trans zero_le_one hNr)
      have hNu := mul_le_mul_of_nonneg_left hkr' (le_trans zero_le_one hNr)
      constructor <;> nlinarith only [ha,hb,hx.1,hx.2,hNl,hNu,hlowR,hNr]
    · intro k hk
      obtain ⟨hk₁,hk₂⟩ := Finset.mem_Ico.mp hk
      have hkq : (k:ℤ)+1≤q := by exact_mod_cast (show k+1≤q by omega)
      constructor
      · nlinarith only [Int.natCast_nonneg N,Int.natCast_nonneg k]
      · have h := mul_le_mul_of_nonneg_left hkq (Int.natCast_nonneg N)
        nlinarith only [h,hlow]
    · let lo := a+(N:ℤ)*12
      let hi := a+(N:ℤ)*(q-10:ℕ)
      have hqcast : ((q-10:ℕ):ℝ)=(q:ℝ)-10 := by rw [Nat.cast_sub (by omega)]; norm_num
      have hlo : a≤lo := by dsimp only [lo]; nlinarith only [Int.natCast_nonneg N]
      have hmid : lo≤hi := by dsimp only [lo,hi]; gcongr; omega
      have hhi : hi≤b := by
        have hh : ((q-10:ℕ):ℤ)≤q := by exact_mod_cast Nat.sub_le q 10
        have h := mul_le_mul_of_nonneg_left hh (Int.natCast_nonneg N)
        dsimp only [hi]
        omega
      have he := (sum_integer_Ioc_join g hlo (hmid.trans hhi))
      rw [←sum_integer_Ioc_join g hmid hhi] at he
      rw [←he]
      have hnorm := (norm_add_le (∑ n∈Finset.Ioc a lo,g n)
        ((∑ n∈Finset.Ioc lo hi,g n)+(∑ n∈Finset.Ioc hi b,g n))).trans
        (add_le_add le_rfl (norm_add_le (∑ n∈Finset.Ioc lo hi,g n)
          (∑ n∈Finset.Ioc hi b,g n)))
      have hb₁ := norm_sum_integer_Ioc_le g hg hlo
      have hb₂ := norm_sum_integer_Ioc_le g hg hhi
      have hblocks := sum_integer_blocks g a (N:=N) (u:=12) (v:=q-10) (by omega)
      norm_num only [Nat.cast_ofNat] at hblocks
      have hcore : ‖∑ n∈Finset.Ioc lo hi,g n‖≤
          ∑ k∈S,‖∑ n∈Finset.Ioc (a+(N:ℤ)*k) (a+(N:ℤ)*k+N),g n‖ := by
        dsimp only [lo,hi]
        rw [←hblocks]
        convert norm_sum_le _ _ using 1
        simp only [S,mul_add,mul_one,add_assoc]
      have hlor : (lo:ℝ)=(a:ℝ)+(N:ℝ)*12 := by simp only [lo,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
      have hhir : (hi:ℝ)=(a:ℝ)+(N:ℝ)*((q:ℝ)-10) := by
        simp only [hi,Int.cast_add,Int.cast_mul,Int.cast_natCast,hqcast]
      nlinarith only [hnorm,hb₁,hb₂,hcore,hlor,hhir,hhighR]
  · refine ⟨∅,by simp,by simp,?_⟩
    simp only [Finset.sum_empty,add_zero]
    have hqR : (q:ℝ)+1≤22 := by exact_mod_cast (show q+1≤22 by omega)
    have h := mul_le_mul_of_nonneg_left hqR (le_trans zero_le_one hNr)
    have hn := norm_sum_integer_Ioc_le g hg hab
    nlinarith only [hn,hhighR,h,hNr]

open Expdb

private theorem displacement_model_buffered_entry {σ : ℝ} (hσ : 0<σ) :
    ∃ δ>(0:ℝ), ∀ (F : ℝ → ℝ) (T P : ℝ) (a b N : ℕ),
      0<T → 0<P → 0<N → a ≤ b → P ≤ a → (b:ℝ) ≤ 2*P →
      Expdb.IsApproximateModelPhaseFunction F σ 3 δ →
      let f := fun x => T*F (x/P)
      let A := P+1/2
      let B := 2*P-1/2
      let L := modelPhaseJetLower σ 2*T/P^3
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3/6
      let lambda := modelPhaseJetLower σ 3*T/P^4
      let F4 := (modelPhaseJetCoefficient σ 3+1)*T/P^4
      let X := (modelPhaseJetCoefficient σ 1+1)*T/P^2/2
      0<L ∧ 0<U ∧ 0<lambda ∧ 0 ≤ F4 ∧ 0 ≤ X ∧
      (∀ x∈Icc A B, ContDiffAt ℝ 5 f x) ∧
      (∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x ∧ iteratedDeriv 3 f x ≤ 6*U) ∧
      (∀ x∈Icc A B, -F4 ≤ iteratedDeriv 4 f x ∧ iteratedDeriv 4 f x ≤ -lambda) ∧
      (∀ x∈Icc A B, |iteratedDeriv 2 f x/2| ≤ X) ∧
      ∃ S : Finset ℕ,
        (∀ k∈S, Icc ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k-(7*(N:ℝ)+2))
          ((a:ℝ)-2*(N:ℝ)+(N:ℝ)*k+(7*(N:ℝ)+2)) ⊆ Icc A B) ∧
        (∀ k∈S, (a:ℤ) ≤ a+(N:ℤ)*k ∧ a+(N:ℤ)*k+N ≤ b) ∧
        (∀ j : ℤ, (S.filter (fun k : ℕ => (k:ℤ)=j)).card ≤ 1) ∧
        ‖exponentialSumAt F T P a b‖ ≤ 1+23*(N:ℝ)+
          ∑ k∈S,‖∑ n∈Finset.Ioc ((a:ℤ)+(N:ℤ)*k)
            ((a:ℤ)+(N:ℤ)*k+N),(𝐞 (f n):ℂ)‖ := by
  obtain ⟨δ,hδ,hdata⟩ := model_displacement_derivative_data hσ
  refine ⟨δ,hδ,?_⟩
  intro F T P a b N hT hP hN hab ha hb hF f A B L U lambda F4 X
  obtain ⟨hreg,hthree,hfour,hcurv⟩ := hdata F T P hT hP hF
  have hinside : Icc A B ⊆ Ioo P (2*P) := by
    intro x hx
    dsimp only [A,B] at hx
    constructor <;> linarith only [hx.1,hx.2]
  have hc₂ := modelPhaseJetLower_pos hσ 2
  have hc₃ := modelPhaseJetLower_pos hσ 3
  have hC₁ := modelPhaseJetCoefficient_nonneg σ 1
  have hC₂ := modelPhaseJetCoefficient_nonneg σ 2
  have hC₃ := modelPhaseJetCoefficient_nonneg σ 3
  refine ⟨by dsimp only [L]; positivity,by dsimp only [U]; positivity,
    by dsimp only [lambda]; positivity,by dsimp only [F4]; positivity,
    by dsimp only [X]; positivity,
    fun x hx => hreg x (hinside hx),?_,
    fun x hx => hfour x (hinside hx),fun x hx => hcurv x (hinside hx),?_⟩
  · intro x hx
    obtain ⟨hl,hu⟩ := hthree x (hinside hx)
    refine ⟨hl,hu.trans_eq ?_⟩
    dsimp only [U]
    ring
  · obtain ⟨S,hbuf,hspan,hbound⟩ := exists_buffered_integer_source_blocks
      (fun n => (𝐞 (f n):ℂ)) (by intro n; simp)
      (a:=(a:ℤ)) (b:=(b:ℤ)) (P:=P) (by exact_mod_cast hab)
      (by exact_mod_cast ha) (by exact_mod_cast hb) N hN
    refine ⟨S,hbuf,hspan,?_,?_⟩
    · intro j
      apply Finset.card_le_one.mpr
      intro k hk l hl
      have hk' := (Finset.mem_filter.mp hk).2
      have hl' := (Finset.mem_filter.mp hl).2
      exact_mod_cast hk'.trans hl'.symm
    · rw [exponentialSumAt_eq_int_sum]
      rw [Finset.Icc_eq_cons_Ioc (by exact_mod_cast hab),Finset.sum_cons]
      have hh := norm_add_le (oscillatory F T P a)
        (∑ n∈Finset.Ioc (a:ℤ) b,oscillatory F T P n)
      rw [norm_oscillatory] at hh
      change ‖oscillatory F T P a+(∑ n∈Finset.Ioc (a:ℤ) b,oscillatory F T P n)‖ ≤ _
      dsimp only [f] at hbound
      change ‖∑ n∈Finset.Ioc (a:ℤ) b,oscillatory F T P n‖ ≤ _ at hbound
      linarith only [hh,hbound]

#print axioms displacement_model_buffered_entry

-- Existing private production geometry, copied for scratch visibility only.
private theorem bourgain_minimal_arc_rounded_source_geometry
    {N : ℕ} {start : ℤ} {base z A B : ℝ} (hN : 0 < N)
    (hstart : (start:ℝ)=base+2*(N:ℝ))
    (hz : z∈Ioo (base-(N:ℝ)/4) (base+(N:ℝ)/4))
    (hbuffer : Icc (base-(7*(N:ℝ)+2)) (base+(7*(N:ℝ)+2)) ⊆ Icc A B) :
    z∈Ioo A B ∧ |z-(round z:ℝ)| ≤ 1/2 ∧
      ((N:ℤ) ≤ start-round z ∧ start-round z ≤ 3*(N:ℤ)) ∧
      Icc ((round z:ℝ)-(6*(N:ℝ)+1)) ((round z:ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hround : |z-(round z:ℝ)| ≤ 1/2 := abs_sub_round z
  have hround' := abs_le.mp hround
  have hlo := (hbuffer (left_mem_Icc.mpr (by linarith only [hNr]))).1
  have hhi := (hbuffer (right_mem_Icc.mpr (by linarith only [hNr]))).2
  refine ⟨⟨by linarith only [hlo,hz.1,hNr],by linarith only [hhi,hz.2,hNr]⟩,hround,?_,?_⟩
  · have hlow : (N:ℝ) ≤ (start:ℝ)-(round z:ℝ) := by
      linarith only [hz.1,hz.2,hround'.1,hround'.2,hstart,hNr]
    have hhigh : (start:ℝ)-(round z:ℝ) ≤ 3*(N:ℝ) := by
      linarith only [hz.1,hz.2,hround'.1,hround'.2,hstart,hNr]
    constructor
    · exact_mod_cast hlow
    · exact_mod_cast hhigh
  · intro x hx
    apply hbuffer
    constructor <;> linarith only [hx.1,hx.2,hz.1,hz.2,hround'.1,hround'.2,hNr]

private theorem displacement_minimal_source_family
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ℝ → ℝ) (k : ι → ℤ)
    (N : ℕ) (s : ℤ) {A B L X : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hX : 0 ≤ X)
    (hf : ∀ x∈Icc A B, ContDiffAt ℝ 3 f x)
    (hthree : ∀ x∈Icc A B, L ≤ iteratedDeriv 3 f x)
    (hcurv : ∀ x∈Icc A B, |iteratedDeriv 2 f x/2| ≤ X)
    (hmul : ∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ 1) :
    let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
    (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2)) ⊆ Icc A B) →
    ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈S, z i∈Ioo A B ∧ |z i-(round (z i):ℝ)| ≤ 1/2 ∧
        ((N:ℤ) ≤ s+(N:ℤ)*k i-round (z i) ∧ s+(N:ℤ)*k i-round (z i) ≤ 3*(N:ℤ)) ∧
        Icc ((round (z i):ℝ)-(6*(N:ℝ)+1)) ((round (z i):ℝ)+(6*(N:ℝ)+1)) ⊆ Icc A B) ∧
      (∀ i∈S, iteratedDeriv 2 f (z i)/2=(r i:ℝ)) ∧
      (∀ Q : ℕ, 2 ≤ Q →
        let D := 8/(L*(N:ℝ)*(Q:ℝ))
        ((S.filter (fun i => Q ≤ (r i).den)).card:ℝ) ≤
          4*(X+1)*D^2+D*(2+Real.log (D+1))) := by
  classical
  intro base hbuffer
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have ht i (hi : i∈S) : base i∈Icc A B :=
    hbuffer i hi ⟨by linarith only [hNr],by linarith only [hNr]⟩
  obtain ⟨r,z,hr,htail⟩ := exists_bourgain_C3_minimal_curvature_arc_count S f k N 1
    ((s:ℝ)-2*(N:ℝ)) hN hL hX hf hthree hmul
    (by
      intro i hi x hx
      apply hbuffer i hi
      change base i-(N:ℝ)/4 ≤ x ∧ x ≤ base i+(N:ℝ)/4 at hx
      constructor <;> linarith only [hx.1,hx.2,hNr])
    (fun i hi => hcurv _ (ht i hi))
  refine ⟨r,z,?_,fun i hi => (hr i hi).2.1,?_⟩
  · intro i hi
    exact bourgain_minimal_arc_rounded_source_geometry hN
      (by dsimp only [base]; push_cast; ring) (hr i hi).1 (hbuffer i hi)
  · intro Q hQ D
    simpa only [Nat.cast_one,one_mul] using htail Q hQ

#print axioms displacement_minimal_source_family

private theorem exists_displacement_cardinality_majorants
    {l x : ℝ} (hl : 0 < l) (hx : 0 ≤ x) :
    ∃ C ≥ (1:ℝ), ∀ (P U Q : ℝ),
      0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U → 1 ≤ Q →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      Q ≤ 2*(N:ℝ) →
      let X := x*P*U
      let D := 16/(l*U*(N:ℝ)*Q)
      4*Q*(2*X*Q+1) ≤ C*P*U*Q^2 ∧
        4*(X+1)*D^2+D*(2+Real.log (D+1)) ≤
          C*(P/Q^2)*(1+Real.log P) := by
  let c := 192/l
  let C₁ := 8*x+4
  let C₂ := 4*(x+1)*c^2+c*(2+Real.log (c+1))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcLog : 0 ≤ Real.log (c+1) := Real.log_nonneg (by linarith only [hc])
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂]; positivity
  refine ⟨1+C₁+C₂,by linarith only [hC₁,hC₂],?_⟩
  intro P U Q hP hU hUsmall hPU hQ N hQN X D
  have hQp : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hP1 : 1 ≤ P := hPU.trans (by nlinarith only [mul_le_mul_of_nonneg_left hU1 hP.le])
  have hlogP := Real.log_nonneg hP1
  have hblock := displacement_block_scale hU hUsmall
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hblock.1
  let v := Real.sqrt U
  have hv : 0 < v := Real.sqrt_pos.mpr hU
  have hvsq : v^2=U := Real.sq_sqrt hU.le
  have hUH : v/12 ≤ U*(N:ℝ) := by
    calc
      _ = v*(1/12) := by ring
      _ ≤ v*((N:ℝ)*v) := mul_le_mul_of_nonneg_left hblock.2.1 hv.le
      _ = v^2*N := by ring
      _ = _ := by rw [hvsq]
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hDbound : D ≤ c/(v*Q) := by
    have hden : (l/12)*v*Q ≤ l*U*(N:ℝ)*Q := by
      have hh := mul_le_mul_of_nonneg_left hUH (show 0 ≤ l*Q by positivity)
      nlinarith only [hh]
    calc
      _ ≤ 16/((l/12)*v*Q) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = _ := by dsimp only [c]; field_simp; norm_num
  have hQv : Q ≤ P*v := by
    have hh := mul_le_mul_of_nonneg_left hQN hv.le
    have hn : (N:ℝ)*v ≤ 1/10 := hblock.2.2.1
    have hqv : Q*v ≤ P*U := by nlinarith only [hh,hn,hPU]
    apply (mul_le_mul_iff_right₀ hv).mp
    calc
      _ = Q*v := by ring
      _ ≤ P*U := hqv
      _ = _ := by rw [←hvsq]; ring
  have hDlinear : D ≤ c*(P/Q^2) := by
    calc
      _ ≤ c/(v*Q) := hDbound
      _ ≤ _ := by
        apply (div_le_iff₀ (mul_pos hv hQp)).mpr
        have hh := mul_le_mul_of_nonneg_left hQv (show 0 ≤ c/Q by positivity)
        convert hh using 1 <;> field_simp
  have hQsq : 1 ≤ Q^2 := by nlinarith only [hQ]
  have hDP : D ≤ c*P := by
    exact hDlinear.trans (mul_le_mul_of_nonneg_left (div_le_self hP.le hQsq) hc.le)
  have hlogD0 : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith only [hD])
  have hlogD : 2+Real.log (D+1) ≤ (2+Real.log (c+1))*(1+Real.log P) := by
    have hh := Real.log_le_log (by positivity : 0 < D+1)
      (show D+1 ≤ (c+1)*P by nlinarith only [hDP,hP1])
    rw [Real.log_mul (by positivity : c+1 ≠ 0) hP.ne'] at hh
    nlinarith only [hh,hlogP,mul_nonneg hcLog hlogP]
  have hDsquare : D^2 ≤ c^2/(U*Q^2) := by
    calc
      _ ≤ (c/(v*Q))^2 := pow_le_pow_left₀ hD hDbound 2
      _ = _ := by rw [div_pow,mul_pow,hvsq]
  have hquadratic : 4*(X+1)*D^2 ≤ (4*(x+1)*c^2)*(P/Q^2) := by
    have hX : X+1 ≤ (x+1)*P*U := by dsimp only [X]; nlinarith only [hPU]
    calc
      _ ≤ 4*((x+1)*P*U)*(c^2/(U*Q^2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hX (by norm_num)) hDsquare (sq_nonneg D) (by positivity)
      _ = _ := by field_simp
  constructor
  · have hh : 4*Q ≤ 4*P*U*Q^2 := by
      have hpq : 1 ≤ (P*U)*Q := by
        calc
          _ = (1:ℝ)*1 := by ring
          _ ≤ _ := mul_le_mul hPU hQ (by norm_num) (le_trans zero_le_one hPU)
      have hh := mul_le_mul_of_nonneg_left hpq (show 0 ≤ 4*Q by positivity)
      nlinarith only [hh]
    have hfirst : 4*Q*(2*X*Q+1) ≤ C₁*P*U*Q^2 := by
      dsimp only [X,C₁]
      nlinarith only [hh]
    exact hfirst.trans (by gcongr; linarith only [hC₂])
  · calc
      _ ≤ (4*(x+1)*c^2)*(P/Q^2)+(c*(P/Q^2))*((2+Real.log (c+1))*(1+Real.log P)) :=
        add_le_add hquadratic (mul_le_mul hDlinear hlogD (by positivity) (by positivity))
      _ ≤ C₂*(P/Q^2)*(1+Real.log P) := by
        have hh := mul_nonneg (show 0 ≤ (4*(x+1)*c^2)*(P/Q^2) by positivity) hlogP
        dsimp only [C₂]
        nlinarith only [hh]
      _ ≤ _ := by gcongr; linarith only [hC₁]

#print axioms exists_displacement_cardinality_majorants

private theorem exists_displacement_source_bands
    {ε l b a x : ℝ} (hε : 0 < ε) (hl : 0 < l) (hb : 0 < b) (ha : 0 < a)
    (hx : 0 ≤ x) :
    ∃ Cd ≥ (1:ℝ), ∃ Cf > (0:ℝ), ∀ (ι : Type*) [DecidableEq ι]
      (S : Finset ι) (f : ℝ → ℝ) (k : ι → ℤ) (H : ι → ℕ)
      (s : ℤ) (A B P U : ℝ),
      0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U*Real.sqrt U → b ≤ P*U →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let F := b*U/P
      let lam := a*U/P
      let X := x*P*U
      (∀ t∈Icc A B, ContDiffAt ℝ 5 f t) →
      (∀ t∈Icc A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U) →
      (∀ t∈Icc A B, -F ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
      (∀ t∈Icc A B, |iteratedDeriv 2 f t/2| ≤ X) →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ 1) →
      (∀ i∈S, H i ≤ N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2)) ⊆ Icc A B) →
      ∃ r : ι → ℚ,
        (∀ Q₀ : ℕ, 2 ≤ Q₀ →
          let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
          ((S.filter (fun i => Q₀ ≤ (r i).den)).card:ℝ) ≤
            4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1))) ∧
        (∀ j : ℕ,
          let Q : ℕ := 2^(j+1)
          let G := (S.filter (fun i => (r i).den ≤ N)).filter (fun i => Nat.log 2 (r i).den=j)
          let Z := (G.card:ℝ)
          let Zd := 4*(Q:ℝ)*(2*X*Q+1)
          let D := 16/(L*(N:ℝ)*(Q:ℝ))
          let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))
          Z ≤ Zd ∧
          (1 ≤ j → Z ≤ 4*(X+1)*D^2+D*(2+Real.log (D+1))) ∧
          (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
            Cd*Zd*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+Err) ∧
          (12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
            let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
            let V := 756*U/L
            let W := 1+32/(L*(Q:ℝ)^2*N)
            let d := L*(Q:ℝ)*N/12
            let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
              (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
            let R := Z+(P*U^((3:ℝ)/2)+P^2*U^((5:ℝ)/2)+P^2*U^((13:ℝ)/6)+P*U^((5:ℝ)/4))*
              (1+Real.log P)
            (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
              Cf*(Loss*(2*Z)^10*R+(Z*Err)^12))) := by
  classical
  obtain ⟨Cd,hCd,hdirect⟩ := exists_bourgain_C4_low_denominator_source
  obtain ⟨Cf,hCf,hfrozenSource⟩ := exists_displacement_scaled_frozen_source hε hl hb ha
  refine ⟨Cd,hCd,Cf,hCf,?_⟩
  intro ι instι S f k H s A B P U hP hU hUsmall hK hbPU N L F lam X
    hf hthree hfour hcurv hmul hH base hbuffer
  have hN : 0 < N := (displacement_block_scale hU hUsmall).1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hf₄ t (ht : t∈Icc A B) : ContDiffAt ℝ 4 f t := (hf t ht).of_le (by norm_num)
  have hfourAbs t (ht : t∈Icc A B) : |iteratedDeriv 4 f t| ≤ F := by
    have hh := hfour t ht
    rw [abs_of_neg (by linarith only [hh.2,hlam])]
    linarith only [hh.1]
  obtain ⟨r,z,hgeo,hlevel,htail⟩ := displacement_minimal_source_family S f k N s hN hL hX
    (fun t ht => (hf t ht).of_le (by norm_num)) (fun t ht => (hthree t ht).1) hcurv hmul hbuffer
  refine ⟨r,htail,?_⟩
  intro j Q G Z Zd D Err
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hGS : G ⊆ S := fun i hi =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hmulG n : (G.filter (fun i => k i=n)).card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset_filter _ hGS)).trans (hmul n)
  have hqdata i (hi : i∈G) :
      (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧ (r i).den ≤ N := by
    obtain ⟨hi',hj⟩ := Finset.mem_filter.mp hi
    have hlo := Nat.pow_log_le_self 2 (r i).pos.ne'
    have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) (r i).den
    rw [hj] at hlo hhi
    refine ⟨hhi.le,?_,(Finset.mem_filter.mp hi').2⟩
    calc
      Q=2*2^j := by dsimp only [Q]; rw [pow_succ,Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ hlo
  have hsmall := displacement_taylor_smallness hb hP hU hUsmall hbPU
  have hdir := hdirect ι G f r z (fun i => round (z i)) k H N Q 1 s A B L F U X
    hN hQ hL hF hU hX hsmall.1 hsmall.2 hf₄ hthree hfourAbs
    (fun i hi => (hgeo i (hGS hi)).1)
    (fun i hi => (hgeo i (hGS hi)).2.2.2)
    (fun i hi => (hgeo i (hGS hi)).2.1)
    (fun i hi => (hgeo i (hGS hi)).2.2.1)
    hmulG (fun i hi => hH i (hGS hi)) hqdata
    (fun i hi => hlevel i (hGS hi))
    (fun i hi => hcurv _ ⟨(hgeo i (hGS hi)).1.1.le,(hgeo i (hGS hi)).1.2.le⟩)
  dsimp only at hdir
  simp only [Nat.cast_one,mul_one] at hdir
  refine ⟨hdir.1,?_,?_,?_⟩
  · intro hj
    have htwo : 2 ≤ 2^j := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hj
    have hsubset : G ⊆ S.filter (fun i => 2^j ≤ (r i).den) := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨hGS hi,?_⟩
      have hh := Nat.pow_log_le_self 2 (r i).pos.ne'
      rw [(Finset.mem_filter.mp hi).2] at hh
      exact hh
    have hh := (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans (htail (2^j) htwo)
    have he : 8/(L*(N:ℝ)*(2^j:ℕ))=D := by
      dsimp only [D,Q]
      rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      ring
    simpa only [he] using hh
  · dsimp only [Err,Zd]
    convert hdir.2 using 1
    ring
  · intro hdual hfrozen M V W d Loss R
    exact hfrozenSource ι G f r z (fun i => round (z i)) k H Q s A B P U
      hQ hP hU hUsmall hK hbPU hf hthree hfour
      (fun i hi => (hgeo i (hGS hi)).1)
      (fun i hi => (hgeo i (hGS hi)).2.2.2)
      (fun i hi => (hgeo i (hGS hi)).2.1)
      (fun i hi => (hgeo i (hGS hi)).2.2.1)
      hmulG (fun i hi => hH i (hGS hi)) hqdata
      (fun i hi => hlevel i (hGS hi)) hdual hfrozen

#print axioms exists_displacement_source_bands

private theorem displacement_cardinality_geometric
    {U Q B Z : ℝ} (hU : 0 ≤ U) (hQ : 0 < Q) (hZ : 0 ≤ Z)
    (hlo : Z ≤ B*U*Q^2) (hhi : Z*Q^2 ≤ B) : Z ≤ B*Real.sqrt U := by
  have hB : 0 ≤ B := (mul_nonneg hZ (sq_nonneg Q)).trans hhi
  have hh := mul_le_mul hlo hhi (mul_nonneg hZ (sq_nonneg Q)) (by positivity : 0 ≤ B*U*Q^2)
  have hsq : Z^2 ≤ B^2*U := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hQ)).mp
    nlinarith only [hh]
  apply (sq_le_sq₀ hZ (mul_nonneg hB (Real.sqrt_nonneg U))).mp
  rwa [mul_pow,Real.sq_sqrt hU]

#print axioms displacement_cardinality_geometric

private theorem displacement_tail_two_terms {P U : ℝ}
    (hP : 0 ≤ P) (hU : 0 < U) (hU1 : U ≤ 1) :
    P*U^((3:ℝ)/2)+P^2*U^((5:ℝ)/2)+P^2*U^((13:ℝ)/6)+P*U^((5:ℝ)/4) ≤
      2*(P*Real.sqrt U+P^2*U^((13:ℝ)/6)) := by
  have h₁ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hU hU1 (by norm_num : (1:ℝ)/2 ≤ 3/2)) hP
  have h₂ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hU hU1 (by norm_num : (13:ℝ)/6 ≤ 5/2)) (sq_nonneg P)
  have h₃ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hU hU1 (by norm_num : (1:ℝ)/2 ≤ 5/4)) hP
  rw [Real.sqrt_eq_rpow]
  linarith only [h₁,h₂,h₃]

private theorem displacement_two_term_product {P U : ℝ} (hU : 0 < U) :
    P^10*Real.sqrt U*(P*Real.sqrt U+P^2*U^((13:ℝ)/6)) =
      P^11*U+P^12*U^((8:ℝ)/3) := by
  have hp : Real.sqrt U*U^((13:ℝ)/6)=U^((8:ℝ)/3) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hU]
    norm_num
  calc
    _ = P^11*(Real.sqrt U)^2+P^12*(Real.sqrt U*U^((13:ℝ)/6)) := by ring
    _ = _ := by rw [Real.sq_sqrt hU.le,hp]

#print axioms displacement_tail_two_terms
#print axioms displacement_two_term_product

private theorem exists_displacement_frozen_error_majorant {l : ℝ} (hl : 0 < l) :
    ∃ C > (0:ℝ), ∀ (P U Q : ℝ),
      0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U → 1 ≤ Q →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(l*U*(N:ℝ)^2)+
        Real.sqrt (12/(l*U*(N:ℝ)*Q)) ≤ C*U^(-(1:ℝ)/4)*(1+Real.log P) := by
  let L₀ := 1+Real.log 6
  let C := Real.sqrt 3*L₀+864/l+12/Real.sqrt l
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hL₀ : 0 < L₀ := by dsimp only [L₀]; positivity
  have hrootl : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro P U Q hP hU hUsmall hPU hQ N
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hP1 : 1 ≤ P := hPU.trans (by nlinarith only [mul_le_mul_of_nonneg_left hU1 hP.le])
  have hQp : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hblock := displacement_block_scale hU hUsmall
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hblock.1
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hblock.1
  let v := Real.sqrt U
  let w := U^(-(1:ℝ)/4)
  have hv : 0 < v := Real.sqrt_pos.mpr hU
  have hw : 0 < w := Real.rpow_pos_of_pos hU _
  have hvsq : v^2=U := Real.sq_sqrt hU.le
  have hw2 : w^2=1/v := by
    calc
      _ = U^(-(1:ℝ)/2) := by
        dsimp only [w]
        rw [←Real.rpow_mul_natCast hU.le]
        congr 1
        norm_num
      _ = _ := by
        rw [show (-(1:ℝ)/2)= -((1:ℝ)/2) by ring,Real.rpow_neg hU.le]
        rw [←Real.sqrt_eq_rpow]
        simp only [one_div,v]
  have hw1 : 1 ≤ w := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_ge hU hU1 (by norm_num : (-(1:ℝ)/4) ≤ 0))
  have hNinv : (N:ℝ) ≤ 1/v := by
    apply (le_div_iff₀ hv).mpr
    linarith only [hblock.2.2.1]
  have hUP : U ≤ v := by
    have hs : v ≤ 1 := Real.sqrt_le_one.mpr hU1
    nlinarith only [hvsq,hs,hv.le]
  have hNP : (N:ℝ) ≤ P := by
    have hh := mul_le_mul_of_nonneg_left hUP hNp.le
    have hn : (N:ℝ)*v ≤ 1/10 := hblock.2.2.1
    apply (mul_le_mul_iff_right₀ hU).mp
    nlinarith only [hh,hn,hPU]
  have hlogP := Real.log_nonneg hP1
  have hlogN : 0 ≤ Real.log (6*(N:ℝ)) := Real.log_nonneg (by linarith only [hN1])
  have hlogBound : Real.log (6*(N:ℝ)) ≤ L₀*(1+Real.log P) := by
    have hh := Real.log_le_log (by positivity : 0 < 6*(N:ℝ))
      (mul_le_mul_of_nonneg_left hNP (by norm_num : (0:ℝ) ≤ 6))
    rw [Real.log_mul (by norm_num : (6:ℝ) ≠ 0) hP.ne'] at hh
    dsimp only [L₀]
    nlinarith only [hh,hlogP,mul_nonneg hlog6 hlogP]
  have hsqrtN : Real.sqrt (3*(N:ℝ)) ≤ Real.sqrt 3*w := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity),mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),hw2]
    exact mul_le_mul_of_nonneg_left hNinv (by norm_num)
  have hunit : 6/(l*U*(N:ℝ)^2) ≤ 864/l := by
    have hh := mul_le_mul_of_nonneg_left hblock.2.2.2.1 hl.le
    have hden : l/144 ≤ l*U*(N:ℝ)^2 := by nlinarith only [hh]
    calc
      _ ≤ 6/(l/144) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = _ := by field_simp; norm_num
  have hUH : v/12 ≤ U*(N:ℝ) := by
    calc
      _ = v*(1/12) := by ring
      _ ≤ v*((N:ℝ)*v) := mul_le_mul_of_nonneg_left hblock.2.1 hv.le
      _ = v^2*N := by ring
      _ = _ := by rw [hvsq]
  have hden : l*v/12 ≤ l*U*(N:ℝ)*Q := by
    have hh := mul_le_mul_of_nonneg_left hUH hl.le
    have hq := le_mul_of_one_le_right (show 0 ≤ l*U*(N:ℝ) by positivity) hQ
    nlinarith only [hh,hq]
  have hlast : Real.sqrt (12/(l*U*(N:ℝ)*Q)) ≤ (12/Real.sqrt l)*w := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity),mul_pow,div_pow,Real.sq_sqrt hl.le,hw2]
    have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 12)
      (show 0 < l*v/12 by positivity) hden
    convert hh using 1
    field_simp
  have hlog1 : 1 ≤ 1+Real.log P := by linarith only [hlogP]
  have hunit' : 6/(l*U*(N:ℝ)^2) ≤ (864/l)*w*(1+Real.log P) := by
    calc
      _ ≤ 864/l := hunit
      _ ≤ _ := by
        have hh := mul_le_mul hw1 hlog1 (by norm_num : (0:ℝ) ≤ 1) hw.le
        have hc := mul_le_mul_of_nonneg_left hh (show 0 ≤ 864/l by positivity)
        nlinarith only [hc]
  have hfirst := mul_le_mul hsqrtN hlogBound hlogN (by positivity : 0 ≤ Real.sqrt 3*w)
  have hlast' := hlast.trans (le_mul_of_one_le_right
    (show 0 ≤ (12/Real.sqrt l)*w by positivity) hlog1)
  change _ ≤ C*w*(1+Real.log P)
  dsimp only [C]
  nlinarith only [hfirst,hunit',hlast']

#print axioms exists_displacement_frozen_error_majorant

private theorem exists_displacement_uniform_frozen_rhs
    {l ε Cc : ℝ} (hl : 0 < l) (hε : 0 < ε) (hCc : 1 ≤ Cc) :
    ∃ C > (0:ℝ), ∀ (P U Z : ℝ) (Q : ℕ),
      0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U → 0 ≤ Z → 0 < Q → (Q:ℝ) ≤ P →
      Z ≤ Cc*P*U*(Q:ℝ)^2 → Z ≤ Cc*(P/(Q:ℝ)^2)*(1+Real.log P) →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let M : ℕ := ⌈63*U*(Q:ℝ)*(N:ℝ)^2⌉₊+1
      let V := 756*U/L
      let W := 1+32/(L*(Q:ℝ)^2*N)
      let d := L*(Q:ℝ)*N/12
      let Loss := (5*W)^11*W^2*(6*(3+8*Real.pi*V)*(1+Real.log M))^12*
        (2/d)^6*(M:ℝ)^((12:ℝ)+ε)
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
        Real.sqrt (12/(L*(N:ℝ)*Q))
      let R := Z+(P*U^((3:ℝ)/2)+P^2*U^((5:ℝ)/2)+P^2*U^((13:ℝ)/6)+P*U^((5:ℝ)/4))*
        (1+Real.log P)
      Loss*(2*Z)^10*R+(Z*Err)^12 ≤
        C*P^ε*(1+Real.log P)^24*(P^11*U+P^12*U^((8:ℝ)/3)) := by
  obtain ⟨Cl,hCl,hloss⟩ := exists_displacement_frozen_loss_bound hl hε
  obtain ⟨Ce,hCe,herror⟩ := exists_displacement_frozen_error_majorant hl
  let C := Cl*Cc^10*(Cc+2)+(Cc*Ce)^12
  have hCcp : 0 < Cc := lt_of_lt_of_le zero_lt_one hCc
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro P U Z Q hP hU hUsmall hPU hZ hQ hQP hZlo hZhi N L M V W d Loss Err R
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hP1 : 1 ≤ P := hPU.trans (by nlinarith only [mul_le_mul_of_nonneg_left hU1 hP.le])
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  let J := 1+Real.log P
  let B := Cc*P*J
  let V₂ := P*Real.sqrt U+P^2*U^((13:ℝ)/6)
  let E := P^11*U+P^12*U^((8:ℝ)/3)
  have hlogP := Real.log_nonneg hP1
  have hJ1 : 1 ≤ J := by dsimp only [J]; linarith only [hlogP]
  have hJ : 0 < J := lt_of_lt_of_le zero_lt_one hJ1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hV₂ : 0 ≤ V₂ := by dsimp only [V₂]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hZlo' : Z ≤ B*U*(Q:ℝ)^2 := by
    calc
      _ ≤ Cc*P*U*(Q:ℝ)^2 := hZlo
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right (show 0 ≤ Cc*P*U*(Q:ℝ)^2 by positivity) hJ1
        dsimp only [B]
        nlinarith only [hh]
  have hZhi' : Z*(Q:ℝ)^2 ≤ B := by
    have hh := mul_le_mul_of_nonneg_right hZhi (sq_nonneg (Q:ℝ))
    convert hh using 1
    dsimp only [B,J]
    field_simp
  have hZgeo : Z ≤ Cc*P*J*Real.sqrt U :=
    displacement_cardinality_geometric hU.le hQr hZ hZlo' hZhi'
  have hR : R ≤ (Cc+2)*V₂*J := by
    have ht := mul_le_mul_of_nonneg_right (displacement_tail_two_terms hP.le hU hU1) hJ.le
    have hv := mul_le_mul_of_nonneg_left
      (show P*Real.sqrt U ≤ V₂ by
        exact le_add_of_nonneg_right (by positivity)) (show 0 ≤ Cc*J by positivity)
    dsimp only [R]
    change Z+_ * J ≤ _
    nlinarith only [ht,hv,hZgeo]
  have hQpow : (Q:ℝ)^ε ≤ P^ε := Real.rpow_le_rpow hQr.le hQP hε.le
  have hlogQ : 0 ≤ 1+Real.log Q := by
    have hh := Real.log_nonneg hQ1
    positivity
  have hlogQP : 1+Real.log Q ≤ J := add_le_add_right (Real.log_le_log hQr hQP) 1
  have hLoss : Loss*(2*Z)^10 ≤ Cl*Cc^10*P^10*Real.sqrt U*P^ε*J^22 := by
    calc
      _ ≤ Cl*B^10*Real.sqrt U*(Q:ℝ)^ε*(1+Real.log Q)^12 :=
        hloss U B Z Q hU hUsmall hZ hQ hZlo' hZhi'
      _ ≤ Cl*B^10*Real.sqrt U*P^ε*J^12 := by gcongr
      _ = _ := by dsimp only [B]; ring
  have hmain₀ := mul_le_mul hLoss hR (by dsimp only [R]; positivity) (by positivity)
  have hprod : P^10*Real.sqrt U*V₂=E := displacement_two_term_product hU
  have hmain : Loss*(2*Z)^10*R ≤ Cl*Cc^10*(Cc+2)*P^ε*J^24*E := by
    calc
      _ ≤ (Cl*Cc^10*P^10*Real.sqrt U*P^ε*J^22)*((Cc+2)*V₂*J) := hmain₀
      _ = Cl*Cc^10*(Cc+2)*P^ε*J^23*(P^10*Real.sqrt U*V₂) := by ring
      _ = Cl*Cc^10*(Cc+2)*P^ε*J^23*E := by rw [hprod]
      _ ≤ _ := by gcongr; norm_num
  have hErr : Err ≤ Ce*U^(-(1:ℝ)/4)*J := herror P U Q hP hU hUsmall hPU hQ1
  have hErr0 : 0 ≤ Err := by
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (displacement_block_scale hU hUsmall).1
    have hlogN := Real.log_nonneg (show 1 ≤ 6*(N:ℝ) by linarith only [hN1])
    dsimp only [Err,L]
    positivity
  have hquarter : Real.sqrt U*U^(-(1:ℝ)/4)=U^((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hU]
    norm_num
  have hZE : Z*Err ≤ Cc*Ce*P*U^((1:ℝ)/4)*J^2 := by
    calc
      _ ≤ (Cc*P*J*Real.sqrt U)*(Ce*U^(-(1:ℝ)/4)*J) :=
        mul_le_mul hZgeo hErr hErr0 (by positivity)
      _ = Cc*Ce*P*(Real.sqrt U*U^(-(1:ℝ)/4))*J^2 := by ring
      _ = _ := by rw [hquarter]
  have hUpow : (U^((1:ℝ)/4))^12=U^(3:ℝ) := by
    rw [←Real.rpow_mul_natCast hU.le]
    norm_num
  have hU3 : U^(3:ℝ) ≤ U^((8:ℝ)/3) :=
    Real.rpow_le_rpow_of_exponent_ge hU hU1 (by norm_num)
  have hPe : 1 ≤ P^ε := Real.one_le_rpow hP1 hε.le
  have herror₀ : (Z*Err)^12 ≤ (Cc*Ce)^12*P^12*U^((8:ℝ)/3)*J^24 := by
    calc
      _ ≤ (Cc*Ce*P*U^((1:ℝ)/4)*J^2)^12 := pow_le_pow_left₀ (by positivity) hZE 12
      _ = (Cc*Ce)^12*P^12*U^(3:ℝ)*J^24 := by rw [mul_pow,mul_pow,mul_pow,hUpow]; ring
      _ ≤ _ := by gcongr
  have herror' : (Z*Err)^12 ≤ (Cc*Ce)^12*P^ε*J^24*E := by
    calc
      _ ≤ (Cc*Ce)^12*P^12*U^((8:ℝ)/3)*J^24 := herror₀
      _ ≤ (Cc*Ce)^12*J^24*E := by
        have hh : P^12*U^((8:ℝ)/3) ≤ E := le_add_of_nonneg_left (by positivity)
        convert mul_le_mul_of_nonneg_left hh (show 0 ≤ (Cc*Ce)^12*J^24 by positivity) using 1
        ring
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right (show 0 ≤ (Cc*Ce)^12*J^24*E by positivity) hPe
        nlinarith only [hh]
  calc
    _ ≤ Cl*Cc^10*(Cc+2)*P^ε*J^24*E+(Cc*Ce)^12*P^ε*J^24*E := add_le_add hmain herror'
    _ = C*P^ε*J^24*E := by dsimp only [C]; ring

#print axioms exists_displacement_uniform_frozen_rhs

private theorem displacement_block_physical_scale {P U : ℝ}
    (hP : 0 < P) (hU : 0 < U) (hUsmall : U ≤ 1/3600)
    (hK : 1 ≤ P*U*Real.sqrt U) :
    1 ≤ P*U ∧ 1 ≤ P ∧ 2*(⌊1/(10*Real.sqrt U)⌋₊:ℝ) ≤ P := by
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hv1 := Real.sqrt_le_one.mpr hU1
  have hPU : 1 ≤ P*U := hK.trans (mul_le_of_le_one_right (by positivity) hv1)
  have hP1 : 1 ≤ P := hPU.trans (mul_le_of_le_one_right hP.le hU1)
  refine ⟨hPU,hP1,?_⟩
  have hUv : U ≤ Real.sqrt U := by
    nlinarith only [Real.sq_sqrt hU.le,hv1,Real.sqrt_nonneg U]
  have hh := (displacement_block_scale hU hUsmall).2.2.1
  have hu := mul_le_mul_of_nonneg_left hUv
    (show 0 ≤ (⌊1/(10*Real.sqrt U)⌋₊:ℝ) by positivity)
  apply (mul_le_mul_iff_right₀ hU).mp
  nlinarith only [hh,hu,hPU]

private theorem exists_displacement_uniform_source_bands
    {ε l b a x : ℝ} (hε : 0 < ε) (hl : 0 < l) (hb : 0 < b) (ha : 0 < a)
    (hx : 0 ≤ x) :
    ∃ Cd ≥ (1:ℝ), ∃ Cf > (0:ℝ), ∀ (ι : Type*) [DecidableEq ι]
      (S : Finset ι) (f : ℝ → ℝ) (k : ι → ℤ) (H : ι → ℕ)
      (s : ℤ) (A B P U : ℝ),
      0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U*Real.sqrt U → b ≤ P*U →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let F := b*U/P
      let lam := a*U/P
      let X := x*P*U
      (∀ t∈Icc A B, ContDiffAt ℝ 5 f t) →
      (∀ t∈Icc A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U) →
      (∀ t∈Icc A B, -F ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
      (∀ t∈Icc A B, |iteratedDeriv 2 f t/2| ≤ X) →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ 1) →
      (∀ i∈S, H i ≤ N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2)) ⊆ Icc A B) →
      ∃ r : ι → ℚ,
        (∀ Q₀ : ℕ, 2 ≤ Q₀ →
          let D₀ := 8/(L*(N:ℝ)*(Q₀:ℝ))
          ((S.filter (fun i => Q₀ ≤ (r i).den)).card:ℝ) ≤
            4*(X+1)*D₀^2+D₀*(2+Real.log (D₀+1))) ∧
        (∀ j : ℕ,
          let Q : ℕ := 2^(j+1)
          let G := (S.filter (fun i => (r i).den ≤ N)).filter (fun i => Nat.log 2 (r i).den=j)
          let Zd := 4*(Q:ℝ)*(2*X*Q+1)
          let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(L*(N:ℝ)^2)+
            Real.sqrt (12/(L*(N:ℝ)*Q))
          (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖) ≤
            Cd*Zd*(3*(N:ℝ)*Real.sqrt (3*U*(Q:ℝ)*N)+Err) ∧
          (1 ≤ j → 12 ≤ L*(Q:ℝ)*(N:ℝ)^2 → 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3 →
            (∑ i∈G, ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
              Cf*P^ε*(1+Real.log P)^24*(P^11*U+P^12*U^((8:ℝ)/3)))) := by
  classical
  obtain ⟨Cd,hCd,Cf,hCf,hsource⟩ := exists_displacement_source_bands hε hl hb ha hx
  obtain ⟨Cc,hCc,hcard⟩ := exists_displacement_cardinality_majorants hl hx
  obtain ⟨Cr,hCr,hrhs⟩ := exists_displacement_uniform_frozen_rhs hl hε hCc
  refine ⟨Cd,hCd,Cf*Cr,by positivity,?_⟩
  intro ι instι S f k H s A B P U hP hU hUsmall hK hbPU N L F lam X
    hf hthree hfour hcurv hmul hH base hbuffer
  obtain ⟨r,htail,hbands⟩ := hsource ι S f k H s A B P U hP hU hUsmall hK hbPU
    hf hthree hfour hcurv hmul hH hbuffer
  refine ⟨r,htail,?_⟩
  intro j Q G Zd Err
  have hband := hbands j
  refine ⟨hband.2.2.1,?_⟩
  intro hj hdual hfrozen
  by_cases hempty : G=∅
  · simp only [hempty,Finset.sum_empty,zero_pow (by norm_num : (12:ℕ)≠0)]
    positivity
  have hscale := displacement_block_physical_scale hP hU hUsmall hK
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hi',hlog⟩ := Finset.mem_filter.mp hi
  have hiN := (Finset.mem_filter.mp hi').2
  have hp := Nat.pow_log_le_self 2 (r i).pos.ne'
  rw [hlog] at hp
  have hQN : (Q:ℝ) ≤ 2*(N:ℝ) := by
    have hh : Q ≤ 2*N := by
      calc
        Q=2*2^j := by dsimp only [Q]; rw [pow_succ,Nat.mul_comm]
        _ ≤ 2*N := Nat.mul_le_mul_left _ (hp.trans hiN)
    exact_mod_cast hh
  have hc := hcard P U Q hP hU hUsmall hscale.1 hQ1 hQN
  have hZlo : (G.card:ℝ) ≤ Cc*P*U*(Q:ℝ)^2 := hband.1.trans hc.1
  have hZhi : (G.card:ℝ) ≤ Cc*(P/(Q:ℝ)^2)*(1+Real.log P) :=
    (hband.2.1 hj).trans hc.2
  have hh := hrhs P U G.card Q hP hU hUsmall hscale.1 (by positivity)
    hQ (hQN.trans hscale.2.2) hZlo hZhi
  have hs := hband.2.2.2 hdual hfrozen
  have hm := mul_le_mul_of_nonneg_left hh hCf.le
  exact hs.trans (by convert hm using 1; ring)

#print axioms displacement_block_physical_scale
#print axioms exists_displacement_uniform_source_bands

private theorem exists_displacement_small_band_cutoff {l : ℝ} (hl : 0 < l) :
    ∃ C ≥ (1:ℝ), ∀ U Q : ℝ,
      0 < U → U ≤ 1/3600 → 0 < Q →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      (Q ≤ 2 ∨ l*U*Q*(N:ℝ)^2 < 12 ∨ (l*U)^2*Q^3*(N:ℝ)^3 < 384) →
      Q ≤ C*U^(-(1:ℝ)/6) := by
  let C := 2+1728/l+663552/l^2
  have hA : 0 < 663552/l^2 := by positivity
  have hB : 0 < 1728/l := by positivity
  have hC1 : 1 ≤ C := by dsimp only [C]; linarith only [hA,hB]
  refine ⟨C,hC1,?_⟩
  intro U Q hU hUsmall hQ N hcase
  have hblock := displacement_block_scale hU hUsmall
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr hblock.1
  have hw : 0 < U^((1:ℝ)/6) := Real.rpow_pos_of_pos hU _
  have hinv : U^(-(1:ℝ)/6)=(U^((1:ℝ)/6))⁻¹ := by
    rw [neg_div,Real.rpow_neg hU.le]
  have huinv : 1 ≤ U^(-(1:ℝ)/6) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hU hU1 (by norm_num : (-(1:ℝ)/6) ≤ 0)
  have hCbase : C ≤ C*U^(-(1:ℝ)/6) := le_mul_of_one_le_right (by linarith only [hC1]) huinv
  rcases hcase with hlow|hdual|hfrozen
  · exact (hlow.trans (by dsimp only [C]; linarith only [hA,hB])).trans hCbase
  · have hh := mul_le_mul_of_nonneg_left hblock.2.2.2.1 (show 0 ≤ l*Q by positivity)
    have hq : Q < 1728/l := by
      apply (lt_div_iff₀ hl).mpr
      nlinarith only [hh,hdual]
    exact (hq.le.trans (by dsimp only [C]; linarith only [hA])).trans hCbase
  · let v := Real.sqrt U
    have hv : 0 < v := Real.sqrt_pos.mpr hU
    have hv2 : v^2=U := Real.sq_sqrt hU.le
    have hv3 : (U^((1:ℝ)/6))^3=v := by
      rw [←Real.rpow_mul_natCast hU.le]
      norm_num
      exact (Real.sqrt_eq_rpow U).symm
    have hn3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/12) hblock.2.1 3
    have hden : v/1728 ≤ U^2*(N:ℝ)^3 := by
      have hh : v*(1/12)^3 ≤ v*((N:ℝ)*v)^3 := mul_le_mul_of_nonneg_left hn3 hv.le
      have hid : ((N:ℝ)*v)^3*v=U^2*(N:ℝ)^3 := by
        calc
          _ = (v^2)^2*(N:ℝ)^3 := by ring
          _ = _ := by rw [hv2]
      calc
        _ = v*(1/12)^3 := by ring
        _ ≤ v*((N:ℝ)*v)^3 := hh
        _ = ((N:ℝ)*v)^3*v := by ring
        _ = _ := hid
    have hh := mul_le_mul_of_nonneg_left hden (show 0 ≤ l^2*Q^3 by positivity)
    have hq3 : Q^3*v ≤ 663552/l^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
      nlinarith only [hh,hfrozen]
    have hC3 : 663552/l^2 ≤ C^3 := by
      calc
        _ ≤ C := by dsimp only [C]; linarith only [hB]
        _ ≤ _ := by simpa using pow_le_pow_right₀ hC1 (by norm_num : 1 ≤ 3)
    have hqw : Q*U^((1:ℝ)/6) ≤ C := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ Q*U^((1:ℝ)/6))
        (by linarith only [hC1] : 0 ≤ C) (by norm_num : (3:ℕ)≠0)).mp
      rw [mul_pow,hv3]
      exact hq3.trans hC3
    rw [hinv,←div_eq_mul_inv]
    exact (le_div_iff₀ hw).mpr hqw

#print axioms exists_displacement_small_band_cutoff

private theorem exists_displacement_small_band_majorant
    {l x K : ℝ} (hl : 0 < l) (hx : 0 ≤ x) (hK : 1 ≤ K) :
    ∃ C > (0:ℝ), ∀ P U Q : ℝ,
      0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U → 1 ≤ Q → Q ≤ K*U^(-(1:ℝ)/6) →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let X := x*P*U
      let Err := Real.sqrt (3*(N:ℝ))*Real.log (6*(N:ℝ))+6/(l*U*(N:ℝ)^2)+
        Real.sqrt (12/(l*U*(N:ℝ)*Q))
      4*Q*(2*X*Q+1)*(3*(N:ℝ)*Real.sqrt (3*U*Q*N)+Err) ≤
        C*P*U^((1:ℝ)/3)*(1+Real.log P) := by
  obtain ⟨Ce,hCe,herror⟩ := exists_displacement_frozen_error_majorant hl
  let C := (8*x+4)*(3*Real.sqrt 3+Ce)*K^((5:ℝ)/2)
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro P U Q hP hU hUsmall hPU hQ hQbound N X Err
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hP1 : 1 ≤ P := hPU.trans (mul_le_of_le_one_right hP.le hU1)
  have hQp : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hblock := displacement_block_scale hU hUsmall
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr hblock.1
  have hNbound : (N:ℝ) ≤ U^(-(1:ℝ)/2) := by
    rw [neg_div,Real.rpow_neg hU.le,←Real.sqrt_eq_rpow,←one_div]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hU)).mpr
    linarith only [hblock.2.2.1]
  have hmain : 3*(N:ℝ)*Real.sqrt (3*U*Q*N) ≤
      3*Real.sqrt 3*U^(-(1:ℝ)/4)*Q^((1:ℝ)/2) := by
    calc
      _ ≤ 3*U^(-(1:ℝ)/2)*Real.sqrt (3*U*Q*U^(-(1:ℝ)/2)) := by gcongr
      _ = _ := by
        rw [Real.sqrt_eq_rpow]
        rw [Real.mul_rpow (by positivity : 0 ≤ 3*U*Q) (by positivity : 0 ≤ U^(-(1:ℝ)/2)),
          Real.mul_rpow (by positivity : 0 ≤ 3*U) hQp.le,
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hU.le,
          ←Real.rpow_mul hU.le,Real.sqrt_eq_rpow]
        have he : U^(-(1:ℝ)/2)*(U^((1:ℝ)/2)*U^((-(1:ℝ)/2)*((1:ℝ)/2)))=U^(-(1:ℝ)/4) := by
          rw [←Real.rpow_add hU,←Real.rpow_add hU]
          norm_num
        calc
          _ = 3*(3:ℝ)^((1:ℝ)/2)*(U^(-(1:ℝ)/2)*
            (U^((1:ℝ)/2)*U^((-(1:ℝ)/2)*((1:ℝ)/2))))*Q^((1:ℝ)/2) := by ring
          _ = _ := by rw [he]
  let J := 1+Real.log P
  have hJ1 : 1 ≤ J := by
    have hh := Real.log_nonneg hP1
    dsimp only [J]
    linarith only [hh]
  have hJ : 0 < J := lt_of_lt_of_le zero_lt_one hJ1
  have hQhalf : 1 ≤ Q^((1:ℝ)/2) := Real.one_le_rpow hQ (by norm_num)
  have herror' : Err ≤ Ce*U^(-(1:ℝ)/4)*Q^((1:ℝ)/2)*J := by
    calc
      _ ≤ Ce*U^(-(1:ℝ)/4)*J := herror P U Q hP hU hUsmall hPU hQ
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right (show 0 ≤ Ce*U^(-(1:ℝ)/4)*J by positivity) hQhalf
        nlinarith only [hh]
  have hmain' : 3*(N:ℝ)*Real.sqrt (3*U*Q*N)+Err ≤
      (3*Real.sqrt 3+Ce)*U^(-(1:ℝ)/4)*Q^((1:ℝ)/2)*J := by
    have hh := hmain.trans (le_mul_of_one_le_right (by positivity) hJ1)
    nlinarith only [hh,herror']
  have hcount : 4*Q*(2*X*Q+1) ≤ (8*x+4)*P*U*Q^2 := by
    have hh : 1 ≤ P*U*Q := by
      simpa only [one_mul] using mul_le_mul hPU hQ (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ P*U)
    dsimp only [X]
    nlinarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*Q by positivity)]
  have hpowQ : Q^2*Q^((1:ℝ)/2) ≤ K^((5:ℝ)/2)*U^(-(5:ℝ)/12) := by
    calc
      _ = Q^((5:ℝ)/2) := by
        rw [←Real.rpow_natCast Q 2,←Real.rpow_add hQp]
        norm_num
      _ ≤ (K*U^(-(1:ℝ)/6))^((5:ℝ)/2) := Real.rpow_le_rpow hQp.le hQbound (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow hKp.le (by positivity),←Real.rpow_mul hU.le]
        norm_num
  have hUproduct : U*U^(-(1:ℝ)/4)*U^(-(5:ℝ)/12)=U^((1:ℝ)/3) := by
    calc
      _ = U^(1:ℝ)*U^(-(1:ℝ)/4)*U^(-(5:ℝ)/12) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hU,←Real.rpow_add hU]; norm_num
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hblock.1
  have hlogN := Real.log_nonneg (show 1 ≤ 6*(N:ℝ) by linarith only [hN1])
  calc
    _ ≤ ((8*x+4)*P*U*Q^2)*((3*Real.sqrt 3+Ce)*U^(-(1:ℝ)/4)*Q^((1:ℝ)/2)*J) :=
      mul_le_mul hcount hmain' (by dsimp only [Err]; positivity) (by positivity)
    _ = ((8*x+4)*(3*Real.sqrt 3+Ce)*P*(U*U^(-(1:ℝ)/4))*J)*(Q^2*Q^((1:ℝ)/2)) := by ring
    _ ≤ ((8*x+4)*(3*Real.sqrt 3+Ce)*P*(U*U^(-(1:ℝ)/4))*J)*
        (K^((5:ℝ)/2)*U^(-(5:ℝ)/12)) := mul_le_mul_of_nonneg_left hpowQ (by positivity)
    _ = C*P*(U*U^(-(1:ℝ)/4)*U^(-(5:ℝ)/12))*J := by dsimp only [C]; ring
    _ = _ := by rw [hUproduct]

#print axioms exists_displacement_small_band_majorant

private theorem exists_displacement_tail_majorant {l x : ℝ} (hl : 0 < l) (hx : 0 ≤ x) :
    ∃ C > (0:ℝ), ∀ P U : ℝ,
      0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let D := 8/(l*U*(N:ℝ)*((N:ℝ)+1))
      1+23*(N:ℝ) ≤ 24*P*Real.sqrt U ∧
      (N:ℝ)*(4*(x*P*U+1)*D^2+D*(2+Real.log (D+1))) ≤ C*P*Real.sqrt U := by
  let d := 1152/l
  let C := 4*(x+1)*d^2+d*(2+Real.log (d+1))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hlogd : 0 ≤ Real.log (d+1) := Real.log_nonneg (by linarith only [hd])
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro P U hP hU hUsmall hPU N D
  have hblock := displacement_block_scale hU hUsmall
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr hblock.1
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  let v := Real.sqrt U
  have hv : 0 < v := Real.sqrt_pos.mpr hU
  have hv2 : v^2=U := Real.sq_sqrt hU.le
  have hv1 : v ≤ 1 := Real.sqrt_le_one.mpr hU1
  have hUv : U ≤ v := by nlinarith only [hv2,hv1,hv.le]
  have hPv1 : 1 ≤ P*v := hPU.trans (mul_le_mul_of_nonneg_left hUv hP.le)
  have hNPv : (N:ℝ) ≤ P*v := by
    apply (mul_le_mul_iff_right₀ hv).mp
    calc
      _ = (N:ℝ)*v := by ring
      _ ≤ 1/10 := hblock.2.2.1
      _ ≤ P*U := by linarith only [hPU]
      _ = P*v^2 := by rw [hv2]
      _ = _ := by ring
  refine ⟨by nlinarith only [hNPv,hPv1],?_⟩
  have hD : 0 < D := by dsimp only [D]; positivity
  have hden : l/144 ≤ l*U*(N:ℝ)*((N:ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_left hblock.2.2.2.1 hl.le
    have ht : 0 ≤ l*U*(N:ℝ) := by positivity
    nlinarith only [hh,ht]
  have hDhi : D ≤ d := by
    calc
      _ ≤ 8/(l/144) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = _ := by dsimp only [d]; field_simp; norm_num
  have hlogD : 0 ≤ Real.log (D+1) := Real.log_nonneg (by linarith only [hD])
  have hlogDhi : Real.log (D+1) ≤ Real.log (d+1) :=
    Real.log_le_log (by positivity) (by linarith only [hDhi])
  have hX : x*P*U+1 ≤ (x+1)*P*U := by nlinarith only [hPU]
  have hcount : 4*(x*P*U+1)*D^2+D*(2+Real.log (D+1)) ≤ C*P*U := by
    have hfirst : 4*(x*P*U+1)*D^2 ≤ 4*((x+1)*P*U)*d^2 := by gcongr
    have hsecond : D*(2+Real.log (D+1)) ≤ d*(2+Real.log (d+1)) := by gcongr
    have hsecond' := hsecond.trans (le_mul_of_one_le_right (by positivity) hPU)
    dsimp only [C]
    nlinarith only [hfirst,hsecond']
  have hNU : (N:ℝ)*U ≤ v := by
    calc
      _ = (N:ℝ)*v^2 := by rw [hv2]
      _ = ((N:ℝ)*v)*v := by ring
      _ ≤ (1/10)*v := mul_le_mul_of_nonneg_right hblock.2.2.1 hv.le
      _ ≤ v := by linarith only [hv.le]
  calc
    _ ≤ (N:ℝ)*(C*P*U) := mul_le_mul_of_nonneg_left hcount hN.le
    _ = C*P*((N:ℝ)*U) := by ring
    _ ≤ C*P*v := mul_le_mul_of_nonneg_left hNU (by positivity)

#print axioms exists_displacement_tail_majorant

-- Existing production finite-sum and dyadic helpers, copied only for private visibility.
private theorem sum_by_denominator_bands {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (q : ι → ℕ) (w : ι → ℝ) (N : ℕ) :
    (∑ i∈S,w i) =
      (∑ i∈S.filter (fun i => N+1 ≤ q i),w i)+
      ∑ j∈Finset.range (Nat.log 2 N+1),
        ∑ i∈(S.filter (fun i => q i ≤ N)).filter (fun i => Nat.log 2 (q i)=j),w i := by
  have hmap : ∀ i∈S.filter (fun i => q i ≤ N),
      Nat.log 2 (q i)∈Finset.range (Nat.log 2 N+1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.log_mono_right (Finset.mem_filter.mp hi).2))
  rw [Finset.sum_fiberwise_of_maps_to hmap w]
  have h := Finset.sum_filter_add_sum_filter_not S (fun i => N+1 ≤ q i) w
  simpa only [Nat.not_le, Nat.lt_succ_iff] using h.symm


private theorem boundary_and_bands_twelfth (B A : ℝ) (g : ℕ → ℝ)
    (J : ℕ) (hB : 0 ≤ B) (hA : 0 ≤ A) (hg : ∀ j,0 ≤ g j) :
    (B+A+∑ j∈Finset.range J,g j)^12 ≤
      ((J:ℝ)+2)^11*(B^12+A^12+∑ j∈Finset.range J,(g j)^12) := by
  let f : ℕ → ℝ := fun j => if j=0 then B else if j=1 then A else g (j-2)
  have hf (j : ℕ) : 0 ≤ f j := by
    dsimp only [f]
    split_ifs
    · exact hB
    · exact hA
    · exact hg _
  have hs (p : ℕ) :
      (∑ j∈Finset.range (2+J),(f j)^p) =
        B^p+A^p+∑ j∈Finset.range J,(g j)^p := by
    rw [Finset.sum_range_add]
    have hne (x : ℕ) : 2+x≠1 := by omega
    simp [Finset.sum_range_succ,f,hne]
  have h := pow_sum_le_card_mul_sum_pow
    (s:=Finset.range (2+J)) (f:=f) (fun j _ => hf j) 11
  have hs1 := hs 1
  simp only [pow_one] at hs1
  rw [hs1,hs 12] at h
  simpa only [Finset.card_range,Nat.cast_add,Nat.cast_ofNat,add_comm (2:ℝ)] using h


private theorem physical_dyadic_geometry
    {K T : ℝ} {N : ℕ} (hK : 1000 ≤ K) (hT : 1 ≤ T)
    (hN : 0<N) (hNT : (N:ℝ) ≤ T) :
    let J := Nat.log 2 N+1
    (J:ℝ)+2 ≤ K*(1+Real.log T) ∧
      ∀ j∈Finset.range J, (1:ℝ) ≤ (2^(j+1):ℕ) ∧ (2^(j+1):ℝ) ≤ 2*(N:ℝ) := by
  intro J
  have hNreal : 0<(N:ℝ) := by exact_mod_cast hN
  have hp : (2:ℝ)^(Nat.log 2 N) ≤ (N:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hN)
  have hh := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) _) hp
  rw [Real.log_pow] at hh
  have hlogtwo : (1:ℝ)/2 ≤ Real.log 2 := by
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hl ⊢
    exact hl
  have hlogN := Real.log_le_log hNreal hNT
  have hlogT := Real.log_nonneg hT
  constructor
  · have hhalf := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg (Nat.log 2 N))
    have hcoef := mul_nonneg (show 0 ≤ K-2 by linarith only [hK]) hlogT
    dsimp only [J]
    rw [Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,hhalf,hlogN,hcoef,hK]
  · intro j hj
    have hjlog : j ≤ Nat.log 2 N := by
      have hh := Finset.mem_range.mp hj
      dsimp only [J] at hh
      omega
    have hQ : 2^(j+1) ≤ 2*N := by
      calc
        _ = 2*2^j := by rw [pow_succ,Nat.mul_comm]
        _ ≤ 2*2^(Nat.log 2 N) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hjlog)
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (Nat.ne_of_gt hN))
    constructor
    · exact_mod_cast (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2) : 1 ≤ 2^(j+1))
    · exact_mod_cast hQ







































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

private theorem displacement_finite_moment_budget
    {B A K : ℝ} (g : ℕ → ℝ) (J : ℕ)
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hg : ∀ j, 0 ≤ g j)
    (hBK : B^12 ≤ K) (hAK : A^12 ≤ K)
    (hgK : ∀ j∈Finset.range J, (g j)^12 ≤ K) :
    (B+A+∑ j∈Finset.range J,g j)^12 ≤ ((J:ℝ)+2)^12*K := by
  have hs : (∑ j∈Finset.range J,(g j)^12) ≤ (J:ℝ)*K := by
    simpa using Finset.sum_le_sum hgK
  calc
    _ ≤ ((J:ℝ)+2)^11*(B^12+A^12+∑ j∈Finset.range J,(g j)^12) :=
      boundary_and_bands_twelfth B A g J hB hA hg
    _ ≤ ((J:ℝ)+2)^11*(((J:ℝ)+2)*K) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [hBK,hAK,hs]
    _ = _ := by ring

private theorem exists_displacement_physical_source_global
    {ε l b a x : ℝ} (hε : 0 < ε) (hl : 0 < l) (hb : 0 < b) (ha : 0 < a)
    (hx : 0 ≤ x) :
    ∃ C > (0:ℝ), ∀ (ι : Type*) [DecidableEq ι]
      (S : Finset ι) (f : ℝ → ℝ) (k : ι → ℤ) (H : ι → ℕ)
      (s : ℤ) (A B P U : ℝ),
      0 < P → 0 < U → U ≤ 1/3600 → 1 ≤ P*U*Real.sqrt U → b ≤ P*U →
      let N := ⌊1/(10*Real.sqrt U)⌋₊
      let L := l*U
      let F := b*U/P
      let lam := a*U/P
      let X := x*P*U
      (∀ t∈Icc A B, ContDiffAt ℝ 5 f t) →
      (∀ t∈Icc A B, L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ 6*U) →
      (∀ t∈Icc A B, -F ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
      (∀ t∈Icc A B, |iteratedDeriv 2 f t/2| ≤ X) →
      (∀ j : ℤ, (S.filter (fun i => k i=j)).card ≤ 1) →
      (∀ i∈S, H i ≤ N) →
      let base := fun i => (s:ℝ)-2*(N:ℝ)+(N:ℝ)*(k i:ℝ)
      (∀ i∈S, Icc (base i-(7*(N:ℝ)+2)) (base i+(7*(N:ℝ)+2)) ⊆ Icc A B) →
      (1+23*(N:ℝ)+∑ i∈S,
        ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖)^12 ≤
        C*P^ε*(1+Real.log P)^36*(P^11*U+P^12*U^((8:ℝ)/3)) := by
  classical
  obtain ⟨Cd,hCd,Cf,hCf,hsource⟩ := exists_displacement_uniform_source_bands hε hl hb ha hx
  obtain ⟨K,hK,hcutoff⟩ := exists_displacement_small_band_cutoff hl
  obtain ⟨Cs,hCs,hsmall⟩ := exists_displacement_small_band_majorant hl hx hK
  obtain ⟨Ct,hCt,htailSize⟩ := exists_displacement_tail_majorant hl hx
  let C₀ := (24:ℝ)^12+Ct^12+Cf+(Cd*Cs)^12
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨1000^12*C₀,by positivity,?_⟩
  intro ι instι S f k H s A B P U hP hU hUsmall hKscale hbPU N L F lam X
    hf hthree hfour hcurv hmul hH base hbuffer
  have hscale := displacement_block_physical_scale hP hU hUsmall hKscale
  have hU1 : U ≤ 1 := by linarith only [hUsmall]
  have hN := (displacement_block_scale hU hUsmall).1
  obtain ⟨r,htail,hband⟩ := hsource ι S f k H s A B P U hP hU hUsmall hKscale hbPU
    hf hthree hfour hcurv hmul hH hbuffer
  let w := fun i => ‖∑ n∈Finset.Ioc (s+(N:ℤ)*k i) (s+(N:ℤ)*k i+H i),(𝐞 (f n):ℂ)‖
  let R := S.filter (fun i => N+1 ≤ (r i).den)
  let g := fun j => ∑ i∈(S.filter (fun i => (r i).den ≤ N)).filter (fun i => Nat.log 2 (r i).den=j),w i
  let J := Nat.log 2 N+1
  let Log := 1+Real.log P
  let E := P^11*U+P^12*U^((8:ℝ)/3)
  let Budget := C₀*P^ε*Log^24*E
  have hlog1 : 1 ≤ Log := by
    have hh := Real.log_nonneg hscale.2.1
    dsimp only [Log]
    linarith only [hh]
  have hLog : 0 < Log := lt_of_lt_of_le zero_lt_one hlog1
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hbudget (c : ℝ) (hc : c ≤ C₀) : c*P^ε*Log^24*E ≤ Budget := by
    dsimp only [Budget]
    gcongr
  have hCdp : 0 ≤ Cd := by linarith only [hCd]
  have hCf₀ : Cf ≤ C₀ := by
    dsimp only [C₀]
    linarith only [pow_nonneg hCt.le 12,pow_nonneg (mul_nonneg hCdp hCs.le) 12]
  have hCs₀ : (Cd*Cs)^12 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [hCf.le,pow_nonneg hCt.le 12]
  have hCt₀ : Ct^12 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [hCf.le,pow_nonneg (mul_nonneg hCdp hCs.le) 12]
  have hCb₀ : (24:ℝ)^12 ≤ C₀ := by
    dsimp only [C₀]
    linarith only [hCf.le,pow_nonneg hCt.le 12,pow_nonneg (mul_nonneg hCdp hCs.le) 12]
  have hw (i : ι) : 0 ≤ w i := norm_nonneg _
  have hwH (i : ι) (hi : i∈S) : w i ≤ N := by
    have hh := norm_sum_integer_Ioc_le (fun n => (𝐞 (f n):ℂ)) (by intro n; simp)
      (a:=s+(N:ℤ)*k i) (b:=s+(N:ℤ)*k i+H i) (by omega)
    have he : ((s+(N:ℤ)*k i+H i:ℤ):ℝ)-(s+(N:ℤ)*k i:ℤ)=H i := by push_cast; ring
    rw [he] at hh
    exact hh.trans (Nat.cast_le.mpr (hH i hi))
  have htail' : (∑ i∈R,w i) ≤ Ct*P*Real.sqrt U := by
    have hq0 : 2 ≤ N+1 := by omega
    have hc := htail (N+1) hq0
    have hs : (∑ i∈R,w i) ≤ (R.card:ℝ)*(N:ℝ) := by
      calc
        _ ≤ ∑ _i∈R,(N:ℝ) := Finset.sum_le_sum (fun i hi => hwH i (Finset.mem_filter.mp hi).1)
        _ = _ := by simp
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (N:ℝ) by positivity)
    have hsize := (htailSize P U hP hU hUsmall hscale.1).2
    simp only [Nat.cast_add,Nat.cast_one] at hm
    change (N:ℝ)*(R.card:ℝ) ≤ _ at hm
    exact hs.trans (by
      calc
        _ = (N:ℝ)*(R.card:ℝ) := by ring
        _ ≤ _ := hm
        _ ≤ _ := hsize)
  have htailMoment : (∑ i∈R,w i)^12 ≤ Budget := by
    have hh : (∑ i∈R,w i) ≤ Ct*P*U^((1:ℝ)/2)*Log := by
      rw [←Real.sqrt_eq_rpow]
      exact htail'.trans (le_mul_of_one_le_right (by positivity) hlog1)
    exact (displacement_elementary_twelfth hscale.2.1 hU hU1 (Finset.sum_nonneg (fun i _ => hw i))
      hε.le (by norm_num : (2:ℝ)/9 ≤ 1/2) hh).trans (hbudget _ hCt₀)
  have hboundary : (1+23*(N:ℝ))^12 ≤ Budget := by
    have hh : 1+23*(N:ℝ) ≤ 24*P*U^((1:ℝ)/2)*Log := by
      rw [←Real.sqrt_eq_rpow]
      exact (htailSize P U hP hU hUsmall hscale.1).1.trans
        (le_mul_of_one_le_right (by positivity) hlog1)
    exact (displacement_elementary_twelfth hscale.2.1 hU hU1 (by positivity)
      hε.le (by norm_num : (2:ℝ)/9 ≤ 1/2) hh).trans (hbudget _ hCb₀)
  have hbands (j : ℕ) : (g j)^12 ≤ Budget := by
    let Q : ℕ := 2^(j+1)
    have hQ1 : (1:ℝ) ≤ Q := by dsimp only [Q]; exact_mod_cast (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2) : 1 ≤ 2^(j+1))
    have hQ : (0:ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ1
    by_cases hlarge : 1 ≤ j ∧ 12 ≤ L*(Q:ℝ)*(N:ℝ)^2 ∧ 384 ≤ L^2*(Q:ℝ)^3*(N:ℝ)^3
    · exact ((hband j).2 hlarge.1 hlarge.2.1 hlarge.2.2).trans (hbudget _ hCf₀)
    have hcases : (Q:ℝ) ≤ 2 ∨ l*U*(Q:ℝ)*(N:ℝ)^2 < 12 ∨ (l*U)^2*(Q:ℝ)^3*(N:ℝ)^3 < 384 := by
      by_cases hj : 1 ≤ j
      · by_cases hd : 12 ≤ L*(Q:ℝ)*(N:ℝ)^2
        · exact Or.inr (Or.inr (lt_of_not_ge (fun hh => hlarge ⟨hj,hd,hh⟩)))
        · exact Or.inr (Or.inl (lt_of_not_ge hd))
      · have hj0 : j=0 := by omega
        left
        simp only [Q,hj0,zero_add,pow_one,Nat.cast_ofNat,le_refl]
    have hcut := hcutoff U Q hU hUsmall hQ hcases
    have hs := hsmall P U Q hP hU hUsmall hscale.1 hQ1 hcut
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ Cd by linarith only [hCd])
    have hg : g j ≤ (Cd*Cs)*P*U^((1:ℝ)/3)*Log := by
      calc
        _ ≤ _ := (hband j).1
        _ ≤ _ := by convert hm using 1 <;> ring
    exact (displacement_elementary_twelfth hscale.2.1 hU hU1 (Finset.sum_nonneg (fun i _ => hw i))
      hε.le (by norm_num : (2:ℝ)/9 ≤ 1/3) hg).trans (hbudget _ hCs₀)
  have hfinite := displacement_finite_moment_budget g J (by positivity)
    (Finset.sum_nonneg (fun i _ => hw i)) (fun j => Finset.sum_nonneg (fun i _ => hw i))
    hboundary htailMoment (fun j _ => hbands j)
  have hJbound : (J:ℝ)+2 ≤ 1000*Log :=
    (physical_dyadic_geometry (by norm_num : (1000:ℝ) ≤ 1000) hscale.2.1 hN
      (by linarith only [hscale.2.2,show (0:ℝ) ≤ N by positivity])).1
  change (1+23*(N:ℝ)+∑ i∈S,w i)^12 ≤ _
  rw [sum_by_denominator_bands S (fun i => (r i).den) w N]
  change (1+23*(N:ℝ)+((∑ i∈R,w i)+∑ j∈Finset.range J,g j))^12 ≤ _
  calc
    _ = (1+23*(N:ℝ)+(∑ i∈R,w i)+∑ j∈Finset.range J,g j)^12 := by congr 1; ring
    _ ≤ ((J:ℝ)+2)^12*Budget := hfinite
    _ ≤ (1000*Log)^12*Budget := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hJbound 12) (by dsimp only [Budget]; positivity)
    _ = (1000^12*C₀)*P^ε*(1+Real.log P)^36*(P^11*U+P^12*U^((8:ℝ)/3)) := by
      change _ = (1000^12*C₀)*P^ε*Log^36*E
      dsimp only [Budget]
      ring

#print axioms displacement_finite_moment_budget
#print axioms exists_displacement_physical_source_global

private theorem displacement_physical_energy_identity {P T u : ℝ}
    (hP : 0 < P) (hT : 0 < T) (hu : 0 < u) :
    P^11*(u*T/P^3)+P^12*(u*T/P^3)^((8:ℝ)/3) =
      u*(T*P^8)+u^((8:ℝ)/3)*(T^((8:ℝ)/3)*P^4) := by
  have hPpow : (P^3)^((8:ℝ)/3)=P^8 := by
    rw [←Real.rpow_natCast_mul hP.le]
    norm_num
  rw [Real.div_rpow (by positivity) (by positivity),Real.mul_rpow hu.le hT.le,hPpow]
  field_simp

private theorem exists_displacement_model_global_bound {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ > (0:ℝ), ∃ C > (0:ℝ), ∃ K ≥ (1:ℝ),
      ∀ (G : ℝ → ℝ) (T P : ℝ) (a b : ℕ),
      0 < T → 0 < P → a ≤ b → P ≤ a → (b:ℝ) ≤ 2*P →
      IsApproximateModelPhaseFunction G σ 3 δ →
      let U := (modelPhaseJetCoefficient σ 2+1)*T/P^3/6
      U ≤ 1/3600 → 1 ≤ P*U*Real.sqrt U → K ≤ P*U →
      ‖exponentialSumAt G T P a b‖^12 ≤
        C*P^ε*(1+Real.log P)^36*(T*P^8+T^((8:ℝ)/3)*P^4) := by
  let c₂ := modelPhaseJetCoefficient σ 2+1
  let c₃ := modelPhaseJetCoefficient σ 3+1
  let c₁ := modelPhaseJetCoefficient σ 1+1
  let l := 6*modelPhaseJetLower σ 2/c₂
  let b₄ := 6*c₃/c₂
  let a₄ := 6*modelPhaseJetLower σ 3/c₂
  let x := 3*c₁/c₂
  let u := c₂/6
  have hc₂ : 0 < c₂ := by
    have hh := modelPhaseJetCoefficient_nonneg σ 2
    dsimp only [c₂]
    positivity
  have hc₃ : 0 < c₃ := by
    have hh := modelPhaseJetCoefficient_nonneg σ 3
    dsimp only [c₃]
    positivity
  have hc₁ : 0 < c₁ := by
    have hh := modelPhaseJetCoefficient_nonneg σ 1
    dsimp only [c₁]
    positivity
  have hl : 0 < l := by
    have hh := modelPhaseJetLower_pos hσ 2
    dsimp only [l]
    positivity
  have hb₄ : 0 < b₄ := by dsimp only [b₄]; positivity
  have ha₄ : 0 < a₄ := by
    have hh := modelPhaseJetLower_pos hσ 3
    dsimp only [a₄]
    positivity
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hu : 0 < u := by dsimp only [u]; positivity
  obtain ⟨δ,hδ,hentry⟩ := displacement_model_buffered_entry hσ
  obtain ⟨Cf,hCf,hglobal⟩ := exists_displacement_physical_source_global hε hl hb₄ ha₄ hx
  let D := u+u^((8:ℝ)/3)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨δ,hδ,Cf*D,by positivity,max 1 b₄,le_max_left _ _,?_⟩
  intro G T P a b hT hP hab ha hb hG U hUsmall hK hPU
  have hU : 0 < U := by change 0 < c₂*T/P^3/6; positivity
  let N := ⌊1/(10*Real.sqrt U)⌋₊
  have hN : 0 < N := (displacement_block_scale hU hUsmall).1
  obtain ⟨hL,hU',hlam,hF,hX,hreg,hthree,hfour,hcurv,S,hbuffer,hspan,hmul,hsource⟩ :=
    hentry G T P a b N hT hP hN hab ha hb hG
  have hLid : l*U=modelPhaseJetLower σ 2*T/P^3 := by
    change (6*modelPhaseJetLower σ 2/c₂)*(c₂*T/P^3/6)=_
    field_simp
  have hFid : b₄*U/P=(modelPhaseJetCoefficient σ 3+1)*T/P^4 := by
    change (6*c₃/c₂)*(c₂*T/P^3/6)/P=c₃*T/P^4
    field_simp
  have hlamid : a₄*U/P=modelPhaseJetLower σ 3*T/P^4 := by
    change (6*modelPhaseJetLower σ 3/c₂)*(c₂*T/P^3/6)/P=_
    field_simp
  have hXid : x*P*U=(modelPhaseJetCoefficient σ 1+1)*T/P^2/2 := by
    change (3*c₁/c₂)*P*(c₂*T/P^3/6)=c₁*T/P^2/2
    field_simp
    ring
  have hs := hglobal ℕ S (fun t => T*G (t/P)) (fun k => (k:ℤ)) (fun _ => N)
    (a:ℤ) (P+1/2) (2*P-1/2) P U hP hU hUsmall hK ((le_max_right _ _).trans hPU)
    hreg (by simpa only [hLid] using hthree)
    (by simpa only [hFid,hlamid] using hfour)
    (by simpa only [hXid] using hcurv)
    hmul (fun _ _ => le_rfl)
    (by simpa only [Int.cast_natCast] using hbuffer)
  have hphysical := (pow_le_pow_left₀ (norm_nonneg _) hsource 12).trans hs
  have hUid : U=u*T/P^3 := by change c₂*T/P^3/6=(c₂/6)*T/P^3; ring
  have he : P^11*U+P^12*U^((8:ℝ)/3) ≤ D*(T*P^8+T^((8:ℝ)/3)*P^4) := by
    rw [hUid,displacement_physical_energy_identity hP hT hu]
    have hfirst : u ≤ D := le_add_of_nonneg_right (by positivity)
    have hsecond : u^((8:ℝ)/3) ≤ D := le_add_of_nonneg_left hu.le
    have hh := add_le_add
      (mul_le_mul_of_nonneg_right hfirst (show 0 ≤ T*P^8 by positivity))
      (mul_le_mul_of_nonneg_right hsecond (show 0 ≤ T^((8:ℝ)/3)*P^4 by positivity))
    convert hh using 1
    ring
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ Cf*P^ε*(1+Real.log P)^36 by positivity)
  exact hphysical.trans (by convert hm using 1; ring)

#print axioms displacement_physical_energy_identity
#print axioms exists_displacement_model_global_bound

open Filter
open scoped Topology

-- Reuse the production logarithmic-loss absorption lemma.
private theorem eventually_const_log36_le_rpow {D q : ℝ} (hD : 0 ≤ D) (hq : 0<q) :
    ∀ᶠ T : ℝ in atTop, D*(1+Real.log T)^36 ≤ T^q := by
  have hl := ((isLittleO_log_rpow_rpow_atTop (36:ℝ) hq).const_mul_left (D*2^36)).eventuallyLE
  filter_upwards [hl,eventually_ge_atTop (Real.exp 1)] with T hh hT
  have hTp : 0<T := (Real.exp_pos 1).trans_le hT
  have hlog : 1 ≤ Real.log T := by
    have ht := Real.log_le_log (Real.exp_pos 1) hT
    simpa only [Real.log_exp] using ht
  have hlog0 : 0 ≤ Real.log T := zero_le_one.trans hlog
  have hp : 0 ≤ D*2^36*(Real.log T)^(36:ℝ) := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hp,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTp.le q)] at hh
  norm_num only [Real.rpow_ofNat] at hh
  calc
    _ ≤ D*(2*Real.log T)^36 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hlog]) 36) hD
    _ = D*2^36*(Real.log T)^36 := by ring
    _ ≤ _ := by
      convert hh using 1
      norm_num

private theorem eventually_displacement_physical_scales {u K a δ : ℝ}
    (hu : 0 < u) (hlo : (1:ℝ)/3 < a-δ) (hhi : a+δ < 3/7) :
    ∀ᶠ T : ℝ in atTop, ∀ P : ℝ, 0 < P → T^(a-δ) ≤ P → P ≤ T^(a+δ) →
      let U := u*T/P^3
      U ≤ 1/3600 ∧ 1 ≤ P*U*Real.sqrt U ∧ K ≤ P*U := by
  have hsmall := eventually_const_mul_rpow_le_rpow (D:=3600*u)
    (by linarith only [hlo] : (1:ℝ) < (a-δ)*3)
  have hsize := eventually_const_mul_rpow_le_rpow (D:=K/u)
    (by linarith only [hhi] : (a+δ)*2 < (1:ℝ))
  have hcurve := eventually_const_mul_rpow_le_rpow (D:=1/u^3)
    (by linarith only [hhi] : (a+δ)*7 < (3:ℝ))
  filter_upwards [hsmall,hsize,hcurve,eventually_gt_atTop (0:ℝ)] with T ht₁ ht₂ ht₃ hT
  intro P hP hPl hPh U
  have hU : 0 < U := by dsimp only [U]; positivity
  have hPlo : T^((a-δ)*3) ≤ P^3 := by
    calc
      _ = (T^(a-δ))^3 := by simpa using Real.rpow_mul_natCast hT.le (a-δ) 3
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hT.le _) hPl 3
  have hPtwo : P^2 ≤ T^((a+δ)*2) := by
    calc
      _ ≤ (T^(a+δ))^2 := pow_le_pow_left₀ hP.le hPh 2
      _ = _ := by simpa using (Real.rpow_mul_natCast hT.le (a+δ) 2).symm
  have hPseven : P^7 ≤ T^((a+δ)*7) := by
    calc
      _ ≤ (T^(a+δ))^7 := pow_le_pow_left₀ hP.le hPh 7
      _ = _ := by simpa using (Real.rpow_mul_natCast hT.le (a+δ) 7).symm
  rw [Real.rpow_one] at ht₁ ht₂
  have hUbound : U ≤ 1/3600 := by
    apply (div_le_iff₀ (pow_pos hP 3)).mpr
    linarith only [ht₁.trans hPlo]
  have hphysicalK : K ≤ P*U := by
    have hh := mul_le_mul_of_nonneg_left ht₂ hu.le
    have hid : u*(K/u*T^((a+δ)*2))=K*T^((a+δ)*2) := by field_simp
    rw [hid] at hh
    by_cases hK : 0 ≤ K
    · have hk := (mul_le_mul_of_nonneg_left hPtwo hK).trans hh
      have he : P*U=u*T/P^2 := by dsimp only [U]; field_simp
      rw [he]
      exact (le_div_iff₀ (pow_pos hP 2)).mpr hk
    · exact (le_of_not_ge hK).trans (by positivity)
  have hcurve' : P^7 ≤ u^3*T^3 := by
    have hh := mul_le_mul_of_nonneg_left ht₃ (pow_nonneg hu.le 3)
    have hid : u^3*(1/u^3*T^((a+δ)*7))=T^((a+δ)*7) := by field_simp
    rw [hid] at hh
    norm_num only [Real.rpow_ofNat] at hh
    exact hPseven.trans hh
  have henergy : 1 ≤ P^2*U^3 := by
    have he : P^2*U^3=u^3*T^3/P^7 := by dsimp only [U]; field_simp
    rw [he]
    exact (le_div_iff₀ (pow_pos hP 7)).mpr (by simpa only [one_mul] using hcurve')
  have hidentity : (P*U*Real.sqrt U)^2=P^2*U^3 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hU.le]
    ring
  have hroot : 1 ≤ P*U*Real.sqrt U := by
    nlinarith only [henergy,hidentity,show 0 ≤ P*U*Real.sqrt U by positivity]
  exact ⟨hUbound,hroot,hphysicalK⟩

private theorem eventually_displacement_scale_majorant {C a δ η ε : ℝ}
    (hC : 0 ≤ C) (ha : (17:ℝ)/42 ≤ a) (ha' : a ≤ 3/7)
    (hδ : 0 ≤ δ) (hgap : a+δ ≤ 1) (hδη : δ ≤ η)
    (hη : 0 < η) (hηε : η ≤ ε/100) :
    ∀ᶠ T : ℝ in atTop, ∀ P : ℝ, 1 ≤ P → P ≤ T^(a+δ) →
      C*P^η*(1+Real.log P)^36*(T*P^8+T^((8:ℝ)/3)*P^4) ≤
        T^(12*((13:ℝ)/84+a/2+ε)) := by
  filter_upwards [eventually_const_log36_le_rpow (show 0 ≤ 2*C by positivity) hη,
    eventually_ge_atTop (1:ℝ)] with T hlog hT
  intro P hP hPh
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hPT : P ≤ T := hPh.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hT hgap)
  have hlogP := Real.log_nonneg hP
  have hlogT := Real.log_nonneg hT
  have hlogPT := Real.log_le_log hPp hPT
  have hPe : P^η ≤ T^η := Real.rpow_le_rpow hPp.le hPT hη.le
  let d := 12*((13:ℝ)/84+a/2)+8*δ
  have hmain₁ : T*P^8 ≤ T^d := by
    calc
      _ ≤ T*(T^(a+δ))^8 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hPp.le hPh 8) hTp.le
      _ = T^(1+(a+δ)*8) := by
        rw [←Real.rpow_mul_natCast hTp.le,Real.rpow_add hTp,Real.rpow_one]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by dsimp only [d]; linarith only [ha'])
  have hmain₂ : T^((8:ℝ)/3)*P^4 ≤ T^d := by
    calc
      _ ≤ T^((8:ℝ)/3)*(T^(a+δ))^4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hPp.le hPh 4) (Real.rpow_nonneg hTp.le _)
      _ = T^((8:ℝ)/3+(a+δ)*4) := by
        rw [←Real.rpow_mul_natCast hTp.le,←Real.rpow_add hTp]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by dsimp only [d]; linarith only [ha,hδ])
  have hsum : T*P^8+T^((8:ℝ)/3)*P^4 ≤ 2*T^d := by linarith only [hmain₁,hmain₂]
  calc
    _ ≤ C*T^η*(1+Real.log T)^36*(2*T^d) := by gcongr
    _ = (2*C*(1+Real.log T)^36)*(T^η*T^d) := by ring
    _ ≤ T^η*(T^η*T^d) := mul_le_mul_of_nonneg_right hlog (by positivity)
    _ = T^(d+2*η) := by rw [←Real.rpow_add hTp,←Real.rpow_add hTp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by dsimp only [d]; linarith only [hδη,hηε,hη])

#print axioms eventually_displacement_physical_scales
#print axioms eventually_displacement_scale_majorant

private theorem isExponentSumBoundNonAsymptotic_bourgain_refined
    {α : NNReal} (hα : (17:ℝ)/42 ≤ (α:ℝ)) (hαupper : (α:ℝ) < 3/7) :
    IsExponentSumBoundNonAsymptotic α ((13:ℝ)/84+(α:ℝ)/2) := by
  intro ε hε σ hσ
  let η := min ((1:ℝ)/1000) (ε/100)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηε : η ≤ ε/100 := min_le_right _ _
  obtain ⟨δ₀,hδ₀,C₀,hC₀,K,hK,hsource⟩ := exists_displacement_model_global_bound hσ hη
  let δ := min δ₀ (min η (min (((α:ℝ)-1/3)/2) ((3/7-(α:ℝ))/2)))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hη (lt_min
    (by linarith only [hα]) (by linarith only [hαupper])))
  have hδ0 : δ ≤ δ₀ := min_le_left _ _
  have hδη : δ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hδgaps : δ ≤ min (((α:ℝ)-1/3)/2) ((3/7-(α:ℝ))/2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hlow : (1:ℝ)/3 < (α:ℝ)-δ := by
    have hh := hδgaps.trans (min_le_left _ _)
    linarith only [hh,hα]
  have hhigh : (α:ℝ)+δ < 3/7 := by
    have hh := hδgaps.trans (min_le_right _ _)
    linarith only [hh,hαupper]
  let u := (modelPhaseJetCoefficient σ 2+1)/6
  have hu : 0 < u := by
    have hh := modelPhaseJetCoefficient_nonneg σ 2
    dsimp only [u]
    positivity
  have hentry := eventually_displacement_physical_scales (K:=K) hu hlow hhigh
  have hmajor := eventually_displacement_scale_majorant hC₀.le hα hαupper.le hδ.le
    (by linarith only [hhigh]) hδη hη hηε
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hentry.and hmajor)
  let C := max 1 M
  have hC : 1 ≤ C := le_max_left _ _
  have hMC : M ≤ C := le_max_right _ _
  refine ⟨δ,hδ,3,by norm_num,C,hC,?_⟩
  intro T P G a b hs
  have hT : 1 ≤ T := hC.trans hs.threshold_le_param
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hPp : 0 < P := (Real.rpow_pos_of_pos hTp _).trans_le hs.rpow_sub_le_scale
  have hP1 : 1 ≤ P := (Real.one_le_rpow hT (by linarith only [hlow] : 0 ≤ (α:ℝ)-δ)).trans
    hs.rpow_sub_le_scale
  obtain ⟨hphysical,hbudget⟩ := hM T (hMC.trans hs.threshold_le_param)
  obtain ⟨hUsmall,hcurve,hPU⟩ := hphysical P hPp hs.rpow_sub_le_scale hs.scale_le_rpow_add
  have hUid : (modelPhaseJetCoefficient σ 2+1)*T/P^3/6=u*T/P^3 := by dsimp only [u]; ring
  by_cases hab : a ≤ b
  · have hbound := hsource G T P a b hTp hPp hab hs.scale_le_start hs.end_le_two_mul_scale
      (approximateModelPhase_mono hs.isApproximateModelPhase le_rfl hδ0)
      (by simpa only [hUid] using hUsmall)
      (by simpa only [hUid] using hcurve)
      (by simpa only [hUid] using hPU)
    have hpower := hbound.trans (hbudget P hP1 hs.scale_le_rpow_add)
    have hpower' : ‖exponentialSumAt G T P a b‖^12 ≤
        (T^((13:ℝ)/84+(α:ℝ)/2+ε))^12 := by
      rw [←Real.rpow_mul_natCast hTp.le]
      convert hpower using 1
      congr 1
      ring
    have hh := (pow_le_pow_iff_left₀ (norm_nonneg _)
      (Real.rpow_nonneg hTp.le _) (by norm_num : (12:ℕ)≠0)).mp hpower'
    exact hh.trans (le_mul_of_one_le_left (Real.rpow_nonneg hTp.le _) hC)
  · have hEmpty : Finset.Icc a b=∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab)
    simp only [exponentialSumAt,hEmpty,Finset.sum_empty,norm_zero]
    exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hTp.le _)

#print axioms isExponentSumBoundNonAsymptotic_bourgain_refined

private theorem exponentPair_bourgain : ExponentPair (13/84) (55/84) := by
  apply exponentPair_of_beta_bound_half (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hαhalf
  have hbound : exponentSumGrowthExponent α ≤ (13:ℝ)/84+(α:ℝ)/2 := by
    by_cases hshort : (α:ℝ) ≤ 17/42
    · exact exponentSumGrowthExponent_le_bourgain_short_of_robertSargos hshort
    · by_cases hbaseline : (3:ℝ)/7 ≤ (α:ℝ)
      · exact exponentSumGrowthExponent_le_bourgain_baseline hbaseline hαhalf
      · exact exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
          (isExponentSumBoundNonAsymptotic_bourgain_refined (le_of_not_ge hshort) (lt_of_not_ge hbaseline))
  convert hbound using 1
  simp only [exponentPairLine]
  ring

#print axioms exponentPair_bourgain

-- The stronger analytic Bourgain pair also supplies the exact Watt coordinates.
-- This is an alternate provenance proof, not a reproduction of Watt's argument.
private theorem exponentPair_watt_of_bourgain : ExponentPair (89/560) (369/560) := by
  apply exponentPair_of_beta_bound_half (by norm_num [InExponentPairTriangle]) (by norm_num)
  intro α hαhalf
  have h := exponentSumGrowthExponent_le_exponentPairLine_closed exponentPair_bourgain α
    (by linarith only [hαhalf] : (α:ℝ) ≤ 1)
  unfold exponentPairLine at h ⊢
  linarith only [h]

#print axioms exponentPair_watt_of_bourgain

end TaoTrudgianYang2025.RefinedPrototype

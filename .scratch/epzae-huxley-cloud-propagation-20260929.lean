import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped ContDiff BigOperators FourierTransform Classical

namespace HuxleyCloudPropagationScratch

example
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let s := fun i => -vinv i-(q i:ℤ)*⌊-(vinv i:ℝ)/q i⌋
    ∃ v : Fin 2 → ℤ, (∀ i, v i*(q i:ℤ)-(rat i).num*s i=1) ∧
      |mu 1*(q 1:ℝ)^3/(mu 0*(q 0:ℝ)^3)-1| ≤ B*R^2/N^2 ∧
      |(s 1:ℝ)/q 1-(s 0:ℝ)/q 0| ≤ B*R^4/((q 0:ℝ)^2*N^2) ∧
      let C := (cround 0:ℝ)*s 0/q 0-(cround 1:ℝ)*s 1/q 1
      |C-round C| ≤ B*R^2/((q 0:ℝ)*N) ∧
      |((q 0:ℝ)*ell 0-cround 0)-((q 1:ℝ)*ell 1-cround 1)| ≤ B*(q 0:ℝ)/N :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_conditions (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Q K₀ rat vinv parity (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {x eps : ℝ} {c : ℤ} (heps : eps < 1/2)
    (hc : c∈minorArcCenterLabels x eps) :
    ∃ p : Fin 2, c=⌊x⌋+(p:ℕ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCenterLabels_fourier_parity (x:=x) (eps:=eps) (c:=c) heps hc

example
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let s := fun i => -vinv i-(q i:ℤ)*⌊-(vinv i:ℝ)/q i⌋
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 → (Q:ℝ) ≤ N → 2*R^2 ≤ (Q:ℝ)*N →
    ∃ v : Fin 2 → ℤ, (∀ i, v i*(q i:ℤ)-(rat i).num*s i=1) ∧
      ∀ (x₁ : Fin 2 → ℝ) (u t tb ub : ℤ),
      0 < t → t*tb+u*ub=1 →
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2)) →
      let n := fun i => round (x₁ i)-round (x₀ i)
      let qnew := fun i => (q i:ℝ)*u+s i*t
      let d₁ := fun i => deriv (f i) (round (x₁ i))
      let C := (cround 0:ℝ)*s 0/q 0-(cround 1:ℝ)*s 1/q 1
      let C₂ := modelPhaseJetCoefficient σ 2+δ
      let C₃ := modelPhaseJetCoefficient σ 3+δ
      let κ := modelPhaseThirdLower σ
      let Ct := C₂/2+5*C₃/12
      let Cc := C₂/κ+C₃/(2*κ)
      let z := fun i => qnew i*d₁ i
      let j := fun i => cround i*u+2*n i*((rat i).num*u+v i*t)
      let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
      let inverse := fun i => (q i:ℤ)*tb-s i*ub
      let X := fun (i : Fin 2) (cnew : ℤ) => (inverse i:ℝ)*cnew/qnew i
      let nu := fun i => iteratedDeriv 3 (f i) (round (x₁ i))/6
      let Cfirst := 1+3*(σ*(σ+1)+1)/(2*κ)
      let Cv := C₃/κ
      (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=
        (((rat i).num:ℝ)*u+v i*t)/qnew i) →
      (∀ i, |x₁ i-x₀ i| ≤ N-1) →
      (∀ i, (σ*(σ+1)+1)*|x₁ i-x₀ i| ≤ 2*N) →
      (∀ i, (Q:ℝ)/2 ≤ qnew i ∧ qnew i ≤ Q) →
      Cv*(R^2/N^2) ≤ 1/2 → Δ < 1/2 →
      ∃ cnew∈minorArcCenterLabels (z 0) Δ,
        ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
        cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
        (cnew-j 0)-(cnew₁-j 1)=round C*t ∧
        |(X 0 cnew-X 1 cnew₁)-round (X 0 cnew-X 1 cnew₁)| ≤
          (201*B+192*B*Cc+8*Cc+4*B*Ct)*R^2/(N*(Q:ℝ)) ∧
        |(inverse 0:ℝ)/qnew 0-(inverse 1:ℝ)/qnew 1| ≤
          4*B*Cfirst*R^4/(N^2*(Q:ℝ)^2) ∧
        |nu 1*(qnew 1)^3/(nu 0*(qnew 0)^3)-1| ≤ (33*B+4*Cv)*R^2/N^2 ∧
        ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_short_propagation (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Q K₀ rat vinv parity (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let s := fun i => -vinv i-(q i:ℤ)*⌊-(vinv i:ℝ)/q i⌋
    let H := N/(σ*(σ+1)+3)
    2 ≤ N → (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 → (Q:ℝ) ≤ N → 2*R^2 ≤ (Q:ℝ)*N →
    ∃ v : Fin 2 → ℤ, (∀ i, v i*(q i:ℤ)-(rat i).num*s i=1) ∧
      ∀ u t tb ub : ℤ, 0 < t → t*tb+u*ub=1 →
      (t:ℝ) ≤ modelPhaseThirdLower σ*(Q:ℝ)^2/(8*(σ*(σ+1)+3)*R^2) →
      let qnew := fun i => (q i:ℝ)*u+s i*t
      (∀ i, (Q:ℝ)/2 ≤ qnew i ∧ qnew i ≤ Q) →
      let C := (cround 0:ℝ)*s 0/q 0-(cround 1:ℝ)*s 1/q 1
      let C₂ := modelPhaseJetCoefficient σ 2+δ
      let C₃ := modelPhaseJetCoefficient σ 3+δ
      let κ := modelPhaseThirdLower σ
      let Ct := C₂/2+5*C₃/12
      let Cc := C₂/κ+C₃/(2*κ)
      let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
      let inverse := fun i => (q i:ℤ)*tb-s i*ub
      let X := fun (i : Fin 2) (cnew : ℤ) => (inverse i:ℝ)*cnew/qnew i
      let Cfirst := 1+3*(σ*(σ+1)+1)/(2*κ)
      let Cv := C₃/κ
      Cv*(R^2/N^2) ≤ 1/2 → Δ < 1/2 →
      ∃ x₁ : Fin 2 → ℝ, (∀ i, x₁ i∈uIcc (x₀ i) (x₀ i+H)) ∧
        (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2)) ∧
        (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=
          (((rat i).num:ℝ)*u+v i*t)/qnew i) ∧
        let n := fun i => round (x₁ i)-round (x₀ i)
        let d₁ := fun i => deriv (f i) (round (x₁ i))
        let z := fun i => qnew i*d₁ i
        let j := fun i => cround i*u+2*n i*((rat i).num*u+v i*t)
        let nu := fun i => iteratedDeriv 3 (f i) (round (x₁ i))/6
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          (cnew-j 0)-(cnew₁-j 1)=round C*t ∧
          |(X 0 cnew-X 1 cnew₁)-round (X 0 cnew-X 1 cnew₁)| ≤
            (201*B+192*B*Cc+8*Cc+4*B*Ct)*R^2/(N*(Q:ℝ)) ∧
          |(inverse 0:ℝ)/qnew 0-(inverse 1:ℝ)/qnew 1| ≤
            4*B*Cfirst*R^4/(N^2*(Q:ℝ)^2) ∧
          |nu 1*(qnew 1)^3/(nu 0*(qnew 0)^3)-1| ≤ (33*B+4*Cv)*R^2/N^2 ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_root_propagation (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Q K₀ rat vinv parity (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv


example
    {a b c d e₀ r₀ v₀ s₀ e₁ r₁ v₁ s₁ : ℤ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (h₀ : v₀*r₀-e₀*s₀=1) (h₁ : v₁*r₁-e₁*s₁=1)
    (hdet : a*d-b*c=1)
    (he : a*e₀+b*r₀=e₁) (hr : c*e₀+d*r₀=r₁)
    (hsmall : |c|+|r₀*s₁-s₀*r₁| < r₀*r₁) :
    a*v₀+b*s₀=v₁ ∧ c*v₀+d*s₀=s₁ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.farey_matrix_companion_unique (a:=a) (b:=b) (c:=c) (d:=d) (e₀:=e₀) (r₀:=r₀) (v₀:=v₀) (s₀:=s₀) (e₁:=e₁) (r₁:=r₁) (v₁:=v₁) (s₁:=s₁) hr₀ hr₁ h₀ h₁ hdet he hr hsmall

example
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2))
    (hnear : |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2)) :
    let s := fun i => -vinv i-q i*⌊-(vinv i:ℝ)/q i⌋
    ∃ v : Fin 2 → ℤ,
      (∀ i, v i*q i-e i*s i=1) ∧
      (∀ i, (s i:ℝ)/q i=Int.fract (-(vinv i:ℝ)/q i)) ∧
      ∀ u t : ℤ,
        A 0*(e 0*u+v 0*t)+A 1*(q 0*u+s 0*t)=e 1*u+v 1*t ∧
        A 2*(e 0*u+v 0*t)+A 3*(q 0*u+s 0*t)=q 1*u+s 1*t :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fourier_matrix_normalized_chart_transport q e vinv A (Q:=Q) (K:=K) hq hK hband hinv hdet ht hmap hgamma hnear

example
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℝ) (z : ι → ℝ) (r : ι → ℚ) (v : ι → ℤ)
    (Q K₀ : ℕ) [NeZero K₀] (μ₀ U₀ : ℝ) (hμ₀ : 0 < μ₀)
    (hμbounds : ∀ i∈S, μ₀ ≤ iteratedDeriv 3 (f i) (round (z i))/6 ∧
      iteratedDeriv 3 (f i) (round (z i))/6 ≤ U₀)
    (hlevel : ∀ i∈S, iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ))
    (hden : ∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den)
    (hinv : ∀ i∈S, ((r i).den:ℤ) ∣ (r i).num*v i-1) :
    let q := fun i => (r i).den
    let μ := fun i => iteratedDeriv 3 (f i) (round (z i))/6
    let ℓ := fun i => deriv (f i) (round (z i))
    let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
    let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
    let K := fun i => -2*μ i*(Real.sqrt (2/(3*μ i*(q i:ℝ))))^3
    let x := fun i p =>
      (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
    let V := S ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : ι × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let h := fun i => iteratedDeriv 2 (f i) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ A : ((ι × Fin 2) × (ι × Fin 2)) → Fin 4 → ℤ,
      ∀ ij∈P,
        A ij 0*A ij 3-A ij 1*A ij 2=1 ∧
        let t := (A ij 2:ℝ)*h ij.1.1+A ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((A ij 0:ℝ)*h ij.1.1+A ij 1)/t=h ij.2.1 ∧
        |(A ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(A ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(A ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (A ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(A ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-h ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          A ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num) ∧
        let qi : Fin 2 → ℤ := ![(q ij.1.1:ℤ),(q ij.2.1:ℤ)]
        let ei : Fin 2 → ℤ := ![(r ij.1.1).num,(r ij.2.1).num]
        let vi : Fin 2 → ℤ := ![v ij.1.1,v ij.2.1]
        let si := fun i => -vi i-qi i*⌊-(vi i:ℝ)/qi i⌋
        ∃ vc : Fin 2 → ℤ,
          (∀ i, vc i*qi i-ei i*si i=1) ∧
          (∀ i, (si i:ℝ)/qi i=Int.fract (-(vi i:ℝ)/qi i)) ∧
          ∀ u t : ℤ,
            A ij 0*(ei 0*u+vc 0*t)+A ij 1*(qi 0*u+si 0*t)=ei 1*u+vc 1*t ∧
            A ij 2*(ei 0*u+vc 0*t)+A ij 3*(qi 0*u+si 0*t)=qi 1*u+si 1*t :=
  TaoTrudgianYang2025.HuxleyRationalPhase.source_arc_fourier_cloud_chart_transport (ι:=ι) S f z r v Q K₀ μ₀ U₀ hμ₀ hμbounds hlevel hden hinv


example
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let γ := fun i => q i*(d₁ i-d₀ i-2*(e i:ℝ)*n i/r i-
      (n i:ℝ)*t/(r i*q i))
    let H := fun i => ((c i:ℝ)*s i-n i)*t/r i+θ i*q i/r i+γ i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, |(t:ℝ)|/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    |H 0-H 1-(round C:ℝ)*t| ≤ (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_residual_difference_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (Q:=Q) (K:=K) (u:=u) (t:=t) (F:=F) (A:=A) (W:=W) (x₀:=x₀) (x₁:=x₁) (e:=e) (r:=r) (v:=v) (s:=s) hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hA hW hx₀ hx₁ hr ht hdet

example
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (ht : t ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun i => round (x₁ i)-round (x₀ i)
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |(n i:ℝ)| ≤ N) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, |(t:ℝ)|/r i ≤ q i/R^2) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    |(z 0-z 1)-round (z 0-z 1)| ≤ (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_fourth_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (Q:=Q) (K:=K) (u:=u) (t:=t) (F:=F) (A:=A) (W:=W) (x₀:=x₀) (x₁:=x₁) (e:=e) (r:=r) (v:=v) (s:=s) hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hA hW hx₀ hx₁ hr ht hdet

example
    {σ δ T M N R A W x₀ x₁ e r v s u t : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx₀ : x₀ ∈ Set.Ioo 0 W) (hx₁ : x₁ ∈ Set.Ioo 0 W)
    (hr : 0 < r) (hq : 0 < r*u+s*t) (hdet : v*r-e*s=1)
    (hwidth : |x₁-x₀| ≤ N-1)
    (hphasewidth : (σ*(σ+1)+1)*|x₁-x₀| ≤ 2*N) :
    let f := heathBrownPhysicalPhase F T M A 1
    iteratedDeriv 2 f x₀/2=e/r →
    iteratedDeriv 2 f x₁/2=(e*u+v*t)/(r*u+s*t) →
    |(round x₁:ℝ)-(round x₀:ℝ)| ≤ N ∧ |t|/r ≤ (r*u+s*t)/R^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_window_geometry_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (A:=A) (W:=W) (x₀:=x₀) (x₁:=x₁) (e:=e) (r:=r) (v:=v) (s:=s) (u:=u) (t:=t) (F:=F) hσ hδ hF hT hM hN hR hscale hA hW hx₀ hx₁ hr hq hdet hwidth hphasewidth

example
    {σ δ T M N R Q K : ℝ} {u t : ℤ}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ x₁ : Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (TaoTrudgianYang2025.modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hsmall : K*R^2/N^2 ≤ 1/2)
    (hNR : N ≤ R^2) (hRN : R ≤ N) (hcube : N^3 ≤ M*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ i, x₁ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, 0 < r i) (hdet : ∀ i, v i*r i-e i*s i=1) :
    let f := fun i => TaoTrudgianYang2025.heathBrownPhysicalPhase (F i) T M (A i) 1
    let q := fun i => (r i:ℝ)*u+s i*t
    let d₀ := fun i => iteratedDeriv 1 (f i) (round (x₀ i))
    let d₁ := fun i => iteratedDeriv 1 (f i) (round (x₁ i))
    let c := fun i => round ((r i:ℝ)*d₀ i)
    let θ := fun i => (r i:ℝ)*d₀ i-c i
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let C := (c 0:ℝ)*s 0/r 0-(c 1:ℝ)*s 1/r 1
    let C₂ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 2+δ
    let C₃ := TaoTrudgianYang2025.modelPhaseJetCoefficient σ 3+δ
    let κ := TaoTrudgianYang2025.modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let z := fun i => q i*d₁ i
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=((e i:ℝ)*u+v i*t)/q i) →
    (∀ i, |x₁ i-x₀ i| ≤ N-1) →
    (∀ i, 0 < q i ∧ q i ≤ Q) →
    (∀ i, (σ*(σ+1)+1)*|x₁ i-x₀ i| ≤ 2*N) →
    R^2/N ≤ (r 0:ℝ) →
    |μ 1*(r 1:ℝ)^3/(μ 0*(r 0:ℝ)^3)-1| ≤ K*R^2/N^2 →
    |(s 1:ℝ)/r 1-(s 0:ℝ)/r 0| ≤ K*R^4/((r 0:ℝ)^2*N^2) →
    |C-round C| ≤ K*R^2/((r 0:ℝ)*N) →
    |θ 0-θ 1| ≤ K*(r 0:ℝ)/N →
    |(z 0-z 1)-round (z 0-z 1)| ≤ (37*K/2+16*K*Cc+2*Ct+2*Cc)*Q/N :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_window_fourth (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (Q:=Q) (K:=K) (u:=u) (t:=t) (F:=F) (A:=A) (W:=W) (x₀:=x₀) (x₁:=x₁) (e:=e) (r:=r) (v:=v) (s:=s) hσ hδ hF hT hM hN hR hscale hQ hK hsmall hNR hRN hcube hA hW hx₀ hx₁ hr hdet

example
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    let s := fun i => -vinv i-(q i:ℤ)*⌊-(vinv i:ℝ)/q i⌋
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    ∃ v : Fin 2 → ℤ, (∀ i, v i*(q i:ℤ)-(rat i).num*s i=1) ∧
      ∀ (x₁ : Fin 2 → ℝ) (u t : ℤ),
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2)) →
      let qnew := fun i => (q i:ℝ)*u+s i*t
      let d₁ := fun i => deriv (f i) (round (x₁ i))
      let C₂ := modelPhaseJetCoefficient σ 2+δ
      let C₃ := modelPhaseJetCoefficient σ 3+δ
      let κ := modelPhaseThirdLower σ
      let Ct := C₂/2+5*C₃/12
      let Cc := C₂/κ+C₃/(2*κ)
      let z := fun i => qnew i*d₁ i
      let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
      (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=
        (((rat i).num:ℝ)*u+v i*t)/qnew i) →
      (∀ i, |x₁ i-x₀ i| ≤ N-1) →
      (∀ i, (σ*(σ+1)+1)*|x₁ i-x₀ i| ≤ 2*N) →
      (∀ i, 0 < qnew i ∧ qnew i ≤ Q) →
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_signed_fourth (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Q K₀ rat vinv parity (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    ∀ (x₁ : Fin 2 → ℝ) (a d : ℤ),
      let anew : Fin 2 → ℤ := ![a,Mat 0*a+Mat 1*d]
      let qnew : Fin 2 → ℤ := ![d,Mat 2*a+Mat 3*d]
      let C₂ := modelPhaseJetCoefficient σ 2+δ
      let C₃ := modelPhaseJetCoefficient σ 3+δ
      let κ := modelPhaseThirdLower σ
      let Ct := C₂/2+5*C₃/12
      let Cc := C₂/κ+C₃/(2*κ)
      let z := fun i => (qnew i:ℝ)*deriv (f i) (round (x₁ i))
      let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2)) →
      (∀ i, iteratedDeriv 2 (f i) (x₁ i)/2=(anew i:ℝ)/qnew i) →
      (∀ i, |x₁ i-x₀ i| ≤ N-1) →
      (∀ i, (σ*(σ+1)+1)*|x₁ i-x₀ i| ≤ 2*N) →
      (∀ i, 0 < (qnew i:ℝ) ∧ (qnew i:ℝ) ≤ Q) →
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_matrix_fourth (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Q K₀ rat vinv parity Mat (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_conditions
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.minorArcCenterLabels_fourier_parity
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_short_propagation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_root_propagation
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_matrix_companion_unique
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fourier_matrix_normalized_chart_transport
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.source_arc_fourier_cloud_chart_transport
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_residual_difference_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_block_fourth_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_window_geometry_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_short_window_fourth
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_signed_fourth
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_matrix_fourth


example
    {σ δ T M N R : ℝ} (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hRN : R ≤ N) (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hgamma : |(Mat 2:ℝ)| ≤ R^4/(6*N^2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    let y₀ := iteratedDeriv 2 (f 0) (x₀ 0)/2
    let target := fun y => (![y,((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)] : Fin 2 → ℝ)
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1/2:ℝ) ≤ (Mat 2:ℝ)*y₀+Mat 3 →
    (Mat 2:ℝ)*y₀+Mat 3 ≤ 2 →
    target y₀ 1=iteratedDeriv 2 (f 1) (x₀ 1)/2 →
    0 < ε ∧ ∃ ρ : ℝ → Fin 2 → ℝ, ∀ y, |y-y₀| ≤ ε →
      ((1/4:ℝ) ≤ (Mat 2:ℝ)*y+Mat 3 ∧ (Mat 2:ℝ)*y+Mat 3 ≤ 3) ∧
      ∀ i, ρ y i∈Icc (x₀ i-H) (x₀ i+H) ∧
        ρ y i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (ρ y i)/2=target y i ∧
        |ρ y i-x₀ i| ≤ H ∧
        |(round (ρ y i):ℝ)-(round (x₀ i):ℝ)| ≤ H+1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_matrix_window_roots (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Mat (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hRN hscale hA hW hx₀ hdet hgamma

example
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    0 < ε ∧ ∃ ρ : ℝ → Fin 2 → ℝ, ∀ (a d : ℤ),
      0 < (d:ℝ) → (d:ℝ) ≤ (Q:ℝ)/3 → |(a:ℝ)/d-(rat 0:ℝ)| ≤ ε →
      let x₁ := ρ ((a:ℝ)/d)
      let anew : Fin 2 → ℤ := ![a,Mat 0*a+Mat 1*d]
      let qnew : Fin 2 → ℤ := ![d,Mat 2*a+Mat 3*d]
      let C₂ := modelPhaseJetCoefficient σ 2+δ
      let C₃ := modelPhaseJetCoefficient σ 3+δ
      let κ := modelPhaseThirdLower σ
      let Ct := C₂/2+5*C₃/12
      let Cc := C₂/κ+C₃/(2*κ)
      let z := fun i => (qnew i:ℝ)*deriv (f i) (round (x₁ i))
      let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (x₁ i)/2=(anew i:ℝ)/qnew i ∧
        |x₁ i-x₀ i| ≤ H ∧ 0 < (qnew i:ℝ) ∧ (qnew i:ℝ) ≤ Q) ∧
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_matrix_root_fourth (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Q K₀ rat vinv parity Mat (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_matrix_window_roots
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_matrix_root_fourth


example
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → 0 < r → 0 < s →
    (e:ℝ)/r < (rat 0:ℝ)-ε →
    (rat 0:ℝ)+ε < (v:ℝ)/s →
    (r:ℝ)*((rat 0:ℝ)+ε)-e ≤ 2*((r:ℝ)*((rat 0:ℝ)-ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*((r:ℝ)*l-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ S.card ∧
    ∃ ξ : ℝ → Fin 2 → ℝ, ∀ p∈S,
      let a := e*p.1+v*p.2
      let d := r*p.1+s*p.2
      let x₁ := ξ ((p.1:ℝ)/p.2)
      let anew : Fin 2 → ℤ := ![a,Mat 0*a+Mat 1*d]
      let qnew : Fin 2 → ℤ := ![d,Mat 2*a+Mat 3*d]
      let z := fun i => (qnew i:ℝ)*deriv (f i) (round (x₁ i))
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (x₁ i)/2=(anew i:ℝ)/qnew i ∧
        |x₁ i-x₀ i| ≤ H ∧ 0 < (qnew i:ℝ) ∧ (qnew i:ℝ) ≤ Q) ∧
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_complete_sector_fourth (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {K : ℕ} {σ δ T M N R B dmin l w Bd Δ Q : ℝ}
    {p₀ : ℤ × ℤ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xseed : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    {cnew : ℤ × ℤ → Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ p ∈ HuxleyLinearForm.fareySector K l w, ∀ i,
      x₁ ((p.1:ℝ)/p.2) i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hxseed : ∀ i, xseed i∈Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hBd : 1 ≤ Bd) (htseed : 0 < p₀.2)
    (hyseed : (p₀.1:ℝ)/p₀.2∈Set.Icc l w)
    (hden : ∀ y ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*y+s i) :
    let S := HuxleyLinearForm.fareySector K l w
    let y₀ := (p₀.1:ℝ)/p₀.2
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun y i => round (x₁ y i)
    let n := fun y i => b y i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μseed := fun i => iteratedDeriv 3 (f i) (round (xseed i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun y => g y-h y
    let z := fun (p : ℤ × ℤ) i => q p i*iteratedDeriv 1 (f i) (b ((p.1:ℝ)/p.2) i)
    let j := fun (p : ℤ × ℤ) i => round ((r i:ℝ)*d₀ i)*p.1+
      2*n ((p.1:ℝ)/p.2) i*(e i*p.1+v i*p.2)
    let H := fun p => (cnew p 0-j p 0)-(cnew p 1-j p 1)
    let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
    let η := D+(K:ℝ)*C*(w-l)^2
    let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    l ∈ finiteBoundaryCell Z l w k →
    w ∈ finiteBoundaryCell Z l w k →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (xseed i)/2=((e i:ℝ)*p₀.1+v i*p₀.2)/q p₀ i) →
    (∀ i, |(round (xseed i):ℝ)-(a i:ℝ)|^2 ≤ M*R) →
    (∀ p ∈ S, ∀ i,
      iteratedDeriv 2 (f i) (x₁ ((p.1:ℝ)/p.2) i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n ((p.1:ℝ)/p.2) i:ℝ)|^2 ≤ M*R) →
    |μseed 1*(q p₀ 1)^3/(μseed 0*(q p₀ 0)^3)-1| ≤ B*R^2/N^2 →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    max ((w-l)*(K:ℝ)^2/Bd) 2 ≤ S.card →
    1536*Bd*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    ∀ p ∈ S, H p=p.1*round (α-deriv φ y₀)+p.2*round (β-φ y₀+y₀*deriv φ y₀) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_sector_labels_from_seed (K:=K) (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (B:=B) (dmin:=dmin) (l:=l) (w:=w) (Bd:=Bd) (Δ:=Δ) (Q:=Q) (p₀:=p₀) (k:=k) (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xseed:=xseed) (x₁:=x₁) (e:=e) (r:=r) (v:=v) (s:=s) (cnew:=cnew) hσ hδ hF hT hM hN hR hRM hNscale hscale hB hdmin hΔ hQ hA hW hx₀ hx₁ hxseed hr hdet hl hw hlw hBd htseed hyseed hden

example
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → 0 < r → 0 < s →
    (e:ℝ)/r < (rat 0:ℝ)-ε →
    (rat 0:ℝ)+ε < (v:ℝ)/s →
    (r:ℝ)*((rat 0:ℝ)+ε)-e ≤ 2*((r:ℝ)*((rat 0:ℝ)-ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*((r:ℝ)*l-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    ∃ (ξ : ℝ → Fin 2 → ℝ) (cnew : ℤ × ℤ → Fin 2 → ℤ),
      let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
      let xp := fun p : ℤ × ℤ => ξ ((p.1:ℝ)/p.2)
      let zp := fun p i => qp p i*deriv (f i) (round (xp p i))
      let jp := fun (p : ℤ × ℤ) i => round ((rp i:ℝ)*dr i)*p.1+
        2*(round (xp p i)-ar i)*(ep i*p.1+vp i*p.2)
      (∀ p∈S, ∀ i, xp p i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xp p i)/2=((ep i:ℝ)*p.1+vp i*p.2)/qp p i ∧
        0 < qp p i ∧ qp p i ≤ Q) ∧
      (∀ p∈S, (∀ i, cnew p i∈minorArcCenterLabels (zp p i) Δ) ∧
        |(zp p 0-cnew p 0)-(zp p 1-cnew p 1)| ≤ Δ) ∧
      ∀ p∈S, ((cnew p 0-jp p 0)-(cnew p 1-jp p 1)=
        p.1*round (ac-deriv φ yseed)+p.2*round (bc-φ yseed+yseed*deriv φ yseed)) ∧
        |(ac-round (ac-deriv φ yseed))*((p.1:ℝ)/p.2)+
          (bc-round (bc-φ yseed+yseed*deriv φ yseed))-
          g ((p.1:ℝ)/p.2)+hq ((p.1:ℝ)/p.2)| ≤
          (Δ+quarticNonlinearResidualConstant σ δ*(qp p 0+qp p 1)/N)/(p.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_sector_linearization (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_complete_sector_fourth
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_sector_labels_from_seed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_sector_linearization

example
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (y : ι → ℝ)
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ ac bc : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hwidth : U*(w-l) ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤ 9 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_coefficient_color_count (ι:=ι) S y (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ hwidth hheight

example
    (S : Finset ℕ) (y : ℕ → ℝ) (hS : 288 ≤ S.card)
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ ac bc : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hwidth : U*(w-l) ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      ∀ i : Fin 7, (S.card:ℝ)/144 ≤ (j i.succ:ℝ)-(j i.castSucc:ℝ)-1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_common_coefficient_windows S y hS (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ hwidth hheight

example
    {σ δ T M N R L : ℝ} (Mat : Fin 4 → ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hLpos : 0 < L) (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hgamma : |(Mat 2:ℝ)| ≤ R^4/(6*N^2))
    (hwindow : modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let H := L*N
    let ε := modelPhaseThirdLower σ*L/(16*R^2)
    let y₀ := iteratedDeriv 2 (f 0) (x₀ 0)/2
    let target := fun y => (![y,((Mat 0:ℝ)*y+Mat 1)/((Mat 2:ℝ)*y+Mat 3)] : Fin 2 → ℝ)
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (1/2:ℝ) ≤ (Mat 2:ℝ)*y₀+Mat 3 →
    (Mat 2:ℝ)*y₀+Mat 3 ≤ 2 →
    target y₀ 1=iteratedDeriv 2 (f 1) (x₀ 1)/2 →
    0 < ε ∧ ∃ ρ : ℝ → Fin 2 → ℝ, ∀ y, |y-y₀| ≤ ε →
      ((1/4:ℝ) ≤ (Mat 2:ℝ)*y+Mat 3 ∧ (Mat 2:ℝ)*y+Mat 3 ≤ 3) ∧
      ∀ i, ρ y i∈Icc (x₀ i-H) (x₀ i+H) ∧
        ρ y i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (ρ y i)/2=target y i ∧
        |ρ y i-x₀ i| ≤ H ∧
        |(round (ρ y i):ℝ)-(round (x₀ i):ℝ)| ≤ H+1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_matrix_long_window_roots (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) Mat (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hLpos hscale hA hW hx₀ hdet hgamma hwindow

example
    {σ δ T M N R L : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (Mat : Fin 4 → ℤ) (e r : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hLpos : 0 < L) (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hgamma : |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2))
    (hwindow : modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2)
    (hr : 0 < r) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=((rat 1).den:ℝ)/(rat 0).den →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    ∃ xref : Fin 2 → ℝ, ∀ i,
      0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
      iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
      |xref i-x₀ i| ≤ L*N ∧
      |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_matrix_reference_roots (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) Q K₀ rat Mat e r (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hLpos hQ hscale hmesh hA hW hx₀ hden hdet hgamma hwindow hr

example
    {σ δ T M N R L dmin : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → 0 < r → 0 < s →
    (e:ℝ)/r < (rat 0:ℝ)-ε →
    (rat 0:ℝ)+ε < (v:ℝ)/s →
    (r:ℝ)*((rat 0:ℝ)+ε)-e ≤ 2*((r:ℝ)*((rat 0:ℝ)-ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*((r:ℝ)*l-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    0 < L →
    modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2 →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    (H+L*N+1)^2 ≤ M*R →
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x₀ i| ≤ L*N ∧
        |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1) ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    ∀ k : Fin 17, α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    ∃ (ξ : ℝ → Fin 2 → ℝ) (cnew : ℤ × ℤ → Fin 2 → ℤ),
      let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
      let xp := fun p : ℤ × ℤ => ξ ((p.1:ℝ)/p.2)
      let zp := fun p i => qp p i*deriv (f i) (round (xp p i))
      let jp := fun (p : ℤ × ℤ) i => round ((rp i:ℝ)*dr i)*p.1+
        2*(round (xp p i)-ar i)*(ep i*p.1+vp i*p.2)
      (∀ p∈S, ∀ i, xp p i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xp p i)/2=((ep i:ℝ)*p.1+vp i*p.2)/qp p i ∧
        0 < qp p i ∧ qp p i ≤ Q) ∧
      (∀ p∈S, (∀ i, cnew p i∈minorArcCenterLabels (zp p i) Δ) ∧
        |(zp p 0-cnew p 0)-(zp p 1-cnew p 1)| ≤ Δ) ∧
      ∀ p∈S, ((cnew p 0-jp p 0)-(cnew p 1-jp p 1)=
        p.1*round (ac-deriv φ yseed)+p.2*round (bc-φ yseed+yseed*deriv φ yseed)) ∧
        |(ac-round (ac-deriv φ yseed))*((p.1:ℝ)/p.2)+
          (bc-round (bc-φ yseed+yseed*deriv φ yseed))-
          g ((p.1:ℝ)/p.2)+hq ((p.1:ℝ)/p.2)| ≤
          (Δ+quarticNonlinearResidualConstant σ δ*(qp p 0+qp p 1)/N)/(p.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_linearization (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (dmin:=dmin) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_coefficient_color_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_common_coefficient_windows
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_matrix_long_window_roots
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_matrix_reference_roots
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_linearization

open TaoTrudgianYang2025.HuxleyLinearForm in
example
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 1 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (fareySector N l μ).card)
    (hlarge : 1536*B*δ*(μ*(N:ℝ))*(N:ℝ) < (fareySector N l μ).card)
    (hnear : ∀ p ∈ fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ∀ p : ℤ × ℤ, 0 ≤ (p.1:ℝ) → (p.1:ℝ) ≤ 12*(μ*(N:ℝ)) →
      0 ≤ (p.2:ℝ) → (p.2:ℝ) ≤ 12*(N:ℝ) → ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*(round α)+p.2*(round β) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_integer_labels_enlarged_rectangle (N:=N) (l:=l) (μ:=μ) (B:=B) (α:=α) (β:=β) (δ:=δ) hl hμ hB hδ hR hlarge hnear

example
    {e r v s : ℤ} {anchor seed : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s)
    (hlw : l < w) (hl : (e:ℝ)/r < l) (hw : w < (v:ℝ)/s)
    (ha : (anchor:ℝ)∈Icc l w) (hseed : (seed:ℝ)∈Icc l w)
    (hdyad : (r:ℝ)*w-e ≤ 2*((r:ℝ)*l-e))
    (hcut : 256*(anchor.den:ℝ) ≤ Q/3) (hseedQ : (seed.den:ℝ) ≤ Q) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊(Q/3)*((r:ℝ)*l-e)⌋₊
    let p : ℤ × ℤ := (v*seed.den-s*seed.num,r*seed.num-e*seed.den)
    0 < (p.2:ℝ) ∧ (p.1:ℝ)/p.2∈Icc α β ∧
      0 ≤ (p.1:ℝ) ∧ (p.1:ℝ) ≤ 12*(β*(K:ℝ)) ∧
      (p.2:ℝ) ≤ 12*(K:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_original_seed_enlarged_rectangle (e:=e) (r:=r) (v:=v) (s:=s) (anchor:=anchor) (seed:=seed) (l:=l) (w:=w) (Q:=Q) hdet hr hs hlw hl hw ha hseed hdyad hcut hseedQ

example
    {K : ℕ} {l w B y₀ α β δ C : ℝ} {g : ℝ → ℝ} {H : ℤ × ℤ → ℤ} {p₀ : ℤ × ℤ} {H₀ : ℤ}
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hcard : max ((w-l)*(K:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector K l w).card)
    (htaylor : ∀ p ∈ HuxleyLinearForm.fareySector K l w,
      |g ((p.1:ℝ)/p.2)-g y₀-deriv g y₀*((p.1:ℝ)/p.2-y₀)| ≤
        C*|((p.1:ℝ)/p.2)-y₀|^2)
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector K l w,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/p.2)-H p| ≤ δ) :
    let η := δ+(K:ℝ)*C*(w-l)^2
    1536*B*η*(w*(K:ℝ))*(K:ℝ) < (HuxleyLinearForm.fareySector K l w).card →
    0 ≤ (p₀.1:ℝ) → (p₀.1:ℝ) ≤ 12*(w*(K:ℝ)) →
    0 < (p₀.2:ℝ) → (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    (p₀.1:ℝ)/p₀.2=y₀ →
    |(p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*g y₀-H₀| ≤ δ →
    H₀=p₀.1*round (α-deriv g y₀)+p₀.2*round (β-g y₀+y₀*deriv g y₀) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.sector_seed_label_of_taylor_remainders (K:=K) (l:=l) (w:=w) (B:=B) (y₀:=y₀) (α:=α) (β:=β) (δ:=δ) (C:=C) (g:=g) (H:=H) (p₀:=p₀) (H₀:=H₀) hl hw hlw hB hy₀ hδ hC hcard htaylor hnear

example
    {K : ℕ} {σ δ T M N R B dmin l w Bd Δ Q : ℝ}
    {p₀ : ℤ × ℤ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xseed : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ} {e r v s : Fin 2 → ℤ}
    {cnew : ℤ × ℤ → Fin 2 → ℤ} {cseed : Fin 2 → ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 1 ≤ M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hNscale : N^2 ≤ M*R) (hscale : T*N*R^2=M^3)
    (hB : 0 ≤ B) (hdmin : 0 < dmin) (hΔ : 0 ≤ Δ) (hQ : 0 ≤ Q)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ p ∈ HuxleyLinearForm.fareySector K l w, ∀ i,
      x₁ ((p.1:ℝ)/p.2) i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hxseed : ∀ i, xseed i∈Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : 0 < l) (hw : 1 ≤ w) (hlw : l ≤ w) (hBd : 1 ≤ Bd) (htseed : 0 < p₀.2)
    (hyseed : (p₀.1:ℝ)/p₀.2∈Set.Icc l w)
    (hden : ∀ y ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*y+s i) :
    let S := HuxleyLinearForm.fareySector K l w
    let y₀ := (p₀.1:ℝ)/p₀.2
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let a := fun i => round (x₀ i)
    let b := fun y i => round (x₁ y i)
    let n := fun y i => b y i-a i
    let μ := fun i => iteratedDeriv 3 (f i) (a i)/6
    let μseed := fun i => iteratedDeriv 3 (f i) (round (xseed i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (a i)/24
    let q := fun (p : ℤ × ℤ) i => (r i:ℝ)*p.1+s i*p.2
    let d₀ := fun i => iteratedDeriv 1 (f i) (a i)
    let δ₀ := fun i => iteratedDeriv 2 (f i) (a i)/2-(e i:ℝ)/r i
    let θ := fun i => (r i:ℝ)*d₀ i-round ((r i:ℝ)*d₀ i)
    let β₀ := fun i => d₀ i*s i+2*δ₀ i/(3*μ i*r i)
    let α := θ 0-θ 1
    let β := β₀ 0-β₀ 1
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun y => g y-h y
    let z := fun (p : ℤ × ℤ) i => q p i*iteratedDeriv 1 (f i) (b ((p.1:ℝ)/p.2) i)
    let zseed := fun i => q p₀ i*iteratedDeriv 1 (f i) (round (xseed i))
    let jseed := fun i => round ((r i:ℝ)*d₀ i)*p₀.1+
      2*(round (xseed i)-a i)*(e i*p₀.1+v i*p₀.2)
    let Hseed := (cseed 0-jseed 0)-(cseed 1-jseed 1)
    let C := (2/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*Q/N
    let η := D+(K:ℝ)*C*(w-l)^2
    let U := (4/modelPhaseThirdLower σ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    l ∈ finiteBoundaryCell Z l w k →
    w ∈ finiteBoundaryCell Z l w k →
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(e i:ℝ)/r i) →
    (∀ i, iteratedDeriv 2 (f i) (xseed i)/2=((e i:ℝ)*p₀.1+v i*p₀.2)/q p₀ i) →
    (∀ i, |(round (xseed i):ℝ)-(a i:ℝ)|^2 ≤ M*R) →
    (∀ p ∈ S, ∀ i,
      iteratedDeriv 2 (f i) (x₁ ((p.1:ℝ)/p.2) i)/2=((e i:ℝ)*p.1+v i*p.2)/q p i) →
    (∀ p ∈ S, ∀ i, |(n ((p.1:ℝ)/p.2) i:ℝ)|^2 ≤ M*R) →
    |μseed 1*(q p₀ 1)^3/(μseed 0*(q p₀ 0)^3)-1| ≤ B*R^2/N^2 →
    (∀ p ∈ S, |(z p 0-cnew p 0)-(z p 1-cnew p 1)| ≤ Δ) →
    (∀ p ∈ S, |q p 0|+|q p 1| ≤ Q) →
    max ((w-l)*(K:ℝ)^2/Bd) 2 ≤ S.card →
    1536*Bd*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    (p₀.1:ℝ) ≤ 12*(w*(K:ℝ)) →
    (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    |(zseed 0-cseed 0)-(zseed 1-cseed 1)| ≤ Δ →
    |q p₀ 0|+|q p₀ 1| ≤ Q →
    Hseed=p₀.1*round (α-deriv φ y₀)+p₀.2*round (β-φ y₀+y₀*deriv φ y₀) ∧
    |(α-round (α-deriv φ y₀))*y₀+
      (β-round (β-φ y₀+y₀*deriv φ y₀))-φ y₀| ≤ D/(p₀.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_original_seed_linearization (K:=K) (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (B:=B) (dmin:=dmin) (l:=l) (w:=w) (Bd:=Bd) (Δ:=Δ) (Q:=Q) (p₀:=p₀) (k:=k) (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xseed:=xseed) (x₁:=x₁) (e:=e) (r:=r) (v:=v) (s:=s) (cnew:=cnew) (cseed:=cseed) hσ hδ hF hT hM hN hR hRM hNscale hscale hB hdmin hΔ hQ hA hW hx₀ hx₁ hxseed hr hdet hl hw hlw hBd htseed hyseed hden

example
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → 0 < r → 0 < s →
    (e:ℝ)/r < (rat 0:ℝ)-ε →
    (rat 0:ℝ)+ε < (v:ℝ)/s →
    (r:ℝ)*((rat 0:ℝ)+ε)-e ≤ 2*((r:ℝ)*((rat 0:ℝ)-ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*((r:ℝ)*l-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤ D/(pseed.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_residual (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {σ δ T M N R L dmin : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → 0 < r → 0 < s →
    (e:ℝ)/r < (rat 0:ℝ)-ε →
    (rat 0:ℝ)+ε < (v:ℝ)/s →
    (r:ℝ)*((rat 0:ℝ)+ε)-e ≤ 2*((r:ℝ)*((rat 0:ℝ)-ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*((r:ℝ)*l-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    0 < L →
    modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2 →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    (H+L*N+1)^2 ≤ M*R →
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x₀ i| ≤ L*N ∧
        |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1) ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    ∀ k : Fin 17, α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤ D/(pseed.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_seed_residual (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (dmin:=dmin) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → ℝ) (hS : 288 ≤ S.card)
    {σ δ T M A W step base μ ν r s μ₁ ν₁ r₁ s₁ U l w y₀ ac bc e v : ℝ}
    {F : ℝ → ℝ} {k : Fin 17}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hdet : v*r-e*s=1)
    (hden : ∀ z∈Icc l w, 0 < r*z+s)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hwidth : U*(w-l) ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2)
    (hpt : ∀ i∈S, 0 < (p i).2)
    (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hwindow : ∀ i∈S, x i∈Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let f := heathBrownPhysicalPhase F T M A 1
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    (∀ i∈S, iteratedDeriv 2 f (x i)/2=
      (e*(p i).1+v*(p i).2)/(r*(p i).1+s*(p i).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      StrictAnti (fun i => y (j i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/144 ≤ x (j i.succ)-x (j i.castSucc)) ∧
      ∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/144) ≤
        minorArcCoordinate μ r s (y (j i.succ))-
        minorArcCoordinate μ r s (y (j i.castSucc)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_common_coefficient_samples S p x hS (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (step:=step) (base:=base) (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (e:=e) (v:=v) (F:=F) (k:=k) hσ hδ hF hT hM hA hW hstep hμ hμ₁ hr hr₁ hdet hden hden₁ hwidth hheight hpt hx hwindow

example
    {σ δ T M : ℝ} {F : Fin 2 → ℝ → ℝ} {A W x y target : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ i, x i∈Ioo 0 (W i)) (hy : ∀ i, y i∈Ioo 0 (W i)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x i)/2=target i) →
    (∀ i, iteratedDeriv 2 (f i) (y i)/2=target i) → x=y :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_reference_roots_unique (σ:=σ) (δ:=δ) (T:=T) (M:=M) (F:=F) (A:=A) (W:=W) (x:=x) (y:=y) (target:=target) hσ hδ hF hT hM hA hW hx hy

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_integer_labels_enlarged_rectangle
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_original_seed_enlarged_rectangle
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_seed_label_of_taylor_remainders
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_original_seed_linearization
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_residual
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_seed_residual
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_common_coefficient_samples
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_reference_roots_unique

example
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → 0 < r → 0 < s →
    (e:ℝ)/r < (rat 0:ℝ)-ε →
    (rat 0:ℝ)+ε < (v:ℝ)/s →
    (r:ℝ)*((rat 0:ℝ)+ε)-e ≤ 2*((r:ℝ)*((rat 0:ℝ)-ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*((r:ℝ)*l-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_source_residual (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → 0 < r → 0 < s →
    (e:ℝ)/r < (rat 0:ℝ)-ε →
    (rat 0:ℝ)+ε < (v:ℝ)/s →
    (r:ℝ)*((rat 0:ℝ)+ε)-e ≤ 2*((r:ℝ)*((rat 0:ℝ)-ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*((r:ℝ)*l-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_source_bounds (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {σ δ T M N R L dmin : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → 0 < r → 0 < s →
    (e:ℝ)/r < (rat 0:ℝ)-ε →
    (rat 0:ℝ)+ε < (v:ℝ)/s →
    (r:ℝ)*((rat 0:ℝ)+ε)-e ≤ 2*((r:ℝ)*((rat 0:ℝ)-ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*((r:ℝ)*l-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    0 < L →
    modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2 →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    (H+L*N+1)^2 ≤ M*R →
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x₀ i| ≤ L*N ∧
        |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1) ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    ∀ k : Fin 17, α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_source_bounds (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (dmin:=dmin) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {C J μ N R r s d l w Bcut : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : 0 < r) (hs : 0 ≤ s) (hd : 0 < d)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hw : 1 ≤ w)
    (hdlo : d ≤ r*l+s) (hdhi : r*w+s ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : minorArcCoordinate μ r s l ≤ r*N^2/(Bcut*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l) ≤ 1/2 ∧
      U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coefficient_budgets_of_source_coordinate_cutoff (C:=C) (J:=J) (μ:=μ) (N:=N) (R:=R) (r:=r) (s:=s) (d:=d) (l:=l) (w:=w) (Bcut:=Bcut) hC hJ hμ hN hR hr hs hd hl hlw hw hdlo hdhi hμupper hBcut hBsize hG

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ) (hS : 288 ≤ S.card)
    {σ δ T M N R base d K nSpan Ccurv Bcut l w y₀ ac bc : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hK : 0 ≤ K) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hr₀ : 0 < r 0) (hs₀ : 0 ≤ s 0) (hl : 0 ≤ l) (hw : 1 ≤ w)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : 5*Ccurv*(σ*(σ+1)+1) ≤ Bcut) :
    let U := Ccurv*R^4/(N*d^3)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let μ := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
    let y := fun j => ((p j).1:ℝ)/(p j).2
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(144*(σ*(σ+1)+1))*(S.card:ℝ)
    G l ≤ r 0*N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      K*R^2/|r 0*G (y j)|) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    |r 0*s 1-s 0*r 1| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_determinant S p x hS (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (K:=K) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hσ hδ hF hT hM hN hR hd hK hRM hscale hA hW hxref hpt hx hwindow hdisplacement hspan hsourcecube hr hdet hden hr₀ hs₀ hl hw hCcurv hBcut hBsize

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_source_residual
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_source_bounds
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_source_bounds
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coefficient_budgets_of_source_coordinate_cutoff
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_determinant


example
    (S : Finset ℕ) (y : ℕ → ℝ) (hS : 288 ≤ S.card)
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ ac bc : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hwidth : U*(w-l) ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      (∀ i : Fin 7, (S.card:ℝ)/144 ≤ (j i.succ:ℝ)-(j i.castSucc:ℝ)-1) ∧
      ∀ i : Fin 7, (S.card:ℝ)/144 ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_common_coefficient_windows_with_mass S y hS (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ hwidth hheight

example
    {σ δ T M N R L d K α β nSpan : ℝ} (x : Fin 8 → ℝ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ e r v s : Fin 2 → ℝ}
    {x₁ : ℝ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hL : 0 < L)
    (hNL : (L*N)^2 ≤ M*R) (hd : 0 < d) (hK : 0 ≤ K)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hx₁ : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      x₁ y i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, d ≤ r i*y+s i)
    (hdenUpper : ∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, r i*y+s i ≤ 2*d)
    (hmono : StrictMono x)
    (hsize : L*N ≤ nSpan) (hcube : nSpan^3 ≤ M*R^2)
    (hwindow : ∀ y∈Icc (x 0) (x 7), ∀ z∈Icc (x 0) (x 7), ∀ i,
      |(round (x₁ y i):ℝ)-(round (x₁ z i):ℝ)| ≤ nSpan) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let n := fun y i => (round (x₁ y i):ℝ)-(round (x₀ i):ℝ)
    let μ := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let μnew := fun y i => iteratedDeriv 3 (f i) (round (x₁ y i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (x₀ i))/24
    let D := fun y i => r i*y+s i
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let H := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=e i/r i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i,
      iteratedDeriv 2 (f i) (x₁ y i)/2=(e i*y+v i)/D y i) →
    (∀ y ∈ Set.Icc (x 0) (x 7), ∀ i, |n y i|^2 ≤ M*R) →
    (∀ j : Fin 7, L*N ≤ |G (x j.succ)-G (x j.castSucc)|) →
    (∀ j : Fin 8, |α*x j+β-g (x j)+H (x j)| ≤ K*R^2/|r 0*G (x j)|) →

    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    ∀ z∈Icc (x 3) (x 4),
      |μnew z 1*(D z 1)^3/(μnew z 0*(D z 0)^3)-1| ≤
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_middle_third_condition (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (d:=d) (K:=K) (α:=α) (β:=β) (nSpan:=nSpan) x (F:=F) (A:=A) (W:=W) (x₀:=x₀) (e:=e) (r:=r) (v:=v) (s:=s) (x₁:=x₁) hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hx₀ hx₁ hr hdet hden hdenUpper hmono hsize hcube hwindow

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → ℝ) (hS : 288 ≤ S.card)
    {σ δ T M A W step base μ ν r s μ₁ ν₁ r₁ s₁ U l w y₀ ac bc e v : ℝ}
    {F : ℝ → ℝ} {k : Fin 17}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hdet : v*r-e*s=1)
    (hden : ∀ z∈Icc l w, 0 < r*z+s)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hwidth : U*(w-l) ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2)
    (hpt : ∀ i∈S, 0 < (p i).2)
    (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hwindow : ∀ i∈S, x i∈Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let f := heathBrownPhysicalPhase F T M A 1
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    (∀ i∈S, iteratedDeriv 2 f (x i)/2=
      (e*(p i).1+v*(p i).2)/(r*(p i).1+s*(p i).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      StrictAnti (fun i => y (j i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/144 ≤ x (j i.succ)-x (j i.castSucc)) ∧
      (∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/144) ≤
        minorArcCoordinate μ r s (y (j i.succ))-
        minorArcCoordinate μ r s (y (j i.castSucc))) ∧
      (∀ i : Fin 7, (S.card:ℝ)/144 ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ)) ∧
      AntitoneOn y (S:Set ℕ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_common_coefficient_samples_with_mass S p x hS (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (step:=step) (base:=base) (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (e:=e) (v:=v) (F:=F) (k:=k) hσ hδ hF hT hM hA hW hstep hμ hμ₁ hr hr₁ hdet hden hden₁ hwidth hheight hpt hx hwindow

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ) (hS : 288 ≤ S.card)
    {σ δ T M N R base d K nSpan Ccurv Bcut l w y₀ ac bc : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hK : 0 ≤ K) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hr₀ : 0 < r 0) (hs₀ : 0 ≤ s 0) (hl : 0 ≤ l) (hw : 1 ≤ w)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : 5*Ccurv*(σ*(σ+1)+1) ≤ Bcut) :
    let U := Ccurv*R^4/(N*d^3)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let μ := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
    let y := fun j => ((p j).1:ℝ)/(p j).2
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(144*(σ*(σ+1)+1))*(S.card:ℝ)
    G l ≤ r 0*N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      K*R^2/|r 0*G (y j)|) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    ∃ E : Finset ℕ, E ⊆ S ∧ (S.card:ℝ)/144 ≤ (E.card:ℝ) ∧
      ∀ j∈E,
        |(iteratedDeriv 3 (f 1) (round (x j 1))/6)*(r 1*y j+s 1)^3/
          ((iteratedDeriv 3 (f 0) (round (x j 0))/6)*(r 0*y j+s 0)^3)-1| ≤
          (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_third_mass S p x hS (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (K:=K) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hσ hδ hF hT hM hN hR hd hK hRM hscale hA hW hxref hpt hx hwindow hdisplacement hspan hsourcecube hr hdet hden hr₀ hs₀ hl hw hCcurv hBcut hBsize

example
    (S : Finset ℕ) (hS : 288 ≤ S.card) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s)
    (hd : 0 < d) (hl : 0 ≤ l) (hw : 1 ≤ w) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, (e:ℝ)/r < (rat j 0:ℝ)-ε) →
    (∀ j∈S, (rat j 0:ℝ)+ε < (v:ℝ)/s) →
    (∀ j∈S, (r:ℝ)*((rat j 0:ℝ)+ε)-e ≤
      2*((r:ℝ)*((rat j 0:ℝ)-ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*((r:ℝ)*lo j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let U := Ccurv*R^4/(N*d^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    Δ < 1/2 →
    (∀ j∈S, 1 ≤ β j) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 1536*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    G l ≤ (rp 0:ℝ)*N^2/(Bcut*R^2) →
    let Γ := Cphys/κ
    let L := κ/(144*Cphys)*(S.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    ∃ E : Finset ℕ, E ⊆ S ∧ (S.card:ℝ)/144 ≤ (E.card:ℝ) ∧
      ∀ j∈E, |mu j 1*(q j 1:ℝ)^3/(mu j 0*(q j 0:ℝ)^3)-1| ≤
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_family_long_block S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hs hd hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_common_coefficient_windows_with_mass
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_middle_third_condition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_common_coefficient_samples_with_mass
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_third_mass
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_family_long_block

example
    (S : Finset ℕ) (x y : ℕ → ℝ) (a b c d : ℤ)
    {σ δ T M Δ N R Z : ℝ} {τ A W : Fin 2 → ℝ} {F : Fin 2 → ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hδ0 : 0 ≤ δ)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hτ : ∀ i, T ≤ τ i ∧ τ i ≤ 2*T) (hM : 0 < M) (hN : 0 < N)
    (hphase : T*N*R^2=M^3) (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hΔ : 0 ≤ Δ) (hdet : a*d-b*c=1) (hc : c ≠ 0)
    (hscale : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤ |(c:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (hx : ∀ p ∈ S, x p ∈ Set.Ioo (1/2:ℝ) (W 0-1/2))
    (hy : ∀ p ∈ S, y p ∈ Set.Ioo (1/2:ℝ) (W 1-1/2))
    (hwindow : ∀ k ∈ S, Z+(k:ℝ)*N ≤ x k ∧ x k ≤ Z+((k:ℝ)+1)*N) :
    let f := fun i => heathBrownPhysicalPhase (F i) (τ i) M (A i) 1
    let μ := fun i z => iteratedDeriv 3 (f i) (round z)/6
    let t := fun p : ℕ => (c:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+d
    (∀ p ∈ S, ((a:ℝ)*(iteratedDeriv 2 (f 0) (x p)/2)+b)/t p=
      iteratedDeriv 2 (f 1) (y p)/2) →
    (∀ p ∈ S, (1:ℝ)/2 ≤ t p ∧ t p ≤ 2) →
    (∀ p ∈ S, |μ 1 (y p)*(t p)^3/μ 0 (x p)-1| ≤ Δ) →
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let η := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
    (S.card:ℝ) ≤ 2+32*(σ*(σ+1)+1)*(Γ^2*Δ+2*Γ*η)*R^2/(κ^2*|(c:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_paired_large_entry_nat_block_count S x y a b c d (σ:=σ) (δ:=δ) (T:=T) (M:=M) (Δ:=Δ) (N:=N) (R:=R) (Z:=Z) (τ:=τ) (A:=A) (W:=W) (F:=F) hσ hδ hδ0 hF hT hτ hM hN hphase hA hW hΔ hdet hc hscale hx hy hwindow

example
    (S : Finset ℕ) (hS : 288 ≤ S.card) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s)
    (hd : 0 < d) (hl : 0 ≤ l) (hw : 1 ≤ w) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2))
    (hc : Mat 2 ≠ 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, (e:ℝ)/r < (rat j 0:ℝ)-ε) →
    (∀ j∈S, (rat j 0:ℝ)+ε < (v:ℝ)/s) →
    (∀ j∈S, (r:ℝ)*((rat j 0:ℝ)+ε)-e ≤
      2*((r:ℝ)*((rat j 0:ℝ)-ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*((r:ℝ)*lo j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let U := Ccurv*R^4/(N*d^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    Δ < 1/2 →
    (∀ j∈S, 1 ≤ β j) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 1536*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    G l ≤ (rp 0:ℝ)*N^2/(Bcut*R^2) →
    let Γ := Cphys/κ
    let L := κ/(144*Cphys)*(S.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Ccount := (4608*Cphys/κ^2)*
      (Γ^2*(Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)+
        Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    (S.card:ℝ) ≤ 288+Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_large_entry_family_count S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hs hd hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_paired_large_entry_nat_block_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_large_entry_family_count

example
    (S : Finset ℕ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε boundary : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N)) :
    let f := heathBrownPhysicalPhase F T M A 1
    (∀ j∈S, |iteratedDeriv 2 f (x j)/2-boundary| ≤ ε) →
    S.card ≤ 3 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_curvature_boundary_window_count S x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (N:=N) (R:=R) (base:=base) (ε:=ε) (boundary:=boundary) (F:=F) hσ hδ hF hT hM hN hR hA hW hphase hsmall hx hwindow

example
    (S : Finset ℕ) (Z : Finset ℝ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε e r v s : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hZden : ∀ z∈Z, 0 < r*z+s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (∀ j∈S, 0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e) →
    ((S.filter (fun j => ∃ z∈Z, z∈Icc (α j) (β j))).card ≤ 3*Z.card) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_boundary_crossing_count S Z x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (N:=N) (R:=R) (base:=base) (ε:=ε) (e:=e) (r:=r) (v:=v) (s:=s) (F:=F) hσ hδ hF hT hM hN hR hA hW hphase hsmall hx hwindow hZden

example
    (S : Finset ℕ) (Z : Finset ℝ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε e r v s l w : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ) (hε : 0 ≤ ε)
    (hdet : v*r-e*s=1) (hr : 0 < r) (hZ : Z.card ≤ 16)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hregion : ∀ z∈Icc l w, 0 < r*z+s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (∀ j∈S, 0 < r*(q j-ε)-e) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    ∃ (k : Fin 17) (E : Finset ℕ), E⊆S ∧ S.card ≤ 48+17*E.card ∧
      ∀ j∈E, α j∈finiteBoundaryCell Z l w k ∧ β j∈finiteBoundaryCell Z l w k :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_common_cell_selection S Z x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (N:=N) (R:=R) (base:=base) (ε:=ε) (e:=e) (r:=r) (v:=v) (s:=s) (l:=l) (w:=w) (F:=F) hσ hδ hF hT hM hN hR hA hW hphase hsmall hε hdet hr hZ hx hwindow hregion

example
    (S : Finset ℕ) (x : ℕ → ℝ)
    {μ ν μ₁ ν₁ r₁ s₁ U : ℝ}
    {σ δ T M A W N R base e r v s l w : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hdet : v*r-e*s=1) (hr : 0 < r)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hregion : ∀ z∈Icc l w, 0 < r*z+s) :
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+3)*R^2)
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (∀ j∈S, 0 < r*(q j-ε)-e) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    ∃ (k : Fin 17) (E : Finset ℕ), E⊆S ∧ S.card ≤ 48+17*E.card ∧
      ∀ j∈E, α j∈finiteBoundaryCell Z l w k ∧ β j∈finiteBoundaryCell Z l w k :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_common_cell_selection S x (μ:=μ) (ν:=ν) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (N:=N) (R:=R) (base:=base) (e:=e) (r:=r) (v:=v) (s:=s) (l:=l) (w:=w) (F:=F) hσ hδ hF hT hM hN hR hA hW hphase hdet hr hx hwindow hregion

example
    (rat : Fin 2 → ℚ) (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    (hchart : v*r-e*s=1)
    (hMatt : (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=((rat 1).den:ℝ)/(rat 0).den)
    (hMatmap : ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ)) :
    let p : ℤ × ℤ := (v*((rat 0).den:ℤ)-s*(rat 0).num,
      r*(rat 0).num-e*((rat 0).den:ℤ))
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∀ i, (rp i:ℝ)*p.1+sp i*p.2=((rat i).den:ℝ) ∧
      (ep i:ℝ)*p.1+vp i*p.2=((rat i).num:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.farey_matrix_original_seed_coordinates rat Mat e r v s hchart hMatt hMatmap

example
    (S : Finset ℕ) (hS : 4944 ≤ S.card) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s)
    (hd : 0 < d) (hl : 0 ≤ l) (hw : 1 ≤ w) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, (e:ℝ)/r < (rat j 0:ℝ)-ε) →
    (∀ j∈S, (rat j 0:ℝ)+ε < (v:ℝ)/s) →
    (∀ j∈S, (r:ℝ)*((rat j 0:ℝ)+ε)-e ≤
      2*((r:ℝ)*((rat j 0:ℝ)-ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*((r:ℝ)*lo j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    Δ < 1/2 →
    (∀ j∈S, 1 ≤ β j) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 1536*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    G l ≤ (rp 0:ℝ)*N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Γ := Cphys/κ
    let L := κ/(144*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    ∃ E : Finset ℕ, E ⊆ S₀ ∧ (S₀.card:ℝ)/144 ≤ (E.card:ℝ) ∧
      ∀ j∈E, |mu j 1*(q j 1:ℝ)^3/(mu j 0*(q j 0:ℝ)^3)-1| ≤
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_long_block S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hs hd hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear

example
    (S : Finset ℕ) (x : ℕ → ℝ)
    {κ Cphys M N R nSpan H base center : ℝ}
    (hS : 288 ≤ S.card) (hκ : 0 < κ) (hCp : 0 < Cphys) (hκle : κ ≤ Cphys)
    (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hwindow : ∀ j∈S, x j∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, |x j-center| ≤ H)
    (hspan : 2*H+1 ≤ nSpan) :
    let L := κ/(144*Cphys)*(S.card:ℝ)
    L*N ≤ nSpan ∧ L^2*N^2 ≤ M*R^2 ∧ 1/M ≤ R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.occupied_cubic_span_inverse_budget S x (κ:=κ) (Cphys:=Cphys) (M:=M) (N:=N) (R:=R) (nSpan:=nSpan) (H:=H) (base:=base) (center:=center) hS hκ hCp hκle hM hN hR hRM hsourcecube hwindow hdisplacement hspan

example
    (S : Finset ℕ) (hS : 4944 ≤ S.card) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s)
    (hd : 0 < d) (hl : 0 ≤ l) (hw : 1 ≤ w) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2))
    (hc : Mat 2 ≠ 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, (e:ℝ)/r < (rat j 0:ℝ)-ε) →
    (∀ j∈S, (rat j 0:ℝ)+ε < (v:ℝ)/s) →
    (∀ j∈S, (r:ℝ)*((rat j 0:ℝ)+ε)-e ≤
      2*((r:ℝ)*((rat j 0:ℝ)-ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*((r:ℝ)*lo j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    Δ < 1/2 →
    (∀ j∈S, 1 ≤ β j) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 1536*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    G l ≤ (rp 0:ℝ)*N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Γ := Cphys/κ
    let L := κ/(144*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Ccount := (4608*Cphys/κ^2)*
      (Γ^2*(Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)+
        Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    (S.card:ℝ) ≤ 4944+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_family_count S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hs hd hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_curvature_boundary_window_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_boundary_crossing_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_common_cell_selection
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_common_cell_selection
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_matrix_original_seed_coordinates
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_long_block
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.occupied_cubic_span_inverse_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_family_count

example
    (S : Finset ℕ) (x : ℕ → Fin 2 → ℝ) (xref Hspan : Fin 2 → ℝ)
    {Cphys M N R nSpan base : ℝ}
    (hS : 288 ≤ S.card) (hC : 0 ≤ Cphys)
    (hM : 0 < M) (hN : 0 < N) (hNtwo : 2 ≤ N)
    (hR : 1 ≤ R) (hRM : R ≤ M)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i)
    (hspan : ∀ i, 2*Hspan i+1 ≤ nSpan) :
    let H := N/(Cphys+2)
    N^3 ≤ M*R^2 ∧ ∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R :=
  TaoTrudgianYang2025.HuxleyRationalPhase.occupied_cubic_span_buffer_budget S x xref Hspan (Cphys:=Cphys) (M:=M) (N:=N) (R:=R) (nSpan:=nSpan) (base:=base) hS hC hM hN hNtwo hR hRM hsourcecube hwindow hdisplacement hspan

example
    (S : Finset ℕ) (hS : 4944 ≤ S.card) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : 0 < r) (hs : 0 < s)
    (hd : 0 < d) (hl : 0 ≤ l) (hw : 1 ≤ w) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2))
    (hc : Mat 2 ≠ 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, (e:ℝ)/r < (rat j 0:ℝ)-ε) →
    (∀ j∈S, (rat j 0:ℝ)+ε < (v:ℝ)/s) →
    (∀ j∈S, (r:ℝ)*((rat j 0:ℝ)+ε)-e ≤
      2*((r:ℝ)*((rat j 0:ℝ)-ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*((r:ℝ)*lo j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    Δ < 1/2 →
    (∀ j∈S, 1 ≤ β j) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 1536*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    G l ≤ (rp 0:ℝ)*N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Γ := Cphys/κ
    let L := κ/(144*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Ccount := (4608*Cphys/κ^2)*
      (Γ^2*(Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)+
        Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    (S.card:ℝ) ≤ 4944+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_source_count S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hs hd hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge

example {Q : ℕ} {a : ℚ} {ε : ℝ}
    (hcut : 2*a.den ≤ Q) (hscale : 4 ≤ ε*(Q:ℝ)*a.den) :
    ∃ b : ℚ, b.den ≤ Q ∧ Q ≤ 2*b.den ∧
      (a:ℝ) < b ∧ |(b:ℝ)-(a:ℝ)| ≤ ε/2 ∧
      (b:ℝ)-(a:ℝ)=1/((a.den:ℝ)*b.den) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_dyadic_rational_near_anchor (Q:=Q) (a:=a) (ε:=ε) hcut hscale

example
    {Q : ℕ} {a : ℚ} {σ δ T M N R A W x : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hscale : T*N*R^2=M^3) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hx : x∈Ioo (1/2:ℝ) (W-1/2))
    (hcut : 2*a.den ≤ Q)
    (hmajor : 64*(σ*(σ+1)+3)*R^2 ≤ modelPhaseThirdLower σ*(Q:ℝ)*a.den) :
    let f := heathBrownPhysicalPhase F T M A 1
    let H := N/(σ*(σ+1)+3)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+3)*R^2)
    iteratedDeriv 2 f x/2=(a:ℝ) →
    x+H∈Ioo (1/2:ℝ) (W-1/2) →
    ∃ b : ℚ, b.den ≤ Q ∧ Q ≤ 2*b.den ∧
      (a:ℝ) < b ∧ |(b:ℝ)-(a:ℝ)| ≤ ε/2 ∧
      ∃ z∈Icc x (x+H/16), z∈Ioo (1/2:ℝ) (W-1/2) ∧
        iteratedDeriv 2 f z/2=(b:ℝ) ∧
        (round z:ℝ)∈Ioo 0 W ∧
        |(round z:ℝ)-(round x:ℝ)| ≤ H/16+1 ∧
        |iteratedDeriv 2 f (round z)/2-(b:ℝ)| ≤
          T*(modelPhaseJetCoefficient σ 2+δ)/(4*M^3) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_dyadic_anchor_center (Q:=Q) (a:=a) (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (A:=A) (W:=W) (x:=x) (F:=F) hσ hδ hF hT hM hN hR hscale hA hW hx hcut hmajor

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.occupied_cubic_span_buffer_budget
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_source_count
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_dyadic_rational_near_anchor
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_dyadic_anchor_center

example
    (F : ℝ → ℝ) {Q : ℕ} {a : ℚ} {σ c η y T M N R x : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hNM : N ≤ M)
    (hphase : T*N*R^2=M^3)
    (hx : x∈Icc (7*M/8) (17*M/8))
    (hcut : 2*a.den ≤ Q) (hmajor : 128*σ*R^2 ≤ c*(Q:ℝ)*a.den) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    iteratedDeriv 2 f x/2=(a:ℝ) →
    ∃ b : ℚ, b.den ≤ Q ∧ Q ≤ 2*b.den ∧
      (a:ℝ) < b ∧ |(b:ℝ)-(a:ℝ)| ≤ c/(64*σ*R^2) ∧
      ∃ z∈Icc x (x+N/16), iteratedDeriv 2 f z/2=(b:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_dyadic_anchor_center F (Q:=Q) (a:=a) (σ:=σ) (c:=c) (η:=η) (y:=y) (T:=T) (M:=M) (N:=N) (R:=R) (x:=x) hσ hc hη hηmax hy hf hnegative hT hM hN hR hNM hphase hx hcut hmajor

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N → (∀ i∈S, 2*(anchor i).den ≤ Q) →
      (∀ i∈S, 128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈S, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈S, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈S, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((1+Real.log K₀)*
            (∑ i∈S, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈S, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_dyadic_anchor_source_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (S : Finset ι) (F : ℝ → ℝ)
      (y : ι → ℝ) (L : ι → ℤ) (H : ι → ℕ) (anchor : ι → ℚ) (za : ι → ℝ)
      (N Q : ℕ) (η T M R : ℝ),
      1 ≤ N → (∀ i∈S, H i ≤ N) →
      0 < η → η ≤ 1/8 → 0 < T → 0 < M → 0 < R →
      (∀ i∈S, y i∈Icc (1:ℝ) 2) →
      (∀ i∈S, (L i:ℝ)-2*(N:ℝ)∈Icc M (2*M)) →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 →
      7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      Q ≤ N →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      (∀ i∈S, za i∈Ioo ((L i:ℝ)-2*(N:ℝ)-(N:ℝ)/8)
        ((L i:ℝ)-2*(N:ℝ)+(N:ℝ)/8) ∧
        iteratedDeriv 2 (f i) (za i)/2=(anchor i:ℝ)) →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
      ∃ (r : ι → ℚ) (z : ι → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i:ℝ) < r i ∧ |(r i:ℝ)-(anchor i:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i) (za i+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i) (z i)/2=(r i:ℝ)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i) (m i)/6
      let ℓ := fun i => deriv (f i) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈S, ‖∑ n∈Finset.Ioc (L i) (L i+H i),(𝐞 (f i n):ℂ)‖) ≤
          C*((∑ i∈S.filter (fun i => ¬ Good i),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_dyadic_anchor_source_partition (σ:=σ) (c:=c) (J:=J) hσ hc hJ

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (F : ℝ → ℝ) (N : ℕ) (s : ℤ) (H : ℤ → ℕ)
      (η y T M R U x₁ x₂ : ℝ),
      1 ≤ N → (∀ k, H k ≤ N) →
      0 < η → η ≤ 1/8 → y∈Icc (1:ℝ) 2 → 0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
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
      ∀ Q : ℕ, Q ≤ N →
      let Good := fun i => 2*(anchor i).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i).den
      let G := S.filter Good
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
          C*((∑ i∈S.filter (fun i => ¬ Good i),(H i:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_interior_gap_dyadic_source_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_dyadic_anchor_center
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_dyadic_anchor_source_fourier
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_dyadic_anchor_source_partition
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_interior_gap_dyadic_source_fourier

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, Q ≤ N →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*((∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_tagged_gap_dyadic_source_fourier (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_tagged_gap_dyadic_source_fourier

example
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hε : 0 < ε) :
    ∃ δ η₀ a : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y : ι → ℝ) (η : ℝ),
          (∀ i∈S, y i∈Icc (1:ℝ) 2) → 0 < η → η ≤ η₀ →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            ∀ xi T N R : ℝ, 0 < xi → 0 < T → 0 < R → T*N*R^2=M^3 →
            let Tnew := T*σ*y i₀/xi
            let Rnew := R*Real.sqrt (xi/(σ*y i₀))
            0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y i₀) ∧
              Tnew*N*Rnew^2=M^3 ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fext u-Fext (u+η*y i))/(σ*η*y i₀)
              let f := fun w => T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
                (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
                (∀ (A : ℤ) (w : ℝ) (k : ℕ),
                  iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
                    iteratedDeriv k f (round w)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_colored_linked_models (σ:=σ) (ε:=ε) hσ P hε

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_colored_linked_models

example {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε c J : ℝ, 0 < ε ∧ 0 < c ∧ 0 < J ∧
      ∀ Fext : ℝ → ℝ,
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6,
          |iteratedDeriv (n+1) Fext x-iteratedDeriv n (Expdb.modelPhase σ) x| ≤ ε) →
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ J) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -c) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.modelPhase_compact_jet_signed_source_tests (σ:=σ) hσ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.modelPhase_compact_jet_signed_source_tests

example
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hP : 5 ≤ P) (hε : 0 < ε) :
    ∃ δ η₀ a c J : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < c ∧ 0 < J ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ J) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -c) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        ∀ {ι : Type*} (S : Finset ι) (y : ι → ℝ) (η : ℝ),
          (∀ i∈S, y i∈Icc (1:ℝ) 2) → 0 < η → η ≤ η₀ →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            ∀ xi T N R : ℝ, 0 < xi → 0 < T → 0 < R → T*N*R^2=M^3 →
            let Tnew := T*σ*y i₀/xi
            let Rnew := R*Real.sqrt (xi/(σ*y i₀))
            0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y i₀) ∧
              Tnew*N*Rnew^2=M^3 ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fext u-Fext (u+η*y i))/(σ*η*y i₀)
              let f := fun w => T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
                (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
                (∀ (A : ℤ) (w : ℝ) (k : ℕ),
                  iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
                    iteratedDeriv k f (round w)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_colored_linked_source_tests (σ:=σ) (ε:=ε) hσ P hP hε

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_colored_linked_source_tests

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∀ (ι : Type*) (Y : Finset ι) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ι → ℤ → ℕ)
      (η T M R U : ℝ) (y x₁ x₂ : ι → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, y i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
      (∀ w, 0 < w → ContDiffAt ℝ ∞ F w) →
      (∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J) →
      (∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c) →
      T*(N:ℝ)*R^2=M^3 → 7*(N:ℝ)+2 ≤ M/4 →
      (3*J/σ)*(6*(N:ℝ)+1)^4 ≤ M*(N:ℝ)*R^2 →
      (3*J/(4*σ))*(6*(N:ℝ)+1)^2 ≤ (N:ℝ)*R^2 →
      3*J ≤ σ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*y i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ι → Finset ℤ) (anchor : ι → ℤ → ℚ) (za : ι → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, Q ≤ N →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      ∃ (r : ι × ℤ → ℚ) (z : ι × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ι × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*((∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ∧
    let μ₀ := c/(12*σ*(N:ℝ)*R^2)
    let U₀ := U₃
    let V := G ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ι × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let hcenter := fun i => iteratedDeriv 2 (f i.1) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ Mat : (((ι × ℤ) × Fin 2) × ((ι × ℤ) × Fin 2)) → Fin 4 → ℤ,
      ∀ ij∈P,
        Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
        let t := (Mat ij 2:ℝ)*hcenter ij.1.1+Mat ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((Mat ij 0:ℝ)*hcenter ij.1.1+Mat ij 1)/t=hcenter ij.2.1 ∧
        |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(Mat ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(Mat ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(Mat ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-hcenter ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          Mat ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_tagged_gap_dyadic_fourier_matrices (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_tagged_gap_dyadic_fourier_matrices

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∃ Kfiber Cfiber : ℝ, 0 < Kfiber ∧ 0 < Cfiber ∧ ∀ (Y : Finset ℝ) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ℝ → ℤ → ℕ)
      (η T M R U : ℝ) (x₁ x₂ : ℝ → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
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
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ℝ → Finset ℤ) (anchor : ℝ → ℤ → ℚ) (za : ℝ → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, Q ≤ N →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      ∃ (r : ℝ × ℤ → ℚ) (z : ℝ × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      ∀ (K₀ : ℕ) [NeZero K₀], 63*U₃*(Q:ℝ)*(N:ℝ)^2 ≤ K₀ →
      ∃ v : ℝ × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*((∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ∧
    let μ₀ := c/(12*σ*(N:ℝ)*R^2)
    let U₀ := U₃
    let V := G ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let hcenter := fun i => iteratedDeriv 2 (f i.1) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
        let t := (Mat ij 2:ℝ)*hcenter ij.1.1+Mat ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((Mat ij 0:ℝ)*hcenter ij.1.1+Mat ij 1)/t=hcenter ij.2.1 ∧
        |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(Mat ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(Mat ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(Mat ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-hcenter ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          Mat ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      ∀ Jsep : ℝ, 0 < Jsep →
      (∀ y∈Y, ∀ y'∈Y, y ≠ y' → 1 ≤ Jsep*|y-y'|) →
      let Δ := (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2)
      let B := max 1 (max (3*J/σ) (2*σ/c))
      (P.card:ℝ) ≤ 6*Kfiber*(1+8*Cfiber*B*(Δ+5/M)*Jsep)*
        ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_real_gap_fourier_matrix_fibers (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_real_gap_fourier_matrix_fibers

example
    {σ J N R Q : ℝ} (hσ : 0 < σ)
    (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q) (hbase : R^2 ≤ Q*N) :
    let C := max 1 (63*J/(2*σ))
    ∃ K₀ : ℕ, 0 < K₀ ∧
      63*(J/(2*σ*N*R^2))*Q*N^2 ≤ K₀ ∧
      Q*N ≤ (K₀:ℝ)*R^2 ∧
      (K₀:ℝ) ≤ 2*C*Q*N/R^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_positive_difference_source_fourier_mesh (σ:=σ) (J:=J) (N:=N) (R:=R) (Q:=Q) hσ hN hR hQ hbase

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.exists_positive_difference_source_fourier_mesh

example
    {σ c J N R Q K₀ : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hN : 0 < N) (hR : 0 < R) (hQ : 0 < Q)
    (hK : 1 ≤ K₀) (hmesh : Q*N ≤ K₀*R^2) :
    let μ₀ := c/(12*σ*N*R^2)
    let U₀ := J/(2*σ*N*R^2)
    (16*U₀/μ₀)*Real.sqrt (U₀*Q^3)*Real.sqrt K₀/(6*K₀^2) ≤
      (16*J/c)*Real.sqrt (J/(2*σ))*R^2/N^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_linked_cubic_error_bound (σ:=σ) (c:=c) (J:=J) (N:=N) (R:=R) (Q:=Q) (K₀:=K₀) hσ hc hJ hN hR hQ hK hmesh

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_linked_cubic_error_bound

example
    {σ c J : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J) :
    ∃ C ≥ (1:ℝ), ∃ Kfiber Cfiber : ℝ, 0 < Kfiber ∧ 0 < Cfiber ∧ ∀ (Y : Finset ℝ) (F : ℝ → ℝ)
      (N : ℕ) (s : ℤ) (H : ℝ → ℤ → ℕ)
      (η T M R U : ℝ) (x₁ x₂ : ℝ → ℝ),
      1 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ 1/8 → (∀ i∈Y, i∈Icc (1:ℝ) 2) →
      0 < T → 0 < M → 0 < R → 0 < U →
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
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      let f := fun i w => T*(F (w/M)-F (w/M+η*i))/(σ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*σ*R^2)
      let Vbound := 3*J*M/(2*σ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ℝ → Finset ℤ) (anchor : ℝ → ℤ → ℚ) (za : ℝ → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (σ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*σ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*σ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, Q ≤ N → R^2 ≤ (Q:ℝ)*(N:ℝ) →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*σ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      ∃ (r : ℝ × ℤ → ℚ) (z : ℝ × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*σ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*σ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      let Cmesh := max 1 (63*J/(2*σ))
      ∃ (K₀ : ℕ) (hKpos : 0 < K₀),
      let _ : NeZero K₀ := ⟨Nat.ne_of_gt hKpos⟩
      (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 ∧
      (K₀:ℝ) ≤ 2*Cmesh*(Q:ℝ)*(N:ℝ)/R^2 ∧
      ∃ v : ℝ × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*((∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ∧
    let μ₀ := c/(12*σ*(N:ℝ)*R^2)
    let U₀ := U₃
    let V := G ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let hcenter := fun i => iteratedDeriv 2 (f i.1) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
        let t := (Mat ij 2:ℝ)*hcenter ij.1.1+Mat ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((Mat ij 0:ℝ)*hcenter ij.1.1+Mat ij 1)/t=hcenter ij.2.1 ∧
        |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let F₁ := 2*(round (z ij.2.1):ℝ)-2*(Mat ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 2:ℝ)*ℓ ij.1.1
          let F₂ := ℓ ij.2.1-2*(Mat ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 0:ℝ)*ℓ ij.1.1
          |F₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(Mat ij 2:ℝ)|/q ij.1.1 ∧
          |(F₂-e₂)-hcenter ij.2.1*(F₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          Mat ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      ∀ Jsep : ℝ, 0 < Jsep →
      (∀ y∈Y, ∀ y'∈Y, y ≠ y' → 1 ≤ Jsep*|y-y'|) →
      let Δ := (16*J/c)*Real.sqrt (J/(2*σ))*R^2/(N:ℝ)^2
      let B := max 1 (max (3*J/σ) (2*σ/c))
      (P.card:ℝ) ≤ 6*Kfiber*(1+8*Cfiber*B*(Δ+5/M)*Jsep)*
        ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_real_gap_chosen_mesh_matrix_fibers (σ:=σ) (c:=c) (J:=J) hσ hc hJ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_real_gap_chosen_mesh_matrix_fibers

example
    {σ ε : ℝ} (hσ : 0 < σ) (P : ℕ) (hP : 5 ≤ P) (hε : 0 < ε) :
    ∃ δ η₀ a c J ξ C Kfiber Cfiber : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/8 ∧ 0 < a ∧ 0 < c ∧ 0 < J ∧
      0 < ξ ∧ 7203*J ≤ ξ ∧ 2*σ ≤ ξ ∧ 1 ≤ C ∧ 0 < Kfiber ∧ 0 < Cfiber ∧
      ∀ (M : ℝ) (F : ℝ → ℝ), 1 ≤ M →
      Expdb.IsApproximateModelPhaseFunction F σ (P+2) δ →
      ∃ Fext : ℝ → ℝ,
        (∀ w, 0 < w → ContDiffAt ℝ ∞ Fext w) ∧
        (∀ w∈Icc (1/2:ℝ) 3, ∀ p ≤ P+1,
          |iteratedDeriv (p+1) Fext w-iteratedDeriv p (Expdb.modelPhase σ) w| ≤ ε) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fext x| ≤ J) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, ∀ j,
          c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
            (fun i : Fin 4 => iteratedDeriv (i.val+3) Fext x) j|) ∧
        (∀ x ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 Fext x ≤ -c) ∧
        (∀ (T : ℝ) (m n : ℕ), M ≤ (m:ℝ) → (n:ℝ) ≤ 2*M →
          ‖Expdb.exponentialSumAt F T M m n-Expdb.exponentialSumAt Fext T M m n‖ ≤ 6) ∧
        (∀ {ι : Type*} (S : Finset ι) (y : ι → ℝ) (η : ℝ),
          (∀ i∈S, y i∈Icc (1:ℝ) 2) → 0 < η → η ≤ η₀ →
          let color := fun i => ⌊y i/a⌋
          let Cap := 4/a+3
          ((S.image color).card:ℝ) ≤ Cap ∧
          (∀ z : ι → ℂ, ‖∑ i∈S,z i‖^12 ≤
            Cap^11*∑ j∈S.image color, ‖∑ i∈S.filter (fun i => color i=j),z i‖^12) ∧
          ∀ j∈S.image color, ∃ i₀∈S, color i₀=j ∧
            ∀ xi T N R : ℝ, 0 < xi → 0 < T → 0 < R → T*N*R^2=M^3 →
            let Tnew := T*σ*y i₀/xi
            let Rnew := R*Real.sqrt (xi/(σ*y i₀))
            0 < Tnew ∧ 0 < Rnew ∧ Rnew^2=R^2*xi/(σ*y i₀) ∧
              Tnew*N*Rnew^2=M^3 ∧
            ∀ i∈S, color i=j →
              let G := fun u => (Fext u-Fext (u+η*y i))/(σ*η*y i₀)
              let f := fun w => T*(Fext (w/M)-Fext (w/M+η*y i))/(xi*η)
              Expdb.IsApproximateModelPhaseFunction G (σ+1) P ε ∧
                (∀ A x : ℝ, heathBrownPhysicalPhase G Tnew M A 1 x=f (A+x)) ∧
                (∀ (A : ℤ) (w : ℝ) (k : ℕ),
                  iteratedDeriv k (heathBrownPhysicalPhase G Tnew M A 1) (round (w-A))=
                    iteratedDeriv k f (round w))) ∧
        ∀ (Y : Finset ℝ)
      (N : ℕ) (s : ℤ) (H : ℝ → ℤ → ℕ)
      (η T R U : ℝ) (x₁ x₂ : ℝ → ℝ),
      29 ≤ N → (∀ i∈Y, ∀ k, H i k ≤ N) →
      0 < η → η ≤ η₀ → (∀ i∈Y, i∈Icc (1:ℝ) 2) →
      0 < T → 1 ≤ R → R ≤ (N:ℝ) → (N:ℝ) ≤ R^2 →
      (N:ℝ)^2 ≤ M → (N:ℝ)^10 ≤ M^3*R^7 → 0 < U →
      T*(N:ℝ)*R^2=M^3 →
      3*J ≤ ξ*U →
      (∀ i∈Y, x₁ i∈Icc M (2*M)) → (∀ i∈Y, x₂ i∈Icc M (2*M)) →
      let f := fun i w => T*(Fext (w/M)-Fext (w/M+η*i))/(ξ*η)
      let h := fun i w => iteratedDeriv 2 (f i) w/2
      let t := fun k : ℤ => (s:ℝ)+(N:ℝ)*k
      let L := fun k : ℤ => s+(N:ℤ)*k+2*(N:ℤ)
      let delta := c/(64*ξ*R^2)
      let Vbound := 3*J*M/(2*ξ*(N:ℝ)*R^2)
      (∀ i∈Y, U/(4*R^2) ≤ h i (x₂ i)-h i (x₁ i) ∧
        h i (x₂ i)-h i (x₁ i) ≤ 7*U/(2*R^2)) →
      ∃ (S : ℝ → Finset ℤ) (anchor : ℝ → ℤ → ℚ) (za : ℝ → ℤ → ℝ),
        (∀ i∈Y,
          (∀ k : ℤ, k∈(S i) ↔ (x₁ i)+(N:ℝ)/4 ≤ t k ∧ t k ≤ (x₂ i)-(N:ℝ)/4) ∧
        (∀ k∈(S i), (za i) k∈Ioo (x₁ i) (x₂ i) ∧ (h i) ((za i) k)=((anchor i) k:ℝ) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (x₁ i)) ((h i) (x₂ i)) ∧
          ((anchor i) k:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) ∧
          ∀ a : ℚ, (a:ℝ)∈Ioo ((h i) (t k)-delta) ((h i) (t k)+delta) → ((anchor i) k).den ≤ a.den) ∧
        (∀ k∈(S i), |(za i) k-t k| ≤ (N:ℝ)/16) ∧
        (ξ/(6*J))*U-3/2 ≤ ((S i).card:ℝ) ∧ ((S i).card:ℝ) ≤ (56*ξ/c)*U+1/2 ∧
        (∀ Q : ℕ, 2 ≤ Q →
          let D := 64*ξ*R^2/(c*(Q:ℝ))
          (((S i).filter (fun k => Q ≤ ((anchor i) k).den)).card:ℝ) ≤
            4*(Vbound+1)*D^2+D*(2+Real.log (D+1)))) ∧
      ∀ Q : ℕ, Q ≤ N → R^2 ≤ (Q:ℝ)*(N:ℝ) →
      let Sall := Y.biUnion (fun i => (S i).image (fun k => (i,k)))
      let Good := fun i => 2*(anchor i.1 i.2).den ≤ Q ∧
        128*ξ*R^2 ≤ c*(Q:ℝ)*(anchor i.1 i.2).den
      let G := Sall.filter Good
      ∃ (r : ℝ × ℤ → ℚ) (z : ℝ × ℤ → ℝ),
      (∀ i∈G, (r i).den ≤ Q ∧ Q ≤ 2*(r i).den ∧
        (anchor i.1 i.2:ℝ) < r i ∧ |(r i:ℝ)-(anchor i.1 i.2:ℝ)| ≤ c/(64*ξ*R^2) ∧
        z i∈Icc (za i.1 i.2) (za i.1 i.2+(N:ℝ)/16) ∧
        iteratedDeriv 2 (f i.1) (z i)/2=(r i:ℝ)) ∧
      (∀ i∈G, z i∈Ioo (x₁ i.1) (x₂ i.1)) ∧
      let m := fun i => round (z i)
      let A := fun i => (L i.2-m i).toNat
      let q := fun i => (r i).den
      let μ := fun i => iteratedDeriv 3 (f i.1) (m i)/6
      let ℓ := fun i => deriv (f i.1) (m i)
      let U₃ := J/(2*ξ*(N:ℝ)*R^2)
      (∀ i∈G, |z i-(m i:ℝ)| ≤ 1/2 ∧
        N ≤ A i ∧ A i ≤ 3*N ∧ m i+(A i:ℤ)=L i.2) ∧
      let Cmesh := max 1 (63*J/(2*ξ))
      ∃ (K₀ : ℕ) (hKpos : 0 < K₀),
      let _ : NeZero K₀ := ⟨Nat.ne_of_gt hKpos⟩
      (Q:ℝ)*(N:ℝ) ≤ (K₀:ℝ)*R^2 ∧
      (K₀:ℝ) ≤ 2*Cmesh*(Q:ℝ)*(N:ℝ)/R^2 ∧
      ∃ v : ℝ × ℤ → ℤ, (∀ i∈G, (q i:ℤ) ∣ (r i).num*v i-1) ∧
      let b := fun i (p : Fin 2) => (⌊(q i:ℝ)*ℓ i⌋+(p:ℕ) : ℤ)
      let τ := fun i p => ((b i p:ℝ)-(q i:ℝ)*ℓ i)/2
      let s := fun i => Real.sqrt (2/(3*μ i*(q i:ℝ)))
      let K := fun i => -2*μ i*(s i)^3
      let x := fun i p =>
        (![-(v i:ℝ)*b i p/q i,-(v i:ℝ)/q i,K i,3*K i*τ i p/2] : Fin 4 → ℝ)
      ∃ k : ZMod K₀,
        (∑ i∈Sall, ‖∑ n∈Finset.Ioc (L i.2) (L i.2+H i.1 i.2),(𝐞 (f i.1 n):ℂ)‖) ≤
          C*((∑ i∈Sall.filter (fun i => ¬ Good i),(H i.1 i.2:ℝ))+
            (1+Real.log K₀)*
            (∑ i∈G, ∑ p : Fin 2,
              (Real.sqrt (2*(q i:ℝ))/((q i:ℝ)*Real.sqrt (μ i*A i)))*
              ‖∑ j : ZMod K₀,ZMod.stdAddChar (-(j*k))*
                GafniTao.fordAdditiveCharacter (∑ d,x i p d*
                  (![(j.val+1:ℝ),(j.val+1:ℝ)^2,(j.val+1:ℝ)^((3:ℝ)/2),
                    Real.sqrt (j.val+1:ℝ)] : Fin 4 → ℝ) d)‖)+
            ∑ i∈G, (Real.sqrt (A i)*Real.log (2*(A i:ℝ))+1/(μ i*(A i:ℝ)^2))) ∧
    let μ₀ := c/(12*ξ*(N:ℝ)*R^2)
    let U₀ := U₃
    let V := G ×ˢ (Finset.univ : Finset (Fin 2))
    let w := fun ip : (ℝ × ℤ) × Fin 2 =>
      (![Int.fract (x ip.1 ip.2 0),Int.fract (x ip.1 ip.2 1),
        x ip.1 ip.2 2/Real.sqrt K₀,x ip.1 ip.2 3/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    let P := (V ×ˢ V).filter (fun ij => ∀ d, |w ij.1 d-w ij.2 d| ≤ 2*radius d)
    let hcenter := fun i => iteratedDeriv 2 (f i.1) (z i)/2
    let D := (Real.sqrt K₀/(9*(K₀:ℝ))+Real.sqrt K₀/(12*(K₀:ℝ)^2))*
      Real.sqrt (U₀*(Q:ℝ)^3)
    ∃ Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ,
      (∀ ij∈P,
        Mat ij 0*Mat ij 3-Mat ij 1*Mat ij 2=1 ∧
        let t := (Mat ij 2:ℝ)*hcenter ij.1.1+Mat ij 3
        t=(q ij.2.1:ℝ)/q ij.1.1 ∧ (1:ℝ)/2 ≤ t ∧ t ≤ 2 ∧
        ((Mat ij 0:ℝ)*hcenter ij.1.1+Mat ij 1)/t=hcenter ij.2.1 ∧
        |(Mat ij 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) ∧
        |μ ij.2.1/μ ij.1.1*t^3-1| ≤
          (16*U₀/μ₀)*Real.sqrt (U₀*(Q:ℝ)^3)*Real.sqrt K₀/(6*(K₀:ℝ)^2) ∧
        |τ ij.1.1 ij.1.2-τ ij.2.1 ij.2.2| ≤ D ∧
        (∃ e₁ e₂ : ℤ,
          let Fext₁ := 2*(round (z ij.2.1):ℝ)-2*(Mat ij 3:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 2:ℝ)*ℓ ij.1.1
          let Fext₂ := ℓ ij.2.1-2*(Mat ij 1:ℝ)*(round (z ij.1.1):ℝ)-
            (Mat ij 0:ℝ)*ℓ ij.1.1
          |Fext₁-e₁| ≤ (q ij.2.1:ℝ)/(6*(K₀:ℝ))+|(Mat ij 2:ℝ)|/q ij.1.1 ∧
          |(Fext₂-e₂)-hcenter ij.2.1*(Fext₁-e₁)| ≤ 2*D/q ij.2.1) ∧
        ((Q:ℝ)^2/(6*(K₀:ℝ)^2) < 1 →
          Mat ij 2=0 ∧ q ij.1.1=q ij.2.1 ∧
            (q ij.1.1:ℤ) ∣ (r ij.2.1).num-(r ij.1.1).num)) ∧
      ∀ Jsep : ℝ, 0 < Jsep →
      (∀ y∈Y, ∀ y'∈Y, y ≠ y' → 1 ≤ Jsep*|y-y'|) →
      let Δ := (16*J/c)*Real.sqrt (J/(2*ξ))*R^2/(N:ℝ)^2
      let B := max 1 (max (3*J/ξ) (2*ξ/c))
      (P.card:ℝ) ≤ 6*Kfiber*(1+8*Cfiber*B*(Δ+5/M)*Jsep)*
        ((P.image (fun ij => (Mat ij,ij.1))).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_chosen_mesh_source_family (σ:=σ) (ε:=ε) hσ P hP hε

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.approximateModelPhase_enlarged_chosen_mesh_source_family

example
    {σ δ T M N R L : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (Mat : Fin 4 → ℤ) (e r : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hLpos : 0 < L) (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hdet : Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hgamma : |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2))
    (hwindow : modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2)
    (hr : r ≠ 0) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=((rat 1).den:ℝ)/(rat 0).den →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    ∃ xref : Fin 2 → ℝ, ∀ i,
      0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
      iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
      |xref i-x₀ i| ≤ L*N ∧
      |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_matrix_reference_roots_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) Q K₀ rat Mat e r (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hLpos hQ hscale hmesh hA hW hx₀ hden hdet hgamma hwindow hr

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_matrix_reference_roots_signed

example {e r v s l w x : ℝ}
    (hdet : v*r-e*s=1) (hl : 0 < r*l-e) (hw : 0 < r*w-e)
    (hx : x∈Icc l w) :
    (v-s*x)/(r*x-e)∈Icc ((v-s*w)/(r*w-e)) ((v-s*l)/(r*l-e)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_mem_interval_signed (e:=e) (r:=r) (v:=v) (s:=s) (l:=l) (w:=w) (x:=x) hdet hl hw hx

example
    {e r v s : ℤ} {a : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1)
    (hlw : l < w) (hl : 0 < (r:ℝ)*l-e) (hw : 0 < (r:ℝ)*w-e)
    (hnw : 0 < (v:ℝ)-s*w)
    (ha : (a:ℝ) ∈ Set.Icc l w)
    (hdyad : max ((r:ℝ)*l-e) ((r:ℝ)*w-e) ≤ 2*min ((r:ℝ)*l-e) ((r:ℝ)*w-e))
    (hcut : 256*(a.den:ℝ) ≤ Q) (hscale : 256 ≤ (w-l)*Q*a.den) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊Q*min ((r:ℝ)*l-e) ((r:ℝ)*w-e)⌋₊
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ (HuxleyLinearForm.fareySector K α β).card ∧
      ∀ p ∈ HuxleyLinearForm.fareySector K α β,
        0 < (r:ℝ)*p.1+s*p.2 ∧ (r:ℝ)*p.1+s*p.2 ≤ Q ∧
        ((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∈ Set.Icc l w :=
  TaoTrudgianYang2025.HuxleyRationalPhase.completeSector_density_from_curvature_signed (e:=e) (r:=r) (v:=v) (s:=s) (a:=a) (l:=l) (w:=w) (Q:=Q) hdet hlw hl hw hnw ha hdyad hcut hscale

example
    {σ δ T M N R : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 3 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    0 < (v:ℝ)-s*((rat 0:ℝ)+ε) →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ S.card ∧
    ∃ ξ : ℝ → Fin 2 → ℝ, ∀ p∈S,
      let a := e*p.1+v*p.2
      let d := r*p.1+s*p.2
      let x₁ := ξ ((p.1:ℝ)/p.2)
      let anew : Fin 2 → ℤ := ![a,Mat 0*a+Mat 1*d]
      let qnew : Fin 2 → ℤ := ![d,Mat 2*a+Mat 3*d]
      let z := fun i => (qnew i:ℝ)*deriv (f i) (round (x₁ i))
      (∀ i, x₁ i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (x₁ i)/2=(anew i:ℝ)/qnew i ∧
        |x₁ i-x₀ i| ≤ H ∧ 0 < (qnew i:ℝ) ∧ (qnew i:ℝ) ≤ Q) ∧
      |(z 0-z 1)-round (z 0-z 1)| ≤ Δ ∧
      (Δ < 1/2 →
        ∃ cnew∈minorArcCenterLabels (z 0) Δ,
          ∃ cnew₁∈minorArcCenterLabels (z 1) Δ,
          cnew=round (z 0) ∧ |(z 0-cnew)-(z 1-cnew₁)| ≤ Δ ∧
          ∃ p₀ p₁ : Fin 2, cnew=⌊z 0⌋+(p₀:ℕ) ∧ cnew₁=⌊z 1⌋+(p₁:ℕ)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_complete_sector_fourth_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    0 < (v:ℝ)-s*((rat 0:ℝ)+ε) →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    ∃ (ξ : ℝ → Fin 2 → ℝ) (cnew : ℤ × ℤ → Fin 2 → ℤ),
      let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
      let xp := fun p : ℤ × ℤ => ξ ((p.1:ℝ)/p.2)
      let zp := fun p i => qp p i*deriv (f i) (round (xp p i))
      let jp := fun (p : ℤ × ℤ) i => round ((rp i:ℝ)*dr i)*p.1+
        2*(round (xp p i)-ar i)*(ep i*p.1+vp i*p.2)
      (∀ p∈S, ∀ i, xp p i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xp p i)/2=((ep i:ℝ)*p.1+vp i*p.2)/qp p i ∧
        0 < qp p i ∧ qp p i ≤ Q) ∧
      (∀ p∈S, (∀ i, cnew p i∈minorArcCenterLabels (zp p i) Δ) ∧
        |(zp p 0-cnew p 0)-(zp p 1-cnew p 1)| ≤ Δ) ∧
      ∀ p∈S, ((cnew p 0-jp p 0)-(cnew p 1-jp p 1)=
        p.1*round (ac-deriv φ yseed)+p.2*round (bc-φ yseed+yseed*deriv φ yseed)) ∧
        |(ac-round (ac-deriv φ yseed))*((p.1:ℝ)/p.2)+
          (bc-round (bc-φ yseed+yseed*deriv φ yseed))-
          g ((p.1:ℝ)/p.2)+hq ((p.1:ℝ)/p.2)| ≤
          (Δ+quarticNonlinearResidualConstant σ δ*(qp p 0+qp p 1)/N)/(p.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_sector_linearization_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {σ δ T M N R L dmin : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → r ≠ 0 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    0 < (v:ℝ)-s*((rat 0:ℝ)+ε) →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    0 < L →
    modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2 →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    (H+L*N+1)^2 ≤ M*R →
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x₀ i| ≤ L*N ∧
        |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1) ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    ∀ k : Fin 17, α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    ∃ (ξ : ℝ → Fin 2 → ℝ) (cnew : ℤ × ℤ → Fin 2 → ℤ),
      let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
      let xp := fun p : ℤ × ℤ => ξ ((p.1:ℝ)/p.2)
      let zp := fun p i => qp p i*deriv (f i) (round (xp p i))
      let jp := fun (p : ℤ × ℤ) i => round ((rp i:ℝ)*dr i)*p.1+
        2*(round (xp p i)-ar i)*(ep i*p.1+vp i*p.2)
      (∀ p∈S, ∀ i, xp p i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xp p i)/2=((ep i:ℝ)*p.1+vp i*p.2)/qp p i ∧
        0 < qp p i ∧ qp p i ≤ Q) ∧
      (∀ p∈S, (∀ i, cnew p i∈minorArcCenterLabels (zp p i) Δ) ∧
        |(zp p 0-cnew p 0)-(zp p 1-cnew p 1)| ≤ Δ) ∧
      ∀ p∈S, ((cnew p 0-jp p 0)-(cnew p 1-jp p 1)=
        p.1*round (ac-deriv φ yseed)+p.2*round (bc-φ yseed+yseed*deriv φ yseed)) ∧
        |(ac-round (ac-deriv φ yseed))*((p.1:ℝ)/p.2)+
          (bc-round (bc-φ yseed+yseed*deriv φ yseed))-
          g ((p.1:ℝ)/p.2)+hq ((p.1:ℝ)/p.2)| ≤
          (Δ+quarticNonlinearResidualConstant σ δ*(qp p 0+qp p 1)/N)/(p.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_linearization_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (dmin:=dmin) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {e r v s : ℤ} {anchor seed : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1)
    (hl : 0 < (r:ℝ)*l-e) (hw : 0 < (r:ℝ)*w-e)
    (hnw : 0 < (v:ℝ)-s*w)
    (ha : (anchor:ℝ)∈Icc l w) (hseed : (seed:ℝ)∈Icc l w)
    (hdyad : max ((r:ℝ)*l-e) ((r:ℝ)*w-e) ≤ 2*min ((r:ℝ)*l-e) ((r:ℝ)*w-e))
    (hcut : 256*(anchor.den:ℝ) ≤ Q/3) (hseedQ : (seed.den:ℝ) ≤ Q) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊(Q/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w-e)⌋₊
    let p : ℤ × ℤ := (v*seed.den-s*seed.num,r*seed.num-e*seed.den)
    0 < (p.2:ℝ) ∧ (p.1:ℝ)/p.2∈Icc α β ∧
      0 ≤ (p.1:ℝ) ∧ (p.1:ℝ) ≤ 12*(β*(K:ℝ)) ∧
      (p.2:ℝ) ≤ 12*(K:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_original_seed_enlarged_rectangle_signed (e:=e) (r:=r) (v:=v) (s:=s) (anchor:=anchor) (seed:=seed) (l:=l) (w:=w) (Q:=Q) hdet hl hw hnw ha hseed hdyad hcut hseedQ

example
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    0 < (v:ℝ)-s*((rat 0:ℝ)+ε) →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤ D/(pseed.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_residual_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

example
    {σ δ T M N R L dmin : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → r ≠ 0 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    0 < (v:ℝ)-s*((rat 0:ℝ)+ε) →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    0 < L →
    modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2 →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    (H+L*N+1)^2 ≤ M*R →
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x₀ i| ≤ L*N ∧
        |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1) ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    ∀ k : Fin 17, α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤ D/(pseed.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_seed_residual_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (dmin:=dmin) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_mem_interval_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.completeSector_density_from_curvature_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_complete_sector_fourth_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_sector_linearization_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_linearization_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_original_seed_enlarged_rectangle_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_residual_signed
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_seed_residual_signed

/-- The source-normalized residual at the original seed for either
reference orientation, reusing the actual signed seed residual and the
same cubic scale conversion with its absolute denominator. -/
theorem physicalModelPhase_actual_fourier_original_seed_source_residual_signed
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    0 < (v:ℝ)-s*((rat 0:ℝ)+ε) →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ ep rp sp pseed yseed ar μr νr dr δr θr βr ac bc g hq φ
    Ctay D η U Z hMone hRone hRM hNscale hdmin hβ hΔ hrp hxref href hbudget
    hd hleft hright hlarge
  have hraw := physicalModelPhase_actual_fourier_original_seed_residual_signed
    Q K₀ rat vinv parity Mat anchor e r v s
    hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv
    hlevel hcolor hnear hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    hMone hRone hRM hNscale hdmin hβ hΔ hrp hxref href hbudget hd hleft hright hlarge
  let Kres := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,C]; positivity
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hseedI : (rat 0:ℝ)∈Icc l w' :=
    ⟨by dsimp only [l]; linarith only [hε],
      by dsimp only [w']; linarith only [hε]⟩
  have hrect := inverseFarey_original_seed_enlarged_rectangle_signed
    hchart hdl hdw hnum ha hseedI hdyad hcut
    (show ((rat 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden 0).1)
  have ht : (0:ℝ) < pseed.2 := hrect.1
  have hyseed : yseed∈Icc α β := hrect.2.1
  let d := (rp 0:ℝ)*yseed+sp 0
  have hdpos : 0 < d := hdmin.trans_le (hd yseed hyseed 0)
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hqp : (rp 0:ℝ)*pseed.1+sp 0*pseed.2=(q 0:ℝ) := by
    change (r:ℝ)*pseed.1+s*pseed.2=(q 0:ℝ)
    dsimp only [pseed]
    push_cast
    linear_combination (q 0:ℝ)*hchartR
  have hdq : d*(pseed.2:ℝ)=(q 0:ℝ) := by
    calc
      _ = (rp 0:ℝ)*pseed.1+sp 0*pseed.2 := by
        dsimp only [d,yseed]; field_simp
      _ = _ := hqp
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCn : 0 ≤ quarticNonlinearResidualConstant σ δ := by
    dsimp only [quarticNonlinearResidualConstant]; positivity
  have hKres : 0 ≤ Kres := by dsimp only [Kres,Cc,Ct,C₂,C₃]; positivity
  have hD : D=Kres*(Q:ℝ)/N := by dsimp only [D,Δ,Kres]; ring
  have hQq : (Q:ℝ) ≤ 2*(q 0:ℝ) := by exact_mod_cast (hden 0).2
  have hres : D/(pseed.2:ℝ) ≤ 2*Kres*d/N := by
    rw [hD]
    calc
      _ ≤ (Kres*(2*(q 0:ℝ))/N)/(pseed.2:ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQq hKres) hN.le) ht.le
      _ = _ := by rw [← hdq]; field_simp
  have hF₂ := approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl
  have hround := physicalModelPhase_halfCurvature_round_error hσ.le hF₂
    hT hM (hA 0) (hW 0) (hxref 0)
  have hμbounds := physicalModelPhase_cubicCoefficient_bounds hσ hδ hF₂
    hT hM (hA 0) (hW 0) hround.1
  have hμpos : 0 < μr 0 := lt_of_lt_of_le (by positivity) hμbounds.1
  have hphaseLower : κ/(2*N) ≤ 3*μr 0*R^2 := by
    have hh := mul_le_mul_of_nonneg_right hμbounds.1 (show 0 ≤ 3*R^2 by positivity)
    have he : (κ*T/(6*M^3))*(3*R^2)=κ/(2*N) := by
      have hTeq : T=M^3/(N*R^2) :=
        (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
      rw [hTeq]
      field_simp
      norm_num
    rw [he] at hh
    change κ/(2*N) ≤ μr 0*(3*R^2) at hh
    nlinarith only [hh]
  have hfinal : 2*Kres*d/N ≤ (4*Kres/κ)*R^2/
      |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| := by
    rw [scaled_minorArcCoordinate_abs hμpos.ne'
      (by exact_mod_cast hrp 0) hdpos.ne',abs_of_pos hμpos,abs_of_pos hdpos,
      one_div,div_inv_eq_mul]
    have hh := mul_le_mul_of_nonneg_left hphaseLower
      (show 0 ≤ (4*Kres/κ)*d by positivity)
    convert hh using 1 <;> field_simp
    ring
  exact hraw.trans (hres.trans hfinal)


#print axioms physicalModelPhase_actual_fourier_original_seed_source_residual_signed

/-- The actual Fourier data yield both measured quartic curvature and
the source-normalized residual at the same original seed, for either
reference orientation and without assuming either analytic conclusion. -/
theorem physicalModelPhase_actual_fourier_original_seed_source_bounds_signed
    {σ δ T M N R dmin : ℝ} {k : Fin 17} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ xref : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    0 < (v:ℝ)-s*((rat 0:ℝ)+ε) →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ ep rp sp pseed yseed ar μr νr dr δr θr βr ac bc g hq φ
    Ctay D η U Z hMone hRone hRM hNscale hdmin hβ hΔ hrp hxref href hbudget
    hd hleft hright hlarge
  have hresult := physicalModelPhase_actual_fourier_original_seed_source_residual_signed
    Q K₀ rat vinv parity Mat anchor e r v s
    hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv
    hlevel hcolor hnear hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    hMone hRone hRM hNscale hdmin hβ hΔ hrp hxref href hbudget hd hleft hright hlarge
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,C]; positivity
  have ha : (anchor:ℝ)∈Icc l w' := by
    have hh := abs_le.mp hanchor
    exact ⟨by dsimp only [l]; linarith only [hh.1],
      by dsimp only [w']; linarith only [hh.2]⟩
  have hseedI : (rat 0:ℝ)∈Icc l w' :=
    ⟨by dsimp only [l]; linarith only [hε],
      by dsimp only [w']; linarith only [hε]⟩
  have hrect := inverseFarey_original_seed_enlarged_rectangle_signed
    hchart hdl hdw hnum ha hseedI hdyad hcut
    (show ((rat 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden 0).1)
  have ht : (0:ℝ) < pseed.2 := hrect.1
  have hyseed : yseed∈Icc α β := hrect.2.1
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  refine ⟨?_,hresult⟩
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  let qp := fun (p : ℤ × ℤ) i => (rp i:ℝ)*p.1+sp i*p.2
  let ap := fun (p : ℤ × ℤ) i => (ep i:ℝ)*p.1+vp i*p.2
  have hH : 0 < H := by dsimp only [H,C]; positivity
  have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
  have hqpos i : (0:ℝ) < q i := by exact_mod_cast (rat i).pos
  have hrat i : (rat i:ℝ)=((rat i).num:ℝ)/(q i:ℝ) := Rat.cast_def _
  have hdenR : (Mat 2:ℝ)*(rat 0).num+Mat 3*q 0=q 1 := by
    calc
      _ = ((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)*q 0 := by
        rw [hrat]; field_simp [(hqpos 0).ne']
      _ = q 1 := by rw [hMatt]; field_simp [(hqpos 0).ne']
  have hnumR : (Mat 0:ℝ)*(rat 0).num+Mat 1*q 0=(rat 1).num := by
    have hm := hMatmap
    rw [hMatt,hrat 0,hrat 1] at hm
    have hh := (div_eq_iff (div_ne_zero (hqpos 1).ne' (hqpos 0).ne')).mp hm
    field_simp [(hqpos 0).ne',(hqpos 1).ne'] at hh
    nlinarith only [hh]
  have hseedq (i) : qp pseed i=(q i:ℝ) := by
    fin_cases i
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination (q 0:ℝ)*hchartR
    · dsimp only [qp,pseed,rp,sp]; push_cast
      linear_combination ((Mat 2:ℝ)*(rat 0).num+Mat 3*q 0)*hchartR+hdenR
  have hseeda (i) : ap pseed i=((rat i).num:ℝ) := by
    fin_cases i
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((rat 0).num:ℝ)*hchartR
    · dsimp only [ap,pseed,ep,vp]; push_cast
      linear_combination ((Mat 0:ℝ)*(rat 0).num+Mat 1*q 0)*hchartR+hnumR
  have hseedroot (i) : iteratedDeriv 2 (f i) (x₀ i)/2=ap pseed i/qp pseed i := by
    rw [hseedq,hseeda,hlevel,hrat]
  have hdetp (i) : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hseedSq i : |(round (x₀ i):ℝ)-(ar i:ℝ)|^2 ≤ M*R := by
    have hh := rounded_displacement_bound (x₀ i) (xref i)
    have hb : |(round (x₀ i):ℝ)-(ar i:ℝ)| ≤ H+|x₀ i-xref i|+1 := by
      dsimp only [ar]
      linarith only [hh,hH]
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 2).trans (hbudget i)
  obtain ⟨_v,_hv,hthird,_hsecond,_hfirst,_hfourth⟩ := physicalModelPhase_actual_fourier_conditions
    Q K₀ rat vinv parity hσ hδ hF₃ hT hM hN hR hQ hscale hmesh
    hA hW hx₀ hden hinv hlevel hcolor hnear
  have hthird' : |mu 1*(qp pseed 1)^3/(mu 0*(qp pseed 0)^3)-1| ≤ B*R^2/N^2 := by
    simpa only [hseedq] using hthird
  exact physicalModelPhase_quartic_curvature_source_scale
    (u:=(pseed.1:ℝ)) (t:=(pseed.2:ℝ)) (x₀:=xref) (x₁:=x₀)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    hσ hδ hF hT hM hN hRone hNscale hscale hB hdmin hA hW hxref hx₀
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast hrp i) ht
    (fun i => by change 0 < qp pseed i; rw [hseedq]; exact hqpos i)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i) href hseedroot hseedSq
    (hd yseed hyseed) hthird'


#print axioms physicalModelPhase_actual_fourier_original_seed_source_bounds_signed

/-- Construct paired physical reference roots from the actual Fourier
matrix and derive both source bounds for the signed original seed. -/
theorem physicalModelPhase_actual_fourier_constructed_reference_source_bounds_signed
    {σ δ T M N R L dmin : ℝ} (Q K₀ : ℕ) [NeZero K₀]
    (rat : Fin 2 → ℚ) (vinv : Fin 2 → ℤ) (parity : Fin 2 → Fin 2) (Mat : Fin 4 → ℤ) (anchor : ℚ) (e r v s : ℤ)
    {F : Fin 2 → ℝ → ℝ} {A W x₀ : Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx₀ : ∀ i, x₀ i∈Ioo (1/2:ℝ) (W i-1/2))
    (hden : ∀ i, (rat i).den ≤ Q ∧ Q ≤ 2*(rat i).den)
    (hinv : ∀ i, ((rat i).den:ℤ) ∣ (rat i).num*vinv i-1) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ i, iteratedDeriv 2 (f i) (x₀ i)/2=(rat i:ℝ)) →
    let q := fun i => (rat i).den
    let mu := fun i => iteratedDeriv 3 (f i) (round (x₀ i))/6
    let ell := fun i => deriv (f i) (round (x₀ i))
    let b := fun i => (⌊(q i:ℝ)*ell i⌋+(parity i:ℕ) : ℤ)
    let cround := fun i => round ((q i:ℝ)*ell i)
    let tau := fun i => ((b i:ℝ)-(q i:ℝ)*ell i)/2
    let dual := fun i => -2*mu i*(Real.sqrt (2/(3*mu i*(q i:ℝ))))^3
    let w := fun i => (![Int.fract (-(vinv i:ℝ)*b i/q i),
      Int.fract (-(vinv i:ℝ)/q i),dual i/Real.sqrt K₀,
      (3*dual i*tau i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    b 0-cround 0=b 1-cround 1 →
    (∀ d, |w 0 d-w 1 d| ≤ 2*radius d) →
    let c := modelPhaseThirdLower σ/6
    let J := (σ*(σ+1)+1)/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (Mat 2:ℝ)*(rat 0:ℝ)+Mat 3=(q 1:ℝ)/q 0 →
    ((Mat 0:ℝ)*(rat 0:ℝ)+Mat 1)/((Mat 2:ℝ)*(rat 0:ℝ)+Mat 3)=(rat 1:ℝ) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let C := σ*(σ+1)+1
    let H := N/(C+2)
    let ε := modelPhaseThirdLower σ/(16*(C+2)*R^2)
    2 ≤ N →
    (∀ i, x₀ i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    v*r-e*s=1 → r ≠ 0 →
    0 < (r:ℝ)*((rat 0:ℝ)-ε)-e →
    0 < (r:ℝ)*((rat 0:ℝ)+ε)-e →
    0 < (v:ℝ)-s*((rat 0:ℝ)+ε) →
    max ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat 0:ℝ)-ε)-e) ((r:ℝ)*((rat 0:ℝ)+ε)-e) →
    |(anchor:ℝ)-(rat 0:ℝ)| ≤ ε →
    256*(anchor.den:ℝ) ≤ (Q:ℝ)/3 →
    256 ≤ (2*ε)*((Q:ℝ)/3)*anchor.den →
    let l := (rat 0:ℝ)-ε
    let w' := (rat 0:ℝ)+ε
    let α := ((v:ℝ)-s*w')/((r:ℝ)*w'-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊((Q:ℝ)/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w'-e)⌋₊
    let S := HuxleyLinearForm.fareySector K α β
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let κ := modelPhaseThirdLower σ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    let pseed : ℤ × ℤ := (v*(q 0:ℤ)-s*(rat 0).num,r*(rat 0).num-e*(q 0:ℤ))
    let yseed := (pseed.1:ℝ)/pseed.2
    0 < L →
    modelPhaseThirdLower σ*L*R^2 ≤ 24*N^2 →
    (∀ i, x₀ i-L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, x₀ i+L*N∈Ioo (1/2:ℝ) (W i-1/2)) →
    |(e:ℝ)/r-(rat 0:ℝ)| ≤ modelPhaseThirdLower σ*L/(16*R^2) →
    (H+L*N+1)^2 ≤ M*R →
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x₀ i| ≤ L*N ∧
        |(round (xref i):ℝ)-(round (x₀ i):ℝ)| ≤ L*N+1) ∧
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let dr := fun i => deriv (f i) (ar i)
    let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
    let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
    let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
    let ac := θr 0-θr 1
    let bc := βr 0-βr 1
    let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
    let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
    let φ := fun y => g y-hq y
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := D+(K:ℝ)*Ctay*(β-α)^2
    let U := (4/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*dmin^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    1 ≤ M → 1 ≤ R → R ≤ M → N^2 ≤ M*R → 0 < dmin →
    1 ≤ β → Δ < 1/2 →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    ∀ k : Fin 17, α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| := by
  classical
  intro f hlevel q mu ell b cround tau dual w radius hcolor hnear c J B
    hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    C H ε hNtwo hL hU hchart hr hdl hdw hnum hdyad hanchor hcut hcount
    l w' α β K S C₂ C₃ κ Ct Cc Δ ep rp sp pseed yseed
    hLpos hwindow hwideL hwideU hreference hbudget
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  obtain ⟨xref,hxref⟩ := physicalModelPhase_actual_matrix_reference_roots_signed
    Q K₀ rat Mat e r hσ hδ hF₂ hT hM hN hR hLpos hQ hscale hmesh
    hA hW hx₀ hden hMatdet hMatgamma hwindow hr hlevel hMatt hMatmap
    hwideL hwideU hreference
  refine ⟨xref,hxref,?_⟩
  intro ar μr νr dr δr θr βr ac bc g hq φ Ctay D η U Z
    hMone hRone hRM hNscale hdmin hβ hΔ hd k hleft hright hlarge
  have hH : 0 < H := by dsimp only [H,C]; positivity
  have hfarbudget i : (H+|x₀ i-xref i|+1)^2 ≤ M*R := by
    have hdist : |x₀ i-xref i| ≤ L*N := by
      simpa only [abs_sub_comm] using (hxref i).2.2.2.1
    apply (pow_le_pow_left₀ (by positivity : 0 ≤ H+|x₀ i-xref i|+1)
      (show H+|x₀ i-xref i|+1 ≤ H+L*N+1 by linarith only [hdist]) 2).trans hbudget
  exact physicalModelPhase_actual_fourier_original_seed_source_bounds_signed
    Q K₀ rat vinv parity Mat anchor e r v s
    hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv
    hlevel hcolor hnear hsmall hNR hRN hcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hchart hdl hdw hnum hdyad hanchor hcut hcount
    hMone hRone hRM hNscale hdmin hβ hΔ (fun i => (mul_ne_zero_iff.mp (hxref i).1.ne').1)
    (fun i => (hxref i).2.1) (fun i => (hxref i).2.2.1) hfarbudget
    hd hleft hright hlarge


#print axioms physicalModelPhase_actual_fourier_constructed_reference_source_bounds_signed

/-- Absolute-value source cutoff for either reference orientation.
The dyadic affine-denominator range and coordinate height are explicit
geometric inputs; both coefficient budgets follow with the same 5*C*J
constant, without a positive-reference-denominator assumption. -/
theorem quartic_coefficient_budgets_of_source_coordinate_cutoff_signed
    {C J μ N R r s d l w Bcut : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hw : 1 ≤ w)
    (hdlo : d ≤ min (r*l+s) (r*w+s)) (hdhi : max (r*l+s) (r*w+s) ≤ 2*d)
    (hcoord : |r| *w ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l) ≤ 1/2 ∧
      U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 := by
  intro U
  let dl := r*l+s
  let r₀ := |r|
  have hr₀ : 0 < r₀ := abs_pos.mpr hr
  have hdl : 0 < dl := hd.trans_le (hdlo.trans (min_le_left _ _))
  have hdlhi : dl ≤ 2*d := (le_max_left _ _).trans hdhi
  have hdwlo : d ≤ r*w+s := hdlo.trans (min_le_right _ _)
  have hdwhi : r*w+s ≤ 2*d := (le_max_right _ _).trans hdhi
  have hG' : 1/(3*μ*r₀*dl) ≤ r₀*N^2/(Bcut*R^2) := by
    change |1/(3*μ*r*dl)| ≤ r₀*N^2/(Bcut*R^2) at hG
    simpa only [abs_div,abs_one,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3),
      abs_of_pos hμ,abs_of_pos hdl] using hG
  have hμmul : 6*μ*N*R^2 ≤ J := by
    have hh := (le_div_iff₀ (show 0 < 6*N*R^2 by positivity)).mp hμupper
    nlinarith only [hh]
  have hGclear : Bcut*R^2 ≤ (r₀*N^2)*(3*μ*r₀*dl) := by
    have hh := (div_le_div_iff₀
      (show 0 < 3*μ*r₀*dl by positivity)
      (show 0 < Bcut*R^2 by positivity)).mp hG'
    simpa only [one_mul] using hh
  have hGfour : Bcut*R^4 ≤ (3*μ*N*R^2)*(r₀^2*dl*N) := by
    have hh := mul_le_mul_of_nonneg_right hGclear (sq_nonneg R)
    nlinarith only [hh]
  have hμhalf : 3*μ*N*R^2 ≤ J/2 := by nlinarith only [hμmul]
  have hupper : Bcut*R^4 ≤ J*r₀^2*d*N := by
    have hh := mul_le_mul_of_nonneg_right hμhalf
      (show 0 ≤ r₀^2*dl*N by positivity)
    have hh' := mul_le_mul_of_nonneg_left hdlhi
      (show 0 ≤ J*r₀^2*N/2 by positivity)
    nlinarith only [hGfour,hh,hh']
  have hsmall : 5*C*R^4 ≤ N*r₀^2*d := by
    have hh := mul_le_mul_of_nonneg_right hBsize (pow_nonneg hR.le 4)
    have he : J*(5*C*R^4) ≤ J*(N*r₀^2*d) := by nlinarith only [hh,hupper]
    exact (mul_le_mul_iff_right₀ hJ).mp he
  have hdiff : w-l ≤ d/r₀ := by
    apply (le_div_iff₀ hr₀).mpr
    have hdllo : d ≤ r*l+s := hdlo.trans (min_le_left _ _)
    rcases le_total 0 r with hsign | hsign
    · dsimp only [r₀]
      rw [abs_of_nonneg hsign]
      nlinarith only [hdllo,hdwhi]
    · dsimp only [r₀]
      rw [abs_of_nonpos hsign]
      change r*l+s ≤ 2*d at hdlhi
      nlinarith only [hdwlo,hdlhi]
  have hwbound : w ≤ 2*d/r₀ := by
    apply (le_div_iff₀ hr₀).mpr
    nlinarith only [hcoord]
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hmax : max |l| |w|=w := by
    rw [abs_of_nonneg hl,abs_of_nonneg (zero_le_one.trans hw),max_eq_right hlw]
  have hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 := by
    rw [hmax]
    calc
      _ ≤ U*(d/r₀)*(2*d/r₀+(d/r₀)/2) := by gcongr
      _ = 5*C*R^4/(2*N*r₀^2*d) := by dsimp only [U]; field_simp; ring
      _ ≤ _ := by
        apply (div_le_iff₀ (show 0 < 2*N*r₀^2*d by positivity)).mpr
        nlinarith only [hsmall]
  refine ⟨?_,hheight⟩
  have hfactor : 1 ≤ max |l| |w|+(w-l)/2 := by
    rw [hmax]
    linarith only [hw,hlw]
  exact (le_mul_of_one_le_right (mul_nonneg hU (sub_nonneg.mpr hlw)) hfactor).trans hheight

#print axioms quartic_coefficient_budgets_of_source_coordinate_cutoff_signed

/-- The occupied-window pure L^-3 determinant bound
for either reference orientation. The absolute source cutoff and explicit
coordinate height discharge the same coefficient budgets; all physical
sample and interval-root arguments are unchanged. -/
theorem physicalModelPhase_occupied_window_quartic_determinant_signed
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ) (hS : 288 ≤ S.card)
    {σ δ T M N R base d K nSpan Ccurv Bcut l w y₀ ac bc : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hK : 0 ≤ K) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| *w ≤ 2*d) (hl : 0 ≤ l) (hw : 1 ≤ w)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : 5*Ccurv*(σ*(σ+1)+1) ≤ Bcut) :
    let U := Ccurv*R^4/(N*d^3)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let μ := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
    let y := fun j => ((p j).1:ℝ)/(p j).2
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(144*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      K*R^2/|r 0*G (y j)|) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    |r 0*s 1-s 0*r 1| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2) := by
  classical
  intro U f μ ν y g h φ G Z κ Γ L hGcut hbase hpoint hy₀ hy hcurv hres C
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hcount : (0:ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hCpos : 0 < σ*(σ+1)+1 := by positivity
  have hL : 0 < L := mul_pos (div_pos hκ (mul_pos (by norm_num) hCpos)) hcount
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hround i := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hxref i)
  have hμbounds i := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i)
    hT hM (hA i) (hW i) (hround i).1
  have hμpos i : 0 < μ i := lt_of_lt_of_le (by positivity) (hμbounds i).1
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hμupper : μ 0 ≤ (σ*(σ+1)+1)/(6*N*R^2) := by
    have hb := (hμbounds 0).2
    have hTeq : T=M^3/(N*R^2) :=
      (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
    have he : (σ*(σ+1)+1)*T/(6*M^3)=(σ*(σ+1)+1)/(6*N*R^2) := by
      rw [hTeq]
      field_simp
    exact hb.trans_eq he
  have hlw : l ≤ w := hy₀.1.1.trans hy₀.1.2
  obtain ⟨hwidth,hheight⟩ := quartic_coefficient_budgets_of_source_coordinate_cutoff_signed
    hCcurv hCpos (hμpos 0) hN hRpos (hr 0) hd hl hlw hw
    (le_min (hden l ⟨le_rfl,hlw⟩ 0).1 (hden w ⟨hlw,le_rfl⟩ 0).1)
    (max_le (hden l ⟨le_rfl,hlw⟩ 0).2 (hden w ⟨hlw,le_rfl⟩ 0).2)
    hcoord hμupper hBcut hBsize hGcut
  have hdx (j) (hj : j∈S) : x j 0∈Ioo 0 (W 0) :=
    ⟨by linarith [(hx j hj 0).1],by linarith [(hx j hj 0).2]⟩
  obtain ⟨a,b,j,_hj,hcoeff,hanti,hphys,hG⟩ := physicalModelPhase_common_coefficient_samples
    (ac:=ac) (bc:=bc)
    S p (fun n => x n 0) hS hσ hδ (hF₂ 0) hT hM (hA 0) (hW 0) hN
    (hμpos 0) (hμpos 1).ne' (hr 0) (hr 1) (hdet 0)
    (fun z hz => hd.trans_le (hden z hz 0).1)
    (fun z hz => (hd.trans_le (hden z hz 1).1).ne') hwidth hheight hpt hdx hwindow
    (fun n hn => hpoint n hn 0) hy₀ hy hcurv
  have hH i : 0 ≤ H i := (abs_nonneg _).trans (hdisplacement _ (hcoeff 0).1 i)
  have hn : 0 < nSpan := by linarith only [hH 0,hspan 0]
  have hnsquare : nSpan^2 ≤ M*R := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg nSpan) (mul_nonneg hM.le hRpos.le)
      (by norm_num : (3:ℕ) ≠ 0)).mp
    have hh := pow_le_pow_left₀ (pow_nonneg hn.le 3) hsourcecube 2
    have hh' := mul_le_mul_of_nonneg_left hRM (show 0 ≤ M^2*R^3 by positivity)
    nlinarith only [hh,hh']
  have hsquare i : (H i+1)^2 ≤ M*R := by
    apply (pow_le_pow_left₀ (add_nonneg (hH i) zero_le_one)
      (show H i+1 ≤ nSpan by linarith only [hH i,hspan i]) 2).trans hnsquare
  have hκle : κ ≤ σ*(σ+1)+1 := by
    have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ (hF₂ 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2)
    exact hh.1.trans hh.2
  have hLspan : L*N ≤ nSpan := by
    have hrati : κ/(σ*(σ+1)+1) ≤ 1 := (div_le_one hCpos).mpr hκle
    have hsmall := mul_le_mul_of_nonneg_right hrati
      (div_pos (mul_pos hN hcount) (by norm_num : (0:ℝ)<144)).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/144) := by
      dsimp only [L]
      field_simp
    rw [← he,one_mul] at hsmall
    have hg := hphys (0:Fin 7)
    have hdiff := le_abs_self (x (j (1:Fin 8)) 0-x (j (0:Fin 8)) 0)
    have htri := abs_sub_le (x (j (1:Fin 8)) 0) (xref 0) (x (j (0:Fin 8)) 0)
    rw [abs_sub_comm (xref 0)] at htri
    have hleft := hdisplacement _ (hcoeff (0:Fin 8)).1 0
    have hright := hdisplacement _ (hcoeff (1:Fin 8)).1 0
    change N*(S.card:ℝ)/144 ≤ x (j 1) 0-x (j 0) 0 at hg
    linarith only [hsmall,hg,hdiff,htri,hleft,hright,hspan 0]
  have hNL : (L*N)^2 ≤ M*R :=
    (pow_le_pow_left₀ (mul_pos hL hN).le hLspan 2).trans hnsquare
  let Kw := nSpan/(L*N)
  have hKw : 0 ≤ Kw := (div_pos hn (mul_pos hL hN)).le
  have hKwscale : Kw*L*N=nSpan := by dsimp only [Kw]; field_simp
  have hdiam i : 2*H i+1 ≤ Kw*L*N := by rw [hKwscale]; exact hspan i
  have hcube : Kw*L^3*N^3 ≤ M*R^2 := by
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_pos hL hN).le hLspan 2) hn.le
    calc
      _ = nSpan*(L*N)^2 := by dsimp only [Kw]; field_simp
      _ ≤ nSpan*nSpan^2 := hh
      _ = nSpan^3 := by ring
      _ ≤ _ := hsourcecube
  let z : Fin 8 → ℝ := fun i => y (j i.rev)
  have hmono : StrictMono z := hanti.comp Fin.rev_strictAnti
  have hz (i : Fin 8) : z i∈Icc l w := (hy _ (hcoeff i.rev).1).1
  have hsub : Icc (z 0) (z 7) ⊆ Icc l w :=
    fun q hq => ⟨(hz 0).1.trans hq.1,hq.2.trans (hz 7).2⟩
  have hcoef : κ/(σ*(σ+1)+1) ≤ κ*T/(6*μ 0*M^3) := by
    have hb : 6*μ 0*M^3 ≤ (σ*(σ+1)+1)*T := by
      have hh := (le_div_iff₀ (show 0 < 6*M^3 by positivity)).mp (hμbounds 0).2
      change μ 0*(6*M^3) ≤ (σ*(σ+1)+1)*T at hh
      nlinarith only [hh]
    apply (div_le_div_iff₀ hCpos
      (mul_pos (mul_pos (by norm_num) (hμpos 0)) (pow_pos hM 3))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hb hκ.le]
  have hgap (i : Fin 7) : L*N ≤ |G (z i.succ)-G (z i.castSucc)| := by
    have hh := mul_le_mul_of_nonneg_right hcoef
      (div_pos (mul_pos hN hcount) (by norm_num : (0:ℝ) < 144)).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/144) := by
      dsimp only [L]
      field_simp
    rw [he]
    dsimp only [z]
    rw [Fin.rev_succ,Fin.rev_castSucc,abs_sub_comm]
    exact (hh.trans (hG i.rev)).trans (le_abs_self _)
  have hroot (i : Fin 8) (a : Fin 2) :
      iteratedDeriv 2 (f a) (x (j i.rev) a)/2=(e a*z i+v a)/(r a*z i+s a) := by
    rw [hpoint _ (hcoeff i.rev).1 a]
    have ht : ((p (j i.rev)).2:ℝ) ≠ 0 := by
      exact_mod_cast (hpt _ (hcoeff i.rev).1).ne'
    dsimp only [z,y]
    have hn : e a*(((p (j i.rev)).1:ℝ)/(p (j i.rev)).2)+v a=
      (e a*(p (j i.rev)).1+v a*(p (j i.rev)).2)/(p (j i.rev)).2 := by field_simp
    have hd' : r a*(((p (j i.rev)).1:ℝ)/(p (j i.rev)).2)+s a=
      (r a*(p (j i.rev)).1+s a*(p (j i.rev)).2)/(p (j i.rev)).2 := by field_simp
    rw [hn,hd',div_div_div_cancel_right₀ ht]
  have hex (i : Fin 2) := physicalModelPhase_interval_root_family
    (l:=z 0) (w:=z 7) (x₀:=xref i) hσ.le (hF₂ i) hT hM (hA i) (hW i)
    (hx _ (hcoeff (0:Fin 8).rev).1 i) (hx _ (hcoeff (7:Fin 8).rev).1 i)
    (hd.trans_le (hden _ (hz 0) i).1) (hd.trans_le (hden _ (hz 7) i).1)
    (hdisplacement _ (hcoeff (0:Fin 8).rev).1 i)
    (hdisplacement _ (hcoeff (7:Fin 8).rev).1 i)
    (by rw [← hroot 0 i]; exact Set.left_mem_uIcc)
    (by rw [← hroot 7 i]; exact Set.right_mem_uIcc)
  choose ρ hρ hρdiam using hex
  have hdiam' i : |x (j (7:Fin 8).rev) i-x (j (0:Fin 8).rev) i|+1 ≤ Kw*L*N := by
    have hh := abs_sub_le (x (j (7:Fin 8).rev) i) (xref i) (x (j (0:Fin 8).rev) i)
    rw [abs_sub_comm (xref i)] at hh
    linarith only [hh,hdisplacement _ (hcoeff (7:Fin 8).rev).1 i,
      hdisplacement _ (hcoeff (0:Fin 8).rev).1 i,hdiam i]
  have hbound := physicalModelPhase_quartic_long_block_determinant
    (x₁:=fun q i => ρ i q) (α:=ac-a) (β:=bc-b) z
    hσ hδ hF hT hM hN hR hL hNL hd hK hKw hscale hA hW hxref
    (fun q hq i => (hρ i q hq).2.1) hr hdet
    (fun q hq i => (hden q (hsub hq) i).1)
    (fun q hq i => (hden q (hsub hq) i).2) hmono
    (fun q hq t ht i => (hρdiam i q hq t ht).trans (hdiam' i)) hbase
    (fun q hq i => (hρ i q hq).2.2.1)
    (fun q hq i => (pow_le_pow_left₀ (abs_nonneg _)
      (hρ i q hq).2.2.2.2 2).trans (hsquare i))
    hgap (fun i => by
      have hh := hres _ (hcoeff i.rev).1
      rw [(hcoeff i.rev).2.1,(hcoeff i.rev).2.2] at hh
      exact hh)

  have hΓ : 0 < Γ := div_pos hCpos hκ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (heathBrownPhysicalPoint_mem_interior hM (hA 0) (hW 0) (hround 0).1) 4 le_rfl)
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have habsorb : Kw*N*R^2/M ≤ R^4/(L^3*N^2) := by
    apply (div_le_div_iff₀ hM (show 0 < L^3*N^2 by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hcube (sq_nonneg R)
    nlinarith only [hh]
  have hvar := mul_le_mul_of_nonneg_left habsorb
    (show 0 ≤ 2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ by positivity)
  have htotal := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl ((1+Γ^2)*C*R^4/(L^3*N^2))) hvar)
    (show 0 ≤ 64*Γ/(3*κ) by positivity)
  apply hbound.trans
  calc
    _ = (64*Γ/(3*κ))*((1+Γ^2)*C*R^4/(L^3*N^2)+
        (2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*(Kw*N*R^2/M)) := by ring
    _ ≤ _ := htotal
    _ = _ := by ring

#print axioms physicalModelPhase_occupied_window_quartic_determinant_signed

/-- The occupied-window improved L^-2 Third Condition on an actual occupied subfamily
for either reference orientation. The absolute source cutoff and explicit
coordinate height discharge the same coefficient budgets; all physical
sample and interval-root arguments are unchanged. -/
theorem physicalModelPhase_occupied_window_quartic_third_mass_signed
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ) (hS : 288 ≤ S.card)
    {σ δ T M N R base d K nSpan Ccurv Bcut l w y₀ ac bc : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hK : 0 ≤ K) (hRM : R ≤ M)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| *w ≤ 2*d) (hl : 0 ≤ l) (hw : 1 ≤ w)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : 5*Ccurv*(σ*(σ+1)+1) ≤ Bcut) :
    let U := Ccurv*R^4/(N*d^3)
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    let μ := fun i => iteratedDeriv 3 (f i) (round (xref i))/6
    let ν := fun i => iteratedDeriv 4 (f i) (round (xref i))/24
    let y := fun j => ((p j).1:ℝ)/(p j).2
    let g := rationalPhase (μ 0) (r 0) (s 0) (μ 1) (r 1) (s 1)
    let h := quarticPhase (μ 0) (ν 0) (r 0) (s 0) (μ 1) (ν 1) (r 1) (s 1)
    let φ := fun z => g z-h z
    let G := minorArcCoordinate (μ 0) (r 0) (s 0)
    let Z := quarticCurvatureBoundaryRoots (μ 0) (ν 0) (r 0) (s 0)
      (μ 1) (ν 1) (r 1) (s 1) U
    let κ := modelPhaseThirdLower σ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(144*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      K*R^2/|r 0*G (y j)|) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    ∃ E : Finset ℕ, E ⊆ S ∧ (S.card:ℝ)/144 ≤ (E.card:ℝ) ∧
      ∀ j∈E,
        |(iteratedDeriv 3 (f 1) (round (x j 1))/6)*(r 1*y j+s 1)^3/
          ((iteratedDeriv 3 (f 0) (round (x j 0))/6)*(r 0*y j+s 0)^3)-1| ≤
          (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) := by
  classical
  intro U f μ ν y g h φ G Z κ Γ L hGcut hbase hpoint hy₀ hy hcurv hres C
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hcount : (0:ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hCpos : 0 < σ*(σ+1)+1 := by positivity
  have hL : 0 < L := mul_pos (div_pos hκ (mul_pos (by norm_num) hCpos)) hcount
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  have hround i := physicalModelPhase_halfCurvature_round_error hσ.le (hF₂ i)
    hT hM (hA i) (hW i) (hxref i)
  have hμbounds i := physicalModelPhase_cubicCoefficient_bounds hσ hδ (hF₂ i)
    hT hM (hA i) (hW i) (hround i).1
  have hμpos i : 0 < μ i := lt_of_lt_of_le (by positivity) (hμbounds i).1
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hμupper : μ 0 ≤ (σ*(σ+1)+1)/(6*N*R^2) := by
    have hb := (hμbounds 0).2
    have hTeq : T=M^3/(N*R^2) :=
      (eq_div_iff (by positivity)).mpr (by nlinarith only [hscale])
    have he : (σ*(σ+1)+1)*T/(6*M^3)=(σ*(σ+1)+1)/(6*N*R^2) := by
      rw [hTeq]
      field_simp
    exact hb.trans_eq he
  have hlw : l ≤ w := hy₀.1.1.trans hy₀.1.2
  obtain ⟨hwidth,hheight⟩ := quartic_coefficient_budgets_of_source_coordinate_cutoff_signed
    hCcurv hCpos (hμpos 0) hN hRpos (hr 0) hd hl hlw hw
    (le_min (hden l ⟨le_rfl,hlw⟩ 0).1 (hden w ⟨hlw,le_rfl⟩ 0).1)
    (max_le (hden l ⟨le_rfl,hlw⟩ 0).2 (hden w ⟨hlw,le_rfl⟩ 0).2)
    hcoord hμupper hBcut hBsize hGcut
  have hdx (j) (hj : j∈S) : x j 0∈Ioo 0 (W 0) :=
    ⟨by linarith [(hx j hj 0).1],by linarith [(hx j hj 0).2]⟩
  obtain ⟨a,b,j,_hj,hcoeff,hanti,hphys,hG,hmass,hantiAll⟩ := physicalModelPhase_common_coefficient_samples_with_mass
    (ac:=ac) (bc:=bc)
    S p (fun n => x n 0) hS hσ hδ (hF₂ 0) hT hM (hA 0) (hW 0) hN
    (hμpos 0) (hμpos 1).ne' (hr 0) (hr 1) (hdet 0)
    (fun z hz => hd.trans_le (hden z hz 0).1)
    (fun z hz => (hd.trans_le (hden z hz 1).1).ne') hwidth hheight hpt hdx hwindow
    (fun n hn => hpoint n hn 0) hy₀ hy hcurv
  have hH i : 0 ≤ H i := (abs_nonneg _).trans (hdisplacement _ (hcoeff 0).1 i)
  have hn : 0 < nSpan := by linarith only [hH 0,hspan 0]
  have hnsquare : nSpan^2 ≤ M*R := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg nSpan) (mul_nonneg hM.le hRpos.le)
      (by norm_num : (3:ℕ) ≠ 0)).mp
    have hh := pow_le_pow_left₀ (pow_nonneg hn.le 3) hsourcecube 2
    have hh' := mul_le_mul_of_nonneg_left hRM (show 0 ≤ M^2*R^3 by positivity)
    nlinarith only [hh,hh']
  have hsquare i : (H i+1)^2 ≤ M*R := by
    apply (pow_le_pow_left₀ (add_nonneg (hH i) zero_le_one)
      (show H i+1 ≤ nSpan by linarith only [hH i,hspan i]) 2).trans hnsquare
  have hκle : κ ≤ σ*(σ+1)+1 := by
    have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ (hF₂ 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2)
    exact hh.1.trans hh.2
  have hLspan : L*N ≤ nSpan := by
    have hrati : κ/(σ*(σ+1)+1) ≤ 1 := (div_le_one hCpos).mpr hκle
    have hsmall := mul_le_mul_of_nonneg_right hrati
      (div_pos (mul_pos hN hcount) (by norm_num : (0:ℝ)<144)).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/144) := by
      dsimp only [L]
      field_simp
    rw [← he,one_mul] at hsmall
    have hg := hphys (0:Fin 7)
    have hdiff := le_abs_self (x (j (1:Fin 8)) 0-x (j (0:Fin 8)) 0)
    have htri := abs_sub_le (x (j (1:Fin 8)) 0) (xref 0) (x (j (0:Fin 8)) 0)
    rw [abs_sub_comm (xref 0)] at htri
    have hleft := hdisplacement _ (hcoeff (0:Fin 8)).1 0
    have hright := hdisplacement _ (hcoeff (1:Fin 8)).1 0
    change N*(S.card:ℝ)/144 ≤ x (j 1) 0-x (j 0) 0 at hg
    linarith only [hsmall,hg,hdiff,htri,hleft,hright,hspan 0]
  have hNL : (L*N)^2 ≤ M*R :=
    (pow_le_pow_left₀ (mul_pos hL hN).le hLspan 2).trans hnsquare
  let Kw := nSpan/(L*N)
  have hKwscale : Kw*L*N=nSpan := by dsimp only [Kw]; field_simp
  have hdiam i : 2*H i+1 ≤ Kw*L*N := by rw [hKwscale]; exact hspan i
  let z : Fin 8 → ℝ := fun i => y (j i.rev)
  have hmono : StrictMono z := hanti.comp Fin.rev_strictAnti
  have hz (i : Fin 8) : z i∈Icc l w := (hy _ (hcoeff i.rev).1).1
  have hsub : Icc (z 0) (z 7) ⊆ Icc l w :=
    fun q hq => ⟨(hz 0).1.trans hq.1,hq.2.trans (hz 7).2⟩
  have hcoef : κ/(σ*(σ+1)+1) ≤ κ*T/(6*μ 0*M^3) := by
    have hb : 6*μ 0*M^3 ≤ (σ*(σ+1)+1)*T := by
      have hh := (le_div_iff₀ (show 0 < 6*M^3 by positivity)).mp (hμbounds 0).2
      change μ 0*(6*M^3) ≤ (σ*(σ+1)+1)*T at hh
      nlinarith only [hh]
    apply (div_le_div_iff₀ hCpos
      (mul_pos (mul_pos (by norm_num) (hμpos 0)) (pow_pos hM 3))).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hb hκ.le]
  have hgap (i : Fin 7) : L*N ≤ |G (z i.succ)-G (z i.castSucc)| := by
    have hh := mul_le_mul_of_nonneg_right hcoef
      (div_pos (mul_pos hN hcount) (by norm_num : (0:ℝ) < 144)).le
    have he : L*N=κ/(σ*(σ+1)+1)*(N*(S.card:ℝ)/144) := by
      dsimp only [L]
      field_simp
    rw [he]
    dsimp only [z]
    rw [Fin.rev_succ,Fin.rev_castSucc,abs_sub_comm]
    exact (hh.trans (hG i.rev)).trans (le_abs_self _)
  have hroot (i : Fin 8) (a : Fin 2) :
      iteratedDeriv 2 (f a) (x (j i.rev) a)/2=(e a*z i+v a)/(r a*z i+s a) := by
    rw [hpoint _ (hcoeff i.rev).1 a]
    have ht : ((p (j i.rev)).2:ℝ) ≠ 0 := by
      exact_mod_cast (hpt _ (hcoeff i.rev).1).ne'
    dsimp only [z,y]
    have hn : e a*(((p (j i.rev)).1:ℝ)/(p (j i.rev)).2)+v a=
      (e a*(p (j i.rev)).1+v a*(p (j i.rev)).2)/(p (j i.rev)).2 := by field_simp
    have hd' : r a*(((p (j i.rev)).1:ℝ)/(p (j i.rev)).2)+s a=
      (r a*(p (j i.rev)).1+s a*(p (j i.rev)).2)/(p (j i.rev)).2 := by field_simp
    rw [hn,hd',div_div_div_cancel_right₀ ht]
  have hex (i : Fin 2) := physicalModelPhase_interval_root_family
    (l:=z 0) (w:=z 7) (x₀:=xref i) hσ.le (hF₂ i) hT hM (hA i) (hW i)
    (hx _ (hcoeff (0:Fin 8).rev).1 i) (hx _ (hcoeff (7:Fin 8).rev).1 i)
    (hd.trans_le (hden _ (hz 0) i).1) (hd.trans_le (hden _ (hz 7) i).1)
    (hdisplacement _ (hcoeff (0:Fin 8).rev).1 i)
    (hdisplacement _ (hcoeff (7:Fin 8).rev).1 i)
    (by rw [← hroot 0 i]; exact Set.left_mem_uIcc)
    (by rw [← hroot 7 i]; exact Set.right_mem_uIcc)
  choose ρ hρ hρdiam using hex
  have hdiam' i : |x (j (7:Fin 8).rev) i-x (j (0:Fin 8).rev) i|+1 ≤ Kw*L*N := by
    have hh := abs_sub_le (x (j (7:Fin 8).rev) i) (xref i) (x (j (0:Fin 8).rev) i)
    rw [abs_sub_comm (xref i)] at hh
    linarith only [hh,hdisplacement _ (hcoeff (7:Fin 8).rev).1 i,
      hdisplacement _ (hcoeff (0:Fin 8).rev).1 i,hdiam i]
  have hmiddle := physicalModelPhase_quartic_middle_third_condition
    (x₁:=fun q i => ρ i q) (α:=ac-a) (β:=bc-b) z
    hσ hδ hF hT hM hN hR hL hNL hd hK hA hW hxref
    (fun q hq i => (hρ i q hq).2.1) hr hdet
    (fun q hq i => (hden q (hsub hq) i).1)
    (fun q hq i => (hden q (hsub hq) i).2) hmono hLspan hsourcecube
    (fun q hq t ht i => by
      have hh := (hρdiam i q hq t ht).trans (hdiam' i)
      rwa [hKwscale] at hh)
    hbase (fun q hq i => (hρ i q hq).2.2.1)
    (fun q hq i => (pow_le_pow_left₀ (abs_nonneg _)
      (hρ i q hq).2.2.2.2 2).trans (hsquare i))
    hgap (fun i => by
      have hh := hres _ (hcoeff i.rev).1
      rw [(hcoeff i.rev).2.1,(hcoeff i.rev).2.2] at hh
      exact hh)
  let E := S.filter (fun n => j 3<n ∧ n<j 4)
  refine ⟨E,Finset.filter_subset _ _,?_,?_⟩
  · exact hmass 3
  · intro n hn
    obtain ⟨hnS,hleftn,hrightn⟩ := Finset.mem_filter.mp hn
    have hymid : y n∈Icc (z 3) (z 4) := by
      change y (j 4) ≤ y n ∧ y n ≤ y (j 3)
      exact ⟨hantiAll hnS (hcoeff 4).1 hrightn.le,
        hantiAll (hcoeff 3).1 hnS hleftn.le⟩
    have hyn : y n∈Icc (z 0) (z 7) :=
      ⟨(hmono.monotone (by decide : (0:Fin 8) ≤ 3)).trans hymid.1,
        hymid.2.trans (hmono.monotone (by decide : (4:Fin 8) ≤ 7))⟩
    have hpointn i : iteratedDeriv 2 (f i) (x n i)/2=(e i*y n+v i)/(r i*y n+s i) := by
      rw [hpoint n hnS i]
      have ht : ((p n).2:ℝ) ≠ 0 := by exact_mod_cast (hpt n hnS).ne'
      dsimp only [y]
      have ha : e i*((p n).1:ℝ)/(p n).2+v i=
          (e i*(p n).1+v i*(p n).2)/(p n).2 := by field_simp
      have hb : r i*((p n).1:ℝ)/(p n).2+s i=
          (r i*(p n).1+s i*(p n).2)/(p n).2 := by field_simp
      rw [← mul_div_assoc,ha,← mul_div_assoc,hb,div_div_div_cancel_right₀ ht]
    have hsame : (fun i => ρ i (y n))=x n :=
      physicalModelPhase_reference_roots_unique hσ hδ hF₂ hT hM hA hW
        (fun i => ⟨by linarith [(hρ i (y n) hyn).2.1.1],
          by linarith [(hρ i (y n) hyn).2.1.2]⟩)
        (fun i => ⟨by linarith [(hx n hnS i).1],by linarith [(hx n hnS i).2]⟩)
        (fun i => (hρ i (y n) hyn).2.2.1) hpointn
    have hh := hmiddle (y n) hymid
    change |(iteratedDeriv 3 (f 1) (round (ρ 1 (y n)))/6)*(r 1*y n+s 1)^3/
      ((iteratedDeriv 3 (f 0) (round (ρ 0 (y n)))/6)*(r 0*y n+s 0)^3)-1| ≤ _ at hh
    rw [show ρ 1 (y n)=x n 1 from congrFun hsame 1,
      show ρ 0 (y n)=x n 0 from congrFun hsame 0] at hh
    exact hh

#print axioms physicalModelPhase_occupied_window_quartic_third_mass_signed

/-- The literal actual Fourier family, with a signed reference selected
from an occupied seed, yields the original-matrix L^-3 bound and an
occupied subfamily with the original-denominator L^-2 Third Condition.
The absolute source cutoff and coordinate height replace the left-chart
sign restriction; anchor, cell and scalar geometry remain explicit. -/
theorem physicalModelPhase_actual_fourier_constructed_family_long_block_signed
    (S : Finset ℕ) (hS : 288 ≤ S.card) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| *w ≤ 2*d) (hl : 0 ≤ l) (hw : 1 ≤ w) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, 0 < (v:ℝ)-s*((rat j 0:ℝ)+ε)) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let U := Ccurv*R^4/(N*d^3)
    let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
      (μr 1) (νr 1) (rp 1) (sp 1) U
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    Δ < 1/2 →
    (∀ j∈S, 1 ≤ β j) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 1536*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    let Γ := Cphys/κ
    let L := κ/(144*Cphys)*(S.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    ∃ E : Finset ℕ, E ⊆ S ∧ (S.card:ℝ)/144 ≤ (E.card:ℝ) ∧
      ∀ j∈E, |mu j 1*(q j 1:ℝ)^3/(mu j 0*(q j 0:ℝ)^3)-1| ≤
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) := by
  classical
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  obtain ⟨xref,hxr⟩ := physicalModelPhase_actual_matrix_reference_roots_signed
    Q K₀ (rat jref) Mat e r hσ hδ hF₂ hT hM hN hRpos hLref hQ hscale hmesh
    hA hW (hx jref hjref) (hden jref hjref) hMatdet hMatgamma hrefWindow hr
    (hlevel jref hjref) (hMatt jref hjref) (hMatmap jref hjref) hwideL hwideU hrefNear
  refine ⟨xref,hxr,?_⟩
  intro Hspan hdisplacement hspan ar μr νr G Ccurv Ctay D η U Z Kres hbudget hΔ hβ
    hdenregion hleft hright hlarge hBsize hGcut Γ L C
  have hrp i : rp i ≠ 0 := (mul_ne_zero_iff.mp (hxr i).1.ne').1
  have hxref i : xref i∈Ioo (1/2:ℝ) (W i-1/2) := (hxr i).2.1
  have href i : iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i := (hxr i).2.2.1
  let p : ℕ → ℤ × ℤ := fun j =>
    (v*(q j 0:ℤ)-s*(rat j 0).num,r*(rat j 0).num-e*(q j 0:ℤ))
  let y := fun j => ((p j).1:ℝ)/(p j).2
  let dr := fun i => deriv (f i) (ar i)
  let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
  let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
  let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
  let ac := θr 0-θr 1
  let bc := βr 0-βr 1
  let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
  let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
  let φ := fun z => g z-hq z
  have hMone : 1 ≤ M := hR.trans hRM
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,Cphys]; positivity
  have hNscale : N^2 ≤ M*R := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg N) (mul_nonneg hM.le hRpos.le)
      (by norm_num : (3:ℕ) ≠ 0)).mp
    have hh := pow_le_pow_left₀ (pow_nonneg hN.le 3) hNcube 2
    have hh' := mul_le_mul_of_nonneg_left hRM (show 0 ≤ M^2*R^3 by positivity)
    nlinarith only [hh,hh']
  have hrect j (hj : j∈S) : 0 < (p j).2 ∧ y j∈Icc (α j) (β j) := by
    have ha : (anchor j:ℝ)∈Icc (lo j) (hi j) := by
      have hh := abs_le.mp (hanchor j hj)
      exact ⟨by dsimp only [lo]; linarith only [hh.1],
        by dsimp only [hi]; linarith only [hh.2]⟩
    have hp : (rat j 0:ℝ)∈Icc (lo j) (hi j) := by
      constructor <;> dsimp only [lo,hi] <;> linarith only [hε]
    have hh := inverseFarey_original_seed_enlarged_rectangle_signed
      hchart (hdl j hj) (hdw j hj) (hnum j hj) ha hp (hdyad j hj) (hcut j hj)
      (show ((rat j 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden j hj 0).1)
    exact ⟨by exact_mod_cast hh.1,hh.2.1⟩
  have hy j (hj : j∈S) : y j∈finiteBoundaryCell Z l w k :=
    (finiteBoundaryCell_ordConnected Z l w k).out (hleft j hj) (hright j hj) (hrect j hj).2
  have hlocalI j (hj : j∈S) : Icc (α j) (β j) ⊆ Icc l w :=
    fun z hz => ⟨(hleft j hj).1.1.trans hz.1,hz.2.trans (hright j hj).1.2⟩
  have hleft' j (hj : j∈S) : α j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨le_rfl,(hrect j hj).2.1.trans (hrect j hj).2.2⟩,(hleft j hj).2⟩
  have hright' j (hj : j∈S) : β j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨(hrect j hj).2.1.trans (hrect j hj).2.2,le_rfl⟩,(hright j hj).2⟩
  have hsource j (hj : j∈S) :
      |iteratedDeriv 2 g (y j)-iteratedDeriv 2 hq (y j)| ≤ U ∧
      |(ac-round (ac-deriv φ (y j)))*y j+
        (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+hq (y j)| ≤
        Kres*R^2/|(rp 0:ℝ)*G (y j)| := by
    exact physicalModelPhase_actual_fourier_original_seed_source_bounds_signed
      Q K₀ (rat j) (vinv j) (parity j) Mat (anchor j) e r v s
      hσ hδ hF hT hM hN hRpos hQ hscale hmesh hA hW (hx j hj)
      (hden j hj) (hinv j hj) (hlevel j hj) (hcolor j hj) (hnear j hj)
      hsmall hNR hRN hNcube hminscale hMatdet (hMatt j hj) (hMatmap j hj) hMatgamma
      hNtwo (hL j hj) (hU j hj) hchart (hdl j hj) (hdw j hj) (hnum j hj)
      (hdyad j hj) (hanchor j hj) (hcut j hj) (hcount j hj)
      hMone hR hRM hNscale hd (hβ j hj) hΔ hrp hxref href (hbudget j hj)
      (fun z hz i => (hdenregion z (hlocalI j hj hz) i).1)
      (hleft' j hj) (hright' j hj) (hlarge j hj)
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hdetp i : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hcoordinates j (hj : j∈S) :
      (∀ i, (rp i:ℝ)*(p j).1+sp i*(p j).2=(q j i:ℝ)) ∧
      (∀ i, iteratedDeriv 2 (f i) (x j i)/2=
        ((ep i:ℝ)*(p j).1+vp i*(p j).2)/((rp i:ℝ)*(p j).1+sp i*(p j).2)) := by
    have hqpos a : (0:ℝ) < q j a := by exact_mod_cast (rat j a).pos
    have hrat a : (rat j a:ℝ)=((rat j a).num:ℝ)/(q j a:ℝ) := Rat.cast_def _
    have hdenR : (Mat 2:ℝ)*(rat j 0).num+Mat 3*q j 0=q j 1 := by
      calc
        _ = ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)*q j 0 := by
          rw [hrat]; field_simp [(hqpos 0).ne']
        _ = q j 1 := by rw [hMatt j hj]; field_simp [(hqpos 0).ne']
    have hnumR : (Mat 0:ℝ)*(rat j 0).num+Mat 1*q j 0=(rat j 1).num := by
      have hm := hMatmap j hj
      rw [hMatt j hj,hrat 0,hrat 1] at hm
      have hh := (div_eq_iff (div_ne_zero (hqpos 1).ne' (hqpos 0).ne')).mp hm
      field_simp [(hqpos 0).ne',(hqpos 1).ne'] at hh
      nlinarith only [hh]
    have hqp a : (rp a:ℝ)*(p j).1+sp a*(p j).2=(q j a:ℝ) := by
      fin_cases a
      · dsimp only [p,rp,sp]; push_cast
        linear_combination (q j 0:ℝ)*hchartR
      · dsimp only [p,rp,sp]; push_cast
        linear_combination ((Mat 2:ℝ)*(rat j 0).num+Mat 3*q j 0)*hchartR+hdenR
    have hap a : (ep a:ℝ)*(p j).1+vp a*(p j).2=((rat j a).num:ℝ) := by
      fin_cases a
      · dsimp only [p,ep,vp]; push_cast
        linear_combination ((rat j 0).num:ℝ)*hchartR
      · dsimp only [p,ep,vp]; push_cast
        linear_combination ((Mat 0:ℝ)*(rat j 0).num+Mat 1*q j 0)*hchartR+hnumR
    refine ⟨hqp,?_⟩
    intro i
    rw [hqp,hap,hlevel j hj,hrat]
  have hpoint j (hj : j∈S) i := (hcoordinates j hj).2 i
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]; positivity
  have hCcurv : 0 ≤ Ccurv := by dsimp only [Ccurv]; positivity
  have hKres : 0 ≤ Kres := by
    dsimp only [Kres,Cc,Ct,C₂,C₃,quarticNonlinearResidualConstant]
    positivity
  obtain ⟨j₀,hj₀⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hbound := physicalModelPhase_occupied_window_quartic_determinant_signed
    (ac:=ac) (bc:=bc) (y₀:=y j₀) (Ccurv:=Ccurv) (Bcut:=Bcut)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    S p x hS hσ hδ hF hT hM hN hR hd hKres hRM hscale hA hW hxref
    (fun j hj => (hrect j hj).1) hx hwindow hdisplacement hspan hsourcecube
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast hrp i)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i)
    hdenregion hcoord hl hw hCcurv hBcut hBsize hGcut
    href hpoint (hy j₀ hj₀) hy (hsource j₀ hj₀).1 (fun j hj => (hsource j hj).2)
  have hentry : (rp 0:ℝ)*sp 1-sp 0*rp 1=(Mat 2:ℝ) := by
    dsimp only [rp,sp]
    push_cast
    linear_combination (Mat 2:ℝ)*hchartR
  change |(rp 0:ℝ)*sp 1-sp 0*rp 1| ≤ _ at hbound
  rw [hentry] at hbound
  refine ⟨hbound,?_⟩
  have hthirdMass := physicalModelPhase_occupied_window_quartic_third_mass_signed
    (ac:=ac) (bc:=bc) (y₀:=y j₀) (Ccurv:=Ccurv) (Bcut:=Bcut)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    S p x hS hσ hδ hF hT hM hN hR hd hKres hRM hscale hA hW hxref
    (fun j hj => (hrect j hj).1) hx hwindow hdisplacement hspan hsourcecube
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast hrp i)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i)
    hdenregion hcoord hl hw hCcurv hBcut hBsize hGcut
    href hpoint (hy j₀ hj₀) hy (hsource j₀ hj₀).1 (fun j hj => (hsource j hj).2)
  obtain ⟨E,hES,hEcard,hEthird⟩ := hthirdMass
  refine ⟨E,hES,hEcard,?_⟩
  intro n hn
  have hnS := hES hn
  have ht : ((p n).2:ℝ) ≠ 0 := by exact_mod_cast (hrect n hnS).1.ne'
  have hqp := (hcoordinates n hnS).1
  have hdq i : ((rp i:ℝ)*y n+sp i)*((p n).2:ℝ)=(q n i:ℝ) := by
    calc
      _ = (rp i:ℝ)*(p n).1+sp i*(p n).2 := by
        dsimp only [y]
        rw [add_mul,mul_assoc,div_mul_cancel₀ _ ht]
      _ = _ := hqp i
  have hratio : mu n 1*(q n 1:ℝ)^3/(mu n 0*(q n 0:ℝ)^3)=
      mu n 1*((rp 1:ℝ)*y n+sp 1)^3/(mu n 0*((rp 0:ℝ)*y n+sp 0)^3) := by
    rw [← hdq 1,← hdq 0,mul_pow,mul_pow,← mul_assoc,← mul_assoc]
    exact mul_div_mul_right _ _ (pow_ne_zero 3 ht)
  rw [hratio]
  exact hEthird n hn

#print axioms physicalModelPhase_actual_fourier_constructed_family_long_block_signed

/-- With both affine endpoint denominators positive, the actual
boundary-window count and 17-cell selection have the same 48-window
loss for either reference orientation. No exceptional-count assumption. -/
theorem physicalModelPhase_farey_common_cell_selection_signed
    (S : Finset ℕ) (Z : Finset ℝ) (x : ℕ → ℝ)
    {σ δ T M A W N R base ε e r v s l w : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hphase : T*N*R^2=M^3)
    (hsmall : 4*ε*R^2 ≤ modelPhaseThirdLower σ) (hε : 0 ≤ ε)
    (hdet : v*r-e*s=1) (hZ : Z.card ≤ 16)
    (hx : ∀ j∈S, x j∈Ioo 0 W)
    (hwindow : ∀ j∈S, x j∈Icc (base+(j:ℝ)*N) (base+((j:ℝ)+1)*N))
    (hregion : ∀ z∈Icc l w, 0 < r*z+s) :
    let f := heathBrownPhysicalPhase F T M A 1
    let q := fun j => iteratedDeriv 2 f (x j)/2
    let α := fun j => (v-s*(q j+ε))/(r*(q j+ε)-e)
    let β := fun j => (v-s*(q j-ε))/(r*(q j-ε)-e)
    (∀ j∈S, 0 < r*(q j-ε)-e ∧ 0 < r*(q j+ε)-e) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    ∃ (k : Fin 17) (E : Finset ℕ), E⊆S ∧ S.card ≤ 48+17*E.card ∧
      ∀ j∈E, α j∈finiteBoundaryCell Z l w k ∧ β j∈finiteBoundaryCell Z l w k := by
  classical
  intro f q α β hcharts hends
  have hchart j (hj : j∈S) := (hcharts j hj).1
  have hchart' j (hj : j∈S) := (hcharts j hj).2
  have hab j (hj : j∈S) : α j ≤ β j := by
    have hh := inverseFarey_difference hdet (hchart j hj).ne' (hchart' j hj).ne'
    have hn : 0 ≤ ((q j+ε)-(q j-ε))/((r*(q j-ε)-e)*(r*(q j+ε)-e)) :=
      div_nonneg (by linarith only [hε]) (mul_pos (hchart j hj) (hchart' j hj)).le
    change (v-s*(q j+ε))/(r*(q j+ε)-e) ≤ (v-s*(q j-ε))/(r*(q j-ε)-e)
    linarith only [hh,hn]
  let ZI := Z.filter (fun z => z∈Icc l w)
  let bad := fun j => ∃ z∈Z, z∈Icc (α j) (β j)
  let good := S.filter (fun j => ¬bad j)
  have hbad : (S.filter bad).card ≤ 48 := by
    have hh := physicalModelPhase_farey_boundary_crossing_count S ZI x (v:=v)
      hσ hδ hF hT hM hN hR hA hW hphase hsmall hx hwindow
      (fun z hz => hregion z (Finset.mem_filter.mp hz).2)
      (fun j hj => ⟨hchart j hj,hchart' j hj⟩)
    have he : S.filter bad=S.filter (fun j => ∃ z∈ZI, z∈Icc (α j) (β j)) := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hj,z,hz,hza,hzb⟩
        refine ⟨hj,z,Finset.mem_filter.mpr ⟨hz,?_⟩,hza,hzb⟩
        exact ⟨(hends j hj).1.1.trans hza,hzb.trans (hends j hj).2.2⟩
      · rintro ⟨hj,z,hz,hzz⟩
        exact ⟨hj,z,(Finset.mem_filter.mp hz).1,hzz⟩
    rw [he]
    change (S.filter (fun j => ∃ z∈ZI, z∈Icc (α j) (β j))).card ≤ 3*ZI.card at hh
    have hc : ZI.card ≤ 16 := (Finset.card_filter_le _ _).trans hZ
    omega
  let color : ℕ → Fin 17 := fun j =>
    ⟨(Z.filter (fun z => z<α j)).card,lt_of_le_of_lt (Finset.card_filter_le _ _) (by omega)⟩
  have hbudget : (Finset.univ : Finset (Fin 17)).card • ((good.card:ℝ)/17) ≤ (good.card:ℝ) := by
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_num
    linarith
  obtain ⟨k,_hk,hcount⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (fun j (_hj : j∈good) => Finset.mem_univ (color j)) Finset.univ_nonempty hbudget
  let E := good.filter (fun j => color j=k)
  have hmass : good.card ≤ 17*E.card := by
    have hh : (good.card:ℝ) ≤ 17*(E.card:ℝ) := by
      change (good.card:ℝ)/17 ≤ (E.card:ℝ) at hcount
      linarith only [hcount]
    exact_mod_cast hh
  have hES : E⊆S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  refine ⟨k,E,hES,?_,?_⟩
  · have he := Finset.card_filter_add_card_filter_not (s:=S) bad
    change (S.filter bad).card+good.card=S.card at he
    omega
  · intro j hj
    have hjG := (Finset.mem_filter.mp hj).1
    have hjS := (Finset.mem_filter.mp hjG).1
    have hn := (Finset.mem_filter.mp hjG).2
    have haZ : α j∉Z := by
      intro hz
      exact hn ⟨α j,hz,le_rfl,hab j hjS⟩
    have hbZ : β j∉Z := by
      intro hz
      exact hn ⟨β j,hz,hab j hjS,le_rfl⟩
    have he : Z.filter (fun z => z<α j)=Z.filter (fun z => z<β j) := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · intro hz
        exact ⟨hz.1,hz.2.trans_le (hab j hjS)⟩
      · intro hz
        refine ⟨hz.1,?_⟩
        by_contra hnot
        exact hn ⟨z,hz.1,le_of_not_gt hnot,hz.2.le⟩
    have hc : (Z.filter (fun z => z<α j)).card=k.val :=
      congrArg Fin.val (Finset.mem_filter.mp hj).2
    exact ⟨⟨(hends j hjS).1,haZ,hc⟩,
      ⟨(hends j hjS).2,hbZ,by rw [←he]; exact hc⟩⟩

#print axioms physicalModelPhase_farey_common_cell_selection_signed

/-- Select an actual common curvature cell with the same 48-window
loss and factor 17, then derive both long-block savings for the signed
reference. The selected cell and occupied mass are constructed. -/
theorem physicalModelPhase_actual_fourier_selected_cell_long_block_signed
    (S : Finset ℕ) (hS : 4944 ≤ S.card) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| *w ≤ 2*d) (hl : 0 ≤ l) (hw : 1 ≤ w) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, 0 < (v:ℝ)-s*((rat j 0:ℝ)+ε)) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    Δ < 1/2 →
    (∀ j∈S, 1 ≤ β j) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 1536*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Γ := Cphys/κ
    let L := κ/(144*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    ∃ E : Finset ℕ, E ⊆ S₀ ∧ (S₀.card:ℝ)/144 ≤ (E.card:ℝ) ∧
      ∀ j∈E, |mu j 1*(q j 1:ℝ)^3/(mu j 0*(q j 0:ℝ)^3)-1| ≤
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) := by
 classical
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
  obtain ⟨xref,hxr⟩ := physicalModelPhase_actual_matrix_reference_roots_signed
    Q K₀ (rat jref) Mat e r hσ hδ hF₂ hT hM hN hRpos hLref hQ hscale hmesh
    hA hW (hx jref hjref) (hden jref hjref) hMatdet hMatgamma hrefWindow hr
    (hlevel jref hjref) (hMatt jref hjref) (hMatmap jref hjref) hwideL hwideU hrefNear
  refine ⟨xref,hxr,?_⟩
  intro Hspan hdisplacement hspan ar μr G Ccurv Ctay D η Kres hbudget hΔ hβ
    hdenregion hends hlarge hBsize hGcut
  let νr := fun i => iteratedDeriv 4 (f i) (ar i)/24
  let U := Ccurv*R^4/(N*d^3)
  let Z := quarticCurvatureBoundaryRoots (μr 0) (νr 0) (rp 0) (sp 0)
    (μr 1) (νr 1) (rp 1) (sp 1) U
  have hκp : 0 < κ := modelPhaseThirdLower_pos hσ
  have hchartReal : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hεnonneg : 0 ≤ ε := by dsimp only [ε,Cphys]; positivity
  have hεsmall : 4*ε*R^2 ≤ κ := by
    have hCpos : 0 < Cphys+2 := by dsimp only [Cphys]; positivity
    have heq : 4*ε*R^2=κ/(4*(Cphys+2)) := by
      dsimp only [ε]
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos (by norm_num) hCpos)).mpr
    have hh : 1 ≤ 4*(Cphys+2) := by
      have hp := mul_nonneg hσ.le (add_nonneg hσ.le zero_le_one)
      dsimp only [Cphys]
      linarith only [hp]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hκp.le
  obtain ⟨k,S₀,hS₀S,hS₀card,hcells⟩ :=
    physicalModelPhase_farey_common_cell_selection_signed S Z (fun j => x j 0)
      (ε:=ε) (e:=(e:ℝ)) (r:=(r:ℝ)) (v:=(v:ℝ)) (s:=(s:ℝ))
      hσ hδ (hF₂ 0) hT hM hN hRpos (hA 0) (hW 0) hscale hεsmall hεnonneg
      hchartReal
      (quarticCurvatureBoundaryRoots_card (μr 0) (νr 0) (rp 0) (sp 0)
        (μr 1) (νr 1) (rp 1) (sp 1) U)
      (fun j hj => ⟨by linarith only [(hx j hj 0).1],by linarith only [(hx j hj 0).2]⟩)
      (fun j hj => by simpa only [mul_comm] using hwindow j hj)
      (fun z hz => by
        have hh := (hdenregion z hz 0).1
        change d ≤ (r:ℝ)*z+s at hh
        exact hd.trans_le hh)
      (by
        intro j hj
        change 0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e ∧
          0 < (r:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e
        rw [hlevel j hj 0]
        exact ⟨hdl j hj,hdw j hj⟩)
      (by
        intro j hj
        change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈Icc l w ∧
          (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
            (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈Icc l w
        rw [hlevel j hj 0]
        exact hends j hj)
  have hS₀ : 288 ≤ S₀.card := by omega
  have hcells' j (hj : j∈S₀) :
      α j∈finiteBoundaryCell Z l w k ∧ β j∈finiteBoundaryCell Z l w k := by
    have hh := hcells j hj
    change (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2+ε))/
        (r*(iteratedDeriv 2 (f 0) (x j 0)/2+ε)-e)∈finiteBoundaryCell Z l w k ∧
      (v-s*(iteratedDeriv 2 (f 0) (x j 0)/2-ε))/
        (r*(iteratedDeriv 2 (f 0) (x j 0)/2-ε)-e)∈finiteBoundaryCell Z l w k at hh
    rw [hlevel j (hS₀S hj) 0] at hh
    exact hh
  refine ⟨S₀,hS₀S,hS₀card,?_⟩
  intro Γ L C
  have hx j (hj : j∈S₀) := hx j (hS₀S hj)
  have hwindow j (hj : j∈S₀) := hwindow j (hS₀S hj)
  have hden j (hj : j∈S₀) := hden j (hS₀S hj)
  have hinv j (hj : j∈S₀) := hinv j (hS₀S hj)
  have hlevel j (hj : j∈S₀) := hlevel j (hS₀S hj)
  have hcolor j (hj : j∈S₀) := hcolor j (hS₀S hj)
  have hnear j (hj : j∈S₀) := hnear j (hS₀S hj)
  have hMatt j (hj : j∈S₀) := hMatt j (hS₀S hj)
  have hMatmap j (hj : j∈S₀) := hMatmap j (hS₀S hj)
  have hL j (hj : j∈S₀) := hL j (hS₀S hj)
  have hU j (hj : j∈S₀) := hU j (hS₀S hj)
  have hdl j (hj : j∈S₀) := hdl j (hS₀S hj)
  have hdw j (hj : j∈S₀) := hdw j (hS₀S hj)
  have hnum j (hj : j∈S₀) := hnum j (hS₀S hj)
  have hdyad j (hj : j∈S₀) := hdyad j (hS₀S hj)
  have hanchor j (hj : j∈S₀) := hanchor j (hS₀S hj)
  have hcut j (hj : j∈S₀) := hcut j (hS₀S hj)
  have hcount j (hj : j∈S₀) := hcount j (hS₀S hj)
  have hdisplacement j (hj : j∈S₀) := hdisplacement j (hS₀S hj)
  have hbudget j (hj : j∈S₀) := hbudget j (hS₀S hj)
  have hβ j (hj : j∈S₀) := hβ j (hS₀S hj)
  have hlarge j (hj : j∈S₀) := hlarge j (hS₀S hj)
  have hleft j (hj : j∈S₀) := (hcells' j hj).1
  have hright j (hj : j∈S₀) := (hcells' j hj).2
  have hrp i : rp i ≠ 0 := (mul_ne_zero_iff.mp (hxr i).1.ne').1
  have hxref i : xref i∈Ioo (1/2:ℝ) (W i-1/2) := (hxr i).2.1
  have href i : iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i := (hxr i).2.2.1
  let p : ℕ → ℤ × ℤ := fun j =>
    (v*(q j 0:ℤ)-s*(rat j 0).num,r*(rat j 0).num-e*(q j 0:ℤ))
  let y := fun j => ((p j).1:ℝ)/(p j).2
  let dr := fun i => deriv (f i) (ar i)
  let δr := fun i => iteratedDeriv 2 (f i) (ar i)/2-(ep i:ℝ)/rp i
  let θr := fun i => (rp i:ℝ)*dr i-round ((rp i:ℝ)*dr i)
  let βr := fun i => dr i*sp i+2*δr i/(3*μr i*rp i)
  let ac := θr 0-θr 1
  let bc := βr 0-βr 1
  let g := rationalPhase (μr 0) (rp 0) (sp 0) (μr 1) (rp 1) (sp 1)
  let hq := quarticPhase (μr 0) (νr 0) (rp 0) (sp 0) (μr 1) (νr 1) (rp 1) (sp 1)
  let φ := fun z => g z-hq z
  have hMone : 1 ≤ M := hR.trans hRM
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hε : 0 < ε := by dsimp only [ε,Cphys]; positivity
  have hNscale : N^2 ≤ M*R := by
    apply (pow_le_pow_iff_left₀ (sq_nonneg N) (mul_nonneg hM.le hRpos.le)
      (by norm_num : (3:ℕ) ≠ 0)).mp
    have hh := pow_le_pow_left₀ (pow_nonneg hN.le 3) hNcube 2
    have hh' := mul_le_mul_of_nonneg_left hRM (show 0 ≤ M^2*R^3 by positivity)
    nlinarith only [hh,hh']
  have hrect j (hj : j∈S₀) : 0 < (p j).2 ∧ y j∈Icc (α j) (β j) := by
    have ha : (anchor j:ℝ)∈Icc (lo j) (hi j) := by
      have hh := abs_le.mp (hanchor j hj)
      exact ⟨by dsimp only [lo]; linarith only [hh.1],
        by dsimp only [hi]; linarith only [hh.2]⟩
    have hp : (rat j 0:ℝ)∈Icc (lo j) (hi j) := by
      constructor <;> dsimp only [lo,hi] <;> linarith only [hε]
    have hh := inverseFarey_original_seed_enlarged_rectangle_signed
      hchart (hdl j hj) (hdw j hj) (hnum j hj) ha hp (hdyad j hj) (hcut j hj)
      (show ((rat j 0).den:ℝ) ≤ (Q:ℝ) by exact_mod_cast (hden j hj 0).1)
    exact ⟨by exact_mod_cast hh.1,hh.2.1⟩
  have hy j (hj : j∈S₀) : y j∈finiteBoundaryCell Z l w k :=
    (finiteBoundaryCell_ordConnected Z l w k).out (hleft j hj) (hright j hj) (hrect j hj).2
  have hlocalI j (hj : j∈S₀) : Icc (α j) (β j) ⊆ Icc l w :=
    fun z hz => ⟨(hleft j hj).1.1.trans hz.1,hz.2.trans (hright j hj).1.2⟩
  have hleft' j (hj : j∈S₀) : α j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨le_rfl,(hrect j hj).2.1.trans (hrect j hj).2.2⟩,(hleft j hj).2⟩
  have hright' j (hj : j∈S₀) : β j∈finiteBoundaryCell Z (α j) (β j) k :=
    ⟨⟨(hrect j hj).2.1.trans (hrect j hj).2.2,le_rfl⟩,(hright j hj).2⟩
  have hsource j (hj : j∈S₀) :
      |iteratedDeriv 2 g (y j)-iteratedDeriv 2 hq (y j)| ≤ U ∧
      |(ac-round (ac-deriv φ (y j)))*y j+
        (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+hq (y j)| ≤
        Kres*R^2/|(rp 0:ℝ)*G (y j)| := by
    exact physicalModelPhase_actual_fourier_original_seed_source_bounds_signed
      Q K₀ (rat j) (vinv j) (parity j) Mat (anchor j) e r v s
      hσ hδ hF hT hM hN hRpos hQ hscale hmesh hA hW (hx j hj)
      (hden j hj) (hinv j hj) (hlevel j hj) (hcolor j hj) (hnear j hj)
      hsmall hNR hRN hNcube hminscale hMatdet (hMatt j hj) (hMatmap j hj) hMatgamma
      hNtwo (hL j hj) (hU j hj) hchart (hdl j hj) (hdw j hj) (hnum j hj)
      (hdyad j hj) (hanchor j hj) (hcut j hj) (hcount j hj)
      hMone hR hRM hNscale hd (hβ j hj) hΔ hrp hxref href (hbudget j hj)
      (fun z hz i => (hdenregion z (hlocalI j hj hz) i).1)
      (hleft' j hj) (hright' j hj) (hlarge j hj)
  let vp : Fin 2 → ℤ := ![v,Mat 0*v+Mat 1*s]
  have hchartR : (v:ℝ)*r-e*s=1 := by exact_mod_cast hchart
  have hdetp i : vp i*rp i-ep i*sp i=1 := by
    fin_cases i
    · exact hchart
    · change (Mat 0*v+Mat 1*s)*(Mat 2*e+Mat 3*r)-
        (Mat 0*e+Mat 1*r)*(Mat 2*v+Mat 3*s)=1
      linear_combination (v*r-e*s)*hMatdet+hchart
  have hcoordinates j (hj : j∈S₀) :
      (∀ i, (rp i:ℝ)*(p j).1+sp i*(p j).2=(q j i:ℝ)) ∧
      (∀ i, iteratedDeriv 2 (f i) (x j i)/2=
        ((ep i:ℝ)*(p j).1+vp i*(p j).2)/((rp i:ℝ)*(p j).1+sp i*(p j).2)) := by
    have hh := farey_matrix_original_seed_coordinates (rat j) Mat e r v s
      hchart (hMatt j hj) (hMatmap j hj)
    refine ⟨fun i => (hh i).1,?_⟩
    intro i
    rw [(hh i).1,(hh i).2,hlevel j hj i]
    exact Rat.cast_def _
  have hpoint j (hj : j∈S₀) i := (hcoordinates j hj).2 i
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
    (approximateModelPhase_iteratedDeriv_error (hF 0)
      (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ0
  have hCR : 0 ≤ quarticReciprocalConstant σ δ := by
    dsimp only [quarticReciprocalConstant]; positivity
  have hCcurv : 0 ≤ Ccurv := by dsimp only [Ccurv]; positivity
  have hKres : 0 ≤ Kres := by
    dsimp only [Kres,Cc,Ct,C₂,C₃,quarticNonlinearResidualConstant]
    positivity
  obtain ⟨j₀,hj₀⟩ := Finset.card_pos.mp (show 0 < S₀.card by omega)
  have hbound := physicalModelPhase_occupied_window_quartic_determinant_signed
    (ac:=ac) (bc:=bc) (y₀:=y j₀) (Ccurv:=Ccurv) (Bcut:=Bcut)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    S₀ p x hS₀ hσ hδ hF hT hM hN hR hd hKres hRM hscale hA hW hxref
    (fun j hj => (hrect j hj).1) hx hwindow hdisplacement hspan hsourcecube
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast hrp i)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i)
    hdenregion hcoord hl hw hCcurv hBcut hBsize hGcut
    href hpoint (hy j₀ hj₀) hy (hsource j₀ hj₀).1 (fun j hj => (hsource j hj).2)
  have hentry : (rp 0:ℝ)*sp 1-sp 0*rp 1=(Mat 2:ℝ) := by
    dsimp only [rp,sp]
    push_cast
    linear_combination (Mat 2:ℝ)*hchartR
  change |(rp 0:ℝ)*sp 1-sp 0*rp 1| ≤ _ at hbound
  rw [hentry] at hbound
  refine ⟨hbound,?_⟩
  have hthirdMass := physicalModelPhase_occupied_window_quartic_third_mass_signed
    (ac:=ac) (bc:=bc) (y₀:=y j₀) (Ccurv:=Ccurv) (Bcut:=Bcut)
    (e:=fun i => (ep i:ℝ)) (r:=fun i => (rp i:ℝ))
    (v:=fun i => (vp i:ℝ)) (s:=fun i => (sp i:ℝ))
    S₀ p x hS₀ hσ hδ hF hT hM hN hR hd hKres hRM hscale hA hW hxref
    (fun j hj => (hrect j hj).1) hx hwindow hdisplacement hspan hsourcecube
    (fun i => by change (rp i:ℝ) ≠ 0; exact_mod_cast hrp i)
    (fun i => by
      change (vp i:ℝ)*(rp i:ℝ)-(ep i:ℝ)*(sp i:ℝ)=1
      exact_mod_cast hdetp i)
    hdenregion hcoord hl hw hCcurv hBcut hBsize hGcut
    href hpoint (hy j₀ hj₀) hy (hsource j₀ hj₀).1 (fun j hj => (hsource j hj).2)
  obtain ⟨E,hES,hEcard,hEthird⟩ := hthirdMass
  refine ⟨E,hES,hEcard,?_⟩
  intro n hn
  have hnS := hES hn
  have ht : ((p n).2:ℝ) ≠ 0 := by exact_mod_cast (hrect n hnS).1.ne'
  have hqp := (hcoordinates n hnS).1
  have hdq i : ((rp i:ℝ)*y n+sp i)*((p n).2:ℝ)=(q n i:ℝ) := by
    calc
      _ = (rp i:ℝ)*(p n).1+sp i*(p n).2 := by
        dsimp only [y]
        rw [add_mul,mul_assoc,div_mul_cancel₀ _ ht]
      _ = _ := hqp i
  have hratio : mu n 1*(q n 1:ℝ)^3/(mu n 0*(q n 0:ℝ)^3)=
      mu n 1*((rp 1:ℝ)*y n+sp 1)^3/(mu n 0*((rp 0:ℝ)*y n+sp 0)^3) := by
    rw [← hdq 1,← hdq 0,mul_pow,mul_pow,← mul_assoc,← mul_assoc]
    exact mul_div_mul_right _ _ (pow_ne_zero 3 ht)
  rw [hratio]
  exact hEthird n hn

#print axioms physicalModelPhase_actual_fourier_selected_cell_long_block_signed

/-- The signed selected-cell savings bound the literal whole occupied
family with the same constants, including the large-entry hypothesis. -/
theorem physicalModelPhase_actual_fourier_selected_cell_family_count_signed
    (S : Finset ℕ) (hS : 4944 ≤ S.card) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| *w ≤ 2*d) (hl : 0 ≤ l) (hw : 1 ≤ w) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2))
    (hc : Mat 2 ≠ 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N → N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, 0 < (v:ℝ)-s*((rat j 0:ℝ)+ε)) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    (∀ j∈S, ∀ i, (H+|x j i-xref i|+1)^2 ≤ M*R) →
    Δ < 1/2 →
    (∀ j∈S, 1 ≤ β j) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 1536*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Γ := Cphys/κ
    let L := κ/(144*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Ccount := (4608*Cphys/κ^2)*
      (Γ^2*(Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)+
        Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    (S.card:ℝ) ≤ 4944+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
 classical
  have hlong := physicalModelPhase_actual_fourier_selected_cell_long_block_signed S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  obtain ⟨xref,hxr,hconsumer⟩ := hlong hlevel hcolor hnear
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
  refine ⟨xref,hxr,?_⟩
  intro Hspan hdisplacement hspan ar μr G Ccurv Ctay D η Kres hbudget hΔ hβ
    hdenregion hends hsector hBsize hGcut
  obtain ⟨S₀,hS₀S,hS₀card,hfirst,E,hES,hEcard,hEthird⟩ :=
    hconsumer Hspan hdisplacement hspan hbudget hΔ hβ hdenregion hends hsector hBsize hGcut
  have hS₀ : 288 ≤ S₀.card := by omega
  refine ⟨S₀,hS₀S,hS₀card,?_⟩
  intro Γ L C Ccount
  let Δ₃ := (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2)
  let ηround := (modelPhaseJetCoefficient σ 3+δ)/(2*κ*M)
  have hx j (hj : j∈S₀) := hx j (hS₀S hj)
  have hwindow j (hj : j∈S₀) := hwindow j (hS₀S hj)
  have hden j (hj : j∈S₀) := hden j (hS₀S hj)
  have hlevel j (hj : j∈S₀) := hlevel j (hS₀S hj)
  have hMatt j (hj : j∈S₀) := hMatt j (hS₀S hj)
  have hMatmap j (hj : j∈S₀) := hMatmap j (hS₀S hj)
  have hdisplacement j (hj : j∈S₀) := hdisplacement j (hS₀S hj)
  refine ⟨hfirst,?_⟩
  have hcellcount : (S₀.card:ℝ) ≤ 288+Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
    have hScard : (0:ℝ) < S₀.card := by exact_mod_cast (show 0 < S₀.card by omega)
    have hEpos : (0:ℝ) < E.card := (div_pos hScard (by norm_num)).trans_le hEcard
    obtain ⟨j₀,hj₀⟩ := Finset.card_pos.mp (show 0 < E.card by exact_mod_cast hEpos)
    have hΔ₃ : 0 ≤ Δ₃ := (abs_nonneg _).trans (hEthird j₀ hj₀)
    have hδ0 : 0 ≤ δ := (abs_nonneg _).trans
      (approximateModelPhase_iteratedDeriv_error (hF 0)
        (by norm_num : (3/2:ℝ)∈Ioo 1 2) 4 le_rfl)
    have hF₃ i := approximateModelPhase_mono (hF i) (by norm_num : 3 ≤ 4) le_rfl
    have hqpos j i : (0:ℝ) < q j i := by exact_mod_cast (rat j i).pos
    have htj j (hj : j∈S₀) :
        (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2)+Mat 3=(q j 1:ℝ)/q j 0 := by
      rw [hlevel j hj 0]
      exact hMatt j hj
    have hcnt := physicalModelPhase_paired_large_entry_nat_block_count
      (τ:=fun _ => T) E (fun j => x j 0) (fun j => x j 1)
      (Mat 0) (Mat 1) (Mat 2) (Mat 3)
      hσ hδ hδ0 hF₃ hT (fun _ => ⟨le_rfl,by linarith only [hT]⟩) hM hN
      hscale hA hW hΔ₃ hMatdet hc hlarge
      (fun j hj => hx j (hES hj) 0) (fun j hj => hx j (hES hj) 1)
      (fun j hj => by
        simpa only [Set.mem_Icc,mul_comm] using hwindow j (hES hj))
      (fun j hj => by
        change ((Mat 0:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2)+Mat 1)/
          ((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2)+Mat 3)=
            iteratedDeriv 2 (f 1) (x j 1)/2
        rw [hlevel j (hES hj) 0,hlevel j (hES hj) 1]
        exact hMatmap j (hES hj))
      (fun j hj => by
        change (1:ℝ)/2 ≤ (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2)+Mat 3 ∧
          (Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2)+Mat 3 ≤ 2
        rw [htj j (hES hj)]
        have ha : (q j 0:ℝ) ≤ Q := by exact_mod_cast (hden j (hES hj) 0).1
        have hb : (q j 1:ℝ) ≤ Q := by exact_mod_cast (hden j (hES hj) 1).1
        have ha' : (Q:ℝ) ≤ 2*(q j 0:ℝ) := by exact_mod_cast (hden j (hES hj) 0).2
        have hb' : (Q:ℝ) ≤ 2*(q j 1:ℝ) := by exact_mod_cast (hden j (hES hj) 1).2
        exact ⟨(le_div_iff₀ (hqpos j 0)).mpr (by linarith only [ha,hb']),
          (div_le_iff₀ (hqpos j 0)).mpr (by linarith only [hb,ha'])⟩)
      (fun j hj => by
        change |mu j 1*((Mat 2:ℝ)*(iteratedDeriv 2 (f 0) (x j 0)/2)+Mat 3)^3/
          mu j 0-1| ≤ Δ₃
        rw [htj j (hES hj)]
        have heq : mu j 1*((q j 1:ℝ)/q j 0)^3/mu j 0=
            mu j 1*(q j 1:ℝ)^3/(mu j 0*(q j 0:ℝ)^3) := by rw [div_pow]; ring
        rw [heq]
        exact hEthird j hj)
    have hcard : (S₀.card:ℝ) ≤ 144*(E.card:ℝ) := by
      have hh := (div_le_iff₀ (by norm_num : (0:ℝ)<144)).mp hEcard
      nlinarith only [hh]
    have hwhole : (S₀.card:ℝ) ≤ 144*(2+32*Cphys*(Γ^2*Δ₃+2*Γ*ηround)*R^2/
        (κ^2*|(Mat 2:ℝ)|)) :=
      hcard.trans (mul_le_mul_of_nonneg_left hcnt (by norm_num))
    have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
    have hCp : 0 < Cphys := by dsimp only [Cphys]; positivity
    have hΓ : 0 < Γ := div_pos hCp hκ
    have hκle : κ ≤ Cphys := by
      have hF₂ := approximateModelPhase_mono (hF 0) (by norm_num : 2 ≤ 4) le_rfl
      have hh := approximateModelPhase_thirdDeriv_bounds hσ hδ hF₂
        (by norm_num : (3/2:ℝ)∈Ioo 1 2)
      exact hh.1.trans hh.2
    have hInvM : 1/M ≤ R^2/(L^2*N^2) :=
      (occupied_cubic_span_inverse_budget S₀ (fun j => x j 0)
        hS₀ hκ hCp hκle hM hN hR hRM hsourcecube hwindow
        (fun j hj => hdisplacement j hj 0) (hspan 0)).2.2
    have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
    have hηround : ηround ≤ ((modelPhaseJetCoefficient σ 3+δ)/(2*κ))*R^2/(L^2*N^2) := by
      have hh := mul_le_mul_of_nonneg_left hInvM
        (div_nonneg hC₃ (mul_pos (by norm_num : (0:ℝ)<2) hκ).le)
      convert hh using 1 <;> dsimp only [ηround] <;> ring
    have hcR : (0:ℝ) < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
    apply hwhole.trans
    calc
      _ ≤ 144*(2+32*Cphys*(Γ^2*Δ₃+
          2*Γ*(((modelPhaseJetCoefficient σ 3+δ)/(2*κ))*R^2/(L^2*N^2)))*R^2/
            (κ^2*|(Mat 2:ℝ)|)) := by gcongr
      _ = _ := by dsimp only [Δ₃,Ccount]; ring
  have hmassR : (S.card:ℝ) ≤ 48+17*(S₀.card:ℝ) := by exact_mod_cast hS₀card
  calc
    _ ≤ 48+17*(S₀.card:ℝ) := hmassR
    _ ≤ 48+17*(288+Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|)) := by gcongr
    _ = _ := by ring

#print axioms physicalModelPhase_actual_fourier_selected_cell_family_count_signed

/-- The signed actual source family derives its cubic and padded-square
budgets from the occupied span and yields the same L^-3 matrix bound and
L^-2 whole-family count, with explicit chart geometry and absolute cutoff. -/
theorem physicalModelPhase_actual_fourier_selected_cell_source_count_signed
    (S : Finset ℕ) (hS : 4944 ≤ S.card) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R) (hRM : R ≤ M)
    (hQ : 0 < Q) (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hden : ∀ j∈S, ∀ i, (rat j i).den ≤ Q ∧ Q ≤ 2*(rat j i).den)
    (hinv : ∀ j∈S, ∀ i, ((rat j i).den:ℤ) ∣ (rat j i).num*vinv j i-1)
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| *w ≤ 2*d) (hl : 0 ≤ l) (hw : 1 ≤ w) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2))
    (hc : Mat 2 ≠ 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) :
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=(rat j i:ℝ)) →
    let q := fun j i => (rat j i).den
    let mu := fun j i => iteratedDeriv 3 (f i) (round (x j i))/6
    let ell := fun j i => deriv (f i) (round (x j i))
    let b := fun j i => (⌊(q j i:ℝ)*ell j i⌋+(parity j i:ℕ) : ℤ)
    let cround := fun j i => round ((q j i:ℝ)*ell j i)
    let tau := fun j i => ((b j i:ℝ)-(q j i:ℝ)*ell j i)/2
    let dual := fun j i => -2*mu j i*(Real.sqrt (2/(3*mu j i*(q j i:ℝ))))^3
    let cloud := fun j i => (![Int.fract (-(vinv j i:ℝ)*b j i/q j i),
      Int.fract (-(vinv j i:ℝ)/q j i),dual j i/Real.sqrt K₀,
      (3*dual j i*tau j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ :=
      ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ j∈S, b j 0-cround j 0=b j 1-cround j 1) →
    (∀ j∈S, ∀ a, |cloud j 0 a-cloud j 1 a| ≤ 2*radius a) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 → N ≤ R^2 → R ≤ N →
    2*R^2 ≤ (Q:ℝ)*N →
    Mat 0*Mat 3-Mat 1*Mat 2=1 →
    (∀ j∈S, (Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3=(q j 1:ℝ)/q j 0) →
    (∀ j∈S, ((Mat 0:ℝ)*(rat j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(rat j 0:ℝ)+Mat 3)=(rat j 1:ℝ)) →
    |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2) →
    let H := N/(Cphys+2)
    let ε := κ/(16*(Cphys+2)*R^2)
    2 ≤ N →
    (∀ j∈S, ∀ i, x j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, ∀ i, x j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)-ε)-e) →
    (∀ j∈S, 0 < (r:ℝ)*((rat j 0:ℝ)+ε)-e) →
    (∀ j∈S, 0 < (v:ℝ)-s*((rat j 0:ℝ)+ε)) →
    (∀ j∈S, max ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e) ≤
      2*min ((r:ℝ)*((rat j 0:ℝ)-ε)-e) ((r:ℝ)*((rat j 0:ℝ)+ε)-e)) →
    (∀ j∈S, |(anchor j:ℝ)-(rat j 0:ℝ)| ≤ ε) →
    (∀ j∈S, 256*((anchor j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ j∈S, 256 ≤ (2*ε)*((Q:ℝ)/3)*(anchor j).den) →
    let lo := fun j => (rat j 0:ℝ)-ε
    let hi := fun j => (rat j 0:ℝ)+ε
    let α := fun j => ((v:ℝ)-s*hi j)/((r:ℝ)*hi j-e)
    let β := fun j => ((v:ℝ)-s*lo j)/((r:ℝ)*lo j-e)
    let Kaux := fun j => ⌊((Q:ℝ)/3)*min ((r:ℝ)*lo j-e) ((r:ℝ)*hi j-e)⌋₊
    let Saux := fun j => HuxleyLinearForm.fareySector (Kaux j) (α j) (β j)
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let ep : Fin 2 → ℤ := ![e,Mat 0*e+Mat 1*r]
    let rp : Fin 2 → ℤ := ![r,Mat 2*e+Mat 3*r]
    let sp : Fin 2 → ℤ := ![s,Mat 2*v+Mat 3*s]
    ∃ xref : Fin 2 → ℝ,
      (∀ i, 0 < rp i*r ∧ xref i∈Ioo (1/2:ℝ) (W i-1/2) ∧
        iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i ∧
        |xref i-x jref i| ≤ Lref*N ∧
        |(round (xref i):ℝ)-(round (x jref i):ℝ)| ≤ Lref*N+1) ∧
    ∀ Hspan : Fin 2 → ℝ,
    (∀ j∈S, ∀ i, |x j i-xref i| ≤ Hspan i) →
    (∀ i, 2*Hspan i+1 ≤ nSpan) →
    let ar := fun i => round (xref i)
    let μr := fun i => iteratedDeriv 3 (f i) (ar i)/6
    let G := minorArcCoordinate (μr 0) (rp 0) (sp 0)
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let Ctay := (2/κ)*(B+2*quarticReciprocalConstant σ δ)*R^4/(N*d^3)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let η := fun j => D+(Kaux j:ℝ)*Ctay*(β j-α j)^2
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    Δ < 1/2 →
    (∀ j∈S, 1 ≤ β j) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 1536*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Γ := Cphys/κ
    let L := κ/(144*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Ccount := (4608*Cphys/κ^2)*
      (Γ^2*(Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)+
        Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    (S.card:ℝ) ≤ 4944+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) := by
  classical
  have hsource := physicalModelPhase_actual_fourier_selected_cell_family_count_signed S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge
  intro f hlevel q mu ell b cround tau dual cloud radius hcolor hnear
    κ Cphys c J B hsmall hNR hRN hminscale hMatdet hMatt hMatmap hMatgamma
    H ε hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    lo hi α β Kaux Saux C₂ C₃ Ct Cc Δ ep rp sp
  have hSsmall : 288 ≤ S.card := by omega
  have hC0 : 0 ≤ Cphys := by dsimp only [Cphys]; positivity
  by_cases hNcube : N^3 ≤ M*R^2
  · obtain ⟨xref,hxr,hconsumer⟩ := hsource hlevel hcolor hnear
      hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
      hNtwo hL hU hdl hdw hnum hdyad hanchor hcut hcount
    refine ⟨xref,hxr,?_⟩
    intro Hspan hdisplacement hspan ar μr G Ccurv Ctay D η Kres hΔ hβ
      hdenregion hends hsector hBsize hGcut
    have hpadding := occupied_cubic_span_buffer_budget S x xref Hspan
      hSsmall hC0 hM hN hNtwo hR hRM hsourcecube hwindow hdisplacement hspan
    exact hconsumer Hspan hdisplacement hspan hpadding.2 hΔ hβ
      hdenregion hends hsector hBsize hGcut
  · have hF₂ i := approximateModelPhase_mono (hF i) (by norm_num : 2 ≤ 4) le_rfl
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    obtain ⟨xref,hxr⟩ := physicalModelPhase_actual_matrix_reference_roots_signed
      Q K₀ (rat jref) Mat e r hσ hδ hF₂ hT hM hN hRpos hLref hQ hscale hmesh
      hA hW (hx jref hjref) (hden jref hjref) hMatdet hMatgamma hrefWindow hr
      (hlevel jref hjref) (hMatt jref hjref) (hMatmap jref hjref) hwideL hwideU hrefNear
    refine ⟨xref,hxr,?_⟩
    intro Hspan hdisplacement hspan
    have hpadding := occupied_cubic_span_buffer_budget S x xref Hspan
      hSsmall hC0 hM hN hNtwo hR hRM hsourcecube hwindow hdisplacement hspan
    exact (hNcube hpadding.1).elim

#print axioms physicalModelPhase_actual_fourier_selected_cell_source_count_signed

/-- Reflecting the literal complete sector proves original-coordinate
integer-label rigidity on a negative-slope interval. The strict size
gate also rules out the half-integer rounding tie, so the output uses
the original nearest integers rather than a changed label convention. -/
theorem negative_fareySector_integer_labels_enlarged_rectangle
    {N : ℕ} {l w B α β δ : ℝ}
    (hw : w < 0) (hl : l ≤ -1) (hB : 1 ≤ B) (hδ : 0 ≤ δ) :
    let P := HuxleyLinearForm.fareySector N (-w) (-l)
    let S := P.image (fun p : ℤ × ℤ => (-p.1,p.2))
    max ((w-l)*(N:ℝ)^2/B) 2 ≤ (S.card:ℝ) →
    1536*B*δ*((-l)*(N:ℝ))*(N:ℝ) < (S.card:ℝ) →
    (∀ p∈S, ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) →
    ∀ p : ℤ × ℤ, 0 ≤ -(p.1:ℝ) → -(p.1:ℝ) ≤ 12*((-l)*(N:ℝ)) →
      0 ≤ (p.2:ℝ) → (p.2:ℝ) ≤ 12*(N:ℝ) → ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*round α+p.2*round β := by
  classical
  intro P S hR hlarge hnear
  have hinj : Function.Injective (fun p : ℤ × ℤ => (-p.1,p.2)) := by
    intro p q hpq
    have h₁ := congrArg Prod.fst hpq
    have h₂ := congrArg Prod.snd hpq
    exact Prod.ext (neg_injective h₁) h₂
  have hcard : S.card=P.card := Finset.card_image_of_injective P hinj
  rw [hcard] at hR hlarge
  have hw' : 0 < -w := neg_pos.mpr hw
  have hl' : 1 ≤ -l := by linarith only [hl]
  have hR' : max (((-l)-(-w))*(N:ℝ)^2/B) 2 ≤ (P.card:ℝ) := by
    have heq : (-l)-(-w)=w-l := by ring
    rw [heq]
    exact hR
  have hnear' : ∀ p∈P, ∃ b : ℤ, |(p.1:ℝ)*(-α)+(p.2:ℝ)*β-b| ≤ δ := by
    intro p hp
    obtain ⟨b,hb⟩ := hnear (-p.1,p.2) (Finset.mem_image_of_mem _ hp)
    refine ⟨b,?_⟩
    simpa only [Int.cast_neg,neg_mul,mul_neg] using hb
  obtain ⟨ha,_hb⟩ :=
    (HuxleyLinearForm.fareySector_bounded_density_dichotomy
      hw' hl' hB hδ hR' hnear').resolve_left (not_le.mpr hlarge)
  have hPtwo : (2:ℝ) ≤ P.card := (le_max_right _ _).trans hR'
  have hPpos : (0:ℝ) < P.card := lt_of_lt_of_le (by norm_num) hPtwo
  obtain ⟨p₀,hp₀⟩ := Finset.card_pos.mp
    (show 0 < P.card by exact_mod_cast hPpos)
  have hpdata := (HuxleyLinearForm.mem_fareySector_iff hw'
    (zero_le_one.trans hl')).mp hp₀
  have hN : 1 ≤ N := by omega
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hfactor : 16 ≤ 1536*B*(-l)*(N:ℝ) := by
    calc
      _ ≤ 1536*(1:ℝ)*1*1 := by norm_num
      _ ≤ _ := by gcongr
  have hscaled := mul_le_mul_of_nonneg_right hfactor
    (mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hδ)
  have hsmall : 8*(N:ℝ)*δ/(P.card:ℝ) < 1/2 := by
    apply (div_lt_iff₀ hPpos).mpr
    nlinarith only [hlarge,hscaled]
  have hhalf := abs_lt.mp (ha.trans_lt hsmall)
  have hround : round α= -round (-α) := by
    apply round_eq_iff.mpr
    simp only [Int.cast_neg,Set.mem_Ico]
    constructor <;> linarith only [hhalf.1,hhalf.2]
  have hlabels := fareySector_integer_labels_enlarged_rectangle
    hw' hl' hB hδ hR' hlarge hnear'
  intro p hp0 hpM hpt0 hptN b hb
  have hh := hlabels (-p.1,p.2)
    (by simpa only [Int.cast_neg] using hp0)
    (by simpa only [Int.cast_neg] using hpM) hpt0 hptN b
    (by simpa only [Int.cast_neg,neg_mul,mul_neg,neg_neg] using hb)
  change b=(-p.1)*round (-α)+p.2*round β at hh
  rw [hround]
  nlinarith only [hh]

#print axioms negative_fareySector_integer_labels_enlarged_rectangle

end HuxleyCloudPropagationScratch

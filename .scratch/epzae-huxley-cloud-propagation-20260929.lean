import TaoTrudgianYang2025.HuxleyLinearForms
import TaoTrudgianYang2025.ZetaSourceLogScales
import Mathlib.Analysis.Convex.Deriv

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
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_source_residual_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_source_residual_signed

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
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_source_bounds_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_source_bounds_signed

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
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_source_bounds_signed (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (dmin:=dmin) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv


#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_reference_source_bounds_signed

example
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
      U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coefficient_budgets_of_source_coordinate_cutoff_signed (C:=C) (J:=J) (μ:=μ) (N:=N) (R:=R) (r:=r) (s:=s) (d:=d) (l:=l) (w:=w) (Bcut:=Bcut) hC hJ hμ hN hR hr hd hl hlw hw hdlo hdhi hcoord hμupper hBcut hBsize hG

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coefficient_budgets_of_source_coordinate_cutoff_signed

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
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_determinant_signed S p x hS (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (K:=K) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hσ hδ hF hT hM hN hR hd hK hRM hscale hA hW hxref hpt hx hwindow hdisplacement hspan hsourcecube hr hdet hden hcoord hl hw hCcurv hBcut hBsize

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_determinant_signed

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
          (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_third_mass_signed S p x hS (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (K:=K) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hσ hδ hF hT hM hN hR hd hK hRM hscale hA hW hxref hpt hx hwindow hdisplacement hspan hsourcecube hr hdet hden hcoord hl hw hCcurv hBcut hBsize

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_third_mass_signed

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
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_family_long_block_signed S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_family_long_block_signed

example
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
      ∀ j∈E, α j∈finiteBoundaryCell Z l w k ∧ β j∈finiteBoundaryCell Z l w k :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_common_cell_selection_signed S Z x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (N:=N) (R:=R) (base:=base) (ε:=ε) (e:=e) (r:=r) (v:=v) (s:=s) (l:=l) (w:=w) (F:=F) hσ hδ hF hT hM hN hR hA hW hphase hsmall hε hdet hZ hx hwindow hregion

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_farey_common_cell_selection_signed

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
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_long_block_signed S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_long_block_signed

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
    (S.card:ℝ) ≤ 4944+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_family_count_signed S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_family_count_signed

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
    (S.card:ℝ) ≤ 4944+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_source_count_signed S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hl hw hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_selected_cell_source_count_signed

example
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
      b=p.1*round α+p.2*round β :=
  TaoTrudgianYang2025.HuxleyRationalPhase.negative_fareySector_integer_labels_enlarged_rectangle (N:=N) (l:=l) (w:=w) (B:=B) (α:=α) (β:=β) (δ:=δ) hw hl hB hδ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.negative_fareySector_integer_labels_enlarged_rectangle

example
    {e r v s : ℤ} {a : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1)
    (hlw : l < w) (hl : 0 < (r:ℝ)*l-e) (hw : 0 < (r:ℝ)*w-e)
    (hnl : (v:ℝ)-s*l < 0)
    (ha : (a:ℝ) ∈ Set.Icc l w)
    (hdyad : max ((r:ℝ)*l-e) ((r:ℝ)*w-e) ≤ 2*min ((r:ℝ)*l-e) ((r:ℝ)*w-e))
    (hcut : 256*(a.den:ℝ) ≤ Q) (hscale : 256 ≤ (w-l)*Q*a.den) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊Q*min ((r:ℝ)*l-e) ((r:ℝ)*w-e)⌋₊
    let P := HuxleyLinearForm.fareySector K (-β) (-α)
    let S := P.image (fun p : ℤ × ℤ => (-p.1,p.2))
    max ((β-α)*(K:ℝ)^2/128:ℝ) 2 ≤ S.card ∧
      ∀ p ∈ S,
        0 < (r:ℝ)*p.1+s*p.2 ∧ (r:ℝ)*p.1+s*p.2 ≤ Q ∧
        ((e:ℝ)*p.1+v*p.2)/((r:ℝ)*p.1+s*p.2) ∈ Set.Icc l w :=
  TaoTrudgianYang2025.HuxleyRationalPhase.completeNegativeSector_density_from_curvature (e:=e) (r:=r) (v:=v) (s:=s) (a:=a) (l:=l) (w:=w) (Q:=Q) hdet hlw hl hw hnl ha hdyad hcut hscale

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.completeNegativeSector_density_from_curvature

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
    (v:ℝ)-s*((rat 0:ℝ)-ε) < 0 →
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
    let S := (HuxleyLinearForm.fareySector K (-β) (-α)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
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
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_complete_negative_sector_fourth (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_complete_negative_sector_fourth

example
    {e r v s : ℤ} {anchor seed : ℚ} {l w Q : ℝ}
    (hdet : v*r-e*s=1)
    (hl : 0 < (r:ℝ)*l-e) (hw : 0 < (r:ℝ)*w-e)
    (hnl : (v:ℝ)-s*l < 0)
    (ha : (anchor:ℝ)∈Icc l w) (hseed : (seed:ℝ)∈Icc l w)
    (hdyad : max ((r:ℝ)*l-e) ((r:ℝ)*w-e) ≤ 2*min ((r:ℝ)*l-e) ((r:ℝ)*w-e))
    (hcut : 256*(anchor.den:ℝ) ≤ Q/3) (hseedQ : (seed.den:ℝ) ≤ Q) :
    let α := ((v:ℝ)-s*w)/((r:ℝ)*w-e)
    let β := ((v:ℝ)-s*l)/((r:ℝ)*l-e)
    let K := ⌊(Q/3)*min ((r:ℝ)*l-e) ((r:ℝ)*w-e)⌋₊
    let p : ℤ × ℤ := (v*seed.den-s*seed.num,r*seed.num-e*seed.den)
    0 < (p.2:ℝ) ∧ (p.1:ℝ)/p.2∈Icc α β ∧
      0 ≤ -(p.1:ℝ) ∧ -(p.1:ℝ) ≤ 12*((-α)*(K:ℝ)) ∧
      (p.2:ℝ) ≤ 12*(K:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_negative_original_seed_enlarged_rectangle (e:=e) (r:=r) (v:=v) (s:=s) (anchor:=anchor) (seed:=seed) (l:=l) (w:=w) (Q:=Q) hdet hl hw hnl ha hseed hdyad hcut hseedQ

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_negative_original_seed_enlarged_rectangle

example {N : ℕ} {l w : ℝ} {p : ℤ × ℤ}
    (hw : w < 0) (hlw : l ≤ w) :
    p ∈ (HuxleyLinearForm.fareySector N (-w) (-l)).image
      (fun q : ℤ × ℤ => (-q.1,q.2)) ↔
      1 ≤ p.2 ∧ p.2 ≤ N ∧ IsCoprime p.1 p.2 ∧
        l*(p.2:ℝ) ≤ p.1 ∧ (p.1:ℝ) ≤ w*p.2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.mem_negative_fareySector_iff (N:=N) (l:=l) (w:=w) (p:=p) hw hlw

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.mem_negative_fareySector_iff

example
    {K : ℕ} {l w B y₀ α β δ C : ℝ} {g : ℝ → ℝ} {H : ℤ × ℤ → ℤ} {p₀ : ℤ × ℤ} {H₀ : ℤ}
    (hl : l ≤ -1) (hw : w < 0) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hcard : max ((w-l)*(K:ℝ)^2/B) 2 ≤ (((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))).card)
    (htaylor : ∀ p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))),
      |g ((p.1:ℝ)/p.2)-g y₀-deriv g y₀*((p.1:ℝ)/p.2-y₀)| ≤
        C*|((p.1:ℝ)/p.2)-y₀|^2)
    (hnear : ∀ p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))),
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/p.2)-H p| ≤ δ) :
    let η := δ+(K:ℝ)*C*(w-l)^2
    1536*B*η*((-l)*(K:ℝ))*(K:ℝ) < (((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))).card →
    0 ≤ -(p₀.1:ℝ) → -(p₀.1:ℝ) ≤ 12*((-l)*(K:ℝ)) →
    0 < (p₀.2:ℝ) → (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    (p₀.1:ℝ)/p₀.2=y₀ →
    |(p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*g y₀-H₀| ≤ δ →
    H₀=p₀.1*round (α-deriv g y₀)+p₀.2*round (β-g y₀+y₀*deriv g y₀) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.negative_sector_seed_label_of_taylor_remainders (K:=K) (l:=l) (w:=w) (B:=B) (y₀:=y₀) (α:=α) (β:=β) (δ:=δ) (C:=C) (g:=g) (H:=H) (p₀:=p₀) (H₀:=H₀) hl hw hlw hB hy₀ hδ hC hcard htaylor hnear



#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.negative_sector_seed_label_of_taylor_remainders

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
    (hx₁ : ∀ p ∈ ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))), ∀ i,
      x₁ ((p.1:ℝ)/p.2) i ∈ Set.Ioo (1/2:ℝ) (W i-1/2))
    (hxseed : ∀ i, xseed i∈Set.Ioo (1/2:ℝ) (W i-1/2))
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hl : l ≤ -1) (hw : w < 0) (hlw : l ≤ w) (hBd : 1 ≤ Bd) (htseed : 0 < p₀.2)
    (hyseed : (p₀.1:ℝ)/p₀.2∈Set.Icc l w)
    (hden : ∀ y ∈ Set.Icc l w, ∀ i, dmin ≤ (r i:ℝ)*y+s i) :
    let S := ((HuxleyLinearForm.fareySector K (-w) (-l)).image
      (fun p : ℤ × ℤ => (-p.1,p.2)))
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
    1536*Bd*η*((-l)*(K:ℝ))*(K:ℝ) < S.card →
    -(p₀.1:ℝ) ≤ 12*((-l)*(K:ℝ)) →
    (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    |(zseed 0-cseed 0)-(zseed 1-cseed 1)| ≤ Δ →
    |q p₀ 0|+|q p₀ 1| ≤ Q →
    Hseed=p₀.1*round (α-deriv φ y₀)+p₀.2*round (β-φ y₀+y₀*deriv φ y₀) ∧
    |(α-round (α-deriv φ y₀))*y₀+
      (β-round (β-φ y₀+y₀*deriv φ y₀))-φ y₀| ≤ D/(p₀.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_negative_original_seed_linearization (K:=K) (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (B:=B) (dmin:=dmin) (l:=l) (w:=w) (Bd:=Bd) (Δ:=Δ) (Q:=Q) (p₀:=p₀) (k:=k) (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xseed:=xseed) (x₁:=x₁) (e:=e) (r:=r) (v:=v) (s:=s) (cnew:=cnew) (cseed:=cseed) hσ hδ hF hT hM hN hR hRM hNscale hscale hB hdmin hΔ hQ hA hW hx₀ hx₁ hxseed hr hdet hl hw hlw hBd htseed hyseed hden

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_negative_original_seed_linearization

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
    (v:ℝ)-s*((rat 0:ℝ)-ε) < 0 →
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
    let S := (HuxleyLinearForm.fareySector K (-β) (-α)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
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
    α ≤ -1 → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*((-α)*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤ D/(pseed.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_original_seed_residual (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_original_seed_residual

example
    (e r v s u t : ℤ) (Mat : Fin 4 → ℤ) (hdet : v*r-e*s=1) :
    e*(-s)-(-v)*r=1 ∧
    (-v)*(-t)+e*u=e*u+v*t ∧
    (-s)*(-t)+r*u=r*u+s*t ∧
    Mat 0*((-v)*(-t)+e*u)+Mat 1*((-s)*(-t)+r*u)=
      Mat 0*(e*u+v*t)+Mat 1*(r*u+s*t) ∧
    Mat 2*((-v)*(-t)+e*u)+Mat 3*((-s)*(-t)+r*u)=
      Mat 2*(e*u+v*t)+Mat 3*(r*u+s*t) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.farey_chart_quarter_turn_same_matrix e r v s u t Mat hdet

example
    {e r v s l w : ℝ} (hdet : v*r-e*s=1) (hlw : l ≤ w)
    (hdl : 0 < r*l-e)
    (hnl : 0 < v-s*l) (hnw : 0 < v-s*w)
    (hsmall : (v-s*l)/(r*l-e) < 1) :
    e*(-s)-(-v)*r=1 ∧
    0 < (-s)*l-(-v) ∧ 0 < (-s)*w-(-v) ∧
    (e-r*w)/((-s)*w-(-v)) ≤ (e-r*l)/((-s)*l-(-v)) ∧
    (e-r*l)/((-s)*l-(-v)) < -1 ∧
    (e-r*w)/((-s)*w-(-v)) = -1/((v-s*w)/(r*w-e)) ∧
    (e-r*l)/((-s)*l-(-v)) = -1/((v-s*l)/(r*l-e)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_quarter_turn_small_sector (e:=e) (r:=r) (v:=v) (s:=s) (l:=l) (w:=w) hdet hlw hdl hnl hnw hsmall

example
    {r s l w : ℝ} (hs : 0 ≤ s) (hl : 0 ≤ r*l) (hw : 0 ≤ r*w) :
    |r| * max |l| |w| ≤ max (r*l+s) (r*w+s) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.farey_chart_absolute_coordinate_height (r:=r) (s:=s) (l:=l) (w:=w) hs hl hw

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_chart_quarter_turn_same_matrix
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.inverseFarey_quarter_turn_small_sector
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.farey_chart_absolute_coordinate_height

example
    {C J μ N R r s d l w Bcut : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hlw : l ≤ w) (hsize : 1 ≤ max |l| |w|)
    (hdlo : d ≤ min (r*l+s) (r*w+s)) (hdhi : max (r*l+s) (r*w+s) ≤ 2*d)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l) ≤ 1/2 ∧
      U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coefficient_budgets_of_source_coordinate_cutoff_absolute (C:=C) (J:=J) (μ:=μ) (N:=N) (R:=R) (r:=r) (s:=s) (d:=d) (l:=l) (w:=w) (Bcut:=Bcut) hC hJ hμ hN hR hr hd hlw hsize hdlo hdhi hcoord hμupper hBcut hBsize hG

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.quartic_coefficient_budgets_of_source_coordinate_cutoff_absolute

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
    (hcoord : |r 0| * max |l| |w| ≤ 2*d) (hheight : 1 ≤ max |l| |w|)
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
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_determinant_absolute S p x hS (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (K:=K) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hσ hδ hF hT hM hN hR hd hK hRM hscale hA hW hxref hpt hx hwindow hdisplacement hspan hsourcecube hr hdet hden hcoord hheight hCcurv hBcut hBsize

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_determinant_absolute

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
    (hcoord : |r 0| * max |l| |w| ≤ 2*d) (hheight : 1 ≤ max |l| |w|)
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
          (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_third_mass_absolute S p x hS (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (K:=K) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hσ hδ hF hT hM hN hR hd hK hRM hscale hA hW hxref hpt hx hwindow hdisplacement hspan hsourcecube hr hdet hden hcoord hheight hCcurv hBcut hBsize

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_occupied_window_quartic_third_mass_absolute

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
    (v:ℝ)-s*((rat 0:ℝ)-ε) < 0 →
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
    let S := (HuxleyLinearForm.fareySector K (-β) (-α)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
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
    α ≤ -1 → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*((-α)*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_original_seed_source_residual (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_original_seed_source_residual

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
    (v:ℝ)-s*((rat 0:ℝ)-ε) < 0 →
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
    let S := (HuxleyLinearForm.fareySector K (-β) (-α)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
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
    α ≤ -1 → Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*((-α)*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_original_seed_source_bounds (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_original_seed_source_bounds

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
    (v:ℝ)-s*((rat 0:ℝ)-ε) < 0 →
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
    let S := (HuxleyLinearForm.fareySector K (-β) (-α)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
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
    α ≤ -1 → Δ < 1/2 →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    ∀ k : Fin 17, α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    1536*128*η*((-α)*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      (4*(37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ)/κ)*R^2/
        |(rp 0:ℝ)*minorArcCoordinate (μr 0) (rp 0) (sp 0) yseed| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_negative_reference_source_bounds (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (L:=L) (dmin:=dmin) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_constructed_negative_reference_source_bounds

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
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hheight : 1 ≤ max |l| |w|) (hBcut : 0 < Bcut)
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
    (∀ j∈S, (v:ℝ)-s*((rat j 0:ℝ)-ε) < 0) →
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
    let Saux := fun j => (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
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
    (∀ j∈S, α j ≤ -1) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 1536*128*η j*((-α j)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
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
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_selected_cell_long_block S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hheight hBcut hLref hrefWindow hwideL hwideU hrefNear

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_selected_cell_long_block

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
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hheight : 1 ≤ max |l| |w|) (hBcut : 0 < Bcut)
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
    (∀ j∈S, (v:ℝ)-s*((rat j 0:ℝ)-ε) < 0) →
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
    let Saux := fun j => (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
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
    (∀ j∈S, α j ≤ -1) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 1536*128*η j*((-α j)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
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
    (S.card:ℝ) ≤ 4944+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_selected_cell_family_count S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hheight hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_selected_cell_family_count

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
    (hchart : v*r-e*s=1) (hr : r ≠ 0)
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hheight : 1 ≤ max |l| |w|) (hBcut : 0 < Bcut)
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
    (∀ j∈S, (v:ℝ)-s*((rat j 0:ℝ)-ε) < 0) →
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
    let Saux := fun j => (HuxleyLinearForm.fareySector (Kaux j) (-β j) (-α j)).image
      (fun p : ℤ × ℤ => (-p.1,p.2))
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
    (∀ j∈S, α j ≤ -1) →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 1536*128*η j*((-α j)*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
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
    (S.card:ℝ) ≤ 4944+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_selected_cell_source_count S hS jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hheight hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_negative_selected_cell_source_count

example {N : ℕ} {l w : ℝ}
    (hw : 0 ≤ w) :
    ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤ w*(N:ℝ)^2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_card_le_rectangle_all_slopes (N:=N) (l:=l) (w:=w) hw

example
    {N : ℕ} {l w : ℝ} {m : ℤ}
    (hl : 0 < l) (hlw : l ≤ w) (hm : 0 ≤ m) :
    let T := (HuxleyLinearForm.fareySector N l w).filter (fun p => p.1=m)
    (T.card:ℝ) ≤ N ∧ (T.card:ℝ) ≤ (m:ℝ)/l-(m:ℝ)/w+1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_fiber_bounds (N:=N) (l:=l) (w:=w) (m:=m) hl hlw hm

example {N q : ℕ} {l w : ℝ}
    (hl : 0 < l) (hw : 0 ≤ w) (hR : 2 ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hdvd : ∀ p ∈ HuxleyLinearForm.fareySector N l w, q ∣ p.1.natAbs) : q=1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_common_divisor (N:=N) (q:=q) (l:=l) (w:=w) hl hw hR hdvd

example {N : ℕ} {l w B : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N) (hB : 1 ≤ B)
    (hR : w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hdensity : (w-l)*(N:ℝ)^2 ≤ B*(HuxleyLinearForm.fareySector N l w).card) :
    w*(N:ℝ) ≤ 3*B*((HuxleyLinearForm.fareySector N l w).image Prod.fst).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_card_lower (N:=N) (l:=l) (w:=w) (B:=B) hl hlw hN hB hR hdensity

example
    {N : ℕ} {l w : ℝ} {m : ℤ}
    (hl : 0 < l) (hlw : l ≤ w) (hmM : (m:ℝ) ≤ w*(N:ℝ)) :
    (((HuxleyLinearForm.fareySector N l w).filter (fun p => p.1=m)).card:ℝ) ≤
      (N:ℝ)-(m:ℝ)/w+1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_fiber_cutoff_bound (N:=N) (l:=l) (w:=w) (m:=m) hl hlw hmM

example {N : ℕ} {l w : ℝ}
    (hw : 0 ≤ w) :
    (((HuxleyLinearForm.fareySector N l w).image Prod.fst).card:ℝ) ≤ w*(N:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_projection_card_le (N:=N) (l:=l) (w:=w) hw

example {N : ℕ} {l w : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N)
    (hR : 40*w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card) :
    39 ≤ (w*(N:ℝ))*(1/l-1/w) ∧ 39 ≤ (N:ℝ)-1/w :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_large_numerator_width (N:=N) (l:=l) (w:=w) hl hlw hN hR

example {N : ℕ} {l w : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N)
    (hR : 40*w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card) :
    ∃ m n : ℤ, (m,n) ∈ HuxleyLinearForm.fareySector N l w ∧
      (m,n+1) ∈ HuxleyLinearForm.fareySector N l w :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_consecutive_denominators (N:=N) (l:=l) (w:=w) hl hlw hN hR

example {N : ℕ} {l w α β δ : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N)
    (hR : 40*w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card) (hδ : 0 ≤ δ)
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector N l w,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤ 96*δ*(w*(N:ℝ))*(N:ℝ) ∨
      |β-(round β:ℤ)| ≤ 8*(w*(N:ℝ))*δ/(HuxleyLinearForm.fareySector N l w).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_large_beta_bound (N:=N) (l:=l) (w:=w) (α:=α) (β:=β) (δ:=δ) hl hlw hN hR hδ hnear

example
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 0 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector N l μ).card)
    (hsmall : (max 1 μ*(N:ℝ))*δ ≤ 1/(96*B))
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    |α-(round α:ℤ)| ≤ 8*(N:ℝ)*δ/(HuxleyLinearForm.fareySector N l μ).card ∧
    |β-(round β:ℤ)| ≤ 8*(μ*(N:ℝ))*δ/(HuxleyLinearForm.fareySector N l μ).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_small_error_bounds_all_slopes (N:=N) (l:=l) (μ:=μ) (B:=B) (α:=α) (β:=β) (δ:=δ) hl hμ hB hδ hR hsmall hnear

example {N : ℕ} {l w B α β δ : ℝ}
    (hl : 0 < l) (hlw : l ≤ w) (hN : 0 < N) (hB : 1 ≤ B)
    (hR : w*(N:ℝ) ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hR2 : 2 ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hdensity : (w-l)*(N:ℝ)^2 ≤ B*(HuxleyLinearForm.fareySector N l w).card)
    (hδ : 0 ≤ δ)
    (hβ : |β-(round β:ℤ)| ≤ 8*(w*(N:ℝ))*δ/(HuxleyLinearForm.fareySector N l w).card)
    (hnear : ∀ p∈HuxleyLinearForm.fareySector N l w,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤ 324*B*δ*(w*(N:ℝ))*(N:ℝ) ∨
      |α-(round α:ℤ)| ≤ 27*B*(N:ℝ)*δ/(HuxleyLinearForm.fareySector N l w).card :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_alpha_of_beta_bound (N:=N) (l:=l) (w:=w) (B:=B) (α:=α) (β:=β) (δ:=δ) hl hlw hN hB hR hR2 hdensity hδ hβ hnear

example
    {N : ℕ} {l w B α β δ : ℝ}
    (hl : 0 < l) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((w-l)*(N:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector N l w).card)
    (hnear : ∀ p∈HuxleyLinearForm.fareySector N l w,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ((HuxleyLinearForm.fareySector N l w).card:ℝ) ≤ 3840*B*δ*(w*(N:ℝ))*(N:ℝ) ∨
      (|α-(round α:ℤ)| ≤ 27*B*(N:ℝ)*δ/(HuxleyLinearForm.fareySector N l w).card ∧
       |β-(round β:ℤ)| ≤ 20*B*(w*(N:ℝ))*δ/(HuxleyLinearForm.fareySector N l w).card) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_bounded_density_dichotomy_all_slopes (N:=N) (l:=l) (w:=w) (B:=B) (α:=α) (β:=β) (δ:=δ) hl hB hδ hR hnear

example
    {N : ℕ} {l μ B α β δ : ℝ}
    (hl : 0 < l) (hμ : 0 ≤ μ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hR : max ((μ-l)*(N:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector N l μ).card)
    (hlarge : 3840*B*δ*(μ*(N:ℝ))*(N:ℝ) < (HuxleyLinearForm.fareySector N l μ).card)
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector N l μ,
      ∃ b : ℤ, |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ) :
    ∀ p : ℤ × ℤ, 0 ≤ (p.1:ℝ) → (p.1:ℝ) ≤ 12*(μ*(N:ℝ)) →
      0 ≤ (p.2:ℝ) → (p.2:ℝ) ≤ 12*(N:ℝ) → ∀ b : ℤ,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-b| ≤ δ →
      b=p.1*(round α)+p.2*(round β) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_integer_labels_enlarged_rectangle_all_slopes (N:=N) (l:=l) (μ:=μ) (B:=B) (α:=α) (β:=β) (δ:=δ) hl hμ hB hδ hR hlarge hnear

example
    {K : ℕ} {l w B y₀ α β δ C : ℝ} {g : ℝ → ℝ} {H : ℤ × ℤ → ℤ} {p₀ : ℤ × ℤ} {H₀ : ℤ}
    (hl : 0 < l) (hw : 0 ≤ w) (hlw : l ≤ w) (hB : 1 ≤ B)
    (hy₀ : y₀ ∈ Set.Icc l w) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hcard : max ((w-l)*(K:ℝ)^2/B) 2 ≤ (HuxleyLinearForm.fareySector K l w).card)
    (htaylor : ∀ p ∈ HuxleyLinearForm.fareySector K l w,
      |g ((p.1:ℝ)/p.2)-g y₀-deriv g y₀*((p.1:ℝ)/p.2-y₀)| ≤
        C*|((p.1:ℝ)/p.2)-y₀|^2)
    (hnear : ∀ p ∈ HuxleyLinearForm.fareySector K l w,
      |(p.1:ℝ)*α+(p.2:ℝ)*β-(p.2:ℝ)*g ((p.1:ℝ)/p.2)-H p| ≤ δ) :
    let η := δ+(K:ℝ)*C*(w-l)^2
    3840*B*η*(w*(K:ℝ))*(K:ℝ) < (HuxleyLinearForm.fareySector K l w).card →
    0 ≤ (p₀.1:ℝ) → (p₀.1:ℝ) ≤ 12*(w*(K:ℝ)) →
    0 < (p₀.2:ℝ) → (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    (p₀.1:ℝ)/p₀.2=y₀ →
    |(p₀.1:ℝ)*α+(p₀.2:ℝ)*β-(p₀.2:ℝ)*g y₀-H₀| ≤ δ →
    H₀=p₀.1*round (α-deriv g y₀)+p₀.2*round (β-g y₀+y₀*deriv g y₀) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.sector_seed_label_of_taylor_remainders_all_slopes (K:=K) (l:=l) (w:=w) (B:=B) (y₀:=y₀) (α:=α) (β:=β) (δ:=δ) (C:=C) (g:=g) (H:=H) (p₀:=p₀) (H₀:=H₀) hl hw hlw hB hy₀ hδ hC hcard htaylor hnear

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
    (hl : 0 < l) (hw : 0 ≤ w) (hlw : l ≤ w) (hBd : 1 ≤ Bd) (htseed : 0 < p₀.2)
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
    3840*Bd*η*(w*(K:ℝ))*(K:ℝ) < S.card →
    (p₀.1:ℝ) ≤ 12*(w*(K:ℝ)) →
    (p₀.2:ℝ) ≤ 12*(K:ℝ) →
    |(zseed 0-cseed 0)-(zseed 1-cseed 1)| ≤ Δ →
    |q p₀ 0|+|q p₀ 1| ≤ Q →
    Hseed=p₀.1*round (α-deriv φ y₀)+p₀.2*round (β-φ y₀+y₀*deriv φ y₀) ∧
    |(α-round (α-deriv φ y₀))*y₀+
      (β-round (β-φ y₀+y₀*deriv φ y₀))-φ y₀| ≤ D/(p₀.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_original_seed_linearization_all_slopes (K:=K) (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (B:=B) (dmin:=dmin) (l:=l) (w:=w) (Bd:=Bd) (Δ:=Δ) (Q:=Q) (p₀:=p₀) (k:=k) (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xseed:=xseed) (x₁:=x₁) (e:=e) (r:=r) (v:=v) (s:=s) (cnew:=cnew) (cseed:=cseed) hσ hδ hF hT hM hN hR hRM hNscale hscale hB hdmin hΔ hQ hA hW hx₀ hx₁ hxseed hr hdet hl hw hlw hBd htseed hyseed hden

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
    Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    3840*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤ D/(pseed.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_residual_all_positive_slopes (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_card_le_rectangle_all_slopes
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_fiber_bounds
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_common_divisor
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_card_lower
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_fiber_cutoff_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_numerator_projection_card_le
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_large_numerator_width
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_consecutive_denominators
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_large_beta_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_small_error_bounds_all_slopes
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_alpha_of_beta_bound
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_bounded_density_dichotomy_all_slopes
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.fareySector_integer_labels_enlarged_rectangle_all_slopes
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.sector_seed_label_of_taylor_remainders_all_slopes
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_quartic_original_seed_linearization_all_slopes
#print axioms TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_residual_all_positive_slopes

/-- Source cutoff (5.10), together with the actual physical minor-arc
width, gives the first coefficient budget without a slope-height lower
bound. The source (6.6) weighted budget is a separate estimate. -/
theorem quartic_first_coefficient_budget_of_minor_arc_cutoff
    {C A J μ N R r s d l w Bcut : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hdlo : d ≤ r*l+s) (hdhi : r*l+s ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hwidth : w-l ≤ A*d^2/R^2)
    (hBcut : 0 < Bcut) (hBsize : 2*A*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ N^2/(Bcut*|r|)) :
    (C*R^4/(N*d^3))*(w-l) ≤ 1/2 := by
  let dl := r*l+s
  let r₀ := |r|
  have hr₀ : 0 < r₀ := abs_pos.mpr hr
  have hdl : 0 < dl := hd.trans_le hdlo
  have hG' : 1/(3*μ*r₀*dl) ≤ N^2/(Bcut*r₀) := by
    change |1/(3*μ*r*dl)| ≤ N^2/(Bcut*r₀) at hG
    simpa only [abs_div,abs_one,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3),
      abs_of_pos hμ,abs_of_pos hdl] using hG
  have hμmul : 6*μ*N*R^2 ≤ J := by
    have hh := (le_div_iff₀ (show 0 < 6*N*R^2 by positivity)).mp hμupper
    nlinarith only [hh]
  have hclear : Bcut ≤ 3*μ*N^2*dl := by
    have hh := (div_le_div_iff₀
      (show 0 < 3*μ*r₀*dl by positivity)
      (show 0 < Bcut*r₀ by positivity)).mp hG'
    apply (mul_le_mul_iff_left₀ hr₀).mp
    nlinarith only [hh]
  have hupper : Bcut*R^2 ≤ J*N*d := by
    have hh := mul_le_mul_of_nonneg_right hclear (sq_nonneg R)
    have hμhalf : 3*μ*N*R^2 ≤ J/2 := by nlinarith only [hμmul]
    have hm := mul_le_mul_of_nonneg_right hμhalf (show 0 ≤ N*dl by positivity)
    have hd' := mul_le_mul_of_nonneg_left hdhi (show 0 ≤ J*N/2 by positivity)
    change r*l+s ≤ 2*d at hdhi
    change dl ≤ 2*d at hdhi
    nlinarith only [hh,hm,hd']
  have hsmall : 2*A*C*R^2 ≤ N*d := by
    have hh := mul_le_mul_of_nonneg_right hBsize (sq_nonneg R)
    apply (mul_le_mul_iff_right₀ hJ).mp
    nlinarith only [hh,hupper]
  calc
    _ ≤ (C*R^4/(N*d^3))*(A*d^2/R^2) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = A*C*R^2/(N*d) := by field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ (show 0 < N*d by positivity)).mpr
      nlinarith only [hsmall]

#print axioms quartic_first_coefficient_budget_of_minor_arc_cutoff

/-- The inverse-Farey interval width is controlled by the original
physical interval and its actual endpoint denominators, with no lower
bound on the inverse slopes. -/
theorem inverseFarey_width_from_physical_interval
    {e r v s l w d : ℝ}
    (hdet : v*r-e*s=1) (hlw : l ≤ w)
    (hdl : 0 < r*l-e) (hdw : 0 < r*w-e) (hd : 0 < d)
    (hleft : r*((v-s*w)/(r*w-e))+s ≤ 2*d)
    (hright : r*((v-s*l)/(r*l-e))+s ≤ 2*d) :
    (v-s*l)/(r*l-e)-(v-s*w)/(r*w-e) ≤ 4*(w-l)*d^2 := by
  have hdlrec : r*((v-s*l)/(r*l-e))+s=1/(r*l-e) := by
    field_simp
    linear_combination hdet
  have hdwrec : r*((v-s*w)/(r*w-e))+s=1/(r*w-e) := by
    field_simp
    linear_combination hdet
  have hdlpos : 0 < r*((v-s*l)/(r*l-e))+s := by rw [hdlrec]; positivity
  have hdwpos : 0 < r*((v-s*w)/(r*w-e))+s := by rw [hdwrec]; positivity
  have hprod := mul_le_mul hleft hright hdlpos.le (by positivity : 0 ≤ 2*d)
  have he := inverseFarey_difference hdet hdl.ne' hdw.ne'
  have hid : (w-l)/((r*l-e)*(r*w-e)) =
      (w-l)*(r*((v-s*w)/(r*w-e))+s)*(r*((v-s*l)/(r*l-e))+s) := by
    rw [hdlrec,hdwrec]
    field_simp
  rw [he,hid]
  have hh := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hlw)
  nlinarith only [hh]

/-- The physical interval estimate normalized by its actual minor-arc
radius. This supplies the width premise of the (5.10) coefficient budget. -/
theorem inverseFarey_minor_arc_width_budget
    {e r v s a ε d R A : ℝ}
    (hdet : v*r-e*s=1) (hε : 0 ≤ ε) (hd : 0 < d) (hR : 0 < R)
    (hdl : 0 < r*(a-ε)-e) (hdw : 0 < r*(a+ε)-e)
    (hleft : r*((v-s*(a+ε))/(r*(a+ε)-e))+s ≤ 2*d)
    (hright : r*((v-s*(a-ε))/(r*(a-ε)-e))+s ≤ 2*d)
    (hradius : 8*ε*R^2 ≤ A) :
    (v-s*(a-ε))/(r*(a-ε)-e)-(v-s*(a+ε))/(r*(a+ε)-e) ≤ A*d^2/R^2 := by
  have hh := inverseFarey_width_from_physical_interval hdet
    (show a-ε ≤ a+ε by linarith only [hε]) hdl hdw hd hleft hright
  apply hh.trans
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  have hm := mul_le_mul_of_nonneg_right hradius (sq_nonneg d)
  nlinarith only [hm]

#print axioms inverseFarey_width_from_physical_interval
#print axioms inverseFarey_minor_arc_width_budget

example
    {C J μ N R r s d l w Bcut : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hlw : l ≤ w)
    (hdlo : d ≤ min (r*l+s) (r*w+s)) (hdhi : max (r*l+s) (r*w+s) ≤ 2*d)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_weighted_coefficient_budget_of_source_coordinate_cutoff (C:=C) (J:=J) (μ:=μ) (N:=N) (R:=R) (r:=r) (s:=s) (d:=d) (l:=l) (w:=w) (Bcut:=Bcut) hC hJ hμ hN hR hr hd hlw hdlo hdhi hcoord hμupper hBcut hBsize hG

#print axioms quartic_weighted_coefficient_budget_of_source_coordinate_cutoff

/-- The (5.10) cutoff at the source denominator scale implies the
reference-scale cutoff whenever the actual reference denominator is at
most the source scale. -/
theorem minorArcCoordinate_cutoff_of_reference_denominator_le
    {μ r s l N B Q : ℝ}
    (hr : r ≠ 0) (hB : 0 < B) (hrQ : |r| ≤ Q)
    (hG : |minorArcCoordinate μ r s l| ≤ N^2/(B*Q)) :
    |minorArcCoordinate μ r s l| ≤ N^2/(B*|r|) := by
  apply hG.trans
  exact div_le_div_of_nonneg_left (sq_nonneg N) (mul_pos hB (abs_pos.mpr hr))
    (mul_le_mul_of_nonneg_left hrQ hB.le)

/-- The two source cutoffs discharge both coefficient budgets for
small or large inverse slopes. The first uses the physical arc width;
the weighted second budget uses the source coordinate height. -/
theorem quartic_coefficient_budgets_of_physical_minor_arc_cutoffs
    {C A J μ N R r s d l w Bfive Bsix Q : ℝ}
    (hC : 0 ≤ C) (hJ : 0 < J) (hμ : 0 < μ)
    (hN : 0 < N) (hR : 0 < R) (hr : r ≠ 0) (hd : 0 < d)
    (hlw : l ≤ w)
    (hdlo : d ≤ min (r*l+s) (r*w+s)) (hdhi : max (r*l+s) (r*w+s) ≤ 2*d)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hwidth : w-l ≤ A*d^2/R^2)
    (hBfive : 0 < Bfive) (hBfiveSize : 2*A*C*J ≤ Bfive)
    (hBsix : 0 < Bsix) (hBsixSize : 5*C*J ≤ Bsix)
    (hrQ : |r| ≤ Q)
    (hGfive : |minorArcCoordinate μ r s l| ≤ N^2/(Bfive*Q))
    (hGsix : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bsix*R^2)) :
    let U := C*R^4/(N*d^3)
    U*(w-l) ≤ 1/2 ∧ U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2 := by
  refine ⟨?_,?_⟩
  · exact quartic_first_coefficient_budget_of_minor_arc_cutoff hC hJ hμ hN hR hr hd
      (hdlo.trans (min_le_left _ _)) ((le_max_left _ _).trans hdhi)
      hμupper hwidth hBfive hBfiveSize
      (minorArcCoordinate_cutoff_of_reference_denominator_le hr hBfive hrQ hGfive)
  · exact quartic_weighted_coefficient_budget_of_source_coordinate_cutoff hC hJ hμ
      hN hR hr hd hlw hdlo hdhi hcoord hμupper hBsix hBsixSize hGsix

#print axioms minorArcCoordinate_cutoff_of_reference_denominator_le
#print axioms quartic_coefficient_budgets_of_physical_minor_arc_cutoffs

example
    {f : ℝ → ℝ} {l w x y : ℝ}
    (hconv : ConvexOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : x∈Icc l w) (hy : y∈Icc l w) :
    l*|deriv f y-deriv f x| ≤
      |(y*deriv f y-f y)-(x*deriv f x-f x)| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.convex_weighted_derivative_difference (f:=f) (l:=l) (w:=w) (x:=x) (y:=y) hconv hder hx hy

example
    {f : ℝ → ℝ} {l w x y : ℝ}
    (hshape : ConvexOn ℝ (Icc l w) f ∨ ConcaveOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : x∈Icc l w) (hy : y∈Icc l w) :
    l*|deriv f y-deriv f x| ≤
      |(y*deriv f y-f y)-(x*deriv f x-f x)| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.curvature_branch_weighted_derivative_difference (f:=f) (l:=l) (w:=w) (x:=x) (y:=y) hshape hder hx hy

#print axioms convex_weighted_derivative_difference
#print axioms curvature_branch_weighted_derivative_difference

example
    {f : ℝ → ℝ} {l w x y ac bc D : ℝ} {b : ℤ}
    (hl : 0 < l) (hdyad : w ≤ 2*l) (hD : D ≤ 1/2)
    (hshape : ConvexOn ℝ (Icc l w) f ∨ ConcaveOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : x∈Icc l w) (hy : y∈Icc l w)
    (hresx : |(ac-round (ac-deriv f x))*x+bc-b-f x| ≤ D*x)
    (hresy : |(ac-round (ac-deriv f y))*y+bc-b-f y| ≤ D*y) :
    |round (ac-deriv f y)-round (ac-deriv f x)| ≤ (5:ℤ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fixed_integer_dyadic_first_coefficient_spread (f:=f) (l:=l) (w:=w) (x:=x) (y:=y) (ac:=ac) (bc:=bc) (D:=D) (b:=b) hl hdyad hD hshape hder hx hy hresx hresy

#print axioms fixed_integer_dyadic_first_coefficient_spread

example
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {f : ℝ → ℝ} {l w ac bc D : ℝ} {b : ℤ}
    (hl : 0 < l) (hdyad : w ≤ 2*l) (hD : D ≤ 1/2)
    (hshape : ConvexOn ℝ (Icc l w) f ∨ ConcaveOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : ∀ i∈S, x i∈Icc l w)
    (hres : ∀ i∈S, |(ac-round (ac-deriv f (x i)))*x i+bc-b-f (x i)| ≤ D*x i) :
    (S.image (fun i => round (ac-deriv f (x i)))).card ≤ 6 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.fixed_integer_dyadic_first_coefficient_count (ι:=ι) S x (f:=f) (l:=l) (w:=w) (ac:=ac) (bc:=bc) (D:=D) (b:=b) hl hdyad hD hshape hder hx hres

#print axioms fixed_integer_dyadic_first_coefficient_count

example
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {f : ℝ → ℝ} {l w ac bc D b₀ : ℝ}
    (hl : 0 < l) (hdyad : w ≤ 2*l) (hD : D ≤ 1/2)
    (hshape : ConvexOn ℝ (Icc l w) f ∨ ConcaveOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : ∀ i∈S, x i∈Icc l w)
    (hweighted : ∀ i∈S, |bc-f (x i)+x i*deriv f (x i)-b₀| ≤ 1/2)
    (hres : ∀ i∈S,
      |(ac-round (ac-deriv f (x i)))*x i+
        bc-round (bc-f (x i)+x i*deriv f (x i))-f (x i)| ≤ D*x i) :
    (S.image (fun i => (round (ac-deriv f (x i)),
      round (bc-f (x i)+x i*deriv f (x i))))).card ≤ 18 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.dyadic_curvature_branch_coefficient_pair_count (ι:=ι) S x (f:=f) (l:=l) (w:=w) (ac:=ac) (bc:=bc) (D:=D) (b₀:=b₀) hl hdyad hD hshape hder hx hweighted hres

#print axioms dyadic_curvature_branch_coefficient_pair_count

example
    {μ ν r s μ₁ ν₁ r₁ s₁ x : ℝ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hx : r*x+s ≠ 0) (hx₁ : r₁*x+s₁ ≠ 0) :
    let φ := fun z => rationalPhase μ r s μ₁ r₁ s₁ z-
      quarticPhase μ ν r s μ₁ ν₁ r₁ s₁ z
    DifferentiableAt ℝ φ x ∧ DifferentiableAt ℝ (deriv φ) x ∧
      (deriv^[2] φ) x =
        (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).eval x/
          ((r*x+s)^4*(r₁*x+s₁)^4) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_second_derivative_data (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (x:=x) hμ hμ₁ hr hr₁ hx hx₁

example
    {μ ν r s μ₁ ν₁ r₁ s₁ l w a b : ℝ} {k : ℕ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcell : Icc a b ⊆ finiteBoundaryCell
      (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).roots.toFinset l w k) :
    let φ := fun z => rationalPhase μ r s μ₁ r₁ s₁ z-
      quarticPhase μ ν r s μ₁ ν₁ r₁ s₁ z
    ConvexOn ℝ (Icc a b) φ ∨ ConcaveOn ℝ (Icc a b) φ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_shape_on_curvature_root_cell (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (l:=l) (w:=w) (a:=a) (b:=b) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ hcell

#print axioms quartic_phase_second_derivative_data
#print axioms quartic_phase_shape_on_curvature_root_cell

example
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {μ ν r s μ₁ ν₁ r₁ s₁ l w ac bc D b₀ : ℝ} {k : ℕ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hl : 0 < l) (hdyad : w ≤ 2*l) (hD : D ≤ 1/2) :
    let φ := fun z => rationalPhase μ r s μ₁ r₁ s₁ z-
      quarticPhase μ ν r s μ₁ ν₁ r₁ s₁ z
    let Z := (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).roots.toFinset
    (∀ i∈S, x i∈finiteBoundaryCell Z l w k) →
    (∀ i∈S, |bc-φ (x i)+x i*deriv φ (x i)-b₀| ≤ 1/2) →
    (∀ i∈S, |(ac-round (ac-deriv φ (x i)))*x i+
      bc-round (bc-φ (x i)+x i*deriv φ (x i))-φ (x i)| ≤ D*x i) →
    (S.image (fun i => (round (ac-deriv φ (x i)),
      round (bc-φ (x i)+x i*deriv φ (x i))))).card ≤ 18 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_dyadic_root_cell_coefficient_count (ι:=ι) S x (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (l:=l) (w:=w) (ac:=ac) (bc:=bc) (D:=D) (b₀:=b₀) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ hl hdyad hD

example
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ x bc : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    x∈finiteBoundaryCell Z l w k →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    |(bc-φ x+x*deriv φ x)-(bc-φ x₀+x₀*deriv φ x₀)| ≤ 1/2 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_weighted_coefficient_variation (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (x₀:=x₀) (x:=x) (bc:=bc) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ hheight

#print axioms quartic_phase_dyadic_root_cell_coefficient_count
#print axioms quartic_phase_weighted_coefficient_variation

example
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ ac bc D : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hl : 0 < l) (hdyad : w ≤ 2*l) (hD : D ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, x i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (x i)))*x i+
      bc-round (bc-φ (x i)+x i*deriv φ (x i))-φ (x i)| ≤ D*x i) →
    (S.image (fun i => (round (ac-deriv φ (x i)),
      round (bc-φ (x i)+x i*deriv φ (x i))))).card ≤ 113 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_dyadic_coefficient_color_count (ι:=ι) S x (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ hl hdyad hD hheight

#print axioms quartic_phase_dyadic_coefficient_color_count

example
    {ι : Type*} (S : Finset ι) (p : ι → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hl : 0 < l) (hdyad : w ≤ 2*l) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hp : ∀ i∈S, 0 < (p i).1 ∧ 0 < (p i).2) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤ 113 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_dyadic_source_cutoff_coefficient_count (ι:=ι) S p (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (k:=k) hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hl hdyad hD₀ hD hp

#print axioms quartic_phase_dyadic_source_cutoff_coefficient_count

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (hS : 3616 ≤ S.card)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hl : 0 < l) (hdyad : w ≤ 2*l) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hp : ∀ i∈S, 0 < (p i).1 ∧ 0 < (p i).2) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      ∀ i : Fin 7, (S.card:ℝ)/1808 ≤ (j i.succ:ℝ)-(j i.castSucc:ℝ)-1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_dyadic_source_common_coefficient_windows S p hS (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (k:=k) hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hl hdyad hD₀ hD hp

#print axioms quartic_phase_dyadic_source_common_coefficient_windows

example
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ ac bc D : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hl : 0 < l) (hD : D ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, x i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (x i)))*x i+
      bc-round (bc-φ (x i)+x i*deriv φ (x i))-φ (x i)| ≤ D*x i) →
    (S.image (fun i => (round (ac-deriv φ (x i)),
      round (bc-φ (x i)+x i*deriv φ (x i))))).card ≤ 5+108*(⌊Real.logb 2 (w/l)⌋₊+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_positive_interval_coefficient_color_count (ι:=ι) S x (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ hl hD hheight

#print axioms quartic_phase_positive_interval_coefficient_color_count

example
    {ι : Type*} (S : Finset ι) (p : ι → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hl : 0 < l) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hp : ∀ i∈S, 0 < (p i).1 ∧ 0 < (p i).2) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤ 5+108*(⌊Real.logb 2 (w/l)⌋₊+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_positive_interval_source_cutoff_coefficient_count (ι:=ι) S p (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (k:=k) hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hl hD₀ hD hp

#print axioms quartic_phase_positive_interval_source_cutoff_coefficient_count

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hl : 0 < l) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hS : 32*(5+108*(⌊Real.logb 2 (w/l)⌋₊+1)) ≤ S.card)
    (hp : ∀ i∈S, 0 < (p i).1 ∧ 0 < (p i).2) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      ∀ i : Fin 7, (S.card:ℝ)/(16*((5+108*(⌊Real.logb 2 (w/l)⌋₊+1):ℕ):ℝ)) ≤ (j i.succ:ℝ)-(j i.castSucc:ℝ)-1 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_positive_interval_source_common_coefficient_windows S p (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (k:=k) hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hl hD₀ hD hS hp

#print axioms quartic_phase_positive_interval_source_common_coefficient_windows

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → ℝ)
    {σ δ T M A W step base μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut D l w y₀ ac bc e v : ℝ}
    {F : ℝ → ℝ} {k : Fin 17}
    (hS : 32*(5+108*(⌊Real.logb 2 (w/l)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hdet : v*r-e*s=1)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hGcut : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hl : 0 < l) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hnum : ∀ i∈S, 0 < (p i).1)
    (hpt : ∀ i∈S, 0 < (p i).2)
    (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hwindow : ∀ i∈S, x i∈Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let U := C*R^4/(N*d^3)
    let Blabels := 5+108*(⌊Real.logb 2 (w/l)⌋₊+1)
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
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      StrictAnti (fun i => y (j i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤ x (j i.succ)-x (j i.castSucc)) ∧
      ∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/(16*(Blabels:ℝ))) ≤
        minorArcCoordinate μ r s (y (j i.succ))-
        minorArcCoordinate μ r s (y (j i.castSucc)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_positive_interval_common_coefficient_samples S p x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (step:=step) (base:=base) (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (D:=D) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (e:=e) (v:=v) (F:=F) (k:=k) hS hσ hδ hF hT hM hA hW hstep hμ hμ₁ hr hr₁ hdet hden hden₁ hC hJ hN hR hd hcoord hμupper hBcut hBsize hGcut hl hD₀ hD hnum hpt hx hwindow

#print axioms physicalModelPhase_positive_interval_common_coefficient_samples



example
    (p : ℤ × ℤ) {μ r s κ N R Q Cres D : ℝ}
    (hμ : 0 < μ) (hr : r ≠ 0) (hκ : 0 < κ) (hN : 0 < N)
    (hCres : 0 ≤ Cres) (hu : 0 < p.2)
    (hden : 0 < r*((p.1:ℝ)/p.2)+s)
    (hQband : Q ≤ 2*(r*(p.1:ℝ)+s*p.2))
    (hD : D ≤ Cres*Q/N)
    (hlower : κ/(2*N) ≤ 3*μ*R^2) :
    D/(p.2:ℝ) ≤ (4*Cres/κ)*R^2/
      |r*minorArcCoordinate μ r s ((p.1:ℝ)/p.2)| :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_integer_seed_residual_source_normalization p (μ:=μ) (r:=r) (s:=s) (κ:=κ) (N:=N) (R:=R) (Q:=Q) (Cres:=Cres) (D:=D) hμ hr hκ hN hCres hu hden hQband hD hlower

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ)
    {σ δ T M N R base d Cres Q D nSpan Ccurv Bcut l w y₀ ac bc : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hS : 32*(5+108*(⌊Real.logb 2 (w/l)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hCres : 0 ≤ Cres) (hRM : R ≤ M)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hnum : ∀ j∈S, 0 < (p j).1)
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hQband : ∀ j∈S, Q ≤ 2*(r 0*(p j).1+s 0*(p j).2))
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| * max |l| |w| ≤ 2*d) (hl : 0 < l)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : 5*Ccurv*(σ*(σ+1)+1) ≤ Bcut) :
    let U := Ccurv*R^4/(N*d^3)
    let Blabels := 5+108*(⌊Real.logb 2 (w/l)⌋₊+1)
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
    let K := 4*Cres/κ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(16*(Blabels:ℝ)*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      D/(p j).2) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    |r 0*s 1-s 0*r 1| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_positive_interval_quartic_determinant S p x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (Cres:=Cres) (Q:=Q) (D:=D) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hS hσ hδ hF hT hM hN hR hd hCres hRM hD₀ hD hDupper hscale hA hW hxref hnum hpt hQband hx hwindow hdisplacement hspan hsourcecube hr hdet hden hcoord hl hCcurv hBcut hBsize

#print axioms quartic_integer_seed_residual_source_normalization
#print axioms physicalModelPhase_positive_interval_quartic_determinant

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hl : 0 < l) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hS : 32*(5+108*(⌊Real.logb 2 (w/l)⌋₊+1)) ≤ S.card)
    (hp : ∀ i∈S, 0 < (p i).1 ∧ 0 < (p i).2) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      (∀ i : Fin 7, (S.card:ℝ)/(16*((5+108*(⌊Real.logb 2 (w/l)⌋₊+1):ℕ):ℝ)) ≤
        (j i.succ:ℝ)-(j i.castSucc:ℝ)-1) ∧
      ∀ i : Fin 7, (S.card:ℝ)/(16*((5+108*(⌊Real.logb 2 (w/l)⌋₊+1):ℕ):ℝ)) ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_positive_interval_source_common_coefficient_windows_with_mass S p (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (k:=k) hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hl hD₀ hD hS hp

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → ℝ)
    {σ δ T M A W step base μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut D l w y₀ ac bc e v : ℝ}
    {F : ℝ → ℝ} {k : Fin 17}
    (hS : 32*(5+108*(⌊Real.logb 2 (w/l)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hdet : v*r-e*s=1)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hGcut : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hl : 0 < l) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hnum : ∀ i∈S, 0 < (p i).1)
    (hpt : ∀ i∈S, 0 < (p i).2)
    (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hwindow : ∀ i∈S, x i∈Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let U := C*R^4/(N*d^3)
    let Blabels := 5+108*(⌊Real.logb 2 (w/l)⌋₊+1)
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
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      StrictAnti (fun i => y (j i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤ x (j i.succ)-x (j i.castSucc)) ∧
      (∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/(16*(Blabels:ℝ))) ≤
        minorArcCoordinate μ r s (y (j i.succ))-
        minorArcCoordinate μ r s (y (j i.castSucc))) ∧
      (∀ i : Fin 7, (S.card:ℝ)/(16*(Blabels:ℝ)) ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ)) ∧
      AntitoneOn y (S:Set ℕ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_positive_interval_common_coefficient_samples_with_mass S p x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (step:=step) (base:=base) (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (D:=D) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (e:=e) (v:=v) (F:=F) (k:=k) hS hσ hδ hF hT hM hA hW hstep hμ hμ₁ hr hr₁ hdet hden hden₁ hC hJ hN hR hd hcoord hμupper hBcut hBsize hGcut hl hD₀ hD hnum hpt hx hwindow

#print axioms quartic_phase_positive_interval_source_common_coefficient_windows_with_mass
#print axioms physicalModelPhase_positive_interval_common_coefficient_samples_with_mass

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ)
    {σ δ T M N R base d Cres Q D nSpan Ccurv Bcut l w y₀ ac bc : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hS : 32*(5+108*(⌊Real.logb 2 (w/l)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hCres : 0 ≤ Cres) (hRM : R ≤ M)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hnum : ∀ j∈S, 0 < (p j).1)
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hQband : ∀ j∈S, Q ≤ 2*(r 0*(p j).1+s 0*(p j).2))
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| * max |l| |w| ≤ 2*d) (hl : 0 < l)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : 5*Ccurv*(σ*(σ+1)+1) ≤ Bcut) :
    let U := Ccurv*R^4/(N*d^3)
    let Blabels := 5+108*(⌊Real.logb 2 (w/l)⌋₊+1)
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
    let K := 4*Cres/κ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(16*(Blabels:ℝ)*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      D/(p j).2) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    ∃ E : Finset ℕ, E ⊆ S ∧ (S.card:ℝ)/(16*(Blabels:ℝ)) ≤ (E.card:ℝ) ∧
      ∀ j∈E,
        |(iteratedDeriv 3 (f 1) (round (x j 1))/6)*(r 1*y j+s 1)^3/
          ((iteratedDeriv 3 (f 0) (round (x j 0))/6)*(r 0*y j+s 0)^3)-1| ≤
          (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_positive_interval_quartic_third_mass S p x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (Cres:=Cres) (Q:=Q) (D:=D) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hS hσ hδ hF hT hM hN hR hd hCres hRM hD₀ hD hDupper hscale hA hW hxref hnum hpt hQband hx hwindow hdisplacement hspan hsourcecube hr hdet hden hcoord hl hCcurv hBcut hBsize

#print axioms physicalModelPhase_positive_interval_quartic_third_mass

/- Exact-signature regression preflight for the long-block packet. -/


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
    Δ < 1/2 →
    (∀ i, rp i ≠ 0) →
    (∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=(ep i:ℝ)/rp i) →
    (∀ i, (H+|x₀ i-xref i|+1)^2 ≤ M*R) →
    (∀ y∈Icc α β, ∀ i, dmin ≤ (rp i:ℝ)*y+sp i) →
    α ∈ finiteBoundaryCell Z α β k → β ∈ finiteBoundaryCell Z α β k →
    3840*128*η*(β*(K:ℝ))*(K:ℝ) < S.card →
    |iteratedDeriv 2 g yseed-iteratedDeriv 2 hq yseed| ≤ U ∧
    |(ac-round (ac-deriv φ yseed))*yseed+
      (bc-round (bc-φ yseed+yseed*deriv φ yseed))-g yseed+hq yseed| ≤
      D/(pseed.2:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_original_seed_bounds_all_positive_slopes (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (dmin:=dmin) (k:=k) Q K₀ rat vinv parity Mat anchor e r v s (F:=F) (A:=A) (W:=W) (x₀:=x₀) (xref:=xref) hσ hδ hF hT hM hN hR hQ hscale hmesh hA hW hx₀ hden hinv

#print axioms physicalModelPhase_actual_fourier_original_seed_bounds_all_positive_slopes

example
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ} {k : Fin 17}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hS : 32*(5+108*(⌊Real.logb 2 (w/l)⌋₊+1)) ≤ S.card)
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hl : 0 < l) (hBcut : 0 < Bcut)
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
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    let Blabels := 5+108*(⌊Real.logb 2 (w/l)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    ∃ E : Finset ℕ, E ⊆ S ∧ (S.card:ℝ)/(16*(Blabels:ℝ)) ≤ (E.card:ℝ) ∧
      ∀ j∈E, |mu j 1*(q j 1:ℝ)^3/(mu j 0*(q j 0:ℝ)^3)-1| ≤
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_positive_interval_family_long_block S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hS hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hl hBcut hLref hrefWindow hwideL hwideU hrefNear

#print axioms physicalModelPhase_actual_fourier_positive_interval_family_long_block

example
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hS : 48+544*(5+108*(⌊Real.logb 2 (w/l)⌋₊+1)) ≤ S.card)
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hl : 0 < l) (hBcut : 0 < Bcut)
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
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Blabels := 5+108*(⌊Real.logb 2 (w/l)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    ∃ E : Finset ℕ, E ⊆ S₀ ∧ (S₀.card:ℝ)/(16*(Blabels:ℝ)) ≤ (E.card:ℝ) ∧
      ∀ j∈E, |mu j 1*(q j 1:ℝ)^3/(mu j 0*(q j 0:ℝ)^3)-1| ≤
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_positive_interval_selected_cell_long_block S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hS hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hl hBcut hLref hrefWindow hwideL hwideU hrefNear


#print axioms physicalModelPhase_actual_fourier_positive_interval_selected_cell_long_block

example
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
    (Q K₀ : ℕ) [NeZero K₀]
    (rat : ℕ → Fin 2 → ℚ) (vinv : ℕ → Fin 2 → ℤ)
    (parity : ℕ → Fin 2 → Fin 2) (anchor : ℕ → ℚ)
    (Mat : Fin 4 → ℤ) (e r v s : ℤ)
    {σ δ T M N R d nSpan base l w Bcut Lref : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : ℕ → Fin 2 → ℝ}
    (hS : 48+544*(5+108*(⌊Real.logb 2 (w/l)⌋₊+1)) ≤ S.card)
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hl : 0 < l) (hBcut : 0 < Bcut)
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
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Blabels := 5+108*(⌊Real.logb 2 (w/l)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Ccount := (512*(Blabels:ℝ)*Cphys/κ^2)*
      (Γ^2*(Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)+
        Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    (S.card:ℝ) ≤ 48+544*(Blabels:ℝ)+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_positive_interval_selected_cell_family_count S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hS hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hl hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge

#print axioms physicalModelPhase_actual_fourier_positive_interval_selected_cell_family_count



example
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ ac bc D a b : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (ha : 0 < a) (hband : ∀ i∈S, x i∈Icc a b) (hD : D ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, x i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (x i)))*x i+
      bc-round (bc-φ (x i)+x i*deriv φ (x i))-φ (x i)| ≤ D*x i) →
    (S.image (fun i => (round (ac-deriv φ (x i)),
      round (bc-φ (x i)+x i*deriv φ (x i))))).card ≤ 5+108*(⌊Real.logb 2 (b/a)⌋₊+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_positive_subfamily_coefficient_color_count (ι:=ι) S x (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (a:=a) (b:=b) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ ha hband hD hheight


example
    {ι : Type*} (S : Finset ι) (p : ι → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D P₁ P₂ : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hp : ∀ i∈S, 0 < (p i).1 ∧ 0 < (p i).2)
    (hheight : ∀ i∈S, ((p i).1:ℝ) ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤ 5+108*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_integer_height_source_cutoff_coefficient_count (ι:=ι) S p (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (P₁:=P₁) (P₂:=P₂) (k:=k) hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hP₂ hD₀ hD hp hheight


#print axioms quartic_phase_positive_subfamily_coefficient_color_count
#print axioms quartic_phase_integer_height_source_cutoff_coefficient_count

example
    (q : ℚ) (Q : ℕ) (e r v s : ℤ)
    {σ δ T M A W x : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ P δ)
    (hP : 1 ≤ P) (hT : 0 < T) (hM : 0 < M)
    (hA : M ≤ A) (hW : A+W ≤ 2*M) (hx : x∈Ioo 0 W)
    (hden : q.den ≤ Q)
    (hlevel : iteratedDeriv 2 (heathBrownPhysicalPhase F T M A 1) x/2=(q:ℝ)) :
    let V := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let p : ℤ × ℤ := (v*(q.den:ℤ)-s*q.num,r*q.num-e*(q.den:ℤ))
    |((p.1):ℝ)| ≤ (|(v:ℝ)|+|(s:ℝ)| *V)*(Q:ℝ) ∧
      |((p.2):ℝ)| ≤ (|(r:ℝ)| *V+|(e:ℝ)|)*(Q:ℝ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_original_seed_coordinate_heights q Q e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (x:=x) (P:=P) (F:=F) hσ hF hP hT hM hA hW hx hden hlevel

#print axioms physicalModelPhase_original_seed_coordinate_heights

example
    {ι : Type*} (S : Finset ι) (rat : ι → ℚ) (Q : ℕ) (e r v s : ℤ)
    {σ δ T M A W μ ν μ₁ ν₁ r₁ s₁ C J N R d Bcut l w y₀ ac bc D : ℝ}
    {P : ℕ} {F : ℝ → ℝ} {x : ι → ℝ} {k : Fin 17}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ P δ)
    (hP : 1 ≤ P) (hT : 0 < T) (hM : 0 < M)
    (hA : M ≤ A) (hW : A+W ≤ 2*M) (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hQ : ∀ i∈S, (rat i).den ≤ Q)
    (hlevel : ∀ i∈S,
      iteratedDeriv 2 (heathBrownPhysicalPhase F T M A 1) (x i)/2=(rat i:ℝ))
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ (r:ℝ)*z+s ∧ (r:ℝ)*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |(r:ℝ)| *N^2/(Bcut*R^2))
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) :
    let V := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *V)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *V+|(e:ℝ)|)*(Q:ℝ)
    let p : ι → ℤ × ℤ := fun i =>
      (v*((rat i).den:ℤ)-s*(rat i).num,r*(rat i).num-e*((rat i).den:ℤ))
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    (∀ i∈S, 0 < (p i).1 ∧ 0 < (p i).2) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤
      5+108*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_integer_height_source_coefficient_count (ι:=ι) S rat Q e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (μ:=μ) (ν:=ν) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (D:=D) (P:=P) (F:=F) (x:=x) (k:=k) hσ hF hP hT hM hA hW hx hQ hlevel hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hD₀ hD

#print axioms physicalModelPhase_integer_height_source_coefficient_count



example
    (S : Finset ℝ) {δ : ℝ} {m n u v : ℤ}
    (hδ : 0 < δ) (hn : 0 < n) (hv : 0 < v)
    (hm : (m:ℝ)/n∈S) (hu : (u:ℝ)/v∈S)
    (hdet : |m*v-u*n|=1)
    (hsep : ∀ x∈S, ∀ y∈S, x ≠ y → δ/4 < |x-y|) :
    (n:ℝ)*(v:ℝ) < 4/δ ∧ (n:ℝ) < 4/δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.separated_reference_parent_denominator_bound S (δ:=δ) (m:=m) (n:=n) (u:=u) (v:=v) hδ hn hv hm hu hdet hsep

example
    (S : Finset ℝ) {H : ℤ} {δ : ℝ}
    (hH : 1 ≤ H) (hδ : 0 < δ)
    (hseed : ∀ q : ℚ, (q.den:ℤ) ≤ H → (q:ℝ)∈Icc (0:ℝ) 1 → (q:ℝ)∈S)
    (hsep : ∀ x∈S, ∀ y∈S, x ≠ y → δ/4 < |x-y|) :
    (H:ℝ) < 4/δ :=
  TaoTrudgianYang2025.HuxleyRationalPhase.separated_unit_reference_order_bound S (H:=H) (δ:=δ) hH hδ hseed hsep

#print axioms separated_reference_parent_denominator_bound
#print axioms separated_unit_reference_order_bound

example {δ : ℝ}
    (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4/δ ∧ ∀ L U : ℤ, L ≤ U →
      ∃ T : Finset ℝ,
        (∀ q : ℚ, (q.den:ℤ) ≤ H →
          (q:ℝ) ∈ Icc (L:ℝ) ((U:ℝ)+1) → (q:ℝ) ∈ T) ∧
        (∀ z ∈ T, z ∈ Icc (L:ℝ) ((U:ℝ)+1)) ∧
        (∀ z ∈ T,
          (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
          (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
            1 ≤ δ*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧
            (u:ℝ)/v ∈ Icc (L:ℝ) ((U:ℝ)+1) ∧ |m*v-u*n|=1)) ∧
        (∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ/4 < |x-y|) ∧
        (∀ x ∈ Icc (L:ℝ) ((U:ℝ)+1), ∃ y ∈ T, |x-y| ≤ 7*δ/4) ∧
        (∀ x ∈ T, ∀ y ∈ T, x < y →
          (∀ z ∈ T, ¬ (x < z ∧ z < y)) →
          δ/4 < y-x ∧ y-x ≤ 7*δ/2 ∧
          ∃ a b c d : ℤ, x=(a:ℝ)/b ∧ y=(c:ℝ)/d ∧
            IsCoprime a b ∧ IsCoprime c d ∧ 0 < b ∧ 0 < d ∧
            1 ≤ δ*((max b d:ℤ):ℝ)^2) ∧
        ∀ z∈T, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
          (b:ℝ)<4/δ ∧ |(a:ℝ)| ≤ max |(L:ℝ)| |(U:ℝ)+1| *(4/δ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.exists_source_interval_reference_system_bounded (δ:=δ) hδ hδmax

#print axioms exists_source_interval_reference_system_bounded

example
    (F : ℝ → ℝ) {σ c J η T M N R U : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hUmax : U ≤ R^2) (hphase : T*N*R^2=M^3) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4*R^2/U ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/U ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/U)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ U*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → U/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*U/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        U/(4*R^2) < b-a ∧ b-a ≤ 7*U/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ U*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*U*N)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_constructed_reference_system_bounded F (σ:=σ) (c:=c) (J:=J) (η:=η) (T:=T) (M:=M) (N:=N) (R:=R) (U:=U) hσ hc hJ hη hηmax hf hbound htests hnegative hT hM hN hR hU hUmax hphase

#print axioms positive_difference_constructed_reference_system_bounded



example
    {f : ℝ → ℝ} {l w x y a ac bc D : ℝ} {b : ℤ}
    (ha : 0 < a) (hside : (a ≤ l ∧ w ≤ 2*a) ∨ (-2*a ≤ l ∧ w ≤ -a))
    (hD : D ≤ 1/2)
    (hshape : ConvexOn ℝ (Icc l w) f ∨ ConcaveOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : x∈Icc l w) (hy : y∈Icc l w)
    (hresx : |(ac-round (ac-deriv f x))*x+bc-b-f x| ≤ D*|x|)
    (hresy : |(ac-round (ac-deriv f y))*y+bc-b-f y| ≤ D*|y|) :
    |round (ac-deriv f y)-round (ac-deriv f x)| ≤ (5:ℤ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.signed_dyadic_first_coefficient_spread (f:=f) (l:=l) (w:=w) (x:=x) (y:=y) (a:=a) (ac:=ac) (bc:=bc) (D:=D) (b:=b) ha hside hD hshape hder hx hy hresx hresy

#print axioms signed_dyadic_first_coefficient_spread

example
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {f : ℝ → ℝ} {l w a₀ ac bc D b₀ : ℝ}
    (ha₀ : 0 < a₀)
    (hside : (a₀ ≤ l ∧ w ≤ 2*a₀) ∨ (-2*a₀ ≤ l ∧ w ≤ -a₀)) (hD : D ≤ 1/2)
    (hshape : ConvexOn ℝ (Icc l w) f ∨ ConcaveOn ℝ (Icc l w) f)
    (hder : ∀ z∈Icc l w, DifferentiableAt ℝ f z)
    (hx : ∀ i∈S, x i∈Icc l w)
    (hweighted : ∀ i∈S, |bc-f (x i)+x i*deriv f (x i)-b₀| ≤ 1/2)
    (hres : ∀ i∈S,
      |(ac-round (ac-deriv f (x i)))*x i+
        bc-round (bc-f (x i)+x i*deriv f (x i))-f (x i)| ≤ D*|x i|) :
    (S.image (fun i => (round (ac-deriv f (x i)),
      round (bc-f (x i)+x i*deriv f (x i))))).card ≤ 18 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.signed_dyadic_curvature_branch_coefficient_pair_count (ι:=ι) S x (f:=f) (l:=l) (w:=w) (a₀:=a₀) (ac:=ac) (bc:=bc) (D:=D) (b₀:=b₀) ha₀ hside hD hshape hder hx hweighted hres

#print axioms signed_dyadic_curvature_branch_coefficient_pair_count

example
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {μ ν r s μ₁ ν₁ r₁ s₁ l w a₀ ac bc D b₀ : ℝ} {k : ℕ}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (ha₀ : 0 < a₀)
    (hside : (a₀ ≤ l ∧ w ≤ 2*a₀) ∨ (-2*a₀ ≤ l ∧ w ≤ -a₀)) (hD : D ≤ 1/2) :
    let φ := fun z => rationalPhase μ r s μ₁ r₁ s₁ z-
      quarticPhase μ ν r s μ₁ ν₁ r₁ s₁ z
    let Z := (quarticCurvatureNumerator μ ν r s μ₁ ν₁ r₁ s₁).roots.toFinset
    (∀ i∈S, x i∈finiteBoundaryCell Z l w k) →
    (∀ i∈S, |bc-φ (x i)+x i*deriv φ (x i)-b₀| ≤ 1/2) →
    (∀ i∈S, |(ac-round (ac-deriv φ (x i)))*x i+
      bc-round (bc-φ (x i)+x i*deriv φ (x i))-φ (x i)| ≤ D*|x i|) →
    (S.image (fun i => (round (ac-deriv φ (x i)),
      round (bc-φ (x i)+x i*deriv φ (x i))))).card ≤ 18 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_signed_dyadic_root_cell_coefficient_count (ι:=ι) S x (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (l:=l) (w:=w) (a₀:=a₀) (ac:=ac) (bc:=bc) (D:=D) (b₀:=b₀) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ ha₀ hside hD

#print axioms quartic_phase_signed_dyadic_root_cell_coefficient_count

example
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {μ ν r s μ₁ ν₁ r₁ s₁ U l w x₀ ac bc D a b : ℝ} {k : Fin 17}
    (hμ : μ ≠ 0) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hden : ∀ z∈Icc l w, r*z+s ≠ 0)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (ha : 0 < a) (hband : ∀ i∈S, |x i|∈Icc a b) (hD : D ≤ 1/2)
    (hheight : U*(w-l)*(max |l| |w|+(w-l)/2) ≤ 1/2) :
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, x i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (x i)))*x i+
      bc-round (bc-φ (x i)+x i*deriv φ (x i))-φ (x i)| ≤ D*|x i|) →
    (S.image (fun i => (round (ac-deriv φ (x i)),
      round (bc-φ (x i)+x i*deriv φ (x i))))).card ≤ 5+216*(⌊Real.logb 2 (b/a)⌋₊+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_signed_subfamily_coefficient_color_count (ι:=ι) S x (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (U:=U) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (a:=a) (b:=b) (k:=k) hμ hμ₁ hr hr₁ hden hden₁ ha hband hD hheight

#print axioms quartic_phase_signed_subfamily_coefficient_color_count

example
    {ι : Type*} (S : Finset ι) (p : ι → ℤ × ℤ)
    {μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut l w x₀ ac bc D P₁ P₂ : ℝ} {k : Fin 17}
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hp : ∀ i∈S, 0 < (p i).2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂) :
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    x₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g x₀-iteratedDeriv 2 h x₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤ 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.quartic_phase_signed_integer_height_source_cutoff_coefficient_count (ι:=ι) S p (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (x₀:=x₀) (ac:=ac) (bc:=bc) (D:=D) (P₁:=P₁) (P₂:=P₂) (k:=k) hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hP₂ hD₀ hD hp hheight

#print axioms quartic_phase_signed_integer_height_source_cutoff_coefficient_count

example
    {ι : Type*} (S : Finset ι) (rat : ι → ℚ) (Q : ℕ) (e r v s : ℤ)
    {σ δ T M A W μ ν μ₁ ν₁ r₁ s₁ C J N R d Bcut l w y₀ ac bc D : ℝ}
    {P : ℕ} {F : ℝ → ℝ} {x : ι → ℝ} {k : Fin 17}
    (hσ : 0 ≤ σ) (hF : Expdb.IsApproximateModelPhaseFunction F σ P δ)
    (hP : 1 ≤ P) (hT : 0 < T) (hM : 0 < M)
    (hA : M ≤ A) (hW : A+W ≤ 2*M) (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hQ : ∀ i∈S, (rat i).den ≤ Q)
    (hlevel : ∀ i∈S,
      iteratedDeriv 2 (heathBrownPhysicalPhase F T M A 1) (x i)/2=(rat i:ℝ))
    (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0) (hr : r ≠ 0) (hr₁ : r₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hden : ∀ z∈Icc l w, d ≤ (r:ℝ)*z+s ∧ (r:ℝ)*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hG : |minorArcCoordinate μ r s l| ≤ |(r:ℝ)| *N^2/(Bcut*R^2))
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) :
    let V := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *V)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *V+|(e:ℝ)|)*(Q:ℝ)
    let p : ι → ℤ × ℤ := fun i =>
      (v*((rat i).den:ℤ)-s*(rat i).num,r*(rat i).num-e*((rat i).den:ℤ))
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    (∀ i∈S, 0 < (p i).2) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card ≤
      6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_signed_integer_height_source_coefficient_count (ι:=ι) S rat Q e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (μ:=μ) (ν:=ν) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (D:=D) (P:=P) (F:=F) (x:=x) (k:=k) hσ hF hP hT hM hA hW hx hQ hlevel hμ hμ₁ hr hr₁ hC hJ hN hR hd hden hden₁ hcoord hμupper hBcut hBsize hG hD₀ hD

#print axioms physicalModelPhase_signed_integer_height_source_coefficient_count

example
    {σ J Jv T M N R Q U V e r v s : ℝ}
    (hσ : 0 < σ) (hJ : 0 ≤ J) (hJv : 0 ≤ Jv)
    (hT : 0 < T) (hM : 0 < M) (hR : 1 ≤ R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hNM : N^2 ≤ M)
    (hU : 1 ≤ U) (hscale : T*N*R^2=M^3)
    (hV₀ : 0 ≤ V) (hV : V ≤ Jv*T/(2*M^2))
    (hr : |r| ≤ 4*R^2/U) (hs : |s| ≤ 4*R^2/U)
    (he : |e| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U))
    (hv : |v| ≤ (3*J*T/(2*σ*M^2)+1)*(4*R^2/U)) :
    let C := 1+4*(3*J/(2*σ)+1+Jv/2)
    1 ≤ T ∧ 1 ≤ C ∧
      1+(|v|+|s| *V)*Q ≤ C*T^3 ∧
      1+(|r| *V+|e|)*Q ≤ C*T^3 :=
  TaoTrudgianYang2025.HuxleyRationalPhase.source_reference_seed_height_polynomial (σ:=σ) (J:=J) (Jv:=Jv) (T:=T) (M:=M) (N:=N) (R:=R) (Q:=Q) (U:=U) (V:=V) (e:=e) (r:=r) (v:=v) (s:=s) hσ hJ hJv hT hM hR hRQ hQN hNM hU hscale hV₀ hV hr hs he hv

#print axioms source_reference_seed_height_polynomial

example
    {C ε : ℝ} (hC : 1 ≤ C) (m : ℕ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ P₁ P₂ : ℝ,
      1 ≤ P₁ → 1 ≤ P₂ → P₁ ≤ C*T^3 → P₂ ≤ C*T^3 →
      (((6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1):ℕ):ℝ)^m) ≤ T^ε :=
  TaoTrudgianYang2025.HuxleyRationalPhase.eventually_signed_height_coefficient_cost (C:=C) (ε:=ε) hC m hε

#print axioms eventually_signed_height_coefficient_cost

example
    {ι : Type*} {σ Jref ε : ℝ}
    (hσ : 0 < σ) (hJref : 0 ≤ Jref) (m : ℕ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀
    (S : Finset ι) (rat : ι → ℚ) (Q : ℕ) (e r v s : ℤ)
    {δ M A W μ ν μ₁ ν₁ r₁ s₁ C J N R d Bcut l w y₀ ac bc D : ℝ}
    {P : ℕ} {F : ℝ → ℝ} {x : ι → ℝ} {k : Fin 17}
    (_ : Expdb.IsApproximateModelPhaseFunction F σ P δ)
    (_ : 1 ≤ P) (_ : 0 < T) (_ : 0 < M)
    (_ : M ≤ A) (_ : A+W ≤ 2*M) (_ : ∀ i∈S, x i∈Ioo 0 W)
    (_ : ∀ i∈S, (rat i).den ≤ Q)
    (_ : ∀ i∈S,
      iteratedDeriv 2 (heathBrownPhysicalPhase F T M A 1) (x i)/2=(rat i:ℝ))
    (_ : 0 < μ) (_ : μ₁ ≠ 0) (_ : r ≠ 0) (_ : r₁ ≠ 0)
    (_ : 0 ≤ C) (_ : 0 < J) (_ : 0 < N) (_ : 1 ≤ R) (_ : 0 < d)
    (_ : ∀ z∈Icc l w, d ≤ (r:ℝ)*z+s ∧ (r:ℝ)*z+s ≤ 2*d)
    (_ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (_ : |(r:ℝ)| * max |l| |w| ≤ 2*d)
    (_ : μ ≤ J/(6*N*R^2))
    (_ : 0 < Bcut) (_ : 5*C*J ≤ Bcut)
    (_ : |minorArcCoordinate μ r s l| ≤ |(r:ℝ)| *N^2/(Bcut*R^2))
    (_ : 0 ≤ D) (_ : D ≤ 1/2)
    (_ : δ ≤ 1) {Uref : ℝ}
    (_ : R ≤ (Q:ℝ)) (_ : (Q:ℝ) ≤ N) (_ : N^2 ≤ M)
    (_ : 1 ≤ Uref) (_ : T*N*R^2=M^3)
    (_ : |(r:ℝ)| ≤ 4*R^2/Uref) (_ : |(s:ℝ)| ≤ 4*R^2/Uref)
    (_ : |(e:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/Uref))
    (_ : |(v:ℝ)| ≤ (3*Jref*T/(2*σ*M^2)+1)*(4*R^2/Uref)),
    let p : ι → ℤ × ℤ := fun i =>
      (v*((rat i).den:ℤ)-s*(rat i).num,r*(rat i).num-e*((rat i).den:ℤ))
    let U := C*R^4/(N*d^3)
    let g := rationalPhase μ r s μ₁ r₁ s₁
    let h := quarticPhase μ ν r s μ₁ ν₁ r₁ s₁
    let φ := fun z => g z-h z
    let y := fun i => ((p i).1:ℝ)/(p i).2
    let Z := quarticCurvatureBoundaryRoots μ ν r s μ₁ ν₁ r₁ s₁ U
    (∀ i∈S, 0 < (p i).2) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ i∈S, y i∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    (((S.image (fun i => (round (ac-deriv φ (y i)),
      round (bc-φ (y i)+y i*deriv φ (y i))))).card:ℝ)^m) ≤ T^ε :=
  TaoTrudgianYang2025.HuxleyRationalPhase.eventually_physicalModelPhase_bounded_reference_coefficient_count (ι:=ι) (σ:=σ) (Jref:=Jref) (ε:=ε) hσ hJref m hε

#print axioms eventually_physicalModelPhase_bounded_reference_coefficient_count

example
    (F : ℝ → ℝ) {σ c J η ε T M N R Q B : ℝ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (htests : ∀ w ∈ Icc (1/2:ℝ) 3, ∀ j,
      c ≤ |TaoTrudgianYang2025.HuxleyModel.tests
        (fun i : Fin 4 => iteratedDeriv (i.val+3) F w) j|)
    (hnegative : ∀ w ∈ Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hRQ : R ≤ Q) (hQN : Q ≤ N) (hNR : N ≤ R^2) (hNM : N^2 ≤ M)
    (hB : 1 ≤ B) (hBε : 5 < ε*B) (hlarge : 2*B ≤ (N/Q)^((2:ℝ)/3))
    (hphase : T*N*R^2=M^3) :
    let f := fun y w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let h := fun y w => iteratedDeriv 2 (f y) w/2
    let curvatureScale := 3*J*T/(2*σ*M^2)
    ∃ U : ℕ, 1 ≤ U ∧
      (N/Q)^((2:ℝ)/3)/(2*B) ≤ (U:ℝ) ∧
      (U:ℝ) ≤ (N/Q)^((2:ℝ)/3)/B ∧
      (U:ℝ) ≤ R^2 ∧ B*(U:ℝ)*Q ≤ N ∧ B^2*(U:ℝ)^3*R^2 ≤ N^2 ∧
      7*(U:ℝ)/(2*R^2)+Real.sqrt (U:ℝ)/R < ε*T/M^2 ∧
    ∃ H : ℤ, 2 ≤ H ∧ (H:ℝ)<4*R^2/(U:ℝ) ∧ ∃ S : Finset ℝ,
      (∀ q : ℚ, (q.den:ℤ) ≤ H → |(q:ℝ)| ≤ curvatureScale → (q:ℝ) ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ q : ℚ, (q.den:ℤ) ≤ H →
        (q:ℝ) ∈ Icc a b → (q:ℝ) ∈ S) ∧
      (∃ l ∈ S, ∃ u ∈ S, l ≤ -curvatureScale ∧ curvatureScale ≤ u) ∧
      (∀ z ∈ S, |z| ≤ curvatureScale+1) ∧
      (∀ z∈S, ∃ a b : ℤ, z=(a:ℝ)/b ∧ IsCoprime a b ∧ 0 < b ∧
        (b:ℝ)<4*R^2/(U:ℝ) ∧ |(a:ℝ)| ≤ (curvatureScale+1)*(4*R^2/(U:ℝ))) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), |h y x| ≤ curvatureScale) ∧
      (∀ z ∈ S,
        (∃ q : ℚ, z=(q:ℝ) ∧ (q.den:ℤ) ≤ H) ∨
        (∃ m n u v : ℤ, z=(m:ℝ)/n ∧ IsCoprime m n ∧ 0 < n ∧
          R^2 ≤ (U:ℝ)*(n:ℝ)^2 ∧ 0 < v ∧ v ≤ H ∧ (u:ℝ)/v ∈ S ∧ |m*v-u*n|=1)) ∧
      (∀ x ∈ S, ∀ z ∈ S, x ≠ z → (U:ℝ)/(4*R^2) < |x-z|) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M),
        ∃ q ∈ S, |h y x-q| ≤ 7*(U:ℝ)/(4*R^2)) ∧
      (∀ y ∈ Icc (1:ℝ) 2, ∀ q ∈ S,
        q ∈ Icc (h y M) (h y (2*M)) →
        ∃ x ∈ Icc M (2*M), h y x=q) ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b →
        (∀ z ∈ S, ¬ (a < z ∧ z < b)) →
        (U:ℝ)/(4*R^2) < b-a ∧ b-a ≤ 7*(U:ℝ)/(2*R^2) ∧
        (∃ m n u v : ℤ, a=(m:ℝ)/n ∧ b=(u:ℝ)/v ∧
          IsCoprime m n ∧ IsCoprime u v ∧ 0 < n ∧ 0 < v ∧
          R^2 ≤ (U:ℝ)*((max n v:ℤ):ℝ)^2) ∧
        (∀ y ∈ Icc (1:ℝ) 2, ∀ x ∈ Icc M (2*M), ∀ z ∈ Icc M (2*M),
          h y x=a → h y z=b → |z-x| ≤ (14*σ/c)*(U:ℝ)*N)) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.positive_difference_chosen_block_reference_system_bounded F (σ:=σ) (c:=c) (J:=J) (η:=η) (ε:=ε) (T:=T) (M:=M) (N:=N) (R:=R) (Q:=Q) (B:=B) hσ hc hJ hη hηmax hf hbound htests hnegative hT hM hN hR hRQ hQN hNR hNM hB hBε hlarge hphase

#print axioms positive_difference_chosen_block_reference_system_bounded



#print axioms physicalModelPhase_signed_height_common_coefficient_samples_with_mass

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → ℝ)
    {σ δ T M A W step base μ ν r s μ₁ ν₁ r₁ s₁ C J N R d Bcut D l w y₀ ac bc e v P₁ P₂ : ℝ}
    {F : ℝ → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : Expdb.IsApproximateModelPhaseFunction F σ 2 δ)
    (hT : 0 < T) (hM : 0 < M) (hA : M ≤ A) (hW : A+W ≤ 2*M)
    (hstep : 0 < step) (hμ : 0 < μ) (hμ₁ : μ₁ ≠ 0)
    (hr : r ≠ 0) (hr₁ : r₁ ≠ 0) (hdet : v*r-e*s=1)
    (hden : ∀ z∈Icc l w, d ≤ r*z+s ∧ r*z+s ≤ 2*d)
    (hden₁ : ∀ z∈Icc l w, r₁*z+s₁ ≠ 0)
    (hC : 0 ≤ C) (hJ : 0 < J) (hN : 0 < N) (hR : 0 < R) (hd : 0 < d)
    (hcoord : |r| * max |l| |w| ≤ 2*d)
    (hμupper : μ ≤ J/(6*N*R^2))
    (hBcut : 0 < Bcut) (hBsize : 5*C*J ≤ Bcut)
    (hGcut : |minorArcCoordinate μ r s l| ≤ |r| *N^2/(Bcut*R^2))
    (hP₂ : 0 < P₂) (hD₀ : 0 ≤ D) (hD : D ≤ 1/2)
    (hheight : ∀ i∈S, |((p i).1:ℝ)| ≤ P₁ ∧ ((p i).2:ℝ) ≤ P₂)
    (hpt : ∀ i∈S, 0 < (p i).2)
    (hx : ∀ i∈S, x i∈Ioo 0 W)
    (hwindow : ∀ i∈S, x i∈Icc (base+step*(i:ℝ)) (base+step*((i:ℝ)+1))) :
    let U := C*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
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
    (∀ i∈S, |(ac-round (ac-deriv φ (y i)))*y i+
      bc-round (bc-φ (y i)+y i*deriv φ (y i))-φ (y i)| ≤ D/(p i).2) →
    ∃ (a b : ℤ) (j : Fin 8 → ℕ), StrictMono j ∧
      (∀ i, j i∈S ∧ round (ac-deriv φ (y (j i)))=a ∧
        round (bc-φ (y (j i))+y (j i)*deriv φ (y (j i)))=b) ∧
      StrictAnti (fun i => y (j i)) ∧
      (∀ i : Fin 7, step*(S.card:ℝ)/(16*(Blabels:ℝ)) ≤ x (j i.succ)-x (j i.castSucc)) ∧
      (∀ i : Fin 7, modelPhaseThirdLower σ*T/(6*μ*M^3)*(step*(S.card:ℝ)/(16*(Blabels:ℝ))) ≤
        minorArcCoordinate μ r s (y (j i.succ))-
        minorArcCoordinate μ r s (y (j i.castSucc))) ∧
      (∀ i : Fin 7, (S.card:ℝ)/(16*(Blabels:ℝ)) ≤
        ((S.filter (fun n => j i.castSucc<n ∧ n<j i.succ)).card:ℝ)) ∧
      AntitoneOn y (S:Set ℕ) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_signed_height_common_coefficient_samples_with_mass S p x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (A:=A) (W:=W) (step:=step) (base:=base) (μ:=μ) (ν:=ν) (r:=r) (s:=s) (μ₁:=μ₁) (ν₁:=ν₁) (r₁:=r₁) (s₁:=s₁) (C:=C) (J:=J) (N:=N) (R:=R) (d:=d) (Bcut:=Bcut) (D:=D) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (e:=e) (v:=v) (P₁:=P₁) (P₂:=P₂) (F:=F) (k:=k) hS hσ hδ hF hT hM hA hW hstep hμ hμ₁ hr hr₁ hdet hden hden₁ hC hJ hN hR hd hcoord hμupper hBcut hBsize hGcut hP₂ hD₀ hD hheight hpt hx hwindow





#print axioms physicalModelPhase_signed_height_quartic_determinant
#print axioms physicalModelPhase_signed_height_quartic_third_mass

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ)
    {σ δ T M N R base d Cres Q D nSpan Ccurv Bcut l w y₀ ac bc P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hCres : 0 ≤ Cres) (hRM : R ≤ M)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ j∈S, |((p j).1:ℝ)| ≤ P₁ ∧ ((p j).2:ℝ) ≤ P₂)
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hQband : ∀ j∈S, Q ≤ 2*(r 0*(p j).1+s 0*(p j).2))
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| * max |l| |w| ≤ 2*d) (hP₂ : 0 < P₂)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : 5*Ccurv*(σ*(σ+1)+1) ≤ Bcut) :
    let U := Ccurv*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
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
    let K := 4*Cres/κ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(16*(Blabels:ℝ)*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      D/(p j).2) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    |r 0*s 1-s 0*r 1| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_signed_height_quartic_determinant S p x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (Cres:=Cres) (Q:=Q) (D:=D) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (P₁:=P₁) (P₂:=P₂) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hS hσ hδ hF hT hM hN hR hd hCres hRM hD₀ hD hDupper hscale hA hW hxref hheight hpt hQband hx hwindow hdisplacement hspan hsourcecube hr hdet hden hcoord hP₂ hCcurv hBcut hBsize

example
    (S : Finset ℕ) (p : ℕ → ℤ × ℤ) (x : ℕ → Fin 2 → ℝ)
    {σ δ T M N R base d Cres Q D nSpan Ccurv Bcut l w y₀ ac bc P₁ P₂ : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W xref e r v s H : Fin 2 → ℝ} {k : Fin 17}
    (hS : 32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T) (hM : 0 < M) (hN : 0 < N) (hR : 1 ≤ R)
    (hd : 0 < d) (hCres : 0 ≤ Cres) (hRM : R ≤ M)
    (hD₀ : 0 ≤ D) (hD : D ≤ 1/2) (hDupper : D ≤ Cres*Q/N)
    (hscale : T*N*R^2=M^3)
    (hA : ∀ i, M ≤ A i) (hW : ∀ i, A i+W i ≤ 2*M)
    (hxref : ∀ i, xref i∈Ioo (1/2:ℝ) (W i-1/2))
    (hheight : ∀ j∈S, |((p j).1:ℝ)| ≤ P₁ ∧ ((p j).2:ℝ) ≤ P₂)
    (hpt : ∀ j∈S, 0 < (p j).2)
    (hQband : ∀ j∈S, Q ≤ 2*(r 0*(p j).1+s 0*(p j).2))
    (hx : ∀ j∈S, ∀ i, x j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ j∈S, x j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hdisplacement : ∀ j∈S, ∀ i, |x j i-xref i| ≤ H i)
    (hspan : ∀ i, 2*H i+1 ≤ nSpan)
    (hsourcecube : nSpan^3 ≤ M*R^2)
    (hr : ∀ i, r i ≠ 0) (hdet : ∀ i, v i*r i-e i*s i=1)
    (hden : ∀ z∈Icc l w, ∀ i, d ≤ r i*z+s i ∧ r i*z+s i ≤ 2*d)
    (hcoord : |r 0| * max |l| |w| ≤ 2*d) (hP₂ : 0 < P₂)
    (hCcurv : 0 ≤ Ccurv) (hBcut : 0 < Bcut)
    (hBsize : 5*Ccurv*(σ*(σ+1)+1) ≤ Bcut) :
    let U := Ccurv*R^4/(N*d^3)
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
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
    let K := 4*Cres/κ
    let Γ := (σ*(σ+1)+1)/κ
    let L := κ/(16*(Blabels:ℝ)*(σ*(σ+1)+1))*(S.card:ℝ)
    |G l| ≤ |r 0| *N^2/(Bcut*R^2) →
    (∀ i, iteratedDeriv 2 (f i) (xref i)/2=e i/r i) →
    (∀ j∈S, ∀ i, iteratedDeriv 2 (f i) (x j i)/2=
      (e i*(p j).1+v i*(p j).2)/(r i*(p j).1+s i*(p j).2)) →
    y₀∈finiteBoundaryCell Z l w k →
    (∀ j∈S, y j∈finiteBoundaryCell Z l w k) →
    |iteratedDeriv 2 g y₀-iteratedDeriv 2 h y₀| ≤ U →
    (∀ j∈S, |(ac-round (ac-deriv φ (y j)))*y j+
      (bc-round (bc-φ (y j)+y j*deriv φ (y j)))-g (y j)+h (y j)| ≤
      D/(p j).2) →
    let C := Γ*(32*K+9*quarticReciprocalConstant σ δ)
    ∃ E : Finset ℕ, E ⊆ S ∧ (S.card:ℝ)/(16*(Blabels:ℝ)) ≤ (E.card:ℝ) ∧
      ∀ j∈E,
        |(iteratedDeriv 3 (f 1) (round (x j 1))/6)*(r 1*y j+s 1)^3/
          ((iteratedDeriv 3 (f 0) (round (x j 0))/6)*(r 0*y j+s 0)^3)-1| ≤
          (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_signed_height_quartic_third_mass S p x (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (d:=d) (Cres:=Cres) (Q:=Q) (D:=D) (nSpan:=nSpan) (Ccurv:=Ccurv) (Bcut:=Bcut) (l:=l) (w:=w) (y₀:=y₀) (ac:=ac) (bc:=bc) (P₁:=P₁) (P₂:=P₂) (F:=F) (A:=A) (W:=W) (xref:=xref) (e:=e) (r:=r) (v:=v) (s:=s) (H:=H) (k:=k) hS hσ hδ hF hT hM hN hR hd hCres hRM hD₀ hD hDupper hscale hA hW hxref hheight hpt hQband hx hwindow hdisplacement hspan hsourcecube hr hdet hden hcoord hP₂ hCcurv hBcut hBsize





#print axioms physicalModelPhase_actual_fourier_height_family_long_block

example
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    32*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, β j∈finiteBoundaryCell Z l w k) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    ∃ E : Finset ℕ, E ⊆ S ∧ (S.card:ℝ)/(16*(Blabels:ℝ)) ≤ (E.card:ℝ) ∧
      ∀ j∈E, |mu j 1*(q j 1:ℝ)^3/(mu j 0*(q j 0:ℝ)^3)-1| ≤
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_height_family_long_block S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (k:=k) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear





#print axioms physicalModelPhase_actual_fourier_height_selected_cell_long_block
#print axioms physicalModelPhase_actual_fourier_height_selected_cell_family_count

example
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    48+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    ∃ E : Finset ℕ, E ⊆ S₀ ∧ (S₀.card:ℝ)/(16*(Blabels:ℝ)) ≤ (E.card:ℝ) ∧
      ∀ j∈E, |mu j 1*(q j 1:ℝ)^3/(mu j 0*(q j 0:ℝ)^3)-1| ≤
        (Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^2/(L^2*N^2) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_height_selected_cell_long_block S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear

example
    (S : Finset ℕ) (jref : ℕ) (hjref : jref∈S)
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
    (hd : 0 < d) (hcoord : |(r:ℝ)| * max |l| |w| ≤ 2*d) (hBcut : 0 < Bcut)
    (hLref : 0 < Lref) (hrefWindow : modelPhaseThirdLower σ*Lref*R^2 ≤ 24*N^2)
    (hwideL : ∀ i, x jref i-Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ i, x jref i+Lref*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hrefNear : |(e:ℝ)/r-(rat jref 0:ℝ)| ≤ modelPhaseThirdLower σ*Lref/(16*R^2))
    (hc : Mat 2 ≠ 0)
    (hlarge : 32*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := 1+(|(v:ℝ)|+|(s:ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := 1+(|(r:ℝ)| *Vheight+|(e:ℝ)|)*(Q:ℝ)
    48+544*(6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)) ≤ S.card →
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
    D ≤ 1/2 → Δ < 1/2 →
    (∀ z∈Icc l w, ∀ i, d ≤ (rp i:ℝ)*z+sp i ∧ (rp i:ℝ)*z+sp i ≤ 2*d) →
    (∀ j∈S, α j∈Icc l w ∧ β j∈Icc l w) →
    (∀ j∈S, 3840*128*η j*(β j*(Kaux j:ℝ))*(Kaux j:ℝ) < (Saux j).card) →
    5*Ccurv*Cphys ≤ Bcut →
    |G l| ≤ |(rp 0:ℝ)| *N^2/(Bcut*R^2) →
    ∃ S₀ : Finset ℕ, S₀⊆S ∧ S.card ≤ 48+17*S₀.card ∧
    let Blabels := 6+216*(⌊Real.logb 2 (P₁*P₂)⌋₊+1)
    let Γ := Cphys/κ
    let L := κ/(16*(Blabels:ℝ)*Cphys)*(S₀.card:ℝ)
    let C := Γ*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Ccount := (512*(Blabels:ℝ)*Cphys/κ^2)*
      (Γ^2*(Γ^2*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)+
        Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)
    (|(Mat 2:ℝ)| ≤ (64*Γ/(3*κ))*
      ((1+Γ^2)*C+2*Γ*(modelPhaseJetCoefficient σ 3+δ)/κ)*R^4/(L^3*N^2)) ∧
    (S.card:ℝ) ≤ 48+544*(Blabels:ℝ)+17*Ccount*R^4/(L^2*N^2*|(Mat 2:ℝ)|) :=
  TaoTrudgianYang2025.HuxleyRationalPhase.physicalModelPhase_actual_fourier_height_selected_cell_family_count S jref hjref Q K₀ rat vinv parity anchor Mat e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (d:=d) (nSpan:=nSpan) (base:=base) (l:=l) (w:=w) (Bcut:=Bcut) (Lref:=Lref) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hsourcecube hden hinv hchart hr hd hcoord hBcut hLref hrefWindow hwideL hwideU hrefNear hc hlarge

end HuxleyCloudPropagationScratch

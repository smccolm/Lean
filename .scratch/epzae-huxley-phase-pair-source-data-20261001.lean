import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyPhasePairSourceDataScratch

private theorem actual_phase_pair_source_data
    (phase : ℝ → ℝ → ℝ) (z : (ℝ × ℤ) → ℝ)
    (rat : (ℝ × ℤ) → ℚ) (vinv : (ℝ × ℤ) → ℤ) (K₀ : ℕ)
    (ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))
    (ya yb : ℝ) (hphase : ij.1.1.1=ya ∧ ij.2.1.1=yb) :
    let yp : Fin 2 → ℝ := ![ya,yb]
    let ip : Fin 2 → (ℝ × ℤ) × Fin 2 := ![ij.1,ij.2]
    let fp := fun i => phase (yp i)
    let xp : Fin 2 → ℝ := ![z (ya,ij.1.1.2),z (yb,ij.2.1.2)]
    let q := fun j => (rat j).den
    let mu := fun j => iteratedDeriv 3 (phase j.1) (round (z j))/6
    let ell := fun j => deriv (phase j.1) (round (z j))
    let qell := fun j => (q j:ℝ)*ell j
    let b := fun jp : (ℝ × ℤ) × Fin 2 => (⌊qell jp.1⌋+(jp.2:ℕ) : ℤ)
    let offset := fun jp => b jp-round (qell jp.1)
    let tau := fun jp => ((b jp:ℝ)-qell jp.1)/2
    let dual := fun j => -2*mu j*(Real.sqrt (2/(3*mu j*(q j:ℝ))))^3
    let cloud := fun jp => (![Int.fract (-(vinv jp.1:ℝ)*b jp/q jp.1),
      Int.fract (-(vinv jp.1:ℝ)/q jp.1),dual jp.1/Real.sqrt K₀,
      (3*dual jp.1*tau jp/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let qPair := fun i => q (ip i).1
    let muPair := fun i => iteratedDeriv 3 (fp i) (round (xp i))/6
    let ellPair := fun i => deriv (fp i) (round (xp i))
    let qellPair := fun i => (qPair i:ℝ)*ellPair i
    let bPair := fun i => (⌊qellPair i⌋+((ip i).2:ℕ) : ℤ)
    let tauPair := fun i => ((bPair i:ℝ)-qellPair i)/2
    let dualPair := fun i => -2*muPair i*(Real.sqrt (2/(3*muPair i*(qPair i:ℝ))))^3
    let cloudPair := fun i => (![Int.fract (-(vinv (ip i).1:ℝ)*bPair i/qPair i),
      Int.fract (-(vinv (ip i).1:ℝ)/qPair i),dualPair i/Real.sqrt K₀,
      (3*dualPair i*tauPair i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    ∀ i,
      fp i=phase (ip i).1.1 ∧ xp i=z (ip i).1 ∧
      (∀ n, iteratedDeriv n (fp i) (xp i)=
        iteratedDeriv n (phase (ip i).1.1) (z (ip i).1)) ∧
      (∀ n, iteratedDeriv n (fp i) (round (xp i))=
        iteratedDeriv n (phase (ip i).1.1) (round (z (ip i).1))) ∧
      deriv (fp i) (round (xp i))=
        deriv (phase (ip i).1.1) (round (z (ip i).1)) ∧
      bPair i-round (qellPair i) = offset (ip i) ∧
      cloudPair i=cloud (ip i) := by
  intro yp ip fp xp q mu ell qell b offset tau dual cloud
    qPair muPair ellPair qellPair bPair tauPair dualPair cloudPair i
  rcases ij with ⟨⟨⟨a,n⟩,pa⟩,⟨⟨b,m⟩,pb⟩⟩
  dsimp only at hphase
  rcases hphase with ⟨rfl,rfl⟩
  fin_cases i <;> exact ⟨rfl,rfl,fun _ => rfl,fun _ => rfl,rfl,rfl,rfl⟩


example
    (phase : ℝ → ℝ → ℝ) (z : (ℝ × ℤ) → ℝ)
    (rat : (ℝ × ℤ) → ℚ) (vinv : (ℝ × ℤ) → ℤ) (K₀ : ℕ)
    (ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))
    (ya yb : ℝ) (hphase : ij.1.1.1=ya ∧ ij.2.1.1=yb) :
    let yp : Fin 2 → ℝ := ![ya,yb]
    let ip : Fin 2 → (ℝ × ℤ) × Fin 2 := ![ij.1,ij.2]
    let fp := fun i => phase (yp i)
    let xp : Fin 2 → ℝ := ![z (ya,ij.1.1.2),z (yb,ij.2.1.2)]
    let q := fun j => (rat j).den
    let mu := fun j => iteratedDeriv 3 (phase j.1) (round (z j))/6
    let ell := fun j => deriv (phase j.1) (round (z j))
    let qell := fun j => (q j:ℝ)*ell j
    let b := fun jp : (ℝ × ℤ) × Fin 2 => (⌊qell jp.1⌋+(jp.2:ℕ) : ℤ)
    let offset := fun jp => b jp-round (qell jp.1)
    let tau := fun jp => ((b jp:ℝ)-qell jp.1)/2
    let dual := fun j => -2*mu j*(Real.sqrt (2/(3*mu j*(q j:ℝ))))^3
    let cloud := fun jp => (![Int.fract (-(vinv jp.1:ℝ)*b jp/q jp.1),
      Int.fract (-(vinv jp.1:ℝ)/q jp.1),dual jp.1/Real.sqrt K₀,
      (3*dual jp.1*tau jp/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let qPair := fun i => q (ip i).1
    let muPair := fun i => iteratedDeriv 3 (fp i) (round (xp i))/6
    let ellPair := fun i => deriv (fp i) (round (xp i))
    let qellPair := fun i => (qPair i:ℝ)*ellPair i
    let bPair := fun i => (⌊qellPair i⌋+((ip i).2:ℕ) : ℤ)
    let tauPair := fun i => ((bPair i:ℝ)-qellPair i)/2
    let dualPair := fun i => -2*muPair i*(Real.sqrt (2/(3*muPair i*(qPair i:ℝ))))^3
    let cloudPair := fun i => (![Int.fract (-(vinv (ip i).1:ℝ)*bPair i/qPair i),
      Int.fract (-(vinv (ip i).1:ℝ)/qPair i),dualPair i/Real.sqrt K₀,
      (3*dualPair i*tauPair i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    ∀ i,
      fp i=phase (ip i).1.1 ∧ xp i=z (ip i).1 ∧
      (∀ n, iteratedDeriv n (fp i) (xp i)=
        iteratedDeriv n (phase (ip i).1.1) (z (ip i).1)) ∧
      (∀ n, iteratedDeriv n (fp i) (round (xp i))=
        iteratedDeriv n (phase (ip i).1.1) (round (z (ip i).1))) ∧
      deriv (fp i) (round (xp i))=
        deriv (phase (ip i).1.1) (round (z (ip i).1)) ∧
      bPair i-round (qellPair i) = offset (ip i) ∧
      cloudPair i=cloud (ip i) :=
  HuxleyPhasePairSourceDataScratch.actual_phase_pair_source_data phase z rat vinv K₀ ij ya yb hphase


#print axioms actual_phase_pair_source_data

end HuxleyPhasePairSourceDataScratch

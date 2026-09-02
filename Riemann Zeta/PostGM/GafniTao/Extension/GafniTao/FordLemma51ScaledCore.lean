import GafniTao.FordWScaleBound
import GafniTao.FordUniversalCoefficientGrowth

/-!
# Ford Lemma 5.1 at the complete-window scales

This file inserts the quantitative `s=r=2k²` Vinogradov estimate twice and
the central-band `W_j` product estimate into Ford's literal source core.
-/

namespace GafniTao

noncomputable section

def fordDoubleSquareDegree (k : ℕ) : ℕ := 2 * k ^ 2

def fordDoubleSquareDelta (k : ℕ) : ℝ :=
  (3 / 8 : ℝ) * (k : ℝ) ^ 2 *
    Real.exp (1 / 2 - 4 + 17 / (10 * (k : ℝ)))

def fordDoubleSquareCoefficient (k : ℕ) : ℝ :=
  fordMomentCoefficient36 k (2 * k - 1)

/-- The exact unsimplified majorant obtained by inserting the two moment
bounds and the complete-window `W_j` estimate into the source core. -/
def fordScaledSourceCoreMajorant (k N : ℕ) : ℝ :=
  let s := fordDoubleSquareDegree k
  let M₁ : ℝ := (N : ℝ) ^ (1 / 5 : ℝ)
  let M₂ : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  let M : ℕ := ⌊M₁⌋₊
  let Q : ℕ := ⌊M₂⌋₊
  let C : ℝ := fordDoubleSquareCoefficient k
  let delta : ℝ := fordDoubleSquareDelta k
  (5 * (s : ℝ)) ^ k * M₂ ^ (-(2 * s : ℝ)) *
    (M : ℝ) ^ (-(2 * s : ℝ) + fordVinogradovKappa k) *
    (C * (M : ℝ) ^ fordLambda34 s k delta) *
    (C * (Q : ℝ) ^ fordLambda34 s k delta) *
    ((2 * (s : ℝ)) ^ k * M₂ ^ fordVinogradovKappa k *
      (fordWGoodEnvelope k N) ^ (fordGoodDegreeSet k).card)

theorem fordLemma51SourceCore_scaled_le
    {k N : ℕ} {t : ℝ} (hk : 1000 ≤ k)
    (hN : 1024 ≤ N) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    fordLemma51SourceCore k 1 k
        (fordDoubleSquareDegree k) (fordDoubleSquareDegree k)
        ((N : ℝ) ^ (1 / 5 : ℝ)) ((N : ℝ) ^ (1 / 10 : ℝ)) N
        (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) t ≤
      fordScaledSourceCoreMajorant k N := by
  let s := fordDoubleSquareDegree k
  let M₁ : ℝ := (N : ℝ) ^ (1 / 5 : ℝ)
  let M₂ : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  let M : ℕ := ⌊M₁⌋₊
  let Q : ℕ := ⌊M₂⌋₊
  let C : ℝ := fordDoubleSquareCoefficient k
  let delta : ℝ := fordDoubleSquareDelta k
  have hk1000 : 1000 ≤ k := hk
  have hk6 : 6 ≤ k := by omega
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNgt : 1 < N := by omega
  obtain ⟨_hM₁two, _hM₂two, hMhalf, hMone, hQone,
      _hM₁top, _hM₂top, _hprodTop⟩ :=
    ford_basic_scale_data (x := (N : ℝ)) (by exact_mod_cast hN)
  obtain ⟨htBottom, htTop⟩ :=
    ford_lambda_band_t_bounds hNgt ht hlower hupper
  have hrsOne : 1 ≤ s := by
    dsimp [s, fordDoubleSquareDegree]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hrsPos : 0 < s := by omega
  have hmoment := ford_double_square_moment_bound_universal hk
  have hmoment' : FordVinogradovMomentBound s k C delta := by
    simpa [s, C, delta, fordDoubleSquareDegree, fordDoubleSquareCoefficient,
      fordDoubleSquareDelta] using hmoment
  have hC : 0 ≤ C := by
    dsimp [C, fordDoubleSquareCoefficient]
    exact fordMomentCoefficient36_nonneg _ _
  have hMone' : 1 ≤ M := by
    dsimp [M, M₁]
    exact hMone
  have hQone' : 1 ≤ Q := by
    dsimp [Q, M₂]
    exact hQone
  have hgood : ∀ j ∈ fordGoodDegreeSet k,
      fordWNormalizedFactor s M₂ s M N t j ≤ fordWGoodEnvelope k N := by
    intro j hj
    exact fordWNormalizedFactor_good_le hk6 hx ht htBottom htTop
      (by simpa [M, M₁] using hMhalf) hrsOne hrsOne hj
  have hcore := fordLemma51SourceCore_full_le
    (k := k) (r := s) (s := s) (M := M) (Q := Q) (N := N)
    (M₁ := M₁) (M₂ := M₂) (t := t) (C := C) (delta := delta)
    (q := fordWGoodEnvelope k N) rfl (by dsimp [M₂]; positivity)
    hrsPos hrsPos hMone' hQone'
    (by positivity) ht hC hmoment' hmoment' hgood
  simpa [fordScaledSourceCoreMajorant, s, M₁, M₂, M, Q, C, delta] using hcore

#print axioms fordLemma51SourceCore_scaled_le

end

end GafniTao

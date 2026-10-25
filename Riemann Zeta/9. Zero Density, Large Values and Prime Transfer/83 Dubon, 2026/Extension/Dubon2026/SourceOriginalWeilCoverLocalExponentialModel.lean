import Dubon2026.SourceOriginalWeilCoverLogarithmicReading

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> global meromorphic exponential. Reuse the native logarithmic-model and finite-puncture arguments with proved cover geometry and actual residue values. The global period correction remains open. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)

theorem exists_cover_local_exponential_model (v : Place ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : -1 ≤ v.ordDifferential η) (m : ℤ)
    (hm : v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (m : ℂ)) :
    ∃ r : ℝ, 0 < r ∧ r < placeRadius N n radicand A hRadicand hOrders v ∧ ∃ M : ℂ → ℂ,
      MeromorphicAt M 0 ∧ meromorphicOrderAt M 0 = (m : WithTop ℤ) ∧
        ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 →
          M z ≠ 0 ∧ HasDerivAt M (readDifferential N n radicand A hRadicand hOrders v η z * M z) z := by
  obtain ⟨r, hr, hrR, Ψ, hΨa, hΨ⟩ := exists_cover_logarithmic_primitive N n radicand A hRadicand hOrders v η hη (m : ℂ) hm
  let M : ℂ → ℂ := fun z => z ^ m * Complex.exp (Ψ z)
  have he : AnalyticAt ℂ (fun z => Complex.exp (Ψ z)) 0 := hΨa.cexp
  have hM : MeromorphicAt M 0 :=
    ((analyticAt_id.meromorphicAt).zpow m).mul he.meromorphicAt
  refine ⟨r, hr, hrR, M, hM, ?_, fun z hz hn => ?_⟩
  · apply (meromorphicOrderAt_eq_int_iff hM).mpr
    refine ⟨fun z => Complex.exp (Ψ z), he, Complex.exp_ne_zero _, ?_⟩
    exact Eventually.of_forall fun z => by simp only [M, sub_zero, smul_eq_mul]
  · refine ⟨mul_ne_zero (zpow_ne_zero _ hn) (Complex.exp_ne_zero _), ?_⟩
    have hd := (hasDerivAt_zpow m z (Or.inl hn)).mul ((hΨ z hz hn).cexp)
    apply hd.congr_deriv
    dsimp [M]
    rw [zpow_sub_one₀ hn]
    ring


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

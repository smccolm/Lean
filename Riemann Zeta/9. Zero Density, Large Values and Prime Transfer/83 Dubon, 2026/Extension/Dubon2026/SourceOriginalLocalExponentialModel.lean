import Dubon2026.SourceOriginalLogarithmicReading

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
meromorphic exponential. For integer residue m, the actual uniformizer gives
the local model z^m exp(Psi(z)). Its logarithmic derivative is the original
differential reading and its meromorphic order is exactly m. Global period
correction and gluing the path exponential remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_local_exponential_model (v : Place ℂ F) (η : Ω[F⁄ℂ])
    (hη : -1 ≤ v.ordDifferential η) (m : ℤ)
    (hm : originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (m : ℂ)) :
    ∃ r : ℝ, 0 < r ∧ r < placeRadius N v ∧ ∃ M : ℂ → ℂ,
      MeromorphicAt M 0 ∧ meromorphicOrderAt M 0 = (m : WithTop ℤ) ∧
        ∀ z ∈ ball (0 : ℂ) r, z ≠ 0 →
          M z ≠ 0 ∧ HasDerivAt M (readDifferential N v η z * M z) z := by
  obtain ⟨r, hr, hrR, Ψ, hΨa, hΨ⟩ := exists_original_logarithmic_primitive N v η hη (m : ℂ) hm
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
end Dubon2026.SourceFunctionField.OriginalChart

import Dubon2026.SourceOriginalWeilCoverPlaceFamily
import Dubon2026.SourceCurveConvergentPlaceChart

/-! DUB-17/18 -> original Weil nondegeneracy -> auxiliary cover Abel comparison.
Every actual place of the literal torsion cover has an injective analytic
parameter family whose coordinate is its actual uniformizer residue value.
All nonzero function readings are meromorphic with exact normalized orders;
regular readings are analytic. Global chart compatibility and division remain open. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve CuspTaylor Polynomial Metric SourceCurve.AnalyticDisc
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])

theorem exists_originalWeil_cover_parameter
    (D : Divisor ℂ FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (w : Place ℂ EE) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ EE), 0 < ρ ∧ γ 0 = w ∧ Set.InjOn γ (ball 0 ρ) ∧
      (∀ z ∈ ball 0 ρ, (γ z).rationalEval
        (originalWeilKummerCover_residue_bijective N ℂ n f (γ z)) w.uniformizer = z) ∧
      ∀ z ∈ ball 0 ρ, ∀ a : EE, a ≠ 0 →
        MeromorphicAt (fun t => (γ t).rationalEval
          (originalWeilKummerCover_residue_bijective N ℂ n f (γ t)) a) z ∧
        meromorphicOrderAt (fun t => (γ t).rationalEval
          (originalWeilKummerCover_residue_bijective N ℂ n f (γ t)) a) z =
            ((γ z).ord a : WithTop ℤ) ∧
        (a ∈ (γ z).toValuationSubring → AnalyticAt ℂ
          (fun t => (γ t).rationalEval
            (originalWeilKummerCover_residue_bijective N ℂ n f (γ t)) a) z) := by
  obtain ⟨e, R, G, δ, γ, hR, hδ, hγ, _, hm, hall⟩ :=
    exists_originalWeil_cover_place_family N n f D hf hfD w
  exact exists_parameter_of_convergent_family e hR G (fun a => (hm a).1) (fun a => (hm a).2)
    (originalWeilKummerCover_residue_bijective N ℂ n f) w hδ γ hγ
    (fun z hz => (hall z hz).1) (fun z hz => (hall z hz).2.1)
    (fun z hz => (hall z hz).2.2.1)

end
end Dubon2026.SourceFunctionField.OriginalChart

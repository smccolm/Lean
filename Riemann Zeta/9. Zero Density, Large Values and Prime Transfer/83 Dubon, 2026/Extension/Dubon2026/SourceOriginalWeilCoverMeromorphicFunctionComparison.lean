import Dubon2026.SourceOriginalWeilCoverMeromorphicPoleClearing
import Dubon2026.SourceOriginalWeilCoverOnePoleComparison

/-! DUB-17/18 -> auxiliary point division -> Abel converse -> actual field comparison.
Use the proved analytic pole bound and the actual finite-coordinate divisor
spaces to clear poles. The faithful basis relation then identifies the
analytic function in punctured chart germs with an element of the literal
Kummer splitting field. All cover geometry and dimension inputs are proved.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem exists_cover_function_of_meromorphicAt
    (g : Place ℂ (EE) → ℂ)
    (hg : ∀ v, MeromorphicAt (fun z => g (placeFamily N n r A hr hrA v z)) 0) :
    ∃ f : EE, ∀ v,
      (fun z => g (placeFamily N n r A hr hrA v z)) =ᶠ[𝓝[≠] (0 : ℂ)] chartRead N n r A hr hrA v f := by
  let Q := Classical.choice (nonempty_cover_place N n r)
  obtain ⟨k, h, hh0, hh⟩ := exists_cover_meromorphic_pole_clearing N n r A hr hrA Q g hg
  let q : Place ℂ (EE) → ℂ :=
    fun P => g P * P.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r P) h
  obtain ⟨f, hf⟩ := exists_cover_function_of_one_pole_bound N n r A hr hrA Q k q
    (fun v => (hh v).1) (fun v => (hh v).2)
  refine ⟨f * h⁻¹, fun v => ?_⟩
  filter_upwards [hf v, chartRead_mul N n r A hr hrA v f h⁻¹, chartRead_inv N n r A hr hrA v hh0,
    chartRead_eventually_ne_zero N n r A hr hrA v hh0] with z hz hm hi hn
  change g (placeFamily N n r A hr hrA v z) * chartRead N n r A hr hrA v h z = chartRead N n r A hr hrA v f z at hz
  rw [hm, Pi.mul_apply, hi, Pi.inv_apply]
  field_simp
  exact hz

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

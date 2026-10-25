import Dubon2026.SourceOriginalChartLaurentHom
import Dubon2026.SourceOriginalWeilLocalKummerRoot

/-! DUB-17/18 -> auxiliary cover analytic entry -> literal convergent root.
The actual local meromorphic root is represented in the existing convergent
Laurent field. Uniqueness identifies its n-th power with the original chart
homomorphism's radicand, so it can split the actual Kummer polynomial. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve CuspTaylor Filter
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldOver N ℂ

theorem exists_originalWeil_convergent_kummer_root (n : ℕ) [NeZero n]
    (D : Divisor ℂ FF) (f : FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (v : Place ℂ FF) :
    ∃ A : realizedField, A ^ n = chartLaurentHom N v f := by
  obtain ⟨H, hm, _, hp⟩ := originalWeil_local_kummer_root N n D f hf hfD v
  obtain ⟨A, hA⟩ := exists_realized_represents hm
  refine ⟨A, Subtype.ext ?_⟩
  exact (hA.pow n).eq_series ((chartLaurent_represents N v f).congr hp)

end
end Dubon2026.SourceFunctionField.OriginalChart

import Dubon2026.SourceCuspDiscRealization

/-! DUB-17/18 -> auxiliary Kummer cover analytic entry.
Reuse the existing field of convergent Taylor quotients. Every meromorphic
germ at zero has a unique represented Laurent series, and the representation
respects powers. These are the precise bridges needed to realize the local
torsion roots and the original function field in that existing field. -/
namespace Dubon2026.SourceFunctionField.CuspTaylor
noncomputable section
open Filter
open scoped Topology

theorem represents_analytic {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    Represents (series F : LaurentSeries ℂ) F := by
  refine ⟨F, fun _ => 1, hF, analyticAt_const, ?_, ?_, ?_⟩
  · rw [series_const]
    simp
  · rw [series_const]
    simp
  · exact Eventually.of_forall (fun z => (div_one (F z)).symm)

theorem Represents.pow {A : LaurentSeries ℂ} {F : ℂ → ℂ}
    (hF : Represents A F) (n : ℕ) : Represents (A ^ n) (F ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using represents_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem Represents.zpow {A : LaurentSeries ℂ} {F : ℂ → ℂ}
    (hF : Represents A F) (n : ℤ) : Represents (A ^ n) (F ^ n) := by
  cases n with
  | ofNat n => simpa only [zpow_natCast] using hF.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hF.pow (n + 1)).inv

theorem Represents.eq_series {A B : LaurentSeries ℂ} {F : ℂ → ℂ}
    (hA : Represents A F) (hB : Represents B F) : A = B := by
  obtain ⟨f, g, hf, hg, hg0, hA, heA⟩ := hA
  obtain ⟨h, k, hh, hk, hk0, hB, heB⟩ := hB
  rw [hA, hB]
  exact (quotient_eq_iff_eventuallyEq hf hg hh hk hg0 hk0).mpr (heA.symm.trans heB)

theorem Represents.mem_realizedField {A : LaurentSeries ℂ} {F : ℂ → ℂ}
    (hA : Represents A F) : A ∈ realizedField := by
  obtain ⟨f, g, hf, hg, hg0, hA, _⟩ := hA
  exact ⟨f, g, hf, hg, hg0, hA⟩

theorem exists_realized_represents {F : ℂ → ℂ} (hF : MeromorphicAt F 0) :
    ∃ A : realizedField, Represents A.val F := by
  obtain ⟨k, g, hg, hFg⟩ := MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mp hF
  have hrep := ((represents_analytic (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) 0)).zpow k).mul
    (represents_analytic hg)
  have hrepF := hrep.congr (by simpa only [sub_zero, smul_eq_mul] using hFg)
  exact ⟨⟨_, hrepF.mem_realizedField⟩, hrepF⟩

end
end Dubon2026.SourceFunctionField.CuspTaylor

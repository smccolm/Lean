import Dubon2026.SourceOriginalComplementaryPeriodSpan
import Dubon2026.SourceCellPolygonWordAntisymmetry
import Dubon2026.SourcePeriodMatrixLatticeUnimodularity

/-! DUB-17/18 -> original Abel-Jacobi -> exact period matrix reciprocity.
The complementary restriction of the same strict word matrix is skew-symmetric
and unimodular. Integer generation of jumps by periods and periods by jumps,
the actual full real span and exact Euler count prove determinant invertibility.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {D : CellDissection N}
local notation "F" => modularFunctionFieldOver N ℂ

/-- The exact polygon word matrix restricted to the complementary geometric edges. -/
def complementaryWordMatrix (T Ts : Finset D.ιE) {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : D.ιE × Bool // q.1 ∉ Ts}) :
    Matrix {l // l ∈ (T ∪ Ts)ᶜ} {l // l ∈ (T ∪ Ts)ᶜ} ℤ :=
  fun j l => wordMatrix wd j.1 l.1

theorem complementaryWordMatrix_transpose (T Ts : Finset D.ιE) {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : D.ιE × Bool // q.1 ∉ Ts}) :
    (complementaryWordMatrix T Ts wd).transpose = -complementaryWordMatrix T Ts wd := by
  funext j l
  have hj : j.1 ∉ Ts := fun h => (Finset.mem_compl.mp j.2) (Finset.mem_union_right T h)
  have hl : l.1 ∉ Ts := fun h => (Finset.mem_compl.mp l.2) (Finset.mem_union_right T h)
  simp only [Matrix.transpose_apply, Matrix.neg_apply, complementaryWordMatrix,
    wordMatrix_of_not_mem wd hj, wordMatrix_of_not_mem wd hl]
  exact wordChain_antisymm wd j.1 l.1 hj hl

theorem complementaryWordMatrix_isUnit (D : CellDissection N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (V : D.ιC → Set ℂ) (Ψ : Fin n → D.ιC → ℂ → ℂ) (J : D.ιE → Fin n → ℂ)
    (hP : PrimData D (fun i => (b i : Ω[F⁄ℂ])) V Ψ) (hJ : IsJump D Ψ J)
    (T Ts : Finset D.ιE)
    (hc : (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ F))
    (hgen : AddSubgroup.closure (range J) ≤ AddSubgroup.closure (J '' ((T ∪ Ts)ᶜ : Finset D.ιE)))
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hR : RegularCycleGeneration D (fun i => (b i : Ω[F⁄ℂ])) T Ts γ)
    {m : ℕ} [NeZero m] (wd : ZMod m ≃ {q : D.ιE × Bool // q.1 ∉ Ts})
    (hrow : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
      (wordMatrix wd j l : ℂ) • (fun i => pathIntegral N (b i : Ω[F⁄ℂ]) (γ l))) :
    IsUnit (complementaryWordMatrix T Ts wd).det := by
  let z : {l // l ∈ (T ∪ Ts)ᶜ} → Fin n → ℂ :=
    fun l i => pathIntegral N (b i : Ω[F⁄ℂ]) (γ l.1)
  let Jc : {l // l ∈ (T ∪ Ts)ᶜ} → Fin n → ℂ := fun l => J l.1
  apply isUnit_det_of_lattice z Jc (complementaryWordMatrix T Ts wd)
  · intro j
    have hj : j.1 ∉ Ts := fun h => (Finset.mem_compl.mp j.2) (Finset.mem_union_right T h)
    rw [show Jc j = J j.1 from rfl, hrow j.1 hj, ← Finset.sum_coe_sort]
    simp only [complementaryWordMatrix, Int.cast_smul_eq_zsmul, z]
  · intro l
    have hm := hgen (loop_period_mem_jumps D (fun i => (b i : Ω[F⁄ℂ])) V Ψ J hP hJ
      (D.vert (D.ends l.1).1) (γ l.1))
    simpa only [Set.image_eq_range] using hm
  · exact complementary_periods_span_real D b T Ts γ hR
  · have hn : Module.finrank ℂ (regularDifferentials ℂ F) = n := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
    simp only [Fintype.card_coe, hc, hn]
    simp [finrank_real_of_complex, two_mul]

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods

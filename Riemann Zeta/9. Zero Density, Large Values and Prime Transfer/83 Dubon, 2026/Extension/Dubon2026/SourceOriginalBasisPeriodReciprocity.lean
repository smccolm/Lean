import Dubon2026.SourceOriginalCellResidueReciprocity

/-! DUB-17/18 -> original Abel-Jacobi -> raw residue reciprocity.
The exact complementary word matrix simultaneously supplies unimodularity,
the Riemann relation and the original Abel-divisor residue identity on the
actual constructed cycles. This packages the clauses required by the existing
Abel converse; reindexing to its fixed 2g index set remains a separate step.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- Simultaneous unimodular Riemann and original Abel-divisor identities on the complementary cycles. -/
def BasisPeriodReciprocity {n : ℕ} (D : CellDissection N) (η : Fin n → Ω[F⁄ℂ])
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) : Prop :=
  ∃ Q : Matrix {l // l ∈ (T ∪ Ts)ᶜ} {l // l ∈ (T ∪ Ts)ᶜ} ℤ,
    Q.transpose = -Q ∧ IsUnit Q.det ∧
    (∀ i i', (∑ j, ∑ l, (Q j l : ℂ) * pathIntegral N (η i) (γ j.1) *
      pathIntegral N (η i') (γ l.1)) = 0) ∧
    ∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]), (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
      (∀ v : Place ℂ F,
        originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) = (E v : ℂ)) →
      E.support ⊆ S → ∃ c : {l // l ∈ (T ∪ Ts)ᶜ} → ℤ, ∀ i,
        (∑ j, ∑ l, (Q j l : ℂ) * pathIntegral N (η i) (γ j.1) * pathIntegral N θ (γ l.1)) =
          2 * Real.pi * Complex.I * (abelJacobiDiv N η P₀ E i +
            ∑ l, (c l : ℂ) * pathIntegral N (η i) (γ l.1))

theorem basis_period_reciprocity_of_polygon {n : ℕ} (D : CellDissection N)
    (η : Fin n → Ω[F⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : Fin n → D.ιC → ℂ → ℂ)
    (J : D.ιE → Fin n → ℂ) (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J)
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (P₀ : Place ℂ F) (hzero : gvec D Ψ P₀ (cellOf D P₀) = 0)
    (S : Finset (Place ℂ F)) (hW : BilinearCyclePeriodPolygonConclusion D η T Ts J γ S Ψ) :
    BasisPeriodReciprocity D η T Ts γ P₀ S := by
  obtain ⟨hm, wd, _, _, _, _, hcl, hskew, hu, hri, hweighted⟩ := hW
  letI := hm
  have hsk : ∀ j ∈ (T ∪ Ts)ᶜ, ∀ l ∈ (T ∪ Ts)ᶜ, wordMatrix wd l j = -wordMatrix wd j l := by
    intro j hj l hl
    exact congrFun (congrFun hskew ⟨j, hj⟩) ⟨l, hl⟩
  have hsum : ∀ f : D.ιE → D.ιE → ℂ,
      (∑ j : {l // l ∈ (T ∪ Ts)ᶜ}, ∑ l : {l // l ∈ (T ∪ Ts)ᶜ}, f j.1 l.1) =
        ∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ, f j l := by
    intro f
    rw [Finset.sum_coe_sort ((T ∪ Ts)ᶜ) (fun j => ∑ l : {l // l ∈ (T ∪ Ts)ᶜ}, f j l.1)]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_coe_sort _ _
  refine ⟨complementaryWordMatrix T Ts wd, hskew, hu, ?_, ?_⟩
  · intro i i'
    change (∑ j : {l // l ∈ (T ∪ Ts)ᶜ}, ∑ l : {l // l ∈ (T ∪ Ts)ᶜ},
      (wordMatrix wd j.1 l.1 : ℂ) * pathIntegral N (η i) (γ j.1) *
        pathIntegral N (η i') (γ l.1)) = 0
    rw [hsum (fun j l => (wordMatrix wd j l : ℂ) * pathIntegral N (η i) (γ j) *
      pathIntegral N (η i') (γ l))]
    convert hri i' i using 1
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  · intro E θ hθ hres hE
    obtain ⟨c, hc⟩ := residue_reciprocity_of_weighted_cells D η V Ψ J hP hJ T Ts γ hcl
      P₀ hzero S (wordMatrix wd) hsk hweighted E θ hθ hres hE
    refine ⟨fun l => c l.1, fun i => ?_⟩
    change (∑ j : {l // l ∈ (T ∪ Ts)ᶜ}, ∑ l : {l // l ∈ (T ∪ Ts)ᶜ},
      (wordMatrix wd j.1 l.1 : ℂ) * pathIntegral N (η i) (γ j.1) * pathIntegral N θ (γ l.1)) =
        2 * Real.pi * Complex.I * (abelJacobiDiv N η P₀ E i +
          ∑ l : {l // l ∈ (T ∪ Ts)ᶜ}, (c l.1 : ℂ) * pathIntegral N (η i) (γ l.1))
    rw [hsum (fun j l => (wordMatrix wd j l : ℂ) * pathIntegral N (η i) (γ j) *
      pathIntegral N θ (γ l)), Finset.sum_coe_sort ((T ∪ Ts)ᶜ)
        (fun l => (c l : ℂ) * pathIntegral N (η i) (γ l))]
    exact hc i

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods

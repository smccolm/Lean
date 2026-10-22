import Dubon2026.SourceOriginalBasisPeriodReciprocity
import Dubon2026.SourceOriginalMeromorphicBasisExtension

/-! DUB-17/18 -> original Abel-Jacobi -> original Abel converse.
Finite reindexing retains all proved cycle and residue identities and the
unimodular determinant. The basis-coordinate clauses are exactly those of
the existing original Abel-converse consumer; no geometric input is assumed
by the separately assembled existence theorem.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- Exact original geometric inputs to the existing Abel converse on a fixed 2g cycle index. -/
def OriginalRawReciprocityData {n : ℕ} (η : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) : Prop :=
    ∃ (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
      (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
      (∀ k t, Z k t ∉ S ∧ Z k t ≠ P₀) ∧ Q.transpose = -Q ∧ IsUnit Q.det ∧
      (∀ (P : Place ℂ F) (δ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i,
        pathIntegral N (η i) δ = ∑ k, (κ k : ℂ) * pathIntegral N (η i) (Z k)) ∧
      (∀ (P : Place ℂ F) (δ : Path P P), (∀ t, δ t ∉ S) →
        ∃ (κ : Fin n ⊕ Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
          (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral N θ δ = ∑ k, (κ k : ℂ) * pathIntegral N θ (Z k) +
            2 * Real.pi * Complex.I * ∑ v ∈ S,
              (w v : ℂ) * originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ)) ∧
      (∀ i i', (∑ k, ∑ l, (Q k l : ℂ) * pathIntegral N (η i) (Z k) *
        pathIntegral N (η i') (Z l)) = 0) ∧
      (∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]), (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F,
          originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) = (E v : ℂ)) →
        E.support ⊆ S → ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i,
          (∑ k, ∑ l, (Q k l : ℂ) * pathIntegral N (η i) (Z k) *
            pathIntegral N θ (Z l)) = 2 * Real.pi * Complex.I *
              (abelJacobiDiv N η P₀ E i +
                ∑ k, (κ k : ℂ) * pathIntegral N (η i) (Z k)))

theorem reindex_original_reciprocity {n : ℕ} (D : CellDissection N)
    (η : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) (S : Finset (Place ℂ F))
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hcount : (T ∪ Ts)ᶜ.card = 2 * n)
    (hinter : ∀ v ∈ insert P₀ (S : Set (Place ℂ F)),
      ∃ C : D.ιC, v ∈ (D.cell C).interior')
    (hγs : ∀ j t, γ j t ∈ D.skeleton)
    (hR : DissectionPeriods.RegularCycleGeneration D η T Ts γ)
    (hG : MeromorphicPeriods.MeromorphicCycleGeneration D S T Ts γ)
    (hB : DissectionPeriods.BasisPeriodReciprocity D η T Ts γ P₀ S) :
    OriginalRawReciprocityData η P₀ S := by
  classical
  obtain ⟨Q, hskew, hu, hri, hrec⟩ := hB
  have hcard : Fintype.card (Fin n ⊕ Fin n) = Fintype.card {l // l ∈ (T ∪ Ts)ᶜ} := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hcount]
    ring
  let e : Fin n ⊕ Fin n ≃ {l // l ∈ (T ∪ Ts)ᶜ} := Fintype.equivOfCardEq hcard
  have hre : ∀ f : D.ιE → ℂ,
      (∑ k, f (e k).1) = ∑ l ∈ (T ∪ Ts)ᶜ, f l := by
    intro f
    rw [Equiv.sum_comp e (fun l => f l.1)]
    exact Finset.sum_coe_sort _ f
  have hdouble : ∀ f : {l // l ∈ (T ∪ Ts)ᶜ} → {l // l ∈ (T ∪ Ts)ᶜ} → ℂ,
      (∑ k, ∑ l, f (e k) (e l)) = ∑ j, ∑ l, f j l := by
    intro f
    rw [Equiv.sum_comp e (fun j => ∑ l, f j (e l))]
    exact Finset.sum_congr rfl fun j _ => Equiv.sum_comp e (fun l => f j l)
  refine ⟨fun k => D.vert (D.ends (e k).1).1,
    fun k => γ (e k).1, Q.submatrix e e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k t
    have haway : γ (e k).1 t ∉ insert P₀ S := fun hv =>
      D.pole_not_mem_skeleton (insert P₀ S)
        (fun v hv => hinter v (Finset.mem_insert.mp hv)) hv (hγs (e k).1 t)
    exact ⟨fun h => haway (Finset.mem_insert_of_mem h),
      fun h => haway (Finset.mem_insert.mpr (Or.inl h))⟩
  · funext k l
    exact congrFun (congrFun hskew (e k)) (e l)
  · rw [Matrix.det_submatrix_equiv_self]
    exact hu
  · intro P δ
    obtain ⟨a, ha⟩ := hR P δ
    refine ⟨fun k => a (e k).1, fun i => ?_⟩
    exact (ha i).trans (hre (fun l => (a l : ℂ) * pathIntegral N (η i) (γ l))).symm
  · intro P δ hδ
    obtain ⟨a, w, haw⟩ := hG P δ hδ
    refine ⟨fun k => a (e k).1, w, fun θ hθ hreg => ?_⟩
    rw [haw θ hθ hreg, hre (fun l => (a l : ℂ) * pathIntegral N θ (γ l))]
    rfl
  · intro i i'
    exact (hdouble (fun j l => (Q j l : ℂ) * pathIntegral N (η i) (γ j.1) *
      pathIntegral N (η i') (γ l.1))).trans (hri i i')
  · intro E θ hθ hres hE
    obtain ⟨c, hc⟩ := hrec E θ hθ hres hE
    refine ⟨fun k => c (e k), fun i => ?_⟩
    change (∑ k, ∑ l, (Q (e k) (e l) : ℂ) * pathIntegral N (η i) (γ (e k).1) *
      pathIntegral N θ (γ (e l).1)) = 2 * Real.pi * Complex.I *
        (abelJacobiDiv N η P₀ E i +
          ∑ k, (c (e k) : ℂ) * pathIntegral N (η i) (γ (e k).1))
    rw [hdouble (fun j l => (Q j l : ℂ) * pathIntegral N (η i) (γ j.1) *
      pathIntegral N θ (γ l.1)), Equiv.sum_comp e
        (fun l => (c l : ℂ) * pathIntegral N (η i) (γ l.1))]
    exact hc i

end
end Dubon2026.SourceFunctionField.CellGeometry

import Dubon2026.SourceJointChartResidueSpans

/-! DUB-17/18 -> Kummer genus inequality -> actual chart dimension bound.
The inverse-coordinate chart with a pole allowance is the image of its
unweighted residue span under coordinate multiplication. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
variable {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
  {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]

/-- The simultaneous residue span of the inverse chart with pole allowance `M`. -/
def weightedST (R : ∀ i, RegularProlongation A F (Fb i)) (f : F) (M : ℕ) :
    Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
  Submodule.span (IsLocalRing.ResidueField A)
    {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
        u * (f ^ M)⁻¹ ∈ V) ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}

theorem weightedST_eq_map (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers) (hf0 : f ≠ 0)
    (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0)
    (hres : ∀ i, (R i).residue ⟨f, hf i⟩ = u i) (M : ℕ) :
    weightedST R f M = (ST R f⁻¹).map
      ((mulEquiv (k := IsLocalRing.ResidueField A) u hu :
        (∀ i, Fb i) →ₗ[IsLocalRing.ResidueField A] (∀ i, Fb i)) ^ M) := by
  have hr : rv R f hf = u := funext hres
  have hu0 : ∀ i, rv R f hf i ≠ 0 := fun i => by rw [hr]; exact hu i
  change Submodule.span _ _ = _
  rw [span_setM_eq f hf (inv_mem_integers hu0) hf0 hu0 M]
  congr 2
  exact LinearMap.ext fun h => by simp only [LinearEquiv.coe_coe, mulEquiv_apply, hr]

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly

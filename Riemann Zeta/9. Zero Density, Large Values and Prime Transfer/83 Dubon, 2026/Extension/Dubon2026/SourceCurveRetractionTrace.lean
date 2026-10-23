import Dubon2026.SourceCurveFiniteRankTraceComparison

/-! The projector comparison needed for residue/trace compatibility.
Both retractions have the same actual integral subspace as target. Their
projected multiplication operators differ by a map factoring through the
proved finite principal parts. If the second multiplication preserves
integral elements, their commutator traces agree. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Multiplication followed by a retraction, acting on the common integral subspace. -/
def projectedEnd (A : Submodule K V) (r : V →ₗ[K] A) (φ : V →ₗ[K] V) : A →ₗ[K] A :=
  r ∘ₗ φ ∘ₗ A.subtype

/-- Changing the retraction changes projected multiplication only through principal parts. -/
theorem projectedEnd_sub_factor (A : Submodule K V) (r s : V →ₗ[K] A)
    (hr : ∀ a : A, r a = a) (hs : ∀ a : A, s a = a) (φ : V →ₗ[K] V) :
    projectedEnd A r φ - projectedEnd A s φ =
      (r - s) ∘ₗ ((LinearMap.id - A.subtype ∘ₗ r) ∘ₗ φ ∘ₗ A.subtype) := by
  apply LinearMap.ext
  intro a
  change r (φ (a : V)) - s (φ (a : V)) =
    (r - s) (φ (a : V) - (r (φ (a : V)) : V))
  simp only [LinearMap.sub_apply, map_sub, hr, hs]
  abel_nf

/-- A finite principal-part image makes the difference of projected multiplications finite rank. -/
theorem finite_range_projectedEnd_sub (A : Submodule K V) (r s : V →ₗ[K] A)
    (hr : ∀ a : A, r a = a) (hs : ∀ a : A, s a = a) (φ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range
      ((LinearMap.id - A.subtype ∘ₗ r) ∘ₗ φ ∘ₗ A.subtype))] :
    FiniteDimensional K (LinearMap.range (projectedEnd A r φ - projectedEnd A s φ)) := by
  rw [projectedEnd_sub_factor A r s hr hs, LinearMap.range_comp]
  exact Module.Finite.map _ _

/-- A subspace-preserving operator has the same restriction through either retraction. -/
theorem projectedEnd_eq_restrict (A : Submodule K V) (r : V →ₗ[K] A)
    (hr : ∀ a : A, r a = a) (γ : V →ₗ[K] V) (hγ : ∀ x ∈ A, γ x ∈ A) :
    projectedEnd A r γ = γ.restrict hγ := by
  apply LinearMap.ext
  intro a
  exact hr ⟨γ a, hγ a a.2⟩

/-- The finite commutator and its trace survive a change of integral retraction. -/
theorem retraction_commutator_trace (A : Submodule K V) (r s : V →ₗ[K] A)
    (hr : ∀ a : A, r a = a) (hs : ∀ a : A, s a = a)
    (φ γ : V →ₗ[K] V) (hγ : ∀ x ∈ A, γ x ∈ A)
    [FiniteDimensional K (LinearMap.range
      ((LinearMap.id - A.subtype ∘ₗ r) ∘ₗ φ ∘ₗ A.subtype))]
    [FiniteDimensional K (LinearMap.range
      (projectedEnd A r φ ∘ₗ projectedEnd A r γ -
        projectedEnd A r γ ∘ₗ projectedEnd A r φ))] :
    FiniteDimensional K (LinearMap.range
      (projectedEnd A s φ ∘ₗ projectedEnd A s γ -
        projectedEnd A s γ ∘ₗ projectedEnd A s φ)) ∧
    finrankTrace (projectedEnd A r φ ∘ₗ projectedEnd A r γ -
        projectedEnd A r γ ∘ₗ projectedEnd A r φ) =
      finrankTrace (projectedEnd A s φ ∘ₗ projectedEnd A s γ -
        projectedEnd A s γ ∘ₗ projectedEnd A s φ) := by
  let P := projectedEnd A r φ
  let Q := projectedEnd A s φ
  let G := γ.restrict hγ
  haveI : FiniteDimensional K (LinearMap.range (P - Q)) :=
    finite_range_projectedEnd_sub A r s hr hs φ
  haveI := finite_range_comp_left G (P - Q)
  haveI := finite_range_comp_right G (P - Q)
  haveI := finite_range_sub ((P - Q) ∘ₗ G) (G ∘ₗ (P - Q))
  haveI : FiniteDimensional K (LinearMap.range (P ∘ₗ G - G ∘ₗ P)) := by
    have hi : FiniteDimensional K (LinearMap.range
        (projectedEnd A r φ ∘ₗ projectedEnd A r γ -
          projectedEnd A r γ ∘ₗ projectedEnd A r φ)) := inferInstance
    have heC : projectedEnd A r φ ∘ₗ projectedEnd A r γ -
        projectedEnd A r γ ∘ₗ projectedEnd A r φ = P ∘ₗ G - G ∘ₗ P := by
      rw [projectedEnd_eq_restrict A r hr γ hγ]
    exact heC ▸ hi
  have he : Q ∘ₗ G - G ∘ₗ Q = (P ∘ₗ G - G ∘ₗ P) -
      ((P - Q) ∘ₗ G - G ∘ₗ (P - Q)) := by
    ext a
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    abel_nf
  haveI : FiniteDimensional K (LinearMap.range (Q ∘ₗ G - G ∘ₗ Q)) := by
    rw [he]
    exact finite_range_sub _ _
  rw [projectedEnd_eq_restrict A r hr γ hγ, projectedEnd_eq_restrict A s hs γ hγ]
  exact ⟨inferInstance, finrankTrace_commutator_congr P Q G⟩

end Dubon2026.SourceCurve.ResidueTrace

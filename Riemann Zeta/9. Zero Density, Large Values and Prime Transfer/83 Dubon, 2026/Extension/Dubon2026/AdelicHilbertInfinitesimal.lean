import Dubon2026.AdelicHilbertSecondOrderIdentity

/-! # Genuine infinitesimal operators in the original completed adelic representation -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

/-- The actual Hilbert-norm derivative of the original action along a displayed genuine real curve. -/
def adelicHilbertInfinitesimal {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (v : AdelicCyclicHilbert f) : AdelicCyclicHilbert f :=
  deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c t)) v) 0

/-- The original action carries its actual infinitesimal vector to the derivative at every parameter of the same one-parameter orbit. -/
theorem adelicHilbertInfinitesimal_orbit {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (hc : ∀ s t, c (s + t) = c s * c t) (v : AdelicCyclicHilbert f)
    (hd : DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (c t)) v) 0) (s : ℝ) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c s))
      (adelicHilbertInfinitesimal f c v) =
      deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c t)) v) s := by
  apply @continuousLinearMap_orbit_deriv (AdelicCyclicHilbert f) inferInstance inferInstance
    ((adelicCyclicHilbertOperator f (adelicRealSL2Embedding (c s))).restrictScalars ℝ)
    (fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c t)) v) s _ hd
  intro t
  change adelicCyclicHilbertOperator f (adelicRealSL2Embedding (c s))
    (adelicCyclicHilbertOperator f (adelicRealSL2Embedding (c t)) v) =
    adelicCyclicHilbertOperator f (adelicRealSL2Embedding (c (s + t))) v
  rw [hc, map_mul]
  exact (adelicCyclicHilbertOperator_mul f (adelicRealSL2Embedding (c s))
    (adelicRealSL2Embedding (c t)) v).symm

/-- The genuine one-parameter group law identifies two successive actual infinitesimal actions with the original second Hilbert orbit derivative. -/
theorem adelicHilbertInfinitesimal_twice {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (hc : ∀ s t, c (s + t) = c s * c t) (v : AdelicCyclicHilbert f)
    (hd : DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (c t)) v) 0) :
    adelicHilbertInfinitesimal f c (adelicHilbertInfinitesimal f c v) =
      iteratedDeriv 2 (fun t : ℝ => adelicCyclicHilbertRepresentation f
        (adelicRealSL2Embedding (c t)) v) 0 := by
  change deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f
    (adelicRealSL2Embedding (c t)) (adelicHilbertInfinitesimal f c v)) 0 = _
  simp_rw [adelicHilbertInfinitesimal_orbit f c hc v hd]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]

/-- The genuine Hilbert infinitesimal action commutes with complex scaling of each differentiable original vector. -/
theorem adelicHilbertInfinitesimal_smul {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (v : AdelicCyclicHilbert f)
    (hd : DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (c t)) v) 0) (a : ℂ) :
    adelicHilbertInfinitesimal f c (a • v) = a • adelicHilbertInfinitesimal f c v := by
  let C := fun t : ℝ => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c t)) v
  let L : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
    a • ContinuousLinearMap.id ℂ (AdelicCyclicHilbert f)
  have he := @deriv_continuousLinearMap (AdelicCyclicHilbert f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (L.restrictScalars ℝ) C 0 hd
  unfold adelicHilbertInfinitesimal
  simp_rw [map_smul]
  exact he

end
end Dubon2026

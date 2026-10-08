import Dubon2026.AdelicFirstDerivativeBounds
import Dubon2026.BoundedL2Differentiation

/-! # Genuine projective L2 derivatives of the original adelic real orbits -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The actual projective-coordinate function of an original real right translate of the original generator. -/
def adelicProjectiveRealOrbit (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (t : ℝ) : AdelicProjectiveGroup → ℂ :=
  adelicCyclicProjectiveFunction N f
    ((adelicLiftCyclicRepresentation N k f).toRepresentation (adelicRealSL2Embedding (c t))
      (adelicCyclicGenerator N f))

/-- Every original projective orbit point has an actual full adelic representative valid simultaneously for all parameters. -/
theorem adelicProjectiveRealOrbit_representative (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (p : AdelicProjectiveGroup) :
    ∃ g : RationalAdelicGL2, ∀ t : ℝ, adelicProjectiveRealOrbit N f c t p =
      canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t)) := by
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
  obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_surjective p.2
  have hp : p = (QuotientGroup.mk r, ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
  refine ⟨rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a), fun t => ?_⟩
  rw [hp]
  rfl

/-- Each actual original projective orbit function is genuinely square-integrable on its arithmetic fundamental domain. -/
theorem adelicProjectiveRealOrbit_memLp (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ)) (t : ℝ) :
    MemLp (adelicProjectiveRealOrbit N f c t) 2
      (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)) :=
  adelicCyclicProjectiveFunction_memLp_two N f _

/-- Proved pointwise original orbit derivatives and uniform original bounds give a genuine derivative of the actual quotient L2 orbit. -/
theorem adelicProjectiveRealOrbit_differentiableAt_of_bounds (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (hd : ∀ g : RationalAdelicGL2, DifferentiableAt ℝ
      (fun t : ℝ => canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t))) 0)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hD : ∀ g : RationalAdelicGL2, ‖deriv
      (fun t : ℝ => canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t))) 0‖ ≤ C)
    (hL : ∀ g : RationalAdelicGL2, ∀ t : ℝ,
      ‖canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t)) -
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c 0))‖ ≤ C * |t|) :
    DifferentiableAt ℝ (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (adelicRealSL2Embedding (c t))
        (adelicCyclicGenerator N f))) 0 := by
  let μ := adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  let F := adelicProjectiveRealOrbit N f c
  let D := fun p => deriv (fun t : ℝ => F t p) 0
  have hF (t : ℝ) : MemLp (F t) 2 μ := adelicProjectiveRealOrbit_memLp N f c t
  have hpoint (p : AdelicProjectiveGroup) : HasDerivAt (fun t : ℝ => F t p) (D p) 0 := by
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f c p
    have he : (fun t : ℝ => F t p) = fun t =>
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t)) := funext hg
    apply DifferentiableAt.hasDerivAt
    rw [he]
    exact hd g
  have hbound (p : AdelicProjectiveGroup) : ‖D p‖ ≤ C := by
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f c p
    change ‖deriv (fun t : ℝ => F t p) 0‖ ≤ C
    have he : (fun t : ℝ => F t p) = fun t =>
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t)) := funext hg
    rw [he]
    exact hD g
  have hmem : MemLp D 2 μ := memLp_pointwise_derivative F D
    (fun t => (hF t).aestronglyMeasurable) hpoint C hbound
  have herr (t : ℝ) (p : AdelicProjectiveGroup) :
      ‖(t⁻¹ : ℝ) • (F t p - F 0 p) - D p‖ ≤ 2 * C := by
    apply difference_quotient_error_bound (fun u => F u p) (D p) hC0 _ (hbound p)
    intro u
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f c p
    change ‖adelicProjectiveRealOrbit N f c u p - adelicProjectiveRealOrbit N f c 0 p‖ ≤ _
    rw [hg u, hg 0]
    exact hL g u
  exact (hasDerivAt_toLp_of_bounded_difference_quotients F D hF hmem hpoint
    (by positivity : 0 ≤ 2 * C) herr).differentiableAt

end
end Dubon2026

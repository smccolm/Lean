import Dubon2026.AdelicLocalFullAwayTensorAction
import Dubon2026.AdelicLocalAwayTensorCompletion
import Dubon2026.IsometricRepresentationCompletion

/-! # The genuine completed local/full-complement Hilbert tensor factorization of the original full adelic space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UniformSpace
open scoped MatrixGroups TensorProduct

/-- Strong continuity transfers through a proved genuine isometric intertwiner. -/
theorem isometric_intertwiner_stronglyContinuous {G V W : Type*} [TopologicalSpace G]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ρ : G → V → V) (σ : G → W → W) (T : V →ₗᵢ[ℂ] W)
    (h : ∀ g x, T (ρ g x) = σ g (T x)) (hc : ∀ y, Continuous (fun g => σ g y)) (x : V) :
    Continuous (fun g => ρ g x) := by
  apply T.isometry.comp_continuous_iff.mp
  exact (hc (T x)).congr (fun g => (h g x).symm)

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The actual Hilbert tensor completion of the two original algebraic local and real-plus-away orbit cores. -/
abbrev AdelicLocalFullAwayHilbertTensor (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : HeightOneSpectrum ℤ) :=
  Completion (adelicLocalCyclicCore f v ⊗[ℂ] adelicFullAwayCyclicCore f v)

variable {p : ℕ} [NeZero p] [Fact p.Prime] (F : PrimitiveCuspForm N k)

/-- The genuine original external tensor action preserves its actual tensor norm. -/
theorem adelicLocalFullAwayTensorRepresentation_norm (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    ‖adelicLocalFullAwayTensorRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b x‖ = ‖x‖ :=
  @linearMap_norm_of_isometric_intertwiner
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicLocalFullAwayTensorIsometry F hpN) (adelicLocalFullAwayTensorRepresentation F.toCuspForm _ b)
    (adelicLocalFullAwayJointRepresentation F.toCuspForm _ b)
    (adelicLocalFullAwayTensorIsometry_intertwines F hpN b)
    (adelicCyclicHilbertOperator_norm F.toCuspForm
      (adelicLocalFullAwayEquiv _ b)) x

/-- The original tensor action completed by its proved continuous norm-preserving operators. -/
def adelicLocalFullAwayHilbertTensorRepresentation (hpN : p.Coprime N) :
    Representation ℂ (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
      (AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :=
  isometricRepresentationCompletion (adelicLocalFullAwayTensorRepresentation F.toCuspForm _)
    (adelicLocalFullAwayTensorRepresentation_norm F hpN)

/-- The genuine original tensor isometry extended to its actual Hilbert completion. -/
def adelicLocalFullAwayHilbertTensorIsometry (hpN : p.Coprime N) :
    AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) →ₗᵢ[ℂ]
      AdelicCyclicHilbert F.toCuspForm :=
  @linearIsometryCompletion
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicLocalFullAwayTensorIsometry F hpN)

/-- The actual completed tensor map agrees with its genuine algebraic source on every original vector. -/
theorem adelicLocalFullAwayHilbertTensorIsometry_coe (hpN : p.Coprime N)
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayHilbertTensorIsometry F hpN
      (x : AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
        adelicLocalFullAwayTensorIsometry F hpN x :=
  linearIsometryCompletion_coe _ x

/-- The actual completed tensor range is the entire original full adelic Hilbert space. -/
theorem adelicLocalFullAwayHilbertTensorIsometry_range (hpN : p.Coprime N) :
    (adelicLocalFullAwayHilbertTensorIsometry F hpN).toLinearMap.range =
      ⊤ :=
  (@linearIsometryCompletion_range
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicLocalFullAwayTensorIsometry F hpN)).trans
    (adelicLocalFullAwayTensorIsometry_range_closure F hpN)

/-- A genuine linear isometry equivalence from the actual completed local/full-complement tensor to the entire original full adelic space. -/
def adelicLocalFullAwayHilbertTensorEquiv (hpN : p.Coprime N) :
    AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ≃ₗᵢ[ℂ]
      AdelicCyclicHilbert F.toCuspForm :=
  (adelicLocalFullAwayHilbertTensorIsometry F hpN).equivRange.trans
    (LinearIsometryEquiv.ofTop _ _ (adelicLocalFullAwayHilbertTensorIsometry_range F hpN))

/-- The actual equivalence retains exactly the original completed tensor map as its ambient value. -/
theorem adelicLocalFullAwayHilbertTensorEquiv_apply (hpN : p.Coprime N)
    (x : AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayHilbertTensorEquiv F hpN x = adelicLocalFullAwayHilbertTensorIsometry F hpN x := rfl

/-- Every actual completed tensor vector has the exact original full adelic action under the completed isometry. -/
theorem adelicLocalFullAwayHilbertTensorIsometry_intertwines (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayHilbertTensorIsometry F hpN (adelicLocalFullAwayHilbertTensorRepresentation F hpN b x) =
      adelicLocalFullAwayJointRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b
        (adelicLocalFullAwayHilbertTensorIsometry F hpN x) :=
  @isometricRepresentationCompletion_intertwines
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    inferInstance inferInstance inferInstance
    (adelicLocalFullAwayTensorRepresentation F.toCuspForm _) (adelicLocalFullAwayTensorRepresentation_norm F hpN)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicLocalFullAwayTensorIsometry F hpN) b
    (adelicCyclicHilbertOperator F.toCuspForm
      (adelicLocalFullAwayEquiv _ b))
    (adelicLocalFullAwayTensorIsometry_intertwines F hpN b) x

/-- The genuine completed external tensor action is strongly continuous in the actual local and full complementary group topologies. -/
theorem adelicLocalFullAwayHilbertTensorRepresentation_stronglyContinuous (hpN : p.Coprime N)
    (x : AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    Continuous (fun b => adelicLocalFullAwayHilbertTensorRepresentation F hpN b x) :=
  @isometric_intertwiner_stronglyContinuous
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicLocalFullAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
    (fun b x => adelicLocalFullAwayHilbertTensorRepresentation F hpN b x)
    (fun b x => adelicLocalFullAwayJointRepresentation F.toCuspForm _ b x)
    (adelicLocalFullAwayHilbertTensorIsometry F hpN)
    (adelicLocalFullAwayHilbertTensorIsometry_intertwines F hpN)
    (fun y => (adelicCyclicHilbertRepresentation_stronglyContinuous F.toCuspForm y).comp
      (adelicLocalFullAwayEquiv_continuous _)) x

end
end Dubon2026

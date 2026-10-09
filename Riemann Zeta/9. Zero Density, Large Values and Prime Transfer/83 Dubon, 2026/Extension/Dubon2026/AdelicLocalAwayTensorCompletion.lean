import Dubon2026.AdelicLocalAwayTensorAction
import Dubon2026.IsometricRepresentationCompletion

/-! # The genuine completed local-away Hilbert tensor factorization of the original lowest-weight space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UniformSpace
open scoped MatrixGroups TensorProduct

/-- An isometric intertwiner with an actual norm-preserving action proves norm preservation on its domain. -/
theorem linearMap_norm_of_isometric_intertwiner {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : V →ₗᵢ[ℂ] W) (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (h : ∀ x, T (A x) = B (T x)) (hB : ∀ y, ‖B y‖ = ‖y‖) (x : V) :
    ‖A x‖ = ‖x‖ := by
  calc
    ‖A x‖ = ‖T (A x)‖ := (T.norm_map _).symm
    _ = ‖B (T x)‖ := congrArg norm (h x)
    _ = ‖T x‖ := hB _
    _ = ‖x‖ := T.norm_map _

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The actual Hilbert tensor completion of the two original algebraic local and away-place orbit cores. -/
abbrev AdelicLocalAwayHilbertTensor (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : HeightOneSpectrum ℤ) :=
  Completion (adelicLocalCyclicCore f v ⊗[ℂ] adelicAwayCyclicCore f v)

variable {p : ℕ} [NeZero p] [Fact p.Prime] (F : PrimitiveCuspForm N k)

/-- The genuine original external tensor action preserves its actual tensor norm. -/
theorem adelicLocalAwayTensorRepresentation_norm (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    ‖adelicLocalAwayTensorRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b x‖ = ‖x‖ :=
  @linearMap_norm_of_isometric_intertwiner
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicLocalAwayTensorIsometry F hpN) (adelicLocalAwayTensorRepresentation F.toCuspForm _ b)
    (adelicLocalAwayJointRepresentation F.toCuspForm _ b)
    (adelicLocalAwayTensorIsometry_intertwines F hpN b)
    (adelicCyclicHilbertOperator_norm F.toCuspForm
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalAwayEquiv _ b))) x

/-- The original tensor action completed by its proved continuous norm-preserving operators. -/
def adelicLocalAwayHilbertTensorRepresentation (hpN : p.Coprime N) :
    Representation ℂ (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
      (AdelicLocalAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :=
  isometricRepresentationCompletion (adelicLocalAwayTensorRepresentation F.toCuspForm _)
    (adelicLocalAwayTensorRepresentation_norm F hpN)

/-- The genuine original tensor isometry extended to its actual Hilbert completion. -/
def adelicLocalAwayHilbertTensorIsometry (hpN : p.Coprime N) :
    AdelicLocalAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) →ₗᵢ[ℂ]
      AdelicCyclicHilbert F.toCuspForm :=
  @linearIsometryCompletion
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicLocalAwayTensorIsometry F hpN)

/-- The actual completed tensor map agrees with its genuine algebraic source on every original vector. -/
theorem adelicLocalAwayHilbertTensorIsometry_coe (hpN : p.Coprime N)
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalAwayHilbertTensorIsometry F hpN
      (x : AdelicLocalAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
        adelicLocalAwayTensorIsometry F hpN x :=
  linearIsometryCompletion_coe _ x

/-- The actual completed tensor range is the entire original lowest rotation-weight Hilbert space. -/
theorem adelicLocalAwayHilbertTensorIsometry_range (hpN : p.Coprime N) (hk : 0 < k) :
    (adelicLocalAwayHilbertTensorIsometry F hpN).toLinearMap.range =
      adelicRotationWeightSpace F.toCuspForm :=
  (@linearIsometryCompletion_range
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicLocalAwayTensorIsometry F hpN)).trans
    (adelicLocalAwayTensorIsometry_range_closure F hk hpN)

/-- A genuine linear isometry equivalence from the actual completed local-away tensor to the entire original lowest-weight space. -/
def adelicLocalAwayHilbertTensorEquiv (hpN : p.Coprime N) (hk : 0 < k) :
    AdelicLocalAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ≃ₗᵢ[ℂ]
      adelicRotationWeightSpace F.toCuspForm :=
  (adelicLocalAwayHilbertTensorIsometry F hpN).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (adelicLocalAwayHilbertTensorIsometry_range F hpN hk))

/-- The actual equivalence retains exactly the original completed tensor map as its ambient value. -/
theorem adelicLocalAwayHilbertTensorEquiv_apply (hpN : p.Coprime N) (hk : 0 < k)
    (x : AdelicLocalAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    (adelicLocalAwayHilbertTensorEquiv F hpN hk x).val = adelicLocalAwayHilbertTensorIsometry F hpN x := rfl

/-- Every actual completed tensor vector has the exact original finite adelic action under the completed isometry. -/
theorem adelicLocalAwayHilbertTensorIsometry_intertwines (hpN : p.Coprime N)
    (b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : AdelicLocalAwayHilbertTensor F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalAwayHilbertTensorIsometry F hpN (adelicLocalAwayHilbertTensorRepresentation F hpN b x) =
      adelicLocalAwayJointRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b
        (adelicLocalAwayHilbertTensorIsometry F hpN x) :=
  @isometricRepresentationCompletion_intertwines
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    inferInstance inferInstance inferInstance
    (adelicLocalAwayTensorRepresentation F.toCuspForm _) (adelicLocalAwayTensorRepresentation_norm F hpN)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicLocalAwayTensorIsometry F hpN) b
    (adelicCyclicHilbertOperator F.toCuspForm
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalAwayEquiv _ b)))
    (adelicLocalAwayTensorIsometry_intertwines F hpN b) x

end
end Dubon2026

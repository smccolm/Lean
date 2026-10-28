import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_AtkinLehner
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_slot_ord_of_algHom_laurentBaseChange
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve AlgebraicCurve
theorem ModularCurve.slot_ord_of_algHom_laurentBaseChange (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (a b : ℕ) (ha : a ∣ N) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        qExpand K N (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (w : Place K (laurentBaseChange K (modularFunctionFieldFull N))) (γ : ℤ) (hγ : 0 < γ)
    (hw : ∀ x, w.ord x * γ = (ι x).order) :
    γ = a * Nat.gcd a (N / a) ∧
    w.ord ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        -((N / a / Nat.gcd a (N / a) : ℕ) : ℤ) ∧
    w.ord ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        -((a / Nat.gcd a (N / a) : ℕ) : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_slot_ord_of_algHom_laurentBaseChange.solution

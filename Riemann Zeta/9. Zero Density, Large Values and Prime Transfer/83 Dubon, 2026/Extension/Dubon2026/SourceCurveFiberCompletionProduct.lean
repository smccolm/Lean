import Dubon2026.SourceCurveFiberCompletionKernels
import Dubon2026.SourceCurveFiberCompletionDegree
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The actual completed tensor algebra is the product of the completions
over the base place. Distinct maximal kernels give surjectivity by the
Chinese remainder theorem; the proved ramification degree sum gives
injectivity. This discharges the product decomposition required for the
DUB-17/18 global field-trace and residue sum. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open scoped TensorProduct

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  (v : Place K F)

/-- The Chinese remainder theorem assembles all actual completion components. -/
theorem fiberCompletionDiagonal_surjective :
    Function.Surjective (v.fiberCompletionDiagonal (E := E)) := by
  classical
  intro y
  let m : {w : Place K E // w.restrict F = v} → Ideal (v.adicCompletion ⊗[F] E) :=
    fun w => RingHom.ker (v.fiberCompletionComponent w).toRingHom
  haveI : ∀ w, (m w).IsMaximal := fun w =>
    RingHom.ker_isMaximal_of_surjective (v.fiberCompletionComponent w).toRingHom
      (v.fiberCompletionComponent_surjective w)
  have hcop : Pairwise (Function.onFun IsCoprime m) := fun i j hij =>
    Ideal.isCoprime_of_isMaximal (I := m i) (J := m j)
      (v.fiberCompletionComponent_ker_ne i j hij)
  choose xw hxw using fun w => v.fiberCompletionComponent_surjective w (y w)
  obtain ⟨xbar, hxbar⟩ := Ideal.quotientInfToPiQuotient_surj hcop
    (fun w => Ideal.Quotient.mk (m w) (xw w))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  refine ⟨x, funext fun w => ?_⟩
  change v.fiberCompletionComponent w x = y w
  have hcomp : Ideal.Quotient.mk (m w) x = Ideal.Quotient.mk (m w) (xw w) := by
    have := congrFun hxbar w
    rwa [Ideal.quotientInfToPiQuotient_mk' m x w] at this
  have hmod : x - xw w ∈ m w := Ideal.Quotient.eq.mp hcomp
  have hzero : v.fiberCompletionComponent w (x - xw w) = 0 := hmod
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, hxw w]

/-- The proved original degree formula makes the completed tensor diagonal bijective. -/
theorem fiberCompletionDiagonal_bijective
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) :
    Function.Bijective (v.fiberCompletionDiagonal (E := E)) := by
  have hsurj := v.fiberCompletionDiagonal_surjective (E := E)
  refine ⟨?_, hsurj⟩
  letI srPi : Semiring ((w : {w : Place K E // w.restrict F = v}) →
    w.1.adicCompletion) := inferInstance
  letI algPi : Algebra v.adicCompletion ((w : {w : Place K E // w.restrict F = v}) →
    w.1.adicCompletion) := inferInstance
  letI modPi : Module v.adicCompletion ((w : {w : Place K E // w.restrict F = v}) →
    w.1.adicCompletion) := @Algebra.toModule _ _ _ srPi algPi
  have hdim : Module.finrank v.adicCompletion (v.adicCompletion ⊗[F] E) =
      Module.finrank v.adicCompletion
        ((w : {w : Place K E // w.restrict F = v}) → w.1.adicCompletion) := by
    rw [v.finrank_fiberCompletion_product hbase htop, Module.finrank_tensorProduct,
      Module.finrank_self, one_mul]
  haveI fdPi : FiniteDimensional v.adicCompletion
    ((w : {w : Place K E // w.restrict F = v}) → w.1.adicCompletion) := inferInstance
  exact (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    v.adicCompletion (v.adicCompletion ⊗[F] E) _ _ _
    ((w : {w : Place K E // w.restrict F = v}) → w.1.adicCompletion) _ modPi _ fdPi
    hdim (v.fiberCompletionDiagonal (E := E)).toLinearMap).mpr hsurj

/-- The actual product decomposition, constructed from the proved diagonal bijection. -/
def fiberCompletionProduct
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) :
    v.adicCompletion ⊗[F] E ≃ₐ[v.adicCompletion]
      ((w : {w : Place K E // w.restrict F = v}) → w.1.adicCompletion) :=
  AlgEquiv.ofBijective (v.fiberCompletionDiagonal (E := E))
    (v.fiberCompletionDiagonal_bijective hbase htop)

/-- The product equivalence sends original elements to their literal completed embeddings. -/
theorem fiberCompletionProduct_one_tmul
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (g : E) (w : {w : Place K E // w.restrict F = v}) :
    v.fiberCompletionProduct hbase htop ((1 : v.adicCompletion) ⊗ₜ[F] g) w =
      algebraMap E w.1.adicCompletion g :=
  v.fiberCompletionDiagonal_one_tmul g w

end Dubon2026.SourceCurve.Place

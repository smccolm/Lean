import Dubon2026.SourceCurveCompletionEmbedding

/-! Literal ring maps and scalar towers for the two completed valuation
rings. These connect spectral integrality to native integral-closure
finiteness and freeness for the integral-basis residue/trace comparison.
All maps are restrictions of the proved original completion embedding. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The actual completion embedding restricted to the integral rings. -/
def completionIntegersComap : (w.restrict F).adicCompletionIntegers →+* w.adicCompletionIntegers :=
  (w.adicCompletionComap (F := F)).restrict _ _
    (fun _ hx => w.adicCompletionComap_mem_integers hx)

/-- The map between integral rings retains the actual completed field embedding. -/
theorem completionIntegersComap_coe (x : (w.restrict F).adicCompletionIntegers) :
    (w.completionIntegersComap x : w.adicCompletion) =
      w.adicCompletionComap (F := F) (x : (w.restrict F).adicCompletion) := rfl

/-- The base integral ring acts through its literal restriction map. -/
instance (priority := 100) completionIntegersAlgebra :
    Algebra (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers :=
  (w.completionIntegersComap (F := F)).toAlgebra

/-- The base integral ring acts on the extension field through the actual completion embedding. -/
instance (priority := 100) completionBaseIntegersAlgebra : Algebra (w.restrict F).adicCompletionIntegers w.adicCompletion :=
  ((algebraMap (w.restrict F).adicCompletion w.adicCompletion).comp
    (algebraMap (w.restrict F).adicCompletionIntegers (w.restrict F).adicCompletion)).toAlgebra

/-- The integral base and the completed base field have compatible actions. -/
instance (priority := 100) completionBaseIntegersTower : IsScalarTower (w.restrict F).adicCompletionIntegers
    (w.restrict F).adicCompletion w.adicCompletion :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The two integral rings and the completed extension field form the actual scalar tower. -/
instance (priority := 100) completionIntegersTower : IsScalarTower (w.restrict F).adicCompletionIntegers
    w.adicCompletionIntegers w.adicCompletion :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The completed integral-ring embedding is injective. -/
theorem completionIntegersComap_injective : Function.Injective (w.completionIntegersComap (F := F)) := by
  intro a b h
  exact Subtype.ext ((w.adicCompletionComap (F := F)).injective (congrArg Subtype.val h))

/-- The extension integral ring is torsion-free over the actual base integral ring. -/
theorem torsionFree_completionIntegers :
    Module.IsTorsionFree (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr w.completionIntegersComap_injective

end Dubon2026.SourceCurve.Place

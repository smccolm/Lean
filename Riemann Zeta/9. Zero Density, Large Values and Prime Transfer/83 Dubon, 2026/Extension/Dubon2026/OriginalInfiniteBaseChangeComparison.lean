import Dubon2026.OriginalGlobalInfiniteH2
import Dubon2026.GaloisUnitBaseChange

/-! # Original infinite completion maps under genuine field base change

The actual restricted automorphism fixes the lower infinite place, and
the literal completed inclusion intertwines the two original transports.
This is needed to preserve the zero-infinite domain in DUB-17's remaining
source-normalized class comparison through the auxiliary finite tower.
-/
namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [Normal K L]

/-- The genuine restriction fixes the actual lower infinite place. -/
theorem originalInfiniteBaseChange_fixed (v : InfinitePlace M)
    (σ : OriginalInfiniteDecompositionGroup E M v) :
    galoisBaseChangeRestriction K E L M σ.val • v.comap (algebraMap L M) =
      v.comap (algebraMap L M) := by
  apply InfinitePlace.ext
  intro x
  have he := congrArg (fun z : InfinitePlace M => z (algebraMap L M x)) σ.property
  change v (σ.val.symm (algebraMap L M x)) = v (algebraMap L M x) at he
  have hc := galoisBaseChangeRestriction_commutes K E L M σ.val⁻¹ x
  have hv := (congrArg v hc).trans he
  simpa only [map_inv] using hv

/-- Restriction between the literal original infinite decomposition groups. -/
def originalInfiniteBaseChangeStabilizerHom (v : InfinitePlace M) :
    OriginalInfiniteDecompositionGroup E M v →*
      OriginalInfiniteDecompositionGroup K L (v.comap (algebraMap L M)) where
  toFun σ := ⟨galoisBaseChangeRestriction K E L M σ.val,
    originalInfiniteBaseChange_fixed K E L M v σ⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ σ.val τ.val)

/-- Actual completed inclusion commutes with both original transports. -/
theorem originalInfiniteBaseChange_transport (v : InfinitePlace M)
    (σ : OriginalInfiniteDecompositionGroup E M v)
    (z : (v.comap (algebraMap L M)).Completion) :
    originalInfiniteCompletionBaseChange L M v
      (numberFieldGaloisArchimedeanTransport K L
        (galoisBaseChangeRestriction K E L M σ.val) _ _
        (originalInfiniteBaseChange_fixed K E L M v σ) z) =
      numberFieldGaloisArchimedeanTransport E M σ.val v v σ.property
        (originalInfiniteCompletionBaseChange L M v z) := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq ((originalInfiniteCompletionBaseChange_isometry L M v).continuous.comp
      (numberFieldGaloisArchimedeanTransport_continuous K L _ _ _ _))
      ((numberFieldGaloisArchimedeanTransport_continuous E M _ _ _ _).comp
        (originalInfiniteCompletionBaseChange_isometry L M v).continuous)) ?_
  intro x
  change originalInfiniteCompletionBaseChange L M v
      (numberFieldGaloisArchimedeanTransport K L _ _ _ _
        (algebraMap L (v.comap (algebraMap L M)).Completion (WithAbs.equiv _ x))) =
      numberFieldGaloisArchimedeanTransport E M _ _ _ _
        (originalInfiniteCompletionBaseChange L M v
          (algebraMap L (v.comap (algebraMap L M)).Completion (WithAbs.equiv _ x)))
  rw [numberFieldGaloisArchimedeanTransport_algebraMap,
    originalInfiniteCompletionBaseChange_algebraMap,
    originalInfiniteCompletionBaseChange_algebraMap,
    numberFieldGaloisArchimedeanTransport_algebraMap]
  exact congrArg (algebraMap M v.Completion)
    (galoisBaseChangeRestriction_commutes K E L M σ.val _)

/-- Literal original infinite-completion coefficient inclusion is equivariant
for the actual decomposition-group restriction. -/
def originalInfiniteBaseChangeRepHom (v : InfinitePlace M) :
    Rep.res (originalInfiniteBaseChangeStabilizerHom K E L M v)
      (originalInfiniteUnitRep K L (v.comap (algebraMap L M))) ⟶
        originalInfiniteUnitRep E M v :=
  Rep.ofHom ⟨(Units.map (originalInfiniteCompletionBaseChange L M v).toMonoidHom).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    apply congrArg Additive.ofMul
    apply Units.ext
    exact originalInfiniteBaseChange_transport K E L M v σ x.toMul.val⟩

end
end Dubon2026

import Dubon2026.NumberFieldGaloisArchimedeanTransport

/-! # Coherence of the original archimedean transport

Identity and multiplication are verified on the same original global
elements and extended by density, as needed for the original idele action.
-/

namespace Dubon2026
noncomputable section
open NumberField UniformSpace
variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- Identity acts identically on each original archimedean completion. -/
theorem numberFieldGaloisArchimedeanTransport_one (v : InfinitePlace L) (x : v.Completion) :
    numberFieldGaloisArchimedeanTransport K L 1 v v (one_smul _ v) x = x := by
  induction x using Completion.induction_on
  · exact isClosed_eq (numberFieldGaloisArchimedeanTransport_continuous K L 1 v v _) continuous_id
  · rename_i x
    change numberFieldGaloisArchimedeanTransport K L 1 v v _
      (algebraMap L v.Completion x.ofAbs) = _
    rw [numberFieldGaloisArchimedeanTransport_algebraMap]
    rfl

/-- Products of original automorphisms compose their original archimedean transports. -/
theorem numberFieldGaloisArchimedeanTransport_mul (σ τ : Gal(L/K))
    (v u w : InfinitePlace L) (hτ : τ • v = u) (hσ : σ • u = w)
    (hστ : (σ * τ) • v = w) (x : v.Completion) :
    numberFieldGaloisArchimedeanTransport K L (σ * τ) v w hστ x =
      numberFieldGaloisArchimedeanTransport K L σ u w hσ
        (numberFieldGaloisArchimedeanTransport K L τ v u hτ x) := by
  induction x using Completion.induction_on
  · exact isClosed_eq (numberFieldGaloisArchimedeanTransport_continuous K L (σ * τ) v w hστ)
      ((numberFieldGaloisArchimedeanTransport_continuous K L σ u w hσ).comp
        (numberFieldGaloisArchimedeanTransport_continuous K L τ v u hτ))
  · rename_i x
    change numberFieldGaloisArchimedeanTransport K L (σ * τ) v w hστ
      (algebraMap L v.Completion x.ofAbs) =
        numberFieldGaloisArchimedeanTransport K L σ u w hσ
          (numberFieldGaloisArchimedeanTransport K L τ v u hτ
            (algebraMap L v.Completion x.ofAbs))
    rw [numberFieldGaloisArchimedeanTransport_algebraMap,
      numberFieldGaloisArchimedeanTransport_algebraMap,
      numberFieldGaloisArchimedeanTransport_algebraMap]
    rfl

end
end Dubon2026

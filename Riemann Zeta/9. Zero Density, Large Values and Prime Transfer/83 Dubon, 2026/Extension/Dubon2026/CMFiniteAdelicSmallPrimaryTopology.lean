import Dubon2026.CMFiniteAdelicSmallPrimaryLevel
import Dubon2026.CMFiniteAdelicSmallParabolicTopology

/-! # The original primary auxiliary unitary level is compact open

The primary level contains the original open row-one level and is
contained in the original compact upper level. This proves its exact
topological status, and the original quotient equivalence proves the
coefficient-primary group property needed by DUB-17's patching input.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {S : Type*} [Fintype S] (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
variable (H : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) (hH : star H = H)
variable (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
variable (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
variable (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t))
variable (w : HeightOneSpectrum (𝓞 K))
variable (hw : ∀ s, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s)) (q : ℕ)

/-- The original row-one auxiliary level lies in the actual primary auxiliary level. -/
theorem cmFiniteAdelicSmallParabolicOne_le_primary :
    cmFiniteAdelicSmallParabolicOne K v n H.val w ≤
      cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q := by
  intro M hM
  let m : cmFiniteAdelicSmallParabolicZero K v n H.val w :=
    ⟨M, cmFiniteAdelicSmallParabolicOne_le K v n H.val w hM⟩
  have hm : QuotientGroup.mk' ((cmFiniteAdelicSmallParabolicOne K v n H.val w).subgroupOf
      (cmFiniteAdelicSmallParabolicZero K v n H.val w)) m = 1 :=
    (QuotientGroup.eq_one_iff (N := (cmFiniteAdelicSmallParabolicOne K v n H.val w).subgroupOf
      (cmFiniteAdelicSmallParabolicZero K v n H.val w)) m).mpr hM
  refine ⟨m, ?_, rfl⟩
  change cmFiniteAdelicSmallPrimaryCharacter K v n H hH hv hlocal hsep w hw q m = 1
  simp only [cmFiniteAdelicSmallPrimaryCharacter, MonoidHom.comp_apply, hm, map_one]

/-- The actual primary auxiliary level is open in the full original unitary group. -/
theorem cmFiniteAdelicSmallPrimaryLevel_isOpen :
    IsOpen (cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q :
      Set (cmFiniteAdelicUnitaryGroup K H.val)) :=
  Subgroup.isOpen_mono (cmFiniteAdelicSmallParabolicOne_le_primary K v n H hH hv hlocal hsep w hw q)
    (cmFiniteAdelicSmallParabolicOne_isOpen K v n H.val w)

/-- The actual primary auxiliary level is compact in the full original unitary group. -/
theorem cmFiniteAdelicSmallPrimaryLevel_isCompact :
    IsCompact (cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q :
      Set (cmFiniteAdelicUnitaryGroup K H.val)) :=
  (cmFiniteAdelicSmallParabolicZero_isCompact K v n H.val w).of_isClosed_subset
    ((cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q).isClosed_of_isOpen
      (cmFiniteAdelicSmallPrimaryLevel_isOpen K v n H hH hv hlocal hsep w hw q))
    (cmFiniteAdelicSmallPrimaryLevel_le K v n H hH hv hlocal hsep w hw q)

/-- The quotient by the actual primary auxiliary unitary level is a coefficient-primary group. -/
theorem cmFiniteAdelicSmallPrimaryQuotient_isPGroup :
    IsPGroup q (cmFiniteAdelicSmallParabolicZero K v n H.val w ⧸
      (cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q).subgroupOf
        (cmFiniteAdelicSmallParabolicZero K v n H.val w)) :=
  (finitePlaceParabolicFamilyDelta_isPGroup K v n q).of_equiv
    (cmFiniteAdelicSmallPrimaryQuotientEquiv K v n H hH hv hlocal hsep w hw q).symm

end
end Dubon2026

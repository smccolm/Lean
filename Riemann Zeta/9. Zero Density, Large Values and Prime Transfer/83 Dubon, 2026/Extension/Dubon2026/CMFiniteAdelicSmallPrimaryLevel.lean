import Dubon2026.CMFiniteAdelicSmallParabolicQuotient

/-! # The actual maximal-primary auxiliary level in the unitary group

The quotient of the actual source parabolic levels is sent to its
proved original maximal-primary quotient. The kernel defines the
actual intermediate unitary level, with its quotient identified with
the source Delta. This is the group acting on DUB-17's actual integral
auxiliary automorphic module.
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

/-- The actual small unitary level maps to the original source maximal-primary quotient. -/
def cmFiniteAdelicSmallPrimaryCharacter :
    cmFiniteAdelicSmallParabolicZero K v n H.val w →* FinitePlaceParabolicFamilyDelta K v n q :=
  (QuotientGroup.mk' (finiteCommutativePrimaryKernel (FinitePlaceParabolicFamilyQuotient K v n) q)).comp
    ((cmFiniteAdelicSmallParabolicQuotientEquiv K v n H hH hv hlocal hsep w hw).toMonoidHom.comp
      (QuotientGroup.mk' ((cmFiniteAdelicSmallParabolicOne K v n H.val w).subgroupOf
        (cmFiniteAdelicSmallParabolicZero K v n H.val w))))

/-- The actual original unitary intermediate level cuts out precisely the source maximal-primary quotient. -/
def cmFiniteAdelicSmallPrimaryLevel : Subgroup (cmFiniteAdelicUnitaryGroup K H.val) :=
  (cmFiniteAdelicSmallPrimaryCharacter K v n H hH hv hlocal hsep w hw q).ker.map
    (cmFiniteAdelicSmallParabolicZero K v n H.val w).subtype

/-- The actual primary auxiliary level is contained in the actual upper level. -/
theorem cmFiniteAdelicSmallPrimaryLevel_le :
    cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q ≤
      cmFiniteAdelicSmallParabolicZero K v n H.val w :=
  Subgroup.map_subtype_le _

/-- Restricting the actual intermediate level back to the upper level recovers the exact primary character kernel. -/
theorem cmFiniteAdelicSmallPrimaryLevel_kernel :
    (cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q).subgroupOf
      (cmFiniteAdelicSmallParabolicZero K v n H.val w) =
        (cmFiniteAdelicSmallPrimaryCharacter K v n H hH hv hlocal hsep w hw q).ker :=
  (cmFiniteAdelicSmallPrimaryCharacter K v n H hH hv hlocal hsep w hw q).ker.comap_map_eq_self_of_injective
    Subtype.val_injective

/-- The actual primary intermediate unitary level is normal in the actual upper level. -/
instance cmFiniteAdelicSmallPrimaryLevel_normal :
    ((cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q).subgroupOf
      (cmFiniteAdelicSmallParabolicZero K v n H.val w)).Normal := by
  rw [cmFiniteAdelicSmallPrimaryLevel_kernel]
  infer_instance

/-- The original primary character on the actual unitary level is surjective. -/
theorem cmFiniteAdelicSmallPrimaryCharacter_surjective :
    Function.Surjective (cmFiniteAdelicSmallPrimaryCharacter K v n H hH hv hlocal hsep w hw q) :=
  (QuotientGroup.mk'_surjective _).comp
    ((cmFiniteAdelicSmallParabolicQuotientEquiv K v n H hH hv hlocal hsep w hw).surjective.comp
      (QuotientGroup.mk'_surjective _))

/-- The quotient by the actual primary unitary level is the original source Delta, with its multiplication preserved. -/
def cmFiniteAdelicSmallPrimaryQuotientEquiv :
    cmFiniteAdelicSmallParabolicZero K v n H.val w ⧸
      (cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q).subgroupOf
        (cmFiniteAdelicSmallParabolicZero K v n H.val w) ≃* FinitePlaceParabolicFamilyDelta K v n q :=
  (QuotientGroup.quotientMulEquivOfEq
    (cmFiniteAdelicSmallPrimaryLevel_kernel K v n H hH hv hlocal hsep w hw q)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (cmFiniteAdelicSmallPrimaryCharacter_surjective K v n H hH hv hlocal hsep w hw q))

/-- The actual unitary primary auxiliary quotient is finite by its original arithmetic realization. -/
theorem cmFiniteAdelicSmallPrimaryQuotient_finite :
    Finite (cmFiniteAdelicSmallParabolicZero K v n H.val w ⧸
      (cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q).subgroupOf
        (cmFiniteAdelicSmallParabolicZero K v n H.val w)) :=
  Finite.of_equiv (FinitePlaceParabolicFamilyDelta K v n q)
    (cmFiniteAdelicSmallPrimaryQuotientEquiv K v n H hH hv hlocal hsep w hw q).symm.toEquiv

end
end Dubon2026

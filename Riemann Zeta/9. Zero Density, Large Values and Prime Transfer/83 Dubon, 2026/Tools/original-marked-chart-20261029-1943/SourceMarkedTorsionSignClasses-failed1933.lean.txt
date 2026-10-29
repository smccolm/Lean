import Dubon2026.SourceCyclicPairOrder

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original marked
chart -> stabilizer comparison. Count actual points of exact order N up to
sign. The native torsion structure will transport the residue-pair count
to the original elliptic point group. Only this sign quotient is needed;
the reference's general subgroup-of-units orbit construction is deferred.
Route adapted from anthropics/fermats-last-theorem (Apache-2.0), commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index.lean. -/
namespace Dubon2026.SourceFunctionField.MarkedTorsion
noncomputable section

/-- The actual unordered sign pairs of points of exact order N. -/
def SignClasses (A : Type*) [AddCommGroup A] (N : ℕ) :=
  {s : Set A // ∃ P : A, addOrderOf P = N ∧ s = {P, -P}}

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {N : ℕ}

theorem signPair_eq_iff (P Q : A) :
    ({P, -P} : Set A) = {Q, -Q} ↔ P = Q ∨ P = -Q := by
  constructor
  · intro h
    have hP : P ∈ ({Q, -Q} : Set A) := h ▸ Set.mem_insert P {-P}
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hP
  · rintro (rfl | rfl)
    · rfl
    · simp only [neg_neg, Set.pair_comm]

/-- Map sign classes through an injective homomorphism of the actual groups. -/
def mapSignClasses (m : A →+ B) (hm : Function.Injective m)
    (s : SignClasses A N) : SignClasses B N :=
  ⟨m '' s.val, by
    obtain ⟨P, hP, hs⟩ := s.property
    refine ⟨m P, (addOrderOf_injective m hm P).trans hP, ?_⟩
    rw [hs, Set.image_pair, map_neg]⟩

theorem mapSignClasses_injective (m : A →+ B) (hm : Function.Injective m) :
    Function.Injective (mapSignClasses (N := N) m hm) := by
  intro s t h
  apply Subtype.ext
  exact (Set.image_injective.mpr hm) (congrArg Subtype.val h)

/-- The torsion basis gives an equivalence of the actual sign-class carriers. -/
def torsionSignClassesEquiv
    (e : ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ A N) :
    SignClasses (ZMod N × ZMod N) N ≃ SignClasses A N := by
  let m : ZMod N × ZMod N →+ A :=
    (Submodule.torsionBy ℤ A N).subtype.toAddMonoidHom.comp e.toAddMonoidHom
  have hm : Function.Injective m := Subtype.val_injective.comp e.injective
  apply Equiv.ofBijective (mapSignClasses m hm)
  refine ⟨mapSignClasses_injective m hm, ?_⟩
  intro s
  obtain ⟨P, hP, hs⟩ := s.property
  have hPN : P ∈ Submodule.torsionBy ℤ A N := by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← hP]
    exact addOrderOf_nsmul_eq_zero P
  let v : ZMod N × ZMod N := e.symm ⟨P, hPN⟩
  have hv : m v = P := congrArg Subtype.val (e.apply_symm_apply ⟨P, hPN⟩)
  have hvord : addOrderOf v = N := by
    rw [← addOrderOf_injective m hm v, hv, hP]
  refine ⟨⟨{v, -v}, v, hvord, rfl⟩, Subtype.ext ?_⟩
  change m '' ({v, -v} : Set (ZMod N × ZMod N)) = s.val
  rw [Set.image_pair, map_neg, hv, hs]

theorem natCard_signClasses_of_torsion_equiv
    (e : ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ A N) :
    Nat.card (SignClasses A N) = Nat.card (SignClasses (ZMod N × ZMod N) N) :=
  (Nat.card_congr (torsionSignClassesEquiv e)).symm

end
end Dubon2026.SourceFunctionField.MarkedTorsion

import GafniTao.FordPrimePacketEventually

/-!
# Monotonicity of Ford's complete finite counts

Ford's Lemma 3.4 enlarges the `Q`-box after applying Lemma 3.2.  This file
implements that source step by an explicit injection of solution types.  The
embedding preserves the represented positive integers, hence every equation
and congruence literally survives the enlargement.
-/

namespace GafniTao

noncomputable section

def fordBoxCastLE {n Q R : ℕ} (hQR : Q ≤ R) :
    FordBox n Q ↪ FordBox n R where
  toFun x i := Fin.castLE hQR (x i)
  inj' := by
    intro x y hxy
    funext i
    apply Fin.ext
    exact congrArg (fun z : Fin R => z.val) (congrFun hxy i)

@[simp] theorem fordBoxValue_fordBoxCastLE
    {n Q R : ℕ} (hQR : Q ≤ R) (x : FordBox n Q) (i : Fin n) :
    fordBoxValue (fordBoxCastLE hQR x) i = fordBoxValue x i := by
  rfl

def fordKVariablesCastQLE {k s P Q R : ℕ} (hQR : Q ≤ R) :
    FordKVariables k s P Q ↪ FordKVariables k s P R where
  toFun v := (v.1,
    (fordBoxCastLE hQR v.2.1, fordBoxCastLE hQR v.2.2))
  inj' := by
    intro v w hvw
    rcases v with ⟨vzw, vxy⟩
    rcases w with ⟨wzw, wxy⟩
    simp only [Prod.mk.injEq] at hvw ⊢
    refine ⟨hvw.1, ?_⟩
    exact Prod.ext
      ((fordBoxCastLE hQR).injective hvw.2.1)
      ((fordBoxCastLE hQR).injective hvw.2.2)

theorem fordPowerDifference_fordBoxCastLE
    {n Q R : ℕ} (hQR : Q ≤ R) (x y : FordBox n Q) (J : ℕ) :
    fordPowerDifference (fordBoxCastLE hQR x) (fordBoxCastLE hQR y) J =
      fordPowerDifference x y J := by
  simp [fordPowerDifference, fordBoxCastLE, fordBoxValue]

theorem fordKEquation_fordKVariablesCastQLE
    {k d T s P Q R q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hQR : Q ≤ R)
    (v : FordKVariables k s P Q) (hv : FordKEquation Ψ q v) :
    FordKEquation Ψ q (fordKVariablesCastQLE hQR v) := by
  intro j
  simpa [fordKVariablesCastQLE, fordPowerDifference_fordBoxCastLE] using hv j

def fordKSolutionCastQLE
    {k d T s P Q R q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hQR : Q ≤ R) :
    {v : FordKVariables k s P Q // FordKEquation Ψ q v} ↪
      {v : FordKVariables k s P R // FordKEquation Ψ q v} where
  toFun v := ⟨fordKVariablesCastQLE hQR v.1,
    fordKEquation_fordKVariablesCastQLE Ψ hQR v.1 v.2⟩
  inj' := by
    intro v w hvw
    apply Subtype.ext
    exact (fordKVariablesCastQLE hQR).injective (congrArg Subtype.val hvw)

theorem fordKCount_mono_Q
    {k d T s P Q R q : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hQR : Q ≤ R) :
    fordKCount Ψ s P Q q ≤ fordKCount Ψ s P R q := by
  exact Fintype.card_le_of_injective (fordKSolutionCastQLE Ψ hQR)
    (fordKSolutionCastQLE Ψ hQR).injective

theorem fordLCongruence_fordKVariablesCastQLE
    {k s P Q R p r : ℕ} (hQR : Q ≤ R)
    (v : FordLVariables k s P Q) (hv : FordLCongruence p r v) :
    FordLCongruence p r (fordKVariablesCastQLE hQR v) := by
  intro i
  simpa [fordKVariablesCastQLE] using hv i

theorem fordLEquation_fordKVariablesCastQLE
    {k d T s P Q R p q r : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hQR : Q ≤ R)
    (v : FordLVariables k s P Q) (hv : FordLEquation Ψ p q r v) :
    FordLEquation Ψ p q r (fordKVariablesCastQLE hQR v) := by
  refine ⟨fordLCongruence_fordKVariablesCastQLE hQR v hv.1, ?_⟩
  intro j
  simpa [fordKVariablesCastQLE, fordPowerDifference_fordBoxCastLE] using hv.2 j

def fordLSolutionCastQLE
    {k d T s P Q R p q r : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hQR : Q ≤ R) :
    {v : FordLVariables k s P Q // FordLEquation Ψ p q r v} ↪
      {v : FordLVariables k s P R // FordLEquation Ψ p q r v} where
  toFun v := ⟨fordKVariablesCastQLE hQR v.1,
    fordLEquation_fordKVariablesCastQLE Ψ hQR v.1 v.2⟩
  inj' := by
    intro v w hvw
    apply Subtype.ext
    exact (fordKVariablesCastQLE hQR).injective (congrArg Subtype.val hvw)

/-- The exact monotonicity in `Q` used in Ford Lemma 3.4. -/
theorem fordLCount_mono_Q
    {k d T s P Q R p q r : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T) (hQR : Q ≤ R) :
    fordLCount Ψ s P Q p q r ≤ fordLCount Ψ s P R p q r := by
  exact Fintype.card_le_of_injective (fordLSolutionCastQLE Ψ hQR)
    (fordLSolutionCastQLE Ψ hQR).injective

#print axioms fordKCount_mono_Q
#print axioms fordLCount_mono_Q

end

end GafniTao

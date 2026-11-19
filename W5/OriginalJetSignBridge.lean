import W5.OriginalPsiJet
import W5.ThetaIntegralStrictPositivity

/-!
# Exact remaining obligations for the original order-five claim

The original theta-jet matrix is proven equal to the genuine
Wronskian, with all derivatives through order eight justified.
Thus only the four determinant signs remain. This is an
explicit conditional reduction, NOT a proof of those signs.
-/

namespace W5

/-- A sign certificate for the original, analytically justified
theta-jet matrix. This does not use the normalized coefficient
matrix or assume that an external numerical computation is sound. -/
def OriginalJetSignCertificate : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (Matrix.of (fun (i j : Fin 2) =>
      originalPsiJet (i.val + j.val) t)).det < 0 ∧
    (Matrix.of (fun (i j : Fin 3) =>
      originalPsiJet (i.val + j.val) t)).det < 0 ∧
    0 < (Matrix.of (fun (i j : Fin 4) =>
      originalPsiJet (i.val + j.val) t)).det ∧
    0 < (Matrix.of (fun (i j : Fin 5) =>
      originalPsiJet (i.val + j.val) t)).det

/-- The four original theta-jet signs, together with the
already proven strict W1 sign, suffice for the entire claim. -/
theorem mainClaim_of_originalJetSignCertificate
    (h : OriginalJetSignCertificate) : MainClaim := by
  intro t ht
  obtain ⟨h2, h3, h4, h5⟩ := h t ht
  refine ⟨W_one_pos t ht, ?_, ?_, ?_, ?_⟩
  · rw [W_eq_originalPsiJet_det 2 (by omega) t]
    exact h2
  · rw [W_eq_originalPsiJet_det 3 (by omega) t]
    exact h3
  · rw [W_eq_originalPsiJet_det 4 (by omega) t]
    exact h4
  · rw [W_eq_originalPsiJet_det 5 (by omega) t]
    exact h5

/-- In fact, the remaining sign certificate is logically equivalent
to the full claim; the r=1 component is already unconditional. -/
theorem originalJetSignCertificate_iff_mainClaim :
    OriginalJetSignCertificate ↔ MainClaim := by
  constructor
  · exact mainClaim_of_originalJetSignCertificate
  · intro h t ht
    obtain ⟨_, h2, h3, h4, h5⟩ := h t ht
    constructor
    · rwa [← W_eq_originalPsiJet_det 2 (by omega) t]
    constructor
    · rwa [← W_eq_originalPsiJet_det 3 (by omega) t]
    constructor
    · rwa [← W_eq_originalPsiJet_det 4 (by omega) t]
    · rwa [← W_eq_originalPsiJet_det 5 (by omega) t]

end W5

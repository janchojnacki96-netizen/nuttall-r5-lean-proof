import Nuttall.PhiJetCoefficients

namespace Nuttall

/-- Tabulate the existing integer recurrence one whole row at a time. -/
private def auxiliaryJetRow (width : ℕ) : ℕ → Vector ℤ width
  | 0 => Vector.ofFn fun k => if k.val = 0 then 1 else 0
  | j + 1 =>
    let old := auxiliaryJetRow width j
    Vector.ofFn fun k =>
      match h : k.val with
      | 0 => -5 * old[0]'(by omega)
      | m + 1 => 4 * old[m]'(by omega) - (5 + 4 * (m + 1 : ℕ)) * old[m+1]'(by omega)

private theorem auxiliaryJetRow_getElem (width j k : ℕ) (hk : k < width) :
    (auxiliaryJetRow width j)[k] = auxiliaryJetCoeff j k := by
  induction j generalizing k with
  | zero => simp [auxiliaryJetRow, auxiliaryJetCoeff]
  | succ j ih =>
    cases k with
    | zero => simp [auxiliaryJetRow, auxiliaryJetCoeff, ih 0 hk]
    | succ k => simp [auxiliaryJetRow, auxiliaryJetCoeff, ih k (by omega), ih (k+1) hk]

/-- The rational coefficient row used by the finite theta interval evaluator. -/
def phiJetCoeffRow (j : ℕ) : Vector ℚ (j+2) :=
  let lo := auxiliaryJetRow (j+2) j
  let hi := auxiliaryJetRow (j+2) (j+1)
  Vector.ofFn fun k => ((-1 : ℚ)^j / 2) * ((hi[k.val] : ℚ) - (lo[k.val] : ℚ))

theorem phiJetCoeffRow_getElem (j k : ℕ) (hk : k < j+2) :
    (phiJetCoeffRow j)[k] = phiJetCoeff j k := by
  simp [phiJetCoeffRow, phiJetCoeff, auxiliaryJetRow_getElem]

end Nuttall

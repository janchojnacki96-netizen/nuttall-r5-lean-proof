import W5.ThetaCompactReplaySoundness

/-!
# The verified final cell reduces the residual proof from 48 to 47

This is a logical chain composition only. The first three original cells
and the last original cell are unconditional established certificates.
Everything between them is explicitly represented as a 47-cell chain.
-/

namespace W5

theorem thetaCompactReplayCellChain_append
    (bs cs : List ℚ) (a : ℚ)
    (hprefix : ThetaUpperRealCellCertificateChain a bs)
    (hsuffix : ThetaUpperRealCellCertificateChain (lastFrom a bs) cs) :
    ThetaUpperRealCellCertificateChain a (bs ++ cs) := by
  induction bs generalizing a with
  | nil => simpa only [List.nil_append, lastFrom] using hsuffix
  | cons b bs ih =>
      have hp : ThetaUpperRealCellCertificate a b ∧
          ThetaUpperRealCellCertificateChain b bs := hprefix
      have ht : ThetaUpperRealCellCertificateChain (lastFrom b bs) cs := hsuffix
      change ThetaUpperRealCellCertificate a b ∧
        ThetaUpperRealCellCertificateChain b (bs ++ cs)
      exact ⟨hp.1, ih b hp.2 ht⟩

def thetaRemaining47Endpoints : List ℚ := (endpoints.drop 3).take 47

theorem thetaRemaining47Endpoints_count : thetaRemaining47Endpoints.length = 47 := by
  native_decide

theorem thetaRemaining47Endpoints_append :
    thetaRemaining47Endpoints ++ [endpoints.reverse.head!] = endpoints.drop 3 := by
  native_decide

theorem thetaRemaining47Endpoints_last :
    lastFrom (821/2048:ℚ) thetaRemaining47Endpoints = (endpoints.reverse.drop 1).head! := by
  native_decide

theorem analyticMatrixPositive_of_remaining_47_upper_certificates
    (h47 : ThetaUpperRealCellCertificateChain (821/2048:ℚ) thetaRemaining47Endpoints) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_48_upper_certificates
  rw [← thetaRemaining47Endpoints_append]
  apply thetaCompactReplayCellChain_append thetaRemaining47Endpoints
    [endpoints.reverse.head!] (821/2048:ℚ) h47
  rw [thetaRemaining47Endpoints_last]
  exact ⟨thetaLastCellCertificate, trivial⟩

end W5

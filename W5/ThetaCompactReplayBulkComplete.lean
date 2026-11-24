import W5.ThetaCompactReplayPilotCertificates
import W5.ThetaCompactReplayBulkGroup0
import W5.ThetaCompactReplayBulkGroup1
import W5.ThetaCompactReplayBulkGroup2
import W5.ThetaCompactReplayBulkGroup3
import W5.ThetaCompactReplayBulkGroup4
import W5.ThetaCompactReplayBulkGroup5

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaRemaining47CompactReplayChain :
    ThetaUpperRealCellCertificateChain (821/2048:ℚ) thetaRemaining47Endpoints := by
  have hs : (821/2048:ℚ) = (0::endpoints)[3]! := by native_decide
  have he : thetaRemaining47Endpoints = [endpoints[3]!, endpoints[4]!, endpoints[5]!, endpoints[6]!, endpoints[7]!, endpoints[8]!, endpoints[9]!, endpoints[10]!, endpoints[11]!, endpoints[12]!, endpoints[13]!, endpoints[14]!, endpoints[15]!, endpoints[16]!, endpoints[17]!, endpoints[18]!, endpoints[19]!, endpoints[20]!, endpoints[21]!, endpoints[22]!, endpoints[23]!, endpoints[24]!, endpoints[25]!, endpoints[26]!, endpoints[27]!, endpoints[28]!, endpoints[29]!, endpoints[30]!, endpoints[31]!, endpoints[32]!, endpoints[33]!, endpoints[34]!, endpoints[35]!, endpoints[36]!, endpoints[37]!, endpoints[38]!, endpoints[39]!, endpoints[40]!, endpoints[41]!, endpoints[42]!, endpoints[43]!, endpoints[44]!, endpoints[45]!, endpoints[46]!, endpoints[47]!, endpoints[48]!, endpoints[49]!] := by native_decide
  rw [hs, he]
  exact ⟨thetaOriginalCell04_compactReplay,
    thetaOriginalCell05_compactReplay,
    thetaOriginalCell06_compactReplay,
    thetaOriginalCell07_compactReplay,
    thetaOriginalCell08_compactReplay,
    thetaOriginalCell09_compactReplay,
    thetaOriginalCell10_compactReplay,
    thetaOriginalCell11_compactReplay,
    thetaOriginalCell12_compactReplay,
    thetaOriginalCell13_compactReplay,
    thetaOriginalCell14_compactReplay,
    thetaOriginalCell15_compactReplay,
    thetaOriginalCell16_compactReplay,
    thetaOriginalCell17_compactReplay,
    thetaOriginalCell18_compactReplay,
    thetaOriginalCell19_compactReplay,
    thetaOriginalCell20_compactReplay,
    thetaOriginalCell21_compactReplay,
    thetaOriginalCell22_compactReplay,
    thetaOriginalCell23_compactReplay,
    thetaOriginalCell24_compactReplay,
    thetaOriginalCell25_compactReplay,
    thetaOriginalCell26_compactReplay,
    thetaOriginalCell27_compactReplay,
    thetaOriginalCell28_compactReplay,
    thetaOriginalCell29_compactReplay,
    thetaOriginalCell30_compactReplay,
    thetaOriginalCell31_compactReplay,
    thetaOriginalCell32_compactReplay,
    thetaOriginalCell33_compactReplay,
    thetaOriginalCell34_compactReplay,
    thetaOriginalCell35_compactReplay,
    thetaOriginalCell36_compactReplay,
    thetaOriginalCell37_compactReplay,
    thetaOriginalCell38_compactReplay,
    thetaOriginalCell39_compactReplay,
    thetaOriginalCell40_compactReplay,
    thetaOriginalCell41_compactReplay,
    thetaOriginalCell42_compactReplay,
    thetaOriginalCell43_compactReplay,
    thetaOriginalCell44_compactReplay,
    thetaOriginalCell45_compactReplay,
    thetaOriginalCell46_compactReplay,
    thetaOriginalCell47_compactReplay,
    thetaOriginalCell48_compactReplay,
    thetaOriginalCell49_compactReplay,
    thetaOriginalCell50_compactReplay, trivial⟩

theorem analyticMatrixPositive_compactReplay : analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_47_upper_certificates thetaRemaining47CompactReplayChain

#print axioms analyticMatrixPositive_compactReplay

end W5

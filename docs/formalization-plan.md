# Plan formalizacji preprintu Jana Chojnackiego o hipotezie Nuttalla (wersja 7)

Gałąź robocza: `formalization/preprint`. Źródła: [artykuł EN](../papers/linear-bounds/EN/main.tex), [artykuł PL](../papers/linear-bounds/PL/main.tex), [suplement z danymi](../papers/linear-bounds/certificates.zip). Numery twierdzeń i oznaczenia w tej notatce odnoszą się do wersji 7. Gdy zmienia się tekst pracy, porównaj tezy i zaktualizuj tylko zależne zadania.

## Stan i kolejność pracy

| Etap | Zależności | Stan i warunek ukończenia |
|---|---|---|
| B. Istniejące R5 | przypięta rewizja | **Zweryfikowany.** [W5.nuttall_r5](../W5/NuttallR5.lean), rewizja `dfaede6d`, [CI](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45486606898). Ścisłe znaki dla pierwszej całki na całej półosi. Audyt wykazuje 228 aksjomatów obliczeń natywnych obok trzech standardowych. |
| A. Definicje i przejście od wrońskianów do RR | W5.Statement, CentralEvaluationPositivity | **Częściowo.** [ReverseSignRegularity.lean](../Nuttall/ReverseSignRegularity.lean) definiuje słabe RR i m(r) oraz przenosi ścisły test na wyznaczniki jądra dla każdego m. [WronskianObstruction.lean](../Nuttall/WronskianObstruction.lean) wyklucza słabe RR przez zły znak wrońskianu i wyprowadza dolną granicę m(r). Słabe RR zachowuje się przy całkowaniu ogonowym. Pozostaje zachowanie ścisłych znaków wrońskianów. |
| U. Analityczny dowód dla dużych rzędów, tw. 1.2 | A; U1–U4 poniżej | **Zweryfikowany w Lean.** [AnalyticUpperBound.lean](../Nuttall/AnalyticUpperBound.lean) dowodzi istnienia skutecznego poziomu dla każdego r oraz m(r)≤2r dla dostatecznie dużych r, w słabej konwencji z preprintu. |
| F. Jawna granica 2r dla wszystkich r, tw. 4.1 | U, wspólny checker, §2.4 i dod. A | **Otwarte.** Zamknąć wszystkie pięć zakresów r z tabeli §4.2. |
| S. Dokładne minima do 8, tw. 2.1 | A, B, checker, §2.4 | **Częściowo.** Pełny dowód m(r)=0 dla r≤4, dolny świadek dla r≥5 i dolna granica m(8)≥2 przeszły CI. Dla m(5)=1 połączenie z wcześniej zweryfikowanym `W5.nuttall_r5` ma osobny cel odtworzenia. Dla Ψ₁ przez rząd 7 sprawdzono w Lean trzy z 67 komórek (pierwszą, 60 i ostatnią) oraz pokrycie siatki. Do sprawdzenia pozostają 64 komórki Ψ₁, ogon oraz górna granica rzędu 8 dla Ψ₂. |
| L. Dolna granica asymptotyczna, tw. 3.1 | A, §3; niezależne od U/F | **Otwarte.** Zachować współczynnik π²/2, dowolne ε>0 i kwantyfikator „dla wszystkich dostatecznie dużych r”. |
| H. Świadkowie 142 i 500, tw. 5.1 i wn. 5.2 | A, checker i dane §5; F dla górnych granic | **Otwarte.** Udowodnić znaki w konkretnych punktach i wykluczyć niższe poziomy. |
| D. Wyznaczniki momentów, tw. 6.2 i dod. C | F dla pierwszego wiersza; pozostałe ścieżki z dod. C | **Otwarte.** Sześć wierszy z właściwymi warunkami i progami. |
| K. Wnioski i pierwszy węzeł, wn. 6.1 i tw. 6.3 | L+F dla asymptotyki; osobny dowód dla węzła | **Otwarte.** Złożyć granice i udowodnić lokalną zmianę znaku pomocniczego wrońskianu. |
| Z. Audyt końcowy | A–K | **Otwarte.** Zbudować wszystkie eksportowane twierdzenia i wykonać procedurę odbioru poniżej. |

**U1 — zweryfikowana tożsamość różniczkowa.** [`Nuttall.twice_phi_eq_neg_deriv_add`](../Nuttall/ThetaAuxiliary.lean) dowodzi 2Φ = −(g′+g) dla każdego t∈ℝ. Dowód przechodzi do całego szeregu przez lokalną sumowalną majorantę gaussowską. [CI commita `5993a9b`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45968883067) pokazuje trzy standardowe aksjomaty Lean i odtworzenie modułów z częściowego cache zapisanego po [poprzednim błędzie](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45968606192).

**U1 — zweryfikowana pierwsza całka ogonowa.** Deklaracja [`Nuttall.twice_psi_one_eq_auxiliary_sub_tail`](../Nuttall/ThetaAuxiliaryIntegral.lean) dowodzi 2Ψ₁(t) = g(t) − ∫ₜ^∞ g(s) ds dla t≥0. Moduł dowodzi 0≤g≤Φ na tej półosi, całkowalności g i ograniczenia g(t)≤g(0)exp(−t). [CI commita `3120b85`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45969867996) pokazuje trzy standardowe aksjomaty oraz odtworzenie cache z pierwszej próby budowy.

**U1 — zweryfikowane dowolne iteracje.** [`Nuttall.twice_psi_succ_eq_auxiliary_iterate_sub`](../Nuttall/TailIteration.lean) dowodzi 2Ψⱼ₊₁(t) = bⱼᵍ(t) − bⱼ₊₁ᵍ(t) dla każdego j∈ℕ i t≥0. Teorematy `tailIterate_auxiliary_integrableOn` i `psi_integrableOn` zapewniają całkowalność od każdego rzeczywistego t. [CI commita `69b616a`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45970770365) potwierdziło trzy standardowe aksjomaty Lean oraz odtworzenie częściowego cache.

**U1 — pochodne i wpisy wrońskianu zweryfikowane.** [`Nuttall.iteratedDeriv_psi` i `Nuttall.wronskian_psi_eq_det`](../Nuttall/PsiDerivatives.lean) dowodzą wzoru na k-tą pochodną Ψₘ dla k≤m na ℝ oraz zapisują cały wrońskian w całkach ogonowych dla 2(p−1)≤m. `tailIntegral_hasDerivAt` jest wspólnym lematem dla Ψ i iteracji g. [CI commita `0abde4c`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45971749592) potwierdziło trzy standardowe aksjomaty obu deklaracji i odtworzenie częściowego cache.

**U1 — podpisany wyznacznik zweryfikowany.** [`Nuttall.signed_wronskian_psi_eq_tail_det`](../Nuttall/SignedTailDeterminant.lean) daje εₚWₚ(Ψₘ;t) = det[Ψ_{m−(p−1)+i−j}(t)] dla 2(p−1)≤m i t∈ℝ. Dowód wylicza znak odwrócenia z liczby inwersji, usuwa przez parę skalowań znaki wpisów i uzasadnia indeksy w ℕ. [CI commita `667cfcd`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45972673587) potwierdza trzy standardowe aksjomaty i odtworzenie częściowego cache.

**U1 — postać momentowa zweryfikowana.** Deklaracja [`Nuttall.tailIterate_auxiliary_eq_moment`](../Nuttall/TailMoments.lean) dowodzi dla każdego j∈ℕ i t≥0, że bⱼ₊₁ᵍ(t) jest całką z (s−t)ʲ g(s) na [t,∞) podzieloną przez j!. Moduł sprawdza całkowalność funkcji na obszarze t≤u≤s i stosuje Fubiniego w kroku indukcji. [CI commita `16acdc0`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45973785279) potwierdza trzy standardowe aksjomaty i odtworzenie częściowego cache.

**U1 — wyznacznik momentowy zweryfikowany.** [`Nuttall.twice_psi_succ_succ_eq_weighted_moment`](../Nuttall/TailMoments.lean) łączy dwa momenty w jedną całkę z różnicą wag. [`Nuttall.twice_pow_signed_wronskian_eq_moment_det`](../Nuttall/WeightedMomentDeterminant.lean) zastępuje wszystkie wpisy podpisanego wyznacznika tymi całkami i rozlicza skalar 2ᵖ. Warunki to 2p≤m i t≥0, więc wynik obejmuje m=2r, p≤r z §4.1. [CI commita `4025de3`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45974858966) potwierdza trzy standardowe aksjomaty obu twierdzeń oraz odtworzenie częściowego cache.

**U1 — rachunek wag i pochodnych składników zweryfikowany.** [`Nuttall.iteratedDeriv_tailMomentWeight_zero`](../Nuttall/MomentWeightCalculus.lean) daje zerowy wyraz brzegowy przy s=t dla każdej pochodnej o rzędzie mniejszym od indeksu wagi. Ten sam moduł identyfikuje k-tą pochodną z wagą o indeksie obniżonym o k. [`Nuttall.iteratedDeriv_auxiliarySummand`](../Nuttall/AuxiliaryDerivativePolynomials.lean) dowodzi dla wszystkich j,n i t∈ℝ wzoru na pochodną gₙ z wielomianem Pⱼ, gdzie P₀=1 i Pⱼ₊₁=(4x−5)Pⱼ−4xPⱼ′. [CI commita `aca9b39`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45975913101) potwierdza trzy standardowe aksjomaty obu twierdzeń i odtworzenie częściowego cache.

### Dziesięć zweryfikowanych kroków U1

Wszystkie pozycje sprawdzono w `lake build Nuttall` dla commita `68dc9c5`. [Zielony przebieg i audyt aksjomatów](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45977797685/job/140433808089)

| Krok | Deklaracja | Formalny wynik |
|---|---|---|
| 1 | [`auxiliaryWeightedSummand_summable`](../Nuttall/AuxiliarySeries.lean) | Sumowalność szeregu gₙP(xₙ) dla każdego wielomianu P, z lokalnie jednostajną majorantą gaussowską. |
| 2 | [`iteratedDeriv_auxiliaryTheta`](../Nuttall/AuxiliarySeries.lean) | Różniczkowanie całego szeregu g wyraz po wyrazie w każdym rzędzie i dla każdego t∈ℝ. |
| 3 | [`auxiliaryWeightedSeries_decay`](../Nuttall/AuxiliarySeries.lean) | Dla każdego P istnieje stała C≥0 ograniczająca normę szeregu przez Cexp(−t) dla t≥0. |
| 4 | [`weight_mul_signedJet_integrable` i `weight_mul_signedJet_tendsto_zero`](../Nuttall/TailIntegrationByParts.lean) | Iloczyny wag i pochodnych są całkowalne na [t,∞) i zanikają w nieskończoności. |
| 5 | [`integral_weight_signedJet_succ`](../Nuttall/TailIntegrationByParts.lean) | Pojedyncze całkowanie przez części. Oba wyrazy brzegowe znikają. |
| 6 | [`integral_weight_signedJet`](../Nuttall/TailIntegrationByParts.lean) | Powtórzenie całkowania przez części j razy przy j≤k dla wagi indeksu k. |
| 7 | [`twice_pow_signed_wronskian_eq_separated_moments`](../Nuttall/TailIntegrationByParts.lean) | Wiersz wyznacza wagę, a kolumna rząd pochodnej w każdym wpisie podpisanego wyznacznika przy m≥2p. |
| 8 | [`auxiliaryDerivativePolynomial_degree_coeff`](../Nuttall/AuxiliaryVandermonde.lean) | Wielomian pochodnej ma stopień ≤j, a współczynnik przy xʲ wynosi 4ʲ. |
| 9 | [`det_auxiliary_weighted_summands`](../Nuttall/AuxiliaryVandermonde.lean) | Dla ustalonej krotki indeksów wyznacznik sprowadza się do Vandermonde’a, iloczynu składników gₙ i iloczynu współczynników 4ʲ. |
| 10 | [`signed_wronskian_eq_andreief_integral`](../Nuttall/ThetaAndreief.lean) | Pierwsza reprezentacja całką wielokrotną. Lean sprawdza całkowalność wszystkich par wag i pochodnych oraz czynnik p!2ᵖ. |

Kroki 1–9 zależą od trzech standardowych aksjomatów Lean. Krok 10 korzysta dodatkowo z klasycznej tożsamości Andréiefa, zadeklarowanej w [module literatury](../Nuttall/Literature/Andreief.lean). CI wykorzystało częściowy cache z poprzedniego przebiegu. Błędy dotyczyły sposobu zapisania iloczynów i granic funkcji w Lean.

### Przesunięcie i rozwinięcie całki — dziesięć zweryfikowanych kroków

Cały moduł `Nuttall` przeszedł kompilację commita `d56f9b4`. Równolegle z CI opracowano algebrę przesunięcia, translację miary oraz rozwinięcie wyznaczników. Weryfikacja przyrostowa korzysta z lokalnych plików Mathlib i cache projektu w CI. Nowe lematy analityczne i algebraiczne używają standardowych aksjomatów Lean, a granica całek wielokrotnych korzysta także z przyjętej wcześniej tożsamości Andréiefa. [Zielone CI i audyt](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45981321293/job/140445649368)

| Krok | Deklaracja lub moduł | Wynik |
|---|---|---|
| 1 | [`thetaKnot_lt_iff` i `auxiliaryCoordinate_shift`](../Nuttall/ShiftedThetaAlgebra.lean) | Warunek aktywności n<exp(2u) i zmiana argumentu theta na X exp(4u). |
| 2 | [`auxiliarySummand_shift`](../Nuttall/ShiftedThetaAlgebra.lean) | Przesunięty składnik daje wagę exp(5u−Xexp(4u)) i czynnik 1/√n. |
| 3 | [`det_auxiliary_summands_shift`](../Nuttall/ShiftedThetaAlgebra.lean) | Vandermonde po zmianie zmiennych i pełny czynnik skalujący pojedynczą krotkę. |
| 4 | [`integral_product_tails_add`](../Nuttall/ProductTailTranslation.lean) | Przesunięcie każdej współrzędnej i odpowiadającej jej granicy całkowania. |
| 5 | [`product_tail_measure_open_eq_closed` i `product_tail_measure_restrict`](../Nuttall/ProductTailTranslation.lean) | Końce przedziałów nie zmieniają miary produktu. Dodatnie dolne granice można wyrazić przez ograniczenie wspólnej miary na ortancie. |
| 6 | [`shiftedMomentTerm_tsum_eq_sum` i `det_shiftedMomentTerm_eq_indicator`](../Nuttall/ShiftedMomentCutoff.lean) | Suma R ma skończoną podporę w każdym punkcie. Warunki aktywności można umieścić w kolumnach wyznacznika. |
| 7 | [`det_sum_columns` i `tendsto_auxiliary_determinant_truncations`](../Nuttall/ThetaDeterminantTruncations.lean) | Rozwinięcie skończonych sum po indeksach i granica punktowa do wyznacznika szeregu. |
| 8 | [`tendsto_weighted_truncated_moment`](../Nuttall/TruncatedMomentConvergence.lean) | Wspólne ograniczenie dominujące oraz przejście do granicy w całce dla każdego wpisu momentowego. |
| 9 | [`integral_truncated_determinants_eq_sum`](../Nuttall/IntegratedThetaTruncations.lean) i [`tendsto_truncated_andreief`](../Nuttall/TruncatedMomentConvergence.lean) | Zamiana skończonej sumy z całką z uzasadnieniem całkowalności oraz granica nieprzesuniętych całek wielokrotnych. |
| 10 | [`integral_fixed_indices_shift`](../Nuttall/ShiftedThetaIntegral.lean) | Dokładna zmiana zmiennych w całce dla każdej krotki dodatnich indeksów, z granicami uᵢ≥aₙᵢ. |

**Następny cel.** Pokaż, że wkład krotek zawierających indeks 0 znika przez zerową kolumnę. Przenieś każdą pozostałą całkę na wspólny ortant uᵢ>0, korzystając z lematu o ograniczeniu miary i wyznacznika z funkcjami charakterystycznymi. Wyłącz skalary wspólne dla wszystkich krotek, a skończoną sumę wstaw w kolumny, uzyskując obcięte R. Dla przejścia do granicy po przesunięciu udowodnij dominację niezależną od obcięcia. Przy u≥0 aktywnych jest najwyżej ⌈exp(2u)⌉ indeksów, a 0≤u−aₙ≤u dla aktywnego n≥1. To daje oszacowanie (wielomian w u)exp(2u), które można połączyć z wykładniczym czynnikiem Vandermonde’a i zanikiem exp(−Xexp(4u)). Wtedy porównaj obie granice i rozlicz p!2ᵖ, uzyskując `eq:anorm`.

## Ścieżka do twierdzeń 1.2 i 4.1

**A — znaczenie tezy.** Słabe RR dotyczy wszystkich rosnących dodatnich węzłów obu zmiennych i wszystkich 1≤p≤r. W Lean m(r) jest infimum poziomów w ℕ∞, więc przy braku skutecznego poziomu wynosi nieskończoność. Wystarczalność ścisłego testu i monotoniczność względem rzędu są sformalizowane poniżej. Słabe RR zachowuje się przy całkowaniu ogonowym i wyklucza ujemny podpisany wrońskian, również w t=0. Pozostaje zachowanie ścisłych znaków wrońskianów przy całkowaniu.

**U1 — pełna normalizacja z §4.1 i przygotowanie U3.** Wszystkie pozycje poniżej przeszły `lake build Nuttall` lokalnie oraz w [CI commita `c8fdbac`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45984688802/job/140457170000). Kroki 7 i 8 korzystają dodatkowo z zarejestrowanego aksjomatu `Literature.andreief`. Pozostałe mają trzy standardowe aksjomaty Lean. Dla 1≤p i 2p≤m przy t≥0 otrzymujemy równanie `eq:anorm` z czynnikiem (Xeᵗ/2)ᵖ(4X)ᵖ⁽ᵖ⁻¹⁾⁄²/p!. Macierz przesuniętych momentów jest transponowana względem zapisu w preprincie, co nie zmienia wyznacznika.

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | [`integral_fixed_indices_common_orthant`](../Nuttall/ShiftedThetaOrthant.lean) | Wspólna miara na ortancie, czynniki 1/√n w kolumnach i zerowanie krotek z n=0. |
| 2 | [`shiftedMomentTruncated_eq_of_ge_ceil`](../Nuttall/ShiftedMomentBounds.lean) | Dla każdego węzła od pewnego indeksu przycięta suma jest dokładnie równa pełnej sumie. |
| 3 | [`abs_shiftedMomentTruncated_le` i `abs_shiftedMoment_le`](../Nuttall/ShiftedMomentBounds.lean) | Wspólne ograniczenie 4exp(3u) dla u≥0. |
| 4 | [`tilted_thetaOrthantWeight_le`](../Nuttall/ShiftedMomentBounds.lean) | Waga superwykładnicza po przemnożeniu przez exp(Au) jest ograniczona stałą razy exp(−u). |
| 5 | [`integrable_shiftedOrthant_term` i `integrable_shiftedOrthant`](../Nuttall/ShiftedOrthantConvergence.lean) | Całkowalność bezwzględna ustalonych krotek i całego integrandu, użyteczna także przy kontroli ogona U3. |
| 6 | [`tendsto_shiftedOrthant_integral`](../Nuttall/ShiftedOrthantConvergence.lean) | Zbieżność całek po obcięciu sumy theta, przez twierdzenie o zbieżności zdominowanej. |
| 7 | [`andreief_integral_eq_shifted`](../Nuttall/ShiftedWronskian.lean) | Złożenie skończonych całek po zmianie zmiennych i identyfikacja ich wspólnej granicy. |
| 8 | [`signed_wronskian_eq_shifted_orthant` i `signed_wronskian_pos_iff_shifted_orthant`](../Nuttall/ShiftedWronskian.lean) | Dokładna normalizacja `eq:anorm` i równoważność ścisłej dodatniości. |
| 9 | [`signed_wronskian_order_one_pos`](../Nuttall/FirstWronskian.lean) | Dodatniość w rzędzie 1 dla każdego poziomu całkowania. |
| 10 | [`integral_pos_of_relative_tail`](../Nuttall/RelativeIntegralTail.lean) | Ogólne domknięcie argumentu U3. Po wykazaniu dodatniej masy i nieujemnego znaku na części centralnej wystarczy, żeby masa bezwzględna dopełnienia stanowiła mniej niż połowę całości. |

**U2 — pierwsza redukcja zweryfikowana.** [`iteratedDeriv_shiftedMoment`](../Nuttall/ShiftedMomentDerivatives.lean) używa lokalnie stałego zbioru aktywnych indeksów i identyfikuje pochodną rzędu i z momentem o indeksie niższym o i. [`shiftedMoment_wronskian_reverse_columns`](../Nuttall/ShiftedMomentDerivatives.lean) daje macierz Hankela z wpisem R_{L+k−1−i−j} po odwróceniu kolumn, przy k≤L i poza węzłami. Obie deklaracje zależą od trzech standardowych aksjomatów Lean.

**U2 — rdzeń macierzy przesunięcia.** Dziesięć kroków przeszło `lake build Nuttall` lokalnie i w [CI commita `64f2cdd`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45986552990/job/140463570245). Audyt wykazał tylko trzy standardowe aksjomaty Lean. W zapisie Lean zewnętrzny wielomian ma zmienną w, a jego współczynniki są wielomianami w z. Norma jest euklidesową normą operatorową Mathlib.

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | [`bilinearPolynomial_shift`](../Nuttall/ShiftCore.lean) | Zapis postaci 1−wz−d(1−w)(1−z) zgodny z preprintem. |
| 2 | [`coeff_bilinearPolynomial_pow`](../Nuttall/ShiftCore.lean) | Współczynnik przy wⁱ po wyciągnięciu czynnika dwumianowego jest iloczynem dwóch potęg form liniowych w z. |
| 3 | [`shiftCore_zero`](../Nuttall/ShiftCore.lean) | Przy k≤M+1 zachodzi C₀=Jₖ. |
| 4 | [`bilinearCoeff_scale` i `bilinearCoeff_const_mul`](../Nuttall/ShiftCoreScaling.lean) | Podstawienie sw,sz mnoży współczynnik przez sⁱ⁺ʲ, a skalowanie całej formy przez s daje czynnik sᴹ. |
| 5 | [`shiftReflection_mul_transpose`](../Nuttall/ShiftCoreScaling.lean) | Macierz odbicia jest ortogonalna dla 0≤d≤1. |
| 6 | [`shiftCore_eq_scaled_reflectionPower`](../Nuttall/ShiftCoreScaling.lean) | Przy 0≤d<1 wpis C_d jest współczynnikiem potęgi odbicia razy s_d^{M−i−j}. |
| 7 | [`shift_residual_exponent`](../Nuttall/ShiftCoreScaling.lean) | Przy 1≤k≤p≤r wykładnik 2r−p−k znika dokładnie dla p=k=r. |
| 8 | [`shiftReflectionPower_transpose_mul`](../Nuttall/ShiftReflectionOrthogonality.lean) | Ortogonalność pełnej potęgi symetrycznej w bazie z normalizacją dwumianową. |
| 9 | [`norm_shiftReflectionPower_le_one`, `shiftCore_eq_diagonal_mul`, `norm_shiftCore_le_pow`](../Nuttall/ShiftCoreNorm.lean) | Po obcięciu do k współrzędnych dla 0≤d<1 i 2(k−1)≤M otrzymujemy ‖C_d‖≤s_d^{M−2(k−1)}. |
| 10 | [`norm_shiftCore_le_one`](../Nuttall/ShiftCoreNorm.lean) | Oszacowanie ‖C_d‖≤1 przenosi się przez ciągłość na d=1. |

**U2 — poprawka wielomianowa zweryfikowana.** Całe `lake build Nuttall` przeszło lokalnie i w [CI commita `5201466`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45987060820/job/140465274294). Nowe deklaracje zależą tylko od trzech standardowych aksjomatów Lean. [`normalizedShiftCoefficients_geometric_left` i `normalizedShiftCoefficients_geometric_right`](../Nuttall/ShiftGeometricPrefix.lean) identyfikują ucięte szeregi geometryczne z mnożeniem przez U i Uᵀ przy k≤M+1. [`shiftCorrectionMultiplier_clear`](../Nuttall/ShiftCorrection.lean) po usunięciu mianowników wyznacza jawne reszty wielokrotne wᵏ lub zᵏ. [`normalized_shifted_polynomial_with_correction`](../Nuttall/ShiftCorrection.lean) daje A_d=C_d−u/(M+1)(V_dC_d+C_dV_dᵀ) na poziomie współczynników.

**U2 — kongruencja macierzy Hankela zweryfikowana.** Dziesięć kroków przeszło `lake build Nuttall` lokalnie i w [CI commita `e3ea142`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45988911850/job/140471464202). W tych deklaracjach M=L+k−2 jest indeksem w Lean, czyli o jeden mniejszym od indeksu R w preprincie. Warunek 2(k−1)≤M zapewnia prawidłowy indeks każdego wpisu.

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | [`shiftHankelBasisTerm_coeff_eq_zero` i `shiftHankelBasisTerm_coeff_diag`](../Nuttall/ShiftHankelBasis.lean) | Współczynniki kolumny wⁱ w wyrazie uᵃ/a! · wᵃ(1−w)^{M−a} znikają dla i<a. Przekątna przed normalizacją to uᵃ/a!. |
| 2 | [`det_shiftHankelBasis_pos`](../Nuttall/ShiftHankelBasis.lean) | Wyznacznik dolnotrójkątnej zmiany bazy jest dodatni przy u>0 i k≤M+1. |
| 3 | [`normalizedShiftCoefficients_hankelPolynomial`](../Nuttall/ShiftHankelBasis.lean) | Ekstrakcja i normalizacja niskich współczynników daje dokładną kongruencję S H Sᵀ. |
| 4 | [`hankelPowerMatrix_coeff`](../Nuttall/ShiftHankelPower.lean) | Rozwinięcie trójmianu, przeliczenie trzech silni i odcięcie wysokich wierszy i kolumn dają dokładnie czynnik uᴹ/M!. |
| 5 | [`ShiftCoeffEq.mul`](../Nuttall/ShiftHankelTruncation.lean) | Równość na bloku współczynników zachowuje się po pomnożeniu przez ten sam wielomian. |
| 6 | [`shiftHankelPolynomial_succ_prefix`](../Nuttall/ShiftHankelTruncation.lean) | Dwa skończone szeregi geometryczne przenoszą bazę z wykładnika M+1 do M na zachowanym bloku. |
| 7 | [`geometricPrefix_shiftForm`](../Nuttall/ShiftHankelTruncation.lean) | Dodatkowa potęga formy daje wcześniej udowodniony mnożnik poprawki po odcięciu reszt wᵏ i zᵏ. |
| 8 | [`shiftHankel_single_congruence`](../Nuttall/ShiftHankelCongruence.lean) | Jeden przesunięty składnik daje A_d z pełnym czynnikiem uᴹ/M!. |
| 9 | [`shiftHankel_congruence` i `shiftedMomentHankel_weighted_det_pos_iff`](../Nuttall/ShiftHankelCongruence.lean) | W macierzy pełnych momentów kongruencja obejmuje wszystkie aktywne indeksy z wagami 1/√n i zachowuje znak wyznacznika z dowolnym wspólnym czynnikiem. |
| 10 | [`shiftedMomentWronskian_pos_iff`](../Nuttall/ShiftedMomentWronskianReduction.lean) | Przy k≤L i u>0 poza węzłami ścisła dodatniość zwykłego wrońskianu odpowiada ścisłej dodatniości wyznacznika sumy A_d z podpisem odwrócenia kolumn. |

**U2 — oszacowanie poza centralnym kwadratem zweryfikowane.** Weryfikacja w tym samym przebiegu CI. [`shiftScale_le_exp_neg` i `abs_shiftCore_le_offCentral`](../Nuttall/ShiftOffCentral.lean) dają s_d≤exp(−d) na [0,1] oraz ograniczenie exp(−d√M/16) na moduł każdego wpisu C_d spoza centralnego kwadratu przy 0≤d<1.

**U2 — oszacowanie współczynnika na okręgu.** Średnia Fouriera i ograniczenie logarytmiczne przeszły powyższy przebieg CI. Pełne oszacowanie współczynnika przeszło `lake build Nuttall` lokalnie i w [CI commita `e0d2ab8`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45989532464/job/140473555677). Audyt wykazał tylko trzy standardowe aksjomaty Lean w nowych deklaracjach. [`norm_polynomialCoeff_le_circleAverage`](../Nuttall/ShiftCircleCoefficient.lean) ogranicza każdy współczynnik zespolonego wielomianu przez średnią modułu na okręgu jednostkowym za pomocą współczynników Fouriera Mathlib. [`shiftCentralLogBound`](../Nuttall/ShiftCentralLogBound.lean) dla −1<x<1 i 0≤j≤M przy M>0 daje logarytmiczne ograniczenie 4β²/M−Mx²/16, gdzie β=M/2−j.

[`shiftCentral_circle_product_bound`](../Nuttall/ShiftCentralCircle.lean) formalizuje kwadraty modułów 1±2cd cos θ i przechodzi przez x=±1 przez domknięcie przedziału. [`shiftAngularGaussian_average`](../Nuttall/ShiftAngularGaussian.lean) ogranicza średnią exp(−b cos²θ) przez √π/(2√b), za pomocą symetrii, nierówności `Real.mul_le_sin` i całki gaussowskiej z Mathlib. [`norm_central_shift_polynomialCoeff_le`](../Nuttall/ShiftCentralCoefficient.lean) składa oba kroki z ograniczeniem Fouriera i daje exp(4β²/M)√π/(cd√M) dla M>0, 0≤j≤M, c,d>0 i c²+d²=1.

**U2 — oszacowanie operatorowe `eq:shift` zweryfikowane.** Dziesięć kroków przeszło `lake build Nuttall` lokalnie i w [CI commita `f0f6953`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45990606214/job/140477165192). Audyt nowych deklaracji pokazuje wyłącznie trzy standardowe aksjomaty Lean. Zakres to M>0, 0<d<1 oraz 2(k−1)≤M.

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | [`bilinearCoeff_symm`](../Nuttall/ShiftCentralEntry.lean) | Symetria współczynników dwuliniowej formy i jej potęg wynika ze splotu współczynników. |
| 2 | [`shiftReflectionPower_symm_entry`](../Nuttall/ShiftCentralEntry.lean) | Symetria przechodzi przez normalizację dwumianową. |
| 3 | [`choose_monotone_to_half`](../Nuttall/ShiftCentralEntry.lean) | Współczynniki dwumianowe są monotoniczne do środka, więc dla j≤i≤M/2 prefaktor jest najwyżej 1. |
| 4 | [`shiftReflectionPower_entry_formula`](../Nuttall/ShiftCentralEntry.lean) | Dokładny wzór na wpis to prefaktor √(choose M j / choose M i) razy współczynnik wielomianu z poprzedniego kroku U2. |
| 5 | [`exp_small_mul_sqrt_pi_le_two`](../Nuttall/ShiftCentralEntry.lean) | W kwadracie centralnym exp(4β²/M)√π≤2, z jawnymi oszacowaniami exp(1/64) i π. |
| 6 | [`abs_shiftReflectionPower_entry_central`](../Nuttall/ShiftCentralEntry.lean) | Ograniczenie 2/(cd√M) na znormalizowany wpis odbicia w dowolnej kolejności indeksów. |
| 7 | [`norm_matrix_le_sqrt_sum_sq`](../Nuttall/ShiftMatrixEnvelope.lean) | Norma operatorowa jest ograniczona przez normę Frobeniusa, przez nierówność Cauchy'ego–Schwarza w każdym wierszu. |
| 8 | [`norm_matrix_le_of_entry_envelope`](../Nuttall/ShiftMatrixEnvelope.lean) | Ograniczenie b·vᵢvⱼ na moduł wpisu prowadzi do normy ≤b∑vᵢ². |
| 9 | [`shift_geometricWeight_sum_le`](../Nuttall/ShiftMatrixEnvelope.lean) | Suma kwadratów wag jest najwyżej 1/(1−s²). |
| 10 | [`norm_shiftCore_le_eq_shift`](../Nuttall/ShiftOperatorBound.lean) | Rozkład na kwadrat centralny i jego dopełnienie daje oba składniki dokładnej nierówności `eq:shift`. |

**U2 — oszacowanie poprawki zweryfikowane.** Całe `lake build Nuttall` przeszło lokalnie i w [CI commita `2f26cc2`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45992201453/job/140482575455). [`shiftTriangular_entry_le_gaussian`](../Nuttall/ShiftTriangularDecay.lean) ogranicza wpis Uᵢⱼ przez exp(−(i−j)²/N), gdzie N=M+1. [`norm_matrix_le_of_row_col_sum`](../Nuttall/MatrixSchurBound.lean) daje oszacowanie normy przez wspólne ograniczenie nieujemnych sum wierszy i kolumn. [`norm_shiftCorrectionMatrix_le`](../Nuttall/ShiftCorrectionNorm.lean) stosuje półosiową całkę gaussowską i dodatnią przekątną V_d, uzyskując 2‖V_d‖≤1+√(πN). [`norm_correctedShiftCore_sub_le_uniform`](../Nuttall/ShiftCorrectionError.lean) daje ‖A_d−C_d‖≤E‖C_d‖ przy 0≤u≤B, 0<r≤N i 0≤d≤1, z E=B(1/r+√(π/r)).

**U2 — przygotowanie sumy wcześniejszych przesunięć zweryfikowane.** Weryfikacja w tym samym przebiegu CI. [`norm_shiftCore_le_earlierTerms` i `shiftKnot_gap_lower`](../Nuttall/ShiftEarlierTerms.lean) upraszczają mianownik środkowego składnika `eq:shift` do d²√(1−d)√M i ograniczają odstęp od węzła przez (K−n)/(2B exp(2B)) przy n≤K≤exp(2u) i 0<u≤B.

**U2 — rozkład normy względem macierzy znaków zweryfikowany.** Całe `lake build Nuttall` przeszło lokalnie i w [CI commita `0167804`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45992601315/job/140483946709). [`norm_summedCorrectedShiftCore_sub_le_split`](../Nuttall/ShiftCriticalSplit.lean) oddziela n=1, ostatni aktywny indeks K i wcześniejsze dodatnie przesunięcia. Pierwszy wkład ma normę najwyżej E, ostatni najwyżej (1+E)/√2. K=ceil(exp(2u))−1 odtwarza ścisły warunek aktywności również na węźle. Dowód przenosi cały pozostały problem na sumę wcześniejszych norm C_d.

**U2 — przejście od marginesu do znaku zweryfikowane.** CI wykazało wyłącznie trzy standardowe aksjomaty Lean w obu nowych modułach. [`det_pos_of_matrix_norm_sub_one_lt`](../Nuttall/ShiftDeterminantMargin.lean) wykorzystuje odwracalność w kuli jednostkowej oraz ciągłość wyznacznika na odcinku. [`shiftedMomentWronskian_pos_of_norm_margin`](../Nuttall/ShiftDeterminantMargin.lean) stosuje to do J_k. Dla k≤L i u>0 poza węzłami warunek ‖∑ n^{−1/2}A_d−J_k‖<1 daje ścisłą dodatniość zwykłego wrońskianu przesuniętych momentów.

**U2 — suma wcześniejszych przesunięć zweryfikowana.** [CI commita `29449a8`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45995148972/job/140492566662). [`sum_inv_sqrt_succ_le` i `sum_cross_inv_sqrt_le_four`](../Nuttall/ShiftWeightSum.lean) dają teleskopowe oszacowanie przez 2√m oraz dokładną stałą 4 dla sumy ∑_{1≤n<K} 1/√(n(K−n)). [`lastActiveTheta_lt_exp` i `thetaKnot_two_div_le`](../Nuttall/ShiftEarlierSum.lean) zapewniają K<exp(2u) oraz d≥a₂/B dla n≥2. [`norm_earlier_shift_sum_le`](../Nuttall/ShiftEarlierSum.lean) składa te fakty z `eq:shift` i dolną granicą 1−d. Wynik ma jawny majorant `shiftEarlierError`, jednostajny dla 0<u≤B i właściwych wymiarów. [`eventually_shiftCriticalCutoff_bounds`](../Nuttall/ShiftCriticalCutoff.lean) dowodzi dla dokładnego B z pracy, że w końcu B≤r^{1/32} i exp B≤r^{3/8}.

**U2 — jednostajny margines bloku krytycznego zweryfikowany.** Całe `lake build Nuttall` przeszło lokalnie oraz w [CI commita `e2685f3`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45995805793/job/140494778256). Poniższe kroki kończą część asymptotyczną lematu `lem:critical`.

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | [`sum_inv_sqrt_succ_le`](../Nuttall/ShiftWeightSum.lean) | Teleskopowanie daje sumę do m ograniczoną przez 2√m. |
| 2 | [`sum_cross_inv_sqrt_le_four`](../Nuttall/ShiftWeightSum.lean) | Podział przy K/2 i odbicie drugiej połowy dają dokładne ograniczenie przez 4. |
| 3 | [`lastActiveTheta_lt_exp`, `thetaKnot_two_div_le`](../Nuttall/ShiftEarlierSum.lean) | Ścisłe K<exp(2u) i dodatnie d≥a₂/B dla wcześniejszych n≥2. |
| 4 | [`norm_earlier_shift_sum_le`](../Nuttall/ShiftEarlierSum.lean) | Jawny majorant sumy wcześniejszych przesunięć dla wszystkich 0<u≤B. |
| 5 | [`norm_summedCorrectedShiftCore_sub_le_explicit`](../Nuttall/ShiftEarlierSum.lean) | Oszacowanie całej odległości od J_k dla danego skończonego rzędu. |
| 6 | [`eventually_shiftCriticalCutoff_bounds`](../Nuttall/ShiftCriticalCutoff.lean) | Dla dokładnego B z §4.1 zachodzi ostatecznie B≤r^{1/32} i exp B≤r^{3/8}. |
| 7 | [`eventually_earlier_shift_sum_le`](../Nuttall/ShiftCriticalAsymptotic.lean) | Dwa składniki majorantu dążą do zera jednostajnie dla M≥r−1, k≤r i 0<u≤B. |
| 8 | [`eventually_shiftCorrection_budget_le`](../Nuttall/ShiftCriticalMargin.lean) | Budżet poprawki E jest ograniczony przez (1+√π)r^{−15/32} dla dostatecznie dużych r. |
| 9 | [`eventually_shiftCriticalMargin`](../Nuttall/ShiftCriticalMargin.lean) | Dla każdego ε>0 istnieje wspólny próg, od którego odległość od J_k jest najwyżej 1/√2+ε dla wszystkich dopuszczalnych p, k i u. |
| 10 | [`eventually_shiftedMomentWronskian_pos`](../Nuttall/ShiftCriticalMargin.lean) | Wybór ε=1/8 daje dodatniość wszystkich początkowych wrońskianów przesuniętych momentów poza węzłami, dla 1≤k≤p≤r i 0<u≤B. |

**U3 — ciągłość momentów zweryfikowana.** Ten sam przebieg CI. [`continuous_shiftedMoment_succ`](../Nuttall/ShiftedMomentContinuity.lean) dowodzi ciągłości wszystkich dodatnich indeksów Lean na całej prostej, również w węzłach, przez lokalną równość ze skończoną sumą.

**U3 — pochodne i znak w węzłach zweryfikowane.** Całe `lake build Nuttall` przeszło lokalnie i w [CI commita `27b366e`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45996553594/job/140497272292). [`iteratedDeriv_shiftedMoment_of_lt`](../Nuttall/ShiftedMomentKnotDerivative.lean) daje regułę pochodnej na całej prostej aż do dodatniego indeksu momentu. [`eventually_initialShiftedMomentWronskian_pos`](../Nuttall/ShiftedMomentWronskianAtKnots.lean) daje ścisłą dodatniość dla k<p na całym 0<u≤B, także w węzłach. Margines działa w węźle bezpośrednio dzięki globalnej regule pochodnych i kongruencji Hankela.

**U3 — redukcja wyznacznika ewaluacji zweryfikowana.** Zbudowano lokalnie i w [CI commita `cc28bb6`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45998126012/job/140502591692).

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | [`det_eval_eq_prod_mul_det_differences`](../Nuttall/EvaluationDeterminant.lean) | Normalizacja przez wartości pierwszej funkcji i odejmowanie sąsiednich wierszy redukują rozmiar macierzy o jeden. |
| 2 | [`det_integral_rows`, `integrable_evaluation_det`](../Nuttall/EvaluationDeterminant.lean) | Rozwinięcie permutacyjne i Fubini zamieniają wyznacznik całek w całkę z wyznacznika i dowodzą jego całkowalności. |
| 3 | [`det_eval_eq_prod_mul_integral_deriv`](../Nuttall/EvaluationDeterminant.lean) | Twierdzenie podstawowe dla absolutnie ciągłych ilorazów daje dokładną formułę z §4.1. |
| 4 | [`strictMono_of_adjacent_Ioc`, `integral_adjacent_Ioc_pos`](../Nuttall/EvaluationDeterminant.lean) | Punkty z kolejnych przedziałów są ściśle uporządkowane. Przeliczalne wyłączenia w każdej współrzędnej zachowują dodatniość całki. |
| 5 | [`det_eval_pos_of_reduced`](../Nuttall/EvaluationDeterminant.lean) | Jeśli wyznacznik rodziny zredukowanej jest dodatni poza zbiorem wyjątków, dodatni jest także wyznacznik wyjściowy. |
| 6 | [`familyWronskian_mul_left`](../Nuttall/WronskianReduction.lean) | Wspólny czynnik działa na macierz pochodnych przez dolną macierz trójkątną. |
| 7 | [`familyWronskian_eq_pow_mul_reduced`](../Nuttall/WronskianReduction.lean) | Wrońskian pochodnych ilorazów ma właściwy znak dzięki dokładnej tożsamości z potęgą pierwszej funkcji. |
| 8 | [`contDiffAt_shiftedMoment_off_knots`, `contDiff_shiftedMoment_of_lt`](../Nuttall/ShiftedMomentRegularity.lean) | Momenty są gładkie poza węzłami. Pochodne z dodatnim indeksem momentu są ciągłe również na węzłach. |
| 9 | [`locallyLipschitz_shiftedMoment_succ`, `absolutelyContinuousOnInterval_iteratedDeriv_shiftedMoment`](../Nuttall/ShiftedMomentRegularity.lean) | Dodatnie indeksy dają lokalną lipschitzowskość, stąd absolutną ciągłość na każdym zwartym przedziale. |
| 10 | [`eventually_lastShiftedMomentWronskian_pos_ae`](../Nuttall/ShiftedMomentRegularity.lean) | Ostatni wrońskian jest dodatni prawie wszędzie na przedziale centralnym. |

**U3 — dodatniość centralnego wyznacznika zweryfikowana.** Pełne `lake build Nuttall` przeszło lokalnie i w [CI commita `3905d5d`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45999491781/job/140507185278). [`locallyLipschitzOn_iteratedDeriv_div`](../Nuttall/LocalJetRegularity.lean) zachowuje lokalną lipschitzowskość pochodnych ilorazu, gdy mianownik jest niezerowy. [`det_eval_pos_of_familyWronskians`](../Nuttall/CentralEvaluationPositivity.lean) składa redukcje indukcyjnie z zachowaniem znaku wrońskianów i przeliczalnego zbioru wyjątków na ostatnim poziomie. [`eventually_shiftedMoment_evaluation_det_pos`](../Nuttall/ShiftedMomentEvaluationPositivity.lean) stosuje to do przesuniętych momentów jednocześnie dla wszystkich (1≤p≤r) i dowolnych ściśle uporządkowanych punktów w (0,B), również gdy punkt wypada na węźle theta. Dla p=1 znak w węźle wynika bezpośrednio z marginesu i warunku (k<2r-p).

**U3 — współczynnik oszacowania ogona zweryfikowany.** Ten sam przebieg CI. [`shiftRelativeTailRatio_mul_lt_quarter`](../Nuttall/ShiftRelativeTailRatio.lean) dowodzi pη<1/4 już dla r≥4, p≤r oraz X≥π. Stała `shiftRelativeTailRatio` jest dokładną formułą η z §4.1. Ta deklaracja sprawdza wielkość współczynnika. Zastosowanie go do całki wymaga jeszcze dowodu względnego oszacowania przekroju.

**U3 — znak podcałkowy i redukcja do oszacowania ogona zweryfikowane.** [CI commita `945fc52`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46000602967/job/140510960226) zbudowało cały moduł `Nuttall`. Redukcja do wrońskianu korzysta z odnotowanej wcześniej tożsamości Andréiefa. [`eventually_shiftedOrthantIntegrand_central_sign`](../Nuttall/CentralOrthantSign.lean) przenosi dodatniość na podcałkową funkcję z §4.1. Na dowolnej permutacji znak obu wyznaczników zmienia się tak samo, a przy zderzeniu węzłów iloczyn znika. [`eventually_signRegularWronskians_two_mul_of_shiftRelativeTailRatio`](../Nuttall/CentralOrthantMass.lean) wykazuje dodatnią masę na uporządkowanym prostokącie w sześcianie i łączy ją z tożsamością Andréiefa. Warunkiem pozostaje jedna nierówność: masa bezwzględna dopełnienia sześcianu jest najwyżej pη razy całkowitą masą bezwzględną.

**U3 — wielomian w centralnym przekroju zweryfikowany.** Ten sam przebieg CI. [`shiftedMoment_linearCombination_eq_polynomial`](../Nuttall/ShiftCentralSlicePolynomial.lean) redukuje kombinację momentów na (0,1/4] do u^{L−1} razy wielomian stopnia ≤p, bo aktywny pozostaje tylko pierwszy składnik theta. [`abs_le_abs_shiftCentralSlicePolynomial_coeff_of_max`](../Nuttall/ShiftCentralSlicePolynomial.lean) daje współczynnik o module co najmniej F przy L≥2, z indeksem maksymalnego znormalizowanego współczynnika.

**U3 — Fubini i dolne ograniczenie wielomianu poza otoczeniami pierwiastków zweryfikowane.** [CI commita `bcf28f4`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46002397295/job/140517086640). [`integral_coordinate_compl_le_of_slice`, `integral_pi_compl_le_of_slices`](../Nuttall/OrthantSliceBound.lean) wydzielają współrzędną i sumują oszacowania dla dopełnienia sześcianu. [`integral_shiftedOrthant_compl_le_of_slices`](../Nuttall/ShiftedOrthantSliceBound.lean) stosuje tę redukcję do całki z §4.1 i pomija punkt brzegowy B przez zerową miarę singletonu. [`coeff_norm_mul_pow_le_eval_norm`, `relative_root_separation`](../Nuttall/ShiftSliceRootBound.lean) wykorzystują faktoryzację nad ℂ z Mathlib i dają dolną granicę wartości wielomianu na podstawie współczynnika i względnej odległości od pierwiastków.

**U3 — przekrój i dopełnienie sześcianu.** Kroki 1–5 sprawdzono w CI powyżej. Kroki 6–10 przeszły w [CI commita `5f579f6`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46003761683/job/140521661243).

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | [`integral_coordinate_compl_le_of_slice`](../Nuttall/OrthantSliceBound.lean) | Fubini przenosi oszacowanie przekroju na obszar z jedną współrzędną poza przedziałem. |
| 2 | [`integral_pi_compl_le_of_slices`](../Nuttall/OrthantSliceBound.lean) | Suma wskaźników pokrywa dopełnienie sześcianu i daje mnożnik p. |
| 3 | [`integral_shiftedOrthant_compl_le_of_slices`](../Nuttall/ShiftedOrthantSliceBound.lean) | Redukcja dla właściwej całki używa otwartych półprostych i rozlicza punkt B. |
| 4 | [`coeff_norm_mul_pow_le_eval_norm`](../Nuttall/ShiftSliceRootBound.lean) | Z faktoryzacji przez pierwiastki uzyskujemy dolną granicę wartości wielomianu. |
| 5 | [`relative_root_separation`](../Nuttall/ShiftSliceRootBound.lean) | Odstęp δ od części rzeczywistej pierwiastka daje znormalizowany odstęp δ/3. |
| 6 | [`separated_exp_four_sub_lower`, `abs_exp_four_sub_le`](../Nuttall/ShiftSliceGeometry.lean) | Dolna i górna granica znormalizowanych czynników Vandermonde'a. |
| 7 | [`shiftSliceGoodSet_volume_lower`](../Nuttall/ShiftSliceGeometry.lean) | Po wyłączeniach w przedziale [1/8,1/4] pozostaje objętość co najmniej 1/16. |
| 8 | [`shiftSlice_central_mass_lower`](../Nuttall/ShiftSliceCentralLower.lean) | Z dokładnymi stałymi uzyskano dolną granicę całki z modułu przekroju. |
| 9 | [`abs_shiftedMoment_linearCombination_le_envelope`](../Nuttall/ShiftSliceMomentUpper.lean) | Suma aktywnych wag jest ≤2exp(u). Na całej półosi otrzymujemy wielomianową majorantę kombinacji momentów. |
| 10 | [`exp_four_gamma_envelope`](../Nuttall/ShiftSliceGamma.lean) | Podstawienie y=exp(4u) i całka Eulera dają całkowalność majoranty oraz granicę m!. |

**U3 — pełne oszacowanie względne zweryfikowane.** Pełna kompilacja lokalna oraz [CI commita `96dce6e`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46004454682/job/140523990682) zakończyły się sukcesem. [`abs_shiftedOrthantIntegrand_insertNth`](../Nuttall/ShiftSliceFactorization.lean) wydziela kolumnę momentów z kofaktorami, zależne czynniki Vandermonde'a i wagę wolnej współrzędnej. [`shiftSlice_tail_mass_upper`](../Nuttall/ShiftSliceTailUpper.lean) całkuje górną majorantę poza B z dokładną stałą z §4.1. [`shiftSlice_relative_tail_le`](../Nuttall/ShiftRelativeTailProof.lean) porównuje górną i dolną granicę bez dzielenia przez skalę kofaktorów. Stąd Fubini i suma po współrzędnych dają koszt dopełnienia sześcianu najwyżej pη razy całkowita masa bezwzględna.

**U4 — ścisłe znaki wrońskianów zweryfikowane.** Ten sam przebieg CI. [`eventually_signRegularWronskians_two_mul` i `exists_level_signRegularWronskians`](../Nuttall/ShiftRelativeTailProof.lean) dowodzą odpowiednio, że dla wszystkich dostatecznie dużych r poziom 2r przechodzi ścisły test, i że każdy zadany r≥1 ma pewien skuteczny poziom dla tego testu. Audyt ścieżki używa trzech standardowych aksjomatów Lean oraz wcześniej przyjętej tożsamości Andréiefa.

**A/U — kryterium jądrowe i twierdzenie 1.2.** Pełny `lake build Nuttall` przeszedł w [CI commita `6e210de`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46008815492/job/140538728785). Kryterium jądrowe używa wyłącznie standardowych aksjomatów Lean. Końcowy wynik analityczny zależy także od wcześniej przyjętej tożsamości Andréiefa.

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | [`contDiff_auxiliaryTheta`](../Nuttall/PsiSmoothness.lean) | Każda pochodna pomocniczego szeregu theta jest różniczkowalna na ℝ. |
| 2 | [`contDiff_phi`, `contDiff_psi`](../Nuttall/PsiSmoothness.lean) | Φ i wszystkie iterowane całki Ψₘ są gładkie, także dla m=0 i m=1. |
| 3 | [`det_alternating_columns`](../Nuttall/SignedKernelCriterion.lean) | Iloczyn znaków kolumn daje dokładny znak (−1)^{p(p−1)/2}. |
| 4 | [`det_eval_pos_of_contDiff_family`](../Nuttall/SignedKernelCriterion.lean) | Na dodatniej półosi stosujemy kryterium jednowymiarowe z pustym zbiorem wyłączeń. |
| 5 | [`signed_derivative_evaluation_pos`](../Nuttall/SignedKernelCriterion.lean) | Pierwsza aplikacja daje znak macierzy kolejnych pochodnych w przesuniętych rosnących punktach. |
| 6 | [`signed_kernel_evaluation_pos`](../Nuttall/SignedKernelCriterion.lean) | Druga aplikacja daje ścisły znak jądra dla obu rodzin punktów. |
| 7 | [`signRegularWronskians.strictReverseSignRegular`](../Nuttall/ReverseSignRegularity.lean) | Kryterium działa dla każdego poziomu Ψₘ i każdego badanego rzędu. |
| 8 | [`kernelIntegrationOrder`, `kernelIntegrationOrder_mono`, `kernelIntegrationOrder_attained_of_exists`](../Nuttall/ReverseSignRegularity.lean) | Definicja m(r) używa słabych znaków, a minimum jest monotoniczne względem r. Przy istnieniu skutecznego poziomu infimum jest osiągane. |
| 9 | [`exists_reverseSignRegular_psi`, `kernelIntegrationOrder_attained`](../Nuttall/AnalyticUpperBound.lean) | Każdy r ma skuteczny poziom, a m(r) jest skończone i osiągane. |
| 10 | [`eventually_strictReverseSignRegular_psi_two_mul`, `eventually_kernelIntegrationOrder_le_two_mul`](../Nuttall/AnalyticUpperBound.lean) | Dla dostatecznie dużych r poziom 2r daje ścisły znak wszystkich minorów i stąd m(r)≤2r. |

[`kernelIntegrationOrder_five_le_one_of_mainClaim`](../Nuttall/ReverseSignRegularity.lean) wiąże wynik istniejącego certyfikatu W5 z nową definicją. Przyjmuje `W5.MainClaim` jako hipotezę, dzięki czemu kompilacja analitycznej gałęzi pomija ciężkie obliczenia z `W5.NuttallR5`. Specjalizacja daje stronę górną m(5)≤1.

**A — zły znak wrońskianu i zachowanie słabego RR.** Pełny `lake build Nuttall` przeszedł w [CI commita `e382998`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46011982462/job/140549533135). Oba dowody i wynik o dolnej granicy używają tylko standardowych aksjomatów Lean.

| Krok | Deklaracja lub argument | Wynik |
|---|---|---|
| 1 | Macierz Newtona w [ForwardDifferenceKernel.lean](../Nuttall/ForwardDifferenceKernel.lean) | Macierz jest dolnotrójkątna z jedynkami na przekątnej, więc jej wyznacznik wynosi jeden. |
| 2 | `det_kernelGrid_eq_det_forwardDiff` | Przejście od wartości na siatce do różnic skończonych w obu zmiennych zachowuje wyznacznik. |
| 3 | `det_forwardDiff_eq_scaled` | Normalizacja różnic zmienia wyznacznik o dodatni czynnik dla dodatniego kroku siatki. |
| 4 | Rozwinięcie Taylora w [ForwardDifferenceLimit.lean](../Nuttall/ForwardDifferenceLimit.lean) | Różnica rzędu k usuwa potęgi stopnia poniżej k i mnoży składnik stopnia k przez k!. |
| 5 | `tendsto_normalized_fwdDiff` | Każda znormalizowana różnica zbiega do odpowiedniej pochodnej. |
| 6 | [`signed_wronskian_nonneg_of_reverseSignRegular`](../Nuttall/WronskianObstruction.lean) | Granica wyznaczników daje słaby znak wrońskianu dla t>0, a ciągłość rozszerza go na t=0. |
| 7 | `not_reverseSignRegular_psi_of_negative_wronskian` | Świadek o ujemnym podpisanym wrońskianie wyklucza RR na badanym poziomie. |
| 8 | [`det_tail_eq_integral_on_ordered_partition`](../Nuttall/KernelTailPersistence.lean) | Sąsiednie różnice wierszy zmieniają całki ogonowe w całki na rozłącznych, uporządkowanych przedziałach. |
| 9 | `reverseSignRegular.psi_succ`, `reverseSignRegular.psi_of_le` | Słabe RR przechodzi na każdy wyższy poziom całkowania. |
| 10 | `kernelIntegrationOrder_succ_le_of_negative_wronskian`, `kernelIntegrationOrder_five_eq_one_of_witnesses` | Ujemny podpisany wrońskian na poziomie m wymusza m(r)≥m+1. Dla r=5 deklaracja łączy certyfikat górny i ujemnego świadka dla Φ w t=0. |

**S — świadek (W_5(\Phi;0)<0) i dokładne minimum.** Oczekuje na CI. Szybki cel `lake build Nuttall.FiveIntegrationOrder` sprawdza samodzielny dowód dolnej granicy. Osobny cel `lake build W5.NuttallR5IntegrationOrder` dołącza istniejący dowód dodatniości pierwszej całki na całej półosi. Standardowe CI sprawdza nowy świadek i twierdzenie składające oba kierunki dla założenia `W5.MainClaim`. Pełne odtworzenie osobnego celu korzysta z tego samego kodu `W5.nuttall_r5`, zweryfikowanego wcześniej w rewizji `dfaede6d`, wraz z jego dotychczasowymi założeniami o obliczeniach natywnych. W razie zimnego cache można użyć sześciu [artefaktów odtworzenia](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45453506606), jeśli źródła w archiwach i wersja Lean są zgodne.

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | [`iteratedDeriv_phi_eq_auxiliary`](../Nuttall/PhiJetSeries.lean) | Pochodne Φ wyrażają się przez dwie sąsiednie pochodne szeregu pomocniczego. |
| 2 | `iteratedDeriv_phi_eq_tsum`, `auxiliaryWeightedSummand_origin` | Wyrażenie w zerze jest szeregiem, którego czynnik gaussowski to potęga e^(−π). |
| 3 | [`coeff_auxiliaryDerivativePolynomial`](../Nuttall/PhiJetCoefficients.lean) | Rekurencja całkowita oblicza rzeczywiste współczynniki wielomianów pochodnych, łącznie z zerami ponad stopniem. |
| 4 | `eval_phiJetPolynomial` | Wystarcza dziesięć współczynników na każdy z dziewięciu potrzebnych rzędów. |
| 5 | [`exp_neg_pi_bounds`](../Nuttall/OriginGaussianBounds.lean) | Taylor i granice π z Mathlib zamykają e^(−π) w przedziale wymiernym. |
| 6 | [`phiOriginTail_abs_le`](../Nuttall/PhiOriginTail.lean) | Od indeksu 8 bezwzględny ogon każdej sumy jest najwyżej 10⁻¹². |
| 7 | [`phiOriginJet_bounds`](../Nuttall/PhiOriginCertificate.lean) | Sprawdzone przedziały dla indeksów 0–7 wraz z ogonem zamykają pochodne Φ rzędu 0–8. |
| 8 | [`determinant_containsReal`, `phiOriginHankelBox_upper`](../Nuttall/OriginWronskianInterval.lean) | Rozwinięcie Laplace’a z dokładnymi końcami wymiernymi ogranicza wyznacznik z góry przez −2111237149457137148. |
| 9 | `phi_origin_wronskian_neg`, [`one_le_kernelIntegrationOrder_of_five_le`](../Nuttall/FiveIntegrationOrder.lean) | Świadek w zerze dowodzi m(r)≥1 dla każdego r≥5. |
| 10 | [`kernelIntegrationOrder_five_eq_one`](../W5/NuttallR5IntegrationOrder.lean) | Istniejący certyfikat dla Ψ₁ domyka górną stronę m(5)=1. |

**S — rząd pierwszy.** [`kernelIntegrationOrder_one_eq_zero`](../Nuttall/FirstIntegrationOrder.lean) przenosi `W5.Phi_pos` na ścisły znak minora 1×1 i wykazuje m(1)=0. Pełny `lake build Nuttall` i audyt trzech standardowych aksjomatów przeszły w [CI commita `0f0ea85`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46015136528/job/140560209577).

**S — rzędy 2–4.** Część analityczna, pierwsza komórka i redukcja do skończonego testu przeszły pełny `lake build Nuttall` w [CI commita `323feeb`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46021816417/job/140583073025). Audyt końcowej implikacji wykazał wyłącznie trzy standardowe aksjomaty Lean. Redukcja miała jedną hipotezę, `phiCompactGridChecked`, którą sprawdzono w osobnych paczkach opisanych poniżej. Obejmuje 51 komórek i cztery podpisane wyznaczniki na każdej. Odtworzenie w Pythonie na dokładnych ułamkach przyjęło wszystkie komórki. Lean zweryfikował osobno wszystkie cztery testy dla pierwszej komórki w `phiCompact_first_cell_pass`. Próba zamknięcia całej koniunkcji jednym obliczeniem jądra Lean została przerwana kodem 137 w lokalnym wykonawcy. Rozwinięcie bezpośrednie w X z suplementu zastępuje w tym zakresie ogólny test Taylora w t. Na [3,16] używamy 51 zamkniętych komórek, zmienionych przez dokładny wariant wymierny. Poza 16 stosujemy dominację wierszową zamiast oszacowania przez zespoloną całkę Gaussa.

| Krok | Deklaracja lub plik | Rola w dowodzie |
|---|---|---|
| 1 | [`phiCompactPolynomial_eq_rows`](../Nuttall/PhiCompactNormalization.lean) | Algebraiczna identyfikacja znormalizowanych współczynników gaussowskich z wierszami działającymi na zwykłe pochodne. |
| 2 | [`phiCompactTerm_summable`](../Nuttall/PhiCompactTransfer.lean) | Przeniesienie znormalizowanego szeregu przez macierz z oryginalnymi pochodnymi i istniejące lemmy o sumowalności. |
| 3 | `phiCompactMatrix_signed_det_pos_iff` | Kongruencja trójkątna przenosi znak na rzeczywisty wrońskian. |
| 4 | [`phiCompactExpBox_containsReal`](../Nuttall/PhiCompactExponential.lean) | Taylor z resztą i zaokrąglenie na zewnątrz pozwalają odzyskać exp(−X) wyłącznie z końców wymiernych. |
| 5 | [`phiCompactTail_abs_le`, `phiCompactFarTail_abs_le`](../Nuttall/PhiCompactTailBound.lean) | Wspólna majoranta geometryczna ogranicza pominiętą część szeregu na przedziale zwartym i na półosi od X=16. |
| 6 | [`phiCompactBlockBox_containsReal`](../Nuttall/PhiCompactInterval.lean) | Trzy niezerowe składniki oraz oszacowanie ogona ograniczają rzeczywiste wpisy znormalizowanej macierzy. |
| 7 | [`phiCompactWronskian_pos`](../Nuttall/PhiCompactCells.lean) | Pokrycie całego [3,16] jest dowodzone w Lean. Wynik używa jawnej hipotezy przejścia skończonych testów. |
| 8 | [`det_pos_of_row_diagonal_margin`](../Nuttall/MatrixRowMargin.lean) | Dodatnia przekątna i ścisła dominacja wierszowa dają dodatni wyznacznik. |
| 9 | [`phiFarWronskian_pos`](../Nuttall/PhiFarSign.lean) | Pierwszy składnik i jednolity błąd szeregu spełniają test na X≥16. |
| 10 | [`kernelIntegrationOrder_eq_zero_of_le_four_of_compact_check`](../Nuttall/ZeroIntegrationOrder.lean) | Oba zakresy oraz kryterium jądrowe składają się w wynik dla wszystkich r≤4, po potwierdzeniu testu. |

**S — końcowa weryfikacja siatki.** Pełny `lake build Nuttall` przeszedł w [CI commita `6501742`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46023478613/job/140588773252). Wszystkie 51 komórek, 204 podpisane wyznaczniki, pokrycie, złożenie ogona i twierdzenie m(r)=0 dla r≤4 są zweryfikowane. Audyt obu końcowych twierdzeń wykazał tylko `propext`, `Classical.choice` i `Quot.sound`. [PhiCompactReplay.lean](../Nuttall/PhiCompactReplay.lean) składa 11 niezależnych celów kompilacji. Każdy cel zawiera co najwyżej pięć osobnych deklaracji arytmetycznych i zapisuje wynik w osobnym pliku `.olean`. Pierwsza komórka korzysta z poprzedniego dowodu. Surowe wyniki wymierne są redukowane przez `decide +kernel`. Zgodność list komórek i pokrycie sprawdza ta sama siatka co w dowodzie części zwartej. [ZeroIntegrationOrder.lean](../Nuttall/ZeroIntegrationOrder.lean) udostępnia końcowe `kernelIntegrationOrder_eq_zero_of_le_four`.

**S — przygotowanie świadka rzędu 8.** [CI commita `2f1dc13`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46025106376/job/140594367144) zweryfikowało dwa pierwsze lemmy i wykorzystało cache wszystkich 11 paczek rzędu czwartego. [`iteratedDeriv_succ_psi_one_eq_tsum`](../Nuttall/PsiHankelJets.lean) daje formułę każdej pochodnej Ψ₁ dodatniego rzędu. [`two_le_kernelIntegrationOrder_of_psiOne_corner`](../Nuttall/PsiEightWitness.lean) redukuje wykluczenie poziomu 1 do trzech nierówności: dolnego ograniczenia wyrazu Ψ₁(t), ujemności wyznacznika po podstawieniu tego ograniczenia i niedodatniości dopełnienia algebraicznego wpisu (0,0). Pozwala to zastąpić dokładną kwadraturę słabszym jednostronnym oszacowaniem.

**S — dolny przedział dla świadka rzędu 8.** Pełny `lake build Nuttall` przeszedł w [CI commita `c8d6e94`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46026032316/job/140597547036). Nowe deklaracje używają tylko standardowych aksjomatów Lean. [`psi_one_at_rankEight_witness_ge`](../Nuttall/PsiEightCornerBound.lean) wykazuje Ψ₁(5/64)≥29/1000. Wykorzystuje `psi_one_ge_auxiliary_mul_rate`, tożsamość 2Ψ₁=g−∫g i wykładniczą majorantę g(s)≤g(t)e^(−12(s−t)). [`SchurIntervalChain.det_containsReal`](../Nuttall/SchurIntervalChain.lean) pozwala zaokrąglać przedziały na zewnątrz po każdym dopełnieniu Schura. [`two_le_kernelIntegrationOrder_of_rankEight_schur`](../Nuttall/PsiEightSchur.lean) sprowadza m(8)≥2 do obramowania pozostałych wpisów i dwóch sprawdzeń znaku.

**S — świadek rzędu 8 zweryfikowany.** Pełny `lake build Nuttall` przeszedł w [CI commita `306a9da`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46028702755/job/140606660247). Audyt obu końcowych twierdzeń wykazał wyłącznie `propext`, `Classical.choice` i `Quot.sound`. [PsiEightReplay.lean](../Nuttall/PsiEightReplay.lean) domyka bez dodatkowych hipotez `psiOne_wronskian_at_rankEight_witness_neg` i `two_le_kernelIntegrationOrder_eight`. Wykorzystuje dolny róg 29/1000 i dwa łańcuchy Schura dla macierzy zastępczej oraz jej dopełnienia algebraicznego przy (0,0). Oba górne końce przedziałów wyznaczników są ściśle ujemne. Dane przechowują dokładne końce wymierne w skali 10¹². Lean sprawdza obie strony wszystkich 14 przedziałów pochodnych, separację pivotów, zawieranie po każdym zaokrągleniu i końcowe znaki przez `decide +kernel`.

| Krok | Deklaracja | Wynik |
|---|---|---|
| 1 | `phiJetPolynomial_natDegree_le`, `eval_phiJetPolynomial_of_lt` | Jawna skończona suma dla każdego potrzebnego wielomianu pochodnej. |
| 2 | `auxiliaryWeightedSummand_le_exp_of_coeff_bound` | Oszacowanie składnika szeregu przez skończoną sumę modułów współczynników i czynnik gaussowski. |
| 3 | `rankEight_phiJetTail_abs_le` | Wspólna reszta 10⁻¹² od indeksu dziewiątego dla rzędów 0–13 funkcji Φ. Hipotezy `t ≤ 1` i `4 ≤ π exp(4t)` spełnia punkt 5/64. |
| 4 | `expTimeBox_containsReal`, `coordinateBox_containsReal`, `gaussianBox_containsReal` | Wymierne przedziały dla czynników wykładniczych w punkcie 5/64, z twierdzeń Taylora i przedziału dla π. |
| 5 | `jetTermBox_containsReal`, `psiEightJetRawBox_containsReal` | Skończona suma przedziałowa i reszta dają rzeczywiste obramowanie pochodnych Ψ₁ rzędu 1–14. |
| 6 | `jetBounds_enclose_raw`, `psiEightWitnessBox_containsReal` | Zaokrąglenie przedziałów i przejście do wszystkich wpisów macierzy Hankela z dolnym rogiem. |
| 7 | `cornerChain` | Sprawdzenie macierzy 8×8 z rogiem 29/1000 i wszystkich kolejnych dopełnień Schura. |
| 8 | `cofactorChain` | Niezależne sprawdzenie dopełnienia algebraicznego 7×7 i wszystkich jego kroków Schura. |
| 9 | `psiOne_wronskian_at_rankEight_witness_neg` | Znak prawdziwego W₈(Ψ₁;5/64) przez afiniczną zależność od wpisu (0,0). |
| 10 | `two_le_kernelIntegrationOrder_eight` | Świadek wyklucza słabe RR na poziomie pierwszym i dowodzi m(8)≥2. |

**S — kongruencja dla certyfikatów zwartych zweryfikowana.** Pełny `lake build Nuttall` przeszedł w [CI commita `ad346b8`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46030841107/job/140613917043). Audyt lematu wykazał tylko trzy standardowe aksjomaty Lean. [MatrixCongruenceMargin.lean](../Nuttall/MatrixCongruenceMargin.lean) dowodzi `signed_leading_det_pos_of_triangular_congruence`. Dla rzeczywistej macierzy A i dolnotrójkątnej U z niezerową przekątną jedna nierówność normy wierszowej dla UAUᵀ względem J=diag((-1)ⁱ) implikuje ścisłe podpisane znaki wszystkich minorów początkowych. Obcięcie do p≤n komutuje z kongruencją, a jej mnożnik w wyznaczniku jest dodatnim kwadratem. Ten sam lemat stosuje się do (2.1) oraz do certyfikatu Ψ₂.

**S — reszta Taylora i oszacowanie na dysku zweryfikowane.** Pełny `lake build Nuttall` przeszedł w [CI commita `f2aa740`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46033037050/job/140621387589). Audyt obu wyników wykazał trzy standardowe aksjomaty Lean. [CompactTaylor.lean](../Nuttall/CompactTaylor.lean) dowodzi `cellTaylor_error_le` dla wszystkich |v|≤1, w tym środka i końców komórki. Resztę ogranicza norma pochodnej rzędu d+1 na całym przedziale. [PhiComplexDisk.lean](../Nuttall/PhiComplexDisk.lean) dowodzi `phiComplexSummand_norm_le_disk` na zamkniętym dysku o promieniu 1/8 przy c≤2 oraz przenosi je przez twierdzenie Cauchy’ego na każdy rząd pochodnej pojedynczego składnika. Do użycia przy rzeczywistych wpisach trzeba zidentyfikować pochodne składników i zsumować oszacowania. Następnie reszta dla Ψ₁ wynika z relacji Ψ₁′=−Φ.

**S — rzeczywiste pochodne i dane przedziałowe zweryfikowane.** Pełny `lake build Nuttall` przeszedł w [CI commita `1e66313`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46034330312/job/140625787556). Audyt nowych wyników wykazał trzy standardowe aksjomaty Lean. `phiJetSummand_norm_le` identyfikuje pochodne rzeczywistych składników z ograniczonymi pochodnymi zespolonymi. `iteratedDeriv_phi_compact_norm_le` daje Cauchy’ego granicę 10⁶·j!·8ʲ na [0,2], a `phiJet_from_twenty_five_norm_le` daje błąd 2⁻⁹⁰⁰·j!·8ʲ po zachowaniu 24 niezerowych składników. Ogólnie `phiJet_geometric_tail` pozwala dowolnie dobrać liczbę składników. `phiJetPrefixBox_containsReal` zamyka skończoną sumę dla dowolnego rzędu, gdy dane są przedziały dla exp(t), X i exp(−X). `psi_one_at_two_bounds` dowodzi przedziału [0,2⁻⁵⁰⁰] w punkcie 2. `psiPanel_error_le` przenosi go w lewo za pomocą wielomianu Taylora z jawną granicą na pierwszą pominiętą pochodną. `signed_leading_det_pos_of_compactPolynomial` sprawdza podpisane minory na podstawie przedziałów dla przekształconych współczynników oraz błędu, a `congruence_entry_abs_le` przenosi błąd pojedynczego wpisu przez kongruencję.

**S — reguła kwadratury i wpisy pierwszej komórki zweryfikowane.** Pełny `lake build Nuttall` przeszedł w [CI commita `9271327`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46036173838/job/140632034655). Audyt reszty pierwszej komórki, złożenia paneli i obramowania wpisów pokazał trzy standardowe aksjomaty Lean. `psiOneUniformGridBox_containsReal` składa wszystkie panele z jednej reguły i zachowuje rzeczywisty przedział wartości Ψ₁ na każdym lewym końcu. `phiCompactJetBox_containsReal` łączy ocenę skończonej sumy z dowiedzionym ogonem. W środku pierwszej komórki [0,1/128], przy c=h=1/256, `psiOneFirstCellJetBox_containsReal` używa siedmiu niezerowych składników i formalnych przedziałów wykładniczych. `psiOne_compact_cell_contains_hankel` obejmuje l≤12, 25 współczynników i każdy |v|≤1, z błędem co najwyżej 10⁻¹⁹ przed kongruencją. Reguła wpisów przyjmuje przedział dla Ψ₁(1/256), który dostarcza konkretna kwadratura poniżej.

**S — konkretna kwadratura rogu pierwszej komórki zweryfikowana.** [CI commita `30265e4`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46036904966/job/140634499633) zbudowało cały `Nuttall` i potwierdziło wyłącznie trzy standardowe aksjomaty `psiOne_first_cell_corner_containsReal`. `psi_one_short_seed_bounds` domyka słabszy przedział [0,10⁻⁷] dla dowolnego punktu od 1/2, co pozwala zacząć od 129/256. `psiGridPhiJetBox_containsReal` składa przedziały wykładnicze dla wymiernych czasów z istniejących małych przedziałów exp(−x). `psiOne_first_cell_corner_containsReal` używa przesuniętej siatki 16 paneli długości 1/32, 20 wyrazów na panel i siedmiu niezerowych składników theta, a potem zamyka rzeczywisty róg Ψ₁(1/256). Zaokrąglenia wejściowych przedziałów na zewnątrz w skali 10²³ ograniczają wzrost mianowników.

**S — kongruencja współczynników przedziałowych zweryfikowana.** Ten sam przebieg CI potwierdził trzy standardowe aksjomaty. `compactIntervalCongruence_containsReal` wylicza wszystkie obramowania po zastosowaniu bazy wymiernej, używając wyłącznie mnożeń i sum przedziałów z udowodnioną semantyką rzeczywistą.

**S — pierwsza komórka zweryfikowana w Lean.** Pełny `lake build Nuttall` przeszedł w [CI commita `c030d1c`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46043167851/job/140655741505). Audyt `psiOne_first_cell_signed_wronskians` wykazał wyłącznie trzy standardowe aksjomaty Lean. Deklaracja dowodzi właściwych ścisłych znaków wrońskianów Ψ₁ dla każdego p≤7 i każdej t∈[0,1/128]. `phiJetCoeffRow_getElem` weryfikuje tabulację rekurencji całkowitej przez całe wiersze, aby stopień 36 nie wymagał ponownego rozwijania niższych rzędów.

**S — sprawdzenie danych pierwszej komórki.** [Log kompilacji `44eca65`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46042156895/job/140652333541) potwierdził przedział rogu, 36 przedziałów pochodnych i `psiOne_first_cell_margin_checked`, który daje granicę 13/25 dla wszystkich siedmiu wierszy. Audyty tych trzech deklaracji wykazały tylko standardowe aksjomaty Lean. Kompilacja tego commita zatrzymała się w osobnym dowodzie trójkątności macierzy.

**S — siatka dla pozostałych komórek.** Sprawdzono sumy kontrolne wszystkich 105 plików suplementu i pokrycie [0,1/2] przez 67 wierszy `small/cells.csv`. W niezależnym rachunku wymiernym 22 wspólne panele długości 1/32 propagują przedział startowy [0,10⁻¹⁶] przy 11/16, a ostatni krótki panel dochodzi do środka każdej komórki. Każdy panel ma 36 wyrazów. Kandydaci na bazę z mianownikiem 1024 i współczynniki zaokrąglone na zewnątrz w skali 2⁹⁰ dały granice normy poniżej 664164877/10⁹ w każdej z 67 komórek, po doliczeniu reszty przed kongruencją równej 10⁻¹⁹. Granice wymagają jeszcze odtworzenia w Lean. Wykorzystaj wspólne obliczenia w węzłach 1/32, dokładny przedział wykładniczy z `W5.ThetaGammaBinExpNegBox` i jedną regułę reszty dla h≤1/256. Po odtworzeniu siatki połącz wyniki z ogonem. Do dokładnego m(8)=2 potrzebna jest osobno górna granica na poziomie Ψ₂.

**S — rozszerzenie testu na całą siatkę.** Pełny `lake build Nuttall` przeszedł w [CI commita `8f97d3f`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46044232600/job/140659349498), z wyłącznie trzema standardowymi aksjomatami Lean. `psiOne_compact_scaled_entry_error_le` podaje resztę dla dowolnego środka c i h∈[0,1/256], przy [c−h,c+h]⊆[0,2]. `psiOne_compact_cell_signed_wronskians` przyjmuje przedziały 25 współczynników, trójkątną bazę i sprawdzoną granicę sum wierszowych. Pierwsza komórka używa tej deklaracji. `psiOneCompactCells_cover` sprawdza pokrycie [0,1/2], a `psi_one_precise_compact_seed_bounds` daje [0,10⁻¹⁶] dla wartości Ψ₁ przy t∈[11/16,1].

**S — kwadratura ze wspólnych węzłów.** Pełny `lake build Nuttall` przeszedł w [CI commita `f0dbc4a`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46047310635/job/140669682832). `psiOneCompactCornerFromAnchorBox_containsReal` przenosi obramowanie Ψ₁ ze wspólnego węzła do środka komórki. `psiOneCompactCoefficientBox_containsReal` zamienia przedziały wartości i pochodnych na współczynniki po przeskalowaniu. `psiOneCompactBasis_lower`, `psiOneCompactBasis_diagonal_ne_zero` i `psiOneCompactBasis_row_le` sprawdzają trójkątność, niezerową przekątną i wspólną granicę sum wierszowych dla 67 baz. Audyty używają wyłącznie trzech standardowych aksjomatów. `psiOne_compact_grid_signed_wronskians` składa znaki komórek na całym [0,1/2] pod warunkiem przejścia ich testów.

**S — skrajna prawa komórka zweryfikowana.** Pełny `lake build Nuttall` przeszedł w [CI commita `6346f4b`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46065173408/job/140728636189). `psiOne_compact_last_cell_signed_wronskians` daje ścisłe znaki przez rząd 7 na [127/256,1/2]. `psiOneCompactHalfAnchor_containsReal` dostarcza wspólną kotwicę w 1/2. Oba twierdzenia oraz `psiOneLastCellCornerSnapshot_containsReal` używają trzech standardowych aksjomatów Lean. Wcześniejsze [CI commita `9c9dea2`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46063463842/job/140723032519) zweryfikowało wszystkie 252 przedziały pochodnych i 7 paneli, po czym zapisało je w cache. Rozdzielenie obliczeń skróciło pierwsze odtworzenie paneli do niespełna siedmiu minut w kroku kompilacji. Złożenie paneli i końcowy znak odtworzono z tego cache.

**S — komórka 60 i wspólne kotwice.** [CI commita `71ce7b8`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46065551657/job/140729869965) zbudowało moduły komórki 60, wraz z końcowym twierdzeniem i jego audytem. Wykazało wyłącznie trzy standardowe aksjomaty. Pełne [CI commita `67579ee`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46066978021/job/140734548600) potwierdziło także wspólne kotwice i twierdzenie składające certyfikat; audyty używają trzech standardowych aksjomatów Lean. `psiOne_compact_cell60_signed_wronskians` dla [15/32,61/128] używa kotwicy w 1/2 i krótkiego panelu długości 7/256. Niezależny rachunek wymierny sprawdził 89 węzłów oraz 469 sum wierszy. Maksimum z resztą jest mniejsze niż 664424843/10⁹ i występuje w komórce 60. Dane odtwarza `python tools/preprint_psi_one_compact_probe.py --output compact-grid.json`. `psiOne_compact_certified_grid_signed_wronskians` składa dowód z pokrycia, wspólnych paneli, krótkiej kwadratury, pochodnych i testów macierzowych. W pełnej siatce te hipotezy wymagają osobnego odtworzenia.

**S — następna deklaracja.** Odtwórz `psiOne_compact_grid_checked` w paczkach. Przy skali D=2⁹⁰ sprawdzaj w jądrze sumę całkowitą mniejszą niż ⌊7D/10⌋. Po podzieleniu przez D i doliczeniu reszty 7·10⁻¹⁹·(20 000 000)² otrzymasz normę mniejszą niż 1. Użyj `psiOne_compact_certified_grid_signed_wronskians` do spięcia 67 indeksów.

**S — koszt obliczania pochodnych.** Dla prawej komórki potwierdzony w CI commita `6346f4b`. `compactFixedHorner_containsReal` i `psiFixedGridPhiJetBoxOfInputs_containsReal` stosują Hornera, mnożenia i potęgi w skali 2⁷⁶⁸ oraz końcowe obramowanie pochodnych w skali 2⁹⁰. Lokalny audyt `compactFixedHorner_containsReal`, `phiCompactPreciseExpBox_containsReal` oraz `psiOne_compact_fixed_cell_signed_wronskians` wykazał trzy standardowe aksjomaty. Reguła dla wykładniczej używa Hornera dla zredukowanego argumentu i istniejącej reszty dla 65 wyrazów. Niezależny rachunek odtworzył wszystkie 89 wejściowych trójek przedziałów na siatce, potwierdził zawieranie w dotychczasowych obramowaniach paneli i 36 pochodnych prawej komórki oraz dał granicę 664164876/10⁹ dla wszystkich 67 komórek przy indywidualnych sumach wierszowych baz.

**S — uruchomienie przyspieszonej weryfikacji.** Zmieniono nazwę grupy współbieżności, ponieważ starszy przebieg wciąż wyświetlał stan aktywny po upływie 45-minutowego limitu, a [przebieg commita `e6c2bc5`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46053456766) czekał bez przydzielonego zadania. Dowód reszty dla wykładniczej importuje teraz bezpośrednio arytmetykę przedziałową. Test normy ostatniej komórki importuje tylko przeskalowanie współczynników i regułę macierzową.

**S — oszacowanie zaburzenia i znak wyznacznika na ogonie.** Lokalny Lean potwierdził `sixteen_le_theta_tail_coordinate` dla t≥1/2, `phiRankEightGaussianMajorantRow_lt` dla ośmiu wierszy, `phiRankEightGaussianMatrix_norm_le` dla bloku p≤8 oraz `phiRankEightTailEnvelope_summable_le` z granicą 1/1000 dla X≥16. `det_pos_of_quadratic_entry_margin` wykazuje dodatniość wyznacznika macierzy z dodatnim marginesem formy kwadratowej po zaburzeniu jej wpisów. Audyty wykazały wyłącznie trzy standardowe aksjomaty. Pełne [CI commita `67579ee`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46066978021/job/140734548600) również przeszło. Do znaku wrońskianów pozostają macierz mnożenia przez 1+u/√X, zależność macierzy współczynników od oryginalnego wrońskianu oraz ścisłe zachowanie znaków przy całkowaniu.

**S — pierwszy składnik Gaussa i macierz przesunięcia.** Lokalny Lean potwierdził `phiRankEightGaussian_one`, czyli przekątną znakową dla q=1, oraz oba ograniczenia normy macierzy P i jej transpozycji przez 7/4 dla X≥16, p≤8. Pełny `lake build Nuttall` przeszedł w [CI commita `86f0593`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46067824442/job/140737319791). Audyt normy ogona i marginesu pierwszego bloku wykazał tylko standardowe aksjomaty. `phiRankEightTailMatrix_summable_norm_lt` jest zweryfikowane. Wykazuje sumowalność znormalizowanych bloków od drugiego kwadratu i ogranicza normę sumy przez 1/1000 dla 1≤p≤8, X≥16. `phiRankEightDominantBlock_quadratic_le` wykazuje margines 2X−2p−1 dla przekątnej i części antysymetrycznej. `phiRankEightFirstTerm_signed_eq` identyfikuje pierwszy składnik po przemnożeniu przez przekątną znakową. `phiRankEightNormalized_det_pos` wykazuje dodatniość tak podpisanego wyznacznika znormalizowanej macierzy dla 1≤p≤8, X≥16. Oba twierdzenia przeszły `lake build Nuttall` i audyt trzech standardowych aksjomatów w [CI commita `de2080f`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46068531715/job/140739732835). Następnie udowodnij `phiRankEightPolynomial_eq_rows`, rozszerzając tożsamość wielomianową z rzędu 4 na rząd 8. Do wyniku dla Ψ₁ i Ψ₂ pozostaje ścisłe zachowanie znaku przy całkowaniu. Niezależny rachunek w ℚ[X,q] porównał wszystkie 36 niezależnych par indeksów poniżej 8. Wagi zmiany zmiennych to współczynniki szeregu exp(Xu)(1+u)^(−5/4)(log(1+u)/4)^a/a!.

**S — identyfikacja współczynników rzędu 8.** [CI commita `6102cd4`](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/46069347793/job/140742279082) potwierdziło dodatni wyznacznik zmiany zmiennych, zgodność 15 rzędów pochodnych oraz tożsamość dla wpisu (7,7). `phiRankEightPolynomial_eq_rows` rozszerza sprawdzanie na wszystkie pary poniżej 8. `phiRankEightGaussian_eq_scaled_compact` identyfikuje współczynniki Gaussa po przeskalowaniu baz. Te dwie deklaracje oczekują na CI. Następna deklaracja to `phiRankEightTerm_eq_scaled_compact` dla całego bloku jednego kwadratu.

**S — komórka 59.** Oczekuje na CI. `psiOneCompactFifteen32Anchor_containsReal` weryfikuje wspólną kotwicę w 15/32 z panelu do 1/2. `psiOne_compact_cell59_signed_wronskians` używa tej kotwicy dla [59/128,15/32]. Dane pochodzą z dokładnego rachunku wymiernego dla siatki.

**S — niezależny ogon.** Dla rang do 8 można sprawdzić sumy wierszowe z jawnych współczynników `G_q` z §2.4. Po podstawieniu X=16, q=4 i zastąpieniu q−1 przez q, największa suma majorant współczynników ma granicę 2⁴⁶. Użyj max(i!,j!) jako majoranty √(i!j!). Dla większych X i q wyłącz czynniki (X/16)⁸ i (q/4)¹⁴. Wykładniczy czynnik exp(−(q−1)(X−16)) kompensuje cały pierwszy czynnik. Z `B_n` dostaje się 7q²X oraz iloraz kolejnych majorant co najwyżej (3/2)³²(3/8)⁸⁰<1/2. Rachunek wymierny potwierdził granicę perturbacji 2·1792·2⁴⁶·(3/8)⁴⁸<10⁻³. W Lean pozostają identyfikacja współczynników do rzędu 8, przeniesienie znaku znormalizowanego wyznacznika na wrońskian oraz ścisłe zachowanie znaków przez całkowanie dla t≥1/2. Do ostatniego kroku można redukować wyznacznik z wierszami pochodnych w t i ostatnim wierszem wartości w s przez dzielenie przez pierwszą funkcję oraz różniczkowanie ostatniego wiersza.

Proponowane liczniki wierszy dolnego trójkąta macierzy U w pierwszej komórce. Mianownik każdego wpisu wynosi 1024.

```text
4167
4252 9203
4287 9537 14068
4267 15198 14568 19486
3746 13569 39258 17881 34880
-3377 -11171 -36360 -4682 -32721 10292
3908 13208 35324 8445 33545 -9189 4694
```

**F — od dostatecznie dużych rzędów do każdego r.** Zaimplementuj jawny próg i połącz poniższe zakresy jednym dowodem pokrycia. Samo istnienie niejawnego R₀ nie uzasadnia startu przy 10¹¹. Dla każdego zakresu sprawdzaj wszystkie mniejsze minory przy jednym poziomie 2r.

| Rzędy | Dane i zadanie |
|---|---|
| 1–32 | Z `historical32/` odtwórz 459+1845+8615=10 919 komórek, w tym dodatkową zmianę skali dla 3017 komórek. Sprawdź złączenia przedziałów t i X, dwa końce każdego zakresu, ogon i osobne przypadki 1,2. |
| 33–649 | Warstwy parzystości dla h≥1. Dla centralnego p=k=r użyj podpisanego skalarnego dopełnienia Schura z §4.3. |
| 650–1449 | Warstwy pokrywają wszystkie h≥0. Sprawdź granice warstw i przynależność przypadków brzegowych. |
| 1450–10¹¹−1 | Odtwórz bloki rang i oszacowania aktywnych indeksów theta. Sprawdź nakładanie się bloków oraz powtórne sprawdzenie ostatniego przedziału indeksów K według lematu o pokryciu. Dane i kod: `upper/`, w tym `upper/kod/verify.py`. |
| Od 10¹¹ | Wyprowadź oszacowania ilościowe z `upper/large.md`, wartości przy progu i monotoniczność dalej; rozróżnij K<2, u≤4 i u>4. |

## Wspólna weryfikacja danych i pozostałe wyniki

**Checker i dodatek A.** Najpierw połącz dokładne przedziały wymierne/dyadyczne z nierównościami rzeczywistymi. Udowodnij raz poprawność operacji, ograniczeń normy, kongruencji trójkątnej dla bloków początkowych i zmiany znaku wykluczającej poziom. Połącz przybliżenia wpisów z rzeczywistymi momentami i pochodnymi. Obejmuje to ogony szeregu theta, reszty Taylora/Cauchy’ego, kwadratury i zaokrąglenia właściwe dla danej rodziny. Użyj kodu `W5/` tam, gdzie pasują obiekt, norma i wymiar. Generator może proponować bazę lub świadka. Dowodem jest poprawność checkera i sprawdzenie danych wraz z pokryciem. Zbiorczo sprawdzaj komórki lub paczki, a wielkość paczek dobieraj z czasów CI. Rozpakuj `certificates.zip` do katalogu roboczego i wykonaj `sha256sum -c SHA256SUMS` z jego katalogu głównego. `python verify_release.py` to szybka kontrola danych z dodatku B. Zależności formalne muszą obejmować użyte bajty certyfikatu albo wygenerowany z nich moduł Lean.

**S — minima 1–8.** Na [0,1/2] zastosuj checker do 64 komórek Φ (rzędy do 4), 67 komórek Ψ₁ (do 7) i 86 komórek Ψ₂ (do 8). Uzupełnij ogon z §2.4 i ścisłe zachowanie znaków przy całkowaniu. W przypadku r=5 można bezpośrednio użyć `W5.nuttall_r5` na całej półosi. W₅(Φ;0)<0 obsługuje punktowy certyfikat opisany powyżej. Wykaż z przedziałów W₈(Ψ₁;5/64)<0. Przez A połącz obie strony każdego minimum. Oczekiwane wartości to kolejno 0,0,0,0,1,1,1,2.

**L — §3.** Zdefiniuj liczbę zmian znaku i udowodnij ograniczenie zmian znaku pochodnych z własności zmniejszania wahań. Dla wysokich pochodnych Φ wyprowadź wzór współczynnikowy, jednostajną asymptotykę pary punktów siodłowych i separację składników theta na rozłącznych przedziałach. Zsumuj dolne ograniczenia i uzyskaj współczynnik 2/π² z lematu 3.2. Dopiero potem wprowadź część całkowitą k i przenieś wynik przez słabe RR na tw. 3.1. Warunek odbioru: dokładna nierówność dla każdego ε>0, łącznie z zależnością progu od ε.

**H — §5.** Sformalizuj przedziały momentów z kwadratury Fouriera, reszty i błędy arytmetyki stałoprzecinkowej. Wspólny checker macierzy otrzymuje: r=500, m=767, t=15/8192 oraz r=142, m=196, t=0. Odtwórz wzory znaków, porównania na sąsiednich poziomach jak w pracy i uwzględnij ciągłość w zerze. A i F dają odpowiednio 768≤m(500)≤1000 oraz 197≤m(142)≤284. Siatka 742 punktów ma status obliczenia pomocniczego.

**D — §6.1 i dodatek C.** Ustal normalizację β_j (zero dla ujemnych indeksów), D(n,r), F, a₀ i D_a. Udowodnij osobno każdy wiersz tw. 6.2:
1. n≥r≥1, z F, zachowania znaków i kryterium minorów kolejnych;
2. wszystkie n≥0, r≤9 561 277 002 984, z kryterium sektorowego C.1 i zweryfikowanej informacji o zerach;
3. n≤1 810 540 931 075 dla każdego r≥1, z twierdzenia Sry, tożsamości Jacobiego–Trudiego i Andréiefa, łącznie z zakresem r<n;
4. n≤110 000 000 000, ilościowy wynik fazowy D_a>0,069 a₀ʳPʳ z C.2–C.3;
5. 1≤n≤12 363 153 437 137 przy dodatkowym r+1>12Mₙ/(1−qₙ)² z C.4;
6. zbiór G o dolnej gęstości ≥1 669 159/2 478 195 i dla każdego n∈G osobny próg R(n). Zweryfikuj status zewnętrznego wyniku o proporcji zer i jego hipotezy przed dodaniem do rejestru literatury; jeśli pozostaje hipotezą, zachowaj to jawnie w statusie wiersza.

Certyfikuj zaokrąglenia stałych z `determinants/check_constants.py`. Te sześć twierdzeń ma różne kwantyfikatory. Przenieś je do końcowego modułu w postaci rozróżnialnych deklaracji.

**K — §6.** Z L i F złóż 1≤liminf m(r)/r≤limsup m(r)/r≤2. Dla nieparzystych r≥3 przy m=2r−1 wyprowadź zmianę znaku pomocniczego wrońskianu przy pierwszym dodatnim węźle (log 2)/2, z odpowiednimi stronami węzła. Istnienie granicy, dokładne minima dla 142 i 500 oraz RH pozostają poza katalogiem twierdzeń wersji 7.

**Z — odbiór.** Każdy wiersz mapuje się na publiczną deklarację, numer twierdzenia w pracy, import z modułu zbiorczego i zweryfikowany commit. Zbuduj całość na czystej kopii kodu z przypiętymi zależnościami, bez przywracania cache projektu, i wypisz `#print axioms` głównych wyników. Sprawdź brak `sorryAx`, rejestr założeń literaturowych oraz zakres zaufania do `native_decide`. Przy publikacji podaj polecenie odtworzenia, identyfikator rewizji i log. Twierdzenie pozostaje warunkowe, dopóki ma choć jedną hipotezę zawierającą potrzebny nowy wynik.

## Jak skrócić czas kompilacji

Punkt odniesienia (commit `824d9ca`): [pierwszy przebieg](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45967568402/job/140399822304) zbudował W5.Statement, Nuttall.Existence i Nuttall oraz zapisał cache projektu. [Powtórzenie na nowym runnerze](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45967568402/job/140400739827) odtworzyło ten sam klucz (880 107 bajtów). Krok `lake build Nuttall` trwał odpowiednio 14,8 s i 4,4 s; za drugim razem log podaje `Replayed Nuttall.Existence`. Czasy wyłączają przygotowanie zależności. Mathlib jest pobierany z upstream, co przy obecnym małym celu zajmuje większą część całego przebiegu. Przy rozbudowie mierz oba etapy osobno. Zapis częściowego cache po błędzie jest skonfigurowany; oba pomiary dotyczyły udanych kompilacji.

- Lokalnie zachowaj checkout i `.lake`. Po zmianie dowodu użyj `lake build Nuttall.Existence` lub celu aktualnie zmienianego modułu. Po połączeniu modułów uruchom `lake build Nuttall`. Lake korzysta z poprzednich wyników i śladów zależności. Zmiana centralnej definicji może prawidłowo uruchomić przebudowę jej użytkowników. Z tego powodu trzymaj ciężkie obliczenia i końcowe zestawienia w modułach importujących definicje, nie odwrotnie.
- Na CI workflow [preprint.yml](../.github/workflows/preprint.yml) pobiera gotowe biblioteki przez `lake exe cache get Mathlib`. Osobny cache projektu obejmuje `.lake/build` wraz ze śladami Lake. Klucz zgodności zawiera system, architekturę i skrót narzędzi oraz rozwiązanych zależności. Dokładny wpis ma dodatkowo skrót źródeł. Po zmianie Lean, Mathlib albo schematu kompilacji rozpocznij od zgodnego zestawu. Przy podejrzeniu błędu cache odtwórz problem w świeżym katalogu budowy.
- Po zmianie pliku Lean workflow próbuje odtworzyć najbliższy zgodny wpis, a następnie zawsze wywołuje Lake. Po błędzie kompilacji może zapisać już zbudowane moduły. Lake wznowi pracę od nieaktualnych lub brakujących celów; przerwany dowód w jednym pliku jest kompilowany ponownie od początku tego modułu. Nie czyść całego cache przy błędzie elaboracji.
- Push na gałąź kanoniczną tworzy cache dostępny dla PR-ów do niej. Wpis zapisany na scalającej rewizji PR ma zakres tego PR. Po scaleniu polegaj na przebiegu kanonicznym. Aktualizacje samego planu i instrukcji pomijają preprint CI. Zmiany konfiguracji cache oraz kodu powinny mieć log rzeczywistej kompilacji.
- Aktualizując checker, certyfikat lub importowane dane, w tym samym PR uwzględnij wejście w zależnościach Lake, filtrach uruchamiania i kluczu cache. Przetestuj zmianę przykładowego wejścia, aby wykazać unieważnienie odpowiedniego dowodu. Przy błędzie najpierw odczytaj najwcześniejszy błąd właściwego modułu, potem ponów jego cel.
- Korzystaj ze standardowego publicznego runnera. Mierz osobno pobranie Mathlib, odtworzenie cache, kompilację i zapis. Zachowuj większe archiwa lub zwiększaj liczbę równoległych zadań tylko po pomiarze, gdy przynosi to zysk. Przy presji na limit pozwól wygasać starym kopiom. Nie zmieniaj płatnego limitu konta w ramach aktualizacji dowodów.

## Rejestr twierdzeń przyjętych z literatury

- `Nuttall.Literature.andreief`. Tożsamość determinantowa Andréiefa, P. J. Forrester, *Meet Andréief, Bordeaux 1886, and Andreev, Kharkov 1882–83*, równanie (1.7) i §2.1. W Lean przyjmuje σ-skończoną miarę rzeczywistą i całkowalność każdego produktu fᵢgⱼ. Zastosowanie w `Nuttall.signed_wronskian_eq_andreief_integral` sprawdza te warunki dla wag i pochodnych szeregu theta. [Źródło](https://arxiv.org/abs/1806.10411)

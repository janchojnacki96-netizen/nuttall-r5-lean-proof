# Plan formalizacji preprintu Jana Chojnackiego o hipotezie Nuttalla (wersja 7)

Gałąź robocza: `formalization/preprint`. Źródła: [artykuł EN](../papers/linear-bounds/EN/main.tex), [artykuł PL](../papers/linear-bounds/PL/main.tex), [suplement z danymi](../papers/linear-bounds/certificates.zip). Numery twierdzeń i oznaczenia w tej notatce odnoszą się do wersji 7. Gdy zmienia się tekst pracy, porównaj tezy i zaktualizuj tylko zależne zadania.

## Stan i kolejność pracy

| Etap | Zależności | Stan i warunek ukończenia |
|---|---|---|
| B. Istniejące R5 | przypięta rewizja | **Zweryfikowany.** [W5.nuttall_r5](../W5/NuttallR5.lean), rewizja `dfaede6d`, [CI](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45486606898). Ścisłe znaki dla pierwszej całki na całej półosi. Audyt wykazuje 228 aksjomatów obliczeń natywnych obok trzech standardowych. |
| A. Definicje i redukcja istnienia | W5.Statement | **Częściowo.** [Existence.lean](../Nuttall/Existence.lean) definiuje iterowane całki i test znaków. `exists_level_of_eventual_two_mul` przyjmuje jako hipotezę wynik dla dużych R. [CI d6599bc](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45965923111). Do wykonania słabe RR, minimalny poziom i mosty poniżej. |
| U. Analityczny dowód dla dużych rzędów, tw. 1.2 | A; U1–U4 poniżej | **W toku, priorytet.** U1 ma zweryfikowaną tożsamość różniczkową i jej iteracje dla wszystkich poziomów oraz podpisany wyznacznik po odwróceniu wierszy. Postać momentowa iteracji g też jest zweryfikowana. Pozostają zastąpienie wpisów podpisanego wyznacznika momentami, reprezentacja Andréiefa i oszacowania U2–U4. |
| F. Jawna granica 2r dla wszystkich r, tw. 4.1 | U, wspólny checker, §2.4 i dod. A | **Otwarte.** Zamknąć wszystkie pięć zakresów r z tabeli §4.2. |
| S. Dokładne minima do 8, tw. 2.1 | A, B, checker, §2.4 | **Otwarte.** Dla każdego minimum uzyskać górną i dolną granicę dla słabego RR. |
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

**U1 — wyznacznik momentowy oczekuje na CI.** Złóż `tailIterate_auxiliary_eq_moment` z `twice_psi_succ_eq_auxiliary_iterate_sub` dla poziomów Ψⱼ₊₂. Wprowadź różnicę znormalizowanych wag wielomianowych oraz wykaż jej całkowalność przed połączeniem całek. Następnie użyj `signed_wronskian_psi_eq_tail_det`, żeby zastąpić wpisy macierzy momentami na zakresie rozpatrywanym w §4.1. Dla p≤r i r≥1 najmniejszy indeks wpisu przy m=2r wynosi 2r−2(p−1)≥2, więc wystarczy postać dla Ψⱼ₊₂.

## Ścieżka do twierdzeń 1.2 i 4.1

**A — znaczenie tezy.** Zdefiniuj słabe RR dla wszystkich rosnących dodatnich węzłów obu zmiennych i wszystkich 1≤p≤r, zgodnie z §1. Zdefiniuj najmniejszy skuteczny poziom z możliwością nieskończoności albo stosuj minimum dopiero po dowodzie istnienia. Udowodnij monotoniczność względem rzędu, słabe zachowanie RR przy całkowaniu, wystarczalność ścisłego testu wrońskianowego oraz wykluczenie słabego RR przez ściśle zły znak (zlanie węzłów i ciągłość także dla t=0). Dla lematu 1.1 potrzebne jest ponadto zachowanie ściśle poprawnych znaków przy całkowaniu, z warunkami całkowalności i zaniku. Oddziel pomocniczy test ścisły od definicji minimum w artykule.

**U1 — tożsamość całkowa z §4.** Rozwiń rachunek całek ogonowych, odwrócenie kolejności wierszy i znaki, zmianę zmiennych oraz sumy przesuniętych składników. Zastosuj tożsamość Andréiefa po sprawdzeniu zbieżności i hipotez całkowych. Warunek odbioru: dla właściwego zakresu otrzymać równość podpisanego wrońskianu z całką z równania oznaczonego `eq:anorm` i dodatnim czynnikiem normalizacyjnym. Obsłuż p=1 oddzielnie.

**U2 — macierz przesunięcia.** Sformalizuj odwrócenie kolumn, zmianę bazy o dodatnich przekątnych, normalizację dwumianową i kongruencję potęgi symetrycznej. Udowodnij oszacowania dla C_d oraz poprawki A_d−C_d, z osobnymi końcami d=0,1. Warunek odbioru: nierówność `eq:shift` i jednostajny margines lematu 4.2, również kiedy p=k=r i wykładnik 2r−p−k znika.

**U3 — dodatniość na centralnym obszarze.** Przenieś margines normowy <1 na znak każdego bloku, następnie na wyznacznik przy różnych węzłach przez redukcję układu Czebyszewa. Sprawdź węzły progowe i ostatni wrońskian dodatni prawie wszędzie. Osobno wyprowadź oszacowanie bezwzględnej całki na pominiętym obszarze względem części centralnej, z jednolitym błędem i warunkiem na pη. Zachowaj wszystkie mniejsze minory i wszystkie t≥0 przy tym samym poziomie 2R.

**U4 — złożenie istnienia.** Wykaż istnienie R₀ takie, że dla każdego R≥max(1,R₀) zachodzi `signRegularWronskians (2*R) R`. Użyj `exists_level_of_eventual_two_mul` i mostu A, aby uzyskać twierdzenie 1.2. To pierwszy cel publikacyjny osiągalny przed pełnym odtworzeniem certyfikatów skończonych rzędów.

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

**S — minima 1–8.** Na [0,1/2] zastosuj checker do 64 komórek Φ (rzędy do 4), 67 komórek Ψ₁ (do 7) i 86 komórek Ψ₂ (do 8). Uzupełnij ogon z §2.4 i ścisłe zachowanie znaków przy całkowaniu. W przypadku r=5 można bezpośrednio użyć `W5.nuttall_r5` na całej półosi. Wykaż z przedziałów W₅(Φ;0)<0 oraz W₈(Ψ₁;5/64)<0. Przez A połącz obie strony każdego minimum. Oczekiwane wartości to kolejno 0,0,0,0,1,1,1,2.

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

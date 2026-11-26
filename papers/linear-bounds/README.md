# Linear bounds for the integration order of the Riemann theta kernel
# Liniowe ograniczenia na liczbę całkowań jądra theta Riemanna

Jan Chojnacki · 26 November / listopada 2026

Wersja 7 w rozdziale 3 wyprowadza współczynnik π²/2 w dolnym oszacowaniu dla m(r). Dla każdego ε > 0 i dostatecznie dużych r zachodzi m(r) ≥ r − (π²/2 + ε)r/log r. W §6.2 dowodzimy, że dla nieparzystych r ≥ 3 przy m = 2r − 1 pomocniczy wrońskian zmienia znak przy pierwszym dodatnim węźle. W §4.2 podajemy przeskalowanie dla 3017 komórek, a w §2.3 niezależny rachunek sprawdzający wartość wrońskianu w 5/64.

Praca wyznacza pierwszych osiem minimów. Dla rzędów 1–4 wystarcza poziom 0, w rzędach 5–7 minimum wynosi 1, a dla rzędu 8 wynosi 2. W tym ostatnim przypadku 86 przedziałów pokrywa [0, 1/2], a znak przy 5/64 wyklucza jedno całkowanie. Świadki punktowe dają 197 ≤ m(142) ≤ 284 i 768 ≤ m(500) ≤ 1000 po połączeniu ich z ograniczeniem ogólnym. Dowody i polecenia odtworzenia znajdują się w rozdziałach 2 i 5 oraz w dodatku B.

In version 7, Section 3 obtains the coefficient π²/2 in the lower bound for m(r). For every ε > 0 and all sufficiently large r, m(r) ≥ r − (π²/2 + ε)r/log r. Section 6.2 proves that for odd r ≥ 3, at m = 2r − 1, the auxiliary Wronskian changes sign at the first positive knot. Section 4.2 gives the rescaling used on 3017 cells, and Section 2.3 gives an independent check of the Wronskian at 5/64.

The paper determines the first eight minima. Level 0 suffices through order 4, orders 5–7 have minimum 1, and order 8 has minimum 2. At order 8 the compact certificate covers [0, 1/2] with 86 intervals, and the witness at 5/64 excludes level one. Combining point witnesses with the general upper bound gives 197 ≤ m(142) ≤ 284 and 768 ≤ m(500) ≤ 1000. Sections 2 and 5 and Appendix B give proofs and reproduction commands.

## Czytanie i odtworzenie

Polski artykuł znajduje się w PL/Nuttall_preprint_PL.pdf, a angielski w EN/Nuttall_preprint_EN.pdf. Każdy z plików main.tex jest samodzielnym źródłem odpowiedniej wersji. W katalogu PL lub EN uruchom pdflatex main.tex dwukrotnie, aby utworzyć PDF z odsyłaczami. Wystarczy TeX Live z amsart i fontami Latin Modern.

Po rozpakowaniu certificates.zip zacznij od README.md. Polecenia weryfikacji pracują na lokalnych plikach. Zasięg matematyczny wyników, w tym różnicę między ścisłym świadkiem a testem na siatce dla rzędu 500, wyjaśniają rozdziały 5 i 6. Instrukcje dla certyfikatów znajdują się w dodatku B.

## Reading and reproduction

The English manuscript is EN/Nuttall_preprint_EN.pdf. The Polish translation is PL/Nuttall_preprint_PL.pdf. Each main.tex is a standalone source. From either language directory run pdflatex main.tex twice for the final PDF with cross-references. Use TeX Live with amsart and Latin Modern.

Unpack certificates.zip and read its README.md for the verification commands. Sections 5 and 6 distinguish the order-500 point witness from the exploratory mesh and discuss the scope of the asymptotic conclusions. Appendix B describes the computational materials.

Outer and inner archives each include SHA256SUMS covering their respective payloads. Run sha256sum -c SHA256SUMS from the unpacked root before replay.

§6.1 zestawia sześć warunków dodatniości D(n,r). W dodatku C.3 znajduje się niezależny dowód fazowy dla n ≤ 110 000 000 000, a w C.5 wyprowadzenie szerszego pasa z twierdzenia 1.2 Sry. Dodatek C zawiera dowody, założenia i granice liczbowe. Skrypt determinants/check_constants.py sprawdza te liczby.

Section 6.1 gives six sufficient conditions for positivity of D(n,r). Appendix C.3 gives the independent phase bound for n ≤ 110,000,000,000. Appendix C.5 derives the wider strip from Theorem 1.2 of Sra. Appendix C gives the proofs, assumptions, and numerical bounds. The script determinants/check_constants.py checks the constants.

W twierdzeniu 6.2 granica przesunięcia 12 363 153 437 137 w wierszu dotyczącym tożsamości Cauchy’ego obowiązuje przy podanym tam warunku na rząd. Dokładna dolna granica gęstości w ostatnim wierszu wynosi 1 669 159 / 2 478 195. Oba wnioski wyprowadza dodatek C.4.

In Theorem 6.2 the shift endpoint 12,363,153,437,137 in the Cauchy-identity row applies under the stated condition on the order. The final row has the density lower bound 1,669,159 / 2,478,195. Appendix C.4 derives both values.

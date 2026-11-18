import Mathlib

/-!
Exact rational interval partition and the ordered-field pivot implication.
This is NOT a certification of the analytic matrix entries.
-/
namespace W5

def endpointsNumerators : List ℕ := [
  12500000000000000, 34570312500000000, 40087890625000000, 42846679687500000, 45605468750000000,
  46984863281250000, 48364257812500000, 49053955078125000, 49743652343750000, 50433349609375000,
  51123046875000000, 51467895507812500, 51812744140625000, 52157592773437500, 52502441406250000,
  52847290039062500, 53192138671875000, 53536987304687500, 53709411621093750, 53881835937500000,
  54054260253906250, 54226684570312500, 54399108886718750, 54571533203125000, 54743957519531250,
  54916381835937500, 55088806152343750, 55175018310546875, 55261230468750000, 55347442626953125,
  55433654785156250, 55519866943359375, 55606079101562500, 55692291259765625, 55778503417968750,
  55864715576171875, 55950927734375000, 56037139892578125, 56123352050781250, 56166458129882812,
  56209564208984375, 56252670288085938, 56295776367187500, 56338882446289062, 56381988525390625,
  56425094604492188, 56468200683593750, 56511306762695312, 56554412841796875, 56597518920898438,
  56640625000000000
]

def endpoints : List ℚ :=
  endpointsNumerators.map (fun n => (n : ℚ) / 100000000000000000)

def lastFrom (a : ℚ) : List ℚ → ℚ
  | [] => a
  | b :: bs => lastFrom b bs

def Chain (a : ℚ) : List ℚ → ℝ → Prop
  | [], _ => False
  | b :: bs, x =>
    (((a : ℝ) ≤ x) ∧ (x ≤ (b : ℝ))) ∨ Chain b bs x

theorem chain_cover : ∀ (bs : List ℚ) (a : ℚ) (x : ℝ),
    (a : ℝ) ≤ x → x ≤ (lastFrom a bs : ℝ) →
    bs ≠ [] → Chain a bs x
  | [], _, _, _, _, hne => False.elim (hne rfl)
  | b :: bs, a, x, hstart, hend, _ => by
    change (((a : ℝ) ≤ x) ∧ (x ≤ (b : ℝ))) ∨ Chain b bs x
    by_cases hxb : x ≤ (b : ℝ)
    · exact Or.inl ⟨hstart, hxb⟩
    · have hbx : (b : ℝ) ≤ x := le_of_lt (lt_of_not_ge hxb)
      cases bs with
      | nil =>
        have hlast : x ≤ (b : ℝ) := hend
        exact False.elim (hxb hlast)
      | cons c cs =>
        apply Or.inr
        exact chain_cover (c :: cs) b x hbx hend (by simp)

theorem endpoint_count : endpointsNumerators.length = 51 := by decide
theorem endpoints_ne : endpoints ≠ [] := by decide
theorem endpoints_last : lastFrom 0 endpoints = (145 : ℚ) / 256 := by decide

theorem cover_51 (x : ℝ) (hzero : 0 ≤ x)
    (hmax : x ≤ (145 : ℝ) / 256) : Chain 0 endpoints x := by
  apply chain_cover endpoints 0 x
  · simpa using hzero
  · have heq : (((145 : ℚ) / 256 : ℚ) : ℝ) = (145 : ℝ) / 256 := by norm_num
    rw [endpoints_last, heq]
    exact hmax
  · exact endpoints_ne

def PivotSigns (p1 p2 p3 p4 p5 : ℝ) : Prop :=
  0 < p1 ∧ p2 < 0 ∧ 0 < p3 ∧ p4 < 0 ∧ 0 < p5

def ProductSigns (p1 p2 p3 p4 p5 : ℝ) : Prop :=
  0 < p1 ∧ p1 * p2 < 0 ∧ p1 * p2 * p3 < 0 ∧
  0 < p1 * p2 * p3 * p4 ∧ 0 < p1 * p2 * p3 * p4 * p5

theorem productSigns_of_pivotSigns {p1 p2 p3 p4 p5 : ℝ}
    (hp : PivotSigns p1 p2 p3 p4 p5) :
    ProductSigns p1 p2 p3 p4 p5 := by
  rcases hp with ⟨h1, h2, h3, h4, h5⟩
  have h12 : p1 * p2 < 0 := mul_neg_of_pos_of_neg h1 h2
  have h123 : p1 * p2 * p3 < 0 := mul_neg_of_neg_of_pos h12 h3
  have h1234 : 0 < p1 * p2 * p3 * p4 := mul_pos_of_neg_of_neg h123 h4
  have h12345 : 0 < p1 * p2 * p3 * p4 * p5 := mul_pos h1234 h5
  exact ⟨h1, h12, h123, h1234, h12345⟩
end W5

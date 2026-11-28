import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33602_aux

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def tbl (N : ℕ) (C : Circuit) (x y : Fin N) : Bool :=
  C.eval (oneEach x y)

def areaOf {N : ℕ} (f : Fin N → Fin N → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => f z.1 z.2 = true)).card

def hitsOf {N : ℕ} (f : Fin N → Fin N → Bool) (v : Fin N) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
    f z.1 z.2 = true ∧ (z.2.val + N - z.1.val) % N = v.val)).card

def IsLine {N : ℕ} (f : Fin N → Fin N → Bool) : Prop :=
  (∃ x0 : Fin N, ∀ x y, f x y = decide (x = x0)) ∨
  (∃ y0 : Fin N, ∀ x y, f x y = decide (y = y0))

def IsPair {N : ℕ} (f : Fin N → Fin N → Bool) : Prop :=
  ∃ T : Finset (Fin N), T.card = 2 ∧
    ((∀ x y : Fin N, f x y = decide (x ∈ T)) ∨ (∀ x y : Fin N, f x y = decide (y ∈ T)))

def IsTShape {N : ℕ} (f : Fin N → Fin N → Bool) : Prop :=
  (∃ x0 x1 y0 : Fin N, x0 ≠ x1 ∧ ∀ x y, f x y = decide (x = x0 ∨ x = x1 ∨ y = y0)) ∨
  (∃ y0 y1 x0 : Fin N, y0 ≠ y1 ∧ ∀ x y, f x y = decide (y = y0 ∨ y = y1 ∨ x = x0))

def Gate1Class {N : ℕ} (f : Fin N → Fin N → Bool) : Prop :=
  (∀ x y, f x y = false) ∨
  (∀ x y, f x y = true) ∨
  (∃ x0 y0 : Fin N, ∀ x y, f x y = decide (x = x0 ∧ y = y0)) ∨
  IsLine f ∨
  (∃ x0 y0 : Fin N, ∀ x y, f x y = decide (x = x0 ∨ y = y0)) ∨
  IsPair f ∨
  (∃ g : Fin N → Fin N → Bool, IsLine g ∧ ∀ x y, f x y = !g x y)

lemma oneEach_len {N : ℕ} (x y : Fin N) : (oneEach x y).length = N + N := by
  simp [oneEach]

lemma oneEach_getD_lt {N : ℕ} (x y : Fin N) {w : ℕ} (hw : w < N) :
    (oneEach x y).getD w false = decide (x = ⟨w, hw⟩) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw])]
  simp [hw, eq_comm]

lemma oneEach_getD_ge {N : ℕ} (x y : Fin N) {w : ℕ} (hw1 : N ≤ w) (hw2 : w < N + N) :
    (oneEach x y).getD w false = decide (y = ⟨w - N, by omega⟩) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hw1])]
  simp [eq_comm, show w - N < N by omega]

lemma oneEach_wire_isLine {N : ℕ} {w : ℕ} (hw : w < N + N) :
    IsLine (fun x y : Fin N => (oneEach x y).getD w false) := by
  by_cases h : w < N
  · left
    exact ⟨⟨w, h⟩, fun x y => oneEach_getD_lt x y h⟩
  · right
    have hge : N ≤ w := by omega
    exact ⟨⟨w - N, by omega⟩, fun x y => oneEach_getD_ge x y hge hw⟩

lemma areaOf_eq {N : ℕ} {f g : Fin N → Fin N → Bool} (h : ∀ x y, f x y = g x y) :
    areaOf f = areaOf g := by
  unfold areaOf
  congr 1
  ext z
  simp [h]

lemma areaOf_false {N : ℕ} : areaOf (fun _ _ : Fin N => false) = 0 := by
  simp [areaOf]

lemma areaOf_true {N : ℕ} : areaOf (fun _ _ : Fin N => true) = N * N := by
  simp [areaOf]

lemma areaOf_point {N : ℕ} (x0 y0 : Fin N) :
    areaOf (fun x y : Fin N => decide (x = x0 ∧ y = y0)) = 1 := by
  unfold areaOf
  have heq : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => decide (z.1 = x0 ∧ z.2 = y0) = true) =
      {(x0, y0)} := by
    ext ⟨x, y⟩
    simp
  rw [heq, Finset.card_singleton]

lemma areaOf_row {N : ℕ} (x0 : Fin N) :
    areaOf (fun x _ : Fin N => decide (x = x0)) = N := by
  unfold areaOf
  have heq : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => decide (z.1 = x0) = true) =
      ({x0} : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)) := by
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [heq, Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ, Fintype.card_fin]

lemma areaOf_col {N : ℕ} (y0 : Fin N) :
    areaOf (fun _ y : Fin N => decide (y = y0)) = N := by
  unfold areaOf
  have heq : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => decide (z.2 = y0) = true) =
      (Finset.univ : Finset (Fin N)) ×ˢ ({y0} : Finset (Fin N)) := by
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [heq, Finset.card_product, Finset.card_singleton, mul_one, Finset.card_univ, Fintype.card_fin]

lemma areaOf_isLine {N : ℕ} {f : Fin N → Fin N → Bool} (hf : IsLine f) : areaOf f = N := by
  rcases hf with ⟨x0, hx⟩ | ⟨y0, hy⟩
  · rw [areaOf_eq hx, areaOf_row]
  · rw [areaOf_eq hy, areaOf_col]

lemma areaOf_not {N : ℕ} (f : Fin N → Fin N → Bool) :
    areaOf (fun x y => !f x y) + areaOf f = N * N := by
  unfold areaOf
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N × Fin N))) (p := fun z => f z.1 z.2 = true)
  have heq : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (!f z.1 z.2) = true) =
      (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => ¬ f z.1 z.2 = true) := by
    ext z; simp
  rw [heq]
  have hcard : (Finset.univ : Finset (Fin N × Fin N)).card = N * N := by simp
  omega

lemma areaOf_and_le_left {N : ℕ} (f g : Fin N → Fin N → Bool) :
    areaOf (fun x y => f x y && g x y) ≤ areaOf f := by
  unfold areaOf
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true] at hz ⊢
  exact hz.1

lemma areaOf_and_le_right {N : ℕ} (f g : Fin N → Fin N → Bool) :
    areaOf (fun x y => f x y && g x y) ≤ areaOf g := by
  unfold areaOf
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true] at hz ⊢
  exact hz.2

lemma areaOf_le_or_left {N : ℕ} (f g : Fin N → Fin N → Bool) :
    areaOf f ≤ areaOf (fun x y => f x y || g x y) := by
  unfold areaOf
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.or_eq_true] at hz ⊢
  exact Or.inl hz

lemma areaOf_or_le_add {N : ℕ} (f g : Fin N → Fin N → Bool) :
    areaOf (fun x y => f x y || g x y) ≤ areaOf f + areaOf g := by
  unfold areaOf
  have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (f z.1 z.2 || g z.1 z.2) = true) ⊆
      (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => f z.1 z.2 = true) ∪
      (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => g z.1 z.2 = true) := by
    intro z hz
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Bool.or_eq_true] at hz ⊢
    exact hz
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma areaOf_cross {N : ℕ} (x0 y0 : Fin N) :
    areaOf (fun x y : Fin N => decide (x = x0 ∨ y = y0)) = 2 * N - 1 := by
  unfold areaOf
  have hu : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => decide (z.1 = x0 ∨ z.2 = y0) = true) =
      (({x0} : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))) ∪
      ((Finset.univ : Finset (Fin N)) ×ˢ ({y0} : Finset (Fin N))) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      Finset.mem_union, Finset.mem_product, Finset.mem_singleton, and_true, true_and]
  have hi : (({x0} : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))) ∩
      ((Finset.univ : Finset (Fin N)) ×ˢ ({y0} : Finset (Fin N))) = {(x0, y0)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
      and_true, true_and, Prod.mk.injEq]
  rw [hu]
  have h1 := Finset.card_union_add_card_inter
    (({x0} : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)))
    ((Finset.univ : Finset (Fin N)) ×ˢ ({y0} : Finset (Fin N)))
  rw [hi] at h1
  simp only [Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
    one_mul, mul_one] at h1
  omega

lemma areaOf_pair {N : ℕ} {f : Fin N → Fin N → Bool} (hf : IsPair f) : areaOf f = 2 * N := by
  rcases hf with ⟨T, hT, hx | hy⟩
  · rw [areaOf_eq hx]
    unfold areaOf
    have heq : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => decide (z.1 ∈ T) = true) =
        T ×ˢ (Finset.univ : Finset (Fin N)) := by
      ext ⟨x, y⟩; simp
    rw [heq, Finset.card_product, hT, Finset.card_univ, Fintype.card_fin]
  · rw [areaOf_eq hy]
    unfold areaOf
    have heq : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => decide (z.2 ∈ T) = true) =
        (Finset.univ : Finset (Fin N)) ×ˢ T := by
      ext ⟨x, y⟩; simp
    rw [heq, Finset.card_product, hT, Finset.card_univ, Fintype.card_fin, mul_comm]

lemma areaOf_three_rows {N : ℕ} {x0 x1 x2 : Fin N} (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) :
    areaOf (fun x _ : Fin N => decide (x = x0 ∨ x = x1 ∨ x = x2)) = 3 * N := by
  unfold areaOf
  let T : Finset (Fin N) := {x0, x1, x2}
  have hT : T.card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
      Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
  have heq : (Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => decide (z.1 = x0 ∨ z.1 = x1 ∨ z.1 = x2) = true) = T ×ˢ Finset.univ := by
    ext ⟨x, y⟩; simp [T]
  rw [heq, Finset.card_product, hT, Finset.card_univ, Fintype.card_fin]

lemma areaOf_three_cols {N : ℕ} {y0 y1 y2 : Fin N} (h01 : y0 ≠ y1) (h02 : y0 ≠ y2) (h12 : y1 ≠ y2) :
    areaOf (fun _ y : Fin N => decide (y = y0 ∨ y = y1 ∨ y = y2)) = 3 * N := by
  unfold areaOf
  let T : Finset (Fin N) := {y0, y1, y2}
  have hT : T.card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
      Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
  have heq : (Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => decide (z.2 = y0 ∨ z.2 = y1 ∨ z.2 = y2) = true) = Finset.univ ×ˢ T := by
    ext ⟨x, y⟩; simp [T]
  rw [heq, Finset.card_product, hT, Finset.card_univ, Fintype.card_fin, mul_comm]

lemma areaOf_tshape {N : ℕ} {f : Fin N → Fin N → Bool} (hf : IsTShape f) :
    areaOf f = 3 * N - 2 := by
  rcases hf with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
  · rw [areaOf_eq h]
    unfold areaOf
    let T : Finset (Fin N) := {x0, x1}
    have hT : T.card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have hu : (Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => decide (z.1 = x0 ∨ z.1 = x1 ∨ z.2 = y0) = true) =
        (T ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ ({y0} : Finset (Fin N))) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
        Finset.mem_union, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
        T, and_true, true_and, or_assoc]
    have hi : (T ×ˢ (Finset.univ : Finset (Fin N))) ∩
        ((Finset.univ : Finset (Fin N)) ×ˢ ({y0} : Finset (Fin N))) =
        T ×ˢ ({y0} : Finset (Fin N)) := by
      ext ⟨x, y⟩; simp
    rw [hu]
    have h1 := Finset.card_union_add_card_inter
      (T ×ˢ (Finset.univ : Finset (Fin N)))
      ((Finset.univ : Finset (Fin N)) ×ˢ ({y0} : Finset (Fin N)))
    rw [hi] at h1
    simp only [Finset.card_product, hT, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
      mul_one] at h1
    omega
  · rw [areaOf_eq h]
    unfold areaOf
    let T : Finset (Fin N) := {y0, y1}
    have hT : T.card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have hu : (Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => decide (z.2 = y0 ∨ z.2 = y1 ∨ z.1 = x0) = true) =
        (Finset.univ ×ˢ T) ∪ (({x0} : Finset (Fin N)) ×ˢ Finset.univ) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
        Finset.mem_union, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
        T, and_true, true_and, or_assoc]
    have hi : ((Finset.univ : Finset (Fin N)) ×ˢ T) ∩
        (({x0} : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))) =
        ({x0} : Finset (Fin N)) ×ˢ T := by
      ext ⟨x, y⟩; simp
    rw [hu]
    have h1 := Finset.card_union_add_card_inter
      ((Finset.univ : Finset (Fin N)) ×ˢ T)
      (({x0} : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)))
    rw [hi] at h1
    simp only [Finset.card_product, hT, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
      one_mul] at h1
    omega

lemma gate1_of_lines {N : ℕ} (g : Gate)
    (hg_len : g.inputs.length ≤ 2)
    (hg_op : g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
    (evalW : ℕ → Fin N → Fin N → Bool)
    (hlines : ∀ i ∈ g.inputs, IsLine (evalW i)) :
    Gate1Class (fun x y => g.op.eval (g.inputs.map (fun i => evalW i x y))) := by
  rcases hg_op with hop | hop | ⟨hop, hlen1⟩
  · rw [hop]
    rcases hli : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · right; left; intro x y; simp [GateOp.eval]
    · right; right; right; left
      simpa [GateOp.eval] using hlines a (by simp [hli])
    · have ha := hlines a (by simp [hli])
      have hb := hlines b (by simp [hli])
      rcases ha with ⟨x0, hx0⟩ | ⟨y0, hy0⟩ <;> rcases hb with ⟨x1, hx1⟩ | ⟨y1, hy1⟩
      · by_cases heq : x0 = x1
        · subst heq
          right; right; right; left; left
          exact ⟨x0, fun x y => by simp [GateOp.eval, hx0, hx1]⟩
        · left
          intro x y
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, hx0, hx1, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          by_cases h1 : x = x0
          · subst h1; exact Or.inr heq
          · exact Or.inl h1
      · right; right; left
        exact ⟨x0, y1, fun x y => by simp [GateOp.eval, hx0, hy1]⟩
      · right; right; left
        exact ⟨x1, y0, fun x y => by by_cases hx : x = x1 <;> by_cases hy : y = y0 <;> simp [GateOp.eval, hy0, hx1, hx, hy]⟩
      · by_cases heq : y0 = y1
        · subst heq
          right; right; right; left; right
          exact ⟨y0, fun x y => by simp [GateOp.eval, hy0, hy1]⟩
        · left
          intro x y
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, hy0, hy1, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          by_cases h1 : y = y0
          · subst h1; exact Or.inr heq
          · exact Or.inl h1
    · rw [hli] at hg_len; simp at hg_len
  · rw [hop]
    rcases hli : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · left; intro x y; simp [GateOp.eval]
    · right; right; right; left
      simpa [GateOp.eval] using hlines a (by simp [hli])
    · have ha := hlines a (by simp [hli])
      have hb := hlines b (by simp [hli])
      rcases ha with ⟨x0, hx0⟩ | ⟨y0, hy0⟩ <;> rcases hb with ⟨x1, hx1⟩ | ⟨y1, hy1⟩
      · by_cases heq : x0 = x1
        · subst heq
          right; right; right; left; left
          exact ⟨x0, fun x y => by simp [GateOp.eval, hx0, hx1]⟩
        · right; right; right; right; right; left
          refine ⟨{x0, x1}, ?_, Or.inl ?_⟩
          · rw [Finset.card_insert_of_notMem (by simp [heq]), Finset.card_singleton]
          · intro x y; simp [GateOp.eval, hx0, hx1]
      · right; right; right; right; left
        exact ⟨x0, y1, fun x y => by simp [GateOp.eval, hx0, hy1]⟩
      · right; right; right; right; left
        exact ⟨x1, y0, fun x y => by by_cases hx : x = x1 <;> by_cases hy : y = y0 <;> simp [GateOp.eval, hy0, hx1, hx, hy]⟩
      · by_cases heq : y0 = y1
        · subst heq
          right; right; right; left; right
          exact ⟨y0, fun x y => by simp [GateOp.eval, hy0, hy1]⟩
        · right; right; right; right; right; left
          refine ⟨{y0, y1}, ?_, Or.inr ?_⟩
          · rw [Finset.card_insert_of_notMem (by simp [heq]), Finset.card_singleton]
          · intro x y; simp [GateOp.eval, hy0, hy1]
    · rw [hli] at hg_len; simp at hg_len
  · rw [hop]
    rcases hli : g.inputs with _ | ⟨a, _ | _⟩
    · rw [hli] at hlen1; simp at hlen1
    · right; right; right; right; right; right
      exact ⟨evalW a, hlines a (by simp [hli]), fun x y => by simp [GateOp.eval]⟩
    · rw [hli] at hlen1; simp at hlen1

lemma gate1_classify {N : ℕ} (hN : 5 < N) {f : Fin N → Fin N → Bool}
    (hf : Gate1Class f) (harea : areaOf f ≤ 3 * N - 2) :
    IsTShape f ∨ IsPair f ∨ areaOf f ≤ 2 * N - 1 := by
  have hNN : 6 * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
  rcases hf with h0 | h1 | ⟨x0, y0, hpt⟩ | hline | ⟨x0, y0, hcr⟩ | hpair | ⟨g, hg, hnot⟩
  · right; right; rw [areaOf_eq h0, areaOf_false]; omega
  · rw [areaOf_eq h1, areaOf_true] at harea; omega
  · right; right; rw [areaOf_eq hpt, areaOf_point]; omega
  · right; right; rw [areaOf_isLine hline]; omega
  · right; right; rw [areaOf_eq hcr, areaOf_cross]
  · right; left; exact hpair
  · have hsum := areaOf_not g
    rw [areaOf_isLine hg, ← areaOf_eq hnot] at hsum
    omega

lemma gate1_area_cases {N : ℕ} {f : Fin N → Fin N → Bool} (hf : Gate1Class f) :
    areaOf f = 0 ∨ areaOf f = N * N ∨ areaOf f = 1 ∨ areaOf f = N ∨
    areaOf f = 2 * N - 1 ∨ areaOf f = 2 * N ∨ areaOf f + N = N * N := by
  rcases hf with h0 | h1 | ⟨x0, y0, hpt⟩ | hline | ⟨x0, y0, hcr⟩ | hpair | ⟨g, hg, hnot⟩
  · left; rw [areaOf_eq h0, areaOf_false]
  · right; left; rw [areaOf_eq h1, areaOf_true]
  · right; right; left; rw [areaOf_eq hpt, areaOf_point]
  · right; right; right; left; exact areaOf_isLine hline
  · right; right; right; right; left; rw [areaOf_eq hcr, areaOf_cross]
  · right; right; right; right; right; left; exact areaOf_pair hpair
  · right; right; right; right; right; right
    have hsum := areaOf_not g
    rw [areaOf_isLine hg, ← areaOf_eq hnot] at hsum
    exact hsum

lemma or_gate1_line_classify {N : ℕ} (hN : 5 < N) {f p : Fin N → Fin N → Bool}
    (hf : Gate1Class f) (hp : IsLine p)
    (harea : areaOf (fun x y => f x y || p x y) ≤ 3 * N - 2) :
    IsTShape (fun x y => f x y || p x y) ∨
    IsPair (fun x y => f x y || p x y) ∨
    areaOf (fun x y => f x y || p x y) ≤ 2 * N - 1 := by
  have hNN : 6 * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
  rcases hf with h0 | h1 | ⟨x0, y0, hpt⟩ | hline | ⟨x0, y0, hcr⟩ | hpair | ⟨g, hg, hnot⟩
  · right; right
    have heq : ∀ x y, (f x y || p x y) = p x y := fun x y => by simp [h0]
    rw [areaOf_eq heq, areaOf_isLine hp]; omega
  · have hle := areaOf_le_or_left f p
    rw [areaOf_eq h1, areaOf_true] at hle
    omega
  · right; right
    have hle := areaOf_or_le_add f p
    rw [areaOf_eq hpt, areaOf_point, areaOf_isLine hp] at hle
    omega
  · have hg1 : Gate1Class (fun x y => f x y || p x y) := by
      rcases hline with ⟨x0, hx0⟩ | ⟨y0, hy0⟩ <;> rcases hp with ⟨x1, hx1⟩ | ⟨y1, hy1⟩
      · by_cases heq : x0 = x1
        · subst heq; right; right; right; left; left; exact ⟨x0, fun x y => by simp [hx0, hx1]⟩
        · right; right; right; right; right; left
          refine ⟨{x0, x1}, ?_, Or.inl fun x y => by simp [hx0, hx1]⟩
          rw [Finset.card_insert_of_notMem (by simp [heq]), Finset.card_singleton]
      · right; right; right; right; left; exact ⟨x0, y1, fun x y => by simp [hx0, hy1]⟩
      · right; right; right; right; left
        exact ⟨x1, y0, fun x y => by by_cases hx : x = x1 <;> by_cases hy : y = y0 <;> simp [hy0, hx1, hx, hy]⟩
      · by_cases heq : y0 = y1
        · subst heq; right; right; right; left; right; exact ⟨y0, fun x y => by simp [hy0, hy1]⟩
        · right; right; right; right; right; left
          refine ⟨{y0, y1}, ?_, Or.inr fun x y => by simp [hy0, hy1]⟩
          rw [Finset.card_insert_of_notMem (by simp [heq]), Finset.card_singleton]
    exact gate1_classify hN hg1 harea
  · rcases hp with ⟨x1, hx1⟩ | ⟨y1, hy1⟩
    · by_cases heq : x0 = x1
      · rw [← heq] at hx1
        right; right
        have h' : ∀ x y, (f x y || p x y) = decide (x = x0 ∨ y = y0) := by
          intro x y; by_cases h1 : x = x0 <;> by_cases h2 : y = y0 <;> simp [hcr, hx1, h1, h2]
        rw [areaOf_eq h', areaOf_cross]
      · left; left
        exact ⟨x0, x1, y0, heq, fun x y => by
          by_cases h1 : x = x0 <;> by_cases h2 : y = y0 <;> by_cases h3 : x = x1 <;>
            simp [hcr, hx1, h1, h2, h3]⟩
    · by_cases heq : y0 = y1
      · rw [← heq] at hy1
        right; right
        have h' : ∀ x y, (f x y || p x y) = decide (x = x0 ∨ y = y0) := by
          intro x y; by_cases h1 : x = x0 <;> by_cases h2 : y = y0 <;> simp [hcr, hy1, h1, h2]
        rw [areaOf_eq h', areaOf_cross]
      · left; right
        exact ⟨y0, y1, x0, heq, fun x y => by
          by_cases h1 : x = x0 <;> by_cases h2 : y = y0 <;> by_cases h3 : y = y1 <;>
            simp [hcr, hy1, h1, h2, h3]⟩
  · rcases hpair with ⟨T, hT, hx | hy⟩
    · rcases Finset.card_eq_two.mp hT with ⟨x0, x1, hne, rfl⟩
      rcases hp with ⟨x2, hx2⟩ | ⟨y0, hy0⟩
      · by_cases h20 : x2 = x0
        · rw [h20] at hx2
          right; left
          refine ⟨{x0, x1}, hT, Or.inl fun x y => ?_⟩
          by_cases h1 : x = x0 <;> by_cases h2 : x = x1 <;> simp [hx, hx2, h1, h2]
        · by_cases h21 : x2 = x1
          · rw [h21] at hx2
            right; left
            refine ⟨{x0, x1}, hT, Or.inl fun x y => ?_⟩
            by_cases h1 : x = x0 <;> by_cases h2 : x = x1 <;> simp [hx, hx2, h1, h2]
          · have h3 : ∀ x y, (f x y || p x y) = decide (x = x0 ∨ x = x1 ∨ x = x2) := by
              intro x y
              by_cases h1 : x = x0 <;> by_cases h2 : x = x1 <;> by_cases h3' : x = x2 <;>
                simp [hx, hx2, h1, h2, h3']
            rw [areaOf_eq h3, areaOf_three_rows hne (Ne.symm h20) (Ne.symm h21)] at harea
            omega
      · left; left
        refine ⟨x0, x1, y0, hne, fun x y => ?_⟩
        by_cases h1 : x = x0 <;> by_cases h2 : x = x1 <;> by_cases h3 : y = y0 <;>
          simp [hx, hy0, h1, h2, h3]
    · rcases Finset.card_eq_two.mp hT with ⟨y0, y1, hne, rfl⟩
      rcases hp with ⟨x0, hx0⟩ | ⟨y2, hy2⟩
      · left; right
        refine ⟨y0, y1, x0, hne, fun x y => ?_⟩
        by_cases h1 : y = y0 <;> by_cases h2 : y = y1 <;> by_cases h3 : x = x0 <;>
          simp [hy, hx0, h1, h2, h3]
      · by_cases h20 : y2 = y0
        · rw [h20] at hy2
          right; left
          refine ⟨{y0, y1}, hT, Or.inr fun x y => ?_⟩
          by_cases h1 : y = y0 <;> by_cases h2 : y = y1 <;> simp [hy, hy2, h1, h2]
        · by_cases h21 : y2 = y1
          · rw [h21] at hy2
            right; left
            refine ⟨{y0, y1}, hT, Or.inr fun x y => ?_⟩
            by_cases h1 : y = y0 <;> by_cases h2 : y = y1 <;> simp [hy, hy2, h1, h2]
          · have h3 : ∀ x y, (f x y || p x y) = decide (y = y0 ∨ y = y1 ∨ y = y2) := by
              intro x y
              by_cases h1 : y = y0 <;> by_cases h2 : y = y1 <;> by_cases h3' : y = y2 <;>
                simp [hy, hy2, h1, h2, h3']
            rw [areaOf_eq h3, areaOf_three_cols hne (Ne.symm h20) (Ne.symm h21)] at harea
            omega
  · have hle := areaOf_le_or_left f p
    have hsum := areaOf_not g
    rw [areaOf_isLine hg, ← areaOf_eq hnot] at hsum
    omega

lemma fits_classify {N : ℕ} (hN : 5 < N) (C : Circuit)
    (hRB : ReadsBack (N + N) C)
    (hout : C.output < N + N + C.size)
    (hgates : ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (hsize : C.size ≤ 2)
    (harea : areaOf (tbl N C) ≤ 3 * N - 2) :
    IsTShape (tbl N C) ∨ IsPair (tbl N C) ∨ areaOf (tbl N C) ≤ 2 * N - 1 := by
  have hNN : 6 * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
  rcases hgl : C.gates with _ | ⟨g0, _ | ⟨g1, _ | _⟩⟩
  · have hout' : C.output < N + N := by simp [Circuit.size, hgl] at hout; exact hout
    have hline : IsLine (tbl N C) := by
      have heq : ∀ x y : Fin N, tbl N C x y = (oneEach x y).getD C.output false := by
        intro x y; simp [tbl, Circuit.eval, Circuit.wires, hgl]
      rcases oneEach_wire_isLine (N := N) hout' with ⟨x0, hx⟩ | ⟨y0, hy⟩
      · left; exact ⟨x0, fun x y => (heq x y).trans (hx x y)⟩
      · right; exact ⟨y0, fun x y => (heq x y).trans (hy x y)⟩
    right; right; rw [areaOf_isLine hline]; omega
  · have hrb0 : ∀ i ∈ g0.inputs, i < N + N := by
      intro i hi
      have h0 := hRB 0 (by simp [hgl]) i
      simp only [gateAt, hgl, List.getD_cons_zero] at h0
      exact h0 hi
    have hg0 := hgates g0 (by simp [hgl])
    let f0 : Fin N → Fin N → Bool := fun x y =>
      g0.op.eval (g0.inputs.map (fun i => (oneEach x y).getD i false))
    have hf0 : Gate1Class f0 := by
      refine gate1_of_lines g0 hg0.1 hg0.2 (fun i x y => (oneEach x y).getD i false) ?_
      intro i hi
      exact oneEach_wire_isLine (hrb0 i hi)
    have hout' : C.output < N + N + 1 := by simp [Circuit.size, hgl] at hout; omega
    by_cases hlt : C.output < N + N
    · have heq : ∀ x y : Fin N, tbl N C x y = (oneEach x y).getD C.output false := by
        intro x y
        simp only [tbl, Circuit.eval, Circuit.wires, hgl, List.foldl_cons, List.foldl_nil]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [oneEach_len]; exact hlt)]
      have hline : IsLine (tbl N C) := by
        rcases oneEach_wire_isLine (N := N) hlt with ⟨x0, hx⟩ | ⟨y0, hy⟩
        · left; exact ⟨x0, fun x y => (heq x y).trans (hx x y)⟩
        · right; exact ⟨y0, fun x y => (heq x y).trans (hy x y)⟩
      right; right; rw [areaOf_isLine hline]; omega
    · have hout_eq : C.output = N + N := by omega
      have heq : ∀ x y : Fin N, tbl N C x y = f0 x y := by
        intro x y
        simp only [tbl, Circuit.eval, Circuit.wires, hgl, hout_eq, List.foldl_cons, List.foldl_nil, f0]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [oneEach_len])]
        simp [oneEach_len]
      rw [areaOf_eq heq] at harea
      have hcl := gate1_classify hN hf0 harea
      rcases hcl with hT | hP | hA
      · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
        · left; exact ⟨x0, x1, y0, hne, fun x y => (heq x y).trans (h x y)⟩
        · right; exact ⟨y0, y1, x0, hne, fun x y => (heq x y).trans (h x y)⟩
      · right; left; rcases hP with ⟨T, hT, hx | hy⟩
        · exact ⟨T, hT, Or.inl fun x y => (heq x y).trans (hx x y)⟩
        · exact ⟨T, hT, Or.inr fun x y => (heq x y).trans (hy x y)⟩
      · right; right; rw [areaOf_eq heq]; exact hA
  · have hrb0 : ∀ i ∈ g0.inputs, i < N + N := by
      intro i hi
      have h0 := hRB 0 (by simp [hgl]) i
      simp only [gateAt, hgl, List.getD_cons_zero] at h0
      exact h0 hi
    have hrb1 : ∀ i ∈ g1.inputs, i < N + N + 1 := by
      intro i hi
      have h1 := hRB 1 (by simp [hgl]) i
      simp only [gateAt, hgl, List.getD_cons_succ, List.getD_cons_zero] at h1
      exact h1 hi
    have hg0 := hgates g0 (by simp [hgl])
    have hg1 := hgates g1 (by simp [hgl])
    let f0 : Fin N → Fin N → Bool := fun x y =>
      g0.op.eval (g0.inputs.map (fun i => (oneEach x y).getD i false))
    have hf0 : Gate1Class f0 := by
      refine gate1_of_lines g0 hg0.1 hg0.2 (fun i x y => (oneEach x y).getD i false) ?_
      intro i hi; exact oneEach_wire_isLine (hrb0 i hi)
    let w1 : Fin N → Fin N → List Bool := fun x y => oneEach x y ++ [f0 x y]
    have hw1_len : ∀ x y : Fin N, (w1 x y).length = N + N + 1 := by
      intro x y; simp [w1, oneEach_len]
    have hw1_lt : ∀ {i : ℕ}, i < N + N → ∀ x y : Fin N, (w1 x y).getD i false = (oneEach x y).getD i false := by
      intro i hi x y
      simp only [w1]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [oneEach_len]; exact hi)]
    have hw1_eq : ∀ x y : Fin N, (w1 x y).getD (N + N) false = f0 x y := by
      intro x y
      simp only [w1]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [oneEach_len])]
      simp [oneEach_len]
    let f1 : Fin N → Fin N → Bool := fun x y =>
      g1.op.eval (g1.inputs.map (fun i => (w1 x y).getD i false))
    have hout' : C.output < N + N + 2 := by simp [Circuit.size, hgl] at hout; exact hout
    by_cases hlt0 : C.output < N + N
    · have heq : ∀ x y : Fin N, tbl N C x y = (oneEach x y).getD C.output false := by
        intro x y
        simp only [tbl, Circuit.eval, Circuit.wires, hgl, List.foldl_cons, List.foldl_nil]
        change ((w1 x y) ++ [f1 x y]).getD C.output false = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hw1_len]; omega),
          ← List.getD_eq_getElem?_getD, hw1_lt hlt0]
      have hline : IsLine (tbl N C) := by
        rcases oneEach_wire_isLine (N := N) hlt0 with ⟨x0, hx⟩ | ⟨y0, hy⟩
        · left; exact ⟨x0, fun x y => (heq x y).trans (hx x y)⟩
        · right; exact ⟨y0, fun x y => (heq x y).trans (hy x y)⟩
      right; right; rw [areaOf_isLine hline]; omega
    · by_cases hlt1 : C.output = N + N
      · have heq : ∀ x y : Fin N, tbl N C x y = f0 x y := by
          intro x y
          simp only [tbl, Circuit.eval, Circuit.wires, hgl, hlt1, List.foldl_cons, List.foldl_nil]
          change ((w1 x y) ++ [f1 x y]).getD (N + N) false = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hw1_len]; omega),
            ← List.getD_eq_getElem?_getD, hw1_eq]
        rw [areaOf_eq heq] at harea
        rcases gate1_classify hN hf0 harea with hT | hP | hA
        · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
          · left; exact ⟨x0, x1, y0, hne, fun x y => (heq x y).trans (h x y)⟩
          · right; exact ⟨y0, y1, x0, hne, fun x y => (heq x y).trans (h x y)⟩
        · right; left; rcases hP with ⟨T, hT, hx | hy⟩
          · exact ⟨T, hT, Or.inl fun x y => (heq x y).trans (hx x y)⟩
          · exact ⟨T, hT, Or.inr fun x y => (heq x y).trans (hy x y)⟩
        · right; right; rw [areaOf_eq heq]; exact hA
      · have hout_eq : C.output = N + N + 1 := by omega
        have heq : ∀ x y : Fin N, tbl N C x y = f1 x y := by
          intro x y
          simp only [tbl, Circuit.eval, Circuit.wires, hgl, hout_eq, List.foldl_cons, List.foldl_nil]
          change ((w1 x y) ++ [f1 x y]).getD (N + N + 1) false = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hw1_len])]
          simp [hw1_len]
        have harea1 : areaOf f1 ≤ 3 * N - 2 := by rw [← areaOf_eq heq]; exact harea
        have hf1_cl : IsTShape f1 ∨ IsPair f1 ∨ areaOf f1 ≤ 2 * N - 1 := by
          have hget_cl : ∀ i ∈ g1.inputs,
              (IsLine (fun x y => (w1 x y).getD i false)) ∨
              (∀ x y, (w1 x y).getD i false = f0 x y) := by
            intro i hi
            have hilt := hrb1 i hi
            by_cases h : i < N + N
            · left
              rcases oneEach_wire_isLine (N := N) h with ⟨x0, hx⟩ | ⟨y0, hy⟩
              · left; exact ⟨x0, fun x y => (hw1_lt h x y).trans (hx x y)⟩
              · right; exact ⟨y0, fun x y => (hw1_lt h x y).trans (hy x y)⟩
            · right
              have hieq : i = N + N := by omega
              subst hieq; exact hw1_eq
          rcases hg1.2 with hop | hop | ⟨hop, hlen1⟩
          · rcases hli : g1.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · have h1 : ∀ x y, f1 x y = true := fun x y => by simp [f1, hop, hli, GateOp.eval]
              rw [areaOf_eq h1, areaOf_true] at harea1; omega
            · have ha := hget_cl a (by simp [hli])
              have h1 : ∀ x y, f1 x y = (w1 x y).getD a false := fun x y => by
                simp [f1, hop, hli, GateOp.eval]
              rcases ha with hline | hfeq
              · right; right; rw [areaOf_eq h1, areaOf_isLine hline]; omega
              · have h1' : ∀ x y, f1 x y = f0 x y := fun x y => (h1 x y).trans (hfeq x y)
                rw [areaOf_eq h1'] at harea1
                rcases gate1_classify hN hf0 harea1 with hT | hP | hA
                · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
                  · left; exact ⟨x0, x1, y0, hne, fun x y => (h1' x y).trans (h x y)⟩
                  · right; exact ⟨y0, y1, x0, hne, fun x y => (h1' x y).trans (h x y)⟩
                · right; left; rcases hP with ⟨T, hT, hx | hy⟩
                  · exact ⟨T, hT, Or.inl fun x y => (h1' x y).trans (hx x y)⟩
                  · exact ⟨T, hT, Or.inr fun x y => (h1' x y).trans (hy x y)⟩
                · right; right; rw [areaOf_eq h1']; exact hA
            · have ha := hget_cl a (by simp [hli])
              have hb := hget_cl b (by simp [hli])
              have h1 : ∀ x y, f1 x y = ((w1 x y).getD a false && (w1 x y).getD b false) :=
                fun x y => by simp [f1, hop, hli, GateOp.eval]
              rcases ha with hline | ha0
              · right; right
                have hle := areaOf_and_le_left (fun x y => (w1 x y).getD a false) (fun x y => (w1 x y).getD b false)
                rw [areaOf_isLine hline, ← areaOf_eq h1] at hle; omega
              · rcases hb with hline | hb0
                · right; right
                  have hle := areaOf_and_le_right (fun x y => (w1 x y).getD a false) (fun x y => (w1 x y).getD b false)
                  rw [areaOf_isLine hline, ← areaOf_eq h1] at hle; omega
                · have h1' : ∀ x y, f1 x y = f0 x y := fun x y => by
                    rw [h1, ha0, hb0, Bool.and_self]
                  rw [areaOf_eq h1'] at harea1
                  rcases gate1_classify hN hf0 harea1 with hT | hP | hA
                  · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
                    · left; exact ⟨x0, x1, y0, hne, fun x y => (h1' x y).trans (h x y)⟩
                    · right; exact ⟨y0, y1, x0, hne, fun x y => (h1' x y).trans (h x y)⟩
                  · right; left; rcases hP with ⟨T, hT, hx | hy⟩
                    · exact ⟨T, hT, Or.inl fun x y => (h1' x y).trans (hx x y)⟩
                    · exact ⟨T, hT, Or.inr fun x y => (h1' x y).trans (hy x y)⟩
                  · right; right; rw [areaOf_eq h1']; exact hA
            · have := hg1.1; rw [hli] at this; simp at this
          · rcases hli : g1.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · right; right
              have h1 : ∀ x y, f1 x y = false := fun x y => by simp [f1, hop, hli, GateOp.eval]
              rw [areaOf_eq h1, areaOf_false]; omega
            · have ha := hget_cl a (by simp [hli])
              have h1 : ∀ x y, f1 x y = (w1 x y).getD a false := fun x y => by
                simp [f1, hop, hli, GateOp.eval]
              rcases ha with hline | hfeq
              · right; right; rw [areaOf_eq h1, areaOf_isLine hline]; omega
              · have h1' : ∀ x y, f1 x y = f0 x y := fun x y => (h1 x y).trans (hfeq x y)
                rw [areaOf_eq h1'] at harea1
                rcases gate1_classify hN hf0 harea1 with hT | hP | hA
                · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
                  · left; exact ⟨x0, x1, y0, hne, fun x y => (h1' x y).trans (h x y)⟩
                  · right; exact ⟨y0, y1, x0, hne, fun x y => (h1' x y).trans (h x y)⟩
                · right; left; rcases hP with ⟨T, hT, hx | hy⟩
                  · exact ⟨T, hT, Or.inl fun x y => (h1' x y).trans (hx x y)⟩
                  · exact ⟨T, hT, Or.inr fun x y => (h1' x y).trans (hy x y)⟩
                · right; right; rw [areaOf_eq h1']; exact hA
            · have ha := hget_cl a (by simp [hli])
              have hb := hget_cl b (by simp [hli])
              have h1 : ∀ x y, f1 x y = ((w1 x y).getD a false || (w1 x y).getD b false) :=
                fun x y => by simp [f1, hop, hli, GateOp.eval]
              rcases ha with hal | ha0 <;> rcases hb with hbl | hb0
              · have hcl := or_gate1_line_classify hN (Or.inr (Or.inr (Or.inr (Or.inl hal)))) hbl
                  (by rw [← areaOf_eq h1]; exact harea1)
                rcases hcl with hT | hP | hA
                · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
                  · left; exact ⟨x0, x1, y0, hne, fun x y => (h1 x y).trans (h x y)⟩
                  · right; exact ⟨y0, y1, x0, hne, fun x y => (h1 x y).trans (h x y)⟩
                · right; left; rcases hP with ⟨T, hT, hx | hy⟩
                  · exact ⟨T, hT, Or.inl fun x y => (h1 x y).trans (hx x y)⟩
                  · exact ⟨T, hT, Or.inr fun x y => (h1 x y).trans (hy x y)⟩
                · right; right; rw [areaOf_eq h1]; exact hA
              · have h1' : ∀ x y, f1 x y = (f0 x y || (w1 x y).getD a false) := fun x y => by
                  rw [h1, hb0, Bool.or_comm]
                have hcl := or_gate1_line_classify hN hf0 hal (by rw [← areaOf_eq h1']; exact harea1)
                rcases hcl with hT | hP | hA
                · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
                  · left; exact ⟨x0, x1, y0, hne, fun x y => (h1' x y).trans (h x y)⟩
                  · right; exact ⟨y0, y1, x0, hne, fun x y => (h1' x y).trans (h x y)⟩
                · right; left; rcases hP with ⟨T, hT, hx | hy⟩
                  · exact ⟨T, hT, Or.inl fun x y => (h1' x y).trans (hx x y)⟩
                  · exact ⟨T, hT, Or.inr fun x y => (h1' x y).trans (hy x y)⟩
                · right; right; rw [areaOf_eq h1']; exact hA
              · have h1' : ∀ x y, f1 x y = (f0 x y || (w1 x y).getD b false) := fun x y => by
                  rw [h1, ha0]
                have hcl := or_gate1_line_classify hN hf0 hbl (by rw [← areaOf_eq h1']; exact harea1)
                rcases hcl with hT | hP | hA
                · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
                  · left; exact ⟨x0, x1, y0, hne, fun x y => (h1' x y).trans (h x y)⟩
                  · right; exact ⟨y0, y1, x0, hne, fun x y => (h1' x y).trans (h x y)⟩
                · right; left; rcases hP with ⟨T, hT, hx | hy⟩
                  · exact ⟨T, hT, Or.inl fun x y => (h1' x y).trans (hx x y)⟩
                  · exact ⟨T, hT, Or.inr fun x y => (h1' x y).trans (hy x y)⟩
                · right; right; rw [areaOf_eq h1']; exact hA
              · have h1' : ∀ x y, f1 x y = f0 x y := fun x y => by
                  rw [h1, ha0, hb0, Bool.or_self]
                rw [areaOf_eq h1'] at harea1
                rcases gate1_classify hN hf0 harea1 with hT | hP | hA
                · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
                  · left; exact ⟨x0, x1, y0, hne, fun x y => (h1' x y).trans (h x y)⟩
                  · right; exact ⟨y0, y1, x0, hne, fun x y => (h1' x y).trans (h x y)⟩
                · right; left; rcases hP with ⟨T, hT, hx | hy⟩
                  · exact ⟨T, hT, Or.inl fun x y => (h1' x y).trans (hx x y)⟩
                  · exact ⟨T, hT, Or.inr fun x y => (h1' x y).trans (hy x y)⟩
                · right; right; rw [areaOf_eq h1']; exact hA
            · have := hg1.1; rw [hli] at this; simp at this
          · rcases hli : g1.inputs with _ | ⟨a, _ | _⟩
            · rw [hli] at hlen1; simp at hlen1
            · have ha := hget_cl a (by simp [hli])
              have h1 : ∀ x y, f1 x y = !((w1 x y).getD a false) := fun x y => by
                simp [f1, hop, hli, GateOp.eval]
              rcases ha with hline | ha0
              · have hsum := areaOf_not (fun x y => (w1 x y).getD a false)
                rw [areaOf_isLine hline, ← areaOf_eq h1] at hsum
                omega
              · have h1' : ∀ x y, f1 x y = !f0 x y := fun x y => by rw [h1, ha0]
                have hsum := areaOf_not f0
                rw [← areaOf_eq h1'] at hsum
                rcases gate1_area_cases hf0 with ha_eq | ha_eq | ha_eq | ha_eq | ha_eq | ha_eq | ha_eq
                · omega
                · right; right; omega
                · omega
                · omega
                · omega
                · omega
                · right; right; omega
            · rw [hli] at hlen1; simp at hlen1
        rcases hf1_cl with hT | hP | hA
        · left; rcases hT with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
          · left; exact ⟨x0, x1, y0, hne, fun x y => (heq x y).trans (h x y)⟩
          · right; exact ⟨y0, y1, x0, hne, fun x y => (heq x y).trans (h x y)⟩
        · right; left; rcases hP with ⟨T, hT, hx | hy⟩
          · exact ⟨T, hT, Or.inl fun x y => (heq x y).trans (hx x y)⟩
          · exact ⟨T, hT, Or.inr fun x y => (heq x y).trans (hy x y)⟩
        · right; right; rw [areaOf_eq heq]; exact hA
  · simp [Circuit.size, hgl] at hsize

lemma shift_unique_y {N : ℕ} (x v : Fin N) :
    (((x.val + v.val) % N + N - x.val) % N = v.val) ∧
    (∀ y : Fin N, (y.val + N - x.val) % N = v.val → y = ⟨(x.val + v.val) % N, Nat.mod_lt _ x.pos⟩) := by
  have hN : 0 < N := x.pos
  constructor
  · have hx := x.isLt
    have hv := v.isLt
    by_cases hlt : x.val + v.val < N
    · have hm : (x.val + v.val) % N = x.val + v.val := Nat.mod_eq_of_lt hlt
      rw [hm]
      have h1 : x.val + v.val + N - x.val = v.val + N := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hv]
    · have hmod : (x.val + v.val) % N = x.val + v.val - N := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have h1 : x.val + v.val - N + N - x.val = v.val := by omega
      rw [h1, Nat.mod_eq_of_lt hv]
  · intro y hy
    have hx := x.isLt
    have hv := v.isLt
    have hyl := y.isLt
    apply Fin.ext
    simp only
    by_cases hxy : x.val ≤ y.val
    · have h1 : y.val + N - x.val = (y.val - x.val) + N := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hy
      have h2 : x.val + v.val = y.val := by omega
      rw [h2, Nat.mod_eq_of_lt hyl]
    · rw [Nat.mod_eq_of_lt (by omega)] at hy
      have h2 : x.val + v.val = y.val + N := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hyl]

lemma shift_unique_x {N : ℕ} (y v : Fin N) :
    ((y.val + N - (y.val + N - v.val) % N) % N = v.val) ∧
    (∀ x : Fin N, (y.val + N - x.val) % N = v.val → x = ⟨(y.val + N - v.val) % N, Nat.mod_lt _ y.pos⟩) := by
  have hN : 0 < N := y.pos
  constructor
  · have hy := y.isLt
    have hv := v.isLt
    by_cases hle : v.val ≤ y.val
    · have hmod : (y.val + N - v.val) % N = y.val - v.val := by
        have e1 : y.val + N - v.val = (y.val - v.val) + N := by omega
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have h1 : y.val + N - (y.val - v.val) = v.val + N := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hv]
    · have hmod : (y.val + N - v.val) % N = y.val + N - v.val := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      have h1 : y.val + N - (y.val + N - v.val) = v.val := by omega
      rw [h1, Nat.mod_eq_of_lt hv]
  · intro x hx
    have hy := y.isLt
    have hv := v.isLt
    have hxl := x.isLt
    apply Fin.ext
    simp only
    by_cases hxy : x.val ≤ y.val
    · have h1 : y.val + N - x.val = (y.val - x.val) + N := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hx
      have h2 : y.val + N - v.val = x.val + N := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hxl]
    · rw [Nat.mod_eq_of_lt (by omega)] at hx
      have h2 : y.val + N - v.val = x.val := by omega
      rw [h2, Nat.mod_eq_of_lt hxl]

lemma hitsOf_pair {N : ℕ} {f : Fin N → Fin N → Bool} (hf : IsPair f) (v : Fin N) :
    hitsOf f v = 2 := by
  have hN : 0 < N := v.pos
  rcases hf with ⟨T, hT, hx | hy⟩
  · rcases Finset.card_eq_two.mp hT with ⟨x0, x1, hne, rfl⟩
    let y0 : Fin N := ⟨(x0.val + v.val) % N, Nat.mod_lt _ hN⟩
    let y1 : Fin N := ⟨(x1.val + v.val) % N, Nat.mod_lt _ hN⟩
    have h0 := (shift_unique_y x0 v).1
    have h1 := (shift_unique_y x1 v).1
    have heq : (Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => f z.1 z.2 = true ∧ (z.2.val + N - z.1.val) % N = v.val) =
        {(x0, y0), (x1, y1)} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_true_eq, Prod.mk.injEq]
      constructor
      · rintro ⟨hx01 | hx01, hsh⟩
        · rw [hx01] at hsh ⊢; left; exact ⟨rfl, (shift_unique_y x0 v).2 y hsh⟩
        · rw [hx01] at hsh ⊢; right; exact ⟨rfl, (shift_unique_y x1 v).2 y hsh⟩
      · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
        · rw [h1', h2']; exact ⟨Or.inl rfl, h0⟩
        · rw [h1', h2']; exact ⟨Or.inr rfl, h1⟩
    unfold hitsOf
    rw [heq, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  · rcases Finset.card_eq_two.mp hT with ⟨y0, y1, hne, rfl⟩
    let x0 : Fin N := ⟨(y0.val + N - v.val) % N, Nat.mod_lt _ hN⟩
    let x1 : Fin N := ⟨(y1.val + N - v.val) % N, Nat.mod_lt _ hN⟩
    have h0 := (shift_unique_x y0 v).1
    have h1 := (shift_unique_x y1 v).1
    have heq : (Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => f z.1 z.2 = true ∧ (z.2.val + N - z.1.val) % N = v.val) =
        {(x0, y0), (x1, y1)} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hy, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_true_eq, Prod.mk.injEq]
      constructor
      · rintro ⟨hy01 | hy01, hsh⟩
        · rw [hy01] at hsh ⊢; left; exact ⟨(shift_unique_x y0 v).2 x hsh, rfl⟩
        · rw [hy01] at hsh ⊢; right; exact ⟨(shift_unique_x y1 v).2 x hsh, rfl⟩
      · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
        · rw [h1', h2']; exact ⟨Or.inl rfl, h0⟩
        · rw [h1', h2']; exact ⟨Or.inr rfl, h1⟩
    unfold hitsOf
    rw [heq, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

lemma hitsOf_tshape {N : ℕ} (hN : 0 < N) {f : Fin N → Fin N → Bool} (hf : IsTShape f) :
    ∃ v1 v2 : Fin N, v1 ≠ v2 ∧
      ∀ v : Fin N, hitsOf f v = if v = v1 ∨ v = v2 then 2 else 3 := by
  rcases hf with ⟨x0, x1, y0, hne, h⟩ | ⟨y0, y1, x0, hne, h⟩
  · let v1 : Fin N := ⟨(y0.val + N - x0.val) % N, Nat.mod_lt _ hN⟩
    let v2 : Fin N := ⟨(y0.val + N - x1.val) % N, Nat.mod_lt _ hN⟩
    have hvne : v1 ≠ v2 := by
      intro heq
      have h1 := congrArg Fin.val heq
      simp only [v1, v2] at h1
      have huniq := (shift_unique_x y0 v1).2
      have ex0 : x0 = ⟨(y0.val + N - v1.val) % N, Nat.mod_lt _ hN⟩ := huniq x0 rfl
      have ex1 : x1 = ⟨(y0.val + N - v1.val) % N, Nat.mod_lt _ hN⟩ := huniq x1 h1.symm
      exact hne (ex0.trans ex1.symm)
    refine ⟨v1, v2, hvne, fun v => ?_⟩
    let p0 : Fin N × Fin N := (x0, ⟨(x0.val + v.val) % N, Nat.mod_lt _ hN⟩)
    let p1 : Fin N × Fin N := (x1, ⟨(x1.val + v.val) % N, Nat.mod_lt _ hN⟩)
    let p2 : Fin N × Fin N := (⟨(y0.val + N - v.val) % N, Nat.mod_lt _ hN⟩, y0)
    have hset : (Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => f z.1 z.2 = true ∧ (z.2.val + N - z.1.val) % N = v.val) = {p0, p1, p2} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, decide_eq_true_eq,
        Finset.mem_insert, Finset.mem_singleton, p0, p1, p2, Prod.mk.injEq]
      constructor
      · rintro ⟨hx0 | hx1 | hy0, hsh⟩
        · rw [hx0] at hsh ⊢; left; exact ⟨rfl, (shift_unique_y x0 v).2 y hsh⟩
        · rw [hx1] at hsh ⊢; right; left; exact ⟨rfl, (shift_unique_y x1 v).2 y hsh⟩
        · rw [hy0] at hsh ⊢; right; right; exact ⟨(shift_unique_x y0 v).2 x hsh, rfl⟩
      · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩)
        · rw [h1', h2']; exact ⟨Or.inl rfl, (shift_unique_y x0 v).1⟩
        · rw [h1', h2']; exact ⟨Or.inr (Or.inl rfl), (shift_unique_y x1 v).1⟩
        · rw [h1', h2']; exact ⟨Or.inr (Or.inr rfl), (shift_unique_x y0 v).1⟩
    have hp01 : p0 ≠ p1 := fun heq => hne (congrArg Prod.fst heq)
    have hp20 : p2 = p0 ↔ v = v1 := by
      constructor
      · intro heq
        have hx : p2.1 = x0 := congrArg Prod.fst heq
        have hsh : (y0.val + N - x0.val) % N = v.val := by
          have := (shift_unique_x y0 v).1
          rw [← hx]; exact this
        exact Fin.ext hsh.symm
      · intro hv; subst hv
        have hx : x0 = p2.1 := (shift_unique_x y0 v1).2 x0 rfl
        have hy : y0 = p0.2 := (shift_unique_y x0 v1).2 y0 rfl
        exact Prod.ext hx.symm hy
    have hp21 : p2 = p1 ↔ v = v2 := by
      constructor
      · intro heq
        have hx : p2.1 = x1 := congrArg Prod.fst heq
        have hsh : (y0.val + N - x1.val) % N = v.val := by
          have := (shift_unique_x y0 v).1
          rw [← hx]; exact this
        exact Fin.ext hsh.symm
      · intro hv; subst hv
        have hx : x1 = p2.1 := (shift_unique_x y0 v2).2 x1 rfl
        have hy : y0 = p1.2 := (shift_unique_y x1 v2).2 y0 rfl
        exact Prod.ext hx.symm hy
    unfold hitsOf
    rw [hset]
    by_cases h12 : v = v1 ∨ v = v2
    · simp only [h12, ↓reduceIte]
      rcases h12 with rfl | rfl
      · have hmem : p2 ∈ ({p0, p1} : Finset (Fin N × Fin N)) := by simp [hp20.mpr rfl]
        have h' : ({p0, p1, p2} : Finset (Fin N × Fin N)) = {p0, p1} := by
          ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl | rfl)
            · left; rfl
            · right; rfl
            · left; exact hp20.mpr rfl
          · rintro (rfl | rfl)
            · left; rfl
            · right; left; rfl
        rw [h', Finset.card_insert_of_notMem (by simp [hp01]), Finset.card_singleton]
      · have h' : ({p0, p1, p2} : Finset (Fin N × Fin N)) = {p0, p1} := by
          ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl | rfl)
            · left; rfl
            · right; rfl
            · right; exact hp21.mpr rfl
          · rintro (rfl | rfl)
            · left; rfl
            · right; left; rfl
        rw [h', Finset.card_insert_of_notMem (by simp [hp01]), Finset.card_singleton]
    · simp only [h12, ↓reduceIte]
      push Not at h12
      have hne0 : p0 ≠ p2 := fun h => h12.1 (hp20.mp h.symm)
      have hne1 : p1 ≠ p2 := fun h => h12.2 (hp21.mp h.symm)
      rw [Finset.card_insert_of_notMem (by simp [hp01, hne0]),
        Finset.card_insert_of_notMem (by simp [hne1]), Finset.card_singleton]
  · let v1 : Fin N := ⟨(y0.val + N - x0.val) % N, Nat.mod_lt _ hN⟩
    let v2 : Fin N := ⟨(y1.val + N - x0.val) % N, Nat.mod_lt _ hN⟩
    have hvne : v1 ≠ v2 := by
      intro heq
      have h1 := congrArg Fin.val heq
      simp only [v1, v2] at h1
      have huniq := (shift_unique_y x0 v1).2
      have ey0 : y0 = ⟨(x0.val + v1.val) % N, Nat.mod_lt _ hN⟩ := huniq y0 rfl
      have ey1 : y1 = ⟨(x0.val + v1.val) % N, Nat.mod_lt _ hN⟩ := huniq y1 h1.symm
      exact hne (ey0.trans ey1.symm)
    refine ⟨v1, v2, hvne, fun v => ?_⟩
    let p0 : Fin N × Fin N := (⟨(y0.val + N - v.val) % N, Nat.mod_lt _ hN⟩, y0)
    let p1 : Fin N × Fin N := (⟨(y1.val + N - v.val) % N, Nat.mod_lt _ hN⟩, y1)
    let p2 : Fin N × Fin N := (x0, ⟨(x0.val + v.val) % N, Nat.mod_lt _ hN⟩)
    have hset : (Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => f z.1 z.2 = true ∧ (z.2.val + N - z.1.val) % N = v.val) = {p0, p1, p2} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, decide_eq_true_eq,
        Finset.mem_insert, Finset.mem_singleton, p0, p1, p2, Prod.mk.injEq]
      constructor
      · rintro ⟨hy0 | hy1 | hx0, hsh⟩
        · rw [hy0] at hsh ⊢; left; exact ⟨(shift_unique_x y0 v).2 x hsh, rfl⟩
        · rw [hy1] at hsh ⊢; right; left; exact ⟨(shift_unique_x y1 v).2 x hsh, rfl⟩
        · rw [hx0] at hsh ⊢; right; right; exact ⟨rfl, (shift_unique_y x0 v).2 y hsh⟩
      · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩)
        · rw [h1', h2']; exact ⟨Or.inl rfl, (shift_unique_x y0 v).1⟩
        · rw [h1', h2']; exact ⟨Or.inr (Or.inl rfl), (shift_unique_x y1 v).1⟩
        · rw [h1', h2']; exact ⟨Or.inr (Or.inr rfl), (shift_unique_y x0 v).1⟩
    have hp01 : p0 ≠ p1 := fun heq => hne (congrArg Prod.snd heq)
    have hp20 : p2 = p0 ↔ v = v1 := by
      constructor
      · intro heq
        have hy : p2.2 = y0 := congrArg Prod.snd heq
        have hsh : (y0.val + N - x0.val) % N = v.val := by
          have := (shift_unique_y x0 v).1
          rw [← hy]; exact this
        exact Fin.ext hsh.symm
      · intro hv; subst hv
        have hx : x0 = p0.1 := (shift_unique_x y0 v1).2 x0 rfl
        have hy : y0 = p2.2 := (shift_unique_y x0 v1).2 y0 rfl
        exact Prod.ext hx hy.symm
    have hp21 : p2 = p1 ↔ v = v2 := by
      constructor
      · intro heq
        have hy : p2.2 = y1 := congrArg Prod.snd heq
        have hsh : (y1.val + N - x0.val) % N = v.val := by
          have := (shift_unique_y x0 v).1
          rw [← hy]; exact this
        exact Fin.ext hsh.symm
      · intro hv; subst hv
        have hx : x0 = p1.1 := (shift_unique_x y1 v2).2 x0 rfl
        have hy : y1 = p2.2 := (shift_unique_y x0 v2).2 y1 rfl
        exact Prod.ext hx hy.symm
    unfold hitsOf
    rw [hset]
    by_cases h12 : v = v1 ∨ v = v2
    · simp only [h12, ↓reduceIte]
      rcases h12 with rfl | rfl
      · have h' : ({p0, p1, p2} : Finset (Fin N × Fin N)) = {p0, p1} := by
          ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl | rfl)
            · left; rfl
            · right; rfl
            · left; exact hp20.mpr rfl
          · rintro (rfl | rfl)
            · left; rfl
            · right; left; rfl
        rw [h', Finset.card_insert_of_notMem (by simp [hp01]), Finset.card_singleton]
      · have h' : ({p0, p1, p2} : Finset (Fin N × Fin N)) = {p0, p1} := by
          ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl | rfl)
            · left; rfl
            · right; rfl
            · right; exact hp21.mpr rfl
          · rintro (rfl | rfl)
            · left; rfl
            · right; left; rfl
        rw [h', Finset.card_insert_of_notMem (by simp [hp01]), Finset.card_singleton]
    · simp only [h12, ↓reduceIte]
      push Not at h12
      have hne0 : p0 ≠ p2 := fun h => h12.1 (hp20.mp h.symm)
      have hne1 : p1 ≠ p2 := fun h => h12.2 (hp21.mp h.symm)
      rw [Finset.card_insert_of_notMem (by simp [hp01, hne0]),
        Finset.card_insert_of_notMem (by simp [hne1]), Finset.card_singleton]

lemma sum_hitsOf {N : ℕ} (hN : 0 < N) (f : Fin N → Fin N → Bool) :
    (∑ v : Fin N, hitsOf f v) = areaOf f := by
  unfold hitsOf areaOf
  rw [← Finset.card_biUnion]
  · congr 1
    ext ⟨x, y⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨_, hf, _⟩ => hf, fun hf => ⟨⟨(y.val + N - x.val) % N, Nat.mod_lt _ hN⟩, hf, rfl⟩⟩
  · intro v1 _ v2 _ hne
    exact Finset.disjoint_left.mpr (fun z h1 h2 => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (Fin.ext (h1.2.symm.trans h2.2)))

lemma shift_sub_mod {N : ℕ} (hN : 0 < N) (x y : Fin N) (u : ℕ) :
    (y.val + N - x.val + N - u % N) % N = ((y.val + N - x.val) % N + N - u % N) % N := by
  have hx := x.isLt
  have hy := y.isLt
  have hu := Nat.mod_lt u hN
  by_cases hxy : x.val ≤ y.val
  · have e1 : y.val + N - x.val = (y.val - x.val) + N := by omega
    have hm : (y.val + N - x.val) % N = y.val - x.val := by
      rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    have e2 : y.val + N - x.val + N - u % N = (y.val - x.val + N - u % N) + N := by omega
    rw [e2, Nat.add_mod_right]
  · have hm : (y.val + N - x.val) % N = y.val + N - x.val := Nat.mod_eq_of_lt (by omega)
    rw [hm]

lemma win_card {N t : ℕ} (htN : t ≤ N) (hN : 0 < N) (u : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
      (z.2.val + N - z.1.val + N - u % N) % N < t)).card = N * t := by
  have hpart : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
      (z.2.val + N - z.1.val + N - u % N) % N < t) =
      (Finset.univ : Finset (Fin N)).biUnion (fun x =>
        (Finset.univ : Finset (Fin t)).image (fun k =>
          (x, ⟨(x.val + u % N + k.val) % N, Nat.mod_lt _ hN⟩))) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · intro hlt
      refine ⟨x, ⟨(y.val + N - x.val + N - u % N) % N, hlt⟩, rfl, ?_⟩
      apply Fin.ext
      simp only
      have hx := x.isLt
      have hy := y.isLt
      have hu := Nat.mod_lt u hN
      rw [shift_sub_mod hN x y u]
      set v := (y.val + N - x.val) % N
      have hv : v < N := Nat.mod_lt _ hN
      have hxv : (x.val + v) % N = y.val := by
        have := (shift_unique_y x ⟨v, hv⟩).2 y rfl
        exact (congrArg Fin.val this).symm
      by_cases huv : u % N ≤ v
      · have hm : (v + N - u % N) % N = v - u % N := by
          have e1 : v + N - u % N = (v - u % N) + N := by omega
          rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hm]
        have e2 : x.val + u % N + (v - u % N) = x.val + v := by omega
        rw [e2, hxv]
      · have hm : (v + N - u % N) % N = v + N - u % N := Nat.mod_eq_of_lt (by omega)
        rw [hm]
        have e2 : x.val + u % N + (v + N - u % N) = (x.val + v) + N := by omega
        rw [e2, Nat.add_mod_right, hxv]
    · rintro ⟨x', k, rfl, rfl⟩
      have hx := x'.isLt
      have hk : k.val < t := k.isLt
      have hu := Nat.mod_lt u hN
      rw [shift_sub_mod hN]
      have hsh : ((x'.val + u % N + k.val) % N + N - x'.val) % N = (u % N + k.val) % N := by
        have h1 : (x'.val + (u % N + k.val) % N) % N = (x'.val + u % N + k.val) % N := by
          simp only [Nat.add_mod, Nat.mod_mod, add_assoc]
        have h2 := (shift_unique_y x' ⟨(u % N + k.val) % N, Nat.mod_lt _ hN⟩).1
        rw [h1] at h2
        exact h2
      rw [hsh]
      by_cases hlt : u % N + k.val < N
      · rw [Nat.mod_eq_of_lt hlt]
        have e1 : u % N + k.val + N - u % N = k.val + N := by omega
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; exact hk
      · have hm : (u % N + k.val) % N = u % N + k.val - N := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hm]
        have e1 : u % N + k.val - N + N - u % N = k.val := by omega
        rw [e1, Nat.mod_eq_of_lt (by omega)]; exact hk
  rw [hpart, Finset.card_biUnion]
  · have hinner : ∀ x : Fin N,
        ((Finset.univ : Finset (Fin t)).image (fun k =>
          (x, (⟨(x.val + u % N + k.val) % N, Nat.mod_lt _ hN⟩ : Fin N)))).card = t := by
      intro x
      rw [Finset.card_image_of_injective]
      · simp
      · intro k1 k2 h
        have hv := congrArg (fun p : Fin N × Fin N => p.2.val) h
        simp only at hv
        have h1 : k1.val < t := k1.isLt
        have h2 : k2.val < t := k2.isLt
        set s := (x.val + u % N) % N
        have hs : s < N := Nat.mod_lt _ hN
        have h1' : (x.val + u % N + k1.val) % N = (s + k1.val) % N := by
          simp only [s, Nat.add_mod, Nat.mod_mod]
        have h2' : (x.val + u % N + k2.val) % N = (s + k2.val) % N := by
          simp only [s, Nat.add_mod, Nat.mod_mod]
        rw [h1', h2'] at hv
        apply Fin.ext
        by_cases c1 : s + k1.val < N <;> by_cases c2 : s + k2.val < N
        · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hv; omega
        · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt c2] at hv; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
    simp [hinner]
  · intro x1 _ x2 _ hne
    exact Finset.disjoint_left.mpr (fun z h1 h2 => by
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with ⟨_, rfl⟩
      rcases h2 with ⟨_, h⟩
      exact hne (congrArg Prod.fst h).symm)

lemma loss_add_two_overlap {N t : ℕ} (htN : t ≤ N) (hN : 0 < N)
    (f : Fin N → Fin N → Bool) (u : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
      f z.1 z.2 ≠ decide ((z.2.val + N - z.1.val + N - u % N) % N < t))).card +
    2 * (∑ k : Fin t, hitsOf f ⟨(u + k.val) % N, Nat.mod_lt _ hN⟩) =
    areaOf f + N * t := by
  let P : Fin N × Fin N → Bool := fun z => f z.1 z.2
  let Q : Fin N × Fin N → Bool := fun z => decide ((z.2.val + N - z.1.val + N - u % N) % N < t)
  have hov : (∑ k : Fin t, hitsOf f ⟨(u + k.val) % N, Nat.mod_lt _ hN⟩) =
      ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true ∧ Q z = true)).card := by
    unfold hitsOf
    rw [← Finset.card_biUnion]
    · congr 1
      ext ⟨x, y⟩
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, P, Q,
        decide_eq_true_eq]
      constructor
      · rintro ⟨k, hf, hsh⟩
        refine ⟨hf, ?_⟩
        rw [shift_sub_mod hN, hsh]
        have hu := Nat.mod_lt u hN
        have hk : k.val < t := k.isLt
        have hm1 : (u + k.val) % N = (u % N + k.val) % N := by
          simp only [Nat.add_mod, Nat.mod_mod]
        rw [hm1]
        by_cases hlt : u % N + k.val < N
        · rw [Nat.mod_eq_of_lt hlt]
          have e1 : u % N + k.val + N - u % N = k.val + N := by omega
          rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; exact hk
        · have hm2 : (u % N + k.val) % N = u % N + k.val - N := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [hm2]
          have e1 : u % N + k.val - N + N - u % N = k.val := by omega
          rw [e1, Nat.mod_eq_of_lt (by omega)]; exact hk
      · rintro ⟨hf, hlt⟩
        rw [shift_sub_mod hN] at hlt
        refine ⟨⟨((y.val + N - x.val) % N + N - u % N) % N, hlt⟩, hf, ?_⟩
        set v := (y.val + N - x.val) % N
        have hv : v < N := Nat.mod_lt _ hN
        have hu := Nat.mod_lt u hN
        have hm1 : (u + (v + N - u % N) % N) % N = (u % N + (v + N - u % N) % N) % N := by
          simp only [Nat.add_mod, Nat.mod_mod]
        rw [hm1]
        by_cases huv : u % N ≤ v
        · have hm2 : (v + N - u % N) % N = v - u % N := by
            have e1 : v + N - u % N = (v - u % N) + N := by omega
            rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hm2]
          have e2 : u % N + (v - u % N) = v := by omega
          rw [e2, Nat.mod_eq_of_lt hv]
        · have hm2 : (v + N - u % N) % N = v + N - u % N := Nat.mod_eq_of_lt (by omega)
          rw [hm2]
          have e2 : u % N + (v + N - u % N) = v + N := by omega
          rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt hv]
    · intro k1 _ k2 _ hne
      exact Finset.disjoint_left.mpr (fun z h1 h2 => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        have hv : (u + k1.val) % N = (u + k2.val) % N := h1.2.symm.trans h2.2
        have h1lt : k1.val < t := k1.isLt
        have h2lt : k2.val < t := k2.isLt
        set ru := u % N
        have hru : ru < N := Nat.mod_lt u hN
        have hm1 : (u + k1.val) % N = (ru + k1.val) % N := by
          simp only [ru, Nat.add_mod, Nat.mod_mod]
        have hm2 : (u + k2.val) % N = (ru + k2.val) % N := by
          simp only [ru, Nat.add_mod, Nat.mod_mod]
        rw [hm1, hm2] at hv
        apply hne; apply Fin.ext
        by_cases c1 : ru + k1.val < N <;> by_cases c2 : ru + k2.val < N
        · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hv; omega
        · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt c2] at hv; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega)
  rw [hov]
  have hQ : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => Q z = true)).card = N * t := by
    simpa [Q] using win_card htN hN u
  rw [← hQ]
  unfold areaOf
  simp only [Finset.card_filter]
  have hpt : ∀ z : Fin N × Fin N,
      (if P z ≠ Q z then (1 : ℕ) else 0) + 2 * (if P z = true ∧ Q z = true then (1 : ℕ) else 0) =
      (if P z = true then (1 : ℕ) else 0) + (if Q z = true then (1 : ℕ) else 0) := by
    intro z; cases P z <;> cases Q z <;> decide
  calc
    (∑ z : Fin N × Fin N, if P z ≠ Q z then (1 : ℕ) else 0) +
        2 * (∑ z : Fin N × Fin N, if P z = true ∧ Q z = true then (1 : ℕ) else 0) =
        ∑ z : Fin N × Fin N, ((if P z ≠ Q z then (1 : ℕ) else 0) +
          2 * (if P z = true ∧ Q z = true then (1 : ℕ) else 0)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ z : Fin N × Fin N, ((if P z = true then (1 : ℕ) else 0) + (if Q z = true then (1 : ℕ) else 0)) :=
      Finset.sum_congr rfl (fun z _ => hpt z)
    _ = (∑ z : Fin N × Fin N, if P z = true then (1 : ℕ) else 0) +
        ∑ z : Fin N × Fin N, if Q z = true then (1 : ℕ) else 0 := Finset.sum_add_distrib

lemma sum_cyclic_window {N t : ℕ} (hN : 0 < N) (g : Fin N → ℕ) :
    (∑ u : Fin N, ∑ k : Fin t, g ⟨(u.val + k.val) % N, Nat.mod_lt _ hN⟩) =
    t * ∑ v : Fin N, g v := by
  rw [Finset.sum_comm]
  have hinner : ∀ k : Fin t,
      (∑ u : Fin N, g ⟨(u.val + k.val) % N, Nat.mod_lt _ hN⟩) = ∑ v : Fin N, g v := by
    intro k
    let σ : Fin N → Fin N := fun u => ⟨(u.val + k.val) % N, Nat.mod_lt _ hN⟩
    have hbij : Function.Bijective σ := by
      refine (Finite.injective_iff_bijective).mp ?_
      intro u1 u2 h
      have hv := congrArg Fin.val h
      simp only [σ] at hv
      set r := k.val % N
      have hr : r < N := Nat.mod_lt k.val hN
      have hm1 : (u1.val + k.val) % N = (u1.val + r) % N := by
        simp only [r, Nat.add_mod, Nat.mod_mod]
      have hm2 : (u2.val + k.val) % N = (u2.val + r) % N := by
        simp only [r, Nat.add_mod, Nat.mod_mod]
      rw [hm1, hm2] at hv
      have h1 := u1.isLt
      have h2 := u2.isLt
      apply Fin.ext
      by_cases c1 : u1.val + r < N <;> by_cases c2 : u2.val + r < N
      · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hv; omega
      · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt c2] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
    exact Equiv.sum_comp (Equiv.ofBijective σ hbij) g
  simp [hinner]

lemma sum_loss_eq {N t : ℕ} (htN : t ≤ N) (h2t : N < 2 * t) (hN : 0 < N)
    (f : Fin N → Fin N → Bool) :
    (∑ u : Fin N, ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
      f z.1 z.2 ≠ decide ((z.2.val + N - z.1.val + N - u.val % N) % N < t))).card) +
    (2 * t - N) * areaOf f = N * N * t := by
  have h1 := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin N))) rfl (fun u _ =>
    loss_add_two_overlap htN hN f u.val)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_cyclic_window hN (hitsOf f),
    sum_hitsOf hN f, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2 : 2 * (t * areaOf f) = N * areaOf f + (2 * t - N) * areaOf f := by
    have : 2 * t = N + (2 * t - N) := by omega
    nlinarith
  nlinarith

def panelCirc (N : ℕ) (x0 x1 y0 : Fin N) : Circuit :=
  { gates := [⟨.or, [x0.val, x1.val]⟩, ⟨.or, [N + N, N + y0.val]⟩]
    output := N + N + 1 }

def pairCirc (N : ℕ) : Circuit :=
  { gates := [⟨.or, [0, 1]⟩]
    output := N + N }

lemma panelCirc_tbl {N : ℕ} (x0 x1 y0 x y : Fin N) :
    tbl N (panelCirc N x0 x1 y0) x y = decide (x = x0 ∨ x = x1 ∨ y = y0) := by
  simp only [tbl, panelCirc, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  have h0 := oneEach_getD_lt x y x0.isLt
  have h1 := oneEach_getD_lt x y x1.isLt
  have hlen := oneEach_len x y
  have h2 : (oneEach x y ++ [(oneEach x y).getD x0.val false || (oneEach x y).getD x1.val false]).getD
      (N + N) false = ((oneEach x y).getD x0.val false || (oneEach x y).getD x1.val false) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen])]
    simp [hlen]
  have h3 : (oneEach x y ++ [(oneEach x y).getD x0.val false || (oneEach x y).getD x1.val false]).getD
      (N + y0.val) false = (oneEach x y).getD (N + y0.val) false := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [hlen]; have := y0.isLt; omega)]
  have h4 : (oneEach x y).getD (N + y0.val) false = decide (y = y0) := by
    have := oneEach_getD_ge x y (w := N + y0.val) (by omega) (by have := y0.isLt; omega)
    simpa [Nat.add_sub_cancel_left] using this
  have h5 : (oneEach x y ++ [(oneEach x y).getD x0.val false || (oneEach x y).getD x1.val false] ++
      [(((oneEach x y ++ [(oneEach x y).getD x0.val false || (oneEach x y).getD x1.val false]).getD
        (N + N) false) ||
       ((oneEach x y ++ [(oneEach x y).getD x0.val false || (oneEach x y).getD x1.val false]).getD
        (N + y0.val) false))]).getD (N + N + 1) false =
      (((oneEach x y ++ [(oneEach x y).getD x0.val false || (oneEach x y).getD x1.val false]).getD
        (N + N) false) ||
       ((oneEach x y ++ [(oneEach x y).getD x0.val false || (oneEach x y).getD x1.val false]).getD
        (N + y0.val) false)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlen])]
    simp [hlen]
  rw [h5, h2, h3, h0, h1, h4]
  simp [Bool.or_assoc]

lemma panelCirc_legal {N : ℕ} (x0 x1 y0 : Fin N) :
    ReadsBack (N + N) (panelCirc N x0 x1 y0) ∧
    (panelCirc N x0 x1 y0).output < N + N + (panelCirc N x0 x1 y0).size ∧
    (∀ g ∈ (panelCirc N x0 x1 y0).gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
    (panelCirc N x0 x1 y0).size ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    have hj2 : j = 0 ∨ j = 1 := by simp [panelCirc] at hj; omega
    rcases hj2 with rfl | rfl
    · simp only [gateAt, panelCirc, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := x0.isLt; omega
      · have := x1.isLt; omega
    · simp only [gateAt, panelCirc, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · omega
      · have := y0.isLt; omega
  · simp [panelCirc, Circuit.size]
  · intro g hg
    simp only [panelCirc, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp
  · simp [panelCirc, Circuit.size]

lemma pairCirc_tbl {N : ℕ} (hN : 5 < N) (x y : Fin N) :
    tbl N (pairCirc N) x y = decide (x = ⟨0, by omega⟩ ∨ x = ⟨1, by omega⟩) := by
  simp only [tbl, pairCirc, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  have hlen := oneEach_len x y
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [oneEach_getD_lt x y (by omega), oneEach_getD_lt x y (by omega)]
  simp

lemma pairCirc_legal {N : ℕ} (hN : 5 < N) :
    ReadsBack (N + N) (pairCirc N) ∧
    (pairCirc N).output < N + N + (pairCirc N).size ∧
    (∀ g ∈ (pairCirc N).gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
    (pairCirc N).size ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    have hj0 : j = 0 := by simp [pairCirc] at hj; omega
    subst hj0
    simp only [gateAt, pairCirc, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · simp [pairCirc, Circuit.size]
  · intro g hg
    simp only [pairCirc, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; simp
  · simp [pairCirc, Circuit.size]

lemma pairCirc_isPair {N : ℕ} (hN : 5 < N) : IsPair (tbl N (pairCirc N)) := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  refine ⟨{i0, i1}, ?_, Or.inl fun x y => ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  · rw [pairCirc_tbl hN]; simp [i0, i1]

lemma panelCirc_hits_for_shifts {N : ℕ} (hN : 0 < N) {v1 v2 : Fin N} (hne : v1 ≠ v2) :
    let x0 : Fin N := ⟨(N - v1.val) % N, Nat.mod_lt _ hN⟩
    let x1 : Fin N := ⟨(N - v2.val) % N, Nat.mod_lt _ hN⟩
    let y0 : Fin N := ⟨0, hN⟩
    x0 ≠ x1 ∧
    ∀ v : Fin N, hitsOf (tbl N (panelCirc N x0 x1 y0)) v = if v = v1 ∨ v = v2 then 2 else 3 := by
  intro x0 x1 y0
  have hv1 : (y0.val + N - x0.val) % N = v1.val := by
    have h := (shift_unique_x y0 v1).1
    simpa [x0, y0] using h
  have hv2 : (y0.val + N - x1.val) % N = v2.val := by
    have h := (shift_unique_x y0 v2).1
    simpa [x1, y0] using h
  have hxne : x0 ≠ x1 := by
    intro heq
    rw [heq] at hv1
    exact hne (Fin.ext (hv1.symm.trans hv2))
  refine ⟨hxne, fun v => ?_⟩
  have htsh : IsTShape (tbl N (panelCirc N x0 x1 y0)) :=
    Or.inl ⟨x0, x1, y0, hxne, fun x y => panelCirc_tbl x0 x1 y0 x y⟩
  let p0 : Fin N × Fin N := (x0, ⟨(x0.val + v.val) % N, Nat.mod_lt _ hN⟩)
  let p1 : Fin N × Fin N := (x1, ⟨(x1.val + v.val) % N, Nat.mod_lt _ hN⟩)
  let p2 : Fin N × Fin N := (⟨(y0.val + N - v.val) % N, Nat.mod_lt _ hN⟩, y0)
  have hset : (Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => tbl N (panelCirc N x0 x1 y0) z.1 z.2 = true ∧ (z.2.val + N - z.1.val) % N = v.val) =
      {p0, p1, p2} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, panelCirc_tbl, decide_eq_true_eq,
      Finset.mem_insert, Finset.mem_singleton, p0, p1, p2, Prod.mk.injEq]
    constructor
    · rintro ⟨hx0 | hx1 | hy0, hsh⟩
      · rw [hx0] at hsh ⊢; left; exact ⟨rfl, (shift_unique_y x0 v).2 y hsh⟩
      · rw [hx1] at hsh ⊢; right; left; exact ⟨rfl, (shift_unique_y x1 v).2 y hsh⟩
      · rw [hy0] at hsh ⊢; right; right; exact ⟨(shift_unique_x y0 v).2 x hsh, rfl⟩
    · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩)
      · rw [h1', h2']; exact ⟨Or.inl rfl, (shift_unique_y x0 v).1⟩
      · rw [h1', h2']; exact ⟨Or.inr (Or.inl rfl), (shift_unique_y x1 v).1⟩
      · rw [h1', h2']; exact ⟨Or.inr (Or.inr rfl), (shift_unique_x y0 v).1⟩
  have hp01 : p0 ≠ p1 := fun heq => hxne (congrArg Prod.fst heq)
  have hp20 : p2 = p0 ↔ v = v1 := by
    constructor
    · intro heq
      have hx : p2.1 = x0 := congrArg Prod.fst heq
      have hsh : (y0.val + N - x0.val) % N = v.val := by
        have := (shift_unique_x y0 v).1; rw [← hx]; exact this
      exact Fin.ext (hsh.symm.trans hv1)
    · intro hv
      have hx : x0 = p2.1 := by simp only [p2]; rw [hv]; exact (shift_unique_x y0 v1).2 x0 hv1
      have hy : y0 = p0.2 := by simp only [p0]; rw [hv]; exact (shift_unique_y x0 v1).2 y0 hv1
      exact Prod.ext hx.symm hy
  have hp21 : p2 = p1 ↔ v = v2 := by
    constructor
    · intro heq
      have hx : p2.1 = x1 := congrArg Prod.fst heq
      have hsh : (y0.val + N - x1.val) % N = v.val := by
        have := (shift_unique_x y0 v).1; rw [← hx]; exact this
      exact Fin.ext (hsh.symm.trans hv2)
    · intro hv
      have hx : x1 = p2.1 := by simp only [p2]; rw [hv]; exact (shift_unique_x y0 v2).2 x1 hv2
      have hy : y0 = p1.2 := by simp only [p1]; rw [hv]; exact (shift_unique_y x1 v2).2 y0 hv2
      exact Prod.ext hx.symm hy
  unfold hitsOf
  rw [hset]
  by_cases h12 : v = v1 ∨ v = v2
  · simp only [h12, ↓reduceIte]
    rcases h12 with rfl | rfl
    · have h' : ({p0, p1, p2} : Finset (Fin N × Fin N)) = {p0, p1} := by
        ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨by rintro (rfl | rfl | rfl); exact Or.inl rfl; exact Or.inr rfl; exact Or.inl (hp20.mpr rfl),
          by rintro (rfl | rfl); exact Or.inl rfl; exact Or.inr (Or.inl rfl)⟩
      rw [h', Finset.card_insert_of_notMem (by simp [hp01]), Finset.card_singleton]
    · have h' : ({p0, p1, p2} : Finset (Fin N × Fin N)) = {p0, p1} := by
        ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨by rintro (rfl | rfl | rfl); exact Or.inl rfl; exact Or.inr rfl; exact Or.inr (hp21.mpr rfl),
          by rintro (rfl | rfl); exact Or.inl rfl; exact Or.inr (Or.inl rfl)⟩
      rw [h', Finset.card_insert_of_notMem (by simp [hp01]), Finset.card_singleton]
  · simp only [h12, ↓reduceIte]
    push Not at h12
    have hne0 : p0 ≠ p2 := fun h => h12.1 (hp20.mp h.symm)
    have hne1 : p1 ≠ p2 := fun h => h12.2 (hp21.mp h.symm)
    rw [Finset.card_insert_of_notMem (by simp [hp01, hne0]),
      Finset.card_insert_of_notMem (by simp [hne1]), Finset.card_singleton]

lemma tshape_loss_formula {N t : ℕ} (htN : t ≤ N) (h2t : N < 2 * t) (hN5 : 5 < N)
    {f : Fin N → Fin N → Bool} (hf : IsTShape f) (u : Fin N) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
      f z.1 z.2 ≠ decide ((z.2.val + N - z.1.val + N - u.val % N) % N < t))).card =
    (N * t - 3 * (2 * t - N) - 2) +
    2 * ((Finset.univ : Finset (Fin t)).filter (fun k =>
      hitsOf f ⟨(u.val + k.val) % N, Nat.mod_lt _ (by omega)⟩ = 2)).card := by
  have hN : 0 < N := by omega
  have hloss := loss_add_two_overlap htN hN f u.val
  rw [areaOf_tshape hf] at hloss
  rcases hitsOf_tshape hN hf with ⟨v1, v2, _, hhits⟩
  have hov : (∑ k : Fin t, hitsOf f ⟨(u.val + k.val) % N, Nat.mod_lt _ hN⟩) +
      ((Finset.univ : Finset (Fin t)).filter (fun k =>
        hitsOf f ⟨(u.val + k.val) % N, Nat.mod_lt _ hN⟩ = 2)).card = 3 * t := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    have hpt : ∀ k : Fin t,
        hitsOf f ⟨(u.val + k.val) % N, Nat.mod_lt _ hN⟩ +
        (if hitsOf f ⟨(u.val + k.val) % N, Nat.mod_lt _ hN⟩ = 2 then 1 else 0) = 3 := by
      intro k
      rw [hhits]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl (fun k _ => hpt k)]
    simp [mul_comm]
  have hge : 3 * (2 * t - N) + 2 ≤ N * t := by
    have h6t : 6 * t ≤ N * t := Nat.mul_le_mul_right t (by omega)
    omega
  omega

lemma beatty_miss_count {N b K : ℕ} (hN : 0 < N) (hb : b < N) (w : Fin N) :
    (K * b) / N ≤ ((Finset.univ : Finset (Fin K)).filter (fun m =>
      (((m.val + 1) * b) % N + N - w.val) % N < b)).card := by
  have hstep : ∀ m : ℕ,
      (((m + 1) * b + (N - w.val)) / N) =
      (m * b + (N - w.val)) / N +
      (if (((m + 1) * b) % N + N - w.val) % N < b then 1 else 0) := by
    intro m
    set y := m * b + (N - w.val)
    have hw := w.isLt
    have hy1 : (m + 1) * b + (N - w.val) = y + b := by ring
    rw [hy1]
    have hrem : (((m + 1) * b) % N + N - w.val) % N = (y + b) % N := by
      have e1 : (y + b) % N = ((m + 1) * b + (N - w.val)) % N := by rw [hy1]
      rw [e1]
      have e2 : ((m + 1) * b + (N - w.val)) % N = (((m + 1) * b) % N + (N - w.val)) % N := by
        simp only [Nat.add_mod, Nat.mod_mod]
      rw [e2]
      have e3 : ((m + 1) * b) % N + N - w.val = ((m + 1) * b) % N + (N - w.val) := by omega
      rw [e3]
    rw [hrem]
    have hdiv := Nat.div_add_mod y N
    have hmod_lt : y % N < N := Nat.mod_lt y hN
    by_cases hlt : y % N + b < N
    · have hq : (y + b) / N = y / N := by
        have e : y + b = N * (y / N) + (y % N + b) := by omega
        conv_lhs => rw [e, Nat.mul_add_div hN]
        rw [Nat.div_eq_of_lt hlt, add_zero]
      have hr : (y + b) % N = y % N + b := by
        have e : y + b = N * (y / N) + (y % N + b) := by omega
        conv_lhs => rw [e, Nat.mul_add_mod]
        rw [Nat.mod_eq_of_lt hlt]
      rw [hq, hr]
      have : ¬ y % N + b < b := by omega
      simp [this]
    · have hq : (y + b) / N = y / N + 1 := by
        have e : y + b = N * (y / N + 1) + (y % N + b - N) := by rw [mul_add, mul_one]; omega
        have h0 : (y % N + b - N) / N = 0 := Nat.div_eq_of_lt (by omega)
        conv_lhs => rw [e, Nat.mul_add_div hN]
        rw [h0, add_zero]
      have hr : (y + b) % N = y % N + b - N := by
        have e : y + b = N * (y / N + 1) + (y % N + b - N) := by rw [mul_add, mul_one]; omega
        conv_lhs => rw [e, Nat.mul_add_mod]
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [hq, hr]
      have : y % N + b - N < b := by omega
      simp [this]
  have htele : ∀ K : ℕ,
      (K * b + (N - w.val)) / N =
      (N - w.val) / N +
      ((Finset.univ : Finset (Fin K)).filter (fun m =>
        (((m.val + 1) * b) % N + N - w.val) % N < b)).card := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.card_filter, Fin.sum_univ_castSucc, ← Finset.card_filter]
      have hst := hstep K
      simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢
      omega
  have hK := htele K
  have hw := w.isLt
  by_cases hw0 : w.val = 0
  · simp only [hw0, Nat.sub_zero, Nat.div_self hN] at hK ⊢
    have hadd : (K * b + N) / N = (K * b) / N + 1 := Nat.add_div_right (K * b) hN
    rw [hadd] at hK
    omega
  · have hdiv0 : (N - w.val) / N = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv0, zero_add] at hK
    have hle : (K * b) / N ≤ (K * b + (N - w.val)) / N := Nat.div_le_div_right (by omega)
    omega

lemma nat_sub_div_complement {N t K : ℕ} (hN : 0 < N) (htN : t ≤ N) :
    K - (K * (N - t)) / N = (K * t + N - 1) / N := by
  have hmul : K * (N - t) + K * t = K * N := by
    rw [← mul_add, Nat.sub_add_cancel htN]
  set q := (K * t) / N
  set r := (K * t) % N
  have hqr : N * q + r = K * t := Nat.div_add_mod (K * t) N
  have hr : r < N := Nat.mod_lt (K * t) hN
  have hKt_le : K * t ≤ K * N := Nat.mul_le_mul_left K htN
  by_cases hr0 : r = 0
  · have hqle : q ≤ K := by
      have : N * q ≤ N * K := by nlinarith
      exact Nat.le_of_mul_le_mul_left this hN
    have h1 : K * (N - t) = (K - q) * N := by
      have : (K - q) * N + q * N = K * N := by rw [← add_mul, Nat.sub_add_cancel hqle]
      nlinarith
    have h2 : (K * (N - t)) / N = K - q := by rw [h1, Nat.mul_div_cancel _ hN]
    have h3 : (K * t + N - 1) / N = q := by
      have e : K * t + N - 1 = N * q + (N - 1) := by omega
      rw [e, Nat.mul_add_div hN, Nat.div_eq_of_lt (by omega), add_zero]
    rw [h2, h3]
    exact Nat.sub_sub_self hqle
  · have hqlt : q < K := by
      have hKN : K * N = N * K := mul_comm K N
      have : N * q < N * K := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    have h1 : K * (N - t) = (K - q - 1) * N + (N - r) := by
      have : (K - q - 1) * N + (q + 1) * N = K * N := by
        rw [← add_mul]; congr 1; omega
      have : (N - r) + r = N := by omega
      nlinarith
    have h2 : (K * (N - t)) / N = K - q - 1 := by
      rw [h1, mul_comm (K - q - 1) N, Nat.mul_add_div hN, Nat.div_eq_of_lt (by omega), add_zero]
    have h3 : (K * t + N - 1) / N = q + 1 := by
      have e : K * t + N - 1 = N * (q + 1) + (r - 1) := by rw [mul_add, mul_one]; omega
      rw [e, Nat.mul_add_div hN, Nat.div_eq_of_lt (by omega), add_zero]
    rw [h2, h3]
    have hle : q + 1 ≤ K := hqlt
    have hsub : K - q - 1 = K - (q + 1) := by omega
    rw [hsub]
    exact Nat.sub_sub_self hle

end PEqualNP.Outside.L_meta_33602_aux

theorem PEqualNP.Outside.L_meta_33602 :
  ∀ (N t M : ℕ), 5 < N → N < 2*t → t ≤ N → 0 < M →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let area := fun (C : Circ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 = true)).card
  let loss := fun (C : Circ) (u : ℕ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 ≠
      decide ((z.2.val + N - z.1.val + N - u % N) % N < t))).card
  let A := 3*N-2
  let fits := fun (C : Circ) => legal C ∧ C.size ≤ 2 ∧ area C ≤ A
  let total := fun (D : Fin M → Circ) (u : X) => ∑ i, loss (D i) u.val
  let a := 2*t-N
  let rounded := M*(N*t-3*a-2)+2*((2*M*t+N-1)/N)
  let exception := 2*t=N+1 ∧ M % N=1
  let value := rounded - (if exception then 1 else 0)
  let pair := fun (C : Circ) => ∃ T : Finset X, T.card=2 ∧
    ((∀ x y : X, table C x y = decide (x ∈ T)) ∨ (∀ x y : X, table C x y = decide (y ∈ T)))
  let hits := fun (C : Circ) (v : X) => ((Finset.univ : Finset (X × X)).filter (fun z =>
    table C z.1 z.2 = true ∧ (z.2.val+N-z.1.val) % N=v.val)).card
  (∃ D : Fin M → Circ, (∀ i, fits (D i)) ∧ ∀ u : X, total D u ≤ value) ∧
  ∀ D : Fin M → Circ, (∀ i, fits (D i)) →
    (∃ u : X, value ≤ total D u) ∧
    (exception → ((∀ u : X, total D u ≤ value) ↔ ∃ j : Fin M,
      pair (D j) ∧ (∀ i : Fin M, i ≠ j → area (D i) = A) ∧
      ∀ v : X, ((Finset.univ : Finset (Fin M)).filter
        (fun i => i ≠ j ∧ hits (D i) v = 2)).card = 2*(M/N))) := by
  intro N t M hN h2t htN hM X Circ legal table area loss A fits total a rounded exception value pair hits
  have hN0 : 0 < N := by omega
  have ha_pos : 0 < a := by omega
  have hA_ge : 3 * a + 2 ≤ N * t := by
    have h6t : 6 * t ≤ N * t := Nat.mul_le_mul_right t (by omega)
    omega
  have hclass : ∀ C : Circ, fits C →
      PEqualNP.Outside.L_meta_33602_aux.IsTShape (table C) ∨
      pair C ∨ area C ≤ 2 * N - 1 := by
    intro C ⟨⟨hRB, hout, hgates⟩, hsize, harea⟩
    exact PEqualNP.Outside.L_meta_33602_aux.fits_classify hN C hRB hout hgates hsize harea
  have harea_eq_A : ∀ C : Circ, fits C → area C = A →
      PEqualNP.Outside.L_meta_33602_aux.IsTShape (table C) := by
    intro C hfit hAeq
    rcases hclass C hfit with hT | hP | hle
    · exact hT
    · have h2N : area C = 2 * N := PEqualNP.Outside.L_meta_33602_aux.areaOf_pair hP; omega
    · omega
  have harea_lt_A : ∀ C : Circ, fits C → area C ≠ A → area C ≤ 2 * N := by
    intro C hfit hne
    rcases hclass C hfit with hT | hP | hle
    · exfalso; exact hne (PEqualNP.Outside.L_meta_33602_aux.areaOf_tshape hT)
    · have h2N : area C = 2 * N := PEqualNP.Outside.L_meta_33602_aux.areaOf_pair hP; omega
    · omega
  have hexcept_conv : ∀ D : Fin M → Circ, (∀ i, fits (D i)) → exception →
      (∃ j : Fin M, pair (D j) ∧ (∀ i : Fin M, i ≠ j → area (D i) = A) ∧
        ∀ v : X, ((Finset.univ : Finset (Fin M)).filter
          (fun i => i ≠ j ∧ hits (D i) v = 2)).card = 2 * (M / N)) →
      ∀ u : X, total D u ≤ value := by
    intro D hD hex ⟨j, hpairj, hrestA, hdeg⟩ u
    rcases hex with ⟨h2t1, hMmod⟩
    have ha1 : a = 1 := by omega
    have hloss_j : loss (D j) u.val = N * t - 2 := by
      have hl : loss (D j) u.val +
          2 * ∑ k : Fin t, PEqualNP.Outside.L_meta_33602_aux.hitsOf (table (D j))
            ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ =
          PEqualNP.Outside.L_meta_33602_aux.areaOf (table (D j)) + N * t :=
        PEqualNP.Outside.L_meta_33602_aux.loss_add_two_overlap htN hN0 (table (D j)) u.val
      have har : PEqualNP.Outside.L_meta_33602_aux.areaOf (table (D j)) = 2 * N :=
        PEqualNP.Outside.L_meta_33602_aux.areaOf_pair hpairj
      have hhi : ∀ k : Fin t, PEqualNP.Outside.L_meta_33602_aux.hitsOf (table (D j))
          ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2 :=
        fun k => PEqualNP.Outside.L_meta_33602_aux.hitsOf_pair hpairj _
      simp only [har, hhi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hl
      omega
    have htot_eq : total D u = loss (D j) u.val + ∑ i ∈ Finset.univ.erase j, loss (D i) u.val := by
      unfold total
      exact (Finset.add_sum_erase Finset.univ (fun i => loss (D i) u.val) (Finset.mem_univ j)).symm
    have hrest_loss : ∀ i ∈ Finset.univ.erase j,
        loss (D i) u.val = (N * t - 5) +
          2 * ((Finset.univ : Finset (Fin t)).filter (fun k =>
            hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card := by
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      have hTi := harea_eq_A (D i) (hD i) (hrestA i hij)
      have hl := PEqualNP.Outside.L_meta_33602_aux.tshape_loss_formula htN h2t hN hTi u
      have h3 : N * t - 3 * (2 * t - N) - 2 = N * t - 5 := by omega
      rw [h3] at hl
      exact hl
    have hsum_e : (∑ i ∈ Finset.univ.erase j,
        ((Finset.univ : Finset (Fin t)).filter (fun k =>
          hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card) =
        t * (2 * (M / N)) := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      have hinner : ∀ k : Fin t,
          (∑ i ∈ Finset.univ.erase j,
            if hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2 then (1 : ℕ) else 0) =
          2 * (M / N) := by
        intro k
        let v : X := ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩
        have hfv : ((Finset.univ : Finset (Fin M)).filter (fun i => i ≠ j ∧ hits (D i) v = 2)).card =
            2 * (M / N) := hdeg v
        rw [← hfv, Finset.card_filter]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        simp [hij, v]
      rw [Finset.sum_congr rfl (fun k _ => hinner k)]
      simp
    have hsum_rest : (∑ i ∈ Finset.univ.erase j, loss (D i) u.val) =
        (M - 1) * (N * t - 5) + 2 * (t * (2 * (M / N))) := by
      rw [Finset.sum_congr rfl hrest_loss, Finset.sum_add_distrib, ← Finset.mul_sum, hsum_e,
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    rw [htot_eq, hloss_j, hsum_rest]
    have hMdiv : M = (M / N) * N + 1 := by
      have := Nat.div_add_mod M N; rw [mul_comm] at this; omega
    have hceil : (2 * M * t + N - 1) / N = 2 * (M / N) * t + 2 := by
      have h1 : 2 * M * t = (2 * (M / N) * t + 1) * N + 1 := by
        calc
          2 * M * t = ((M / N) * N + 1) * (2 * t) := by rw [← hMdiv]; ring
          _ = ((M / N) * N + 1) * (N + 1) := by rw [h2t1]
          _ = (M / N) * (N + 1) * N + N + 1 := by ring
          _ = (M / N) * (2 * t) * N + N + 1 := by rw [← h2t1]
          _ = (2 * (M / N) * t + 1) * N + 1 := by ring
      have h2 : 2 * M * t + N - 1 = N * (2 * (M / N) * t + 2) := by
        calc
          2 * M * t + N - 1 = ((2 * (M / N) * t + 1) * N + 1) + N - 1 := by rw [h1]
          _ = (2 * (M / N) * t + 1) * N + N := by omega
          _ = N * (2 * (M / N) * t + 2) := by ring
      rw [h2, Nat.mul_div_right _ hN0]
    have hval : value = M * (N * t - 5) + 2 * (2 * (M / N) * t + 2) - 1 := by
      have hex1 : exception := ⟨h2t1, hMmod⟩
      have h3a : N * t - 3 * a - 2 = N * t - 5 := by omega
      simp only [value, rounded, hex1, ↓reduceIte, h3a, hceil]
    rw [hval]
    have h5 : 5 ≤ N * t := by nlinarith
    have hM1 : M * (N * t - 5) = (M - 1) * (N * t - 5) + (N * t - 5) := by
      have : M = (M - 1) + 1 := by omega
      conv_lhs => rw [this, add_mul, one_mul]
    have hmul : t * (2 * (M / N)) = 2 * (M / N) * t := by ring
    omega
  constructor
  · by_cases hex : exception
    · rcases hex with ⟨h2t1, hMmod⟩
      let j0 : Fin M := ⟨0, hM⟩
      let D : Fin M → Circ := fun i =>
        if i = j0 then PEqualNP.Outside.L_meta_33602_aux.pairCirc N
        else
          let s : Fin N := ⟨(i.val - 1) % N, Nat.mod_lt _ hN0⟩
          PEqualNP.Outside.L_meta_33602_aux.panelCirc N ⟨0, hN0⟩ ⟨1, by omega⟩ s
      have hne01 : (⟨0, hN0⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      have hD_fits : ∀ i, fits (D i) := by
        intro i
        by_cases hi : i = j0
        · simp only [D, hi, ↓reduceIte]
          have hleg := PEqualNP.Outside.L_meta_33602_aux.pairCirc_legal hN
          have har : area (PEqualNP.Outside.L_meta_33602_aux.pairCirc N) = 2 * N :=
            PEqualNP.Outside.L_meta_33602_aux.areaOf_pair
              (PEqualNP.Outside.L_meta_33602_aux.pairCirc_isPair hN)
          exact ⟨⟨hleg.1, hleg.2.1, hleg.2.2.1⟩, hleg.2.2.2, by omega⟩
        · simp only [D, hi, ↓reduceIte]
          set s : Fin N := ⟨(i.val - 1) % N, Nat.mod_lt _ hN0⟩
          have hleg := PEqualNP.Outside.L_meta_33602_aux.panelCirc_legal (⟨0, hN0⟩ : Fin N) ⟨1, by omega⟩ s
          have htsh : PEqualNP.Outside.L_meta_33602_aux.IsTShape (table (PEqualNP.Outside.L_meta_33602_aux.panelCirc N ⟨0, hN0⟩ ⟨1, by omega⟩ s)) :=
            Or.inl ⟨⟨0, hN0⟩, ⟨1, by omega⟩, s, hne01, fun x y => PEqualNP.Outside.L_meta_33602_aux.panelCirc_tbl _ _ _ x y⟩
          have har : area (PEqualNP.Outside.L_meta_33602_aux.panelCirc N ⟨0, hN0⟩ ⟨1, by omega⟩ s) = 3 * N - 2 :=
            PEqualNP.Outside.L_meta_33602_aux.areaOf_tshape htsh
          exact ⟨⟨hleg.1, hleg.2.1, hleg.2.2.1⟩, hleg.2.2.2, by omega⟩
      refine ⟨D, hD_fits, hexcept_conv D hD_fits ⟨h2t1, hMmod⟩ ⟨j0, ?_, ?_, ?_⟩⟩
      · have hp := PEqualNP.Outside.L_meta_33602_aux.pairCirc_isPair hN
        have hDj : D j0 = PEqualNP.Outside.L_meta_33602_aux.pairCirc N := by simp [D]
        rw [hDj]
        exact hp
      · intro i hij
        simp only [D, hij, ↓reduceIte]
        set s : Fin N := ⟨(i.val - 1) % N, Nat.mod_lt _ hN0⟩
        have htsh : PEqualNP.Outside.L_meta_33602_aux.IsTShape (table (PEqualNP.Outside.L_meta_33602_aux.panelCirc N ⟨0, hN0⟩ ⟨1, by omega⟩ s)) :=
          Or.inl ⟨⟨0, hN0⟩, ⟨1, by omega⟩, s, hne01, fun x y => PEqualNP.Outside.L_meta_33602_aux.panelCirc_tbl _ _ _ x y⟩
        exact PEqualNP.Outside.L_meta_33602_aux.areaOf_tshape htsh
      · intro v
        have hMdiv : M = (M / N) * N + 1 := by have := Nat.div_add_mod M N; rw [mul_comm] at this; omega
        have hhits_s : ∀ s : Fin N,
            hits (PEqualNP.Outside.L_meta_33602_aux.panelCirc N ⟨0, hN0⟩ ⟨1, by omega⟩ s) v = 2 ↔
            s = v ∨ s = ⟨(v.val + 1) % N, Nat.mod_lt _ hN0⟩ := by
          intro s
          have hv1 : ((s.val + N - 0) % N) = s.val := by
            rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt s.isLt]
          have hv2 : (⟨(s.val + N - 1) % N, Nat.mod_lt _ hN0⟩ : Fin N) = v ↔
              s = ⟨(v.val + 1) % N, Nat.mod_lt _ hN0⟩ := by
            have hs := s.isLt
            have hv := v.isLt
            constructor
            · intro h; have hv' := congrArg Fin.val h; simp only at hv'
              apply Fin.ext; simp only
              by_cases hs0 : s.val = 0
              · rw [hs0, zero_add, Nat.mod_eq_of_lt (by omega)] at hv'
                have : v.val + 1 = N := by omega
                rw [this, Nat.mod_self, hs0]
              · have e : s.val + N - 1 = (s.val - 1) + N := by omega
                rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hv'
                have : v.val + 1 = s.val := by omega
                rw [this, Nat.mod_eq_of_lt hs]
            · intro h; have hs' := congrArg Fin.val h; simp only at hs'
              apply Fin.ext; simp only
              by_cases hv1' : v.val + 1 < N
              · rw [Nat.mod_eq_of_lt hv1'] at hs'
                have e : s.val + N - 1 = v.val + N := by omega
                rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hv]
              · have e : v.val + 1 = N := by omega
                rw [e, Nat.mod_self] at hs'
                rw [hs', zero_add, Nat.mod_eq_of_lt (by omega)]; omega
          have htsh : PEqualNP.Outside.L_meta_33602_aux.IsTShape
              (PEqualNP.Outside.L_meta_33602_aux.tbl N
                (PEqualNP.Outside.L_meta_33602_aux.panelCirc N ⟨0, hN0⟩ ⟨1, by omega⟩ s)) :=
            Or.inl ⟨⟨0, hN0⟩, ⟨1, by omega⟩, s, hne01, fun x y =>
              PEqualNP.Outside.L_meta_33602_aux.panelCirc_tbl _ _ _ x y⟩
          have hsh : PEqualNP.Outside.L_meta_33602_aux.hitsOf
              (PEqualNP.Outside.L_meta_33602_aux.tbl N
                (PEqualNP.Outside.L_meta_33602_aux.panelCirc N ⟨0, hN0⟩ ⟨1, by omega⟩ s)) v =
              if v = s ∨ v = ⟨(s.val + N - 1) % N, Nat.mod_lt _ hN0⟩ then 2 else 3 := by
            let v1' : Fin N := s
            let v2' : Fin N := ⟨(s.val + N - 1) % N, Nat.mod_lt _ hN0⟩
            have hne' : v1' ≠ v2' := by
              intro h; have := congrArg Fin.val h; simp only [v1', v2'] at this
              have hs := s.isLt
              by_cases hs0 : s.val = 0
              · rw [hs0, zero_add, Nat.mod_eq_of_lt (by omega)] at this; omega
              · have e : s.val + N - 1 = (s.val - 1) + N := by omega
                rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at this; omega
            have hinv1 : (⟨(N - v1'.val) % N, Nat.mod_lt _ hN0⟩ : Fin N) ≠
                ⟨(N - v2'.val) % N, Nat.mod_lt _ hN0⟩ :=
              (PEqualNP.Outside.L_meta_33602_aux.panelCirc_hits_for_shifts hN0 hne').1
            let p0 : Fin N × Fin N := (⟨0, hN0⟩, ⟨(0 + v.val) % N, Nat.mod_lt _ hN0⟩)
            let p1 : Fin N × Fin N := (⟨1, by omega⟩, ⟨(1 + v.val) % N, Nat.mod_lt _ hN0⟩)
            let p2 : Fin N × Fin N := (⟨(s.val + N - v.val) % N, Nat.mod_lt _ hN0⟩, s)
            have hset : (Finset.univ : Finset (Fin N × Fin N)).filter
                (fun z => PEqualNP.Outside.L_meta_33602_aux.tbl N
                  (PEqualNP.Outside.L_meta_33602_aux.panelCirc N ⟨0, hN0⟩ ⟨1, by omega⟩ s) z.1 z.2 = true ∧
                  (z.2.val + N - z.1.val) % N = v.val) = {p0, p1, p2} := by
              ext ⟨x, y⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                PEqualNP.Outside.L_meta_33602_aux.panelCirc_tbl, decide_eq_true_eq,
                Finset.mem_insert, Finset.mem_singleton, p0, p1, p2, Prod.mk.injEq]
              constructor
              · rintro ⟨hx0 | hx1 | hys, hsh'⟩
                · rw [hx0] at hsh' ⊢; left; exact ⟨rfl, (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y ⟨0, hN0⟩ v).2 y hsh'⟩
                · rw [hx1] at hsh' ⊢; right; left; exact ⟨rfl, (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y ⟨1, by omega⟩ v).2 y hsh'⟩
                · rw [hys] at hsh' ⊢; right; right; exact ⟨(PEqualNP.Outside.L_meta_33602_aux.shift_unique_x s v).2 x hsh', rfl⟩
              · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩)
                · rw [h1', h2']; exact ⟨Or.inl rfl, (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y ⟨0, hN0⟩ v).1⟩
                · rw [h1', h2']; exact ⟨Or.inr (Or.inl rfl), (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y ⟨1, by omega⟩ v).1⟩
                · rw [h1', h2']; exact ⟨Or.inr (Or.inr rfl), (PEqualNP.Outside.L_meta_33602_aux.shift_unique_x s v).1⟩
            have hp01 : p0 ≠ p1 := fun h => hne01 (congrArg Prod.fst h)
            have hp20 : p2 = p0 ↔ v = v1' := by
              constructor
              · intro h; have hx := congrArg Prod.fst h; simp only [p2, p0] at hx
                have hsh' := (PEqualNP.Outside.L_meta_33602_aux.shift_unique_x s v).1
                have hx' : (s.val + N - v.val) % N = 0 := congrArg Fin.val hx
                rw [hx'] at hsh'; exact Fin.ext (hsh'.symm.trans hv1)
              · intro hv
                have hx : (⟨0, hN0⟩ : Fin N) = p2.1 := by simp only [p2]; rw [hv]; exact (PEqualNP.Outside.L_meta_33602_aux.shift_unique_x s v1').2 ⟨0, hN0⟩ hv1
                have hy : s = p0.2 := by simp only [p0]; rw [hv]; exact (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y ⟨0, hN0⟩ v1').2 s hv1
                exact Prod.ext hx.symm hy
            have hp21 : p2 = p1 ↔ v = v2' := by
              constructor
              · intro h; have hx := congrArg Prod.fst h; simp only [p2, p1] at hx
                have hsh' := (PEqualNP.Outside.L_meta_33602_aux.shift_unique_x s v).1
                have hx' : (s.val + N - v.val) % N = 1 := congrArg Fin.val hx
                rw [hx'] at hsh'; exact Fin.ext hsh'.symm
              · intro hv
                have hx : (⟨1, by omega⟩ : Fin N) = p2.1 := by simp only [p2]; rw [hv]; exact (PEqualNP.Outside.L_meta_33602_aux.shift_unique_x s v2').2 ⟨1, by omega⟩ rfl
                have hy : s = p1.2 := by simp only [p1]; rw [hv]; exact (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y ⟨1, by omega⟩ v2').2 s rfl
                exact Prod.ext hx.symm hy
            unfold PEqualNP.Outside.L_meta_33602_aux.hitsOf
            rw [hset]
            by_cases h12 : v = v1' ∨ v = v2'
            · rw [if_pos h12]
              rcases h12 with rfl | rfl
              · have h' : ({p0, p1, p2} : Finset (Fin N × Fin N)) = {p0, p1} := by
                  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
                  exact ⟨by rintro (rfl | rfl | rfl); exact Or.inl rfl; exact Or.inr rfl; exact Or.inl (hp20.mpr rfl),
                    by rintro (rfl | rfl); exact Or.inl rfl; exact Or.inr (Or.inl rfl)⟩
                rw [h', Finset.card_insert_of_notMem (by simp [hp01]), Finset.card_singleton]
              · have h' : ({p0, p1, p2} : Finset (Fin N × Fin N)) = {p0, p1} := by
                  ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
                  exact ⟨by rintro (rfl | rfl | rfl); exact Or.inl rfl; exact Or.inr rfl; exact Or.inr (hp21.mpr rfl),
                    by rintro (rfl | rfl); exact Or.inl rfl; exact Or.inr (Or.inl rfl)⟩
                rw [h', Finset.card_insert_of_notMem (by simp [hp01]), Finset.card_singleton]
            · rw [if_neg h12]
              push Not at h12
              have hne0 : p0 ≠ p2 := fun h => h12.1 (hp20.mp h.symm)
              have hne1 : p1 ≠ p2 := fun h => h12.2 (hp21.mp h.symm)
              rw [Finset.card_insert_of_notMem (by simp [hp01, hne0]),
                Finset.card_insert_of_notMem (by simp [hne1]), Finset.card_singleton]
          have hhi_eq : hits (PEqualNP.Outside.L_meta_33602_aux.panelCirc N ⟨0, hN0⟩ ⟨1, by omega⟩ s) v =
              if v = s ∨ v = ⟨(s.val + N - 1) % N, Nat.mod_lt _ hN0⟩ then 2 else 3 := hsh
          rw [hhi_eq]
          constructor
          · intro h2
            split_ifs at h2 with h12
            · rcases h12 with rfl | h2'
              · left; rfl
              · right; exact hv2.mp h2'.symm
            · omega
          · rintro (rfl | hs)
            · simp
            · have : v = ⟨(s.val + N - 1) % N, Nat.mod_lt _ hN0⟩ := (hv2.mpr hs).symm
              simp [this]
        let v_next : Fin N := ⟨(v.val + 1) % N, Nat.mod_lt _ hN0⟩
        have hvv : v ≠ v_next := by
          intro h; have := congrArg Fin.val h; simp only [v_next] at this
          have hv := v.isLt
          by_cases hlt : v.val + 1 < N
          · rw [Nat.mod_eq_of_lt hlt] at this; omega
          · have e : v.val + 1 = N := by omega
            rw [e, Nat.mod_self] at this; omega
        let emb : Fin (M / N) × Bool → Fin M := fun p =>
          ⟨p.1.val * N + (if p.2 then v_next.val else v.val) + 1, by
            have h1 : (p.1.val + 1) * N ≤ (M / N) * N := Nat.mul_le_mul_right N p.1.isLt
            have h2 : (if p.2 then v_next.val else v.val) < N := by split_ifs <;> exact Fin.isLt _
            rw [add_mul, one_mul] at h1; omega⟩
        have hemb_inj : Function.Injective emb := by
          intro ⟨q1, b1⟩ ⟨q2, b2⟩ h
          have hv' := congrArg Fin.val h
          simp only [emb] at hv'
          have h1 : (if b1 then v_next.val else v.val) < N := by split_ifs <;> exact Fin.isLt _
          have h2 : (if b2 then v_next.val else v.val) < N := by split_ifs <;> exact Fin.isLt _
          have hq : q1.val = q2.val := by
            have hd := congrArg (· / N) (show q1.val * N + (if b1 then v_next.val else v.val) =
              q2.val * N + (if b2 then v_next.val else v.val) by omega)
            rw [mul_comm q1.val N, mul_comm q2.val N, Nat.mul_add_div hN0, Nat.mul_add_div hN0,
              Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2, add_zero, add_zero] at hd
            exact hd
          have hb : b1 = b2 := by
            rw [hq] at hv'
            cases b1 <;> cases b2
            · rfl
            · exfalso; exact hvv (Fin.ext (by simp at hv'; omega))
            · exfalso; exact hvv (Fin.ext (by simp at hv'; omega))
            · rfl
          exact Prod.ext (Fin.ext hq) hb
        have hfilt : (Finset.univ : Finset (Fin M)).filter (fun i => i ≠ j0 ∧ hits (D i) v = 2) =
            Finset.univ.image emb := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · rintro ⟨hij, hhi⟩
            simp only [D, hij, ↓reduceIte] at hhi
            have hs := (hhits_s ⟨(i.val - 1) % N, Nat.mod_lt _ hN0⟩).mp hhi
            have hi_pos : 0 < i.val := by
              by_contra h0; exact hij (Fin.ext (by simp [j0]; omega))
            have hq_lt : (i.val - 1) / N < M / N := by
              have h1 : i.val - 1 < (M / N) * N := by have := i.isLt; omega
              exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h1)
            rcases hs with hs1 | hs2
            · refine ⟨(⟨(i.val - 1) / N, hq_lt⟩, false), ?_⟩
              apply Fin.ext; simp only [emb, Bool.false_eq_true, ↓reduceIte]
              have hmod : (i.val - 1) % N = v.val := congrArg Fin.val hs1
              have hdiv := Nat.div_add_mod (i.val - 1) N
              rw [mul_comm] at hdiv; omega
            · refine ⟨(⟨(i.val - 1) / N, hq_lt⟩, true), ?_⟩
              apply Fin.ext; simp only [emb, ↓reduceIte]
              have hmod : (i.val - 1) % N = v_next.val := congrArg Fin.val hs2
              have hdiv := Nat.div_add_mod (i.val - 1) N
              rw [mul_comm] at hdiv; omega
          · rintro ⟨⟨q, b⟩, rfl⟩
            have hij : emb (q, b) ≠ j0 := by
              intro h; have := congrArg Fin.val h; simp [emb, j0] at this
            refine ⟨hij, ?_⟩
            simp only [D, hij, ↓reduceIte]
            apply (hhits_s _).mpr
            have hsub : (emb (q, b)).val - 1 = q.val * N + (if b then v_next.val else v.val) := by
              simp [emb]
            have hlt_r : (if b then v_next.val else v.val) < N := by split_ifs <;> exact Fin.isLt _
            have hmod : ((emb (q, b)).val - 1) % N = if b then v_next.val else v.val := by
              rw [hsub, mul_comm q.val N, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_r]
            cases b
            · left; apply Fin.ext; simpa using hmod
            · right; apply Fin.ext; simpa using hmod
        rw [hfilt, Finset.card_image_of_injective _ hemb_inj, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]
    · have hval : value = rounded := by simp [value, hex]
      rw [hval]
      by_cases ht_eq : t = N
      · let x0 : Fin N := ⟨0, hN0⟩
        let x1 : Fin N := ⟨1, by omega⟩
        let y0 : Fin N := ⟨0, hN0⟩
        have hne01 : x0 ≠ x1 := by intro h; have := congrArg Fin.val h; simp [x0, x1] at this
        let D : Fin M → Circ := fun _ => PEqualNP.Outside.L_meta_33602_aux.panelCirc N x0 x1 y0
        have htsh : PEqualNP.Outside.L_meta_33602_aux.IsTShape (table (PEqualNP.Outside.L_meta_33602_aux.panelCirc N x0 x1 y0)) :=
          Or.inl ⟨x0, x1, y0, hne01, fun x y => PEqualNP.Outside.L_meta_33602_aux.panelCirc_tbl x0 x1 y0 x y⟩
        have hD_fits : ∀ i, fits (D i) := by
          intro i
          have hleg := PEqualNP.Outside.L_meta_33602_aux.panelCirc_legal x0 x1 y0
          have har : area (D i) = 3 * N - 2 := PEqualNP.Outside.L_meta_33602_aux.areaOf_tshape htsh
          exact ⟨⟨hleg.1, hleg.2.1, hleg.2.2.1⟩, hleg.2.2.2, by omega⟩
        refine ⟨D, hD_fits, fun u => ?_⟩
        have hloss_i : ∀ i : Fin M, loss (D i) u.val = (N * t - 3 * a - 2) + 4 := by
          intro i
          have hl : loss (D i) u.val = (N * t - 3 * a - 2) +
              2 * ((Finset.univ : Finset (Fin t)).filter (fun k =>
                PEqualNP.Outside.L_meta_33602_aux.hitsOf (table (D i))
                  ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card :=
            PEqualNP.Outside.L_meta_33602_aux.tshape_loss_formula htN h2t hN htsh u
          rcases PEqualNP.Outside.L_meta_33602_aux.hitsOf_tshape hN0 htsh with ⟨v1, v2, hvne, hhi⟩
          have hcard2 : ((Finset.univ : Finset (Fin t)).filter (fun k =>
              PEqualNP.Outside.L_meta_33602_aux.hitsOf (table (D i))
                ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card = 2 := by
            let f : Fin t → Fin N := fun k => ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩
            have hbij : Function.Bijective f := by
              have hinj : Function.Injective f := by
                intro k1 k2 h
                have hv := congrArg Fin.val h; simp only [f] at hv
                have h1 : k1.val < N := by have := k1.isLt; omega
                have h2 : k2.val < N := by have := k2.isLt; omega
                have hu := u.isLt
                apply Fin.ext
                by_cases c1 : u.val + k1.val < N <;> by_cases c2 : u.val + k2.val < N
                · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hv; omega
                · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
                · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt c2] at hv; omega
                · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
                    Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
              refine ⟨hinj, fun v => ?_⟩
              refine ⟨⟨(v.val + N - u.val) % N, by rw [ht_eq]; exact Nat.mod_lt _ hN0⟩, ?_⟩
              have := (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y u ⟨(v.val + N - u.val) % N, Nat.mod_lt _ hN0⟩).2 v rfl
              exact Fin.ext (congrArg Fin.val this.symm)
            have himg : ((Finset.univ : Finset (Fin t)).filter (fun k =>
                PEqualNP.Outside.L_meta_33602_aux.hitsOf (table (D i)) (f k) = 2)).image f = {v1, v2} := by
              ext v
              simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨k, hk, rfl⟩
                rw [hhi] at hk; split_ifs at hk with h
                · exact h
                · omega
              · intro h12
                rcases hbij.2 v with ⟨k, rfl⟩
                refine ⟨k, ?_, rfl⟩
                rw [hhi, if_pos h12]
            rw [← Finset.card_image_of_injective _ hbij.1, himg,
              Finset.card_insert_of_notMem (by simp [hvne]), Finset.card_singleton]
          rw [hl, hcard2]
        have htot : total D u = M * (N * t - 3 * a - 2) + 4 * M := by
          unfold total
          rw [Finset.sum_congr rfl (fun i _ => hloss_i i)]
          simp [mul_add]; ring
        rw [htot]
        have hceil : (2 * M * t + N - 1) / N = 2 * M := by
          rw [ht_eq]
          have e : 2 * M * N + N - 1 = N * (2 * M) + (N - 1) := by ring_nf; omega
          rw [e, Nat.mul_add_div hN0, Nat.div_eq_of_lt (by omega), add_zero]
        simp only [rounded, hceil]
        omega
      · let b := N - t
        have hb_pos : 0 < b := by omega
        have hb_lt : b < N := by omega
        let shiftOf : ℕ → Fin N := fun m => ⟨((m + 1) * b) % N, Nat.mod_lt _ hN0⟩
        have hpair_ne : ∀ i : Fin M, shiftOf (2 * i.val) ≠ shiftOf (2 * i.val + 1) := by
          intro i h
          have hv := congrArg Fin.val h
          simp only [shiftOf] at hv
          have e1 : (2 * i.val + 1 + 1) * b = (2 * i.val + 1) * b + b := by ring
          rw [e1] at hv
          set s := ((2 * i.val + 1) * b) % N
          have hs : s < N := Nat.mod_lt _ hN0
          have e2 : ((2 * i.val + 1) * b + b) % N = (s + b) % N := by
            simp only [s, Nat.add_mod, Nat.mod_mod]
          rw [e2] at hv
          by_cases hlt : s + b < N
          · rw [Nat.mod_eq_of_lt hlt] at hv; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
        let D : Fin M → Circ := fun i =>
          let x0 : Fin N := ⟨(N - (shiftOf (2 * i.val)).val) % N, Nat.mod_lt _ hN0⟩
          let x1 : Fin N := ⟨(N - (shiftOf (2 * i.val + 1)).val) % N, Nat.mod_lt _ hN0⟩
          PEqualNP.Outside.L_meta_33602_aux.panelCirc N x0 x1 ⟨0, hN0⟩
        have hD_info : ∀ i : Fin M, fits (D i) ∧
            PEqualNP.Outside.L_meta_33602_aux.IsTShape (table (D i)) ∧
            ∀ v : X, hits (D i) v =
              if v = shiftOf (2 * i.val) ∨ v = shiftOf (2 * i.val + 1) then 2 else 3 := by
          intro i
          have hinfo := PEqualNP.Outside.L_meta_33602_aux.panelCirc_hits_for_shifts hN0 (hpair_ne i)
          have hleg := PEqualNP.Outside.L_meta_33602_aux.panelCirc_legal
            (⟨(N - (shiftOf (2 * i.val)).val) % N, Nat.mod_lt _ hN0⟩ : Fin N)
            ⟨(N - (shiftOf (2 * i.val + 1)).val) % N, Nat.mod_lt _ hN0⟩ ⟨0, hN0⟩
          have htsh : PEqualNP.Outside.L_meta_33602_aux.IsTShape (table (D i)) :=
            Or.inl ⟨_, _, ⟨0, hN0⟩, hinfo.1, fun x y => PEqualNP.Outside.L_meta_33602_aux.panelCirc_tbl _ _ _ x y⟩
          have har := PEqualNP.Outside.L_meta_33602_aux.areaOf_tshape htsh
          exact ⟨⟨⟨hleg.1, hleg.2.1, hleg.2.2.1⟩, hleg.2.2.2, by change PEqualNP.Outside.L_meta_33602_aux.areaOf _ ≤ A; omega⟩,
            htsh, hinfo.2⟩
        refine ⟨D, fun i => (hD_info i).1, fun u => ?_⟩
        have htot_eq : total D u = M * (N * t - 3 * a - 2) +
            2 * ∑ i : Fin M, ((Finset.univ : Finset (Fin t)).filter (fun k =>
              hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card := by
          unfold total
          have hloss_i : ∀ i : Fin M, loss (D i) u.val = (N * t - 3 * a - 2) +
              2 * ((Finset.univ : Finset (Fin t)).filter (fun k =>
                hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card :=
            fun i => PEqualNP.Outside.L_meta_33602_aux.tshape_loss_formula htN h2t hN (hD_info i).2.1 u
          rw [Finset.sum_congr rfl (fun i _ => hloss_i i), Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
        rw [htot_eq]
        let w : Fin N := ⟨(u.val + t) % N, Nat.mod_lt _ hN0⟩
        have hin_win : ∀ v : Fin N,
            (∃ k : Fin t, ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = v) ↔
            ¬ ((v.val + N - w.val) % N < b) := by
          intro v
          have hu := u.isLt
          have hv := v.isLt
          have h1 : (∃ k : Fin t, (u.val + k.val) % N = v.val) ↔ (v.val + N - u.val) % N < t := by
            constructor
            · rintro ⟨k, hk⟩
              have hsh := (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y u ⟨k.val, by omega⟩).1
              have : (v.val + N - u.val) % N = k.val := by
                rw [← hk]; exact hsh
              rw [this]; exact k.isLt
            · intro hlt
              refine ⟨⟨(v.val + N - u.val) % N, hlt⟩, ?_⟩
              have h2 := (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y u ⟨(v.val + N - u.val) % N, by omega⟩).2 v rfl
              exact (congrArg Fin.val h2).symm
          have h2 : (∃ k : Fin t, (⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ : Fin N) = v) ↔
              (∃ k : Fin t, (u.val + k.val) % N = v.val) :=
            ⟨fun ⟨k, hk⟩ => ⟨k, congrArg Fin.val hk⟩, fun ⟨k, hk⟩ => ⟨k, Fin.ext hk⟩⟩
          rw [h2, h1]
          set d := (v.val + N - u.val) % N
          have hd : d < N := Nat.mod_lt _ hN0
          have hw_eq : (v.val + N - w.val) % N = (d + N - t) % N := by
            have hvu : (u.val + d) % N = v.val := by
              have := (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y u ⟨d, hd⟩).2 v rfl
              exact (congrArg Fin.val this).symm
            have hdw : (w.val + (d + N - t) % N) % N = v.val := by
              have e1 : (w.val + (d + N - t) % N) % N = ((u.val + t) + (d + N - t)) % N := by
                simp only [w]
                rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod]
              rw [e1]
              have e2 : u.val + t + (d + N - t) = (u.val + d) + N := by omega
              rw [e2, Nat.add_mod_right, hvu]
            have := (PEqualNP.Outside.L_meta_33602_aux.shift_unique_y w ⟨(d + N - t) % N, Nat.mod_lt _ hN0⟩).1
            simpa [hdw] using this
          rw [hw_eq]
          by_cases hdt : d < t
          · have hm : (d + N - t) % N = d + N - t := Nat.mod_eq_of_lt (by omega)
            rw [hm]; omega
          · have hm : (d + N - t) % N = d - t := by
              have hle : t ≤ d := Nat.le_of_not_lt hdt
              have e : d + N - t = (d - t) + N := by
                calc
                  d + N - t = (d - t + t) + N - t := by rw [Nat.sub_add_cancel hle]
                  _ = ((d - t) + N) + t - t := by ring_nf
                  _ = (d - t) + N := Nat.add_sub_cancel _ _
              rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [hm]
            have hdt_lt : d - t < b := Nat.sub_lt_sub_right (Nat.le_of_not_lt hdt) hd
            exact ⟨fun h => absurd h hdt, fun hnot => absurd hdt_lt hnot⟩
        have he_i : ∀ i : Fin M,
            ((Finset.univ : Finset (Fin t)).filter (fun k =>
              hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card =
            (if ((shiftOf (2 * i.val)).val + N - w.val) % N < b then 0 else 1) +
            (if ((shiftOf (2 * i.val + 1)).val + N - w.val) % N < b then 0 else 1) := by
          intro i
          have hinj : Function.Injective (fun k : Fin t => (⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ : Fin N)) := by
            intro k1 k2 h
            have hv := congrArg Fin.val h; simp only at hv
            have h1 : k1.val < t := k1.isLt; have h2 : k2.val < t := k2.isLt; have hu := u.isLt
            apply Fin.ext
            by_cases c1 : u.val + k1.val < N <;> by_cases c2 : u.val + k2.val < N
            · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hv; omega
            · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt c2] at hv; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
          have hset : ((Finset.univ : Finset (Fin t)).filter (fun k =>
              hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card =
              (((Finset.univ : Finset (Fin t)).image (fun k =>
                (⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ : Fin N))) ∩
                {shiftOf (2 * i.val), shiftOf (2 * i.val + 1)}).card := by
            rw [← Finset.card_image_of_injective _ hinj]
            congr 1
            ext v
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨k, hk, rfl⟩
              rw [(hD_info i).2.2] at hk
              split_ifs at hk with h12
              · exact ⟨⟨k, rfl⟩, h12⟩
              · omega
            · rintro ⟨⟨k, rfl⟩, h12⟩
              refine ⟨k, ?_, rfl⟩
              rw [(hD_info i).2.2]; simp [h12]
          rw [hset]
          set W : Finset (Fin N) := (Finset.univ : Finset (Fin t)).image
            (fun k => (⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ : Fin N))
          have hmem1 : shiftOf (2 * i.val) ∈ W ↔ ¬ ((shiftOf (2 * i.val)).val + N - w.val) % N < b := by
            simpa [W] using hin_win (shiftOf (2 * i.val))
          have hmem2 : shiftOf (2 * i.val + 1) ∈ W ↔ ¬ ((shiftOf (2 * i.val + 1)).val + N - w.val) % N < b := by
            simpa [W] using hin_win (shiftOf (2 * i.val + 1))
          have hne := hpair_ne i
          have hpair_inter : (W ∩ {shiftOf (2 * i.val), shiftOf (2 * i.val + 1)}).card =
              (if shiftOf (2 * i.val) ∈ W then 1 else 0) + (if shiftOf (2 * i.val + 1) ∈ W then 1 else 0) := by
            rw [Finset.inter_comm]
            by_cases h1 : shiftOf (2 * i.val) ∈ W <;> by_cases h2 : shiftOf (2 * i.val + 1) ∈ W
            · have : ({shiftOf (2 * i.val), shiftOf (2 * i.val + 1)} ∩ W) =
                  {shiftOf (2 * i.val), shiftOf (2 * i.val + 1)} := by
                ext z; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
                exact ⟨fun h => h.1, fun h => ⟨h, by rcases h with rfl | rfl; exact h1; exact h2⟩⟩
              rw [this, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]; simp [h1, h2]
            · have : ({shiftOf (2 * i.val), shiftOf (2 * i.val + 1)} ∩ W) = {shiftOf (2 * i.val)} := by
                ext z; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
                exact ⟨by rintro ⟨rfl | rfl, hz⟩; rfl; exact (h2 hz).elim, by rintro rfl; exact ⟨Or.inl rfl, h1⟩⟩
              rw [this, Finset.card_singleton]; simp [h1, h2]
            · have : ({shiftOf (2 * i.val), shiftOf (2 * i.val + 1)} ∩ W) = {shiftOf (2 * i.val + 1)} := by
                ext z; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
                exact ⟨by rintro ⟨rfl | rfl, hz⟩; exact (h1 hz).elim; rfl, by rintro rfl; exact ⟨Or.inr rfl, h2⟩⟩
              rw [this, Finset.card_singleton]; simp [h1, h2]
            · have : ({shiftOf (2 * i.val), shiftOf (2 * i.val + 1)} ∩ W) = ∅ := by
                ext z; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
                rintro ⟨rfl | rfl, hz⟩
                · exact h1 hz
                · exact h2 hz
              rw [this, Finset.card_empty]; simp [h1, h2]
          rw [hpair_inter]
          by_cases c1 : ((shiftOf (2 * i.val)).val + N - w.val) % N < b <;>
            by_cases c2 : ((shiftOf (2 * i.val + 1)).val + N - w.val) % N < b
          · simp [c1, c2, hmem1.not.mpr (not_not.mpr c1), hmem2.not.mpr (not_not.mpr c2)]
          · simp [c1, c2, hmem1.not.mpr (not_not.mpr c1), hmem2.mpr c2]
          · simp [c1, c2, hmem1.mpr c1, hmem2.not.mpr (not_not.mpr c2)]
          · simp [c1, c2, hmem1.mpr c1, hmem2.mpr c2]
        have hsum_bound : (∑ i : Fin M, ((Finset.univ : Finset (Fin t)).filter (fun k =>
              hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card) +
            ((Finset.univ : Finset (Fin (2 * M))).filter (fun m =>
              (((m.val + 1) * b) % N + N - w.val) % N < b)).card = 2 * M := by
          rw [Finset.sum_congr rfl (fun i _ => he_i i), Finset.card_filter]
          have hpair_sum : (∑ m : Fin (2 * M),
              if (((m.val + 1) * b) % N + N - w.val) % N < b then 1 else 0) =
              ∑ i : Fin M,
                ((if ((shiftOf (2 * i.val)).val + N - w.val) % N < b then 1 else 0) +
                 (if ((shiftOf (2 * i.val + 1)).val + N - w.val) % N < b then 1 else 0)) := by
            let g : Fin (2 * M) → ℕ := fun m =>
              if (((m.val + 1) * b) % N + N - w.val) % N < b then 1 else 0
            let e : Fin M × Fin 2 ≃ Fin (2 * M) :=
              { toFun := fun p => ⟨2 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
                invFun := fun m => (⟨m.val / 2, by have := m.isLt; omega⟩, ⟨m.val % 2, Nat.mod_lt _ (by omega)⟩)
                left_inv := fun ⟨i, j⟩ => by
                  have hj := j.isLt
                  apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
                right_inv := fun m => by apply Fin.ext; simp; omega }
            rw [← Fintype.sum_equiv e (fun p => g (e p)) g (fun _ => rfl), Fintype.sum_prod_type]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Fin.sum_univ_two]
            simp [g, e, shiftOf]
          rw [hpair_sum, ← Finset.sum_add_distrib]
          have hpt : ∀ i : Fin M,
              ((if ((shiftOf (2 * i.val)).val + N - w.val) % N < b then 0 else 1) +
               (if ((shiftOf (2 * i.val + 1)).val + N - w.val) % N < b then 0 else 1)) +
              ((if ((shiftOf (2 * i.val)).val + N - w.val) % N < b then 1 else 0) +
               (if ((shiftOf (2 * i.val + 1)).val + N - w.val) % N < b then 1 else 0)) = 2 := by
            intro i; split_ifs <;> omega
          rw [Finset.sum_congr rfl (fun i _ => hpt i)]
          simp [mul_comm]
        have hbeat : (2 * M * (N - t)) / N ≤ ((Finset.univ : Finset (Fin (2 * M))).filter (fun m =>
            (((m.val + 1) * b) % N + N - w.val) % N < b)).card :=
          PEqualNP.Outside.L_meta_33602_aux.beatty_miss_count (K := 2 * M) hN0 hb_lt w
        have hcomp := PEqualNP.Outside.L_meta_33602_aux.nat_sub_div_complement (K := 2 * M) hN0 htN
        have hle_ceil : (∑ i : Fin M, ((Finset.univ : Finset (Fin t)).filter (fun k =>
            hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card) ≤ (2 * M * t + N - 1) / N := by
          rw [← hcomp]; omega
        simp only [rounded]
        omega
  · intro D hD
    have hall_A_lb : (∀ i : Fin M, area (D i) = A) → ∃ u : X, rounded ≤ total D u := by
      intro hallA
      have hT : ∀ i : Fin M, PEqualNP.Outside.L_meta_33602_aux.IsTShape (table (D i)) :=
        fun i => harea_eq_A (D i) (hD i) (hallA i)
      let E : X → ℕ := fun u =>
        ∑ i : Fin M, ((Finset.univ : Finset (Fin t)).filter (fun k =>
          hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card
      have htot_u : ∀ u : X, total D u = M * (N * t - 3 * a - 2) + 2 * E u := by
        intro u
        unfold total
        have hli : ∀ i : Fin M, loss (D i) u.val = (N * t - 3 * a - 2) +
            2 * ((Finset.univ : Finset (Fin t)).filter (fun k =>
              hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card :=
          fun i => PEqualNP.Outside.L_meta_33602_aux.tshape_loss_formula htN h2t hN (hT i) u
        rw [Finset.sum_congr rfl (fun i _ => hli i), Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [E]
      have hsumE : ∑ u : X, E u = 2 * M * t := by
        simp only [E]
        rw [Finset.sum_comm]
        have hinner : ∀ i : Fin M,
            (∑ u : X, ((Finset.univ : Finset (Fin t)).filter (fun k =>
              hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card) = 2 * t := by
          intro i
          simp only [Finset.card_filter]
          rw [PEqualNP.Outside.L_meta_33602_aux.sum_cyclic_window hN0
            (fun v => if hits (D i) v = 2 then 1 else 0)]
          rcases PEqualNP.Outside.L_meta_33602_aux.hitsOf_tshape hN0 (hT i) with ⟨v1, v2, hvne, hhi⟩
          have hsum2 : (∑ v : Fin N, if hits (D i) v = 2 then 1 else 0) = 2 := by
            rw [← Finset.card_filter]
            have hset : (Finset.univ : Finset (Fin N)).filter (fun v => hits (D i) v = 2) = {v1, v2} := by
              ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton]
              change PEqualNP.Outside.L_meta_33602_aux.hitsOf _ v = 2 ↔ _
              rw [hhi]; split_ifs with h <;> simp [h]
            rw [hset, Finset.card_insert_of_notMem (by simp [hvne]), Finset.card_singleton]
          rw [hsum2, mul_comm]
        rw [Finset.sum_congr rfl (fun i _ => hinner i)]
        simp [mul_assoc, mul_left_comm]
      by_contra hlt_all
      push Not at hlt_all
      have hElt : ∀ u : X, E u + 1 ≤ (2 * M * t + N - 1) / N := by
        intro u
        have hu := hlt_all u
        rw [htot_u u] at hu
        simp only [rounded] at hu
        omega
      have hsum_le : ∑ u : X, (E u + 1) ≤ ∑ _u : X, ((2 * M * t + N - 1) / N) :=
        Finset.sum_le_sum (fun u _ => hElt u)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, X, Fintype.card_fin,
        smul_eq_mul, mul_one, hsumE] at hsum_le
      have hdiv_le : N * ((2 * M * t + N - 1) / N) ≤ 2 * M * t + N - 1 :=
        Nat.mul_div_le (2 * M * t + N - 1) N
      omega
    have hsum_total_eq : (∑ u : X, total D u) + a * (∑ i : Fin M, area (D i)) = M * N * N * t := by
      simp only [total]
      rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
      have hinner : ∀ i : Fin M, (∑ u : X, loss (D i) u.val) + a * area (D i) = N * N * t :=
        fun i => PEqualNP.Outside.L_meta_33602_aux.sum_loss_eq htN h2t hN0 (table (D i))
      rw [Finset.sum_congr rfl (fun i _ => hinner i)]
      simp [mul_assoc]
    have hsum_area_le : (∑ i : Fin M, area (D i)) +
        ((Finset.univ : Finset (Fin M)).filter (fun i => area (D i) ≠ A)).card * (N - 2) ≤ M * A := by
      have hpt : ∀ i : Fin M, area (D i) + (if area (D i) ≠ A then N - 2 else 0) ≤ A := by
        intro i
        by_cases hi : area (D i) = A
        · simp [hi]
        · have hle := harea_lt_A (D i) (hD i) hi
          simp only [hi, ne_eq, not_false_eq_true, ↓reduceIte]
          omega
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
      exact hsum
    have hsum_tot_ge :
        M * N * (N * t - 3 * a - 2) + 4 * M * t +
        a * (((Finset.univ : Finset (Fin M)).filter (fun i => area (D i) ≠ A)).card * (N - 2)) ≤
        ∑ u : X, total D u := by
      have hmul_A : M * N * (N * t - 3 * a - 2) + 4 * M * t + a * (M * A) = M * N * N * t := by
        have h1 : N * (N * t - 3 * a - 2) + 4 * t + a * A = N * N * t := by
          have hsub : (N * t - 3 * a - 2) + (3 * a + 2) = N * t := by omega
          have hAeq : A + 2 = 3 * N := by omega
          have h2teq : 2 * t = N + a := by omega
          nlinarith
        calc
          M * N * (N * t - 3 * a - 2) + 4 * M * t + a * (M * A) =
              M * (N * (N * t - 3 * a - 2) + 4 * t + a * A) := by ring
          _ = M * (N * N * t) := by rw [h1]
          _ = M * N * N * t := by ring
      have hle_a := Nat.mul_le_mul_left a hsum_area_le
      rw [mul_add] at hle_a
      omega
    have hN_rounded : N * rounded ≤ M * N * (N * t - 3 * a - 2) + 4 * M * t + 2 * (N - 1) := by
      have hdiv : N * ((2 * M * t + N - 1) / N) ≤ 2 * M * t + N - 1 :=
        Nat.mul_div_le (2 * M * t + N - 1) N
      have hr : N * rounded = M * N * (N * t - 3 * a - 2) + 2 * (N * ((2 * M * t + N - 1) / N)) := by
        simp only [rounded]; ring
      have hmt : 2 * (2 * M * t) = 4 * M * t := by ring
      omega
    have hdiv_pos : 1 ≤ (2 * M * t + N - 1) / N :=
      Nat.div_pos (by have : 1 ≤ 2 * M * t := Nat.mul_pos (by omega) (by omega); omega) hN0
    constructor
    · by_cases hallA : ∀ i : Fin M, area (D i) = A
      · rcases hall_A_lb hallA with ⟨u, hu⟩
        refine ⟨u, ?_⟩
        have : value ≤ rounded := Nat.sub_le _ _
        omega
      · push Not at hallA
        rcases hallA with ⟨i0, hi0⟩
        set k := ((Finset.univ : Finset (Fin M)).filter (fun i => area (D i) ≠ A)).card
        have hk1 : 1 ≤ k := Finset.card_pos.mpr ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0⟩⟩
        by_contra hlt_all
        push Not at hlt_all
        have hsum_le : ∑ u : X, total D u ≤ N * (value - 1) := by
          have h1 : ∀ u : X, total D u ≤ value - 1 := fun u => by have := hlt_all u; omega
          have h2 := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => h1 u)
          simpa [X] using h2
        by_cases hex : exception
        · have hval : value = rounded - 1 := by simp [value, hex]
          have hNval : N * (value - 1) + 2 * N = N * rounded := by
            have hge2 : 2 ≤ rounded := by simp only [rounded]; omega
            rw [hval]
            have : rounded - 1 - 1 + 2 = rounded := by omega
            calc
              N * (rounded - 1 - 1) + 2 * N = N * (rounded - 1 - 1 + 2) := by ring
              _ = N * rounded := by rw [this]
          have : a * (k * (N - 2)) ≥ 1 * (1 * (N - 2)) :=
            Nat.mul_le_mul ha_pos (Nat.mul_le_mul hk1 (le_refl _))
          omega
        · have hval : value = rounded := by simp [value, hex]
          have hNval : N * (value - 1) + N = N * rounded := by
            have hge1 : 1 ≤ rounded := by simp only [rounded]; omega
            rw [hval]
            have : rounded - 1 + 1 = rounded := by omega
            calc
              N * (rounded - 1) + N = N * (rounded - 1 + 1) := by ring
              _ = N * rounded := by rw [this]
          have hka : a * (k * (N - 2)) ≤ N - 2 := by omega
          have ha1 : a = 1 := by
            by_contra hne1
            have : 2 ≤ a := by omega
            have : 2 * (N - 2) ≤ a * (k * (N - 2)) := by
              have h1 : 1 * (N - 2) ≤ k * (N - 2) := Nat.mul_le_mul_right _ hk1
              nlinarith
            omega
          have hk_eq1 : k = 1 := by
            by_contra hne1
            have hk2 : 2 ≤ k := by omega
            have h2N : 2 * (N - 2) ≤ k * (N - 2) := Nat.mul_le_mul_right (N - 2) hk2
            rw [ha1, one_mul] at hka
            omega
          have h2t1 : 2 * t = N + 1 := by omega
          have hMmod_ne : M % N ≠ 1 := fun h1 => hex ⟨h2t1, h1⟩
          have hmod_2Mt : (2 * M * t) % N = M % N := by
            have e : 2 * M * t = M * N + M := by
              calc
                2 * M * t = M * (2 * t) := by ring
                _ = M * (N + 1) := by rw [h2t1]
                _ = M * N + M := by ring
            rw [e, Nat.mul_add_mod_self_right]
          have hN_rounded_tight : N * rounded ≤ M * N * (N * t - 3 * a - 2) + 4 * M * t + 2 * (N - 2) := by
            set r := (2 * M * t) % N
            have hr_lt : r < N := Nat.mod_lt _ hN0
            have hr_ne1 : r ≠ 1 := by rwa [hmod_2Mt]
            have hdiv_tight : N * ((2 * M * t + N - 1) / N) ≤ 2 * M * t + N - 2 := by
              have hqr := Nat.div_add_mod (2 * M * t) N
              by_cases hr0 : r = 0
              · have e : (2 * M * t + N - 1) / N = (2 * M * t) / N := by
                  have h1 : 2 * M * t + N - 1 = N * ((2 * M * t) / N) + (N - 1) := by omega
                  have h0 : (N - 1) / N = 0 := Nat.div_eq_of_lt (by omega)
                  conv_lhs => rw [h1, Nat.mul_add_div hN0]
                  rw [h0, add_zero]
                rw [e]; omega
              · have hr2 : 2 ≤ r := by omega
                have e : (2 * M * t + N - 1) / N = (2 * M * t) / N + 1 := by
                  have h1 : 2 * M * t + N - 1 = N * ((2 * M * t) / N + 1) + (r - 1) := by
                    rw [mul_add, mul_one]; omega
                  have h0 : (r - 1) / N = 0 := Nat.div_eq_of_lt (by omega)
                  conv_lhs => rw [h1, Nat.mul_add_div hN0]
                  rw [h0, add_zero]
                rw [e, mul_add, mul_one]; omega
            have hr_eq : N * rounded = M * N * (N * t - 3 * a - 2) + 2 * (N * ((2 * M * t + N - 1) / N)) := by
              simp only [rounded]; ring
            have hmt : 2 * (2 * M * t) = 4 * M * t := by ring
            omega
          rw [ha1, hk_eq1, one_mul, one_mul] at hsum_tot_ge
          rw [ha1] at hN_rounded_tight
          omega
    · intro hex
      refine ⟨fun hle_all => ?_, hexcept_conv D hD hex⟩
      have hval : value = rounded - 1 := by simp [value, hex]
      have hnot_allA : ¬ ∀ i : Fin M, area (D i) = A := by
        intro hallA
        rcases hall_A_lb hallA with ⟨u, hu⟩
        have := hle_all u
        have hge1 : 1 ≤ rounded := by simp only [rounded]; omega
        omega
      push Not at hnot_allA
      rcases hnot_allA with ⟨j, hj_ne⟩
      set k := ((Finset.univ : Finset (Fin M)).filter (fun i => area (D i) ≠ A)).card
      have hk1 : 1 ≤ k := Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_ne⟩⟩
      have ha1 : a = 1 := by rcases hex with ⟨h2t1, _⟩; omega
      have hsum_le : ∑ u : X, total D u ≤ N * value := by
        have h2 := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => hle_all u)
        simpa [X] using h2
      have hNval : N * value + N = N * rounded := by
        have hge1 : 1 ≤ rounded := by simp only [rounded]; omega
        rw [hval]
        have : rounded - 1 + 1 = rounded := by omega
        calc
          N * (rounded - 1) + N = N * (rounded - 1 + 1) := by ring
          _ = N * rounded := by rw [this]
      have hk_eq1 : k = 1 := by
        rw [ha1, one_mul] at hsum_tot_ge
        rw [ha1] at hN_rounded
        by_contra hne1
        have hk2 : 2 ≤ k := by omega
        have h2N : 2 * (N - 2) ≤ k * (N - 2) := Nat.mul_le_mul_right (N - 2) hk2
        omega
      have hrestA : ∀ i : Fin M, i ≠ j → area (D i) = A := by
        intro i hij
        by_contra hine
        have h2 : 2 ≤ k := by
          have hsub : ({i, j} : Finset (Fin M)) ⊆
              (Finset.univ : Finset (Fin M)).filter (fun m => area (D m) ≠ A) := by
            intro m hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl <;> simp [hine, hj_ne]
          have hc := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton] at hc
          exact hc
        omega
      have hsum_eq : ∑ u : X, total D u = N * value := by
        rw [ha1, hk_eq1, one_mul, one_mul] at hsum_tot_ge
        rw [ha1] at hN_rounded
        omega
      have hall_eq : ∀ u : X, total D u = value := by
        intro u
        by_contra hne
        have hlt : total D u < value := lt_of_le_of_ne (hle_all u) hne
        have hsum_lt : ∑ v : X, total D v < ∑ _v : X, value :=
          Finset.sum_lt_sum (fun v _ => hle_all v) ⟨u, Finset.mem_univ u, hlt⟩
        simp only [Finset.sum_const, Finset.card_univ, X, Fintype.card_fin, smul_eq_mul] at hsum_lt
        rw [hsum_eq] at hsum_lt
        exact lt_irrefl _ hsum_lt
      have harea_j : area (D j) = 2 * N := by
        have hsum_A : ∑ i : Fin M, area (D i) = area (D j) + (M - 1) * A := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          congr 1
          rw [Finset.sum_congr rfl (fun i hi => hrestA i (Finset.mem_erase.mp hi).1),
            Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
        have hmul_A : M * N * (N * t - 3 * a - 2) + 4 * M * t + a * (M * A) = M * N * N * t := by
          have h1 : N * (N * t - 3 * a - 2) + 4 * t + a * A = N * N * t := by
            have hsub : (N * t - 3 * a - 2) + (3 * a + 2) = N * t := by omega
            have hAeq : A + 2 = 3 * N := by omega
            have heq1 : N * (N * t - 3 * a - 2) + N * (3 * a + 2) = N * N * t := by
              calc
                N * (N * t - 3 * a - 2) + N * (3 * a + 2) = N * ((N * t - 3 * a - 2) + (3 * a + 2)) := by ring
                _ = N * (N * t) := by rw [hsub]
                _ = N * N * t := by ring
            have heq2 : 4 * t + a * A = N * (3 * a + 2) := by
              have h4t : 4 * t = 2 * N + 2 * a := by omega
              have haA : a * A + 2 * a = 3 * a * N := by
                calc
                  a * A + 2 * a = a * (A + 2) := by ring
                  _ = a * (3 * N) := by rw [hAeq]
                  _ = 3 * a * N := by ring
              have hRHS : N * (3 * a + 2) = 3 * a * N + 2 * N := by ring
              omega
            omega
          calc
            M * N * (N * t - 3 * a - 2) + 4 * M * t + a * (M * A) =
                M * (N * (N * t - 3 * a - 2) + 4 * t + a * A) := by ring
            _ = M * (N * N * t) := by rw [h1]
            _ = M * N * N * t := by ring
        have hM1A : M * A = A + (M - 1) * A := by
          have : M = 1 + (M - 1) := by omega
          conv_lhs => rw [this, add_mul, one_mul]
        have hle_2N := harea_lt_A (D j) (hD j) hj_ne
        rw [ha1, one_mul] at hsum_total_eq hmul_A
        rw [ha1] at hN_rounded
        rw [hsum_A] at hsum_total_eq
        omega
      have hpair_j : pair (D j) := by
        rcases hclass (D j) (hD j) with hT | hP | hle
        · exfalso; have h3N : area (D j) = 3 * N - 2 := PEqualNP.Outside.L_meta_33602_aux.areaOf_tshape hT; omega
        · exact hP
        · omega
      refine ⟨j, hpair_j, hrestA, ?_⟩
      let deg : X → ℕ := fun v =>
        ((Finset.univ : Finset (Fin M)).filter (fun i => i ≠ j ∧ hits (D i) v = 2)).card
      have hwin_const : ∀ u : X,
          (∑ k : Fin t, deg ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩) =
          (∑ k : Fin t, deg ⟨(0 + k.val) % N, Nat.mod_lt _ hN0⟩) := by
        have htot_deg : ∀ u : X,
            total D u = (N * t - 2) + (M - 1) * (N * t - 5) +
              2 * ∑ k : Fin t, deg ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ := by
          intro u
          rcases hex with ⟨h2t1, _⟩
          have hloss_j : loss (D j) u.val = N * t - 2 := by
            have hl : loss (D j) u.val +
                2 * ∑ k : Fin t, PEqualNP.Outside.L_meta_33602_aux.hitsOf (table (D j))
                  ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ =
                PEqualNP.Outside.L_meta_33602_aux.areaOf (table (D j)) + N * t :=
              PEqualNP.Outside.L_meta_33602_aux.loss_add_two_overlap htN hN0 (table (D j)) u.val
            have har : PEqualNP.Outside.L_meta_33602_aux.areaOf (table (D j)) = 2 * N :=
              PEqualNP.Outside.L_meta_33602_aux.areaOf_pair hpair_j
            have hhi : ∀ k : Fin t, PEqualNP.Outside.L_meta_33602_aux.hitsOf (table (D j))
                ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2 :=
              fun k => PEqualNP.Outside.L_meta_33602_aux.hitsOf_pair hpair_j _
            simp only [har, hhi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hl
            omega
          have htot_eq : total D u = loss (D j) u.val + ∑ i ∈ Finset.univ.erase j, loss (D i) u.val := by
            unfold total
            exact (Finset.add_sum_erase Finset.univ (fun i => loss (D i) u.val) (Finset.mem_univ j)).symm
          have hrest_loss : ∀ i ∈ Finset.univ.erase j,
              loss (D i) u.val = (N * t - 5) +
                2 * ((Finset.univ : Finset (Fin t)).filter (fun k =>
                  hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card := by
            intro i hi
            have hij : i ≠ j := (Finset.mem_erase.mp hi).1
            have hTi := harea_eq_A (D i) (hD i) (hrestA i hij)
            have hl := PEqualNP.Outside.L_meta_33602_aux.tshape_loss_formula htN h2t hN hTi u
            have h3 : N * t - 3 * (2 * t - N) - 2 = N * t - 5 := by omega
            rw [h3] at hl
            exact hl
          have hsum_deg : (∑ i ∈ Finset.univ.erase j,
              ((Finset.univ : Finset (Fin t)).filter (fun k =>
                hits (D i) ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ = 2)).card) =
              ∑ k : Fin t, deg ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ := by
            simp only [Finset.card_filter]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            simp only [deg, Finset.card_filter]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
            simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add]
            refine Finset.sum_congr rfl (fun i hi => by simp [(Finset.mem_erase.mp hi).1])
          rw [htot_eq, hloss_j, Finset.sum_congr rfl hrest_loss, Finset.sum_add_distrib,
            ← Finset.mul_sum, hsum_deg, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
            smul_eq_mul, add_assoc]
        intro u
        have h1 := htot_deg u
        have h2 := htot_deg ⟨0, hN0⟩
        rw [hall_eq u] at h1
        rw [hall_eq ⟨0, hN0⟩] at h2
        simp only at h2
        omega
      have hdeg_step_t : ∀ u : X, deg ⟨(u.val + t) % N, Nat.mod_lt _ hN0⟩ = deg u := by
        intro u
        have hu1 : (∑ k : Fin t, deg ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩) =
            (∑ k : Fin t, deg ⟨(((u.val + 1) % N) + k.val) % N, Nat.mod_lt _ hN0⟩) := by
          rw [hwin_const u, hwin_const ⟨(u.val + 1) % N, Nat.mod_lt _ hN0⟩]
        have ht_pos : 0 < t := by omega
        let tm1 := t - 1
        have htm1 : tm1 + 1 = t := by omega
        have hL : (∑ k : Fin t, deg ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩) =
            deg u + ∑ k : Fin tm1, deg ⟨(u.val + (k.val + 1)) % N, Nat.mod_lt _ hN0⟩ := by
          have h1 : (∑ k : Fin (tm1 + 1), deg ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩) =
              deg ⟨(u.val + 0) % N, Nat.mod_lt _ hN0⟩ +
              ∑ k : Fin tm1, deg ⟨(u.val + (k.val + 1)) % N, Nat.mod_lt _ hN0⟩ := by
            rw [Fin.sum_univ_succ]; rfl
          have h0 : (⟨(u.val + 0) % N, Nat.mod_lt _ hN0⟩ : Fin N) = u :=
            Fin.ext (by simp [Nat.mod_eq_of_lt u.isLt])
          rw [h0] at h1
          have hcast : (∑ k : Fin t, deg ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩) =
              ∑ k : Fin (tm1 + 1), deg ⟨(u.val + k.val) % N, Nat.mod_lt _ hN0⟩ :=
            Fintype.sum_equiv (finCongr htm1.symm) _ _ (fun _ => rfl)
          rw [hcast, h1]
        have hR : (∑ k : Fin t, deg ⟨(((u.val + 1) % N) + k.val) % N, Nat.mod_lt _ hN0⟩) =
            (∑ k : Fin tm1, deg ⟨(u.val + (k.val + 1)) % N, Nat.mod_lt _ hN0⟩) +
            deg ⟨(u.val + t) % N, Nat.mod_lt _ hN0⟩ := by
          have h1 : (∑ k : Fin (tm1 + 1), deg ⟨(((u.val + 1) % N) + k.val) % N, Nat.mod_lt _ hN0⟩) =
              (∑ k : Fin tm1, deg ⟨(((u.val + 1) % N) + k.val) % N, Nat.mod_lt _ hN0⟩) +
              deg ⟨(((u.val + 1) % N) + tm1) % N, Nat.mod_lt _ hN0⟩ := by
            rw [Fin.sum_univ_castSucc]; rfl
          have hmod_eq : ∀ m : ℕ, (((u.val + 1) % N) + m) % N = (u.val + (m + 1)) % N := by
            intro m
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            congr 1; omega
          have hcast : (∑ k : Fin t, deg ⟨(((u.val + 1) % N) + k.val) % N, Nat.mod_lt _ hN0⟩) =
              ∑ k : Fin (tm1 + 1), deg ⟨(((u.val + 1) % N) + k.val) % N, Nat.mod_lt _ hN0⟩ :=
            Fintype.sum_equiv (finCongr htm1.symm) _ _ (fun _ => rfl)
          rw [hcast, h1]
          congr 1
          · refine Finset.sum_congr rfl (fun k _ => by congr 1; exact Fin.ext (hmod_eq k.val))
          · congr 1; exact Fin.ext (by simp only; rw [hmod_eq tm1, htm1])
        rw [hL, hR] at hu1
        omega
      have hdeg_step_1 : ∀ u : X, deg ⟨(u.val + 1) % N, Nat.mod_lt _ hN0⟩ = deg u := by
        intro u
        rcases hex with ⟨h2t1, _⟩
        have h1 := hdeg_step_t u
        have h2 := hdeg_step_t ⟨(u.val + t) % N, Nat.mod_lt _ hN0⟩
        have hmod : (((u.val + t) % N) + t) % N = (u.val + 1) % N := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have e : u.val + t + t = (u.val + 1) + N := by omega
          rw [e, Nat.add_mod_right]
        have h2' : deg ⟨(u.val + 1) % N, Nat.mod_lt _ hN0⟩ = deg ⟨(u.val + t) % N, Nat.mod_lt _ hN0⟩ := by
          simpa [hmod] using h2
        exact h2'.trans h1
      have hdeg_const : ∀ v : X, deg v = deg ⟨0, hN0⟩ := by
        have hind : ∀ k : ℕ, (hk : k < N) → deg ⟨k, hk⟩ = deg ⟨0, hN0⟩ := by
          intro k
          induction k with
          | zero => intro _; rfl
          | succ k ih =>
            intro hk
            have hk' : k < N := by omega
            have hs := hdeg_step_1 ⟨k, hk'⟩
            have hmod : (k + 1) % N = k + 1 := Nat.mod_eq_of_lt hk
            have hs' : deg ⟨k + 1, hk⟩ = deg ⟨k, hk'⟩ := by simpa [hmod] using hs
            exact hs'.trans (ih hk')
        intro v
        exact hind v.val v.isLt
      have hsum_deg_all : ∑ v : X, deg v = 2 * (M - 1) := by
        simp only [deg, Finset.card_filter]
        rw [Finset.sum_comm]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, Finset.sum_const_zero, zero_add]
        have hinner : ∀ i ∈ Finset.univ.erase j,
            (∑ v : X, if i ≠ j ∧ hits (D i) v = 2 then 1 else 0) = 2 := by
          intro i hi
          have hij : i ≠ j := (Finset.mem_erase.mp hi).1
          have hTi := harea_eq_A (D i) (hD i) (hrestA i hij)
          rcases PEqualNP.Outside.L_meta_33602_aux.hitsOf_tshape hN0 hTi with ⟨v1, v2, hvne, hhi⟩
          have h1 : (∑ v : X, if i ≠ j ∧ hits (D i) v = 2 then 1 else 0) =
              ((Finset.univ : Finset X).filter (fun v => hits (D i) v = 2)).card := by
            rw [Finset.card_filter]
            refine Finset.sum_congr rfl (fun v _ => by simp [hij])
          rw [h1]
          have hset : (Finset.univ : Finset X).filter (fun v => hits (D i) v = 2) = {v1, v2} := by
            ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            change PEqualNP.Outside.L_meta_33602_aux.hitsOf _ v = 2 ↔ _
            rw [hhi]; split_ifs with h <;> simp [h]
          rw [hset, Finset.card_insert_of_notMem (by simp [hvne]), Finset.card_singleton]
        rw [Finset.sum_congr rfl hinner, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_comm]
      have hMdiv : M - 1 = (M / N) * N := by
        rcases hex with ⟨_, hMmod⟩
        have := Nat.div_add_mod M N; rw [mul_comm] at this; omega
      intro v
      have hNdeg : N * deg v = N * (2 * (M / N)) := by
        calc
          N * deg v = ∑ _w : X, deg v := by simp [X]
          _ = ∑ w : X, deg w := Finset.sum_congr rfl (fun w _ => (hdeg_const v).trans (hdeg_const w).symm)
          _ = 2 * (M - 1) := hsum_deg_all
          _ = 2 * ((M / N) * N) := by rw [hMdiv]
          _ = N * (2 * (M / N)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hN0 hNdeg

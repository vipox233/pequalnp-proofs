import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50075

open PEqualNP.CircuitLowerBounds

def vop : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.foldr (fun x y => x &&& y) 63
  | GateOp.or, l => l.foldr (fun x y => x ||| y) 0
  | GateOp.not, l => 63 ^^^ l.headD 0
  | _, _ => 0

def vstep (w : List ℕ) (g : Gate) : List ℕ := w ++ [vop g.op (g.inputs.map fun i => w.getD i 0)]

def bstep (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def els (S : ℕ) : List ℕ := (List.range 64).filter (fun a => S.testBit a) ++ [0, 63]

def binMask (S : ℕ) : ℕ :=
  (els S).foldl (fun acc a => (els S).foldl (fun acc2 b => acc2 ||| 2 ^ (a &&& (b &&& 63)) ||| 2 ^ (a ||| (b ||| 0))) (acc ||| 2 ^ (a &&& 63) ||| 2 ^ (a ||| 0))) (2 ^ 63 ||| 2 ^ 0)

def notMask (S : ℕ) : ℕ := (els S).foldl (fun acc a => acc ||| 2 ^ (63 ^^^ a)) (2 ^ (63 ^^^ 0))

def tgt (A B C S : ℕ) : Bool := S.testBit A && S.testBit B && S.testBit C

def miss (A B C S : ℕ) : ℕ := (if S.testBit A then 0 else 1) + (if S.testBit B then 0 else 1) + (if S.testBit C then 0 else 1)

def ok (A B C : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, S => tgt A B C S
  | g + 1, n, S => tgt A B C S || (decide (miss A B C S ≤ g + 1) && (List.range 64).any (fun v => !S.testBit v &&
      (((binMask S).testBit v && ok A B C g n (S ||| 2 ^ v)) ||
        (n != 0 && (notMask S).testBit v && ok A B C g (n - 1) (S ||| 2 ^ v)))))

def maskOf (w : List ℕ) : ℕ := w.foldr (fun v S => S ||| 2 ^ v) 0

theorem testBit_maskOf (w : List ℕ) (x : ℕ) : (maskOf w).testBit x = decide (x ∈ w) := by
  induction w with
  | nil => simp [maskOf]
  | cons v w ih =>
    simp only [maskOf, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, ih, Nat.testBit_two_pow]
    by_cases h : x = v
    · subst h; simp
    · simp [h, Ne.symm h]

theorem maskOf_snoc (w : List ℕ) (v : ℕ) : maskOf (w ++ [v]) = maskOf w ||| 2 ^ v := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [Nat.testBit_or, testBit_maskOf, testBit_maskOf, Nat.testBit_two_pow]
  by_cases h : x = v
  · subst h; simp
  · simp [h, Ne.symm h]

theorem foldl_or_keep {β : Type} (f : ℕ → β → ℕ) (hf : ∀ acc x, ∃ m, f acc x = acc ||| m) :
    ∀ (l : List β) (acc : ℕ) (v : ℕ), acc.testBit v = true → (l.foldl f acc).testBit v = true := by
  intro l
  induction l with
  | nil => intro acc v h; simpa using h
  | cons x l ih =>
    intro acc v h
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨m, hm⟩ := hf acc x
    rw [hm, Nat.testBit_or, h, Bool.true_or]

theorem foldl_or_mem {β : Type} (f : ℕ → β → ℕ) (hf : ∀ acc x, ∃ m, f acc x = acc ||| m) :
    ∀ (l : List β) (acc : ℕ) (x : β) (v : ℕ), x ∈ l → (∀ acc', (f acc' x).testBit v = true) →
      (l.foldl f acc).testBit v = true := by
  intro l
  induction l with
  | nil => intro acc x v hx; simp at hx
  | cons y l ih =>
    intro acc x v hx hset
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h
      exact foldl_or_keep f hf l _ v (hset acc)
    · exact ih _ x v h hset

theorem mem_els (S a : ℕ) (ha : a < 64) (hs : S.testBit a = true) : a ∈ els S := by
  unfold els
  apply List.mem_append_left
  simp [List.mem_filter, List.mem_range, ha, hs]

theorem zero_mem_els (S : ℕ) : 0 ∈ els S := by unfold els; simp

theorem top_mem_els (S : ℕ) : 63 ∈ els S := by unfold els; simp

theorem inner_shape (a : ℕ) (S : ℕ) : ∀ acc x, ∃ m, (fun acc2 b => acc2 ||| 2 ^ (a &&& (b &&& 63)) ||| 2 ^ (a ||| (b ||| 0))) acc x = acc ||| m := by
  intro acc x
  exact ⟨2 ^ (a &&& (x &&& 63)) ||| 2 ^ (a ||| (x ||| 0)), by simp [Nat.or_assoc]⟩

theorem outer_shape (S : ℕ) : ∀ acc x, ∃ m, (fun acc a => (els S).foldl (fun acc2 b => acc2 ||| 2 ^ (a &&& (b &&& 63)) ||| 2 ^ (a ||| (b ||| 0))) (acc ||| 2 ^ (a &&& 63) ||| 2 ^ (a ||| 0))) acc x = acc ||| m := by
  intro acc x
  refine ⟨(els S).foldl (fun acc2 b => acc2 ||| 2 ^ (x &&& (b &&& 63)) ||| 2 ^ (x ||| (b ||| 0))) (acc ||| 2 ^ (x &&& 63) ||| 2 ^ (x ||| 0)), ?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases h1 : acc.testBit i
  · simp
  · rw [foldl_or_keep _ (inner_shape x S) (els S) _ i (by simp [Nat.testBit_or, h1])]
    simp

theorem bin_one (S a : ℕ) (ha : a ∈ els S) :
    (binMask S).testBit (a &&& 63) = true ∧ (binMask S).testBit (a ||| 0) = true := by
  unfold binMask
  constructor
  · apply foldl_or_mem _ (outer_shape S) (els S) _ a _ ha
    intro acc'
    apply foldl_or_keep _ (inner_shape a S)
    simp [Nat.testBit_or, Nat.testBit_two_pow]
  · apply foldl_or_mem _ (outer_shape S) (els S) _ a _ ha
    intro acc'
    apply foldl_or_keep _ (inner_shape a S)
    simp [Nat.testBit_or, Nat.testBit_two_pow]

theorem bin_two (S a b : ℕ) (ha : a ∈ els S) (hb : b ∈ els S) :
    (binMask S).testBit (a &&& (b &&& 63)) = true ∧ (binMask S).testBit (a ||| (b ||| 0)) = true := by
  unfold binMask
  constructor
  · apply foldl_or_mem _ (outer_shape S) (els S) _ a _ ha
    intro acc'
    apply foldl_or_mem _ (inner_shape a S) (els S) _ b _ hb
    intro acc''
    simp [Nat.testBit_or, Nat.testBit_two_pow]
  · apply foldl_or_mem _ (outer_shape S) (els S) _ a _ ha
    intro acc'
    apply foldl_or_mem _ (inner_shape a S) (els S) _ b _ hb
    intro acc''
    simp [Nat.testBit_or, Nat.testBit_two_pow]

theorem bin_zero (S : ℕ) : (binMask S).testBit 63 = true ∧ (binMask S).testBit 0 = true := by
  unfold binMask
  constructor <;>
  · apply foldl_or_keep _ (outer_shape S)
    decide

theorem not_one (S a : ℕ) (ha : a ∈ els S) : (notMask S).testBit (63 ^^^ a) = true := by
  unfold notMask
  apply foldl_or_mem _ _ (els S) _ a _ ha
  · intro acc'
    simp [Nat.testBit_or, Nat.testBit_two_pow]
  · intro acc x
    exact ⟨_, rfl⟩

theorem ok_mono_g (A B C : ℕ) : ∀ g n S, ok A B C g n S = true → ok A B C (g + 1) n S = true := by
  intro g
  induction g with
  | zero =>
    intro n S h
    simp only [ok] at h ⊢
    simp [h]
  | succ g ih =>
    intro n S h
    rw [ok] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h | h
    · simp [h]
    · apply Bool.or_eq_true_iff.mpr; right
      rw [Bool.and_eq_true] at h ⊢
      obtain ⟨hm, h⟩ := h
      refine ⟨by simp at hm ⊢; omega, ?_⟩
      rw [List.any_eq_true] at h ⊢
      obtain ⟨v, hv, hb⟩ := h
      refine ⟨v, hv, ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hb ⊢
      rcases hb with ⟨h1, h2 | h2⟩
      · exact ⟨h1, Or.inl ⟨h2.1, ih _ _ h2.2⟩⟩
      · exact ⟨h1, Or.inr ⟨h2.1, ih _ _ h2.2⟩⟩

theorem ok_mono_n (A B C : ℕ) : ∀ g n n' S, n' ≤ n → ok A B C g n' S = true → ok A B C g n S = true := by
  intro g
  induction g with
  | zero => intro n n' S _ h; simpa [ok] using h
  | succ g ih =>
    intro n n' S hle h
    rw [ok] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h | h
    · simp [h]
    · apply Bool.or_eq_true_iff.mpr; right
      rw [Bool.and_eq_true] at h ⊢
      obtain ⟨hm, h⟩ := h
      refine ⟨hm, ?_⟩
      rw [List.any_eq_true] at h ⊢
      obtain ⟨v, hv, hb⟩ := h
      refine ⟨v, hv, ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hb ⊢
      rcases hb with ⟨h1, h2 | h2⟩
      · exact ⟨h1, Or.inl ⟨h2.1, ih _ _ _ hle h2.2⟩⟩
      · refine ⟨h1, Or.inr ⟨?_, ih _ _ _ (by omega) h2.2⟩⟩
        obtain ⟨hn', hm⟩ := h2.1
        exact ⟨by omega, hm⟩

theorem miss_step (A B C S v : ℕ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    miss A B C S ≤ miss A B C (S ||| 2 ^ v) + 1 := by
  have e : ∀ X, (S ||| 2 ^ v).testBit X = (S.testBit X || decide (v = X)) := by
    intro X; rw [Nat.testBit_or, Nat.testBit_two_pow]
  unfold miss
  rw [e A, e B, e C]
  by_cases hvA : v = A
  · subst hvA
    simp only [hAB, hAC, decide_true, decide_false, Bool.or_true, Bool.or_false, ite_true]
    split_ifs <;> omega
  · by_cases hvB : v = B
    · subst hvB
      simp only [hvA, hBC, decide_true, decide_false, Bool.or_true, Bool.or_false, ite_true]
      split_ifs <;> omega
    · by_cases hvC : v = C
      · subst hvC
        simp only [hvA, hvB, decide_true, decide_false, Bool.or_true, Bool.or_false, ite_true]
        split_ifs <;> omega
      · simp only [hvA, hvB, hvC, decide_false, Bool.or_false]
        omega

theorem ok_succ_false (A B C g n S : ℕ) (ht : tgt A B C S = false)
    (h : ∀ v < 64, S.testBit v = false →
      ((binMask S).testBit v = true → ok A B C g n (S ||| 2 ^ v) = false) ∧
      (n ≠ 0 → (notMask S).testBit v = true → ok A B C g (n - 1) (S ||| 2 ^ v) = false)) :
    ok A B C (g + 1) n S = false := by
  rw [ok, ht, Bool.false_or]
  apply Bool.eq_false_iff.mpr
  intro hc
  rw [Bool.and_eq_true, List.any_eq_true] at hc
  obtain ⟨_, v, hv, hb⟩ := hc
  have hv' := List.mem_range.mp hv
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hb
  obtain ⟨hs, hb⟩ := hb
  have hh := h v hv' hs
  rcases hb with ⟨hm, hok⟩ | ⟨⟨hn, hm⟩, hok⟩
  · rw [hh.1 hm] at hok; exact Bool.false_ne_true hok
  · rw [hh.2 hn hm] at hok; exact Bool.false_ne_true hok

theorem getD_snoc {α : Type} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem eval_bridge (t : ℕ) (ht : t < 6) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (l : List ℕ) (lb : List Bool) (hl : lb = l.map (fun a => a.testBit t)) :
    op.eval lb = (vop op l).testBit t := by
  subst hl
  have h31 : (63 : ℕ).testBit t = true := by interval_cases t <;> decide
  rcases hop with rfl | rfl | rfl
  · simp only [GateOp.eval, vop]
    induction l with
    | nil => simp [h31]
    | cons a l ih => simp [List.foldr_cons, Nat.testBit_and, ih]
  · simp only [GateOp.eval, vop]
    induction l with
    | nil => simp
    | cons a l ih => simp [List.foldr_cons, Nat.testBit_or, ih]
  · simp only [GateOp.eval, vop]
    cases l with
    | nil => simp [h31]
    | cons a l => simp [Nat.testBit_xor, h31]

theorem bridge (t : ℕ) (ht : t < 6) : ∀ (gs : List Gate) (wb : List Bool) (wn : List ℕ),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    wb.length = wn.length →
    (∀ i, wb.getD i false = (wn.getD i 0).testBit t) →
    (gs.foldl bstep wb).length = (gs.foldl vstep wn).length ∧
    ∀ i, (gs.foldl bstep wb).getD i false = ((gs.foldl vstep wn).getD i 0).testBit t := by
  intro gs
  induction gs with
  | nil => intro wb wn _ hlen h; exact ⟨hlen, h⟩
  | cons g gs ih =>
    intro wb wn hops hlen h
    simp only [List.foldl_cons]
    apply ih
    · intro g' hg'; exact hops g' (List.mem_cons_of_mem _ hg')
    · simp [bstep, vstep, hlen]
    · intro i
      have hv : g.op.eval (g.inputs.map fun i => wb.getD i false) =
          (vop g.op (g.inputs.map fun i => wn.getD i 0)).testBit t := by
        apply eval_bridge t ht g.op (hops g (List.mem_cons_self ..))
        rw [List.map_map]
        exact List.map_congr_left (fun a _ => h a)
      simp only [bstep, vstep]
      rw [getD_snoc, getD_snoc, hlen]
      split_ifs
      · exact h i
      · exact hv
      · simp

theorem vop_lt (op : GateOp) (l : List ℕ) (hl : ∀ a ∈ l, a < 64) : vop op l < 64 := by
  cases op with
  | and =>
    simp only [vop]
    induction l with
    | nil => decide
    | cons a l ih =>
      simp only [List.foldr_cons]
      exact lt_of_le_of_lt Nat.and_le_left (hl a (List.mem_cons_self ..))
  | or =>
    simp only [vop]
    induction l with
    | nil => decide
    | cons a l ih =>
      simp only [List.foldr_cons]
      have h1 := hl a (List.mem_cons_self ..)
      have h2 := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
      exact Nat.or_lt_two_pow (n := 6) h1 h2
  | not =>
    simp only [vop]
    have : l.headD 0 < 64 := by
      cases l with
      | nil => decide
      | cons a l => exact hl a (List.mem_cons_self ..)
    exact Nat.xor_lt_two_pow (n := 6) (by decide) this
  | mod m => simp [vop]
  | maj => simp [vop]

theorem fold_lt : ∀ (gs : List Gate) (w : List ℕ), (∀ v ∈ w, v < 64) → ∀ v ∈ gs.foldl vstep w, v < 64 := by
  intro gs
  induction gs with
  | nil => intro w h; simpa using h
  | cons g gs ih =>
    intro w h
    simp only [List.foldl_cons]
    apply ih
    intro v hv
    simp only [vstep, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | hv
    · exact h v hv
    · subst hv
      apply vop_lt
      intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨i, _, rfl⟩ := ha
      rw [List.getD_eq_getElem?_getD]
      cases hi : w[i]? with
      | none => simp
      | some x => simpa using h x (List.mem_of_getElem? hi)

theorem fold_len : ∀ (gs : List Gate) (w : List ℕ), (gs.foldl vstep w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp [ih, vstep]; omega

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

theorem notCount_eq (gs : List Gate) (o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs, o⟩ = (gs.filter (fun g : Gate => isNot g.op)).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g with
  | mk op ins => cases op <;> rfl

theorem miss_bound (A B C : ℕ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ∀ (gs : List Gate) (w : List ℕ), A ∈ gs.foldl vstep w → B ∈ gs.foldl vstep w → C ∈ gs.foldl vstep w →
    miss A B C (maskOf w) ≤ gs.length := by
  intro gs
  induction gs with
  | nil =>
    intro w hA hB hC
    simp only [List.foldl_nil] at hA hB hC
    simp [miss, testBit_maskOf, hA, hB, hC]
  | cons g gs ih =>
    intro w hA hB hC
    have := ih (vstep w g) hA hB hC
    simp only [vstep, maskOf_snoc] at this
    have h2 := miss_step A B C (maskOf w) (vop g.op (g.inputs.map fun i => w.getD i 0)) hAB hAC hBC
    simp only [List.length_cons]
    omega

theorem sound (A B C : ℕ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) : ∀ (gs : List Gate) (w : List ℕ) (n g : ℕ),
    (∀ g0 ∈ gs, (g0.op = GateOp.and ∨ g0.op = GateOp.or ∨ g0.op = GateOp.not) ∧ g0.inputs.length ≤ 2) →
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w.length + j) →
    (∀ v ∈ w, v < 64) →
    (gs.filter (fun g0 : Gate => isNot g0.op)).length ≤ n →
    gs.length ≤ g →
    A ∈ gs.foldl vstep w → B ∈ gs.foldl vstep w → C ∈ gs.foldl vstep w →
    ok A B C g n (maskOf w) = true := by
  intro gs
  induction gs with
  | nil =>
    intro w n g _ _ _ _ _ hA hB hC
    simp only [List.foldl_nil] at hA hB hC
    have ht : tgt A B C (maskOf w) = true := by
      simp [tgt, testBit_maskOf, hA, hB, hC]
    cases g with
    | zero => simpa [ok] using ht
    | succ g => simp [ok, ht]
  | cons g0 gs ih =>
    intro w n g hfan hrb hlt hnot hlen hA hB hC
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp at hlen; omega⟩
    obtain ⟨v, hvdef⟩ : ∃ v, v = vop g0.op (g0.inputs.map fun i => w.getD i 0) := ⟨_, rfl⟩
    have hstep : vstep w g0 = w ++ [v] := by rw [hvdef]; rfl
    have hin : ∀ i ∈ g0.inputs, i < w.length := by
      intro i hi
      have := hrb 0 (by simp) i (by simpa using hi)
      simpa using this
    have hgw : ∀ i ∈ g0.inputs, w.getD i 0 ∈ w := by
      intro i hi
      rw [List.getD_eq_getElem _ _ (hin i hi)]
      exact List.getElem_mem _
    have hval : ∀ i ∈ g0.inputs, w.getD i 0 ∈ els (maskOf w) := by
      intro i hi
      exact mem_els _ _ (hlt _ (hgw i hi)) (by rw [testBit_maskOf]; exact decide_eq_true (hgw i hi))
    have hvlt : v < 64 := by
      rw [hvdef]
      apply vop_lt
      intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact hlt _ (hgw i hi)
    have hfan0 := hfan g0 (List.mem_cons_self ..)
    have hnot' : (gs.filter (fun g1 : Gate => isNot g1.op)).length ≤
        n - (if isNot g0.op = true then 1 else 0) := by
      rw [List.filter_cons] at hnot
      cases hb : isNot g0.op <;> simp [hb] at hnot ⊢ <;> omega
    have hA' : A ∈ gs.foldl vstep (w ++ [v]) := by rw [← hstep]; simpa only [List.foldl_cons] using hA
    have hB' : B ∈ gs.foldl vstep (w ++ [v]) := by rw [← hstep]; simpa only [List.foldl_cons] using hB
    have hC' : C ∈ gs.foldl vstep (w ++ [v]) := by rw [← hstep]; simpa only [List.foldl_cons] using hC
    have IH := ih (w ++ [v]) (n - (if isNot g0.op = true then 1 else 0)) g'
      (fun g1 hg1 => hfan g1 (List.mem_cons_of_mem _ hg1))
      (by
        intro j hj i hi
        have := hrb (j + 1) (by simp; omega) i (by simpa using hi)
        simp; omega)
      (by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · exact hlt x hx
        · subst hx; exact hvlt)
      hnot' (by simp at hlen; omega) hA' hB' hC'
    rw [maskOf_snoc] at IH
    by_cases hdup : (maskOf w).testBit v = true
    · have heq : maskOf w ||| 2 ^ v = maskOf w := by
        apply Nat.eq_of_testBit_eq
        intro x
        rw [Nat.testBit_or, Nat.testBit_two_pow]
        by_cases hx : v = x
        · subst hx; simp [hdup]
        · simp [hx]
      rw [heq] at IH
      apply ok_mono_g
      exact ok_mono_n A B C g' n _ _ (Nat.sub_le _ _) IH
    · rw [ok]
      apply Bool.or_eq_true_iff.mpr; right
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · have hmb := miss_bound A B C hAB hAC hBC (g0 :: gs) w hA hB hC
        simp only [decide_eq_true_eq]
        simp at hlen hmb
        omega
      rw [List.any_eq_true]
      refine ⟨v, List.mem_range.mpr hvlt, ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
      refine ⟨by simpa using hdup, ?_⟩
      rcases hfan0 with ⟨hop | hop | hop, hlen2⟩
      · left
        refine ⟨?_, by simpa [hop, isNot] using IH⟩
        rw [hvdef, hop]
        match hm : g0.inputs, hlen2 with
        | [], _ => simp [vop, (bin_zero _).1]
        | [i], _ =>
          have := hval i (by simp [hm])
          simpa [vop] using (bin_one _ _ this).1
        | [i, j], _ =>
          have h1 := hval i (by simp [hm])
          have h2 := hval j (by simp [hm])
          simpa [vop] using (bin_two _ _ _ h1 h2).1
        | _ :: _ :: _ :: _, h => simp at h
      · left
        refine ⟨?_, by simpa [hop, isNot] using IH⟩
        rw [hvdef, hop]
        match hm : g0.inputs, hlen2 with
        | [], _ => simp [vop, (bin_zero _).2]
        | [i], _ =>
          have := hval i (by simp [hm])
          simpa [vop] using (bin_one _ _ this).2
        | [i, j], _ =>
          have h1 := hval i (by simp [hm])
          have h2 := hval j (by simp [hm])
          simpa [vop] using (bin_two _ _ _ h1 h2).2
        | _ :: _ :: _ :: _, h => simp at h
      · right
        have hb : isNot g0.op = true := by rw [hop]; rfl
        have hn : n ≠ 0 := by
          rw [List.filter_cons] at hnot
          simp [hb] at hnot; omega
        refine ⟨⟨hn, ?_⟩, by simpa [hb] using IH⟩
        rw [hvdef, hop]
        match hm : g0.inputs, hlen2 with
        | [], _ => simpa [vop] using not_one _ _ (zero_mem_els (maskOf w))
        | i :: _, _ =>
          have := hval i (by simp [hm])
          simpa [vop] using not_one _ _ this

theorem lt32_testBit (x i : ℕ) (hx : x < 64) (hi : 6 ≤ i) : x.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi))

theorem base_rel (t : Fin 6) (i : ℕ) :
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true]).getD i false =
      (([62, 60, 56, 48, 32, 0, 63] : List ℕ).getD i 0).testBit t.val := by
  fin_cases t <;> rcases i with _ | _ | _ | _ | _ | _ | _ | i <;> simp [List.ofFn_succ] <;> decide

theorem search_fails : ok 5 33 49 5 2 (maskOf [62, 60, 56, 48, 32, 0, 63]) = false := by
  decide +kernel

theorem main_neg : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (5 : Nat).testBit t.val ∧
    w.getD q.val false = (33 : Nat).testBit t.val ∧
    w.getD r.val false = (49 : Nat).testBit t.val) := by
  rintro ⟨⟨gs, o⟩, p, q, r, hfan, hrb, hnot, hsize, hall⟩
  have hfan' : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hfan g hg
    simpa [Set.mem_insert_iff] using this
  have hrb' : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < ([62, 60, 56, 48, 32, 0, 63] : List ℕ).length + j := by
    intro j hj i hi
    have := hrb j hj i hi
    simpa using this
  rw [notCount_eq] at hnot
  have hsz : gs.length ≤ 5 := hsize
  have hW : ∀ t : Fin 6, ∀ i, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ (List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true])).getD i false =
      ((gs.foldl vstep [62, 60, 56, 48, 32, 0, 63]).getD i 0).testBit t.val := by
    intro t
    exact (bridge t.val t.isLt gs _ _ (fun g hg => (hfan' g hg).1) (by simp) (base_rel t)).2
  have hlt := fold_lt gs [62, 60, 56, 48, 32, 0, 63] (by decide)
  have hlen := fold_len gs [62, 60, 56, 48, 32, 0, 63]
  have key : ∀ (k : Fin (7 + gs.length)) (T : ℕ), T < 64 →
      (∀ t : Fin 6, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ (List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true])).getD k.val false = T.testBit t.val) →
      T ∈ gs.foldl vstep [62, 60, 56, 48, 32, 0, 63] := by
    intro k T hT hk
    have hk' : k.val < (gs.foldl vstep [62, 60, 56, 48, 32, 0, 63]).length := by rw [hlen]; simpa using k.isLt
    have hmem := List.getElem_mem hk'
    have heq : (gs.foldl vstep [62, 60, 56, 48, 32, 0, 63])[k.val] = T := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 6
      · have := hk ⟨i, hi⟩
        rw [hW ⟨i, hi⟩ k.val, List.getD_eq_getElem _ _ hk'] at this
        exact this
      · rw [lt32_testBit _ i (hlt _ hmem) (by omega), lt32_testBit _ i hT (by omega)]
    rw [← heq]; exact hmem
  have hA := key p 5 (by decide) (fun t => by have h := hall t; simp only at h; exact h.1)
  have hB := key q 33 (by decide) (fun t => by have h := hall t; simp only at h; exact h.2.1)
  have hC := key r 49 (by decide) (fun t => by have h := hall t; simp only at h; exact h.2.2)
  have hok := sound 5 33 49 (by decide) (by decide) (by decide) gs [62, 60, 56, 48, 32, 0, 63] 2 5 hfan' hrb' (by decide) hnot hsz hA hB hC
  rw [search_fails] at hok
  exact Bool.false_ne_true hok

end PEqualNP.Outside.L_meta_50075

theorem PEqualNP.Outside.L_meta_50075 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (5 : Nat).testBit t.val ∧
    w.getD q.val false = (33 : Nat).testBit t.val ∧
    w.getD r.val false = (49 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_50075.main_neg

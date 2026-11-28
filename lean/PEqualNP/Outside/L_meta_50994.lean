import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50994_aux

open PEqualNP.CircuitLowerBounds

def TT : ℕ := 6
def FULL : ℕ := 2 ^ TT - 1
def U : ℕ := 2 ^ TT
def tgts : List ℕ := [20, 22, 54]
def c0 : List ℕ := [62, 60, 56, 48, 32, 0, 63]
def X (t : Fin 6) : List Bool := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]

def colEval : GateOp → List ℕ → ℕ
  | .and, L => L.foldr (· &&& ·) FULL
  | .or, L => L.foldr (· ||| ·) 0
  | .not, L => FULL ^^^ L.headD 0
  | _, _ => 0

def colStep (c : List ℕ) (g : Gate) : List ℕ := c ++ [colEval g.op (g.inputs.map fun i => c.getD i 0)]

def wStep (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def maskOf (l : List ℕ) : ℕ := l.foldl (fun m v => m ||| 2 ^ v) 0

def opsOf (S : ℕ) : List ℕ := (List.range U).filter fun v => S.testBit v

def pairsAO (os : List ℕ) : List ℕ := os.flatMap fun a => (os.filter fun b => decide (a ≤ b)).flatMap fun b => [a &&& b, a ||| b]

def succAO (S : ℕ) : ℕ := maskOf (pairsAO (opsOf S)) ||| 2 ^ FULL ||| 2 ^ 0

def succN (S : ℕ) : ℕ := maskOf ((opsOf S).map fun a => FULL ^^^ a) ||| 2 ^ FULL

def miss (S : ℕ) : List ℕ := tgts.filter fun m => !S.testBit m

def bad (g : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun S _ => !(miss S).isEmpty)
    (fun g ih S k => !(miss S).isEmpty && (decide (g + 1 < (miss S).length) ||
      ((List.range U).all (fun v => !(succAO S).testBit v || S.testBit v || ih (S ||| 2 ^ v) k) &&
       (k == 0 || (List.range U).all (fun v => !(succN S).testBit v || S.testBit v || ih (S ||| 2 ^ v) (k - 1)))))) g

theorem bad_zero (S k : ℕ) : bad 0 S k = !(miss S).isEmpty := rfl

theorem bad_succ (g S k : ℕ) : bad (g + 1) S k = (!(miss S).isEmpty && (decide (g + 1 < (miss S).length) ||
      ((List.range U).all (fun v => !(succAO S).testBit v || S.testBit v || bad g (S ||| 2 ^ v) k) &&
       (k == 0 || (List.range U).all (fun v => !(succN S).testBit v || S.testBit v || bad g (S ||| 2 ^ v) (k - 1)))))) := rfl

theorem bad_nonempty (g S k : ℕ) (h : bad g S k = true) : (miss S).isEmpty = false := by
  cases g with
  | zero => rw [bad_zero] at h; simpa using h
  | succ g => rw [bad_succ] at h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.1

theorem monoK : ∀ (g S k : ℕ), bad g S (k + 1) = true → bad g S k = true := by
  intro g
  induction g with
  | zero => intro S k h; exact h
  | succ g ih =>
    intro S k h
    rw [bad_succ] at h ⊢
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
      beq_iff_eq] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with h2 | ⟨hA, hB⟩
    · exact Or.inl h2
    · refine Or.inr ⟨fun v hv => ?_, ?_⟩
      · rcases hA v hv with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (ih _ _ h3)
      · rcases k with _ | k
        · exact Or.inl rfl
        · right
          intro v hv
          rcases hB.resolve_left (by omega) v hv with h3 | h3
          · exact Or.inl h3
          · exact Or.inr (ih _ _ (by simpa using h3))

theorem monoG : ∀ (g S k : ℕ), bad (g + 1) S k = true → bad g S k = true := by
  intro g
  induction g with
  | zero => intro S k h; rw [bad_zero]; have := bad_nonempty _ _ _ h; simp [this]
  | succ g ih =>
    intro S k h
    rw [bad_succ] at h ⊢
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
      beq_iff_eq] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with h2 | ⟨hA, hB⟩
    · exact Or.inl (by omega)
    · refine Or.inr ⟨fun v hv => ?_, ?_⟩
      · rcases hA v hv with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (ih _ _ h3)
      · rcases hB with hB | hB
        · exact Or.inl hB
        · right
          intro v hv
          rcases hB v hv with h3 | h3
          · exact Or.inl h3
          · exact Or.inr (ih _ _ h3)

theorem maskOf_aux (l : List ℕ) : ∀ (m v : ℕ),
    (l.foldl (fun m v => m ||| 2 ^ v) m).testBit v = (m.testBit v || decide (v ∈ l)) := by
  induction l with
  | nil => intro m v; simp
  | cons a l ih =>
    intro m v
    rw [List.foldl_cons, ih]
    simp only [Nat.testBit_or, Nat.testBit_two_pow, List.mem_cons]
    by_cases h : v = a
    · subst h; simp
    · simp [h, Ne.symm h]

theorem maskOf_spec (l : List ℕ) (v : ℕ) : (maskOf l).testBit v = true ↔ v ∈ l := by
  unfold maskOf; rw [maskOf_aux]; simp

theorem getD_snoc {α : Type} (l : List α) (b d : α) (i : ℕ) :
    (l ++ [b]).getD i d = if i < l.length then l.getD i d else if i = l.length then b else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

def OpOk (x : Gate) : Prop := x.op = .and ∨ x.op = .or ∨ x.op = .not

theorem full_bit (t : ℕ) (ht : t < TT) : FULL.testBit t = true := by
  unfold FULL; rw [Nat.testBit_two_pow_sub_one]; simpa using ht

theorem colEval_bit (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not) (t : ℕ) (ht : t < TT)
    (L : List ℕ) (f : ℕ → Bool) (h : ℕ → ℕ) (hfh : ∀ i, f i = (h i).testBit t) :
    op.eval (L.map f) = (colEval op (L.map h)).testBit t := by
  rcases hop with rfl | rfl | rfl
  · induction L with
    | nil => simp [GateOp.eval, colEval, full_bit t ht]
    | cons a L ih =>
      simp only [GateOp.eval, colEval, List.map_cons, List.all_cons, List.foldr_cons, Nat.testBit_and, id] at ih ⊢
      rw [ih, hfh]
  · induction L with
    | nil => simp [GateOp.eval, colEval]
    | cons a L ih =>
      simp only [GateOp.eval, colEval, List.map_cons, List.any_cons, List.foldr_cons, Nat.testBit_or, id] at ih ⊢
      rw [ih, hfh]
  · cases L with
    | nil => simp [GateOp.eval, colEval, full_bit t ht]
    | cons a L => simp [GateOp.eval, colEval, Nat.testBit_xor, full_bit t ht, hfh]

theorem colEval_lt (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not) (L : List ℕ)
    (hL : ∀ a ∈ L, a < U) : colEval op L < U := by
  have hF : FULL < U := by decide
  rcases hop with rfl | rfl | rfl
  · simp only [colEval]
    induction L with
    | nil => exact hF
    | cons a L ih => exact lt_of_le_of_lt Nat.and_le_right (ih (fun b hb => hL b (by simp [hb])))
  · simp only [colEval]
    induction L with
    | nil => decide
    | cons a L ih =>
      exact Nat.or_lt_two_pow (hL a (by simp)) (ih (fun b hb => hL b (by simp [hb])))
  · simp only [colEval]
    have : L.headD 0 < U := by
      cases L with
      | nil => decide
      | cons a L => exact hL a (by simp)
    exact Nat.xor_lt_two_pow hF this

theorem sem (gs : List Gate) : ∀ (ws : Fin 6 → List Bool) (c : List ℕ), (∀ x ∈ gs, OpOk x) →
    (∀ t, (ws t).length = c.length) → (∀ t i, (ws t).getD i false = (c.getD i 0).testBit t.val) →
    ∀ t i, (gs.foldl wStep (ws t)).getD i false = ((gs.foldl colStep c).getD i 0).testBit t.val := by
  induction gs with
  | nil => intro ws c _ _ h; exact h
  | cons x gs ih =>
    intro ws c hok hlen hrel
    simp only [List.foldl_cons]
    refine ih (fun t => wStep (ws t) x) (colStep c x) (fun y hy => hok y (by simp [hy])) ?_ ?_
    · intro t; simp [wStep, colStep, hlen t]
    · intro t i
      simp only [wStep, colStep, getD_snoc, hlen t]
      split_ifs with h1 h2
      · exact hrel t i
      · exact colEval_bit x.op (hok x (by simp)) t.val (by have := t.isLt; unfold TT; omega) x.inputs _ _
          (fun i => hrel t i)
      · simp

theorem len_col (gs : List Gate) : ∀ c : List ℕ, (gs.foldl colStep c).length = c.length + gs.length := by
  induction gs with
  | nil => intro c; simp
  | cons x gs ih => intro c; rw [List.foldl_cons, ih]; simp [colStep]; omega

theorem ext_col (gs : List Gate) : ∀ c : List ℕ, ∃ e, gs.foldl colStep c = c ++ e ∧ e.length = gs.length := by
  induction gs with
  | nil => intro c; exact ⟨[], by simp, rfl⟩
  | cons x gs ih =>
    intro c
    obtain ⟨e, he, hl⟩ := ih (colStep c x)
    refine ⟨colEval x.op (x.inputs.map fun i => c.getD i 0) :: e, ?_, by simp [hl]⟩
    rw [List.foldl_cons, he]; simp [colStep]

theorem bound_col (gs : List Gate) : ∀ c : List ℕ, (∀ x ∈ gs, OpOk x) → (∀ v ∈ c, v < U) →
    ∀ v ∈ gs.foldl colStep c, v < U := by
  induction gs with
  | nil => intro c _ h; exact h
  | cons x gs ih =>
    intro c hok hc
    rw [List.foldl_cons]
    refine ih _ (fun y hy => hok y (by simp [hy])) ?_
    intro v hv
    simp only [colStep, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hc v hv
    · apply colEval_lt x.op (hok x (by simp))
      intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨i, _, rfl⟩ := ha
      by_cases hi : i < c.length
      · rw [List.getD_eq_getElem _ _ hi]; exact hc _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; decide

theorem and_full (a : ℕ) (ha : a < U) : a &&& FULL = a := by
  unfold FULL; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt ha

theorem opsOf_mem {S a : ℕ} (h : a ∈ opsOf S) : a < U ∧ S.testBit a = true := by
  simpa [opsOf] using h

theorem succAO_spec (S : ℕ) (op : GateOp) (hop : op = .and ∨ op = .or) (L : List ℕ)
    (hL : ∀ a ∈ L, a ∈ opsOf S) (hl : L.length ≤ 2) (hv : S.testBit (colEval op L) = false) :
    (succAO S).testBit (colEval op L) = true := by
  have bit : ∀ w, (succAO S).testBit w = true ↔ (w ∈ pairsAO (opsOf S) ∨ FULL = w) ∨ 0 = w := by
    intro w
    simp only [succAO, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, maskOf_spec]
  rw [bit]
  match L, hl, hL with
  | [], _, _ => rcases hop with rfl | rfl <;> simp [colEval]
  | [a], _, h =>
    exfalso
    have ha := opsOf_mem (h a (by simp))
    rcases hop with rfl | rfl <;> simp [colEval, and_full a ha.1, ha.2] at hv
  | [a, b], _, h =>
    left; left
    have ha := h a (by simp)
    have hb := h b (by simp)
    simp only [pairsAO, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    rcases le_total a b with hab | hab
    · refine ⟨a, ha, b, ⟨hb, hab⟩, ?_⟩
      rcases hop with rfl | rfl <;> simp [colEval, and_full b (opsOf_mem hb).1]
    · refine ⟨b, hb, a, ⟨ha, hab⟩, ?_⟩
      rcases hop with rfl | rfl <;> simp [colEval, and_full b (opsOf_mem hb).1, Nat.land_comm, Nat.lor_comm]
  | _ :: _ :: _ :: _, hl, _ => simp at hl

theorem succN_spec (S : ℕ) (L : List ℕ) (hL : ∀ a ∈ L, a ∈ opsOf S) :
    (succN S).testBit (colEval .not L) = true := by
  simp only [succN, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, maskOf_spec,
    decide_eq_true_eq, List.mem_map]
  cases L with
  | nil => right; simp [colEval]
  | cons a L => left; exact ⟨a, hL a (by simp), by simp [colEval]⟩

theorem tgts_nodup : tgts.Nodup := by decide

theorem sound (gs : List Gate) : ∀ (c : List ℕ) (S g k : ℕ),
    (∀ v, S.testBit v = true ↔ v ∈ c) → (∀ v ∈ c, v < U) →
    (∀ x ∈ gs, OpOk x ∧ x.inputs.length ≤ 2) →
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < c.length + j) →
    gs.length ≤ g → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ k →
    bad g S k = true → ∃ m ∈ tgts, m ∉ gs.foldl colStep c := by
  induction gs with
  | nil =>
    intro c S g k hS _ _ _ _ _ hb
    have h := bad_nonempty g S k hb
    rw [List.isEmpty_eq_false_iff_exists_mem] at h
    obtain ⟨m, hm⟩ := h
    simp only [miss, List.mem_filter, Bool.not_eq_true'] at hm
    refine ⟨m, hm.1, fun hc => ?_⟩
    have := (hS m).2 hc
    simp [hm.2] at this
  | cons x gs ih =>
    intro c S g k hS hc hok hR hg hk hb
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp at hg; omega⟩
    by_contra hcon
    push Not at hcon
    have hb0 := hb
    rw [bad_succ] at hb
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
      beq_iff_eq] at hb
    obtain ⟨e, he, hel⟩ := ext_col (x :: gs) c
    rcases hb.2 with hpr | ⟨hA, hB⟩
    ·
      have hsub : miss S ⊆ e := by
        intro m hm
        simp only [miss, List.mem_filter, Bool.not_eq_true'] at hm
        have h1 := hcon m hm.1
        rw [he, List.mem_append] at h1
        rcases h1 with h1 | h1
        · have := (hS m).2 h1; simp [hm.2] at this
        · exact h1
      have hle := (List.subperm_of_subset (tgts_nodup.filter _) hsub).length_le
      simp only [List.length_cons] at hel hg
      unfold miss at hpr
      omega
    · have hx := hok x (by simp)
      have hin : ∀ i ∈ x.inputs, i < c.length := by
        intro i hi; have := hR 0 (by simp) i (by simpa using hi); simpa using this
      set L := x.inputs.map fun i => c.getD i 0 with hLdef
      have hLops : ∀ a ∈ L, a ∈ opsOf S := by
        intro a ha
        rw [hLdef, List.mem_map] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        have hi' := hin i hi
        rw [List.getD_eq_getElem _ _ hi']
        simp only [opsOf, List.mem_filter, List.mem_range]
        exact ⟨hc _ (List.getElem_mem hi'), (hS _).2 (List.getElem_mem hi')⟩
      have hlenL : L.length ≤ 2 := by rw [hLdef, List.length_map]; exact hx.2
      set v := colEval x.op L with hvdef
      have hvU : v < U := colEval_lt x.op hx.1 L (fun a ha => by
        have := hLops a ha; simp only [opsOf, List.mem_filter, List.mem_range] at this; exact this.1)
      have hvr : v ∈ List.range U := List.mem_range.2 hvU
      have hfold : (x :: gs).foldl colStep c = gs.foldl colStep (c ++ [v]) := rfl
      have hc' : ∀ w ∈ c ++ [v], w < U := by
        intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact hc w hw
        · exact hvU
      have hok' : ∀ y ∈ gs, OpOk y ∧ y.inputs.length ≤ 2 := fun y hy => hok y (by simp [hy])
      have hR' : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < (c ++ [v]).length + j := by
        intro j hj i hi
        have := hR (j + 1) (by simp; omega) i (by simpa using hi)
        simp; omega
      have hg' : gs.length ≤ g := by simp at hg; omega

      have hS_new : ∀ w, (S ||| 2 ^ v).testBit w = true ↔ w ∈ c ++ [v] := by
        intro w
        simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
          List.mem_append, List.mem_singleton, hS]
        constructor <;> rintro (h | h) <;> first | exact Or.inl h | exact Or.inr h.symm
      have hS_old : S.testBit v = true → ∀ w, S.testBit w = true ↔ w ∈ c ++ [v] := by
        intro hv w
        simp only [List.mem_append, List.mem_singleton, hS]
        constructor
        · exact Or.inl
        · rintro (h | rfl)
          · exact h
          · exact (hS _).1 hv
      have fin : ∀ S' k', (∀ w, S'.testBit w = true ↔ w ∈ c ++ [v]) →
          PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ k' → bad g S' k' = true → False := by
        intro S' k' h1 h2 h3
        obtain ⟨m, hm, hnm⟩ := ih (c ++ [v]) S' g k' h1 hc' hok' hR' hg' h2 h3
        exact hnm (hfold ▸ hcon m hm)
      have hkk : ∀ k', PEqualNP.NotBracket.notCount ⟨x :: gs, 0⟩ ≤ k' → x.op ≠ .not →
          PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ k' := by
        intro k' h hn; simpa [PEqualNP.NotBracket.notCount, List.filter_cons, hn] using h
      have hkn : x.op = .not → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + 1 ≤ k := by
        intro hn; simpa [PEqualNP.NotBracket.notCount, List.filter_cons, hn] using hk
      by_cases hvS : S.testBit v = true
      · rcases hx.1 with hop | hop | hop
        · exact fin S k (hS_old hvS) (hkk k hk (by rw [hop]; intro h; cases h)) (monoG _ _ _ hb0)
        · exact fin S k (hS_old hvS) (hkk k hk (by rw [hop]; intro h; cases h)) (monoG _ _ _ hb0)
        · have hk1 := hkn hop
          obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          exact fin S k (hS_old hvS) (by omega) (monoK _ _ _ (monoG _ _ _ hb0))
      · have hvF : S.testBit v = false := by simpa using hvS
        rcases hx.1 with hop | hop | hop
        · have hm : (succAO S).testBit v = true := succAO_spec S x.op (Or.inl hop) L hLops hlenL hvF
          rcases hA v hvr with (h | h) | h
          · simp [hm] at h
          · simp [hvF] at h
          · exact fin _ k hS_new (hkk k hk (by rw [hop]; intro h; cases h)) h
        · have hm : (succAO S).testBit v = true := succAO_spec S x.op (Or.inr hop) L hLops hlenL hvF
          rcases hA v hvr with (h | h) | h
          · simp [hm] at h
          · simp [hvF] at h
          · exact fin _ k hS_new (hkk k hk (by rw [hop]; intro h; cases h)) h
        · have hk1 := hkn hop
          obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hm : (succN S).testBit v = true := by rw [hvdef, hop]; exact succN_spec S L hLops
          have hB' := hB.resolve_left (by omega)
          rcases hB' v hvr with (h | h) | h
          · simp [hm] at h
          · simp [hvF] at h
          · exact fin _ k hS_new (by omega) (by simpa using h)

theorem X_len (t : Fin 6) : (X t).length = c0.length := by simp [X, c0]

theorem X_rel : ∀ (t : Fin 6) (i : ℕ), (X t).getD i false = (c0.getD i 0).testBit t.val := by
  have key : ∀ (t : Fin 6) (i : Fin 7), (X t).getD i.val false = (c0.getD i.val 0).testBit t.val := by
    decide
  intro t i
  by_cases hi : i < 7
  · exact key t ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by rw [X_len]; simp [c0]; omega),
      List.getD_eq_default _ _ (by simp [c0]; omega)]
    simp

theorem check : bad 5 (maskOf c0) 2 = true := by decide +kernel

theorem final (D : Circuit) (hF : PEqualNP.MetaComplexity.FanInTwo D)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D) (hN : PEqualNP.NotBracket.notCount D ≤ 2)
    (hS : D.size ≤ 5)
    (hcov : ∀ m ∈ tgts, ∃ i < 7 + D.size, ∀ t : Fin 6, (D.wires (X t)).getD i false = m.testBit t.val) :
    False := by
  have hok : ∀ x ∈ D.gates, OpOk x ∧ x.inputs.length ≤ 2 := by
    intro x hx
    have := hF x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    exact this
  have hc0 : ∀ v ∈ c0, v < U := by decide
  obtain ⟨m, hm, hnm⟩ := sound D.gates c0 (maskOf c0) 5 2 (maskOf_spec c0) hc0 hok
    (fun j hj i hi => hR j hj i hi) hS hN check
  obtain ⟨i, hi, hw⟩ := hcov m hm
  apply hnm
  have hlen : i < (D.gates.foldl colStep c0).length := by
    rw [len_col]; simpa [c0, Circuit.size] using hi
  have hsem := sem D.gates X c0 (fun x hx => (hok x hx).1) X_len X_rel
  have hmU : m < U := (show ∀ m ∈ tgts, m < U by decide) m hm
  have hval : (D.gates.foldl colStep c0).getD i 0 = m := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 6
    · have := hw ⟨j, hj⟩
      rw [← this]
      exact (hsem ⟨j, hj⟩ i).symm
    · have hb := bound_col D.gates c0 (fun x hx => (hok x hx).1) hc0 ((D.gates.foldl colStep c0).getD i 0)
        (by rw [List.getD_eq_getElem _ _ hlen]; exact List.getElem_mem hlen)
      have hp : U ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by unfold TT; omega)
      rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]
  rw [← hval, List.getD_eq_getElem _ _ hlen]
  exact List.getElem_mem hlen

end PEqualNP.Outside.L_meta_50994_aux

theorem PEqualNP.Outside.L_meta_50994 :
    (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
       PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
       PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
       ∀ t : Fin 6,
         let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
         let w := D.wires xs
         w.getD p.val false = (20 : Nat).testBit t.val ∧
         w.getD q.val false = (22 : Nat).testBit t.val ∧
         w.getD r.val false = (54 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hF, hR, hN0, hS0, hall⟩
  have hN : PEqualNP.NotBracket.notCount D ≤ 2 := by omega
  have hS : D.size ≤ 5 := by omega
  apply PEqualNP.Outside.L_meta_50994_aux.final D hF hR hN hS
  intro m hm
  simp only [PEqualNP.Outside.L_meta_50994_aux.tgts, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact ⟨p.val, p.isLt, fun t => (hall t).1⟩
  · exact ⟨q.val, q.isLt, fun t => (hall t).2.1⟩
  · exact ⟨r.val, r.isLt, fun t => (hall t).2.2⟩

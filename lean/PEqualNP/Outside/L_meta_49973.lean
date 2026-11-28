import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49973

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def mk5 (a b c d e : Bool) : ℕ := a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat

lemma mk5_lt : ∀ a b c d e : Bool, mk5 a b c d e < 32 := by decide

lemma mk5_and : ∀ a b c d e a' b' c' d' e' : Bool,
    mk5 (a && a') (b && b') (c && c') (d && d') (e && e') = mk5 a b c d e &&& mk5 a' b' c' d' e' := by
  decide

lemma mk5_or : ∀ a b c d e a' b' c' d' e' : Bool,
    mk5 (a || a') (b || b') (c || c') (d || d') (e || e') = mk5 a b c d e ||| mk5 a' b' c' d' e' := by
  decide

lemma mk5_not : ∀ a b c d e : Bool, mk5 (!a) (!b) (!c) (!d) (!e) = 31 ^^^ mk5 a b c d e := by decide

def col (W : Fin 5 → List Bool) (i : ℕ) : ℕ :=
  mk5 ((W 0).getD i false) ((W 1).getD i false) ((W 2).getD i false) ((W 3).getD i false)
    ((W 4).getD i false)

def tg (S : List ℕ) : Bool := decide (10 ∈ S ∧ 12 ∈ S ∧ 14 ∈ S)

def bin (S : List ℕ) (m : ℕ) : Bool :=
  S.any fun a => S.any fun b => decide (a &&& b = m) || decide (a ||| b = m)

def neg (S : List ℕ) (m : ℕ) : Bool := S.any fun a => decide (31 ^^^ a = m)

def search : ℕ → List ℕ → ℕ → Bool
  | 0, S, _ => tg S
  | f + 1, S, k => tg S || (List.range 32).any fun m =>
      !decide (m ∈ S) && ((bin S m && search f (m :: S) k) ||
        (decide (k < 2) && neg S m && search f (m :: S) (k + 1)))

lemma tg_of_search (f : ℕ) (S : List ℕ) (k : ℕ) (h : search f S k = false) : tg S = false := by
  cases f with
  | zero => exact h
  | succ f =>
    unfold search at h
    exact (Bool.or_eq_false_iff.mp h).1

lemma search_succ (f : ℕ) (S : List ℕ) (k : ℕ) (h : search (f + 1) S k = false) (m : ℕ) (hm : m < 32)
    (hS : m ∉ S) :
    (bin S m = true → search f (m :: S) k = false) ∧
      (k < 2 → neg S m = true → search f (m :: S) (k + 1) = false) := by
  unfold search at h
  have h2 := (Bool.or_eq_false_iff.mp h).2
  rw [List.any_eq_false] at h2
  have h3 := h2 m (List.mem_range.mpr hm)
  constructor
  · intro hb
    by_contra hc
    have hc' : search f (m :: S) k = true := by simpa using hc
    apply h3
    simp [hS, hb, hc']
  · intro hk hn
    by_contra hc
    have hc' : search f (m :: S) (k + 1) = true := by simpa using hc
    apply h3
    simp [hS, hk, hn, hc']

lemma search_fuel : ∀ (f : ℕ) (S : List ℕ) (k : ℕ), search (f + 1) S k = false → search f S k = false := by
  intro f
  induction f with
  | zero =>
    intro S k h
    exact tg_of_search 1 S k h
  | succ f ih =>
    intro S k h
    have ht := tg_of_search _ S k h
    unfold search
    rw [ht, Bool.false_or, List.any_eq_false]
    intro m hm
    have hm' := List.mem_range.mp hm
    by_cases hS : m ∈ S
    · simp [hS]
    · have h1 := search_succ (f + 1) S k h m hm' hS
      have e1 : (bin S m && search f (m :: S) k) = false := by
        by_cases hb : bin S m = true
        · rw [ih _ _ (h1.1 hb), Bool.and_false]
        · rw [Bool.not_eq_true] at hb
          rw [hb, Bool.false_and]
      have e2 : (decide (k < 2) && neg S m && search f (m :: S) (k + 1)) = false := by
        by_cases hk : k < 2
        · by_cases hn : neg S m = true
          · rw [ih _ _ (h1.2 hk hn), Bool.and_false]
          · rw [Bool.not_eq_true] at hn
            rw [hn, Bool.and_false, Bool.false_and]
        · simp [hk]
      rw [e1, e2]
      simp

lemma search_k : ∀ (f : ℕ) (S : List ℕ) (k : ℕ), search f S k = false → search f S (k + 1) = false := by
  intro f
  induction f with
  | zero =>
    intro S k h
    exact h
  | succ f ih =>
    intro S k h
    have ht := tg_of_search _ S k h
    unfold search
    rw [ht, Bool.false_or, List.any_eq_false]
    intro m hm
    have hm' := List.mem_range.mp hm
    by_cases hS : m ∈ S
    · simp [hS]
    · have h1 := search_succ f S k h m hm' hS
      have e1 : (bin S m && search f (m :: S) (k + 1)) = false := by
        by_cases hb : bin S m = true
        · rw [ih _ _ (h1.1 hb), Bool.and_false]
        · rw [Bool.not_eq_true] at hb
          rw [hb, Bool.false_and]
      have e2 : (decide (k + 1 < 2) && neg S m && search f (m :: S) (k + 1 + 1)) = false := by
        by_cases hk : k + 1 < 2
        · by_cases hn : neg S m = true
          · rw [ih _ _ (h1.2 (by omega) hn), Bool.and_false]
          · rw [Bool.not_eq_true] at hn
            rw [hn, Bool.and_false, Bool.false_and]
        · simp [hk]
      rw [e1, e2]
      simp

def stepf (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def nots (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

lemma nots_pos (g : Gate) (gs : List Gate) (h : g.op = GateOp.not) : nots (g :: gs) = nots gs + 1 := by
  simp [nots, PEqualNP.NotBracket.notCount, h]

lemma nots_neg (g : Gate) (gs : List Gate) (h : g.op ≠ GateOp.not) : nots (g :: gs) = nots gs := by
  simp [nots, PEqualNP.NotBracket.notCount, h]

lemma getD_last (w : List Bool) (x : Bool) (L : ℕ) (h : w.length = L) : (w ++ [x]).getD L false = x := by
  subst h
  simp

lemma getD_init (w : List Bool) (x : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [x]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma col_last (W : Fin 5 → List Bool) (v : Fin 5 → Bool) (L : ℕ) (hL : ∀ t, (W t).length = L) :
    col (fun t => W t ++ [v t]) L = mk5 (v 0) (v 1) (v 2) (v 3) (v 4) := by
  unfold col
  simp only [getD_last _ _ L (hL _)]

lemma col_init (W : Fin 5 → List Bool) (v : Fin 5 → Bool) (L i : ℕ) (hL : ∀ t, (W t).length = L)
    (hi : i < L) : col (fun t => W t ++ [v t]) i = col W i := by
  have e : ∀ t, (W t ++ [v t]).getD i false = (W t).getD i false :=
    fun t => getD_init _ _ i (by rw [hL t]; exact hi)
  unfold col
  simp only [e]

lemma newmask (W : Fin 5 → List Bool) (L : ℕ) (S : List ℕ) (g : Gate)
    (hinv : ∀ i, i < L → col W i ∈ S) (h0 : 0 ∈ S) (h31 : 31 ∈ S)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hlen : g.inputs.length ≤ 2)
    (hrd : ∀ i ∈ g.inputs, i < L) :
    mk5 (g.op.eval (g.inputs.map fun i => (W 0).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 1).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 2).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 3).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 4).getD i false)) ∈ S ∨
    (g.op ≠ GateOp.not ∧ bin S (mk5 (g.op.eval (g.inputs.map fun i => (W 0).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 1).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 2).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 3).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 4).getD i false))) = true) ∨
    (g.op = GateOp.not ∧ neg S (mk5 (g.op.eval (g.inputs.map fun i => (W 0).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 1).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 2).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 3).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 4).getD i false))) = true) := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop hlen hrd ⊢
  match inputs, hlen, hrd with
  | [], _, _ =>
    rcases hop with rfl | rfl | rfl
    · left
      simpa [GateOp.eval, mk5] using h31
    · left
      simpa [GateOp.eval, mk5] using h0
    · left
      simpa [GateOp.eval, mk5] using h31
  | [a], _, hrd =>
    have ha : a < L := hrd a (by simp)
    rcases hop with rfl | rfl | rfl
    · left
      simpa [GateOp.eval, col] using hinv a ha
    · left
      simpa [GateOp.eval, col] using hinv a ha
    · right
      right
      refine ⟨rfl, ?_⟩
      unfold neg
      rw [List.any_eq_true]
      refine ⟨col W a, hinv a ha, ?_⟩
      simp [GateOp.eval, col, mk5_not]
  | [a, b], _, hrd =>
    have ha : a < L := hrd a (by simp)
    have hb : b < L := hrd b (by simp)
    rcases hop with rfl | rfl | rfl
    · right
      left
      refine ⟨by simp, ?_⟩
      unfold bin
      rw [List.any_eq_true]
      refine ⟨col W a, hinv a ha, ?_⟩
      rw [List.any_eq_true]
      refine ⟨col W b, hinv b hb, ?_⟩
      simp [GateOp.eval, col, mk5_and]
    · right
      left
      refine ⟨by simp, ?_⟩
      unfold bin
      rw [List.any_eq_true]
      refine ⟨col W a, hinv a ha, ?_⟩
      rw [List.any_eq_true]
      refine ⟨col W b, hinv b hb, ?_⟩
      simp [GateOp.eval, col, mk5_or]
    · right
      right
      refine ⟨rfl, ?_⟩
      unfold neg
      rw [List.any_eq_true]
      refine ⟨col W a, hinv a ha, ?_⟩
      simp [GateOp.eval, col, mk5_not]
  | _ :: _ :: _ :: _, hlen, _ =>
    simp at hlen

theorem main : ∀ (gs : List Gate) (f : ℕ) (W : Fin 5 → List Bool) (L : ℕ) (S : List ℕ) (k : ℕ),
    gs.length ≤ f → (∀ t, (W t).length = L) → (∀ i, i < L → col W i ∈ S) → 0 ∈ S → 31 ∈ S →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < L + j) →
    nots gs + k ≤ 2 → search f S k = false →
    ∃ S' : List ℕ, (∀ i, i < L + gs.length → col (fun t => gs.foldl stepf (W t)) i ∈ S') ∧
      tg S' = false := by
  intro gs
  induction gs with
  | nil =>
    intro f W L S k _ _ hinv _ _ _ _ _ hs
    exact ⟨S, fun i hi => hinv i (by simpa using hi), tg_of_search f S k hs⟩
  | cons g gs ih =>
    intro f W L S k hf hL hinv h0 h31 hg hrd hn hs
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hg0 := hg g (by simp)
    have hrd0 : ∀ i ∈ g.inputs, i < L := by
      intro i hi
      have := hrd 0 (by simp) i (by simpa using hi)
      simpa using this
    have hcase := newmask W L S g hinv h0 h31 hg0.1 hg0.2 hrd0
    have hW1 : ∀ t, (W t ++ [g.op.eval (g.inputs.map fun i => (W t).getD i false)]).length = L + 1 := by
      intro t
      simp [hL t]
    have hfold : (fun t => (g :: gs).foldl stepf (W t)) =
        fun t => gs.foldl stepf (W t ++ [g.op.eval (g.inputs.map fun i => (W t).getD i false)]) := by
      funext t
      rfl
    have hcl := col_last W (fun t => g.op.eval (g.inputs.map fun i => (W t).getD i false)) L hL
    have hci := fun i hi =>
      col_init W (fun t => g.op.eval (g.inputs.map fun i => (W t).getD i false)) L i hL hi
    have hmlt := mk5_lt (g.op.eval (g.inputs.map fun i => (W 0).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 1).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 2).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 3).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 4).getD i false))
    have hgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧
        g'.inputs.length ≤ 2 := fun g' h' => hg g' (List.mem_cons_of_mem g h')
    have hrds : ∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < L + 1 + j := by
      intro j hj i hi
      have := hrd (j + 1) (by simpa using hj) i (by simpa using hi)
      omega
    have hlen' : gs.length ≤ f' := by
      simp at hf
      omega
    have hgoal : ∀ (S1 : List ℕ) (k1 : ℕ), (∀ i, i < L + 1 →
        col (fun t => W t ++ [g.op.eval (g.inputs.map fun i => (W t).getD i false)]) i ∈ S1) →
        0 ∈ S1 → 31 ∈ S1 → nots gs + k1 ≤ 2 → search f' S1 k1 = false →
        ∃ S' : List ℕ, (∀ i, i < L + (g :: gs).length →
          col (fun t => (g :: gs).foldl stepf (W t)) i ∈ S') ∧ tg S' = false := by
      intro S1 k1 hinv1 a0 a31 hn1 hs1
      obtain ⟨S', h1, h2⟩ := ih f' _ (L + 1) S1 k1 hlen' hW1 hinv1 a0 a31 hgs hrds hn1 hs1
      refine ⟨S', ?_, h2⟩
      intro i hi
      rw [hfold]
      exact h1 i (by simp at hi; omega)
    by_cases hmS : mk5 (g.op.eval (g.inputs.map fun i => (W 0).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 1).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 2).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 3).getD i false))
        (g.op.eval (g.inputs.map fun i => (W 4).getD i false)) ∈ S
    · have hinv1 : ∀ i, i < L + 1 →
          col (fun t => W t ++ [g.op.eval (g.inputs.map fun i => (W t).getD i false)]) i ∈ S := by
        intro i hi
        by_cases hiL : i < L
        · rw [hci i hiL]
          exact hinv i hiL
        · have : i = L := by omega
          subst this
          rw [hcl]
          exact hmS
      have hsf := search_fuel f' S k hs
      by_cases hgo : g.op = GateOp.not
      · rw [nots_pos g gs hgo] at hn
        exact hgoal S (k + 1) hinv1 h0 h31 (by omega) (search_k f' S k hsf)
      · rw [nots_neg g gs hgo] at hn
        exact hgoal S k hinv1 h0 h31 (by omega) hsf
    · have hss := search_succ f' S k hs _ hmlt hmS
      have hinv1 : ∀ i, i < L + 1 →
          col (fun t => W t ++ [g.op.eval (g.inputs.map fun i => (W t).getD i false)]) i ∈
            mk5 (g.op.eval (g.inputs.map fun i => (W 0).getD i false))
              (g.op.eval (g.inputs.map fun i => (W 1).getD i false))
              (g.op.eval (g.inputs.map fun i => (W 2).getD i false))
              (g.op.eval (g.inputs.map fun i => (W 3).getD i false))
              (g.op.eval (g.inputs.map fun i => (W 4).getD i false)) :: S := by
        intro i hi
        by_cases hiL : i < L
        · rw [hci i hiL]
          exact List.mem_cons_of_mem _ (hinv i hiL)
        · have : i = L := by omega
          subst this
          rw [hcl]
          exact List.mem_cons_self
      rcases hcase with hc | ⟨hgo, hb⟩ | ⟨hgo, hb⟩
      · exact absurd hc hmS
      · rw [nots_neg g gs hgo] at hn
        exact hgoal _ k hinv1 (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h31) (by omega)
          (hss.1 hb)
      · rw [nots_pos g gs hgo] at hn
        exact hgoal _ (k + 1) hinv1 (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h31) (by omega)
          (hss.2 (by omega) hb)

set_option maxRecDepth 100000 in
lemma search0 : search 5 [30, 28, 24, 16, 0, 31] 0 = false := by decide +kernel

def xs (t : Fin 5) : List Bool := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true]

lemma init_inv : ∀ i, i < 6 → col xs i ∈ [30, 28, 24, 16, 0, 31] := by
  intro i hi
  interval_cases i <;> decide

end PEqualNP.Outside.L_meta_49973

theorem PEqualNP.Outside.L_meta_49973 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (12 : Nat).testBit t.val ∧
    w.getD r.val false = (14 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, hrb, hnc, hsz, h⟩
  have hg : ∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hgm
    have := hfan g hgm
    simpa [Set.mem_insert_iff] using this
  have hrd : ∀ (j : ℕ) (hj : j < D.gates.length), ∀ i ∈ (D.gates[j]).inputs, i < 6 + j := by
    intro j hj i hi
    have := hrb j hj i (by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact hi)
    exact this
  obtain ⟨S', h1, h2⟩ := PEqualNP.Outside.L_meta_49973.main D.gates 5 PEqualNP.Outside.L_meta_49973.xs 6 [30, 28, 24, 16, 0, 31] 0 hsz
    (by intro t; fin_cases t <;> rfl) PEqualNP.Outside.L_meta_49973.init_inv (by decide) (by decide) hg hrd
    (by show PEqualNP.NotBracket.notCount ⟨D.gates, 0⟩ + 0 ≤ 2; exact hnc) PEqualNP.Outside.L_meta_49973.search0
  have hw : ∀ t : Fin 5, D.gates.foldl PEqualNP.Outside.L_meta_49973.stepf (PEqualNP.Outside.L_meta_49973.xs t) = D.wires (PEqualNP.Outside.L_meta_49973.xs t) :=
    fun _ => rfl
  have e0 := h 0
  have e1 := h 1
  have e2 := h 2
  have e3 := h 3
  have e4 := h 4
  have hp : PEqualNP.Outside.L_meta_49973.col (fun t => D.gates.foldl PEqualNP.Outside.L_meta_49973.stepf (PEqualNP.Outside.L_meta_49973.xs t)) p.val = 10 := by
    unfold PEqualNP.Outside.L_meta_49973.col
    simp only [hw]
    have a0 := e0.1
    have a1 := e1.1
    have a2 := e2.1
    have a3 := e3.1
    have a4 := e4.1
    simp only [PEqualNP.Outside.L_meta_49973.xs] at *
    rw [a0, a1, a2, a3, a4]
    decide
  have hq : PEqualNP.Outside.L_meta_49973.col (fun t => D.gates.foldl PEqualNP.Outside.L_meta_49973.stepf (PEqualNP.Outside.L_meta_49973.xs t)) q.val = 12 := by
    unfold PEqualNP.Outside.L_meta_49973.col
    simp only [hw]
    have a0 := e0.2.1
    have a1 := e1.2.1
    have a2 := e2.2.1
    have a3 := e3.2.1
    have a4 := e4.2.1
    simp only [PEqualNP.Outside.L_meta_49973.xs] at *
    rw [a0, a1, a2, a3, a4]
    decide
  have hr : PEqualNP.Outside.L_meta_49973.col (fun t => D.gates.foldl PEqualNP.Outside.L_meta_49973.stepf (PEqualNP.Outside.L_meta_49973.xs t)) r.val = 14 := by
    unfold PEqualNP.Outside.L_meta_49973.col
    simp only [hw]
    have a0 := e0.2.2
    have a1 := e1.2.2
    have a2 := e2.2.2
    have a3 := e3.2.2
    have a4 := e4.2.2
    simp only [PEqualNP.Outside.L_meta_49973.xs] at *
    rw [a0, a1, a2, a3, a4]
    decide
  have m1 := h1 p.val p.2
  have m2 := h1 q.val q.2
  have m3 := h1 r.val r.2
  rw [hp] at m1
  rw [hq] at m2
  rw [hr] at m3
  have : PEqualNP.Outside.L_meta_49973.tg S' = true := by
    unfold PEqualNP.Outside.L_meta_49973.tg
    exact decide_eq_true ⟨m1, m2, m3⟩
  rw [h2] at this
  exact Bool.false_ne_true this

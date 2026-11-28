import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50253

open PEqualNP.CircuitLowerBounds

def maskOf (l : List ℕ) : ℕ := l.foldr (fun x m => m ||| 2 ^ x) 0

def mem (S : ℕ) : List ℕ := (List.range 64).filter (fun a => S.testBit a)

def cands (S : ℕ) : List ℕ :=
  [0, 63] ++ mem S ++ (mem S).flatMap (fun a => (mem S).flatMap (fun b => [a &&& b, a ||| b]))

def nots (S : ℕ) : List ℕ := 63 :: (mem S).map (fun a => 63 ^^^ a)

def miss (S : ℕ) : ℕ :=
  (if S.testBit 4 then 0 else 1) + (if S.testBit 14 then 0 else 1) + (if S.testBit 40 then 0 else 1)

def done (S : ℕ) : Bool := S.testBit 4 && S.testBit 14 && S.testBit 40

def search : ℕ → ℕ → ℕ → Bool
  | S, 0, _ => done S
  | S, k + 1, n => done S || (decide (miss S ≤ k + 1) && (search S k n ||
      (List.range 64).any (fun v => !S.testBit v &&
        (((maskOf (cands S)).testBit v && search (S ||| 2 ^ v) k n) ||
         (decide (n < 2) && (maskOf (nots S)).testBit v && search (S ||| 2 ^ v) k (n + 1))))))

theorem search_false : search (maskOf [62, 60, 56, 48, 32, 0, 63]) 5 0 = false := by decide +kernel

theorem foldr_or (w : List ℕ) : ∀ i : ℕ, w.foldr (fun x m => m ||| 2 ^ x) i = i ||| maskOf w := by
  induction w with
  | nil => intro i; simp [maskOf]
  | cons y w ih =>
    intro i
    simp only [List.foldr_cons, maskOf] at *
    rw [ih i, ih 0]
    simp only [Nat.zero_or]
    rw [Nat.or_assoc]

theorem maskOf_snoc (w : List ℕ) (v : ℕ) : maskOf (w ++ [v]) = maskOf w ||| 2 ^ v := by
  unfold maskOf
  rw [List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil, Nat.zero_or]
  rw [foldr_or]
  exact Nat.or_comm _ _

theorem testBit_maskOf {l : List ℕ} {x : ℕ} (h : x ∈ l) : (maskOf l).testBit x = true := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    show (maskOf l ||| 2 ^ y).testBit x = true
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp h with rfl | h
    · simp [Nat.testBit_two_pow]
    · simp [ih h]

theorem mem_of {S a : ℕ} (ha : a < 64) (h : S.testBit a = true) : a ∈ mem S := by
  simp [mem, ha, h]

theorem or_self_of {S v : ℕ} (h : S.testBit v = true) : S ||| 2 ^ v = S := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hv : v = i
  · subst hv; simp [h]
  · simp [hv]

theorem miss_step (S v : ℕ) : miss S ≤ miss (S ||| 2 ^ v) + 1 := by
  unfold miss
  simp only [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h4 : v = 4
  · subst h4; cases S.testBit 4 <;> cases S.testBit 14 <;> cases S.testBit 40 <;> simp
  by_cases h20 : v = 14
  · subst h20; cases S.testBit 4 <;> cases S.testBit 14 <;> cases S.testBit 40 <;> simp
  by_cases h22 : v = 40
  · subst h22; cases S.testBit 4 <;> cases S.testBit 14 <;> cases S.testBit 40 <;> simp
  simp [h4, h20, h22]

theorem miss_le_of_search : ∀ (k S n : ℕ), search S k n = true → miss S ≤ k := by
  intro k
  induction k with
  | zero =>
    intro S n h
    simp only [search, done, Bool.and_eq_true] at h
    simp [miss, h.1.1, h.1.2, h.2]
  | succ k ih =>
    intro S n h
    simp only [search, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩
    · simp only [done, Bool.and_eq_true] at h
      simp [miss, h.1.1, h.1.2, h.2]
    · exact h

theorem search_succ {S k n : ℕ} (h : search S k n = true) : search S (k + 1) n = true := by
  have hm := miss_le_of_search k S n h
  simp only [search, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨by omega, Or.inl h⟩

theorem search_le {S k n : ℕ} (h : search S k n = true) : ∀ k', k ≤ k' → search S k' n = true := by
  intro k' hk
  induction k', hk using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact search_succ ih

theorem search_mono_n : ∀ (k S n n' : ℕ), n ≤ n' → search S k n' = true → search S k n = true := by
  intro k
  induction k with
  | zero => intro S n n' _ h; simpa [search] using h
  | succ k ih =>
    intro S n n' hn h
    simp only [search, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h ⊢
    rcases h with h | ⟨hm, h | ⟨v, hv, hb, h | ⟨⟨h1, h2⟩, h3⟩⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨hm, Or.inl (ih S n n' hn h)⟩
    · exact Or.inr ⟨hm, Or.inr ⟨v, hv, hb, Or.inl ⟨h.1, ih _ n n' hn h.2⟩⟩⟩
    · exact Or.inr ⟨hm, Or.inr ⟨v, hv, hb, Or.inr ⟨⟨by omega, h2⟩, ih _ (n + 1) (n' + 1) (by omega) h3⟩⟩⟩

def gv (g : Gate) (w : List ℕ) : ℕ :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => w.getD i 0 &&& acc) 63
  | .or => g.inputs.foldr (fun i acc => w.getD i 0 ||| acc) 0
  | .not => match g.inputs with
    | [] => 63
    | i :: _ => 63 ^^^ w.getD i 0
  | _ => 0

def vw (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv g w]) w

theorem length_vw : ∀ (gs : List Gate) (w : List ℕ), (vw gs w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp [vw]
  | cons g gs ih =>
    intro w
    show (vw gs (w ++ [gv g w])).length = _
    rw [ih]; simp; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (k : ℕ) :
    (l ++ [a]).getD k d = if k < l.length then l.getD k d else if k = l.length then a else d := by
  by_cases hk : k < l.length
  · rw [if_pos hk, List.getD_append _ _ _ _ hk]
  · rw [if_neg hk, List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : k = l.length
    · subst he; simp
    · rw [if_neg he]
      rw [List.getD_eq_default]
      simp; omega

theorem bit63 {t : ℕ} (ht : t < 6) : (63 : ℕ).testBit t = true := by
  interval_cases t <;> rfl

theorem gate_bridge {t : ℕ} (ht : t < 6) (wb : List Bool) (wv : List ℕ)
    (h : ∀ k, wb.getD k false = (wv.getD k 0).testBit t) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    g.op.eval (g.inputs.map fun i => wb.getD i false) = (gv g wv).testBit t := by
  rcases hop with hop | hop | hop
  · simp only [gv, hop, GateOp.eval]
    induction g.inputs with
    | nil => simp [bit63 ht]
    | cons i l ih =>
      simp only [List.map_cons, List.all_cons, List.foldr_cons, Nat.testBit_and, id_eq]
      rw [h i, ih]
  · simp only [gv, hop, GateOp.eval]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.any_cons, List.foldr_cons, Nat.testBit_or, id_eq]
      rw [h i, ih]
  · simp only [gv, hop, GateOp.eval]
    cases g.inputs with
    | nil => simp [bit63 ht]
    | cons i l =>
      simp only [List.map_cons, List.headD_cons, Nat.testBit_xor, bit63 ht]
      rw [h i]; simp

theorem bridge {t : ℕ} (ht : t < 6) : ∀ (gs : List Gate) (wb : List Bool) (wv : List ℕ),
    wb.length = wv.length → (∀ k, wb.getD k false = (wv.getD k 0).testBit t) →
    (∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) →
    ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wb).getD k false
      = ((vw gs wv).getD k 0).testBit t := by
  intro gs
  induction gs with
  | nil => intro wb wv _ h _ k; simpa [vw] using h k
  | cons g gs ih =>
    intro wb wv hl h hops k
    simp only [List.foldl_cons]
    show _ = ((vw gs (wv ++ [gv g wv])).getD k 0).testBit t
    apply ih
    · simp [hl]
    · intro k
      rw [getD_snoc, getD_snoc, hl]
      by_cases hk : k < wv.length
      · simp only [if_pos hk]; exact h k
      · simp only [if_neg hk]
        by_cases he : k = wv.length
        · simp only [if_pos he]
          exact gate_bridge ht wb wv h g (hops g (List.mem_cons_self))
        · simp [he]
    · intro g' hg'; exact hops g' (List.mem_cons_of_mem _ hg')

theorem gv_lt (g : Gate) (w : List ℕ) (hw : ∀ x ∈ w, x < 64) : gv g w < 64 := by
  have hget : ∀ i, w.getD i 0 < 64 := by
    intro i
    by_cases hi : i < w.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hw _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  unfold gv
  split
  · induction g.inputs with
    | nil => simp
    | cons i l ih => exact lt_of_le_of_lt Nat.and_le_right ih
  · induction g.inputs with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldr_cons]
      exact Nat.or_lt_two_pow (n := 6) (hget i) ih
  · split
    · omega
    · exact Nat.xor_lt_two_pow (n := 6) (by norm_num) (hget _)
  · omega

theorem vw_lt : ∀ (gs : List Gate) (w : List ℕ), (∀ x ∈ w, x < 64) → ∀ x ∈ vw gs w, x < 64 := by
  intro gs
  induction gs with
  | nil => intro w hw; simpa [vw] using hw
  | cons g gs ih =>
    intro w hw
    show ∀ x ∈ vw gs (w ++ [gv g w]), x < 64
    apply ih
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hw x hx
    · simp at hx; subst hx; exact gv_lt g w hw

theorem getD_mem (w : List ℕ) (hw : ∀ x ∈ w, x < 64) (h0 : (0 : ℕ) ∈ w) (i : ℕ) :
    w.getD i 0 ∈ mem (maskOf w) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact mem_of (hw _ (List.getElem_mem hi)) (testBit_maskOf (List.getElem_mem hi))
  · rw [List.getD_eq_default _ _ (by omega)]
    exact mem_of (by norm_num) (testBit_maskOf h0)

theorem land63 {a : ℕ} (ha : a < 64) : a &&& 63 = a := by
  have : (63 : ℕ) = 2 ^ 6 - 1 := by norm_num
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt ha

theorem gv_mono (g : Gate) (w : List ℕ) (hw : ∀ x ∈ w, x < 64) (h0 : (0 : ℕ) ∈ w)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    gv g w ∈ cands (maskOf w) := by
  have hget := getD_mem w hw h0
  have hlt : ∀ i, w.getD i 0 < 64 := by
    intro i
    by_cases hi : i < w.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hw _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  rcases hop with hop | hop
  · simp only [gv, hop]
    match hg : g.inputs, hlen with
    | [], _ => simp [cands]
    | [i], _ =>
      simp only [List.foldr_cons, List.foldr_nil, land63 (hlt i)]
      rw [cands, List.mem_append, List.mem_append]
      exact Or.inl (Or.inr (hget i))
    | [i, j], _ =>
      simp only [List.foldr_cons, List.foldr_nil, land63 (hlt j)]
      simp only [cands, List.mem_append, List.mem_flatMap]
      right
      exact ⟨w.getD i 0, hget i, w.getD j 0, hget j, by simp⟩
  · simp only [gv, hop]
    match hg : g.inputs, hlen with
    | [], _ => simp [cands]
    | [i], _ =>
      simp only [List.foldr_cons, List.foldr_nil, Nat.or_zero]
      rw [cands, List.mem_append, List.mem_append]
      exact Or.inl (Or.inr (hget i))
    | [i, j], _ =>
      simp only [List.foldr_cons, List.foldr_nil, Nat.or_zero]
      simp only [cands, List.mem_append, List.mem_flatMap]
      right
      exact ⟨w.getD i 0, hget i, w.getD j 0, hget j, by simp⟩

theorem gv_not (g : Gate) (w : List ℕ) (hw : ∀ x ∈ w, x < 64) (h0 : (0 : ℕ) ∈ w)
    (hop : g.op = .not) : gv g w ∈ nots (maskOf w) := by
  have hget := getD_mem w hw h0
  simp only [gv, hop]
  cases g.inputs with
  | nil => simp [nots]
  | cons i l => simp only [nots, List.mem_cons, List.mem_map]; right; exact ⟨_, hget i, rfl⟩

def nc (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem nc_cons_not {g : Gate} {gs : List Gate} (h : g.op = GateOp.not) : nc (g :: gs) = nc gs + 1 := by
  simp [nc, PEqualNP.NotBracket.notCount, List.filter_cons, h]

theorem nc_cons_ne {g : Gate} {gs : List Gate} (h : ¬ g.op = GateOp.not) : nc (g :: gs) = nc gs := by
  simp [nc, PEqualNP.NotBracket.notCount, List.filter_cons, h]

theorem sound : ∀ (gs : List Gate) (w : List ℕ) (n : ℕ), (∀ x ∈ w, x < 64) → (0 : ℕ) ∈ w →
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
    n + nc gs ≤ 2 → 4 ∈ vw gs w → 14 ∈ vw gs w → 40 ∈ vw gs w →
    search (maskOf w) gs.length n = true := by
  intro gs
  induction gs with
  | nil =>
    intro w n _ _ _ _ h5 h20 h22
    simp only [vw, List.foldl_nil] at h5 h20 h22
    simp [search, done, testBit_maskOf h5, testBit_maskOf h20, testBit_maskOf h22]
  | cons g gs ih =>
    intro w n hw h0 hgs hn h5 h20 h22
    have hg := hgs g List.mem_cons_self
    have hw' : ∀ x ∈ w ++ [gv g w], x < 64 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hw x hx
      · simp at hx; subst hx; exact gv_lt g w hw
    have h0' : (0 : ℕ) ∈ w ++ [gv g w] := List.mem_append_left _ h0
    have hgs' : ∀ g' ∈ gs, (g'.op = .and ∨ g'.op = .or ∨ g'.op = .not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    have hop' : g.op = GateOp.not ∨ (g.op = .and ∨ g.op = .or) := by
      rcases hg.1 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    have hstep := miss_step (maskOf w) (gv g w)
    simp only [List.length_cons, search, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true]
    rcases hop' with hnot | hmono
    · rw [nc_cons_not hnot] at hn
      have IH := ih (w ++ [gv g w]) (n + 1) hw' h0' hgs' (by omega) h5 h20 h22
      rw [maskOf_snoc] at IH
      have hm := miss_le_of_search _ _ _ IH
      refine Or.inr ⟨by omega, ?_⟩
      by_cases hv : (maskOf w).testBit (gv g w) = true
      · left
        rw [or_self_of hv] at IH
        exact search_mono_n _ _ _ _ (by omega) IH
      · right
        refine ⟨gv g w, List.mem_range.mpr (gv_lt g w hw), by simpa using hv, ?_⟩
        right
        exact ⟨⟨by omega, testBit_maskOf (gv_not g w hw h0 hnot)⟩, IH⟩
    · have hne : ¬ g.op = GateOp.not := by
        rcases hmono with h | h <;> rw [h] <;> intro hc <;> cases hc
      rw [nc_cons_ne hne] at hn
      have IH := ih (w ++ [gv g w]) n hw' h0' hgs' hn h5 h20 h22
      rw [maskOf_snoc] at IH
      have hm := miss_le_of_search _ _ _ IH
      refine Or.inr ⟨by omega, ?_⟩
      by_cases hv : (maskOf w).testBit (gv g w) = true
      · left
        rw [or_self_of hv] at IH
        exact IH
      · right
        refine ⟨gv g w, List.mem_range.mpr (gv_lt g w hw), by simpa using hv, ?_⟩
        left
        exact ⟨testBit_maskOf (gv_mono g w hw h0 hmono hg.2), IH⟩

theorem eq_of_bits {a b : ℕ} (ha : a < 64) (hb : b < 64) (h : ∀ t < 6, a.testBit t = b.testBit t) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 6
  · exact h t ht
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (by
        calc (64 : ℕ) = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (by
        calc (64 : ℕ) = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem base (t : Fin 6) (k : ℕ) :
    ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]).getD k false =
      (([62, 60, 56, 48, 32, 0, 63] : List ℕ).getD k 0).testBit t.val := by
  by_cases hk : k < 7
  · interval_cases k <;> fin_cases t <;> rfl
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem main (D : Circuit) (p q r : Fin (7 + D.size))
    (hfan : PEqualNP.MetaComplexity.FanInTwo D) (hnot : PEqualNP.NotBracket.notCount D ≤ 2)
    (hsize : D.size ≤ 5)
    (hv : ∀ t : Fin 6,
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD p.val false
        = (4 : Nat).testBit t.val ∧
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD q.val false
        = (14 : Nat).testBit t.val ∧
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD r.val false
        = (40 : Nat).testBit t.val) : False := by
  have hops : ∀ g ∈ D.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    simpa using h1
  have hinit : ∀ x ∈ ([62, 60, 56, 48, 32, 0, 63] : List ℕ), x < 64 := by decide
  have hbr : ∀ (t : Fin 6) (k : ℕ),
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD k false
        = ((vw D.gates [62, 60, 56, 48, 32, 0, 63]).getD k 0).testBit t.val := by
    intro t k
    unfold Circuit.wires
    exact bridge t.isLt D.gates _ _ (by simp) (base t) (fun g hg => (hops g hg).1) k
  have key : ∀ (x : Fin (7 + D.size)) (c : ℕ), c < 64 →
      (∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++
        [false, true])).getD x.val false = c.testBit t.val) →
      c ∈ vw D.gates [62, 60, 56, 48, 32, 0, 63] := by
    intro x c hc h
    have hlen : x.val < (vw D.gates [62, 60, 56, 48, 32, 0, 63]).length := by
      rw [length_vw]
      have := x.isLt
      simp only [Circuit.size] at this
      simp
      omega
    have hmem := List.getElem_mem hlen
    have hval : (vw D.gates [62, 60, 56, 48, 32, 0, 63]).getD x.val 0 = c := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact eq_of_bits (vw_lt _ _ hinit _ hmem) hc
        (fun t ht => by rw [← List.getD_eq_getElem _ 0 hlen, ← hbr ⟨t, ht⟩ x.val]; exact h ⟨t, ht⟩)
    rw [← hval, List.getD_eq_getElem _ _ hlen]
    exact hmem
  have h5 := key p 4 (by norm_num) (fun t => (hv t).1)
  have h20 := key q 14 (by norm_num) (fun t => (hv t).2.1)
  have h22 := key r 40 (by norm_num) (fun t => (hv t).2.2)
  have hs := sound D.gates [62, 60, 56, 48, 32, 0, 63] 0 hinit (by simp) hops
    (by show 0 + PEqualNP.NotBracket.notCount D ≤ 2; omega) h5 h20 h22
  have h6 := search_le hs 5 (by simpa [Circuit.size] using hsize)
  rw [search_false] at h6
  exact absurd h6 (by decide)

end PEqualNP.Outside.L_meta_50253

theorem PEqualNP.Outside.L_meta_50253 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (14 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _hrb, hnot, hsize, hv⟩
  exact PEqualNP.Outside.L_meta_50253.main D p q r hfan hnot hsize (fun t => hv t)

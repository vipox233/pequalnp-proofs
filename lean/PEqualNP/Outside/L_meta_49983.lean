import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket


namespace PEqualNP.Outside.L_meta_49983_aux

open PEqualNP.CircuitLowerBounds

def miss (A B C : Nat) (L : List Nat) : Nat :=
  (if L.contains A then 0 else 1) + (if L.contains B then 0 else 1) + (if L.contains C then 0 else 1)

def ok (A B C : Nat) : Nat → Nat → List Nat → Bool
  | 0, _, L => miss A B C L == 0
  | g + 1, n, L =>
    miss A B C L == 0 ||
    (decide (miss A B C L ≤ g + 1) &&
      (L.any (fun a => L.any (fun b =>
        (!L.contains (a &&& b) && ok A B C g n (L ++ [a &&& b])) ||
        (!L.contains (a ||| b) && ok A B C g n (L ++ [a ||| b])))) ||
       (decide (0 < n) && L.any (fun a => !L.contains (31 ^^^ a) && ok A B C g (n - 1) (L ++ [31 ^^^ a])))))

theorem miss_congr (A B C : Nat) (L L' : List Nat) (h : ∀ x, x ∈ L ↔ x ∈ L') :
    miss A B C L = miss A B C L' := by
  have hc : ∀ x, L.contains x = L'.contains x := by
    intro x
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
    exact h x
  simp only [miss, hc]

theorem any_congr (L L' : List Nat) (h : ∀ x, x ∈ L ↔ x ∈ L') (p p' : Nat → Bool)
    (hp : ∀ x, p x = p' x) : L.any p = L'.any p' := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hpx⟩; exact ⟨x, (h x).1 hx, by rw [← hp]; exact hpx⟩
  · rintro ⟨x, hx, hpx⟩; exact ⟨x, (h x).2 hx, by rw [hp]; exact hpx⟩

theorem ok_congr (A B C : Nat) : ∀ g n (L L' : List Nat), (∀ x, x ∈ L ↔ x ∈ L') →
    ok A B C g n L = ok A B C g n L' := by
  intro g
  induction g with
  | zero => intro n L L' h; simp only [ok, miss_congr A B C L L' h]
  | succ g ih =>
    intro n L L' h
    have hc : ∀ x, L.contains x = L'.contains x := by
      intro x
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
      exact h x
    have happ : ∀ y, ∀ x, x ∈ L ++ [y] ↔ x ∈ L' ++ [y] := by
      intro y x; simp only [List.mem_append, h x]
    simp only [ok, miss_congr A B C L L' h]
    congr 1
    congr 1
    congr 1
    · apply any_congr L L' h
      intro a
      apply any_congr L L' h
      intro b
      rw [hc, hc, ih n _ _ (happ _), ih n _ _ (happ _)]
    · congr 1
      apply any_congr L L' h
      intro a
      rw [hc, ih _ _ _ (happ _)]

theorem ok_mono_g (A B C : Nat) : ∀ g n (L : List Nat), ok A B C g n L = true → ok A B C (g + 1) n L = true := by
  intro g
  induction g with
  | zero =>
    intro n L h
    simp only [ok] at h ⊢
    rw [h]; rfl
  | succ g ih =>
    intro n L h
    rw [ok.eq_2] at h
    rw [ok.eq_2]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      Bool.not_eq_true'] at h ⊢
    rcases h with h | ⟨hm, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨by omega, ?_⟩
      rcases h with ⟨a, ha, b, hb, h⟩ | ⟨hn, a, ha, h⟩
      · left
        refine ⟨a, ha, b, hb, ?_⟩
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, ih _ _ h2⟩
        · exact Or.inr ⟨h1, ih _ _ h2⟩
      · right
        exact ⟨hn, a, ha, h.1, ih _ _ h.2⟩

theorem ok_mono_n (A B C : Nat) : ∀ g n (L : List Nat), ok A B C g n L = true → ok A B C g (n + 1) L = true := by
  intro g
  induction g with
  | zero => intro n L h; simpa only [ok] using h
  | succ g ih =>
    intro n L h
    simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      Bool.not_eq_true'] at h ⊢
    rcases h with h | ⟨hm, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨hm, ?_⟩
      rcases h with ⟨a, ha, b, hb, h⟩ | ⟨hn, a, ha, h⟩
      · left
        refine ⟨a, ha, b, hb, ?_⟩
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, ih _ _ h2⟩
        · exact Or.inr ⟨h1, ih _ _ h2⟩
      · right
        refine ⟨by omega, a, ha, h.1, ?_⟩
        have := ih _ _ h.2
        rwa [show n + 1 - 1 = n - 1 + 1 by omega]

theorem ok_mono (A B C : Nat) (g n g' n' : Nat) (L : List Nat) (hg : g ≤ g') (hn : n ≤ n')
    (h : ok A B C g n L = true) : ok A B C g' n' L = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hg
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : ok A B C g (n + e) L = true := by
    induction e with
    | zero => exact h
    | succ e ih => exact ok_mono_n A B C g (n + e) L (ih (by omega))
  induction d with
  | zero => exact h1
  | succ d ih => exact ok_mono_g A B C (g + d) (n + e) L (ih (by omega))

def gm (g : Gate) (w : List Nat) : Nat :=
  match g.op, g.inputs with
  | .and, [] => 31
  | .and, [a] => w.getD a 0
  | .and, [a, b] => w.getD a 0 &&& w.getD b 0
  | .or, [] => 0
  | .or, [a] => w.getD a 0
  | .or, [a, b] => w.getD a 0 ||| w.getD b 0
  | .not, [] => 31
  | .not, a :: _ => 31 ^^^ w.getD a 0
  | _, _ => 0

def mev (gs : List Gate) (w : List Nat) : List Nat := gs.foldl (fun w g => w ++ [gm g w]) w

def nc (gs : List Gate) : Nat := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem nc_le (g : Gate) (gs : List Gate) : nc gs ≤ nc (g :: gs) := by
  unfold nc PEqualNP.NotBracket.notCount
  simp only [List.filter_cons]
  split <;> simp

def Shape (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_map_bit (w : List Nat) (i t : Nat) :
    (w.map fun m => m.testBit t).getD i false = (w.getD i 0).testBit t := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]; simp

theorem b31 (t : Nat) (ht : t < 5) : (31 : Nat).testBit t = true := by
  interval_cases t <;> decide

theorem gm_bit (g : Gate) (hg : Shape g) (w : List Nat) (t : Nat) (ht : t < 5) :
    (gm g w).testBit t = g.op.eval (g.inputs.map fun i => (w.map fun m => m.testBit t).getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  simp only [getD_map_bit]
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ => simp [gm, GateOp.eval, b31 t ht]
    | [a], _ => simp [gm, GateOp.eval]
    | [a, b], _ => simp [gm, GateOp.eval, Nat.testBit_land]
  · match ins, hlen with
    | [], _ => simp [gm, GateOp.eval]
    | [a], _ => simp [gm, GateOp.eval]
    | [a, b], _ => simp [gm, GateOp.eval, Nat.testBit_lor]
  · match ins, hlen with
    | [], _ => simp [gm, GateOp.eval, b31 t ht]
    | a :: _, _ => simp [gm, GateOp.eval, Nat.testBit_xor, b31 t ht]

theorem mev_bits (t : Nat) (ht : t < 5) : ∀ (gs : List Gate) (w : List Nat), (∀ g ∈ gs, Shape g) →
    (mev gs w).map (fun m => m.testBit t) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map fun m => m.testBit t) := by
  intro gs
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hs
    simp only [mev, List.foldl_cons] at ih ⊢
    rw [← gm_bit g (hs g List.mem_cons_self) w t ht]
    have e : (w.map fun m => m.testBit t) ++ [(gm g w).testBit t] = (w ++ [gm g w]).map fun m => m.testBit t := by simp
    rw [e]
    exact ih _ (fun g' hg' => hs g' (List.mem_cons_of_mem _ hg'))

theorem mev_length : ∀ (gs : List Gate) (w : List Nat), (mev gs w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp [mev]
  | cons g gs ih => intro w; simp only [mev, List.foldl_cons] at ih ⊢; rw [ih]; simp; omega

theorem gm_lt (g : Gate) (w : List Nat) (hw : ∀ m ∈ w, m < 32) : gm g w < 32 := by
  have hd : ∀ i, w.getD i 0 < 32 := by
    intro i
    by_cases h : i < w.length
    · rw [List.getD_eq_getElem _ _ h]; exact hw _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  have h32 : (32 : Nat) = 2 ^ 5 := by norm_num
  unfold gm
  split
  all_goals first
    | omega
    | exact hd _
    | (rw [h32]; exact Nat.and_lt_two_pow _ (by rw [← h32]; exact hd _))
    | (rw [h32]; exact Nat.or_lt_two_pow (by rw [← h32]; exact hd _) (by rw [← h32]; exact hd _))
    | (rw [h32]; exact Nat.xor_lt_two_pow (by norm_num) (by rw [← h32]; exact hd _))

theorem mev_lt : ∀ (gs : List Gate) (w : List Nat), (∀ m ∈ w, m < 32) → ∀ m ∈ mev gs w, m < 32 := by
  intro gs
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    simp only [mev, List.foldl_cons] at ih ⊢
    apply ih
    intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact hw m h
    · rw [List.mem_singleton.1 h]; exact gm_lt g w hw

theorem ind_step (w : List Nat) (m x : Nat) :
    (if w.contains x then 0 else 1) ≤ (if (w ++ [m]).contains x then 0 else 1) + (if x = m then 1 else 0) := by
  by_cases h : x = m
  · subst h; split_ifs <;> omega
  · have e : (w ++ [m]).contains x = w.contains x := by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
      simp [h]
    rw [e]; split_ifs <;> omega

theorem miss_step (A B C : Nat) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (w : List Nat) (m : Nat) :
    miss A B C w ≤ miss A B C (w ++ [m]) + 1 := by
  unfold miss
  have h1 := ind_step w m A
  have h2 := ind_step w m B
  have h3 := ind_step w m C
  have h4 : (if A = m then 1 else 0) + (if B = m then 1 else 0) + (if C = m then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  omega

theorem miss_le (A B C : Nat) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) : ∀ (gs : List Gate) (w : List Nat),
    A ∈ mev gs w → B ∈ mev gs w → C ∈ mev gs w → miss A B C w ≤ gs.length := by
  intro gs
  induction gs with
  | nil =>
    intro w hA hB hC
    simp only [mev, List.foldl_nil] at hA hB hC
    simp [miss, List.contains_iff_mem, hA, hB, hC]
  | cons g gs ih =>
    intro w hA hB hC
    simp only [mev, List.foldl_cons] at hA hB hC
    have := ih _ hA hB hC
    have := miss_step A B C hAB hAC hBC w (gm g w)
    simp only [List.length_cons]
    omega

theorem gm_cases (g : Gate) (hg : Shape g) (w : List Nat) (hin : ∀ i ∈ g.inputs, i < w.length)
    (h0 : 0 ∈ w) (h31 : 31 ∈ w) (gs : List Gate) :
    gm g w ∈ w ∨
    (∃ a ∈ w, ∃ b ∈ w, gm g w = a &&& b ∧ nc (g :: gs) = nc gs) ∨
    (∃ a ∈ w, ∃ b ∈ w, gm g w = a ||| b ∧ nc (g :: gs) = nc gs) ∨
    (∃ a ∈ w, gm g w = 31 ^^^ a ∧ nc (g :: gs) = nc gs + 1) := by
  have hd : ∀ i ∈ g.inputs, w.getD i 0 ∈ w := fun i hi => by
    rw [List.getD_eq_getElem _ _ (hin i hi)]; exact List.getElem_mem _
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen hd
  rcases hop with rfl | rfl | rfl
  · match ins, hlen, hd with
    | [], _, _ => exact Or.inl h31
    | [a], _, hd => exact Or.inl (hd a (by simp))
    | [a, b], _, hd => exact Or.inr (Or.inl ⟨_, hd a (by simp), _, hd b (by simp), rfl, rfl⟩)
  · match ins, hlen, hd with
    | [], _, _ => exact Or.inl h0
    | [a], _, hd => exact Or.inl (hd a (by simp))
    | [a, b], _, hd => exact Or.inr (Or.inr (Or.inl ⟨_, hd a (by simp), _, hd b (by simp), rfl, rfl⟩))
  · match ins, hlen, hd with
    | [], _, _ => exact Or.inl h31
    | a :: _, _, hd => exact Or.inr (Or.inr (Or.inr ⟨_, hd a (by simp), rfl, rfl⟩))

theorem sound (A B C : Nat) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) : ∀ (gs : List Gate) (w : List Nat),
    (∀ g ∈ gs, Shape g) →
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w.length + j) →
    0 ∈ w → 31 ∈ w →
    A ∈ mev gs w → B ∈ mev gs w → C ∈ mev gs w → ok A B C gs.length (nc gs) w = true := by
  intro gs
  induction gs with
  | nil =>
    intro w _ _ _ _ hA hB hC
    simp only [mev, List.foldl_nil] at hA hB hC
    simp [ok, miss, List.contains_iff_mem, hA, hB, hC]
  | cons g gs ih =>
    intro w hs hrb h0 h31 hA hB hC
    have hml := miss_le A B C hAB hAC hBC (g :: gs) w hA hB hC
    simp only [mev, List.foldl_cons] at hA hB hC
    have hrb' : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < (w ++ [gm g w]).length + j := by
      intro j hj i hi
      have := hrb (j + 1) (by simp; omega) i (by simpa using hi)
      simp; omega
    have hIH := ih (w ++ [gm g w]) (fun g' hg' => hs g' (List.mem_cons_of_mem _ hg')) hrb'
      (List.mem_append_left _ h0) (List.mem_append_left _ h31) hA hB hC
    have hin : ∀ i ∈ g.inputs, i < w.length := by
      intro i hi
      have := hrb 0 (by simp) i (by simpa using hi)
      omega
    have hsg := hs g List.mem_cons_self
    by_cases hdup : gm g w ∈ w
    · have hset : ∀ x, x ∈ w ++ [gm g w] ↔ x ∈ w := by
        intro x; simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | rfl)
          · exact h
          · exact hdup
        · intro h; exact Or.inl h
      rw [ok_congr A B C _ _ _ _ hset] at hIH
      exact ok_mono A B C _ _ _ _ w (by simp) (nc_le g gs) hIH
    · have hcont : w.contains (gm g w) = false := by simpa [List.contains_iff_mem] using hdup
      rw [List.length_cons, ok.eq_2]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
        Bool.not_eq_true']
      right
      refine ⟨by simpa using hml, ?_⟩
      rcases gm_cases g hsg w hin h0 h31 gs with h | ⟨a, ha, b, hb, he, hn⟩ | ⟨a, ha, b, hb, he, hn⟩ |
          ⟨a, ha, he, hn⟩
      · exact absurd h hdup
      · left
        refine ⟨a, ha, b, hb, Or.inl ⟨by rw [← he]; exact hcont, ?_⟩⟩
        rw [hn, ← he]; exact hIH
      · left
        refine ⟨a, ha, b, hb, Or.inr ⟨by rw [← he]; exact hcont, ?_⟩⟩
        rw [hn, ← he]; exact hIH
      · right
        refine ⟨by rw [hn]; omega, a, ha, by rw [← he]; exact hcont, ?_⟩
        rw [hn, Nat.add_sub_cancel, ← he]; exact hIH

def init : List Nat := [30, 28, 24, 16, 0, 31]

theorem xs_eq (t : Fin 5) :
    (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true] = init.map fun m => m.testBit t.val := by
  fin_cases t <;> decide

theorem mask_eq (x c : Nat) (hx : x < 32) (hc : c < 32) (h : ∀ t : Fin 5, x.testBit t.val = c.testBit t.val) :
    x = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 5
  · exact h ⟨i, hi⟩
  · have h1 : x < 2 ^ i := lt_of_lt_of_le hx (by
      calc (32 : Nat) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : c < 2 ^ i := lt_of_lt_of_le hc (by
      calc (32 : Nat) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

theorem search_false : ok 6 12 20 5 2 init = false := by decide +kernel

end PEqualNP.Outside.L_meta_49983_aux

theorem PEqualNP.Outside.L_meta_49983 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (12 : Nat).testBit t.val ∧
    w.getD r.val false = (20 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, hrb, hnot, hsize, hval⟩
  have hs : ∀ g ∈ D.gates, PEqualNP.Outside.L_meta_49983_aux.Shape g := fun g hg => hfan g hg
  have hlt : ∀ m ∈ PEqualNP.Outside.L_meta_49983_aux.mev D.gates PEqualNP.Outside.L_meta_49983_aux.init, m < 32 :=
    PEqualNP.Outside.L_meta_49983_aux.mev_lt D.gates _ (by decide)
  have hlen : (PEqualNP.Outside.L_meta_49983_aux.mev D.gates PEqualNP.Outside.L_meta_49983_aux.init).length = 6 + D.size := by
    rw [PEqualNP.Outside.L_meta_49983_aux.mev_length]; rfl
  have hw : ∀ (t : Fin 5) (i : Nat),
      (D.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true])).getD i false =
        ((PEqualNP.Outside.L_meta_49983_aux.mev D.gates PEqualNP.Outside.L_meta_49983_aux.init).getD i 0).testBit t.val := by
    intro t i
    rw [PEqualNP.Outside.L_meta_49983_aux.xs_eq t, PEqualNP.CircuitLowerBounds.Circuit.wires,
      ← PEqualNP.Outside.L_meta_49983_aux.mev_bits t.val t.isLt D.gates _ hs, PEqualNP.Outside.L_meta_49983_aux.getD_map_bit]
  have hmem : ∀ (x : Fin (6 + D.size)) (c : Nat), c < 32 →
      (∀ t : Fin 5, (D.wires ((List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false, true])).getD x.val false =
        c.testBit t.val) → c ∈ PEqualNP.Outside.L_meta_49983_aux.mev D.gates PEqualNP.Outside.L_meta_49983_aux.init := by
    intro x c hc h
    have hx : x.val < (PEqualNP.Outside.L_meta_49983_aux.mev D.gates PEqualNP.Outside.L_meta_49983_aux.init).length := by rw [hlen]; exact x.isLt
    have hm : (PEqualNP.Outside.L_meta_49983_aux.mev D.gates PEqualNP.Outside.L_meta_49983_aux.init).getD x.val 0 ∈ PEqualNP.Outside.L_meta_49983_aux.mev D.gates PEqualNP.Outside.L_meta_49983_aux.init := by
      rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem hx
    have he := PEqualNP.Outside.L_meta_49983_aux.mask_eq _ c (hlt _ hm) hc (fun t => by rw [← hw t x.val]; exact h t)
    rw [← he]; exact hm
  have hA := hmem p 6 (by norm_num) (fun t => (hval t).1)
  have hB := hmem q 12 (by norm_num) (fun t => (hval t).2.1)
  have hC := hmem r 20 (by norm_num) (fun t => (hval t).2.2)
  have hrb' : ∀ j < D.gates.length, ∀ i ∈ (D.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
      i < PEqualNP.Outside.L_meta_49983_aux.init.length + j := fun j hj i hi => hrb j hj i hi
  have hok := PEqualNP.Outside.L_meta_49983_aux.sound 6 12 20 (by norm_num) (by norm_num) (by norm_num) D.gates _ hs hrb'
    (by decide) (by decide) hA hB hC
  have hnc : PEqualNP.Outside.L_meta_49983_aux.nc D.gates = PEqualNP.NotBracket.notCount D := rfl
  have hok' := PEqualNP.Outside.L_meta_49983_aux.ok_mono 6 12 20 _ _ 5 2 _ (by simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hsize)
    (by rw [hnc]; exact hnot) hok
  rw [PEqualNP.Outside.L_meta_49983_aux.search_false] at hok'
  exact Bool.false_ne_true hok'

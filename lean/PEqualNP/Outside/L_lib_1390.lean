import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1390

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq_W (C : Circuit) (w : List Bool) : C.wires w = W C.gates w := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_append (gs hs : List Gate) (w : List Bool) :
    W (gs ++ hs) w = W hs (W gs w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    W (gs ++ [g]) w = W gs w ++ [g.op.eval (g.inputs.map fun i => (W gs w).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (w : List Bool) : (W gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem new_wire (gs : List Gate) (g : Gate) (w : List Bool) :
    (W (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun t => (W gs w).getD t false) := by
  rw [W_snoc, getD_snoc]; simp [W_len]

theorem old_wire (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i ≠ w.length + gs.length) :
    (W (gs ++ [g]) w).getD i false = (W gs w).getD i false := by
  rw [W_snoc, getD_snoc]; simp [W_len, hi]

theorem W_append_old (gs hs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + gs.length) :
    (W (gs ++ hs) w).getD i false = (W gs w).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, old_wire (gs ++ hs) g w i (by simp; omega)]
    exact ih

def prefixInput (n : ℕ) (l : Fin (n + 1)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false, true]

theorem prefixInput_len (n : ℕ) (l : Fin (n + 1)) : (prefixInput n l).length = n + 2 := by
  simp [prefixInput]

theorem prefixInput_lt (n : ℕ) (l : Fin (n + 1)) (i : ℕ) (hi : i < n) :
    (prefixInput n l).getD i false = decide (i < l.val) := by
  unfold prefixInput
  rw [List.getD_append _ _ _ _ (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi])]
  simp

theorem prefixInput_n (n : ℕ) (l : Fin (n + 1)) :
    (prefixInput n l).getD n false = false := by
  unfold prefixInput
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem prefixInput_n1 (n : ℕ) (l : Fin (n + 1)) :
    (prefixInput n l).getD (n + 1) false = true := by
  unfold prefixInput
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

def vl (n : ℕ) (gs : List Gate) (u : ℕ) (l : Fin (n + 1)) : Bool :=
  (W gs (prefixInput n l)).getD u false

def isNotGate (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

theorem isNotGate_eq_true (g : Gate) : isNotGate g = true ↔ g.op = GateOp.not := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNotGate]

theorem isNotGate_eq_false (g : Gate) : isNotGate g = false ↔ g.op ≠ GateOp.not := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNotGate]

def nonNotCount (gs : List Gate) : ℕ := (gs.filter fun g => !isNotGate g).length

theorem filter_split (p : Gate → Bool) (l : List Gate) :
    (l.filter p).length + (l.filter fun g => !p g).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h] <;> omega

theorem notCount_eq_filter (C : Circuit) :
    PEqualNP.NotBracket.notCount C = (C.gates.filter isNotGate).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNotGate]

theorem notCount_add_nonNotCount (C : Circuit) :
    PEqualNP.NotBracket.notCount C + nonNotCount C.gates = C.size := by
  rw [notCount_eq_filter]
  exact filter_split isNotGate C.gates

theorem nonNotCount_append (gs hs : List Gate) :
    nonNotCount (gs ++ hs) = nonNotCount gs + nonNotCount hs := by
  simp [nonNotCount, List.filter_append]

theorem notCount_append (gs hs : List Gate) (o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs ++ hs, o⟩ =
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + PEqualNP.NotBracket.notCount ⟨hs, 0⟩ := by
  rw [notCount_eq_filter, notCount_eq_filter, notCount_eq_filter]
  simp [List.filter_append]

theorem readsBack_of_append {m : ℕ} {gs hs : List Gate}
    (h1 : PEqualNP.MetaComplexity.NestedCover.ReadsBack m ⟨gs, 0⟩)
    (h2 : ∀ k < hs.length, ∀ i ∈ (hs.getD k ⟨GateOp.or, []⟩).inputs, i < m + gs.length + k) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack m ⟨gs ++ hs, 0⟩ := by
  intro j hj i hi
  simp only [List.length_append] at hj
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
  by_cases hlt : j < gs.length
  · have hget : (gs ++ hs).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
      List.getD_append _ _ _ _ hlt
    rw [hget] at hi
    exact h1 j hlt i hi
  · have hge : gs.length ≤ j := Nat.le_of_not_lt hlt
    have hk : j - gs.length < hs.length := by omega
    have hget : (gs ++ hs).getD j ⟨GateOp.or, []⟩ = hs.getD (j - gs.length) ⟨GateOp.or, []⟩ :=
      List.getD_append_right _ _ _ _ hge
    rw [hget] at hi
    have := h2 (j - gs.length) hk i hi
    omega

theorem readsBack_snoc {m : ℕ} {gs : List Gate} {g : Gate}
    (h1 : PEqualNP.MetaComplexity.NestedCover.ReadsBack m ⟨gs, 0⟩)
    (h2 : ∀ i ∈ g.inputs, i < m + gs.length) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack m ⟨gs ++ [g], 0⟩ := by
  apply readsBack_of_append h1
  intro k hk i hi
  have hk0 : k = 0 := by simp at hk; omega
  subst hk0
  simp at hi
  exact Nat.lt_of_lt_of_le (h2 i hi) (by omega)

theorem fanInTwo_append {gs hs : List Gate}
    (h1 : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (h2 : PEqualNP.MetaComplexity.FanInTwo ⟨hs, 0⟩) :
    PEqualNP.MetaComplexity.FanInTwo ⟨gs ++ hs, 0⟩ := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · exact h1 g hg
  · exact h2 g hg

def chg {n : ℕ} (f : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i.castSucc ≠ f i.succ

def falls {n : ℕ} (f : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i.castSucc = true ∧ f i.succ = false

def rises {n : ℕ} (f : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i.castSucc = false ∧ f i.succ = true

theorem mem_chg {n : ℕ} (f : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ chg f ↔ f i.castSucc ≠ f i.succ := by simp [chg]

theorem mem_falls {n : ℕ} (f : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ falls f ↔ f i.castSucc = true ∧ f i.succ = false := by simp [falls]

theorem mem_rises {n : ℕ} (f : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ rises f ↔ f i.castSucc = false ∧ f i.succ = true := by simp [rises]

theorem chg_const {n : ℕ} {f : Fin (n + 1) → Bool} (h : ∀ t t', f t = f t') : chg f = ∅ := by
  ext i; rw [mem_chg]; simp [h i.castSucc i.succ]

theorem chg_congr {n : ℕ} {f g : Fin (n + 1) → Bool}
    (h : (∀ t, g t = f t) ∨ (∀ t, g t = !f t)) : chg g = chg f := by
  ext i; rw [mem_chg, mem_chg]
  rcases h with h | h
  · rw [h, h]
  · rw [h, h]; cases f i.castSucc <;> cases f i.succ <;> simp

theorem falls_not_eq_rises {n : ℕ} (f : Fin (n + 1) → Bool) :
    falls (fun t => !f t) = rises f := by
  ext i; rw [mem_falls, mem_rises]
  cases f i.castSucc <;> cases f i.succ <;> simp

theorem falls_congr {n : ℕ} {f g : Fin (n + 1) → Bool} (h : ∀ t, g t = f t) :
    falls g = falls f := by
  ext i; rw [mem_falls, mem_falls, h, h]

theorem falls_subset_chg {n : ℕ} (f : Fin (n + 1) → Bool) : falls f ⊆ chg f := by
  intro i hi; rw [mem_falls] at hi; rw [mem_chg]; rw [hi.1, hi.2]; decide

theorem rises_le_falls_succ {n : ℕ} (f : Fin (n + 1) → Bool) :
    (rises f).card ≤ (falls f).card + 1 := by
  have key : ∀ (k : ℕ) (hk : k ≤ n),
      ((falls f).filter fun i => i.val < k).card + (f ⟨k, by omega⟩).toNat =
      ((rises f).filter fun i => i.val < k).card + (f ⟨0, by omega⟩).toNat := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h1 : (falls f).filter (fun i => i.val < 0) = ∅ := by ext i; simp
      have h2 : (rises f).filter (fun i => i.val < 0) = ∅ := by ext i; simp
      rw [h1, h2]
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      let idx : Fin n := ⟨k, by omega⟩
      have hcs : idx.castSucc = ⟨k, by omega⟩ := rfl
      have hsc : idx.succ = ⟨k + 1, by omega⟩ := rfl
      have hfsplit : (falls f).filter (fun i => i.val < k + 1) =
          if idx ∈ falls f then insert idx ((falls f).filter (fun i => i.val < k))
          else (falls f).filter (fun i => i.val < k) := by
        split_ifs with hm
        · ext i; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact Or.inr ⟨hi, hlt⟩
            · exact Or.inl (Fin.ext heq)
          · rintro (rfl | ⟨hi, hlt⟩)
            · exact ⟨hm, Nat.lt_succ_self k⟩
            · exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
        · ext i; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact ⟨hi, hlt⟩
            · exfalso; exact hm ((Fin.ext heq : i = idx) ▸ hi)
          · rintro ⟨hi, hlt⟩; exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
      have hrsplit : (rises f).filter (fun i => i.val < k + 1) =
          if idx ∈ rises f then insert idx ((rises f).filter (fun i => i.val < k))
          else (rises f).filter (fun i => i.val < k) := by
        split_ifs with hm
        · ext i; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact Or.inr ⟨hi, hlt⟩
            · exact Or.inl (Fin.ext heq)
          · rintro (rfl | ⟨hi, hlt⟩)
            · exact ⟨hm, Nat.lt_succ_self k⟩
            · exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
        · ext i; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact ⟨hi, hlt⟩
            · exfalso; exact hm ((Fin.ext heq : i = idx) ▸ hi)
          · rintro ⟨hi, hlt⟩; exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
      have hnf : idx ∉ (falls f).filter (fun i => i.val < k) := by simp [idx]
      have hnr : idx ∉ (rises f).filter (fun i => i.val < k) := by simp [idx]
      rw [hfsplit, hrsplit]
      have hmf : idx ∈ falls f ↔ f ⟨k, by omega⟩ = true ∧ f ⟨k + 1, by omega⟩ = false := by
        rw [mem_falls, hcs, hsc]
      have hmr : idx ∈ rises f ↔ f ⟨k, by omega⟩ = false ∧ f ⟨k + 1, by omega⟩ = true := by
        rw [mem_rises, hcs, hsc]
      cases h1 : f ⟨k, by omega⟩ <;> cases h2 : f ⟨k + 1, by omega⟩ <;>
        simp [hmf, hmr, h1, h2, Finset.card_insert_of_notMem hnf,
          Finset.card_insert_of_notMem hnr] at hprev ⊢ <;> omega
  have htop := key n (le_refl n)
  have hf : (falls f).filter (fun i => i.val < n) = falls f := by
    ext i; simp [i.isLt]
  have hr : (rises f).filter (fun i => i.val < n) = rises f := by
    ext i; simp [i.isLt]
  rw [hf, hr] at htop
  cases hlast : f ⟨n, by omega⟩ <;> cases hzero : f ⟨0, by omega⟩ <;>
    simp [hlast, hzero] at htop <;> omega

theorem eq_or_not_of_chg_eq {n : ℕ} {f g : Fin (n + 1) → Bool} (h : chg f = chg g) :
    (∀ l, f l = g l) ∨ (∀ l, f l = !g l) := by
  have step : ∀ (k : ℕ) (hk : k < n + 1),
      (f ⟨0, by omega⟩ = g ⟨0, by omega⟩ → f ⟨k, hk⟩ = g ⟨k, hk⟩) ∧
      (f ⟨0, by omega⟩ ≠ g ⟨0, by omega⟩ → f ⟨k, hk⟩ = !g ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun h0 => h0, fun h0 => ?_⟩
      cases hf : f ⟨0, by omega⟩ <;> cases hg : g ⟨0, by omega⟩ <;> simp_all
    | succ k ih =>
      intro hk
      have ⟨ih1, ih2⟩ := ih (by omega)
      let i : Fin n := ⟨k, by omega⟩
      have hch : (f i.castSucc ≠ f i.succ) ↔ (g i.castSucc ≠ g i.succ) := by
        have := Finset.ext_iff.1 h i
        simpa [mem_chg] using this
      have hcs : i.castSucc = ⟨k, by omega⟩ := rfl
      have hsc : i.succ = ⟨k + 1, hk⟩ := rfl
      rw [hcs, hsc] at hch
      refine ⟨fun h0 => ?_, fun h0 => ?_⟩
      · have hprev := ih1 h0
        cases hf1 : f ⟨k, by omega⟩ <;> cases hf2 : f ⟨k + 1, hk⟩ <;>
          cases hg2 : g ⟨k + 1, hk⟩ <;> simp_all
      · have hprev := ih2 h0
        cases hf1 : f ⟨k, by omega⟩ <;> cases hf2 : f ⟨k + 1, hk⟩ <;>
          cases hg1 : g ⟨k, by omega⟩ <;> cases hg2 : g ⟨k + 1, hk⟩ <;> simp_all
  by_cases h0 : f ⟨0, by omega⟩ = g ⟨0, by omega⟩
  · exact Or.inl fun l => (step l.val l.isLt).1 h0
  · exact Or.inr fun l => (step l.val l.isLt).2 h0

theorem const_of_chg_empty {n : ℕ} {f : Fin (n + 1) → Bool} (h : chg f = ∅) :
    ∀ t t', f t = f t' := by
  have h0 : ∀ (k : ℕ) (hk : k < n + 1), f ⟨k, hk⟩ = f ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hnc : (⟨k, by omega⟩ : Fin n) ∉ chg f := by rw [h]; exact Finset.notMem_empty _
      rw [mem_chg] at hnc
      have heq : f ⟨k, by omega⟩ = f ⟨k + 1, hk⟩ := not_not.1 hnc
      rw [← heq, ih (by omega)]
  intro t t'
  rw [h0 t.val t.isLt, h0 t'.val t'.isLt]

theorem const_after_max {n : ℕ} {f : Fin (n + 1) → Bool} {m : Fin n}
    (hm : ∀ i ∈ chg f, i ≤ m) :
    ∀ l : Fin (n + 1), m.val < l.val → f l = f m.succ := by
  have step : ∀ (d : ℕ) (hd : m.val + 1 + d < n + 1),
      f ⟨m.val + 1 + d, hd⟩ = f m.succ := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      let idx : Fin n := ⟨m.val + 1 + d, by omega⟩
      have hnc : idx ∉ chg f := by
        intro hmem
        have := hm idx hmem
        change idx.val ≤ m.val at this
        simp [idx] at this
        omega
      rw [mem_chg] at hnc
      have heq : f idx.castSucc = f idx.succ := not_not.1 hnc
      have h1 : idx.castSucc = ⟨m.val + 1 + d, by omega⟩ := rfl
      have h2 : idx.succ = ⟨m.val + 1 + (d + 1), hd⟩ := by ext; simp [idx]; omega
      rw [h1, h2] at heq
      rw [← heq, ih (by omega)]
  intro l hl
  have hval : l = ⟨m.val + 1 + (l.val - (m.val + 1)), by omega⟩ := by ext; simp; omega
  rw [hval]
  exact step (l.val - (m.val + 1)) (by omega)

theorem const_before_min {n : ℕ} {f : Fin (n + 1) → Bool} {m : Fin n}
    (hm : ∀ i ∈ chg f, m ≤ i) :
    ∀ l : Fin (n + 1), l.val ≤ m.val → f l = f m.castSucc := by
  have step : ∀ (d : ℕ) (hd : d ≤ m.val),
      f ⟨m.val - d, by omega⟩ = f m.castSucc := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      let idx : Fin n := ⟨m.val - (d + 1), by omega⟩
      have hnc : idx ∉ chg f := by
        intro hmem
        have := hm idx hmem
        change m.val ≤ idx.val at this
        simp [idx] at this
        omega
      rw [mem_chg] at hnc
      have heq : f idx.castSucc = f idx.succ := not_not.1 hnc
      have h1 : idx.castSucc = ⟨m.val - (d + 1), by omega⟩ := rfl
      have h2 : idx.succ = ⟨m.val - d, by omega⟩ := by ext; simp [idx]; omega
      rw [h1, h2] at heq
      rw [heq, ih (by omega)]
  intro l hl
  have hval : l = ⟨m.val - (m.val - l.val), by omega⟩ := by ext; simp; omega
  rw [hval]
  exact step (m.val - l.val) (by omega)

theorem bool_and_sub (x y c d : Bool) : (x && c) ≠ (y && d) → x ≠ y ∨ c ≠ d := by
  revert x y c d; decide

theorem bool_or_sub (x y c d : Bool) : (x || c) ≠ (y || d) → x ≠ y ∨ c ≠ d := by
  revert x y c d; decide

theorem bool_and_l (x y c : Bool) : (x && c) ≠ (y && c) → (x && c) = x := by
  revert x y c; decide

theorem bool_or_l (x y c : Bool) : (x || c) ≠ (y || c) → (x || c) = x := by
  revert x y c; decide

theorem bool_and_r (x c d : Bool) : (x && c) ≠ (x && d) → (x && c) = c := by
  revert x c d; decide

theorem bool_or_r (x c d : Bool) : (x || c) ≠ (x || d) → (x || c) = c := by
  revert x c d; decide

theorem bin_sub {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) : chg f ⊆ chg a ∪ chg b := by
  intro i hi
  rw [Finset.mem_union, mem_chg, mem_chg]
  rw [mem_chg] at hi
  rcases hop with h | h
  · rw [h, h] at hi; exact bool_and_sub _ _ _ _ hi
  · rw [h, h] at hi; exact bool_or_sub _ _ _ _ hi

theorem bin_left {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) (i : Fin n)
    (hi : i ∈ chg f) (hb : i ∉ chg b) : f i.castSucc = a i.castSucc ∧ f i.succ = a i.succ := by
  rw [mem_chg] at hi hb
  have hb' : b i.castSucc = b i.succ := not_not.1 hb
  have h1 : f i.castSucc = a i.castSucc := by
    rcases hop with h | h
    · rw [h, h, ← hb'] at hi; rw [h]; exact bool_and_l _ _ _ hi
    · rw [h, h, ← hb'] at hi; rw [h]; exact bool_or_l _ _ _ hi
  have h2 : f i.succ = a i.succ := by
    rcases hop with h | h
    · rw [h, h, hb'] at hi; rw [h]; exact bool_and_l _ _ _ hi.symm
    · rw [h, h, hb'] at hi; rw [h]; exact bool_or_l _ _ _ hi.symm
  exact ⟨h1, h2⟩

theorem bin_right {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t))) (i : Fin n)
    (hi : i ∈ chg f) (ha : i ∉ chg a) : f i.castSucc = b i.castSucc ∧ f i.succ = b i.succ := by
  rw [mem_chg] at hi ha
  have ha' : a i.castSucc = a i.succ := not_not.1 ha
  have h1 : f i.castSucc = b i.castSucc := by
    rcases hop with h | h
    · rw [h, h, ← ha'] at hi; rw [h]; exact bool_and_r _ _ _ hi
    · rw [h, h, ← ha'] at hi; rw [h]; exact bool_or_r _ _ _ hi
  have h2 : f i.succ = b i.succ := by
    rcases hop with h | h
    · rw [h, h, ha'] at hi; rw [h]; exact bool_and_r _ _ _ hi.symm
    · rw [h, h, ha'] at hi; rw [h]; exact bool_or_r _ _ _ hi.symm
  exact ⟨h1, h2⟩

theorem bin_falls_union {n : ℕ} {f a b : Fin (n + 1) → Bool}
    (hop : (∀ t, f t = (a t && b t)) ∨ (∀ t, f t = (a t || b t)))
    (hdisj : Disjoint (chg a) (chg b)) (hunion : chg f = chg a ∪ chg b) :
    falls f = falls a ∪ falls b ∧ Disjoint (falls a) (falls b) := by
  have hd : Disjoint (falls a) (falls b) :=
    hdisj.mono (falls_subset_chg a) (falls_subset_chg b)
  refine ⟨?_, hd⟩
  ext i
  rw [Finset.mem_union, mem_falls, mem_falls, mem_falls]
  by_cases ha : i ∈ chg a
  · have hb : i ∉ chg b := Finset.disjoint_left.1 hdisj ha
    have hf : i ∈ chg f := by rw [hunion]; exact Finset.mem_union_left _ ha
    have ⟨h1, h2⟩ := bin_left hop i hf hb
    have hnb : ¬(b i.castSucc = true ∧ b i.succ = false) := by
      rintro ⟨hb1, hb2⟩; exact hb (by rw [mem_chg, hb1, hb2]; decide)
    rw [h1, h2]; simp [hnb]
  · by_cases hb : i ∈ chg b
    · have hf : i ∈ chg f := by rw [hunion]; exact Finset.mem_union_right _ hb
      have ⟨h1, h2⟩ := bin_right hop i hf ha
      have hna : ¬(a i.castSucc = true ∧ a i.succ = false) := by
        rintro ⟨ha1, ha2⟩; exact ha (by rw [mem_chg, ha1, ha2]; decide)
      rw [h1, h2]; simp [hna]
    · have hnf : i ∉ chg f := by rw [hunion, Finset.mem_union]; tauto
      have h1 : ¬(f i.castSucc = true ∧ f i.succ = false) := by
        rintro ⟨e1, e2⟩; exact hnf (by rw [mem_chg, e1, e2]; decide)
      have h2 : ¬(a i.castSucc = true ∧ a i.succ = false) := by
        rintro ⟨e1, e2⟩; exact ha (by rw [mem_chg, e1, e2]; decide)
      have h3 : ¬(b i.castSucc = true ∧ b i.succ = false) := by
        rintro ⟨e1, e2⟩; exact hb (by rw [mem_chg, e1, e2]; decide)
      simp [h1, h2, h3]

def Lam {n : ℕ} (A B : Finset (Fin n)) : Prop := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

def blk {n : ℕ} (cls : Fin n → ℕ) (c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => cls j = c

theorem mem_blk {n : ℕ} (cls : Fin n → ℕ) (c : ℕ) (j : Fin n) :
    j ∈ blk cls c ↔ cls j = c := by simp [blk]

def maxFalls {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (S : Finset (Fin n)) : ℕ :=
  ((Finset.range K).filter fun u => chg (F u) = S).sup fun u => (falls (F u)).card

theorem falls_le_maxFalls {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K u : ℕ) (S : Finset (Fin n))
    (hu : u < K) (hS : chg (F u) = S) :
    (falls (F u)).card ≤ maxFalls F K S := by
  apply Finset.le_sup (f := fun v => (falls (F v)).card)
  simp [Finset.mem_filter, Finset.mem_range, hu, hS]

theorem maxFalls_succ_of_ne {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (S : Finset (Fin n))
    (hne : chg (F K) ≠ S) :
    maxFalls F (K + 1) S = maxFalls F K S := by
  unfold maxFalls
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff_lt_or_eq]
  constructor
  · rintro ⟨hu | rfl, hS⟩
    · exact ⟨hu, hS⟩
    · exact absurd hS hne
  · rintro ⟨hu, hS⟩
    exact ⟨Or.inl hu, hS⟩

theorem maxFalls_succ_le {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (S : Finset (Fin n))
    (m : ℕ) (h1 : maxFalls F K S ≤ m) (h2 : chg (F K) = S → (falls (F K)).card ≤ m) :
    maxFalls F (K + 1) S ≤ m := by
  apply Finset.sup_le
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff_lt_or_eq] at hu
  rcases hu.1 with hlt | rfl
  · exact le_trans (falls_le_maxFalls F K u S hlt hu.2) h1
  · exact h2 hu.2

theorem maxFalls_succ_eq_of_unique {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (S : Finset (Fin n))
    (hnone : ∀ u < K, chg (F u) ≠ S) (hK : chg (F K) = S) :
    maxFalls F (K + 1) S = (falls (F K)).card := by
  have hset : (Finset.range (K + 1)).filter (fun u => chg (F u) = S) = {K} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.lt_succ_iff_lt_or_eq]
    constructor
    · rintro ⟨hlt | rfl, hS⟩
      · exact absurd hS (hnone u hlt)
      · rfl
    · rintro rfl; exact ⟨Or.inr rfl, hK⟩
  unfold maxFalls
  rw [hset]
  simp

def GoodWire {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (u : ℕ) : Prop :=
  (∀ t t', F u t = F u t') ∨
  (∃ a < u, (∀ t, F u t = F a t) ∨ (∀ t, F u t = !F a t)) ∨
  (∃ a < u, ∃ b < u, (chg (F a)).Nonempty ∧ (chg (F b)).Nonempty ∧
    Disjoint (chg (F a)) (chg (F b)) ∧ chg (F u) = chg (F a) ∪ chg (F b) ∧
    ((∀ t, F u t = (F a t && F b t)) ∨ (∀ t, F u t = (F a t || F b t))))

def Str {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (cls : Fin n → ℕ) (Q : ℕ) : Prop :=
  (∀ u < K, ∀ v < K, Lam (chg (F u)) (chg (F v))) ∧
  (∀ u, n + 2 ≤ u → u < K → GoodWire F u) ∧
  (∑ c ∈ Finset.univ.image cls, maxFalls F K (blk cls c) ≤ Q)

def Inv {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K P Q : ℕ) : Prop :=
  ∃ cls : Fin n → ℕ,
    (∀ u < K, ∀ i ∈ chg (F u), ∀ j ∈ chg (F u), cls i = cls j) ∧
    n ≤ (Finset.univ.image cls).card + P ∧
    ((n = (Finset.univ.image cls).card + P ∧
        ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i)) → Str F K cls Q)

theorem Inv.congr {n : ℕ} {F F' : ℕ → Fin (n + 1) → Bool} {K P Q : ℕ}
    (h : ∀ u < K, F' u = F u) (hI : Inv F K P Q) : Inv F' K P Q := by
  obtain ⟨cls, hW, hN, hS⟩ := hI
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu; rw [h u hu]; exact hW u hu
  · rintro ⟨heq, hfull⟩
    obtain ⟨hlam, hgood, hfalls⟩ := hS ⟨heq, fun i => by
      obtain ⟨u, hu, hue⟩ := hfull i
      exact ⟨u, hu, by rw [← h u hu]; exact hue⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv; rw [h u hu, h v hv]; exact hlam u hu v hv
    · intro u hlo hhi
      have hg := hgood u hlo hhi
      rcases hg with hc | ⟨a, ha, hs⟩ | ⟨a, ha, b, hb, hna, hnb, hdj, hun, hop⟩
      · exact Or.inl fun t t' => by rw [h u hhi]; exact hc t t'
      · refine Or.inr (Or.inl ⟨a, ha, ?_⟩)
        rcases hs with hs | hs
        · exact Or.inl fun t => by rw [h u hhi, h a (lt_trans ha hhi)]; exact hs t
        · exact Or.inr fun t => by rw [h u hhi, h a (lt_trans ha hhi)]; exact hs t
      · refine Or.inr (Or.inr ⟨a, ha, b, hb, ?_, ?_, ?_, ?_, ?_⟩)
        · rw [h a (lt_trans ha hhi)]; exact hna
        · rw [h b (lt_trans hb hhi)]; exact hnb
        · rw [h a (lt_trans ha hhi), h b (lt_trans hb hhi)]; exact hdj
        · rw [h u hhi, h a (lt_trans ha hhi), h b (lt_trans hb hhi)]; exact hun
        · rcases hop with hop | hop
          · exact Or.inl fun t => by rw [h u hhi, h a (lt_trans ha hhi), h b (lt_trans hb hhi)]; exact hop t
          · exact Or.inr fun t => by rw [h u hhi, h a (lt_trans ha hhi), h b (lt_trans hb hhi)]; exact hop t
    · have hmf : ∀ S, maxFalls F' K S = maxFalls F K S := by
        intro S
        unfold maxFalls
        have hfilt : (Finset.range K).filter (fun u => chg (F' u) = S) =
            (Finset.range K).filter (fun u => chg (F u) = S) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_range]
          constructor <;> rintro ⟨hu, hS⟩ <;> refine ⟨hu, ?_⟩
          · rwa [← h u hu]
          · rwa [h u hu]
        rw [hfilt]
        apply Finset.sup_congr rfl
        intro u hu
        have hlt : u < K := Finset.mem_range.1 (Finset.mem_filter.1 hu).1
        rw [h u hlt]
      simpa [hmf] using hfalls

theorem Inv.const_slack {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q : ℕ}
    (hc : chg (F K) = ∅) (h : Inv F K P Q) : Inv F (K + 1) (P + 1) Q := by
  obtain ⟨cls, hW, hN, -⟩ := h
  refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
  intro u hu i hi j hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
  · exact hW u hu i hi j hj
  · rw [hc] at hi; exact absurd hi (Finset.notMem_empty i)

theorem Inv.copy_slack {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q a : ℕ}
    (ha : a < K) (h : ∀ t, F K t = F a t) (hI : Inv F K P Q) : Inv F (K + 1) (P + 1) Q := by
  have hc : chg (F K) = chg (F a) := chg_congr (Or.inl h)
  obtain ⟨cls, hW, hN, -⟩ := hI
  refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
  intro u hu i hi j hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
  · exact hW u hu i hi j hj
  · rw [hc] at hi hj; exact hW a ha i hi j hj

theorem Inv.const_not {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q : ℕ}
    (hc : chg (F K) = ∅) (h : Inv F K P Q) : Inv F (K + 1) P (Q + 1) := by
  obtain ⟨cls, hW, hN, hS⟩ := h
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · exact hW u hu i hi j hj
    · rw [hc] at hi; exact absurd hi (Finset.notMem_empty i)
  · rintro ⟨heq, hfull⟩
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      obtain ⟨u, hu, hue⟩ := hfull i
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact ⟨u, hu, hue⟩
      · exfalso
        have hi : i ∈ blk cls (cls i) := (mem_blk cls _ i).2 rfl
        rw [← hue, hc] at hi
        exact Finset.notMem_empty i hi
    obtain ⟨hlam, hgood, hfalls⟩ := hS ⟨heq, hfullK⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · exact hlam u hu v hv
        · exact Or.inr (Or.inl (by rw [hc]; exact Finset.empty_subset _))
      · exact Or.inl (by rw [hc]; exact Finset.empty_subset _)
    · intro u hlo hhi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhi with hlt | rfl
      · exact hgood u hlo hlt
      · exact Or.inl (const_of_chg_empty hc)
    · have hsum : ∑ c ∈ Finset.univ.image cls, maxFalls F (K + 1) (blk cls c) =
          ∑ c ∈ Finset.univ.image cls, maxFalls F K (blk cls c) := by
        apply Finset.sum_congr rfl
        intro c hc_mem
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc_mem
        apply maxFalls_succ_of_ne
        intro he
        have hi : i ∈ blk cls (cls i) := (mem_blk cls _ i).2 rfl
        rw [← he, hc] at hi
        exact Finset.notMem_empty i hi
      rw [hsum]; omega

theorem Inv.notGate {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q a : ℕ}
    (ha : a < K) (h : ∀ t, F K t = !F a t) (hI : Inv F K P Q) : Inv F (K + 1) P (Q + 1) := by
  have hc : chg (F K) = chg (F a) := chg_congr (Or.inr h)
  obtain ⟨cls, hW, hN, hS⟩ := hI
  refine ⟨cls, ?_, hN, ?_⟩
  · intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · exact hW u hu i hi j hj
    · rw [hc] at hi hj; exact hW a ha i hi j hj
  · rintro ⟨heq, hfull⟩
    have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
      intro i
      obtain ⟨u, hu, hue⟩ := hfull i
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact ⟨u, hu, hue⟩
      · rw [hc] at hue; exact ⟨a, ha, hue⟩
    obtain ⟨hlam, hgood, hfalls⟩ := hS ⟨heq, hfullK⟩
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · exact hlam u hu v hv
        · rw [hc]; exact hlam u hu a ha
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · rw [hc]; exact hlam a ha v hv
        · exact Or.inl (Finset.Subset.refl _)
    · intro u hlo hhi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhi with hlt | rfl
      · exact hgood u hlo hlt
      · exact Or.inr (Or.inl ⟨a, ha, Or.inr h⟩)
    · by_cases hex : ∃ c ∈ Finset.univ.image cls, chg (F K) = blk cls c
      · obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := hex
        have hother : ∀ c ∈ (Finset.univ.image cls).erase c₀,
            maxFalls F (K + 1) (blk cls c) = maxFalls F K (blk cls c) := by
          intro c hc_mem
          have hne : c ≠ c₀ := (Finset.mem_erase.1 hc_mem).1
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_erase.1 hc_mem).2
          apply maxFalls_succ_of_ne
          intro he
          have hi : i ∈ blk cls (cls i) := (mem_blk cls _ i).2 rfl
          rw [← he, hc₀_eq, mem_blk] at hi
          exact hne hi
        have hc₀_le : maxFalls F (K + 1) (blk cls c₀) ≤ maxFalls F K (blk cls c₀) + 1 := by
          apply maxFalls_succ_le
          · omega
          · intro _
            have hfa : falls (F K) = rises (F a) := by
              rw [falls_congr h, falls_not_eq_rises]
            have h1 := rises_le_falls_succ (F a)
            have h2 := falls_le_maxFalls F K a (blk cls c₀) ha (hc.symm.trans hc₀_eq)
            rw [hfa]; omega
        rw [← Finset.add_sum_erase _ _ hc₀_mem]
        rw [← Finset.add_sum_erase _ _ hc₀_mem] at hfalls
        have hsum_eq : ∑ c ∈ (Finset.univ.image cls).erase c₀, maxFalls F (K + 1) (blk cls c) =
            ∑ c ∈ (Finset.univ.image cls).erase c₀, maxFalls F K (blk cls c) :=
          Finset.sum_congr rfl hother
        rw [hsum_eq]; omega
      · push_neg at hex
        have hsum : ∑ c ∈ Finset.univ.image cls, maxFalls F (K + 1) (blk cls c) =
            ∑ c ∈ Finset.univ.image cls, maxFalls F K (blk cls c) := by
          apply Finset.sum_congr rfl
          intro c hc_mem
          exact maxFalls_succ_of_ne F K (blk cls c) (hex c hc_mem)
        rw [hsum]; omega

theorem Inv.bin {n : ℕ} {F : ℕ → Fin (n + 1) → Bool} {K P Q a b : ℕ}
    (ha : a < K) (hb : b < K)
    (hop : (∀ t, F K t = (F a t && F b t)) ∨ (∀ t, F K t = (F a t || F b t)))
    (hI : Inv F K P Q) : Inv F (K + 1) (P + 1) Q := by
  have hsub : chg (F K) ⊆ chg (F a) ∪ chg (F b) := bin_sub hop
  obtain ⟨cls, hW, hN, hS⟩ := hI
  by_cases hea : (chg (F a)).Nonempty
  · by_cases heb : (chg (F b)).Nonempty
    · obtain ⟨ia, hia⟩ := hea
      obtain ⟨ib, hib⟩ := heb
      set ca := cls ia
      set cb := cls ib
      by_cases hcab : ca = cb
      · refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
        intro u hu i hi j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | heq
        · exact hW u hu i hi j hj
        · rw [heq] at hi hj
          have hmem : ∀ x ∈ chg (F K), cls x = ca := by
            intro x hx
            rcases Finset.mem_union.1 (hsub hx) with hxa | hxb
            · exact hW a ha x hxa ia hia
            · exact (hW b hb x hxb ib hib).trans hcab.symm
          rw [hmem i hi, hmem j hj]
      · let cls' : Fin n → ℕ := fun j => if cls j = cb then ca else cls j
        have himg : Finset.univ.image cls' = (Finset.univ.image cls).erase cb := by
          ext c
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
          constructor
          · rintro ⟨j, rfl⟩
            dsimp only [cls']
            split_ifs with hj
            · exact ⟨hcab, ia, rfl⟩
            · exact ⟨hj, j, rfl⟩
          · rintro ⟨hne, j, rfl⟩
            exact ⟨j, by simp [cls', hne]⟩
        have hcb_mem : cb ∈ Finset.univ.image cls :=
          Finset.mem_image.2 ⟨ib, Finset.mem_univ _, rfl⟩
        have hca_mem : ca ∈ Finset.univ.image cls :=
          Finset.mem_image.2 ⟨ia, Finset.mem_univ _, rfl⟩
        have hca_mem' : ca ∈ Finset.univ.image cls' := by
          rw [himg]; exact Finset.mem_erase.2 ⟨hcab, hca_mem⟩
        have hcard' : (Finset.univ.image cls').card + 1 = (Finset.univ.image cls).card := by
          rw [himg, Finset.card_erase_add_one hcb_mem]
        have hblk_ca : blk cls' ca = blk cls ca ∪ blk cls cb := by
          ext j
          simp only [mem_blk, Finset.mem_union, cls']
          split_ifs with hj
          · simp [hj]
          · simp [hj]
        have hblk_other : ∀ c, c ≠ ca → c ≠ cb → blk cls' c = blk cls c := by
          intro c h1 h2
          ext j
          simp only [mem_blk, cls']
          split_ifs with hj
          · simp [h1.symm, hj, h2.symm]
          · rfl
        have hsub_a : chg (F a) ⊆ blk cls ca := fun x hx =>
          (mem_blk cls ca x).2 (hW a ha x hx ia hia)
        have hsub_b : chg (F b) ⊆ blk cls cb := fun x hx =>
          (mem_blk cls cb x).2 (hW b hb x hx ib hib)
        have hdisj_ab : Disjoint (blk cls ca) (blk cls cb) := by
          rw [Finset.disjoint_left]
          intro x hxa hxb
          rw [mem_blk] at hxa hxb
          exact hcab (hxa.symm.trans hxb)
        refine ⟨cls', ?_, by omega, ?_⟩
        · intro u hu i hi j hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | heq
          · have e := hW u hu i hi j hj
            simp [cls', e]
          · rw [heq] at hi hj
            have hmem : ∀ x ∈ chg (F K), cls' x = ca := by
              intro x hx
              rcases Finset.mem_union.1 (hsub hx) with hxa | hxb
              · have := hW a ha x hxa ia hia
                dsimp only [cls']; rw [this, if_neg hcab]
              · have := hW b hb x hxb ib hib
                dsimp only [cls']; rw [this, if_pos rfl]
            rw [hmem i hi, hmem j hj]
        · rintro ⟨heq', hfull'⟩
          have hno_old : ∀ u < K, chg (F u) ≠ blk cls' ca := by
            intro u hu he
            have hi1 : ia ∈ chg (F u) := by
              rw [he, hblk_ca]; exact Finset.mem_union_left _ ((mem_blk cls ca ia).2 rfl)
            have hi2 : ib ∈ chg (F u) := by
              rw [he, hblk_ca]; exact Finset.mem_union_right _ ((mem_blk cls cb ib).2 rfl)
            exact hcab (hW u hu ia hi1 ib hi2)
          have hchgK : chg (F K) = blk cls ca ∪ blk cls cb := by
            have hcls'_ia : cls' ia = ca := by dsimp only [cls']; exact if_neg hcab
            obtain ⟨u, hu, hue⟩ := hfull' ia
            rw [hcls'_ia] at hue
            rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hlt | heq
            · exact absurd hue (hno_old u hlt)
            · rw [heq, hblk_ca] at hue; exact hue
          have hchg_a : chg (F a) = blk cls ca := by
            apply Finset.Subset.antisymm hsub_a
            intro x hx
            have hxK : x ∈ chg (F K) := by rw [hchgK]; exact Finset.mem_union_left _ hx
            rcases Finset.mem_union.1 (hsub hxK) with hxa | hxb
            · exact hxa
            · exact absurd (hsub_b hxb) (Finset.disjoint_left.1 hdisj_ab hx)
          have hchg_b : chg (F b) = blk cls cb := by
            apply Finset.Subset.antisymm hsub_b
            intro x hx
            have hxK : x ∈ chg (F K) := by rw [hchgK]; exact Finset.mem_union_right _ hx
            rcases Finset.mem_union.1 (hsub hxK) with hxa | hxb
            · exact absurd (hsub_a hxa) (Finset.disjoint_right.1 hdisj_ab hx)
            · exact hxb
          have hfullK : ∀ i : Fin n, ∃ u < K, chg (F u) = blk cls (cls i) := by
            intro i
            by_cases h1 : cls i = ca
            · rw [h1]; exact ⟨a, ha, hchg_a⟩
            · by_cases h2 : cls i = cb
              · rw [h2]; exact ⟨b, hb, hchg_b⟩
              · have hcls'_i : cls' i = cls i := by simp [cls', h2]
                obtain ⟨u, hu, hue⟩ := hfull' i
                rw [hcls'_i, hblk_other (cls i) h1 h2] at hue
                rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hlt | heq
                · exact ⟨u, hlt, hue⟩
                · exfalso
                  rw [heq] at hue
                  have hiaK : ia ∈ chg (F K) := by
                    rw [hchgK]; exact Finset.mem_union_left _ ((mem_blk cls ca ia).2 rfl)
                  rw [hue, mem_blk] at hiaK
                  exact h1 hiaK.symm
          obtain ⟨hlamK, hgoodK, hfallsK⟩ := hS ⟨by omega, hfullK⟩
          have hlam_old_K : ∀ u < K, Lam (chg (F u)) (chg (F K)) := by
            intro u hu
            by_cases heu : (chg (F u)).Nonempty
            · obtain ⟨x, hx⟩ := heu
              have hsub_u : chg (F u) ⊆ blk cls (cls x) := fun y hy =>
                (mem_blk cls (cls x) y).2 (hW u hu y hy x hx)
              by_cases hc1 : cls x = ca
              · exact Or.inl (by rw [hchgK]; exact Finset.Subset.trans hsub_u (by rw [hc1]; exact Finset.subset_union_left))
              · by_cases hc2 : cls x = cb
                · exact Or.inl (by rw [hchgK]; exact Finset.Subset.trans hsub_u (by rw [hc2]; exact Finset.subset_union_right))
                · refine Or.inr (Or.inr ?_)
                  rw [Finset.disjoint_left]
                  intro y hyu hyK
                  have hy1 : cls y = cls x := (mem_blk cls (cls x) y).1 (hsub_u hyu)
                  rw [hchgK, Finset.mem_union, mem_blk, mem_blk] at hyK
                  rcases hyK with hyK | hyK
                  · exact hc1 (hy1.symm.trans hyK)
                  · exact hc2 (hy1.symm.trans hyK)
            · rw [Finset.not_nonempty_iff_eq_empty] at heu
              exact Or.inl (by rw [heu]; exact Finset.empty_subset _)
          refine ⟨?_, ?_, ?_⟩
          · intro u hu v hv
            rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hult | rfl
            · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hvlt | rfl
              · exact hlamK u hult v hvlt
              · exact hlam_old_K u hult
            · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hvlt | rfl
              · rcases hlam_old_K v hvlt with h1 | h2 | h3
                · exact Or.inr (Or.inl h1)
                · exact Or.inl h2
                · exact Or.inr (Or.inr h3.symm)
              · exact Or.inl (Finset.Subset.refl _)
          · intro u hlo hhi
            rcases Nat.lt_succ_iff_lt_or_eq.1 hhi with hlt | rfl
            · exact hgoodK u hlo hlt
            · refine Or.inr (Or.inr ⟨a, ha, b, hb, ⟨ia, hia⟩, ⟨ib, hib⟩, ?_, ?_, hop⟩)
              · rw [hchg_a, hchg_b]; exact hdisj_ab
              · rw [hchg_a, hchg_b, hchgK]
          · have hdisj_chg : Disjoint (chg (F a)) (chg (F b)) := by
              rw [hchg_a, hchg_b]; exact hdisj_ab
            have hunion_chg : chg (F K) = chg (F a) ∪ chg (F b) := by
              rw [hchg_a, hchg_b, hchgK]
            have ⟨hfu, hfd⟩ := bin_falls_union hop hdisj_chg hunion_chg
            have hmf_ca : maxFalls F (K + 1) (blk cls' ca) ≤
                maxFalls F K (blk cls ca) + maxFalls F K (blk cls cb) := by
              rw [maxFalls_succ_eq_of_unique F K (blk cls' ca) hno_old (by rw [hblk_ca, hchgK])]
              rw [hfu, Finset.card_union_of_disjoint hfd]
              exact Nat.add_le_add
                (falls_le_maxFalls F K a (blk cls ca) ha hchg_a)
                (falls_le_maxFalls F K b (blk cls cb) hb hchg_b)
            have hmf_rest : ∑ c ∈ (Finset.univ.image cls').erase ca, maxFalls F (K + 1) (blk cls' c) =
                ∑ c ∈ ((Finset.univ.image cls).erase cb).erase ca, maxFalls F K (blk cls c) := by
              rw [himg]
              apply Finset.sum_congr rfl
              intro c hc
              have hne_a : c ≠ ca := (Finset.mem_erase.1 hc).1
              have hne_b : c ≠ cb := (Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).1
              rw [hblk_other c hne_a hne_b]
              apply maxFalls_succ_of_ne
              intro he
              have hiaK : ia ∈ chg (F K) := by
                rw [hchgK]; exact Finset.mem_union_left _ ((mem_blk cls ca ia).2 rfl)
              rw [he, mem_blk] at hiaK
              exact hne_a hiaK.symm
            rw [← Finset.add_sum_erase _ _ hca_mem', hmf_rest]
            have hca_in_erase : ca ∈ (Finset.univ.image cls).erase cb :=
              Finset.mem_erase.2 ⟨hcab, hca_mem⟩
            have hsplit_old : ∑ c ∈ Finset.univ.image cls, maxFalls F K (blk cls c) =
                maxFalls F K (blk cls cb) +
                  (maxFalls F K (blk cls ca) +
                    ∑ c ∈ ((Finset.univ.image cls).erase cb).erase ca, maxFalls F K (blk cls c)) := by
              rw [← Finset.add_sum_erase _ _ hcb_mem]
              congr 1
              rw [← Finset.add_sum_erase _ _ hca_in_erase]
            omega
    · rw [Finset.not_nonempty_iff_eq_empty] at heb
      refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
      intro u hu i hi j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · exact hW u hu i hi j hj
      · rw [heb, Finset.union_empty] at hsub
        exact hW a ha i (hsub hi) j (hsub hj)
  · rw [Finset.not_nonempty_iff_eq_empty] at hea
    refine ⟨cls, ?_, by omega, fun hp => absurd hp.1 (by omega)⟩
    intro u hu i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · exact hW u hu i hi j hj
    · rw [hea, Finset.empty_union] at hsub
      exact hW b hb i (hsub hi) j (hsub hj)

theorem chg_input_lt (n : ℕ) (u : ℕ) (hu : u < n) :
    chg (vl n [] u) = {⟨u, hu⟩} := by
  ext i
  rw [mem_chg, Finset.mem_singleton]
  simp only [vl, W_nil, prefixInput_lt n _ u hu, Fin.val_castSucc, Fin.val_succ]
  constructor
  · intro hne
    ext
    by_cases h1 : u < i.val
    · exfalso; apply hne
      have h2 : u < i.val + 1 := by omega
      simp [h1, h2]
    · by_cases h2 : u < i.val + 1
      · simp; omega
      · exfalso; apply hne; simp [h1, h2]
  · rintro rfl
    have h1 : ¬(u < u) := lt_irrefl u
    have h2 : u < u + 1 := Nat.lt_succ_self u
    simp [h1, h2]

theorem chg_input_const (n : ℕ) (u : ℕ) (hu : n ≤ u) :
    chg (vl n [] u) = ∅ := by
  apply chg_const
  intro t t'
  simp only [vl, W_nil]
  by_cases h1 : u = n
  · subst h1; rw [prefixInput_n, prefixInput_n]
  · by_cases h2 : u = n + 1
    · subst h2; rw [prefixInput_n1, prefixInput_n1]
    · rw [List.getD_eq_default _ _ (by rw [prefixInput_len]; omega),
          List.getD_eq_default _ _ (by rw [prefixInput_len]; omega)]

theorem falls_input (n : ℕ) (u : ℕ) : falls (vl n [] u) = ∅ := by
  ext i
  rw [mem_falls]
  simp only [Finset.notMem_empty, iff_false, not_and]
  by_cases hu : u < n
  · simp only [vl, W_nil, prefixInput_lt n _ u hu, Fin.val_castSucc, Fin.val_succ,
      decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · have hc := const_of_chg_empty (chg_input_const n u (Nat.le_of_not_lt hu)) i.castSucc i.succ
    rw [hc]; intro h; rw [h]; decide

theorem inv_base (n : ℕ) : Inv (vl n []) (n + 2) 0 0 := by
  let cls : Fin n → ℕ := fun i => i.val
  have hcard : (Finset.univ.image cls).card = n := by
    rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext h)]
    simp
  refine ⟨cls, ?_, by omega, ?_⟩
  · intro u _ i hi j hj
    by_cases hlt : u < n
    · rw [chg_input_lt n u hlt, Finset.mem_singleton] at hi hj
      rw [hi, hj]
    · rw [chg_input_const n u (Nat.le_of_not_lt hlt)] at hi
      exact absurd hi (Finset.notMem_empty i)
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · intro u _ v _
      by_cases hu : u < n
      · by_cases hv : v < n
        · rw [chg_input_lt n u hu, chg_input_lt n v hv]
          by_cases huv : u = v
          · subst huv; exact Or.inl (Finset.Subset.refl _)
          · refine Or.inr (Or.inr ?_)
            rw [Finset.disjoint_singleton]
            intro h; exact huv (congrArg Fin.val h)
        · rw [chg_input_const n v (Nat.le_of_not_lt hv)]
          exact Or.inr (Or.inl (Finset.empty_subset _))
      · rw [chg_input_const n u (Nat.le_of_not_lt hu)]
        exact Or.inl (Finset.empty_subset _)
    · intro u hlo hhi; omega
    · apply Finset.sum_eq_zero _ |>.le
      intro c _
      apply Nat.eq_zero_of_le_zero
      apply Finset.sup_le
      intro u _
      rw [falls_input n u]; simp

theorem inv_all (n : ℕ) (gs : List Gate)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩) :
    Inv (vl n gs) (n + 2 + gs.length) (nonNotCount gs) (PEqualNP.NotBracket.notCount ⟨gs, 0⟩) := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [notCount_eq_filter]
    simpa [nonNotCount] using inv_base n
  | append_singleton gs g ih =>
    have hF_pre : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ :=
      fun x hx => hF x (List.mem_append_left _ hx)
    have hR_pre : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ := by
      intro j hj i hi
      have hj' : j < (gs ++ [g]).length := by
        simp only [List.length_append, List.length_singleton]; exact Nat.lt_succ_of_lt hj
      have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
        List.getD_append _ _ _ _ hj
      exact hR j hj' i (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rwa [hget])
    have hI0 := ih hF_pre hR_pre
    have hcongr : ∀ u < n + 2 + gs.length, vl n (gs ++ [g]) u = vl n gs u := by
      intro u hu
      funext l
      exact old_wire gs g (prefixInput n l) u (by rw [prefixInput_len]; omega)
    have hI := Inv.congr hcongr hI0
    have hnew : ∀ l, vl n (gs ++ [g]) (n + 2 + gs.length) l =
        g.op.eval (g.inputs.map fun t => vl n gs t l) := by
      intro l
      simpa [vl, prefixInput_len] using new_wire gs g (prefixInput n l)
    have hin : ∀ a ∈ g.inputs, a < n + 2 + gs.length := by
      intro a ha
      have hj' : gs.length < (gs ++ [g]).length := by simp
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
      exact hR gs.length hj' a (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rwa [hget])
    have ⟨hgop, hglen⟩ := hF g (List.mem_append_right _ (by simp))
    have hlen : n + 2 + (gs ++ [g]).length = (n + 2 + gs.length) + 1 := by simp; omega
    rw [hlen, nonNotCount_append, notCount_append]
    by_cases hnot : g.op = GateOp.not
    · have hnn : nonNotCount [g] = 0 := by simp [nonNotCount, (isNotGate_eq_true g).2 hnot]
      have hnc : PEqualNP.NotBracket.notCount ⟨[g], 0⟩ = 1 := by
        rw [notCount_eq_filter]; simp [(isNotGate_eq_true g).2 hnot]
      rw [hnn, hnc, Nat.add_zero]
      rcases hgi : g.inputs with _ | ⟨a, rest⟩
      · apply Inv.const_not _ hI
        apply chg_const
        intro t t'
        rw [hnew, hnew, hgi, hnot]; rfl
      · have ha : a < n + 2 + gs.length := hin a (by rw [hgi]; simp)
        apply Inv.notGate ha _ hI
        intro l
        rw [hnew, hgi, hnot, hcongr a ha]
        simp [GateOp.eval]
    · have hnn : nonNotCount [g] = 1 := by simp [nonNotCount, (isNotGate_eq_false g).2 hnot]
      have hnc : PEqualNP.NotBracket.notCount ⟨[g], 0⟩ = 0 := by
        rw [notCount_eq_filter]; simp [(isNotGate_eq_false g).2 hnot]
      rw [hnn, hnc, Nat.add_zero]
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgop
        tauto
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · apply Inv.const_slack _ hI
        apply chg_const
        intro t t'
        rw [hnew, hnew, hgi]; rfl
      · have ha : a < n + 2 + gs.length := hin a (by rw [hgi]; simp)
        apply Inv.copy_slack ha _ hI
        intro l
        rw [hnew, hgi, hcongr a ha]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
      · have ha : a < n + 2 + gs.length := hin a (by rw [hgi]; simp)
        have hb : b < n + 2 + gs.length := hin b (by rw [hgi]; simp)
        apply Inv.bin ha hb _ hI
        rcases hop with h | h
        · refine Or.inl fun l => ?_
          rw [hnew, hgi, h, hcongr a ha, hcongr b hb]
          simp [GateOp.eval]
        · refine Or.inr fun l => ?_
          rw [hnew, hgi, h, hcongr a ha, hcongr b hb]
          simp [GateOp.eval]
      · rw [hgi] at hglen; simp at hglen

theorem tight_structure (n : ℕ) (hn : 0 < n) (C : Circuit) (root : ℕ)
    (hroot_lt : root < n + 2 + C.size)
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hP : C.size - PEqualNP.NotBracket.notCount C ≤ n - 1)
    (hroot : chg (vl n C.gates root) = Finset.univ) :
    (∀ u < n + 2 + C.size, ∀ v < n + 2 + C.size, Lam (chg (vl n C.gates u)) (chg (vl n C.gates v))) ∧
    (∀ u, n + 2 ≤ u → u < n + 2 + C.size → GoodWire (vl n C.gates) u) ∧
    (falls (vl n C.gates root)).card ≤ PEqualNP.NotBracket.notCount C := by
  have hInv := inv_all n C.gates hF hR
  obtain ⟨cls, hW, hN, hS⟩ := hInv
  have hsplit := notCount_add_nonNotCount C
  have hall : ∀ i j : Fin n, cls i = cls j := fun i j =>
    hW root hroot_lt i (by rw [hroot]; exact Finset.mem_univ _) j
      (by rw [hroot]; exact Finset.mem_univ _)
  have hc1 : (Finset.univ.image cls).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro c hc d hd
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hd
    exact hall i j
  have hi0 : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hc_pos : 1 ≤ (Finset.univ.image cls).card :=
    Finset.card_pos.2 ⟨cls ⟨0, hn⟩, Finset.mem_image.2 ⟨⟨0, hn⟩, hi0, rfl⟩⟩
  have hnn_le : nonNotCount C.gates ≤ n - 1 := by omega
  have heq : n = (Finset.univ.image cls).card + nonNotCount C.gates := by omega
  have hfull : ∀ i : Fin n, ∃ u < n + 2 + C.gates.length, chg (vl n C.gates u) = blk cls (cls i) := by
    intro i
    refine ⟨root, hroot_lt, ?_⟩
    rw [hroot]
    ext j; rw [mem_blk]; simp [hall j i]
  obtain ⟨hlam, hgood, hfalls⟩ := hS ⟨heq, hfull⟩
  refine ⟨hlam, hgood, ?_⟩
  have hblk0 : blk cls (cls ⟨0, hn⟩) = Finset.univ := by
    ext j; rw [mem_blk]; simp [hall j ⟨0, hn⟩]
  have hle1 : (falls (vl n C.gates root)).card ≤ maxFalls (vl n C.gates) (n + 2 + C.gates.length) (blk cls (cls ⟨0, hn⟩)) :=
    falls_le_maxFalls _ _ root _ hroot_lt (by rw [hroot, hblk0])
  have hmem0 : cls ⟨0, hn⟩ ∈ Finset.univ.image cls :=
    Finset.mem_image.2 ⟨⟨0, hn⟩, hi0, rfl⟩
  have hle2 : maxFalls (vl n C.gates) (n + 2 + C.gates.length) (blk cls (cls ⟨0, hn⟩)) ≤
      ∑ c ∈ Finset.univ.image cls, maxFalls (vl n C.gates) (n + 2 + C.gates.length) (blk cls c) :=
    Finset.single_le_sum (f := fun c => maxFalls (vl n C.gates) (n + 2 + C.gates.length) (blk cls c))
      (fun _ _ => Nat.zero_le _) hmem0
  exact le_trans hle1 (le_trans hle2 hfalls)

def colorBlock {n d : ℕ} (color : Fin n → Fin d) (j : Fin d) : Finset (Fin n) :=
  Finset.univ.filter fun i => color i = j

theorem mem_colorBlock {n d : ℕ} (color : Fin n → Fin d) (j : Fin d) (i : Fin n) :
    i ∈ colorBlock color j ↔ color i = j := by simp [colorBlock]

theorem colorBlock_nonempty {n d : ℕ} {color : Fin n → Fin d}
    (hsurj : Function.Surjective color) (j : Fin d) : (colorBlock color j).Nonempty := by
  obtain ⟨i, hi⟩ := hsurj j
  exact ⟨i, (mem_colorBlock color j i).2 hi⟩

theorem colorBlock_disjoint {n d : ℕ} (color : Fin n → Fin d) {j k : Fin d} (hne : j ≠ k) :
    Disjoint (colorBlock color j) (colorBlock color k) := by
  rw [Finset.disjoint_left]
  intro i hj hk
  rw [mem_colorBlock] at hj hk
  exact hne (hj.symm.trans hk)

theorem build_prefix_fn {n : ℕ} (f : Fin (n + 1) → Bool) (hne : (chg f).Nonempty)
    (gs : List Gate)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩) :
    ∃ (extra : List Gate) (w : ℕ),
      w < n + 2 + (gs ++ extra).length ∧
      PEqualNP.MetaComplexity.FanInTwo ⟨gs ++ extra, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs ++ extra, 0⟩ ∧
      nonNotCount extra = (chg f).card - 1 ∧
      PEqualNP.NotBracket.notCount ⟨extra, 0⟩ = (falls f).card ∧
      ∀ l, vl n (gs ++ extra) w l = f l := by
  have key : ∀ (c : ℕ) (f : Fin (n + 1) → Bool), (chg f).card = c → (chg f).Nonempty →
      ∀ (gs : List Gate),
        PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ →
        ∃ (extra : List Gate) (w : ℕ),
          w < n + 2 + (gs ++ extra).length ∧
          PEqualNP.MetaComplexity.FanInTwo ⟨gs ++ extra, 0⟩ ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs ++ extra, 0⟩ ∧
          nonNotCount extra = (chg f).card - 1 ∧
          PEqualNP.NotBracket.notCount ⟨extra, 0⟩ = (falls f).card ∧
          ∀ l, vl n (gs ++ extra) w l = f l := by
    intro c
    induction c using Nat.strongRecOn with
    | ind c ih =>
      intro f hc hne gs hF hR
      let m : Fin n := (chg f).max' hne
      have hm_mem : m ∈ chg f := Finset.max'_mem (chg f) hne
      have hm_max : ∀ i ∈ chg f, i ≤ m := fun i hi => Finset.le_max' (chg f) i hi
      by_cases hc1 : c = 1
      · have hsing : chg f = {m} := by
          obtain ⟨m', hm'⟩ := Finset.card_eq_one.1 (hc.trans hc1)
          have : m = m' := Finset.mem_singleton.1 (hm' ▸ hm_mem)
          rw [this, hm']
        have hbefore : ∀ l : Fin (n + 1), l.val ≤ m.val → f l = f m.castSucc :=
          const_before_min fun i hi => by rw [hsing, Finset.mem_singleton] at hi; rw [hi]
        have hafter : ∀ l : Fin (n + 1), m.val < l.val → f l = f m.succ :=
          const_after_max hm_max
        have hm_chg : f m.castSucc ≠ f m.succ := (mem_chg f m).1 hm_mem
        cases hf1 : f m.castSucc
        · have hf2 : f m.succ = true := by
            cases h : f m.succ
            · rw [hf1, h] at hm_chg; exact absurd rfl hm_chg
            · rfl
          have hfalls0 : falls f = ∅ := by
            ext i; simp only [Finset.notMem_empty, iff_false]
            intro hi
            have : i = m := Finset.mem_singleton.1 (hsing ▸ falls_subset_chg f hi)
            subst this
            rw [mem_falls, hf1] at hi; exact Bool.false_ne_true hi.1
          refine ⟨[], m.val, by simp; omega, by simpa using hF, by simpa using hR,
            by rw [hc, hc1]; rfl, by rw [hfalls0]; rfl, fun l => ?_⟩
          simp only [List.append_nil]
          have h0 := W_append_old [] gs (prefixInput n l) m.val (by rw [prefixInput_len]; simp; omega)
          have hv : vl n gs m.val l = decide (m.val < l.val) :=
            h0.trans (prefixInput_lt n l m.val m.isLt)
          rw [hv]
          by_cases hlt : m.val < l.val
          · rw [hafter l hlt, hf2]; simp [hlt]
          · rw [hbefore l (Nat.le_of_not_lt hlt), hf1]; simp [hlt]
        · have hf2 : f m.succ = false := by
            cases h : f m.succ
            · rfl
            · rw [hf1, h] at hm_chg; exact absurd rfl hm_chg
          have hfalls1 : falls f = {m} := by
            ext i; rw [Finset.mem_singleton]
            constructor
            · intro hi; exact Finset.mem_singleton.1 (hsing ▸ falls_subset_chg f hi)
            · rintro rfl; rw [mem_falls]; exact ⟨hf1, hf2⟩
          let gnot : Gate := ⟨GateOp.not, [m.val]⟩
          refine ⟨[gnot], n + 2 + gs.length, by simp, ?_, ?_,
            by rw [hc, hc1]; rfl,
            by rw [hfalls1, notCount_eq_filter]; rfl, fun l => ?_⟩
          · apply fanInTwo_append hF
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gnot]
          · apply readsBack_snoc hR
            intro i hi; simp only [gnot, List.mem_singleton] at hi; subst hi; omega
          · have hnw := new_wire gs gnot (prefixInput n l)
            rw [prefixInput_len] at hnw
            change (W (gs ++ [gnot]) (prefixInput n l)).getD (n + 2 + gs.length) false = f l
            rw [hnw]
            have h0 := W_append_old [] gs (prefixInput n l) m.val (by rw [prefixInput_len]; simp; omega)
            have hv : (W gs (prefixInput n l)).getD m.val false = decide (m.val < l.val) :=
              h0.trans (prefixInput_lt n l m.val m.isLt)
            simp only [gnot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hv]
            by_cases hlt : m.val < l.val
            · rw [hafter l hlt, hf2]; simp [hlt]
            · rw [hbefore l (Nat.le_of_not_lt hlt), hf1]; simp [hlt]
      · have hc2 : 2 ≤ c := by
          have := Finset.card_pos.2 hne; omega
        let f' : Fin (n + 1) → Bool := fun l => if l.val ≤ m.val then f l else f m.castSucc
        have hchg_f' : chg f' = (chg f).erase m := by
          ext i
          rw [mem_chg, Finset.mem_erase, mem_chg]
          by_cases hlt : i.val < m.val
          · have h1 : i.castSucc.val ≤ m.val := by simp [Fin.val_castSucc]; omega
            have h2 : i.succ.val ≤ m.val := by simp [Fin.val_succ]; omega
            have hne_im : i ≠ m := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
            simp only [f', h1, h2, ↓reduceIte]; exact ⟨fun h => ⟨hne_im, h⟩, fun h => h.2⟩
          · by_cases heq : i = m
            · subst heq
              have h1 : m.castSucc.val ≤ m.val := le_refl _
              have h2 : ¬(m.succ.val ≤ m.val) := by simp
              simp only [f', h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, false_and]
            · have hgt : m.val < i.val := by
                have : i.val ≠ m.val := fun h => heq (Fin.ext h)
                omega
              have h1 : ¬(i.castSucc.val ≤ m.val) := by simp [Fin.val_castSucc]; omega
              have h2 : ¬(i.succ.val ≤ m.val) := by simp [Fin.val_succ]; omega
              have hnf : f i.castSucc = f i.succ := by
                by_contra h
                have := hm_max i ((mem_chg f i).2 h)
                change i.val ≤ m.val at this
                omega
              simp only [f', h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, hnf, and_false]
        have hfalls_f' : falls f' = (falls f).erase m := by
          ext i
          rw [mem_falls, Finset.mem_erase, mem_falls]
          by_cases hlt : i.val < m.val
          · have h1 : i.castSucc.val ≤ m.val := by simp [Fin.val_castSucc]; omega
            have h2 : i.succ.val ≤ m.val := by simp [Fin.val_succ]; omega
            have hne_im : i ≠ m := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
            simp only [f', h1, h2, ↓reduceIte]; exact ⟨fun h => ⟨hne_im, h⟩, fun h => h.2⟩
          · by_cases heq : i = m
            · subst heq
              have h1 : m.castSucc.val ≤ m.val := le_refl _
              have h2 : ¬(m.succ.val ≤ m.val) := by simp
              simp only [f', h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, false_and, iff_false, not_and]
              intro h; rw [h]; decide
            · have hgt : m.val < i.val := by
                have : i.val ≠ m.val := fun h => heq (Fin.ext h)
                omega
              have h1 : ¬(i.castSucc.val ≤ m.val) := by simp [Fin.val_castSucc]; omega
              have h2 : ¬(i.succ.val ≤ m.val) := by simp [Fin.val_succ]; omega
              have hnf : f i.castSucc = f i.succ := by
                by_contra h
                have := hm_max i ((mem_chg f i).2 h)
                change i.val ≤ m.val at this
                omega
              simp only [f', h1, h2, ↓reduceIte, ne_eq, heq, not_false_eq_true, true_and, hnf]
              constructor <;> rintro ⟨e1, e2⟩ <;> rw [e1] at e2 <;> exact absurd e2 (by decide)
        have hcard_f' : (chg f').card = c - 1 := by
          rw [hchg_f', Finset.card_erase_of_mem hm_mem, hc]
        have hne_f' : (chg f').Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨e1, w1, hw1_lt, hF1, hR1, hnn1, hnc1, hval1⟩ :=
          ih (c - 1) (by omega) f' hcard_f' hne_f' gs hF hR
        have hafter : ∀ l : Fin (n + 1), m.val < l.val → f l = f m.succ :=
          const_after_max hm_max
        have hm_chg : f m.castSucc ≠ f m.succ := (mem_chg f m).1 hm_mem
        cases hf1 : f m.castSucc
        · have hf2 : f m.succ = true := by
            cases h : f m.succ
            · rw [hf1, h] at hm_chg; exact absurd rfl hm_chg
            · rfl
          have hm_nf : m ∉ falls f := by rw [mem_falls, hf1]; simp
          let gor : Gate := ⟨GateOp.or, [w1, m.val]⟩
          refine ⟨e1 ++ [gor], n + 2 + (gs ++ e1).length, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [← List.append_assoc]; simp
          · rw [← List.append_assoc]
            apply fanInTwo_append hF1
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gor]
          · rw [← List.append_assoc]
            apply readsBack_snoc hR1
            intro i hi
            simp only [gor, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · exact hw1_lt
            · omega
          · rw [nonNotCount_append, hnn1, hcard_f', hc]
            have h1 : nonNotCount [gor] = 1 := by simp [nonNotCount, isNotGate, gor]
            omega
          · rw [notCount_append, hnc1, hfalls_f', Finset.erase_eq_of_notMem hm_nf, notCount_eq_filter]
            simp [isNotGate, gor]
          · intro l
            rw [← List.append_assoc]
            have hnw := new_wire (gs ++ e1) gor (prefixInput n l)
            rw [prefixInput_len] at hnw
            change (W ((gs ++ e1) ++ [gor]) (prefixInput n l)).getD (n + 2 + (gs ++ e1).length) false = f l
            rw [hnw]
            have hm_val : (W (gs ++ e1) (prefixInput n l)).getD m.val false = decide (m.val < l.val) := by
              have h0 := W_append_old [] (gs ++ e1) (prefixInput n l) m.val (by rw [prefixInput_len]; simp; omega)
              exact h0.trans (prefixInput_lt n l m.val m.isLt)
            have hw1_val : (W (gs ++ e1) (prefixInput n l)).getD w1 false = f' l := hval1 l
            simp only [gor, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hw1_val, hm_val]
            by_cases hlt : m.val < l.val
            · rw [hafter l hlt, hf2]; simp [hlt]
            · have hle : l.val ≤ m.val := Nat.le_of_not_lt hlt
              simp [f', hle, hlt]
        · have hf2 : f m.succ = false := by
            cases h : f m.succ
            · rfl
            · rw [hf1, h] at hm_chg; exact absurd rfl hm_chg
          have hm_fl : m ∈ falls f := (mem_falls f m).2 ⟨hf1, hf2⟩
          let wnot := n + 2 + (gs ++ e1).length
          let gnot : Gate := ⟨GateOp.not, [m.val]⟩
          let gand : Gate := ⟨GateOp.and, [w1, wnot]⟩
          have hF2 : PEqualNP.MetaComplexity.FanInTwo ⟨(gs ++ e1) ++ [gnot], 0⟩ := by
            apply fanInTwo_append hF1
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gnot]
          have hR2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨(gs ++ e1) ++ [gnot], 0⟩ := by
            apply readsBack_snoc hR1
            intro i hi; simp only [gnot, List.mem_singleton] at hi; subst hi; omega
          refine ⟨e1 ++ [gnot, gand], n + 2 + ((gs ++ e1) ++ [gnot]).length, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · have hlen : gs ++ (e1 ++ [gnot, gand]) = ((gs ++ e1) ++ [gnot]) ++ [gand] := by simp [List.append_assoc]
            rw [hlen]; simp
          · have hlen : gs ++ (e1 ++ [gnot, gand]) = ((gs ++ e1) ++ [gnot]) ++ [gand] := by simp [List.append_assoc]
            rw [hlen]
            apply fanInTwo_append hF2
            intro x hx; simp only [List.mem_singleton] at hx; subst hx; simp [gand]
          · have hlen : gs ++ (e1 ++ [gnot, gand]) = ((gs ++ e1) ++ [gnot]) ++ [gand] := by simp [List.append_assoc]
            rw [hlen]
            apply readsBack_snoc hR2
            intro i hi
            simp only [gand, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · simp only [List.length_append, List.length_singleton] at hw1_lt ⊢; omega
            · simp [wnot]
          · rw [nonNotCount_append, hnn1, hcard_f', hc]
            have h1 : nonNotCount [gnot, gand] = 1 := rfl
            omega
          · rw [notCount_append, hnc1, hfalls_f']
            have h1 : PEqualNP.NotBracket.notCount ⟨[gnot, gand], 0⟩ = 1 := by
              rw [notCount_eq_filter]; rfl
            rw [h1, Finset.card_erase_add_one hm_fl]
          · intro l
            have hlen : gs ++ (e1 ++ [gnot, gand]) = ((gs ++ e1) ++ [gnot]) ++ [gand] := by simp [List.append_assoc]
            rw [hlen]
            have hnw := new_wire ((gs ++ e1) ++ [gnot]) gand (prefixInput n l)
            rw [prefixInput_len] at hnw
            change (W (((gs ++ e1) ++ [gnot]) ++ [gand]) (prefixInput n l)).getD (n + 2 + ((gs ++ e1) ++ [gnot]).length) false = f l
            rw [hnw]
            have hw1_val : (W ((gs ++ e1) ++ [gnot]) (prefixInput n l)).getD w1 false = f' l := by
              rw [old_wire (gs ++ e1) gnot (prefixInput n l) w1 (by rw [prefixInput_len]; omega)]
              exact hval1 l
            have hwnot_val : (W ((gs ++ e1) ++ [gnot]) (prefixInput n l)).getD wnot false = !decide (m.val < l.val) := by
              have hnw' := new_wire (gs ++ e1) gnot (prefixInput n l)
              rw [prefixInput_len] at hnw'
              change (W ((gs ++ e1) ++ [gnot]) (prefixInput n l)).getD (n + 2 + (gs ++ e1).length) false = _
              rw [hnw']
              have h0 := W_append_old [] (gs ++ e1) (prefixInput n l) m.val (by rw [prefixInput_len]; simp; omega)
              have hv : (W (gs ++ e1) (prefixInput n l)).getD m.val false = decide (m.val < l.val) :=
                h0.trans (prefixInput_lt n l m.val m.isLt)
              simp only [gnot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hv]
            simp only [gand, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, hw1_val, hwnot_val]
            by_cases hlt : m.val < l.val
            · rw [hafter l hlt, hf2]; simp [hlt]
            · have hle : l.val ≤ m.val := Nat.le_of_not_lt hlt
              simp [f', hle, hlt]
  exact key (chg f).card f rfl hne gs hF hR

def dg : Gate := ⟨GateOp.or, []⟩

theorem vl_take (n : ℕ) (gs : List Gate) (k i : ℕ) (hk : k ≤ gs.length) (hi : i < n + 2 + k)
    (l : Fin (n + 1)) :
    vl n gs i l = (W (gs.take k) (prefixInput n l)).getD i false := by
  unfold vl
  conv_lhs => rw [← List.take_append_drop k gs]
  exact W_append_old _ _ _ _ (by rw [prefixInput_len, List.length_take]; omega)

theorem vl_gate (n : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩) (l : Fin (n + 1)) :
    vl n gs (n + 2 + k) l =
      (gs.getD k dg).op.eval ((gs.getD k dg).inputs.map fun i => vl n gs i l) := by
  have h1 : vl n gs (n + 2 + k) l = (W (gs.take (k + 1)) (prefixInput n l)).getD (n + 2 + k) false :=
    vl_take n gs (k + 1) (n + 2 + k) hk (by omega) l
  have htake : gs.take (k + 1) = gs.take k ++ [gs.getD k dg] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
    rfl
  rw [h1, htake]
  have hnw := new_wire (gs.take k) (gs.getD k dg) (prefixInput n l)
  rw [prefixInput_len, List.length_take, min_eq_left hk.le] at hnw
  rw [hnw]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hRi : i < n + 2 + k := hR k hk i hi
  exact (vl_take n gs k i hk.le hRi l).symm

theorem vl_input (n : ℕ) (gs : List Gate) (u : ℕ) (hu : u < n) (l : Fin (n + 1)) :
    vl n gs u l = decide (u < l.val) := by
  rw [vl_take n gs 0 u (Nat.zero_le _) (by omega) l, List.take_zero, W_nil]
  exact prefixInput_lt n l u hu

theorem vl_false (n : ℕ) (gs : List Gate) (l : Fin (n + 1)) : vl n gs n l = false := by
  rw [vl_take n gs 0 n (Nat.zero_le _) (by omega) l, List.take_zero, W_nil]
  exact prefixInput_n n l

theorem vl_true (n : ℕ) (gs : List Gate) (l : Fin (n + 1)) : vl n gs (n + 1) l = true := by
  rw [vl_take n gs 0 (n + 1) (Nat.zero_le _) (by omega) l, List.take_zero, W_nil]
  exact prefixInput_n1 n l

theorem vl_out (n : ℕ) (gs : List Gate) (u : ℕ) (hu : n + 2 + gs.length ≤ u) (l : Fin (n + 1)) :
    vl n gs u l = false := by
  unfold vl
  rw [List.getD_eq_default]
  rw [W_len, prefixInput_len]; omega

theorem chg_input (n : ℕ) (gs : List Gate) (u : ℕ) (hu : u < n) (i : Fin n)
    (hi : i ∈ chg (vl n gs u)) : i.val = u := by
  rw [mem_chg, vl_input n gs u hu, vl_input n gs u hu] at hi
  simp only [Fin.coe_castSucc, Fin.val_succ] at hi
  by_contra hne
  apply hi
  by_cases h : u < i.val
  · rw [decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]

theorem chg_const_wire (n : ℕ) (gs : List Gate) (u : ℕ) (hu : u = n ∨ u = n + 1) :
    chg (vl n gs u) = ∅ := by
  apply chg_const
  intro t t'
  rcases hu with rfl | rfl
  · rw [vl_false, vl_false]
  · rw [vl_true, vl_true]

theorem chg_eval_sub {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (f : Fin (n + 1) → Bool) (op : GateOp)
    (ins : List ℕ) (h : ∀ l, f l = op.eval (ins.map fun a => F a l)) (i : Fin n)
    (hi : i ∈ chg f) : ∃ a ∈ ins, i ∈ chg (F a) := by
  by_contra hno
  push_neg at hno
  apply (mem_chg f i).1 hi
  rw [h, h]
  congr 1
  apply List.map_congr_left
  intro a ha
  have := hno a ha
  rw [mem_chg] at this
  simpa using this

def Merging {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (v : ℕ) : Prop :=
  ¬ ∀ i ∈ chg (F v), ∀ j ∈ chg (F v), ∃ u < v, i ∈ chg (F u) ∧ j ∈ chg (F u)

theorem not_merging_of_sub {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (v u : ℕ) (hu : u < v)
    (h : chg (F v) ⊆ chg (F u)) : ¬ Merging F v := by
  unfold Merging
  push_neg
  intro i hi j hj
  exact ⟨u, hu, h hi, h hj⟩

theorem not_merging_of_empty {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (v : ℕ)
    (h : chg (F v) = ∅) : ¬ Merging F v := by
  unfold Merging
  push_neg
  intro i hi
  rw [h] at hi
  simp at hi

theorem not_eval_cases {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (f : Fin (n + 1) → Bool) (ins : List ℕ)
    (h : ∀ l, f l = GateOp.not.eval (ins.map fun a => F a l)) :
    (ins = [] ∧ chg f = ∅) ∨ ∃ a rest, ins = a :: rest ∧ ∀ l, f l = !F a l := by
  cases ins with
  | nil =>
    left
    refine ⟨rfl, chg_const ?_⟩
    intro t t'
    rw [h, h]
    rfl
  | cons a rest =>
    right
    refine ⟨a, rest, rfl, fun l => ?_⟩
    rw [h]
    rfl

theorem merging_not_not (n : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩)
    (hM : Merging (vl n gs) (n + 2 + k)) : (gs.getD k dg).op ≠ GateOp.not := by
  intro hop
  have hv := vl_gate n gs k hk hR
  rw [hop] at hv
  rcases not_eval_cases (vl n gs) (vl n gs (n + 2 + k)) _ hv with ⟨_, he⟩ | ⟨a, rest, hins, hfa⟩
  · exact not_merging_of_empty _ _ he hM
  · have ha : a < n + 2 + k := hR k hk a (by
      show a ∈ (gs.getD k dg).inputs
      rw [hins]; exact List.mem_cons_self)
    apply not_merging_of_sub _ _ a ha _ hM
    rw [chg_congr (Or.inr hfa)]

theorem filter_len_eq_card (gs : List Gate) (p : Gate → Bool) :
    (gs.filter p).length =
      ((Finset.range gs.length).filter fun k => p (gs.getD k dg) = true).card := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.filter_append, List.length_append, ih, List.length_append, List.length_singleton,
      Finset.range_add_one, Finset.filter_insert]
    have hcongr : ((Finset.range gs.length).filter fun k => p ((gs ++ [g]).getD k dg) = true) =
        ((Finset.range gs.length).filter fun k => p (gs.getD k dg) = true) := by
      apply Finset.filter_congr
      intro k hk
      rw [Finset.mem_range] at hk
      rw [List.getD_append _ _ _ _ hk]
    have hg : (gs ++ [g]).getD gs.length dg = g := by simp
    rw [hg, hcongr]
    by_cases hp : p g = true
    · rw [if_pos hp, Finset.card_insert_of_notMem (by simp)]
      simp [hp]
    · rw [if_neg hp]
      simp [hp]

theorem nonNot_eq_card (gs : List Gate) :
    nonNotCount gs = ((Finset.range gs.length).filter fun k => isNotGate (gs.getD k dg) = false).card := by
  unfold nonNotCount
  rw [filter_len_eq_card]
  simp

theorem notCount_eq_card (gs : List Gate) (o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs, o⟩ =
      ((Finset.range gs.length).filter fun k => isNotGate (gs.getD k dg) = true).card := by
  rw [notCount_eq_filter]
  rw [filter_len_eq_card]

def Inv2 {n : ℕ} (F : ℕ → Fin (n + 1) → Bool) (K : ℕ) (P : ℕ) : Prop :=
  ∃ cls : Fin n → ℕ, (∀ u < K, ∀ i ∈ chg (F u), ∀ j ∈ chg (F u), cls i = cls j) ∧
    n ≤ (Finset.univ.image cls).card + P

theorem image_relabel_card {n : ℕ} (cls : Fin n → ℕ) (ca cb : ℕ) :
    (Finset.univ.image cls).card ≤
      (Finset.univ.image fun i => if cls i = cb then ca else cls i).card + 1 := by
  have hsub : (Finset.univ.image cls).erase cb ⊆
      (Finset.univ.image fun i => if cls i = cb then ca else cls i) := by
    intro c hc
    rw [Finset.mem_erase, Finset.mem_image] at hc
    obtain ⟨hne, i, _, rfl⟩ := hc
    rw [Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, by rw [if_neg hne]⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.image cls) (a := cb)
  omega

open Classical in
theorem inv2_all (n : ℕ) (gs : List Gate)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩) :
    ∀ k ≤ gs.length, Inv2 (vl n gs) (n + 2 + k)
      ((Finset.range k).filter fun k' => Merging (vl n gs) (n + 2 + k')).card := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun i => i.val, ?_, ?_⟩
    · intro u hu i hi j hj
      by_cases hun : u < n
      · show i.val = j.val
        rw [chg_input n gs u hun i hi, chg_input n gs u hun j hj]
      · have hc := chg_const_wire n gs u (by omega)
        rw [hc] at hi
        simp at hi
    · rw [Finset.card_image_of_injective _ Fin.val_injective]
      simp
  | succ k ih =>
    intro hk
    obtain ⟨cls, hcls, hcard⟩ := ih (by omega)
    have hk' : k < gs.length := by omega
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hM : Merging (vl n gs) (n + 2 + k)
    · rw [if_pos hM, Finset.card_insert_of_notMem (by simp)]
      set g := gs.getD k dg with hgdef
      have hlen : g.inputs.length ≤ 2 := (hF g (by
        rw [hgdef, List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk')).2
      set a := g.inputs.getD 0 n
      set b := g.inputs.getD 1 n
      have hab : ∀ x ∈ g.inputs, x = a ∨ x = b := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hx
        rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
        · left; show _ = g.inputs.getD 0 n; rw [List.getD_eq_getElem _ _ hp]
        · right; show _ = g.inputs.getD 1 n; rw [List.getD_eq_getElem _ _ hp]
      have hlt : ∀ x ∈ g.inputs, x < n + 2 + k := fun x hx => hR k hk' x hx
      have hsub : ∀ i ∈ chg (vl n gs (n + 2 + k)), i ∈ chg (vl n gs a) ∨ i ∈ chg (vl n gs b) := by
        intro i hi
        obtain ⟨x, hx, hix⟩ := chg_eval_sub (vl n gs) _ g.op g.inputs (vl_gate n gs k hk' hR) i hi
        rcases hab x hx with rfl | rfl
        · exact Or.inl hix
        · exact Or.inr hix
      have hlab : ∀ x, (x ∈ g.inputs ∨ x = n) → ∃ c, ∀ i ∈ chg (vl n gs x), cls i = c := by
        intro x hx
        by_cases hne : (chg (vl n gs x)).Nonempty
        · rcases hx with hx | heq
          · obtain ⟨i0, hi0⟩ := hne
            exact ⟨cls i0, fun i hi => hcls x (hlt x hx) i hi i0 hi0⟩
          · rw [heq, chg_const_wire n gs n (Or.inl rfl)] at hne
            simp at hne
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          exact ⟨0, fun i hi => by rw [hne] at hi; simp at hi⟩
      have hamem : a ∈ g.inputs ∨ a = n := by
        by_cases hp : 0 < g.inputs.length
        · left; show g.inputs.getD 0 n ∈ _; rw [List.getD_eq_getElem _ _ hp]; exact List.getElem_mem hp
        · right; show g.inputs.getD 0 n = n; rw [List.getD_eq_default _ _ (by omega)]
      have hbmem : b ∈ g.inputs ∨ b = n := by
        by_cases hp : 1 < g.inputs.length
        · left; show g.inputs.getD 1 n ∈ _; rw [List.getD_eq_getElem _ _ hp]; exact List.getElem_mem hp
        · right; show g.inputs.getD 1 n = n; rw [List.getD_eq_default _ _ (by omega)]
      have hlab' : ∀ x, (x = a ∨ x = b) → ∃ c, ∀ i ∈ chg (vl n gs (n + 2 + k)),
          i ∈ chg (vl n gs x) → cls i = c := by
        intro x hx
        obtain ⟨c, hc⟩ := hlab x (by rcases hx with hx | hx <;> rw [hx]; exact hamem; exact hbmem)
        exact ⟨c, fun i _ hi => hc i hi⟩
      obtain ⟨ca, hca⟩ := hlab' a (Or.inl rfl)
      obtain ⟨cb, hcb⟩ := hlab' b (Or.inr rfl)
      refine ⟨fun i => if cls i = cb then ca else cls i, ?_, ?_⟩
      · intro u hu i hi j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show u < n + 2 + k + 1 by omega) with hu' | rfl
        · show (if cls i = cb then ca else cls i) = (if cls j = cb then ca else cls j)
          rw [hcls u hu' i hi j hj]
        · have key : ∀ x ∈ chg (vl n gs (n + 2 + k)), (if cls x = cb then ca else cls x) = ca := by
            intro x hx
            rcases hsub x hx with hxa | hxb
            · rw [hca x hx hxa]
              split_ifs with h
              · rfl
              · rfl
            · rw [if_pos (hcb x hx hxb)]
          show (if cls i = cb then ca else cls i) = (if cls j = cb then ca else cls j)
          rw [key i hi, key j hj]
      · have := image_relabel_card cls ca cb
        omega
    · rw [if_neg hM]
      refine ⟨cls, ?_, hcard⟩
      intro u hu i hi j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 (show u < n + 2 + k + 1 by omega) with hu' | rfl
      · exact hcls u hu' i hi j hj
      · unfold Merging at hM
        push_neg at hM
        obtain ⟨w, hw, hiw, hjw⟩ := hM i hi j hj
        exact hcls w hw i hiw j hjw

open Classical in
theorem tight_merge (n : ℕ) (hn : 0 < n) (gs : List Gate)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩)
    (hP : nonNotCount gs ≤ n - 1) (r : ℕ) (hr : chg (vl n gs r) = Finset.univ) :
    ∀ k < gs.length, isNotGate (gs.getD k dg) = false → Merging (vl n gs) (n + 2 + k) := by
  obtain ⟨cls, hcls, hcard⟩ := inv2_all n gs hF hR gs.length le_rfl
  have hrlt : r < n + 2 + gs.length := by
    by_contra hge
    have h0 : (⟨0, hn⟩ : Fin n) ∈ chg (vl n gs r) := by rw [hr]; exact Finset.mem_univ _
    have := chg_const (f := vl n gs r) (fun t t' => by
      rw [vl_out n gs r (by omega), vl_out n gs r (by omega)])
    rw [this] at h0
    simp at h0
  have himg : (Finset.univ.image cls).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨i, _, rfl⟩ := hx
    obtain ⟨j, _, rfl⟩ := hy
    exact hcls r hrlt i (by rw [hr]; exact Finset.mem_univ _) j (by rw [hr]; exact Finset.mem_univ _)
  have hsubset : ((Finset.range gs.length).filter fun k' => Merging (vl n gs) (n + 2 + k')) ⊆
      ((Finset.range gs.length).filter fun k => isNotGate (gs.getD k dg) = false) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨hk.1, (isNotGate_eq_false _).2 (merging_not_not n gs k hk.1 hR hk.2)⟩
  have hnn := nonNot_eq_card gs
  have heq := Finset.eq_of_subset_of_card_le hsubset (by omega)
  intro k hk hop
  have hmem : k ∈ ((Finset.range gs.length).filter fun k => isNotGate (gs.getD k dg) = false) := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hop⟩
  rw [← heq, Finset.mem_filter] at hmem
  exact hmem.2

theorem falls_and_sub {n : ℕ} (f g : Fin (n + 1) → Bool) :
    falls (fun t => f t && g t) ⊆ falls f ∪ falls g := by
  intro i hi
  rw [mem_falls] at hi
  rw [Finset.mem_union, mem_falls, mem_falls]
  cases h1 : f i.castSucc <;> cases h2 : g i.castSucc <;> cases h3 : f i.succ <;>
    cases h4 : g i.succ <;> simp_all

theorem falls_or_sub {n : ℕ} (f g : Fin (n + 1) → Bool) :
    falls (fun t => f t || g t) ⊆ falls f ∪ falls g := by
  intro i hi
  rw [mem_falls] at hi
  rw [Finset.mem_union, mem_falls, mem_falls]
  cases h1 : f i.castSucc <;> cases h2 : g i.castSucc <;> cases h3 : f i.succ <;>
    cases h4 : g i.succ <;> simp_all

theorem merge_struct (n : ℕ) (gs : List Gate)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩)
    (hLam : ∀ u < n + 2 + gs.length, ∀ v < n + 2 + gs.length,
      Lam (chg (vl n gs u)) (chg (vl n gs v)))
    (k : ℕ) (hk : k < gs.length) (hnot : isNotGate (gs.getD k dg) = false)
    (hM : Merging (vl n gs) (n + 2 + k)) :
    ∃ a b, (gs.getD k dg).inputs = [a, b] ∧ a < n + 2 + k ∧ b < n + 2 + k ∧
      ((∀ l, vl n gs (n + 2 + k) l = (vl n gs a l && vl n gs b l)) ∨
        (∀ l, vl n gs (n + 2 + k) l = (vl n gs a l || vl n gs b l))) ∧
      (chg (vl n gs a)).Nonempty ∧ (chg (vl n gs b)).Nonempty ∧
      Disjoint (chg (vl n gs a)) (chg (vl n gs b)) ∧
      chg (vl n gs (n + 2 + k)) = chg (vl n gs a) ∪ chg (vl n gs b) := by
  set g := gs.getD k dg with hgdef
  have hgmem : g ∈ gs := by rw [hgdef, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    have h1 := (hF g hgmem).1
    have h2 := (isNotGate_eq_false g).1 hnot
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h h2
  have hlen : g.inputs.length ≤ 2 := (hF g hgmem).2
  have hv := vl_gate n gs k hk hR
  have hlt : ∀ x ∈ g.inputs, x < n + 2 + k := fun x hx => hR k hk x hx
  match hins : g.inputs with
  | [] =>
    exfalso
    apply not_merging_of_empty _ _ _ hM
    apply chg_const
    intro t t'
    rw [hv, hv, hins]
    rfl
  | [a] =>
    exfalso
    have ha : a < n + 2 + k := hlt a (by rw [hins]; exact List.mem_singleton_self a)
    apply not_merging_of_sub _ _ a ha _ hM
    have hfa : ∀ l, vl n gs (n + 2 + k) l = vl n gs a l := by
      intro l
      rw [hv, hins]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
    rw [chg_congr (Or.inl hfa)]
  | [a, b] =>
    have ha : a < n + 2 + k := hlt a (by rw [hins]; simp)
    have hb : b < n + 2 + k := hlt b (by rw [hins]; simp)
    have hval : (∀ l, vl n gs (n + 2 + k) l = (vl n gs a l && vl n gs b l)) ∨
        (∀ l, vl n gs (n + 2 + k) l = (vl n gs a l || vl n gs b l)) := by
      rcases hop with h | h
      · left; intro l; rw [hv, hins, h]; simp [GateOp.eval]
      · right; intro l; rw [hv, hins, h]; simp [GateOp.eval]
    have hsub : chg (vl n gs (n + 2 + k)) ⊆ chg (vl n gs a) ∪ chg (vl n gs b) := by
      intro i hi
      obtain ⟨x, hx, hix⟩ := chg_eval_sub (vl n gs) _ g.op g.inputs hv i hi
      rw [hins] at hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_union_left _ hix
      · exact Finset.mem_union_right _ hix
    have hN : n + 2 + k < n + 2 + gs.length := by omega
    have hA : a < n + 2 + gs.length := by omega
    have hB : b < n + 2 + gs.length := by omega
    have hane : (chg (vl n gs a)).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      apply not_merging_of_sub _ _ b hb _ hM
      intro i hi
      rcases Finset.mem_union.1 (hsub hi) with h | h
      · rw [he] at h; simp at h
      · exact h
    have hbne : (chg (vl n gs b)).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      apply not_merging_of_sub _ _ a ha _ hM
      intro i hi
      rcases Finset.mem_union.1 (hsub hi) with h | h
      · exact h
      · rw [he] at h; simp at h
    have hdis : Disjoint (chg (vl n gs a)) (chg (vl n gs b)) := by
      rcases hLam a hA b hB with h | h | h
      · exfalso
        apply not_merging_of_sub _ _ b hb _ hM
        intro i hi
        rcases Finset.mem_union.1 (hsub hi) with h' | h'
        · exact h h'
        · exact h'
      · exfalso
        apply not_merging_of_sub _ _ a ha _ hM
        intro i hi
        rcases Finset.mem_union.1 (hsub hi) with h' | h'
        · exact h'
        · exact h h'
      · exact h
    have hsupA : chg (vl n gs a) ⊆ chg (vl n gs (n + 2 + k)) := by
      rcases hLam (n + 2 + k) hN a hA with h | h | h
      · exact absurd hM (not_merging_of_sub _ _ a ha h)
      · exact h
      · exfalso
        apply not_merging_of_sub _ _ b hb _ hM
        intro i hi
        rcases Finset.mem_union.1 (hsub hi) with h' | h'
        · exact absurd h' (Finset.disjoint_left.1 h hi)
        · exact h'
    have hsupB : chg (vl n gs b) ⊆ chg (vl n gs (n + 2 + k)) := by
      rcases hLam (n + 2 + k) hN b hB with h | h | h
      · exact absurd hM (not_merging_of_sub _ _ b hb h)
      · exact h
      · exfalso
        apply not_merging_of_sub _ _ a ha _ hM
        intro i hi
        rcases Finset.mem_union.1 (hsub hi) with h' | h'
        · exact h'
        · exact absurd h' (Finset.disjoint_left.1 h hi)
    exact ⟨a, b, rfl, ha, hb, hval, hane, hbne, hdis,
      Finset.Subset.antisymm hsub (Finset.union_subset hsupA hsupB)⟩
  | _ :: _ :: _ :: _ =>
    exfalso
    rw [hins] at hlen
    simp at hlen

open Classical in
def NOTs (n : ℕ) (gs : List Gate) (u : ℕ) (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.range gs.length).filter fun k => n + 2 + k ≤ u ∧ isNotGate (gs.getD k dg) = true ∧
    (chg (vl n gs (n + 2 + k))).Nonempty ∧ chg (vl n gs (n + 2 + k)) ⊆ S

open Classical in
def NNs (n : ℕ) (gs : List Gate) (u : ℕ) (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.range gs.length).filter fun k => n + 2 + k ≤ u ∧ isNotGate (gs.getD k dg) = false ∧
    (chg (vl n gs (n + 2 + k))).Nonempty ∧ chg (vl n gs (n + 2 + k)) ⊆ S

theorem NOTs_mono (n : ℕ) (gs : List Gate) {u u' : ℕ} {S S' : Finset (Fin n)} (hu : u ≤ u')
    (hS : S ⊆ S') : NOTs n gs u S ⊆ NOTs n gs u' S' := by
  intro k hk
  unfold NOTs at hk ⊢
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, by omega, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.trans hS⟩

theorem NNs_mono (n : ℕ) (gs : List Gate) {u u' : ℕ} {S S' : Finset (Fin n)} (hu : u ≤ u')
    (hS : S ⊆ S') : NNs n gs u S ⊆ NNs n gs u' S' := by
  intro k hk
  unfold NNs at hk ⊢
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, by omega, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.trans hS⟩

theorem NOTs_disj (n : ℕ) (gs : List Gate) (u u' : ℕ) {S S' : Finset (Fin n)} (h : Disjoint S S') :
    Disjoint (NOTs n gs u S) (NOTs n gs u' S') := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  unfold NOTs at hk hk'
  rw [Finset.mem_filter] at hk hk'
  obtain ⟨i, hi⟩ := hk.2.2.2.1
  exact Finset.disjoint_left.1 h (hk.2.2.2.2 hi) (hk'.2.2.2.2 hi)

theorem NNs_disj (n : ℕ) (gs : List Gate) (u u' : ℕ) {S S' : Finset (Fin n)} (h : Disjoint S S') :
    Disjoint (NNs n gs u S) (NNs n gs u' S') := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  unfold NNs at hk hk'
  rw [Finset.mem_filter] at hk hk'
  obtain ⟨i, hi⟩ := hk.2.2.2.1
  exact Finset.disjoint_left.1 h (hk.2.2.2.2 hi) (hk'.2.2.2.2 hi)

theorem falls_inp (n : ℕ) (gs : List Gate) (u : ℕ) (hu : u < n) : falls (vl n gs u) = ∅ := by
  ext i
  rw [mem_falls, vl_input n gs u hu, vl_input n gs u hu]
  simp only [Fin.coe_castSucc, Fin.val_succ, Finset.notMem_empty, iff_false, not_and,
    decide_eq_true_eq, decide_eq_false_iff_not, not_not]
  intro h; omega

theorem count_bounds (n : ℕ) (gs : List Gate)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩)
    (hLam : ∀ u < n + 2 + gs.length, ∀ v < n + 2 + gs.length,
      Lam (chg (vl n gs u)) (chg (vl n gs v)))
    (hMg : ∀ k < gs.length, isNotGate (gs.getD k dg) = false → Merging (vl n gs) (n + 2 + k)) :
    ∀ u, u < n + 2 + gs.length → (chg (vl n gs u)).Nonempty →
      (falls (vl n gs u)).card ≤ (NOTs n gs u (chg (vl n gs u))).card ∧
      (chg (vl n gs u)).card ≤ (NNs n gs u (chg (vl n gs u))).card + 1 := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro hu hne
  by_cases hin : u < n
  · rw [falls_inp n gs u hin]
    refine ⟨by simp, ?_⟩
    have : (chg (vl n gs u)).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro i hi j hj
      exact Fin.ext ((chg_input n gs u hin i hi).trans (chg_input n gs u hin j hj).symm)
    omega
  by_cases hc : u = n ∨ u = n + 1
  · rw [chg_const_wire n gs u hc] at hne
    simp at hne
  obtain ⟨k, rfl⟩ : ∃ k, u = n + 2 + k := ⟨u - (n + 2), by omega⟩
  have hk : k < gs.length := by omega
  have hv := vl_gate n gs k hk hR
  cases hg : isNotGate (gs.getD k dg) with
  | true =>
    have hop := (isNotGate_eq_true _).1 hg
    rw [hop] at hv
    rcases not_eval_cases (vl n gs) (vl n gs (n + 2 + k)) _ hv with ⟨_, he⟩ | ⟨a, rest, hins, hfa⟩
    · rw [he] at hne; simp at hne
    have ha : a < n + 2 + k := hR k hk a (by
      show a ∈ (gs.getD k dg).inputs
      rw [hins]; exact List.mem_cons_self)
    have hchg : chg (vl n gs (n + 2 + k)) = chg (vl n gs a) := chg_congr (Or.inr hfa)
    have hfun : vl n gs (n + 2 + k) = fun t => !vl n gs a t := funext hfa
    obtain ⟨ih1, ih2⟩ := ih a ha (by omega) (by rw [← hchg]; exact hne)
    rw [hchg]
    constructor
    · rw [hfun, falls_not_eq_rises]
      have h1 := rises_le_falls_succ (vl n gs a)
      have hsub : insert k (NOTs n gs a (chg (vl n gs a))) ⊆ NOTs n gs (n + 2 + k) (chg (vl n gs a)) := by
        apply Finset.insert_subset
        · unfold NOTs
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hk, le_rfl, hg, hne, by rw [hchg]⟩
        · exact NOTs_mono n gs (by omega) (Finset.Subset.refl _)
      have hnm : k ∉ NOTs n gs a (chg (vl n gs a)) := by
        unfold NOTs
        rw [Finset.mem_filter]
        intro h; omega
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnm] at h2
      omega
    · have := Finset.card_le_card (NNs_mono n gs (u := a) (u' := n + 2 + k) (by omega)
        (Finset.Subset.refl (chg (vl n gs a))))
      omega
  | false =>
    obtain ⟨a, b, hins, ha, hb, hval, hane, hbne, hdis, hun⟩ :=
      merge_struct n gs hF hR hLam k hk hg (hMg k hk hg)
    obtain ⟨iha1, iha2⟩ := ih a ha (by omega) hane
    obtain ⟨ihb1, ihb2⟩ := ih b hb (by omega) hbne
    have hfs : falls (vl n gs (n + 2 + k)) ⊆ falls (vl n gs a) ∪ falls (vl n gs b) := by
      rcases hval with h | h
      · rw [show vl n gs (n + 2 + k) = fun t => vl n gs a t && vl n gs b t from funext h]
        exact falls_and_sub _ _
      · rw [show vl n gs (n + 2 + k) = fun t => vl n gs a t || vl n gs b t from funext h]
        exact falls_or_sub _ _
    rw [hun]
    constructor
    · have h1 := Finset.card_le_card hfs
      have h2 := Finset.card_union_le (falls (vl n gs a)) (falls (vl n gs b))
      have hsub : NOTs n gs a (chg (vl n gs a)) ∪ NOTs n gs b (chg (vl n gs b)) ⊆
          NOTs n gs (n + 2 + k) (chg (vl n gs a) ∪ chg (vl n gs b)) :=
        Finset.union_subset (NOTs_mono n gs (by omega) Finset.subset_union_left)
          (NOTs_mono n gs (by omega) Finset.subset_union_right)
      have h3 := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint (NOTs_disj n gs a b hdis)] at h3
      omega
    · rw [Finset.card_union_of_disjoint hdis]
      have hsub : insert k (NNs n gs a (chg (vl n gs a)) ∪ NNs n gs b (chg (vl n gs b))) ⊆
          NNs n gs (n + 2 + k) (chg (vl n gs a) ∪ chg (vl n gs b)) := by
        apply Finset.insert_subset
        · unfold NNs
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hk, le_rfl, hg, by rw [hun]; exact hane.mono Finset.subset_union_left,
            by rw [hun]⟩
        · exact Finset.union_subset (NNs_mono n gs (by omega) Finset.subset_union_left)
            (NNs_mono n gs (by omega) Finset.subset_union_right)
      have hnm : k ∉ NNs n gs a (chg (vl n gs a)) ∪ NNs n gs b (chg (vl n gs b)) := by
        unfold NNs
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        intro h; rcases h with h | h <;> omega
      have h3 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnm, Finset.card_union_of_disjoint (NNs_disj n gs a b hdis)] at h3
      omega

def usedIns (g : Gate) : List ℕ := if isNotGate g then g.inputs.take 1 else g.inputs

theorem eval_usedIns (g : Gate) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((usedIns g).map f) := by
  unfold usedIns
  split_ifs with h
  · have hop := (isNotGate_eq_true g).1 h
    rw [hop]
    cases hi : g.inputs with
    | nil => rfl
    | cons a rest => rfl
  · rfl

theorem usedIns_sub (g : Gate) : ∀ x ∈ usedIns g, x ∈ g.inputs := by
  intro x hx
  unfold usedIns at hx
  split_ifs at hx
  · exact List.mem_of_mem_take hx
  · exact hx

open Classical in
theorem replay (nA nB : ℕ) (gs gsB : List Gate)
    (hFA : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hRA : PEqualNP.MetaComplexity.NestedCover.ReadsBack (nA + 2) ⟨gs, 0⟩)
    (hFB : PEqualNP.MetaComplexity.FanInTwo ⟨gsB, 0⟩)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (nB + 2) ⟨gsB, 0⟩)
    (E : Fin (nA + 1) → Fin (nB + 1) → Prop)
    (Base : ℕ → Prop) (Rep : ℕ → Prop) (σ0 : ℕ → ℕ)
    (hbase : ∀ u, Base u → σ0 u < nB + 2 + gsB.length ∧
      ∀ l l', E l l' → vl nA gs u l = vl nB gsB (σ0 u) l')
    (hrepb : ∀ k, Rep k → ¬ Base (nA + 2 + k))
    (hrepin : ∀ k < gs.length, Rep k → ∀ x ∈ usedIns (gs.getD k dg),
      Base x ∨ (nA + 2 ≤ x ∧ Rep (x - (nA + 2)))) :
    ∀ k ≤ gs.length, ∃ (T : List Gate) (σ : ℕ → ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨gsB ++ T, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (nB + 2) ⟨gsB ++ T, 0⟩ ∧
      PEqualNP.NotBracket.notCount ⟨T, 0⟩ =
        ((Finset.range k).filter fun k' => Rep k' ∧ isNotGate (gs.getD k' dg) = true).card ∧
      nonNotCount T =
        ((Finset.range k).filter fun k' => Rep k' ∧ isNotGate (gs.getD k' dg) = false).card ∧
      ∀ u < nA + 2 + k, (Base u ∨ (nA + 2 ≤ u ∧ Rep (u - (nA + 2)))) →
        σ u < nB + 2 + (gsB ++ T).length ∧
        ∀ l l', E l l' → vl nA gs u l = vl nB (gsB ++ T) (σ u) l' := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], σ0, by simpa using hFB, by simpa using hRB, by rw [notCount_eq_filter]; simp,
      by simp [nonNotCount], ?_⟩
    intro u hu hdom
    rcases hdom with hb | ⟨h1, _⟩
    · simpa using hbase u hb
    · omega
  | succ k ih =>
    intro hk
    have hk' : k < gs.length := by omega
    obtain ⟨T, σ, hF, hR, hnc, hnn, hval⟩ := ih (by omega)
    set g := gs.getD k dg with hgdef
    have hgmem : g ∈ gs := by rw [hgdef, List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    by_cases hrep : Rep k
    · set g' : Gate := ⟨g.op, (usedIns g).map σ⟩ with hg'def
      have hin_ok : ∀ x ∈ usedIns g, x < nA + 2 + k ∧
          (Base x ∨ (nA + 2 ≤ x ∧ Rep (x - (nA + 2)))) := by
        intro x hx
        exact ⟨hRA k hk' x (usedIns_sub g x hx), hrepin k hk' hrep x hx⟩
      refine ⟨T ++ [g'], fun x => if x = nA + 2 + k then nB + 2 + (gsB ++ T).length else σ x,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [← List.append_assoc]
        apply fanInTwo_append hF
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        refine ⟨(hFA g hgmem).1, ?_⟩
        rw [hg'def, List.length_map]
        have := (hFA g hgmem).2
        unfold usedIns
        split_ifs
        · simp
        · exact this
      · rw [← List.append_assoc]
        apply readsBack_snoc hR
        intro i hi
        rw [hg'def, List.mem_map] at hi
        obtain ⟨x, hx, rfl⟩ := hi
        obtain ⟨hxl, hxd⟩ := hin_ok x hx
        exact (hval x hxl hxd).1
      · have hg'n : isNotGate g' = isNotGate g := rfl
        have hnot1 : PEqualNP.NotBracket.notCount ⟨[g'], 0⟩ = if isNotGate g = true then 1 else 0 := by
          rw [notCount_eq_filter]
          cases h : isNotGate g <;> simp [hg'n, h]
        rw [notCount_append, hnc, hnot1]
        cases h : isNotGate g <;> simp [hrep, Finset.card_insert_of_notMem]
      · have hg'n : isNotGate g' = isNotGate g := rfl
        have hnn1 : nonNotCount [g'] = if isNotGate g = false then 1 else 0 := by
          unfold nonNotCount
          cases h : isNotGate g <;> simp [hg'n, h]
        rw [nonNotCount_append, hnn, hnn1]
        cases h : isNotGate g <;> simp [hrep, Finset.card_insert_of_notMem]
      · intro u hu hdom
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show u < nA + 2 + k + 1 by omega) with hlt | rfl
        · beta_reduce
          rw [if_neg (show u ≠ nA + 2 + k by omega)]
          obtain ⟨h1, h2⟩ := hval u hlt hdom
          refine ⟨by simp only [List.length_append, List.length_singleton] at h1 ⊢; omega,
            fun l l' hE => ?_⟩
          rw [h2 l l' hE]
          unfold vl
          rw [← List.append_assoc]
          exact (W_append_old _ _ _ _ (by rw [prefixInput_len]; exact h1)).symm
        · beta_reduce
          rw [if_pos rfl]
          refine ⟨by simp, fun l l' hE => ?_⟩
          have hRB' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (nB + 2) ⟨gsB ++ T ++ [g'], 0⟩ := by
            apply readsBack_snoc hR
            intro i hi
            rw [hg'def, List.mem_map] at hi
            obtain ⟨x, hx, rfl⟩ := hi
            obtain ⟨hxl, hxd⟩ := hin_ok x hx
            exact (hval x hxl hxd).1
          have hidx : nB + 2 + (gsB ++ T).length = nB + 2 + (gsB ++ T).length := rfl
          have hvt := vl_gate nB (gsB ++ T ++ [g']) (gsB ++ T).length (by simp) hRB' l'
          have hgget : (gsB ++ T ++ [g']).getD (gsB ++ T).length dg = g' := by simp
          rw [hgget] at hvt
          rw [List.append_assoc] at hvt
          rw [hvt, vl_gate nA gs k hk' hRA l, ← hgdef, eval_usedIns g (fun i => vl nA gs i l)]
          show g.op.eval ((usedIns g).map fun i => vl nA gs i l) =
            g.op.eval (((usedIns g).map σ).map fun i => vl nB (gsB ++ (T ++ [g'])) i l')
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro x hx
          obtain ⟨hxl, hxd⟩ := hin_ok x hx
          obtain ⟨h1, h2⟩ := hval x hxl hxd
          rw [h2 l l' hE]
          show vl nB (gsB ++ T) (σ x) l' = vl nB (gsB ++ (T ++ [g'])) (σ x) l'
          unfold vl
          rw [← List.append_assoc]
          exact (W_append_old _ _ _ _ (by rw [prefixInput_len]; exact h1)).symm
    · refine ⟨T, fun x => if x = nA + 2 + k then σ0 x else σ x, hF, hR, ?_, ?_, ?_⟩
      · rw [if_neg (fun h => hrep h.1), hnc]
      · rw [if_neg (fun h => hrep h.1), hnn]
      · intro u hu hdom
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show u < nA + 2 + k + 1 by omega) with hlt | rfl
        · beta_reduce
          rw [if_neg (show u ≠ nA + 2 + k by omega)]
          exact hval u hlt hdom
        · beta_reduce
          rw [if_pos rfl]
          rcases hdom with hb | ⟨_, hr⟩
          · obtain ⟨h1, h2⟩ := hbase _ hb
            refine ⟨by simp only [List.length_append] at h1 ⊢; omega, fun l l' hE => ?_⟩
            rw [h2 l l' hE]
            unfold vl
            exact (W_append_old _ _ _ _ (by rw [prefixInput_len]; exact h1)).symm
          · exact absurd (by simpa using hr) hrep

theorem falls_bal {n : ℕ} (f : Fin (n + 1) → Bool) :
    (falls f).card + (f (Fin.last n)).toNat = (rises f).card + (f 0).toNat := by
  have key : ∀ (k : ℕ) (hk : k ≤ n),
      ((falls f).filter fun i => i.val < k).card + (f ⟨k, by omega⟩).toNat =
      ((rises f).filter fun i => i.val < k).card + (f ⟨0, by omega⟩).toNat := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h1 : (falls f).filter (fun i => i.val < 0) = ∅ := by ext i; simp
      have h2 : (rises f).filter (fun i => i.val < 0) = ∅ := by ext i; simp
      rw [h1, h2]
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      let idx : Fin n := ⟨k, by omega⟩
      have hcs : idx.castSucc = ⟨k, by omega⟩ := rfl
      have hsc : idx.succ = ⟨k + 1, by omega⟩ := rfl
      have hfsplit : (falls f).filter (fun i => i.val < k + 1) =
          if idx ∈ falls f then insert idx ((falls f).filter (fun i => i.val < k))
          else (falls f).filter (fun i => i.val < k) := by
        split_ifs with hm
        · ext i; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact Or.inr ⟨hi, hlt⟩
            · exact Or.inl (Fin.ext heq)
          · rintro (rfl | ⟨hi, hlt⟩)
            · exact ⟨hm, Nat.lt_succ_self k⟩
            · exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
        · ext i; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact ⟨hi, hlt⟩
            · exfalso; exact hm ((Fin.ext heq : i = idx) ▸ hi)
          · rintro ⟨hi, hlt⟩; exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
      have hrsplit : (rises f).filter (fun i => i.val < k + 1) =
          if idx ∈ rises f then insert idx ((rises f).filter (fun i => i.val < k))
          else (rises f).filter (fun i => i.val < k) := by
        split_ifs with hm
        · ext i; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact Or.inr ⟨hi, hlt⟩
            · exact Or.inl (Fin.ext heq)
          · rintro (rfl | ⟨hi, hlt⟩)
            · exact ⟨hm, Nat.lt_succ_self k⟩
            · exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
        · ext i; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hi, hlt⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
            · exact ⟨hi, hlt⟩
            · exfalso; exact hm ((Fin.ext heq : i = idx) ▸ hi)
          · rintro ⟨hi, hlt⟩; exact ⟨hi, Nat.lt_succ_of_lt hlt⟩
      have hnf : idx ∉ (falls f).filter (fun i => i.val < k) := by simp [idx]
      have hnr : idx ∉ (rises f).filter (fun i => i.val < k) := by simp [idx]
      rw [hfsplit, hrsplit]
      have hmf : idx ∈ falls f ↔ f ⟨k, by omega⟩ = true ∧ f ⟨k + 1, by omega⟩ = false := by
        rw [mem_falls, hcs, hsc]
      have hmr : idx ∈ rises f ↔ f ⟨k, by omega⟩ = false ∧ f ⟨k + 1, by omega⟩ = true := by
        rw [mem_rises, hcs, hsc]
      cases h1 : f ⟨k, by omega⟩ <;> cases h2 : f ⟨k + 1, by omega⟩ <;>
        simp [hmf, hmr, h1, h2, Finset.card_insert_of_notMem hnf,
          Finset.card_insert_of_notMem hnr] at hprev ⊢ <;> omega
  have htop := key n (le_refl n)
  have hf : (falls f).filter (fun i => i.val < n) = falls f := by
    ext i; simp [i.isLt]
  have hr : (rises f).filter (fun i => i.val < n) = rises f := by
    ext i; simp [i.isLt]
  rw [hf, hr] at htop
  exact htop

theorem chg_eq_union {n : ℕ} (f : Fin (n + 1) → Bool) : chg f = falls f ∪ rises f := by
  ext i
  rw [Finset.mem_union, mem_chg, mem_falls, mem_rises]
  cases f i.castSucc <;> cases f i.succ <;> simp

theorem two_falls {n : ℕ} (f : Fin (n + 1) → Bool) :
    2 * (falls f).card + (f (Fin.last n)).toNat = (chg f).card + (f 0).toNat := by
  have h1 := falls_bal f
  have h2 : (chg f).card = (falls f).card + (rises f).card := by
    rw [chg_eq_union, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro i h h'
    rw [mem_falls] at h
    rw [mem_rises] at h'
    rw [h.1] at h'
    simp at h'
  omega

theorem walk_mem_succ {n d : ℕ} (color : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j)
    (i : Fin n) (j : Fin d) (hj : j ≠ color i) : (j ∈ X i.succ ↔ j ∈ X i.castSucc) := by
  have h := (hX i j).not
  have hj' : ¬ color i = j := fun h' => hj h'.symm
  rw [not_not] at h
  have := h.2 hj'
  by_cases h1 : j ∈ X i.castSucc <;> by_cases h2 : j ∈ X i.succ <;> simp_all

theorem chg_tap {n d : ℕ} (color : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) (j : Fin d) :
    chg (fun l => decide (j ∈ X l)) = colorBlock color j := by
  ext i; rw [mem_chg, mem_colorBlock]; exact hX i j

theorem chg_par {n d : ℕ} (color : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j)
    (M : Finset (Fin d)) (p : Bool) (i : Fin n) :
    i ∈ chg (fun l => Bool.xor p (decide ((X l ∩ M).card % 2 = 1))) ↔ color i ∈ M := by
  rw [mem_chg]
  set c := color i
  have hc := (hX i c).2 rfl
  by_cases hcM : c ∈ M
  · simp only [hcM, iff_true]
    have key : (X i.succ ∩ M).card + 1 = (X i.castSucc ∩ M).card ∨
        (X i.castSucc ∩ M).card + 1 = (X i.succ ∩ M).card := by
      by_cases hin : c ∈ X i.castSucc
      · have hout : c ∉ X i.succ := by
          intro h; apply hc; simp [hin, h]
        left
        have : X i.castSucc ∩ M = insert c (X i.succ ∩ M) := by
          ext j
          rw [Finset.mem_insert, Finset.mem_inter, Finset.mem_inter]
          by_cases hjc : j = c
          · subst hjc; simp [hin, hcM]
          · rw [walk_mem_succ color X hX i j hjc]; simp [hjc]
        rw [this, Finset.card_insert_of_notMem (by simp [hout])]
      · have hout : c ∈ X i.succ := by
          by_contra h; apply hc; simp [hin, h]
        right
        have : X i.succ ∩ M = insert c (X i.castSucc ∩ M) := by
          ext j
          rw [Finset.mem_insert, Finset.mem_inter, Finset.mem_inter]
          by_cases hjc : j = c
          · subst hjc; simp [hout, hcM]
          · rw [walk_mem_succ color X hX i j hjc]; simp [hjc]
        rw [this, Finset.card_insert_of_notMem (by simp [hin])]
    intro h
    have h' : decide ((X i.castSucc ∩ M).card % 2 = 1) = decide ((X i.succ ∩ M).card % 2 = 1) := by
      cases p <;> simpa using h
    rcases key with k | k <;> rw [← k] at h' <;> simp at h' <;> omega
  · simp only [hcM, iff_false, not_not]
    have : X i.succ ∩ M = X i.castSucc ∩ M := by
      ext j
      rw [Finset.mem_inter, Finset.mem_inter]
      by_cases hjM : j ∈ M
      · have hjc : j ≠ c := fun h => hcM (h ▸ hjM)
        rw [walk_mem_succ color X hX i j hjc]
      · simp [hjM]
    rw [this]

theorem build_all {n d : ℕ} (color : Fin n → Fin d) (hsurj : Function.Surjective color)
    (f : Fin d → Fin (n + 1) → Bool) (hf : ∀ j, chg (f j) = colorBlock color j) :
    ∃ (gs : List Gate) (tap : Fin d → ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ ∧
      nonNotCount gs + d = n ∧
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = ∑ j : Fin d, (falls (f j)).card ∧
      ∀ j : Fin d, tap j < n + 2 + gs.length ∧ ∀ l, vl n gs (tap j) l = f j l := by
  have hstep : ∀ k ≤ d,
      ∃ (gs : List Gate) (tap : ∀ j : Fin d, j.val < k → ℕ),
        PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ ∧
        nonNotCount gs = ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k), ((colorBlock color j).card - 1) ∧
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ =
          ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k), (falls (f j)).card ∧
        ∀ j (hj : j.val < k), tap j hj < n + 2 + gs.length ∧ ∀ l, vl n gs (tap j hj) l = f j l := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (by simp), fun _ h => absurd h (by simp),
        by simp [nonNotCount], by rw [notCount_eq_filter]; simp,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨gs, tap, hF, hRB, hnn, hnc, hvals⟩ := ih (by omega)
      let j0 : Fin d := ⟨k, hk⟩
      have hne0 : (chg (f j0)).Nonempty := by
        rw [hf j0]; exact colorBlock_nonempty hsurj j0
      obtain ⟨extra, w0, hw0_lt, hF', hRB', hnn_e, hnc_e, hw0_val⟩ :=
        build_prefix_fn (f j0) hne0 gs hF hRB
      have hfilt : Finset.univ.filter (fun j : Fin d => j.val < k + 1) =
          insert j0 (Finset.univ.filter (fun j : Fin d => j.val < k)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hlt
          rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
          · exact Or.inr hlt
          · exact Or.inl (Fin.ext heq)
        · rintro (rfl | hlt)
          · exact Nat.lt_succ_self k
          · exact Nat.lt_succ_of_lt hlt
      have hj0_nm : j0 ∉ Finset.univ.filter (fun j : Fin d => j.val < k) := by simp [j0]
      refine ⟨gs ++ extra, fun j hj => if h : j.val < k then tap j h else w0, hF', hRB', ?_, ?_, ?_⟩
      · rw [nonNotCount_append, hnn, hnn_e, hf j0, hfilt, Finset.sum_insert hj0_nm]; omega
      · rw [notCount_append, hnc, hnc_e, hfilt, Finset.sum_insert hj0_nm]; omega
      · intro j hj
        dsimp only
        split_ifs with hlt
        · obtain ⟨ht_lt, ht_val⟩ := hvals j hlt
          refine ⟨by simp; omega, fun l => ?_⟩
          have := W_append_old gs extra (prefixInput n l) (tap j hlt) (by rw [prefixInput_len]; exact ht_lt)
          exact this.trans (ht_val l)
        · have hj_eq : j = j0 := Fin.ext (by simp [j0]; omega)
          subst hj_eq
          exact ⟨hw0_lt, hw0_val⟩
  obtain ⟨gs, tap, hF, hRB, hnn, hnc, hvals⟩ := hstep d (le_refl d)
  have hall : Finset.univ.filter (fun j : Fin d => j.val < d) = Finset.univ := by
    ext j; simp [j.isLt]
  rw [hall] at hnn hnc
  have hsum_blk : ∑ j : Fin d, (colorBlock color j).card = n := by
    have hbi : (Finset.univ : Finset (Fin d)).biUnion (colorBlock color) = Finset.univ := by
      ext i; simp [mem_colorBlock]
    have hc := Finset.card_biUnion (s := (Finset.univ : Finset (Fin d)))
      (t := colorBlock color) (fun j _ k _ hne => colorBlock_disjoint color hne)
    rw [hbi] at hc
    simpa using hc.symm
  have hsum_sub : ∑ j : Fin d, ((colorBlock color j).card - 1) + d = n := by
    have h1 : ∑ j : Fin d, ((colorBlock color j).card - 1 + 1) =
        ∑ j : Fin d, (colorBlock color j).card := by
      apply Finset.sum_congr rfl
      intro j _
      have := Finset.card_pos.2 (colorBlock_nonempty hsurj j)
      omega
    rw [Finset.sum_add_distrib] at h1
    simpa [hsum_blk] using h1
  refine ⟨gs, fun j => tap j j.isLt, hF, hRB, by omega, hnc, fun j => hvals j j.isLt⟩

def Fit (d n : ℕ) (X : Fin (n + 1) → Finset (Fin d)) (a : ℕ) (M : Fin (a + 1) → Finset (Fin d))
    (phase : Fin (a + 1) → Bool) (b : ℕ) : Prop :=
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin d → Nat) (out : Fin (a+1) → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ j, tap j < n+2+C.size) ∧ (∀ t, out t < n+2+C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ n-1 ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      ∀ l, let w := C.wires (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false,true])
           (∀ j, w.getD (tap j) false = decide (j ∈ X l)) ∧
           ∀ t, w.getD (out t) false = Bool.xor (phase t) (decide (((X l) ∩ M t).card % 2 = 1))

def IsUp {n d : ℕ} (color : Fin n → Fin d) (f : Fin (n + 1) → Bool) : Prop :=
  (chg f).Nonempty ∧ ∀ j, colorBlock color j ⊆ chg f ∨ Disjoint (colorBlock color j) (chg f)

theorem up_of_union {n d : ℕ} (color : Fin n → Fin d) (f : Fin (n + 1) → Bool)
    (hne : (chg f).Nonempty) (h : ∀ i i', color i = color i' → i ∈ chg f → i' ∈ chg f) :
    IsUp color f := by
  refine ⟨hne, fun j => ?_⟩
  by_cases hj : ∃ i ∈ chg f, color i = j
  · left
    obtain ⟨i, hi, hc⟩ := hj
    intro i' hi'
    rw [mem_colorBlock] at hi'
    exact h i i' (hc.trans hi'.symm) hi
  · right
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [mem_colorBlock] at hi
    exact hj ⟨i, hi', hi⟩

theorem wval {n d : ℕ} (color : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j)
    (f : Fin (n + 1) → Bool) (j : Fin d) (hf : chg f = colorBlock color j) :
    ∀ l, f l = Bool.xor (Bool.xor (f 0) (decide (j ∈ X 0))) (decide (j ∈ X l)) := by
  have h := eq_or_not_of_chg_eq (f := f) (g := fun l => decide (j ∈ X l))
    (by rw [hf, chg_tap color X hX j])
  intro l
  rcases h with h | h
  · rw [h 0, h l]; cases decide (j ∈ X 0) <;> cases decide (j ∈ X l) <;> rfl
  · rw [h 0, h l]; cases decide (j ∈ X 0) <;> cases decide (j ∈ X l) <;> rfl

theorem sum_blocks {n d : ℕ} (color : Fin n → Fin d) :
    ∑ j : Fin d, (colorBlock color j).card = n := by
  have hbi : (Finset.univ : Finset (Fin d)).biUnion (colorBlock color) = Finset.univ := by
    ext i; simp [mem_colorBlock]
  have hc := Finset.card_biUnion (s := (Finset.univ : Finset (Fin d)))
    (t := colorBlock color) (fun j _ k _ hne => colorBlock_disjoint color hne)
  rw [hbi] at hc
  simpa using hc.symm

open Classical in
theorem transfer {d : ℕ} (hd : 0 < d) {nA nB : ℕ} (X : Fin (nA + 1) → Finset (Fin d))
    (Y : Fin (nB + 1) → Finset (Fin d)) (cA : Fin nA → Fin d) (cB : Fin nB → Fin d)
    (hsA : Function.Surjective cA) (hsB : Function.Surjective cB)
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ cA i = j)
    (hY : ∀ i j, (decide (j ∈ Y i.castSucc) ≠ decide (j ∈ Y i.succ)) ↔ cB i = j)
    (hst : ∀ l', ∃ l, X l = Y l') (h0 : X 0 = Y 0) (hl : X (Fin.last nA) = Y (Fin.last nB))
    (a : ℕ) (M : Fin (a + 1) → Finset (Fin d)) (phase : Fin (a + 1) → Bool)
    (hM0 : M 0 = Finset.univ) (β β' : ℕ) (hβ : 2 * β + nB ≤ 2 * β' + nA)
    (hfit : Fit d nA X a M phase β) : Fit d nB Y a M phase β' := by
  obtain ⟨C, tap, out, hF, hR, -, htap, hout, hP, hQ, hval⟩ := hfit
  set gs := C.gates with hgs
  have hF' : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ := hF
  have hR' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (nA + 2) ⟨gs, 0⟩ := hR
  have hsize : C.size = gs.length := rfl
  set F := vl nA gs with hFdef
  have hvt : ∀ j l, F (tap j) l = decide (j ∈ X l) := fun j l => (hval l).1 j
  have hvo : ∀ t l, F (out t) l = Bool.xor (phase t) (decide ((X l ∩ M t).card % 2 = 1)) :=
    fun t l => (hval l).2 t
  have hnA : 0 < nA := by
    obtain ⟨i, _⟩ := hsA ⟨0, hd⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have htapchg : ∀ j, chg (F (tap j)) = colorBlock cA j := by
    intro j
    rw [show F (tap j) = fun l => decide (j ∈ X l) from funext (hvt j)]
    exact chg_tap cA X hX j
  have houtchg : ∀ t i, i ∈ chg (F (out t)) ↔ cA i ∈ M t := by
    intro t i
    rw [show F (out t) = fun l => Bool.xor (phase t) (decide ((X l ∩ M t).card % 2 = 1))
      from funext (hvo t)]
    exact chg_par cA X hX (M t) (phase t) i
  have hroot : chg (F (out 0)) = Finset.univ := by
    ext i
    rw [houtchg 0 i, hM0]
    simp
  have hnn_tot := notCount_add_nonNotCount C
  have hPn : nonNotCount gs ≤ nA - 1 := by
    have : nonNotCount C.gates = C.size - PEqualNP.NotBracket.notCount C := by omega
    rw [← hgs] at this
    omega
  obtain ⟨hLam, -, -⟩ := tight_structure nA hnA C (out 0) (hout 0) hF hR hP hroot
  have hLam' : ∀ u < nA + 2 + gs.length, ∀ v < nA + 2 + gs.length, Lam (chg (F u)) (chg (F v)) :=
    hLam
  have hMg := tight_merge nA hnA gs hF' hR' hPn (out 0) hroot
  have hcb := count_bounds nA gs hF' hR' hLam' hMg
  have hsz : ∀ j, tap j < nA + 2 + gs.length := htap
  have hex : ∀ j, ∃ u, chg (F u) = colorBlock cA j := fun j => ⟨tap j, htapchg j⟩
  set w : Fin d → ℕ := fun j => Nat.find (hex j) with hwdef
  have hw : ∀ j, chg (F (w j)) = colorBlock cA j := fun j => Nat.find_spec (hex j)
  have hwmin : ∀ j u, chg (F u) = colorBlock cA j → w j ≤ u := fun j u h => Nat.find_min' (hex j) h
  have hwN : ∀ j, w j < nA + 2 + gs.length := fun j =>
    lt_of_le_of_lt (hwmin j _ (htapchg j)) (hsz j)
  have hupc : ∀ x, IsUp cA (F x) → (∃ j, x = w j) ∨ (nA + 2 ≤ x ∧ ∀ j, x ≠ w j) := by
    intro x hx
    by_cases hw' : ∃ j, x = w j
    · exact Or.inl hw'
    right
    push_neg at hw'
    refine ⟨?_, hw'⟩
    by_contra hlt
    push_neg at hlt
    by_cases hxn : x < nA
    · obtain ⟨i0, hi0⟩ := hx.1
      have hi0v := chg_input nA gs x hxn i0 hi0
      set j := cA i0
      have hsub : colorBlock cA j ⊆ chg (F x) := by
        rcases hx.2 j with h | h
        · exact h
        · exact absurd hi0 (Finset.disjoint_left.1 h ((mem_colorBlock cA j i0).2 rfl))
      have heq : chg (F x) = colorBlock cA j := by
        apply Finset.Subset.antisymm _ hsub
        intro i hi
        have := chg_input nA gs x hxn i hi
        have : i = i0 := Fin.ext (by omega)
        rw [this]; exact (mem_colorBlock cA j i0).2 rfl
      have hle := hwmin j x heq
      rcases Nat.lt_or_eq_of_le hle with hlt' | heq'
      · have hi0w : i0 ∈ chg (F (w j)) := by rw [hw j]; exact (mem_colorBlock cA j i0).2 rfl
        have := chg_input nA gs (w j) (by omega) i0 hi0w
        omega
      · exact hw' j heq'.symm
    · have hc : x = nA ∨ x = nA + 1 := by omega
      have := chg_const_wire nA gs x hc
      obtain ⟨i0, hi0⟩ := hx.1
      rw [this] at hi0; simp at hi0
  have hupin : ∀ k < gs.length, IsUp cA (F (nA + 2 + k)) → (∀ j, nA + 2 + k ≠ w j) →
      ∀ x ∈ usedIns (gs.getD k dg), IsUp cA (F x) := by
    intro k hk hup hnw x hx
    cases hg : isNotGate (gs.getD k dg) with
    | true =>
      have hv := vl_gate nA gs k hk hR'
      rw [(isNotGate_eq_true _).1 hg] at hv
      rcases not_eval_cases F (F (nA + 2 + k)) _ hv with ⟨_, he⟩ | ⟨a', rest, hins, hfa⟩
      · exact absurd hup.1 (by rw [he]; simp)
      · have hxa : x = a' := by
          unfold usedIns at hx; rw [if_pos hg, hins] at hx; simpa using hx
        subst hxa
        have hc : chg (F (nA + 2 + k)) = chg (F x) := chg_congr (Or.inr hfa)
        unfold IsUp; rw [← hc]; exact hup
    | false =>
      obtain ⟨a', b', hins, ha, hb, -, hane, hbne, hdis, hun⟩ :=
        merge_struct nA gs hF' hR' hLam' k hk hg (hMg k hk hg)
      have hx' : x = a' ∨ x = b' := by
        unfold usedIns at hx; rw [if_neg (by rw [hg]; decide), hins] at hx; simpa using hx
      have side : ∀ p q, chg (F (nA + 2 + k)) = chg (F p) ∪ chg (F q) → (chg (F p)).Nonempty →
          Disjoint (chg (F p)) (chg (F q)) → p < nA + 2 + gs.length → q < nA + 2 + gs.length →
          IsUp cA (F p) := by
        intro p q hpq hpne hdpq hp hq
        refine ⟨hpne, fun j => ?_⟩
        rcases hLam' p hp (tap j) (hsz j) with h | h | h
        · rw [htapchg] at h
          left
          have hBu : colorBlock cA j ⊆ chg (F (nA + 2 + k)) := by
            rcases hup.2 j with h' | h'
            · exact h'
            · exfalso
              obtain ⟨i, hi⟩ := hpne
              exact Finset.disjoint_left.1 h' (h hi) (by rw [hpq]; exact Finset.mem_union_left _ hi)
          rcases hLam' q hq (tap j) (hsz j) with h2 | h2 | h2
          · rw [htapchg] at h2
            exfalso
            have heq : chg (F (nA + 2 + k)) = colorBlock cA j :=
              Finset.Subset.antisymm (by rw [hpq]; exact Finset.union_subset h h2) hBu
            have hle := hwmin j _ heq
            have hlt : w j < nA + 2 + k := lt_of_le_of_ne hle (fun h => hnw j h.symm)
            exact not_merging_of_sub F _ (w j) hlt (by rw [hw j, heq]) (hMg k hk hg)
          · rw [htapchg] at h2
            exfalso
            obtain ⟨i, hi⟩ := hpne
            exact Finset.disjoint_left.1 hdpq hi (h2 (h hi))
          · rw [htapchg] at h2
            intro i hi
            have := hBu hi
            rw [hpq] at this
            rcases Finset.mem_union.1 this with h3 | h3
            · exact h3
            · exact absurd hi (Finset.disjoint_left.1 h2 h3)
        · rw [htapchg] at h; left; exact h
        · rw [htapchg] at h; right; exact h.symm
      rcases hx' with rfl | rfl
      · exact side x b' hun hane hdis (by omega) (by omega)
      · exact side x a' (by rw [hun, Finset.union_comm]) hbne hdis.symm (by omega) (by omega)
  set s : Fin d → Bool := fun j => Bool.xor (F (w j) 0) (decide (j ∈ X 0)) with hsdef
  have hwv : ∀ j l, F (w j) l = Bool.xor (s j) (decide (j ∈ X l)) :=
    fun j => wval cA X hX (F (w j)) j (hw j)
  set fB : Fin d → Fin (nB + 1) → Bool := fun j l' => Bool.xor (s j) (decide (j ∈ Y l'))
    with hfBdef
  have hfBchg : ∀ j, chg (fB j) = colorBlock cB j := by
    intro j
    rw [← chg_tap cB Y hY j]
    apply chg_congr
    by_cases hs : s j = true
    · right; intro t; show Bool.xor (s j) _ = _; rw [hs]; cases decide (j ∈ Y t) <;> rfl
    · left; intro t; show Bool.xor (s j) _ = _; rw [Bool.not_eq_true] at hs; rw [hs]
      cases decide (j ∈ Y t) <;> rfl
  obtain ⟨gsB, tapB, hFB, hRB, hnnB, hncB, hvB⟩ := build_all cB hsB fB hfBchg
  set σ0 : ℕ → ℕ := fun u => if chg (F u) = ∅ then (if F u 0 then nB + 1 else nB)
    else if h : ∃ j, u = w j then tapB h.choose else 0 with hσ0
  set Base : ℕ → Prop := fun u => chg (F u) = ∅ ∨ ∃ j, u = w j with hBase
  set Rep : ℕ → Prop := fun k => IsUp cA (F (nA + 2 + k)) ∧ ∀ j, nA + 2 + k ≠ w j with hRep
  have hbase : ∀ u, Base u → σ0 u < nB + 2 + gsB.length ∧
      ∀ l l', X l = Y l' → vl nA gs u l = vl nB gsB (σ0 u) l' := by
    intro u hu
    by_cases hce : chg (F u) = ∅
    · have hcst := const_of_chg_empty hce
      have hs0 : σ0 u = if F u 0 then nB + 1 else nB := by simp only [hσ0]; rw [if_pos hce]
      rw [hs0]
      cases hF0 : F u 0
      · refine ⟨by simp; omega, fun l l' _ => ?_⟩
        rw [if_neg (by simp), vl_false]
        show F u l = false
        rw [hcst l 0, hF0]
      · refine ⟨by simp; omega, fun l l' _ => ?_⟩
        rw [if_pos rfl, vl_true]
        show F u l = true
        rw [hcst l 0, hF0]
    · have hex' : ∃ j, u = w j := by
        rcases hu with h | h
        · exact absurd h hce
        · exact h
      have hs0 : σ0 u = tapB hex'.choose := by
        simp only [hσ0]; rw [if_neg hce, dif_pos hex']
      rw [hs0]
      refine ⟨(hvB _).1, fun l l' hE => ?_⟩
      rw [(hvB _).2 l']
      have hj : F u l = F (w hex'.choose) l := congrArg (fun x => F x l) hex'.choose_spec
      show F u l = fB hex'.choose l'
      rw [hj, hwv, hE]
  have hrepb : ∀ k, Rep k → ¬ Base (nA + 2 + k) := by
    intro k hk hb
    rcases hb with h | ⟨j, hj⟩
    · obtain ⟨i, hi⟩ := hk.1.1
      rw [h] at hi; simp at hi
    · exact hk.2 j hj
  have hdom_up : ∀ x, IsUp cA (F x) → Base x ∨ (nA + 2 ≤ x ∧ Rep (x - (nA + 2))) := by
    intro x hx
    rcases hupc x hx with h | ⟨h1, h2⟩
    · exact Or.inl (Or.inr h)
    · right
      refine ⟨h1, ?_, ?_⟩
      · rw [Nat.add_sub_cancel' h1]; exact hx
      · rw [Nat.add_sub_cancel' h1]; exact h2
  have hrepin : ∀ k < gs.length, Rep k → ∀ x ∈ usedIns (gs.getD k dg),
      Base x ∨ (nA + 2 ≤ x ∧ Rep (x - (nA + 2))) := by
    intro k hk hr x hx
    exact hdom_up x (hupin k hk hr.1 hr.2 x hx)
  obtain ⟨T, σ, hFT, hRT, hncT, hnnT, hvalT⟩ :=
    replay nA nB gs gsB hF' hR' hFB hRB (fun l l' => X l = Y l') Base Rep σ0 hbase hrepb hrepin
      gs.length le_rfl
  have hszo : ∀ t, out t < nA + 2 + gs.length := hout
  have hupTap : ∀ j, IsUp cA (F (tap j)) := by
    intro j
    refine ⟨by rw [htapchg]; exact colorBlock_nonempty hsA j, fun j' => ?_⟩
    rw [htapchg]
    by_cases hjj : j' = j
    · left; rw [hjj]
    · right; exact colorBlock_disjoint cA hjj
  have hdomTap : ∀ j, Base (tap j) ∨ (nA + 2 ≤ tap j ∧ Rep (tap j - (nA + 2))) :=
    fun j => hdom_up _ (hupTap j)
  have hdomOut : ∀ t, Base (out t) ∨ (nA + 2 ≤ out t ∧ Rep (out t - (nA + 2))) := by
    intro t
    by_cases hce : chg (F (out t)) = ∅
    · exact Or.inl (Or.inl hce)
    · apply hdom_up
      apply up_of_union cA _ (Finset.nonempty_iff_ne_empty.2 hce)
      intro i i' hii' hi
      rw [houtchg] at hi ⊢
      rw [← hii']; exact hi
  have hNOTsj : ∀ j, (falls (F (w j))).card ≤ (NOTs nA gs (w j) (colorBlock cA j)).card ∧
      (colorBlock cA j).card ≤ (NNs nA gs (w j) (colorBlock cA j)).card + 1 := by
    intro j
    have := hcb (w j) (hwN j) (by rw [hw j]; exact colorBlock_nonempty hsA j)
    rw [hw j] at this
    exact this
  have hNOTrep : ∀ j k, k ∈ NOTs nA gs (w j) (colorBlock cA j) → ¬ Rep k := by
    intro j k hk hr
    unfold NOTs at hk
    rw [Finset.mem_filter] at hk
    obtain ⟨_, hle, _, hne, hsub⟩ := hk
    have hBu : colorBlock cA j ⊆ chg (F (nA + 2 + k)) := by
      rcases hr.1.2 j with h | h
      · exact h
      · exfalso; obtain ⟨i, hi⟩ := hne; exact Finset.disjoint_left.1 h (hsub hi) hi
    have heq := Finset.Subset.antisymm hsub hBu
    have := hwmin j _ heq
    exact hr.2 j (by omega)
  have hNNrep : ∀ j k, k ∈ NNs nA gs (w j) (colorBlock cA j) → ¬ Rep k := by
    intro j k hk hr
    unfold NNs at hk
    rw [Finset.mem_filter] at hk
    obtain ⟨_, hle, _, hne, hsub⟩ := hk
    have hBu : colorBlock cA j ⊆ chg (F (nA + 2 + k)) := by
      rcases hr.1.2 j with h | h
      · exact h
      · exfalso; obtain ⟨i, hi⟩ := hne; exact Finset.disjoint_left.1 h (hsub hi) hi
    have heq := Finset.Subset.antisymm hsub hBu
    have := hwmin j _ heq
    exact hr.2 j (by omega)
  set UN := (Finset.univ : Finset (Fin d)).biUnion fun j => NOTs nA gs (w j) (colorBlock cA j)
  set UNN := (Finset.univ : Finset (Fin d)).biUnion fun j => NNs nA gs (w j) (colorBlock cA j)
  have hUN : UN.card = ∑ j, (NOTs nA gs (w j) (colorBlock cA j)).card :=
    Finset.card_biUnion (fun j _ j' _ hne => NOTs_disj nA gs _ _ (colorBlock_disjoint cA hne))
  have hUNN : UNN.card = ∑ j, (NNs nA gs (w j) (colorBlock cA j)).card :=
    Finset.card_biUnion (fun j _ j' _ hne => NNs_disj nA gs _ _ (colorBlock_disjoint cA hne))
  set RN := (Finset.range gs.length).filter fun k' => Rep k' ∧ isNotGate (gs.getD k' dg) = true
  set RNN := (Finset.range gs.length).filter fun k' => Rep k' ∧ isNotGate (gs.getD k' dg) = false
  have hA1 : UN.card + RN.card ≤ PEqualNP.NotBracket.notCount C := by
    have hdj : Disjoint UN RN := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      rw [Finset.mem_biUnion] at hk
      obtain ⟨j, _, hj⟩ := hk
      exact hNOTrep j k hj (Finset.mem_filter.1 hk').2.1
    rw [← Finset.card_union_of_disjoint hdj]
    have : PEqualNP.NotBracket.notCount C = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ := rfl
    rw [this, notCount_eq_card]
    apply Finset.card_le_card
    intro k hk
    rw [Finset.mem_filter]
    rcases Finset.mem_union.1 hk with hk | hk
    · rw [Finset.mem_biUnion] at hk
      obtain ⟨j, _, hj⟩ := hk
      unfold NOTs at hj
      rw [Finset.mem_filter] at hj
      exact ⟨hj.1, hj.2.2.1⟩
    · rw [Finset.mem_filter] at hk
      exact ⟨hk.1, hk.2.2⟩
  have hA2 : UNN.card + RNN.card ≤ nonNotCount gs := by
    have hdj : Disjoint UNN RNN := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      rw [Finset.mem_biUnion] at hk
      obtain ⟨j, _, hj⟩ := hk
      exact hNNrep j k hj (Finset.mem_filter.1 hk').2.1
    rw [← Finset.card_union_of_disjoint hdj, nonNot_eq_card]
    apply Finset.card_le_card
    intro k hk
    rw [Finset.mem_filter]
    rcases Finset.mem_union.1 hk with hk | hk
    · rw [Finset.mem_biUnion] at hk
      obtain ⟨j, _, hj⟩ := hk
      unfold NNs at hj
      rw [Finset.mem_filter] at hj
      exact ⟨hj.1, hj.2.2.1⟩
    · rw [Finset.mem_filter] at hk
      exact ⟨hk.1, hk.2.2⟩
  have hfallsle : ∑ j, (falls (F (w j))).card ≤ ∑ j, (NOTs nA gs (w j) (colorBlock cA j)).card :=
    Finset.sum_le_sum (fun j _ => (hNOTsj j).1)
  have hblkle : nA ≤ ∑ j, (NNs nA gs (w j) (colorBlock cA j)).card + d := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hNOTsj j).2)
    rw [sum_blocks, Finset.sum_add_distrib] at this
    simpa using this
  have hfallsEq : ∀ j, 2 * (falls (fB j)).card + (colorBlock cA j).card =
      2 * (falls (F (w j))).card + (colorBlock cB j).card := by
    intro j
    have h1 := two_falls (fB j)
    have h2 := two_falls (F (w j))
    rw [hfBchg] at h1
    rw [hw] at h2
    have e0 : fB j 0 = F (w j) 0 := by
      show Bool.xor _ _ = _; rw [hwv j 0, h0]
    have e1 : fB j (Fin.last nB) = F (w j) (Fin.last nA) := by
      show Bool.xor _ _ = _; rw [hwv j (Fin.last nA), hl]
    rw [e0, e1] at h1
    omega
  have hsumEq : 2 * ∑ j, (falls (fB j)).card + nA = 2 * ∑ j, (falls (F (w j))).card + nB := by
    have hA := sum_blocks cA
    have hB := sum_blocks cB
    have hS := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin d))) rfl (fun j _ => hfallsEq j)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hS
    omega
  have hncC : PEqualNP.NotBracket.notCount ⟨gsB ++ T, 0⟩ = ∑ j, (falls (fB j)).card + RN.card := by
    rw [notCount_append, hncB, hncT]
    congr 1
    apply congrArg Finset.card
    ext k
    simp only [RN, Finset.mem_filter]
  have hnnC : nonNotCount (gsB ++ T) = nonNotCount gsB + RNN.card := by
    rw [nonNotCount_append, hnnT]
    congr 1
    apply congrArg Finset.card
    ext k
    simp only [RNN, Finset.mem_filter]
  have hszC := notCount_add_nonNotCount ⟨gsB ++ T, 0⟩
  have hdpos : 0 < d := hd
  refine ⟨⟨gsB ++ T, 0⟩, fun j => σ (tap j), fun t => σ (out t), hFT, hRT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < nB + 2 + (gsB ++ T).length; omega
  · intro j; exact (hvalT (tap j) (hsz j) (hdomTap j)).1
  · intro t; exact (hvalT (out t) (hszo t) (hdomOut t)).1
  · show (gsB ++ T).length - _ ≤ nB - 1
    have : (gsB ++ T).length = PEqualNP.NotBracket.notCount ⟨gsB ++ T, 0⟩ + nonNotCount (gsB ++ T) :=
      hszC.symm
    omega
  · show PEqualNP.NotBracket.notCount ⟨gsB ++ T, 0⟩ ≤ β'
    omega
  · intro l'
    obtain ⟨l, hl'⟩ := hst l'
    refine ⟨fun j => ?_, fun t => ?_⟩
    · have := (hvalT (tap j) (hsz j) (hdomTap j)).2 l l' hl'
      show vl nB (gsB ++ T) (σ (tap j)) l' = _
      rw [← this]; exact (hvt j l).trans (by rw [hl'])
    · have := (hvalT (out t) (hszo t) (hdomOut t)).2 l l' hl'
      show vl nB (gsB ++ T) (σ (out t)) l' = _
      rw [← this]; exact (hvo t l).trans (by rw [hl'])

def Adj {d : ℕ} (A B : Finset (Fin d)) : Prop :=
  ∃ c : Fin d, ∀ j, (decide (j ∈ A) ≠ decide (j ∈ B)) ↔ c = j

def hdist {d : ℕ} (A B : Finset (Fin d)) : ℕ := ((A \ B) ∪ (B \ A)).card

theorem adj_symm {d : ℕ} {A B : Finset (Fin d)} (h : Adj A B) : Adj B A := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun j => ?_⟩
  rw [← hc j]
  constructor <;> intro h e <;> exact h e.symm

theorem adj_same {d : ℕ} {A B : Finset (Fin d)} {c j : Fin d}
    (hc : ∀ j, (decide (j ∈ A) ≠ decide (j ∈ B)) ↔ c = j) (hj : c ≠ j) : (j ∈ A ↔ j ∈ B) := by
  have := (hc j).not.2 hj
  rw [not_not] at this
  simpa using this

theorem hdist_self {d : ℕ} (A : Finset (Fin d)) : hdist A A = 0 := by simp [hdist]

theorem hdist_adj {d : ℕ} (Z p x : Finset (Fin d)) (h : Adj p x) : hdist Z x ≤ hdist Z p + 1 := by
  obtain ⟨c, hc⟩ := h
  unfold hdist
  have hsub : (Z \ x) ∪ (x \ Z) ⊆ insert c ((Z \ p) ∪ (p \ Z)) := by
    intro j hj
    rw [Finset.mem_insert]
    by_cases hjc : c = j
    · left; exact hjc.symm
    · right
      have hsame := adj_same hc hjc
      simp only [Finset.mem_union, Finset.mem_sdiff] at hj ⊢
      tauto
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_insert_le _ _

def PathOK {d : ℕ} (x0 v : Finset (Fin d)) (S : Finset (Finset (Fin d)))
    (L : List (Finset (Fin d))) : Prop :=
  L.head? = some x0 ∧ L.getLast? = some v ∧ L.IsChain Adj ∧ L.toFinset = S ∧
    L.length + hdist x0 v + 1 ≤ 2 * S.card

theorem path_append {d : ℕ} {x0 p x : Finset (Fin d)} {S : Finset (Finset (Fin d))}
    {L : List (Finset (Fin d))} (hL : PathOK x0 p S L) (hpx : Adj p x) (hx : x ∉ S) :
    PathOK x0 x (insert x S) (L ++ [x]) := by
  obtain ⟨hh, hlast, hch, hfs, hlen⟩ := hL
  have hne : L ≠ [] := by intro h; rw [h] at hh; simp at hh
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_append, hh]; rfl
  · simp
  · rw [List.isChain_append]
    refine ⟨hch, List.isChain_singleton x, ?_⟩
    intro a ha b hb
    rw [hlast] at ha
    simp at ha hb
    rw [← ha, ← hb]
    exact hpx
  · rw [List.toFinset_append, hfs]
    ext y; simp [or_comm]
  · rw [Finset.card_insert_of_notMem hx]
    have := hdist_adj x0 p x hpx
    simp only [List.length_append, List.length_singleton]
    omega

theorem path_splice {d : ℕ} {x0 v p x : Finset (Fin d)} {S : Finset (Finset (Fin d))}
    {L : List (Finset (Fin d))} (hL : PathOK x0 v S L) (hp : p ∈ S) (hpx : Adj p x) (hx : x ∉ S) :
    ∃ L', PathOK x0 v (insert x S) L' := by
  obtain ⟨hh, hlast, hch, hfs, hlen⟩ := hL
  have hpL : p ∈ L := by rw [← List.mem_toFinset, hfs]; exact hp
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hpL
  refine ⟨s ++ p :: x :: p :: t, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hh]; cases s <;> rfl
  · rw [← hlast, List.getLast?_append_cons, List.getLast?_append_cons, List.getLast?_cons_cons,
      List.getLast?_cons_cons]
  · rw [List.isChain_append] at hch ⊢
    obtain ⟨h1, h2, h3⟩ := hch
    refine ⟨h1, ?_, ?_⟩
    · rw [List.isChain_cons_cons, List.isChain_cons_cons]
      exact ⟨hpx, adj_symm hpx, h2⟩
    · intro a ha b hb
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      exact h3 a ha b (by simp [hb])
  · rw [← hfs]
    ext y; simp
  · rw [Finset.card_insert_of_notMem hx]
    simp only [List.length_append, List.length_cons] at hlen ⊢
    omega

theorem shorten_inv {n d : ℕ} (color : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) :
    ∀ k ≤ n, ∀ v ∈ (Finset.univ.filter (fun l : Fin (n + 1) => l.val ≤ k)).image X,
      ∃ L, PathOK (X 0) v ((Finset.univ.filter (fun l : Fin (n + 1) => l.val ≤ k)).image X) L := by
  intro k
  induction k with
  | zero =>
    intro _ v hv
    have hS : (Finset.univ.filter (fun l : Fin (n + 1) => l.val ≤ 0)).image X = {X 0} := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Nat.le_zero]
      constructor
      · rintro ⟨l, hl, rfl⟩
        rw [show l = 0 from Fin.ext hl]
      · rintro rfl; exact ⟨0, rfl, rfl⟩
    rw [hS] at hv ⊢
    rw [Finset.mem_singleton] at hv
    subst hv
    refine ⟨[X 0], rfl, rfl, List.isChain_singleton _, by simp, ?_⟩
    simp [hdist_self]
  | succ k ih =>
    intro hk v hv
    set S := (Finset.univ.filter (fun l : Fin (n + 1) => l.val ≤ k)).image X with hSdef
    set p := X ⟨k, by omega⟩
    set x := X ⟨k + 1, by omega⟩
    have hS' : (Finset.univ.filter (fun l : Fin (n + 1) => l.val ≤ k + 1)).image X = insert x S := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, hSdef, x]
      constructor
      · rintro ⟨l, hl, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hl) with h | h
        · right; exact ⟨l, by omega, rfl⟩
        · left; rw [show l = ⟨k + 1, by omega⟩ from Fin.ext h]
      · rintro (rfl | ⟨l, hl, rfl⟩)
        · exact ⟨⟨k + 1, by omega⟩, le_rfl, rfl⟩
        · exact ⟨l, by omega, rfl⟩
    have hpS : p ∈ S := by
      rw [hSdef, Finset.mem_image]
      exact ⟨⟨k, by omega⟩, by simp, rfl⟩
    have hpx : Adj p x := ⟨color ⟨k, by omega⟩, fun j => hX ⟨k, by omega⟩ j⟩
    rw [hS'] at hv ⊢
    by_cases hxS : x ∈ S
    · rw [Finset.insert_eq_of_mem hxS] at hv ⊢
      exact ih (by omega) v hv
    · rw [Finset.mem_insert] at hv
      rcases hv with heq | hv
      · obtain ⟨L, hL⟩ := ih (by omega) p hpS
        rw [heq]
        exact ⟨L ++ [x], path_append hL hpx hxS⟩
      · obtain ⟨L, hL⟩ := ih (by omega) v hv
        exact path_splice hL hpS hpx hxS

theorem list_const_coord {d : ℕ} (L : List (Finset (Fin d))) (j : Fin d)
    (h : ∀ i (hi : i + 1 < L.length), (j ∈ L[i] ↔ j ∈ L[i + 1])) :
    ∀ A ∈ L, ∀ B ∈ L, (j ∈ A ↔ j ∈ B) := by
  have key : ∀ i (hi : i < L.length), (j ∈ L[i] ↔ j ∈ L[0]'(by omega)) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih => intro hi; rw [← h i hi]; exact ih (by omega)
  intro A hA B hB
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hA
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hB
  rw [key a ha, key b hb]

theorem shorten {n d : ℕ} (X : Fin (n + 1) → Finset (Fin d)) (color : Fin n → Fin d)
    (hsurj : Function.Surjective color)
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) :
    ∃ (m : ℕ) (Y : Fin (m + 1) → Finset (Fin d)), m ≤ n ∧
      (∃ color' : Fin m → Fin d, Function.Surjective color' ∧
        ∀ i j, (decide (j ∈ Y i.castSucc) ≠ decide (j ∈ Y i.succ)) ↔ color' i = j) ∧
      Finset.univ.image X = Finset.univ.image Y ∧ X 0 = Y 0 ∧ X (Fin.last n) = Y (Fin.last m) ∧
      m + ((X 0 \ X (Fin.last n)) ∪ (X (Fin.last n) \ X 0)).card ≤
        2 * ((Finset.univ.image X).card - 1) := by
  have hall : (Finset.univ.filter (fun l : Fin (n + 1) => l.val ≤ n)).image X =
      Finset.univ.image X := by
    congr 1; ext l; simp [Nat.lt_succ_iff.1 l.isLt]
  have hlastmem : X (Fin.last n) ∈ (Finset.univ.filter (fun l : Fin (n + 1) => l.val ≤ n)).image X := by
    rw [hall]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  obtain ⟨L, hh, hlast, hch, hfs, hlen⟩ := shorten_inv color X hX n le_rfl _ hlastmem
  rw [hall] at hfs hlen
  set S := Finset.univ.image X with hSdef
  have hScard : 1 ≤ S.card := Finset.card_pos.2 ⟨X 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hLne : L ≠ [] := by intro h; rw [h] at hh; simp at hh
  have hLpos : 0 < L.length := List.length_pos_iff.2 hLne
  by_cases hshort : L.length ≤ n + 1
  · set m := L.length - 1 with hm
    have hLm : L.length = m + 1 := by omega
    set Y : Fin (m + 1) → Finset (Fin d) := fun i => L[i.val]'(by omega) with hYdef
    have hadj : ∀ i : Fin m, Adj (Y i.castSucc) (Y i.succ) := by
      intro i
      exact hch.getElem i.val (by have := i.isLt; omega)
    choose color' hcol using hadj
    have hYS : Finset.univ.image Y = S := by
      rw [← hfs]
      ext A
      simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
      constructor
      · rintro ⟨i, rfl⟩; exact List.getElem_mem _
      · intro hA
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
        exact ⟨⟨i, by omega⟩, rfl⟩
    have hY0 : Y 0 = X 0 := by
      show L[0] = X 0
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hLpos] at hh
      exact Option.some.inj hh
    have hYl : Y (Fin.last m) = X (Fin.last n) := by
      show L[m] = X (Fin.last n)
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
      have := Option.some.inj hlast
      rw [← this]
    refine ⟨m, Y, by omega, ⟨color', ?_, fun i j => (hcol i j).trans ⟨fun h => h, fun h => h⟩⟩,
      hYS.symm, hY0.symm, hYl.symm, ?_⟩
    · intro j
      by_contra hno
      push_neg at hno
      obtain ⟨i0, hi0⟩ := hsurj j
      have hdiff := (hX i0 j).2 hi0
      have hconst := list_const_coord L j (by
        intro i hi
        have := hcol ⟨i, by omega⟩ j
        have hne : color' ⟨i, by omega⟩ ≠ j := hno _
        have := (this.not).2 hne
        rw [not_not] at this
        simpa [Y] using this)
      have hA : X i0.castSucc ∈ L := by
        rw [← List.mem_toFinset, hfs]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      have hB : X i0.succ ∈ L := by
        rw [← List.mem_toFinset, hfs]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      apply hdiff
      simp only [decide_eq_decide]
      exact hconst _ hA _ hB
    · unfold hdist at hlen
      omega
  · refine ⟨n, X, le_rfl, ⟨color, hsurj, hX⟩, rfl, rfl, rfl, ?_⟩
    unfold hdist at hlen
    omega

theorem walk_parity {n d : ℕ} (color : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) :
    n + ∑ j : Fin d, (decide (j ∈ X 0)).toNat =
      2 * ∑ j : Fin d, (falls (fun l => decide (j ∈ X l))).card +
        ∑ j : Fin d, (decide (j ∈ X (Fin.last n))).toNat := by
  have h := fun j => two_falls (fun l => decide (j ∈ X l))
  have hS := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin d))) rfl (fun j _ => h j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hS
  have hc : ∑ j : Fin d, (chg (fun l => decide (j ∈ X l))).card = n := by
    refine (Finset.sum_congr rfl (fun j _ => ?_)).trans (sum_blocks color)
    rw [chg_tap color X hX j]
  rw [hc] at hS
  omega

end PEqualNP.Outside.L_lib_1390

theorem PEqualNP.Outside.L_lib_1390 :
    ∀ d : Nat, 0 < d →
  let walk := fun (n : Nat) (X : Fin (n+1) → Finset (Fin d)) =>
    ∃ color : Fin n → Fin d, Function.Surjective color ∧
      ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j
  let states := fun (n : Nat) (X : Fin (n+1) → Finset (Fin d)) => Finset.univ.image X
  let fit := fun (n : Nat) (X : Fin (n+1) → Finset (Fin d)) (a : Nat)
    (M : Fin (a+1) → Finset (Fin d)) (phase : Fin (a+1) → Bool) (b : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin d → Nat) (out : Fin (a+1) → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ j, tap j < n+2+C.size) ∧ (∀ t, out t < n+2+C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ n-1 ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      ∀ l, let w := C.wires (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false,true])
           (∀ j, w.getD (tap j) false = decide (j ∈ X l)) ∧
           ∀ t, w.getD (out t) false = Bool.xor (phase t) (decide (((X l) ∩ M t).card % 2 = 1))
  (∀ (n m : Nat) (X : Fin (n+1) → Finset (Fin d)) (Y : Fin (m+1) → Finset (Fin d)),
    walk n X → walk m Y → m ≤ n → states n X = states m Y →
    X 0 = Y 0 → X (Fin.last n) = Y (Fin.last m) →
    (n-m) % 2 = 0 ∧ ∀ (a : Nat) (M : Fin (a+1) → Finset (Fin d))
      (phase : Fin (a+1) → Bool) (b : Nat), M 0 = Finset.univ →
      (fit n X a M phase (b+(n-m)/2) ↔ fit m Y a M phase b)) ∧
  ∀ (n : Nat) (X : Fin (n+1) → Finset (Fin d)), walk n X →
    ∃ (m : Nat) (Y : Fin (m+1) → Finset (Fin d)), m ≤ n ∧ walk m Y ∧
      states n X = states m Y ∧ X 0 = Y 0 ∧ X (Fin.last n) = Y (Fin.last m) ∧
      m + ((X 0 \ X (Fin.last n)) ∪ (X (Fin.last n) \ X 0)).card ≤ 2*((states n X).card-1) := by
  intro d hd walk states fit
  refine ⟨?_, ?_⟩
  · intro n m X Y hwX hwY hmn hst h0 hl
    obtain ⟨cA, hsA, hX⟩ := hwX
    obtain ⟨cB, hsB, hY⟩ := hwY
    have hpar : (n - m) % 2 = 0 := by
      have p1 := PEqualNP.Outside.L_lib_1390.walk_parity cA X hX
      have p2 := PEqualNP.Outside.L_lib_1390.walk_parity cB Y hY
      simp only [h0, hl] at p1
      omega
    refine ⟨hpar, ?_⟩
    intro a M phase b hM0
    have hst1 : ∀ l', ∃ l, X l = Y l' := by
      intro l'
      have hm : Y l' ∈ states n X := by
        rw [hst]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      obtain ⟨l, _, hl'⟩ := Finset.mem_image.1 hm
      exact ⟨l, hl'⟩
    have hst2 : ∀ l, ∃ l', Y l' = X l := by
      intro l
      have hm : X l ∈ states m Y := by
        rw [← hst]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      obtain ⟨l', _, hl'⟩ := Finset.mem_image.1 hm
      exact ⟨l', hl'⟩
    constructor
    · intro hfit
      exact PEqualNP.Outside.L_lib_1390.transfer hd X Y cA cB hsA hsB hX hY hst1 h0 hl a M phase hM0
        (b + (n - m) / 2) b (by omega) hfit
    · intro hfit
      exact PEqualNP.Outside.L_lib_1390.transfer hd Y X cB cA hsB hsA hY hX hst2 h0.symm hl.symm
        a M phase hM0 b (b + (n - m) / 2) (by omega) hfit
  · intro n X hw
    obtain ⟨c, hs, hX⟩ := hw
    exact PEqualNP.Outside.L_lib_1390.shorten X c hs hX


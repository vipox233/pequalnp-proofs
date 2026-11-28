import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1388

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

inductive ROTree (d : ℕ) where
  | var (j : Fin d) (neg : Bool)
  | bin (isOr : Bool) (l r : ROTree d)

namespace ROTree

def eval {d : ℕ} : ROTree d → Finset (Fin d) → Bool
  | var j b, S => if b then !decide (j ∈ S) else decide (j ∈ S)
  | bin isOr l r, S => if isOr then (l.eval S || r.eval S) else (l.eval S && r.eval S)

def vars {d : ℕ} : ROTree d → Finset (Fin d)
  | var j _ => {j}
  | bin _ l r => l.vars ∪ r.vars

def readOnce {d : ℕ} : ROTree d → Prop
  | var _ _ => True
  | bin _ l r => l.readOnce ∧ r.readOnce ∧ Disjoint l.vars r.vars

def posAt {d : ℕ} (j : Fin d) : ROTree d → Prop
  | var k b => k = j → b = false
  | bin _ l r => l.posAt j ∧ r.posAt j

def allPos {d : ℕ} : ROTree d → Prop
  | var _ b => b = false
  | bin _ l r => l.allPos ∧ r.allPos

def neg {d : ℕ} : ROTree d → ROTree d
  | var j b => var j (!b)
  | bin isOr l r => bin (!isOr) l.neg r.neg

def binCount {d : ℕ} : ROTree d → ℕ
  | var _ _ => 0
  | bin _ l r => l.binCount + r.binCount + 1

theorem eval_neg {d : ℕ} (T : ROTree d) (S : Finset (Fin d)) :
    T.neg.eval S = !T.eval S := by
  induction T with
  | var j b => cases b <;> simp [neg, eval]
  | bin isOr l r ihl ihr => cases isOr <;> simp [neg, eval, ihl, ihr]

theorem vars_neg {d : ℕ} (T : ROTree d) : T.neg.vars = T.vars := by
  induction T with
  | var _ _ => rfl
  | bin _ l r ihl ihr => simp [neg, vars, ihl, ihr]

theorem readOnce_neg {d : ℕ} {T : ROTree d} (h : T.readOnce) : T.neg.readOnce := by
  induction T with
  | var _ _ => trivial
  | bin _ l r ihl ihr =>
    obtain ⟨hl, hr, hdj⟩ := h
    exact ⟨ihl hl, ihr hr, by rw [vars_neg, vars_neg]; exact hdj⟩

theorem vars_nonempty {d : ℕ} (T : ROTree d) : T.vars.Nonempty := by
  induction T with
  | var j _ => exact ⟨j, Finset.mem_singleton_self j⟩
  | bin _ l _ ihl _ =>
    obtain ⟨j, hj⟩ := ihl
    exact ⟨j, Finset.mem_union_left _ hj⟩

theorem binCount_add_one {d : ℕ} {T : ROTree d} (h : T.readOnce) :
    T.binCount + 1 = T.vars.card := by
  induction T with
  | var j _ => simp [binCount, vars]
  | bin _ l r ihl ihr =>
    obtain ⟨hl, hr, hdj⟩ := h
    simp only [binCount, vars, Finset.card_union_of_disjoint hdj]
    have h1 := ihl hl
    have h2 := ihr hr
    omega

theorem eval_congr {d : ℕ} (T : ROTree d) {S₁ S₂ : Finset (Fin d)}
    (h : ∀ j ∈ T.vars, (j ∈ S₁ ↔ j ∈ S₂)) : T.eval S₁ = T.eval S₂ := by
  induction T with
  | var j b =>
    have hj : j ∈ S₁ ↔ j ∈ S₂ := h j (Finset.mem_singleton_self j)
    cases b <;> simp [eval, hj]
  | bin isOr l r ihl ihr =>
    have hl := ihl fun j hj => h j (Finset.mem_union_left _ hj)
    have hr := ihr fun j hj => h j (Finset.mem_union_right _ hj)
    cases isOr <;> simp [eval, hl, hr]

theorem posAt_of_not_mem {d : ℕ} {T : ROTree d} {j : Fin d} (hj : j ∉ T.vars) :
    T.posAt j := by
  induction T with
  | var k b =>
    intro hkj
    subst hkj
    exact absurd (Finset.mem_singleton_self k) hj
  | bin _ l r ihl ihr =>
    exact ⟨ihl fun h => hj (Finset.mem_union_left _ h),
           ihr fun h => hj (Finset.mem_union_right _ h)⟩

theorem allPos_of_forall_posAt {d : ℕ} {T : ROTree d} (h : ∀ j, T.posAt j) : T.allPos := by
  induction T with
  | var j b => exact h j rfl
  | bin _ l r ihl ihr => exact ⟨ihl fun j => (h j).1, ihr fun j => (h j).2⟩

theorem flip_pos {d : ℕ} {T : ROTree d} (hro : T.readOnce) (j : Fin d) {S₁ S₂ : Finset (Fin d)}
    (hagree : ∀ k ≠ j, (k ∈ S₁ ↔ k ∈ S₂))
    (hne : T.eval S₁ ≠ T.eval S₂)
    (hdir : T.eval S₂ = decide (j ∈ S₂)) : T.posAt j := by
  induction T with
  | var k b =>
    intro hkj
    subst hkj
    cases b
    · rfl
    · simp only [eval, ↓reduceIte] at hdir
      cases h : decide (k ∈ S₂) <;> simp [h] at hdir
  | bin isOr l r ihl ihr =>
    obtain ⟨hl_ro, hr_ro, hdj⟩ := hro
    by_cases hjl : j ∈ l.vars
    · have hjr : j ∉ r.vars := Finset.disjoint_left.1 hdj hjl
      have hr_eq : r.eval S₁ = r.eval S₂ :=
        eval_congr r fun k hk => hagree k (fun hkj => hjr (hkj ▸ hk))
      have hl_ne : l.eval S₁ ≠ l.eval S₂ := by
        intro heq
        apply hne
        cases isOr <;> simp [eval, heq, hr_eq]
      have hl_dir : l.eval S₂ = decide (j ∈ S₂) := by
        rw [← hdir]
        cases isOr
        · simp only [eval, Bool.false_eq_true, ↓reduceIte, hr_eq] at hne ⊢
          exact (bool_and_l _ _ _ hne.symm).symm
        · simp only [eval, ↓reduceIte, hr_eq] at hne ⊢
          exact (bool_or_l _ _ _ hne.symm).symm
      exact ⟨ihl hl_ro hl_ne hl_dir, posAt_of_not_mem hjr⟩
    · by_cases hjr : j ∈ r.vars
      · have hl_eq : l.eval S₁ = l.eval S₂ :=
          eval_congr l fun k hk => hagree k (fun hkj => hjl (hkj ▸ hk))
        have hr_ne : r.eval S₁ ≠ r.eval S₂ := by
          intro heq
          apply hne
          cases isOr <;> simp [eval, hl_eq, heq]
        have hr_dir : r.eval S₂ = decide (j ∈ S₂) := by
          rw [← hdir]
          cases isOr
          · simp only [eval, Bool.false_eq_true, ↓reduceIte, hl_eq] at hne ⊢
            exact (bool_and_r _ _ _ hne.symm).symm
          · simp only [eval, ↓reduceIte, hl_eq] at hne ⊢
            exact (bool_or_r _ _ _ hne.symm).symm
        exact ⟨posAt_of_not_mem hjl, ihr hr_ro hr_ne hr_dir⟩
      · exfalso
        have hl_eq : l.eval S₁ = l.eval S₂ :=
          eval_congr l fun k hk => hagree k (fun hkj => hjl (hkj ▸ hk))
        have hr_eq : r.eval S₁ = r.eval S₂ :=
          eval_congr r fun k hk => hagree k (fun hkj => hjr (hkj ▸ hk))
        apply hne
        cases isOr <;> simp [eval, hl_eq, hr_eq]

def compileAux {d : ℕ} : ROTree d → List Gate → List Gate × ℕ
  | var j _, gs => (gs, j.val)
  | bin isOr l r, gs =>
      let (gs1, wl) := l.compileAux gs
      let (gs2, wr) := r.compileAux gs1
      let g : Gate := ⟨if isOr then GateOp.or else GateOp.and, [wl, wr]⟩
      (gs2 ++ [g], d + 2 + gs2.length)

def stateInput {d : ℕ} (S : Finset (Fin d)) : List Bool :=
  List.ofFn (fun j : Fin d => decide (j ∈ S)) ++ [false, true]

theorem stateInput_len {d : ℕ} (S : Finset (Fin d)) : (stateInput S).length = d + 2 := by
  simp [stateInput]

theorem stateInput_lt {d : ℕ} (S : Finset (Fin d)) (j : Fin d) :
    (stateInput S).getD j.val false = decide (j ∈ S) := by
  unfold stateInput
  rw [List.getD_append _ _ _ _ (by simp [j.isLt])]
  rw [List.getD_eq_getElem _ _ (by simp [j.isLt])]
  simp

theorem compileAux_spec {d : ℕ} (T : ROTree d) (hpos : T.allPos) (gs : List Gate)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) ⟨gs, 0⟩)
    (hN : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = 0) :
    let res := T.compileAux gs
    ∃ extra : List Gate,
      res.1 = gs ++ extra ∧
      extra.length = T.binCount ∧
      res.2 < d + 2 + res.1.length ∧
      PEqualNP.MetaComplexity.FanInTwo ⟨res.1, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) ⟨res.1, 0⟩ ∧
      PEqualNP.NotBracket.notCount ⟨res.1, 0⟩ = 0 ∧
      ∀ S : Finset (Fin d), (W res.1 (stateInput S)).getD res.2 false = T.eval S := by
  induction T generalizing gs with
  | var j b =>
    have hb : b = false := hpos
    subst hb
    refine ⟨[], by simp [compileAux], rfl, by simp [compileAux]; omega, hF, hR, hN, ?_⟩
    intro S
    simp only [compileAux, eval, Bool.false_eq_true, ↓reduceIte]
    have h0 := W_append_old [] gs (stateInput S) j.val (by rw [stateInput_len]; simp; omega)
    exact h0.trans (stateInput_lt S j)
  | bin isOr l r ihl ihr =>
    obtain ⟨hlp, hrp⟩ := hpos
    obtain ⟨el, h1_eq, h1_len, h1_lt, h1_F, h1_R, h1_N, h1_eval⟩ :=
      ihl hlp gs hF hR hN
    set gs1 := (l.compileAux gs).1
    set wl := (l.compileAux gs).2
    obtain ⟨er, h2_eq, h2_len, h2_lt, h2_F, h2_R, h2_N, h2_eval⟩ :=
      ihr hrp gs1 h1_F h1_R h1_N
    set gs2 := (r.compileAux gs1).1
    set wr := (r.compileAux gs1).2
    let g : Gate := ⟨if isOr then GateOp.or else GateOp.and, [wl, wr]⟩
    have hres1 : (bin isOr l r).compileAux gs = (gs2 ++ [g], d + 2 + gs2.length) := rfl
    have hwl_lt2 : wl < d + 2 + gs2.length := by
      rw [h2_eq, List.length_append]; omega
    refine ⟨el ++ er ++ [g], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hres1, h2_eq, h1_eq]; simp [List.append_assoc]
    · simp [binCount, h1_len, h2_len]; omega
    · rw [hres1]; simp
    · rw [hres1]
      apply fanInTwo_append h2_F
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      cases isOr <;> simp [g]
    · rw [hres1]
      apply readsBack_snoc h2_R
      intro i hi
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hwl_lt2
      · exact h2_lt
    · rw [hres1, notCount_append, h2_N, notCount_eq_filter]
      cases isOr <;> simp [isNotGate, g]
    · intro S
      rw [hres1]
      have hnw := new_wire gs2 g (stateInput S)
      rw [stateInput_len] at hnw
      rw [hnw]
      have hwl_val : (W gs2 (stateInput S)).getD wl false = l.eval S := by
        rw [h2_eq, W_append_old gs1 er (stateInput S) wl (by rw [stateInput_len]; exact h1_lt)]
        exact h1_eval S
      have hwr_val : (W gs2 (stateInput S)).getD wr false = r.eval S := h2_eval S
      cases isOr
      · simp only [g, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, GateOp.eval,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, eval, hwl_val, hwr_val]
      · simp only [g, ↓reduceIte, List.map_cons, List.map_nil, GateOp.eval,
          List.any_cons, List.any_nil, id_eq, Bool.or_false, eval, hwl_val, hwr_val]

theorem minterm_meet_zero_cert {d : ℕ} (T : ROTree d) (hro : T.readOnce) (hpos : T.allPos)
    (A B : Finset (Fin d))
    (hA1 : T.eval A = true)
    (hA0 : ∀ j ∈ A ∩ T.vars, T.eval (A.erase j) = false)
    (hB0 : T.eval (Finset.univ \ B) = false)
    (hB1 : ∀ j ∈ B ∩ T.vars, T.eval (insert j (Finset.univ \ B)) = true) :
    (A ∩ B ∩ T.vars).card ≤ 1 := by
  induction T with
  | var k b =>
    calc (A ∩ B ∩ (var k b).vars).card
        ≤ ({k} : Finset (Fin d)).card := Finset.card_le_card Finset.inter_subset_right
      _ = 1 := Finset.card_singleton k
  | bin isOr l r ihl ihr =>
    obtain ⟨hl_ro, hr_ro, hdj⟩ := hro
    obtain ⟨hl_pos, hr_pos⟩ := hpos
    cases isOr
    · 
      simp only [eval, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hA1
      obtain ⟨hlA1, hrA1⟩ := hA1
      have hlA0 : ∀ j ∈ A ∩ l.vars, l.eval (A.erase j) = false := by
        intro j hj
        have hjl : j ∈ l.vars := (Finset.mem_inter.1 hj).2
        have hjr : j ∉ r.vars := Finset.disjoint_left.1 hdj hjl
        have hr_eq : r.eval (A.erase j) = r.eval A :=
          eval_congr r fun k hk => by
            have hne : k ≠ j := fun h => hjr (h ▸ hk)
            simp [Finset.mem_erase, hne]
        have hT0 := hA0 j (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_union_left _ hjl⟩)
        simp only [eval, Bool.false_eq_true, ↓reduceIte, hr_eq, hrA1, Bool.and_true] at hT0
        exact hT0
      have hrA0 : ∀ j ∈ A ∩ r.vars, r.eval (A.erase j) = false := by
        intro j hj
        have hjr : j ∈ r.vars := (Finset.mem_inter.1 hj).2
        have hjl : j ∉ l.vars := Finset.disjoint_right.1 hdj hjr
        have hl_eq : l.eval (A.erase j) = l.eval A :=
          eval_congr l fun k hk => by
            have hne : k ≠ j := fun h => hjl (h ▸ hk)
            simp [Finset.mem_erase, hne]
        have hT0 := hA0 j (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_union_right _ hjr⟩)
        simp only [eval, Bool.false_eq_true, ↓reduceIte, hl_eq, hlA1, Bool.true_and] at hT0
        exact hT0
      simp only [eval, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_false_iff] at hB0
      cases hlB : l.eval (Finset.univ \ B)
      · cases hrB : r.eval (Finset.univ \ B)
        · 
          have hempty : A ∩ B ∩ (bin false l r).vars = ∅ := by
            ext j; simp only [Finset.notMem_empty, iff_false]
            intro hj
            have hjB : j ∈ B := (Finset.mem_inter.1 (Finset.mem_inter.1 hj).1).2
            have hjT : j ∈ l.vars ∪ r.vars := (Finset.mem_inter.1 hj).2
            have hT1 := hB1 j (Finset.mem_inter.2 ⟨hjB, hjT⟩)
            simp only [eval, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hT1
            rcases Finset.mem_union.1 hjT with hjl | hjr
            · have hjr' : j ∉ r.vars := Finset.disjoint_left.1 hdj hjl
              have hr_eq : r.eval (insert j (Finset.univ \ B)) = r.eval (Finset.univ \ B) :=
                eval_congr r fun k hk => by
                  have hne : k ≠ j := fun h => hjr' (h ▸ hk)
                  simp [Finset.mem_insert, hne]
              rw [hr_eq, hrB] at hT1; exact Bool.false_ne_true hT1.2
            · have hjl' : j ∉ l.vars := Finset.disjoint_right.1 hdj hjr
              have hl_eq : l.eval (insert j (Finset.univ \ B)) = l.eval (Finset.univ \ B) :=
                eval_congr l fun k hk => by
                  have hne : k ≠ j := fun h => hjl' (h ▸ hk)
                  simp [Finset.mem_insert, hne]
              rw [hl_eq, hlB] at hT1; exact Bool.false_ne_true hT1.1
          rw [hempty]; simp
        · 
          have hBr : ∀ j ∈ r.vars, j ∉ B := by
            intro j hjr hjB
            have hjl' : j ∉ l.vars := Finset.disjoint_right.1 hdj hjr
            have hl_eq : l.eval (insert j (Finset.univ \ B)) = l.eval (Finset.univ \ B) :=
              eval_congr l fun k hk => by
                have hne : k ≠ j := fun h => hjl' (h ▸ hk)
                simp [Finset.mem_insert, hne]
            have hT1 := hB1 j (Finset.mem_inter.2 ⟨hjB, Finset.mem_union_right _ hjr⟩)
            simp only [eval, Bool.false_eq_true, ↓reduceIte, hl_eq, hlB, Bool.false_and] at hT1
          have heq : A ∩ B ∩ (bin false l r).vars = A ∩ B ∩ l.vars := by
            ext j; simp only [Finset.mem_inter, vars, Finset.mem_union]
            constructor
            · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
              · exact ⟨⟨h1, h2⟩, h3⟩
              · exact absurd h2 (hBr j h3)
            · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, Or.inl h3⟩
          rw [heq]
          apply ihl hl_ro hl_pos hlA1 hlA0 hlB
          intro j hj
          have hT1 := hB1 j (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_union_left _ (Finset.mem_inter.1 hj).2⟩)
          simp only [eval, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hT1
          exact hT1.1
      · have hrB : r.eval (Finset.univ \ B) = false := by
          rcases hB0 with h | h
          · rw [hlB] at h; exact absurd h (by decide)
          · exact h
        have hBl : ∀ j ∈ l.vars, j ∉ B := by
          intro j hjl hjB
          have hjr' : j ∉ r.vars := Finset.disjoint_left.1 hdj hjl
          have hr_eq : r.eval (insert j (Finset.univ \ B)) = r.eval (Finset.univ \ B) :=
            eval_congr r fun k hk => by
              have hne : k ≠ j := fun h => hjr' (h ▸ hk)
              simp [Finset.mem_insert, hne]
          have hT1 := hB1 j (Finset.mem_inter.2 ⟨hjB, Finset.mem_union_left _ hjl⟩)
          simp only [eval, Bool.false_eq_true, ↓reduceIte, hr_eq, hrB, Bool.and_false] at hT1
        have heq : A ∩ B ∩ (bin false l r).vars = A ∩ B ∩ r.vars := by
          ext j; simp only [Finset.mem_inter, vars, Finset.mem_union]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
            · exact absurd h2 (hBl j h3)
            · exact ⟨⟨h1, h2⟩, h3⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, Or.inr h3⟩
        rw [heq]
        apply ihr hr_ro hr_pos hrA1 hrA0 hrB
        intro j hj
        have hT1 := hB1 j (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_union_right _ (Finset.mem_inter.1 hj).2⟩)
        simp only [eval, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hT1
        exact hT1.2
    · 
      simp only [eval, ↓reduceIte, Bool.or_eq_false_iff] at hB0
      obtain ⟨hlB0, hrB0⟩ := hB0
      have hlB1 : ∀ j ∈ B ∩ l.vars, l.eval (insert j (Finset.univ \ B)) = true := by
        intro j hj
        have hjl : j ∈ l.vars := (Finset.mem_inter.1 hj).2
        have hjr : j ∉ r.vars := Finset.disjoint_left.1 hdj hjl
        have hr_eq : r.eval (insert j (Finset.univ \ B)) = r.eval (Finset.univ \ B) :=
          eval_congr r fun k hk => by
            have hne : k ≠ j := fun h => hjr (h ▸ hk)
            simp [Finset.mem_insert, hne]
        have hT1 := hB1 j (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_union_left _ hjl⟩)
        simp only [eval, ↓reduceIte, hr_eq, hrB0, Bool.or_false] at hT1
        exact hT1
      have hrB1 : ∀ j ∈ B ∩ r.vars, r.eval (insert j (Finset.univ \ B)) = true := by
        intro j hj
        have hjr : j ∈ r.vars := (Finset.mem_inter.1 hj).2
        have hjl : j ∉ l.vars := Finset.disjoint_right.1 hdj hjr
        have hl_eq : l.eval (insert j (Finset.univ \ B)) = l.eval (Finset.univ \ B) :=
          eval_congr l fun k hk => by
            have hne : k ≠ j := fun h => hjl (h ▸ hk)
            simp [Finset.mem_insert, hne]
        have hT1 := hB1 j (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_union_right _ hjr⟩)
        simp only [eval, ↓reduceIte, hl_eq, hlB0, Bool.false_or] at hT1
        exact hT1
      simp only [eval, ↓reduceIte, Bool.or_eq_true] at hA1
      cases hlA : l.eval A
      · have hrA : r.eval A = true := by
          rcases hA1 with h | h
          · rw [hlA] at h; exact absurd h Bool.false_ne_true
          · exact h
        have hAl : ∀ j ∈ l.vars, j ∉ A := by
          intro j hjl hjA
          have hjr' : j ∉ r.vars := Finset.disjoint_left.1 hdj hjl
          have hr_eq : r.eval (A.erase j) = r.eval A :=
            eval_congr r fun k hk => by
              have hne : k ≠ j := fun h => hjr' (h ▸ hk)
              simp [Finset.mem_erase, hne]
          have hT0 := hA0 j (Finset.mem_inter.2 ⟨hjA, Finset.mem_union_left _ hjl⟩)
          simp only [eval, ↓reduceIte, hr_eq, hrA, Bool.or_true] at hT0
          exact absurd hT0 (by decide)
        have heq : A ∩ B ∩ (bin true l r).vars = A ∩ B ∩ r.vars := by
          ext j; simp only [Finset.mem_inter, vars, Finset.mem_union]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
            · exact absurd h1 (hAl j h3)
            · exact ⟨⟨h1, h2⟩, h3⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, Or.inr h3⟩
        rw [heq]
        apply ihr hr_ro hr_pos hrA _ hrB0 hrB1
        intro j hj
        have hT0 := hA0 j (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_union_right _ (Finset.mem_inter.1 hj).2⟩)
        simp only [eval, ↓reduceIte, Bool.or_eq_false_iff] at hT0
        exact hT0.2
      · cases hrA : r.eval A
        · have hAr : ∀ j ∈ r.vars, j ∉ A := by
            intro j hjr hjA
            have hjl' : j ∉ l.vars := Finset.disjoint_right.1 hdj hjr
            have hl_eq : l.eval (A.erase j) = l.eval A :=
              eval_congr l fun k hk => by
                have hne : k ≠ j := fun h => hjl' (h ▸ hk)
                simp [Finset.mem_erase, hne]
            have hT0 := hA0 j (Finset.mem_inter.2 ⟨hjA, Finset.mem_union_right _ hjr⟩)
            simp only [eval, ↓reduceIte, hl_eq, hlA, Bool.true_or] at hT0
            exact absurd hT0 (by decide)
          have heq : A ∩ B ∩ (bin true l r).vars = A ∩ B ∩ l.vars := by
            ext j; simp only [Finset.mem_inter, vars, Finset.mem_union]
            constructor
            · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
              · exact ⟨⟨h1, h2⟩, h3⟩
              · exact absurd h1 (hAr j h3)
            · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, Or.inl h3⟩
          rw [heq]
          apply ihl hl_ro hl_pos hlA _ hlB0 hlB1
          intro j hj
          have hT0 := hA0 j (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_union_left _ (Finset.mem_inter.1 hj).2⟩)
          simp only [eval, ↓reduceIte, Bool.or_eq_false_iff] at hT0
          exact hT0.1
        · have hempty : A ∩ B ∩ (bin true l r).vars = ∅ := by
            ext j; simp only [Finset.notMem_empty, iff_false]
            intro hj
            have hjA : j ∈ A := (Finset.mem_inter.1 (Finset.mem_inter.1 hj).1).1
            have hjT : j ∈ l.vars ∪ r.vars := (Finset.mem_inter.1 hj).2
            have hT0 := hA0 j (Finset.mem_inter.2 ⟨hjA, hjT⟩)
            simp only [eval, ↓reduceIte, Bool.or_eq_false_iff] at hT0
            rcases Finset.mem_union.1 hjT with hjl | hjr
            · have hjr' : j ∉ r.vars := Finset.disjoint_left.1 hdj hjl
              have hr_eq : r.eval (A.erase j) = r.eval A :=
                eval_congr r fun k hk => by
                  have hne : k ≠ j := fun h => hjr' (h ▸ hk)
                  simp [Finset.mem_erase, hne]
              rw [hr_eq, hrA] at hT0; exact absurd hT0.2 (by decide)
            · have hjl' : j ∉ l.vars := Finset.disjoint_right.1 hdj hjr
              have hl_eq : l.eval (A.erase j) = l.eval A :=
                eval_congr l fun k hk => by
                  have hne : k ≠ j := fun h => hjl' (h ▸ hk)
                  simp [Finset.mem_erase, hne]
              rw [hl_eq, hlA] at hT0; exact absurd hT0.1 (by decide)
          rw [hempty]; simp

end ROTree

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

theorem physical_to_tree {n d b : ℕ} (color : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (R : Fin (n + 1) → Bool) (hd : 0 < d) (hsurj : Function.Surjective color)
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j)
    (hR : ∀ i, R i.castSucc ≠ R i.succ ∧ R i.succ = decide (color i ∈ X i.succ))
    (C : Circuit) (root : ℕ) (tap : Fin d → ℕ)
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hroot_lt : root < n + 2 + C.size) (htap_lt : ∀ j, tap j < n + 2 + C.size)
    (hP : C.size - PEqualNP.NotBracket.notCount C ≤ n - 1)
    (hQ : PEqualNP.NotBracket.notCount C ≤ b)
    (hval : ∀ l, vl n C.gates root l = R l ∧ ∀ j, vl n C.gates (tap j) l = decide (j ∈ X l)) :
    (falls R).card ≤ b ∧
    ∃ T : ROTree d, T.readOnce ∧ T.allPos ∧ T.vars = Finset.univ ∧ ∀ l, T.eval (X l) = R l := by
  obtain ⟨i0, -⟩ := hsurj ⟨0, hd⟩
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i0.isLt
  have hroot_eq : vl n C.gates root = R := funext fun l => (hval l).1
  have htap_eq : ∀ j, vl n C.gates (tap j) = fun l => decide (j ∈ X l) :=
    fun j => funext fun l => (hval l).2 j
  have hroot_chg : chg (vl n C.gates root) = Finset.univ := by
    ext i; rw [mem_chg, hroot_eq]; simp [(hR i).1]
  have htap_chg : ∀ j, chg (vl n C.gates (tap j)) = colorBlock color j := by
    intro j; ext i; rw [mem_chg, htap_eq, mem_colorBlock]; exact hX i j
  obtain ⟨hlam, hgood, hfalls_le⟩ :=
    tight_structure n hn C root hroot_lt hF hRB hP hroot_chg
  have hfalls_b : (falls R).card ≤ b := by
    rw [← hroot_eq]; exact le_trans hfalls_le hQ
  have hbuild : ∀ (u : ℕ), u < n + 2 + C.size →
      ∀ (S : Finset (Fin d)), S.Nonempty →
        chg (vl n C.gates u) = S.biUnion (colorBlock color) →
        ∃ T : ROTree d, T.readOnce ∧ T.vars = S ∧ ∀ l, vl n C.gates u l = T.eval (X l) := by
    intro u
    induction u using Nat.strongRecOn with
    | ind u ih =>
      intro hu S hSne hchg_u
      by_cases hcard1 : S.card = 1
      · obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hcard1
        have hchg_eq : chg (vl n C.gates u) = chg (fun l => decide (j ∈ X l)) := by
          rw [hchg_u, Finset.singleton_biUnion, ← htap_chg j, htap_eq j]
        rcases eq_or_not_of_chg_eq hchg_eq with heq | hneq
        · exact ⟨.var j false, trivial, rfl, fun l => by simpa [ROTree.eval] using heq l⟩
        · exact ⟨.var j true, trivial, rfl, fun l => by simpa [ROTree.eval] using hneq l⟩
      · have hcard2 : 2 ≤ S.card := by
          have := Finset.card_pos.2 hSne; omega
        have hge : n + 2 ≤ u := by
          by_contra hlt
          push_neg at hlt
          have hle1 : (chg (vl n C.gates u)).card ≤ 1 := by
            have heq_in : vl n C.gates u = vl n [] u := by
              funext l
              exact W_append_old [] C.gates (prefixInput n l) u (by rw [prefixInput_len]; simp; omega)
            rw [heq_in]
            by_cases hu_n : u < n
            · rw [chg_input_lt n u hu_n]; simp
            · rw [chg_input_const n u (Nat.le_of_not_lt hu_n)]; simp
          have hge2 : 2 ≤ (S.biUnion (colorBlock color)).card := by
            rw [Finset.card_biUnion (fun j _ k _ hjk => colorBlock_disjoint color hjk)]
            have h1 : S.card ≤ ∑ j ∈ S, (colorBlock color j).card := by
              calc S.card = ∑ _j ∈ S, 1 := by simp
                _ ≤ ∑ j ∈ S, (colorBlock color j).card :=
                    Finset.sum_le_sum fun j _ => Finset.card_pos.2 (colorBlock_nonempty hsurj j)
            omega
          rw [hchg_u] at hle1; omega
        rcases hgood u hge hu with hconst | ⟨a, ha, hs⟩ | ⟨a, ha, b, hb, hna, hnb, hdj, hun, hop⟩
        · exfalso
          have hemp : chg (vl n C.gates u) = ∅ := chg_const hconst
          obtain ⟨j, hj⟩ := hSne
          obtain ⟨i, hi⟩ := colorBlock_nonempty hsurj j
          have hi' : i ∈ chg (vl n C.gates u) := by
            rw [hchg_u]; exact Finset.mem_biUnion.2 ⟨j, hj, hi⟩
          rw [hemp] at hi'; exact Finset.notMem_empty i hi'
        · have hchg_a : chg (vl n C.gates a) = S.biUnion (colorBlock color) := by
            rw [← hchg_u]; exact (chg_congr hs).symm
          obtain ⟨Ta, ha_ro, ha_vars, ha_eval⟩ := ih a ha (lt_trans ha hu) S hSne hchg_a
          rcases hs with hs | hs
          · exact ⟨Ta, ha_ro, ha_vars, fun l => by rw [hs l, ha_eval l]⟩
          · exact ⟨Ta.neg, ROTree.readOnce_neg ha_ro, by rw [ROTree.vars_neg, ha_vars],
              fun l => by rw [hs l, ha_eval l, ROTree.eval_neg]⟩
        · have hno_ssub : ∀ x y : ℕ, x < n + 2 + C.size → y < n + 2 + C.size →
              (chg (vl n C.gates x)).Nonempty →
              Disjoint (chg (vl n C.gates x)) (chg (vl n C.gates y)) →
              chg (vl n C.gates x) ∪ chg (vl n C.gates y) = S.biUnion (colorBlock color) →
              ∀ j : Fin d, ¬ (chg (vl n C.gates x) ⊂ colorBlock color j) := by
            intro x y _ hy hnx hdj_xy hun_xy j hssub
            have hsub_x : chg (vl n C.gates x) ⊆ colorBlock color j := hssub.1
            obtain ⟨i1, hi1⟩ := hnx
            have hi1_B : i1 ∈ colorBlock color j := hsub_x hi1
            have hjS : j ∈ S := by
              have : i1 ∈ S.biUnion (colorBlock color) := by
                rw [← hun_xy]; exact Finset.mem_union_left _ hi1
              obtain ⟨j', hj'S, hi1'⟩ := Finset.mem_biUnion.1 this
              have hjj : j' = j := ((mem_colorBlock color j' i1).1 hi1').symm.trans ((mem_colorBlock color j i1).1 hi1_B)
              rwa [← hjj]
            obtain ⟨i2, hi2_B, hi2_nx⟩ : ∃ i2 ∈ colorBlock color j, i2 ∉ chg (vl n C.gates x) := by
              by_contra hall
              push_neg at hall
              exact hssub.2 hall
            have hi2_y : i2 ∈ chg (vl n C.gates y) := by
              have : i2 ∈ chg (vl n C.gates x) ∪ chg (vl n C.gates y) := by
                rw [hun_xy]; exact Finset.mem_biUnion.2 ⟨j, hjS, hi2_B⟩
              rcases Finset.mem_union.1 this with h | h
              · exact absurd h hi2_nx
              · exact h
            obtain ⟨j', hj'S, hj'ne⟩ : ∃ j' ∈ S, j' ≠ j := by
              have hne : (S.erase j).Nonempty := Finset.card_pos.1 (by
                rw [Finset.card_erase_of_mem hjS]; omega)
              obtain ⟨j', hj'⟩ := hne
              exact ⟨j', (Finset.mem_erase.1 hj').2, (Finset.mem_erase.1 hj').1⟩
            obtain ⟨i3, hi3_B'⟩ := colorBlock_nonempty hsurj j'
            have hi3_y : i3 ∈ chg (vl n C.gates y) := by
              have : i3 ∈ chg (vl n C.gates x) ∪ chg (vl n C.gates y) := by
                rw [hun_xy]; exact Finset.mem_biUnion.2 ⟨j', hj'S, hi3_B'⟩
              rcases Finset.mem_union.1 this with h | h
              · exact absurd (hsub_x h) (Finset.disjoint_left.1 (colorBlock_disjoint color hj'ne) hi3_B')
              · exact h
            have hlam_yj := hlam y hy (tap j) (htap_lt j)
            rw [htap_chg j] at hlam_yj
            rcases hlam_yj with h1 | h2 | h3
            · exact Finset.disjoint_left.1 (colorBlock_disjoint color hj'ne) hi3_B' (h1 hi3_y)
            · exact Finset.disjoint_left.1 hdj_xy hi1 (h2 hi1_B)
            · exact Finset.disjoint_left.1 h3 hi2_y hi2_B
          have hmacro : ∀ x : ℕ, x < n + 2 + C.size →
              (∀ j : Fin d, ¬ (chg (vl n C.gates x) ⊂ colorBlock color j)) →
              chg (vl n C.gates x) =
                (Finset.univ.filter fun j => colorBlock color j ⊆ chg (vl n C.gates x)).biUnion
                  (colorBlock color) := by
            intro x hx hns
            ext i
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hi
              refine ⟨color i, ?_, (mem_colorBlock color (color i) i).2 rfl⟩
              have hlx := hlam x hx (tap (color i)) (htap_lt (color i))
              rw [htap_chg (color i)] at hlx
              rcases hlx with h1 | h2 | h3
              · by_contra hnsub
                exact hns (color i) (Finset.ssubset_iff_subset_ne.2 ⟨h1, fun he => hnsub (he ▸ Finset.Subset.refl _)⟩)
              · exact h2
              · exact absurd ((mem_colorBlock color (color i) i).2 rfl) (Finset.disjoint_left.1 h3 hi)
            · rintro ⟨j, hj_sub, hi_B⟩
              exact hj_sub hi_B
          have hSa_eq := hmacro a (lt_trans ha hu) (hno_ssub a b (lt_trans ha hu) (lt_trans hb hu) hna hdj (hun.symm.trans hchg_u))
          have hSb_eq := hmacro b (lt_trans hb hu) (hno_ssub b a (lt_trans hb hu) (lt_trans ha hu) hnb hdj.symm (by rw [Finset.union_comm, ← hun, hchg_u]))
          set Sa := Finset.univ.filter fun j => colorBlock color j ⊆ chg (vl n C.gates a)
          set Sb := Finset.univ.filter fun j => colorBlock color j ⊆ chg (vl n C.gates b)
          have hSa_ne : Sa.Nonempty := by
            obtain ⟨i, hi⟩ := hna
            rw [hSa_eq] at hi
            obtain ⟨j, hj, -⟩ := Finset.mem_biUnion.1 hi
            exact ⟨j, hj⟩
          have hSb_ne : Sb.Nonempty := by
            obtain ⟨i, hi⟩ := hnb
            rw [hSb_eq] at hi
            obtain ⟨j, hj, -⟩ := Finset.mem_biUnion.1 hi
            exact ⟨j, hj⟩
          have hdisj_S : Disjoint Sa Sb := by
            rw [Finset.disjoint_left]
            intro j hja hjb
            obtain ⟨i, hi⟩ := colorBlock_nonempty hsurj j
            exact Finset.disjoint_left.1 hdj ((Finset.mem_filter.1 hja).2 hi) ((Finset.mem_filter.1 hjb).2 hi)
          have hun_S : Sa ∪ Sb = S := by
            ext j
            obtain ⟨i, hi⟩ := colorBlock_nonempty hsurj j
            constructor
            · intro hj
              have hi_u : i ∈ S.biUnion (colorBlock color) := by
                rw [← hchg_u, hun]
                rcases Finset.mem_union.1 hj with hja | hjb
                · exact Finset.mem_union_left _ ((Finset.mem_filter.1 hja).2 hi)
                · exact Finset.mem_union_right _ ((Finset.mem_filter.1 hjb).2 hi)
              obtain ⟨j', hj'S, hi'⟩ := Finset.mem_biUnion.1 hi_u
              have hjj : j' = j := ((mem_colorBlock color j' i).1 hi').symm.trans ((mem_colorBlock color j i).1 hi)
              rwa [← hjj]
            · intro hjS
              have hi_ab : i ∈ chg (vl n C.gates a) ∪ chg (vl n C.gates b) := by
                rw [← hun, hchg_u]; exact Finset.mem_biUnion.2 ⟨j, hjS, hi⟩
              rcases Finset.mem_union.1 hi_ab with hia | hib
              · rw [hSa_eq] at hia
                obtain ⟨j', hj'a, hi'⟩ := Finset.mem_biUnion.1 hia
                have hjj : j' = j := ((mem_colorBlock color j' i).1 hi').symm.trans ((mem_colorBlock color j i).1 hi)
                exact Finset.mem_union_left _ (hjj ▸ hj'a)
              · rw [hSb_eq] at hib
                obtain ⟨j', hj'b, hi'⟩ := Finset.mem_biUnion.1 hib
                have hjj : j' = j := ((mem_colorBlock color j' i).1 hi').symm.trans ((mem_colorBlock color j i).1 hi)
                exact Finset.mem_union_right _ (hjj ▸ hj'b)
          obtain ⟨Ta, ha_ro, ha_vars, ha_eval⟩ := ih a ha (lt_trans ha hu) Sa hSa_ne hSa_eq
          obtain ⟨Tb, hb_ro, hb_vars, hb_eval⟩ := ih b hb (lt_trans hb hu) Sb hSb_ne hSb_eq
          rcases hop with hop | hop
          · refine ⟨.bin false Ta Tb, ⟨ha_ro, hb_ro, by rw [ha_vars, hb_vars]; exact hdisj_S⟩,
              by simp [ROTree.vars, ha_vars, hb_vars, hun_S], fun l => ?_⟩
            simp [ROTree.eval, hop l, ha_eval l, hb_eval l]
          · refine ⟨.bin true Ta Tb, ⟨ha_ro, hb_ro, by rw [ha_vars, hb_vars]; exact hdisj_S⟩,
              by simp [ROTree.vars, ha_vars, hb_vars, hun_S], fun l => ?_⟩
            simp [ROTree.eval, hop l, ha_eval l, hb_eval l]
  have huniv_ne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have huniv_bi : Finset.univ = (Finset.univ : Finset (Fin d)).biUnion (colorBlock color) := by
    ext i; simp [mem_colorBlock]
  obtain ⟨T, hT_ro, hT_vars, hT_eval⟩ :=
    hbuild root hroot_lt Finset.univ huniv_ne (by rw [hroot_chg, huniv_bi])
  have hT_R : ∀ l, T.eval (X l) = R l := fun l => (hT_eval l).symm.trans (hval l).1
  have hT_pos : T.allPos := by
    apply ROTree.allPos_of_forall_posAt
    intro j
    obtain ⟨i, hi⟩ := hsurj j
    apply ROTree.flip_pos hT_ro j (S₁ := X i.castSucc) (S₂ := X i.succ)
    · intro k hkj
      have hne : color i ≠ k := fun h => hkj (h.symm.trans hi)
      have heq := (hX i k).not.2 hne
      push_neg at heq
      simpa using heq
    · rw [hT_R, hT_R]; exact (hR i).1
    · rw [hT_R, (hR i).2, hi]
  exact ⟨hfalls_b, T, hT_ro, hT_pos, hT_vars, hT_R⟩

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

theorem build_all_taps {n d : ℕ} (color : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (R : Fin (n + 1) → Bool) (hsurj : Function.Surjective color)
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j)
    (hR : ∀ i, R i.castSucc ≠ R i.succ ∧ R i.succ = decide (color i ∈ X i.succ)) :
    ∃ (gs : List Gate) (tap : Fin d → ℕ),
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ ∧
      nonNotCount gs = n - d ∧
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = (falls R).card ∧
      ∀ j : Fin d, tap j < n + 2 + gs.length ∧ ∀ l, vl n gs (tap j) l = decide (j ∈ X l) := by
  have hchg_x : ∀ j : Fin d, chg (fun l => decide (j ∈ X l)) = colorBlock color j := by
    intro j; ext i; rw [mem_chg, mem_colorBlock]; exact hX i j
  have hfalls_x : ∀ j : Fin d,
      falls (fun l => decide (j ∈ X l)) = (falls R).filter fun i => color i = j := by
    intro j; ext i
    rw [mem_falls, Finset.mem_filter, mem_falls]
    constructor
    · rintro ⟨h1, h2⟩
      have hci : color i = j := (hX i j).1 (by rw [h1, h2]; decide)
      have hRs : R i.succ = false := by rw [(hR i).2, hci, h2]
      have hRc : R i.castSucc = true := by
        cases h : R i.castSucc
        · exact absurd (h.trans hRs.symm) (hR i).1
        · rfl
      exact ⟨⟨hRc, hRs⟩, hci⟩
    · rintro ⟨⟨hRc, hRs⟩, hci⟩
      have hx2 : decide (j ∈ X i.succ) = false := by rw [← hci, ← (hR i).2, hRs]
      have hne : decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ) := (hX i j).2 hci
      have hx1 : decide (j ∈ X i.castSucc) = true := by
        cases h : decide (j ∈ X i.castSucc)
        · rw [h, hx2] at hne; exact absurd rfl hne
        · rfl
      exact ⟨hx1, hx2⟩
  have hstep : ∀ k ≤ d,
      ∃ (gs : List Gate) (tap : ∀ j : Fin d, j.val < k → ℕ),
        PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨gs, 0⟩ ∧
        nonNotCount gs = ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k), ((colorBlock color j).card - 1) ∧
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ =
          ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val < k), (falls (fun l => decide (j ∈ X l))).card ∧
        ∀ j (hj : j.val < k), tap j hj < n + 2 + gs.length ∧ ∀ l, vl n gs (tap j hj) l = decide (j ∈ X l) := by
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
      have hne0 : (chg (fun l => decide (j0 ∈ X l))).Nonempty := by
        rw [hchg_x j0]; exact colorBlock_nonempty hsurj j0
      obtain ⟨extra, w0, hw0_lt, hF', hRB', hnn_e, hnc_e, hw0_val⟩ :=
        build_prefix_fn (fun l => decide (j0 ∈ X l)) hne0 gs hF hRB
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
      · rw [nonNotCount_append, hnn, hnn_e, hchg_x j0, hfilt, Finset.sum_insert hj0_nm]; omega
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
  have hsum_falls : ∑ j : Fin d, (falls (fun l => decide (j ∈ X l))).card = (falls R).card := by
    simp only [hfalls_x]
    have hbi : (Finset.univ : Finset (Fin d)).biUnion (fun j => (falls R).filter fun i => color i = j) =
        falls R := by
      ext i; simp
    have hdj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin d)))
        (fun j => (falls R).filter fun i => color i = j) := by
      intro j _ k _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i hj hk
      rw [Finset.mem_filter] at hj hk
      exact hne (hj.2.symm.trans hk.2)
    have hc := Finset.card_biUnion hdj
    rw [hbi] at hc
    exact hc.symm
  refine ⟨gs, fun j => tap j j.isLt, hF, hRB, by omega, by rw [hnc, hsum_falls],
    fun j => hvals j j.isLt⟩

theorem monotoneFit_to_physical {n d b : ℕ} (color : Fin n → Fin d) (X : Fin (n + 1) → Finset (Fin d))
    (R : Fin (n + 1) → Bool) (hd : 0 < d) (hsurj : Function.Surjective color)
    (hX : ∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j)
    (hR : ∀ i, R i.castSucc ≠ R i.succ ∧ R i.succ = decide (color i ∈ X i.succ))
    (hfb : (falls R).card ≤ b)
    (D : Circuit) (out : ℕ)
    (hFD : PEqualNP.MetaComplexity.FanInTwo D)
    (hRD : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) D)
    (hout_lt : out < d + 2 + D.size) (hD_sz : D.size ≤ d - 1)
    (hD_not : PEqualNP.NotBracket.notCount D = 0)
    (hD_eval : ∀ l, (D.wires (ROTree.stateInput (X l))).getD out false = R l) :
    ∃ (C : Circuit) (root : ℕ) (tap : Fin d → ℕ),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
      root < n + 2 + C.size ∧ (∀ j, tap j < n + 2 + C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ n - 1 ∧
      PEqualNP.NotBracket.notCount C ≤ b ∧
      ∀ l, vl n C.gates root l = R l ∧ ∀ j, vl n C.gates (tap j) l = decide (j ∈ X l) := by
  obtain ⟨gs, tap, hF_pre, hRB_pre, hnn_pre, hnc_pre, hvals_pre⟩ :=
    build_all_taps color X R hsurj hX hR
  have hd_le_n : d ≤ n := by
    have hsum_blk : ∑ j : Fin d, (colorBlock color j).card = n := by
      have hbi : (Finset.univ : Finset (Fin d)).biUnion (colorBlock color) = Finset.univ := by
        ext i; simp [mem_colorBlock]
      have hc := Finset.card_biUnion (s := (Finset.univ : Finset (Fin d)))
        (t := colorBlock color) (fun j _ k _ hne => colorBlock_disjoint color hne)
      rw [hbi] at hc; simpa using hc.symm
    calc d = ∑ _j : Fin d, 1 := by simp
      _ ≤ ∑ j : Fin d, (colorBlock color j).card :=
          Finset.sum_le_sum fun j _ => Finset.card_pos.2 (colorBlock_nonempty hsurj j)
      _ = n := hsum_blk
  let remapIdx : ℕ → ℕ := fun p =>
    if hp : p < d then tap ⟨p, hp⟩
    else if p = d then n
    else if p = d + 1 then n + 1
    else n + 2 + gs.length + (p - (d + 2))
  let remapGate : Gate → Gate := fun g => ⟨g.op, g.inputs.map remapIdx⟩
  have hremap_lt : ∀ k p, p < d + 2 + k → remapIdx p < n + 2 + gs.length + k := by
    intro k p hp
    dsimp only [remapIdx]
    split_ifs with h1 h2 h3
    · have := (hvals_pre ⟨p, h1⟩).1; omega
    · omega
    · omega
    · omega
  have hremap_eval : ∀ (ds : List Gate),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) ⟨ds, 0⟩ →
      ∀ (l : Fin (n + 1)) (p : ℕ), p < d + 2 + ds.length →
        (W (gs ++ ds.map remapGate) (prefixInput n l)).getD (remapIdx p) false =
          (W ds (ROTree.stateInput (X l))).getD p false := by
    intro ds
    induction ds using List.reverseRecOn with
    | nil =>
      intro _ l p hp
      simp only [List.map_nil, List.append_nil, W_nil, List.length_nil, Nat.add_zero] at hp ⊢
      dsimp only [remapIdx]
      split_ifs with h1 h2 h3
      · change vl n gs (tap ⟨p, h1⟩) l = (ROTree.stateInput (X l)).getD p false
        rw [(hvals_pre ⟨p, h1⟩).2 l, ROTree.stateInput_lt (X l) ⟨p, h1⟩]
      · subst h2
        have h0 := W_append_old [] gs (prefixInput n l) n (by rw [prefixInput_len]; simp)
        have h0' : (W gs (prefixInput n l)).getD n false = false := h0.trans (prefixInput_n n l)
        rw [h0']
        unfold ROTree.stateInput
        rw [List.getD_append_right _ _ _ _ (by simp)]; simp
      · subst h3
        have h0 := W_append_old [] gs (prefixInput n l) (n + 1) (by rw [prefixInput_len]; simp)
        have h0' : (W gs (prefixInput n l)).getD (n + 1) false = true := h0.trans (prefixInput_n1 n l)
        rw [h0']
        unfold ROTree.stateInput
        rw [List.getD_append_right _ _ _ _ (by simp)]; simp
      · omega
    | append_singleton ds g ih =>
      intro hRds l p hp
      have hR_pre : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) ⟨ds, 0⟩ := by
        intro j hj i hi
        have hj' : j < (ds ++ [g]).length := by
          simp only [List.length_append, List.length_singleton]; exact Nat.lt_succ_of_lt hj
        have hget : (ds ++ [g]).getD j ⟨GateOp.or, []⟩ = ds.getD j ⟨GateOp.or, []⟩ :=
          List.getD_append _ _ _ _ hj
        exact hRds j hj' i (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rwa [hget])
      have hg_in : ∀ i ∈ g.inputs, i < d + 2 + ds.length := by
        intro i hi
        have hj' : ds.length < (ds ++ [g]).length := by simp
        have hget : (ds ++ [g]).getD ds.length ⟨GateOp.or, []⟩ = g := by
          rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
        exact hRds ds.length hj' i (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rwa [hget])
      have hmap_eq : gs ++ (ds ++ [g]).map remapGate = (gs ++ ds.map remapGate) ++ [remapGate g] := by
        simp [List.map_append, List.append_assoc]
      rw [hmap_eq]
      simp only [List.length_append, List.length_singleton] at hp
      by_cases hlt : p < d + 2 + ds.length
      · have hne_l : remapIdx p ≠ (prefixInput n l).length + (gs ++ ds.map remapGate).length := by
          rw [prefixInput_len, List.length_append, List.length_map]
          have := hremap_lt ds.length p hlt
          omega
        have hne_r : p ≠ (ROTree.stateInput (X l)).length + ds.length := by
          rw [ROTree.stateInput_len]; omega
        rw [old_wire _ _ _ _ hne_l, old_wire _ _ _ _ hne_r]
        exact ih hR_pre l p hlt
      · have heq : p = d + 2 + ds.length := by omega
        subst heq
        have hrm : remapIdx (d + 2 + ds.length) = (prefixInput n l).length + (gs ++ ds.map remapGate).length := by
          rw [prefixInput_len, List.length_append, List.length_map]
          dsimp only [remapIdx]
          have h1 : ¬(d + 2 + ds.length < d) := by omega
          have h2 : ¬(d + 2 + ds.length = d) := by omega
          have h3 : ¬(d + 2 + ds.length = d + 1) := by omega
          simp only [h1, h2, h3, ↓reduceDIte, ↓reduceIte]
          omega
        rw [hrm, new_wire]
        have hlen_r : d + 2 + ds.length = (ROTree.stateInput (X l)).length + ds.length := by
          rw [ROTree.stateInput_len]
        rw [hlen_r, new_wire]
        congr 1
        simp only [remapGate, List.map_map]
        apply List.map_congr_left
        intro i hi
        exact ih hR_pre l i (hg_in i hi)
  let C : Circuit := ⟨gs ++ D.gates.map remapGate, 0⟩
  have hD_not_map : PEqualNP.NotBracket.notCount ⟨D.gates.map remapGate, 0⟩ = 0 := by
    have hzero : ∀ g ∈ D.gates, isNotGate g = false := by
      intro g hg
      by_contra hne
      have htrue : isNotGate g = true := by cases h : isNotGate g <;> simp_all
      have hpos : 0 < (D.gates.filter isNotGate).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨hg, htrue⟩)
      rw [notCount_eq_filter] at hD_not
      omega
    rw [notCount_eq_filter]
    have hfilt : ((D.gates.map remapGate).filter isNotGate) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
      have : isNotGate (remapGate g) = isNotGate g := rfl
      rw [this, hzero g hg]
      simp
    rw [hfilt]; rfl
  have hC_not : PEqualNP.NotBracket.notCount C = (falls R).card := by
    dsimp only [C]
    rw [notCount_append, hnc_pre, hD_not_map, Nat.add_zero]
  have hC_nn : nonNotCount C.gates = (n - d) + D.size := by
    dsimp only [C]
    rw [nonNotCount_append, hnn_pre]
    have hsp := notCount_add_nonNotCount ⟨D.gates.map remapGate, 0⟩
    rw [hD_not_map] at hsp
    simp only [Circuit.size, List.length_map] at hsp ⊢
    omega
  have hC_sp := notCount_add_nonNotCount C
  refine ⟨C, remapIdx out, tap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply fanInTwo_append hF_pre
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2⟩ := hFD g hg
    exact ⟨h1, by simpa [remapGate] using h2⟩
  · apply readsBack_of_append hRB_pre
    intro k hk i hi
    simp only [List.length_map] at hk
    have hget : (D.gates.map remapGate).getD k ⟨GateOp.or, []⟩ = remapGate (D.gates.getD k ⟨GateOp.or, []⟩) := by
      rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getD_eq_getElem _ _ hk, List.getElem_map]
    rw [hget] at hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
    exact hremap_lt k p (hRD k hk p (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; exact hp))
  · simp only [C, Circuit.size, List.length_append, List.length_map]
    have := hremap_lt D.gates.length out hout_lt
    omega
  · intro j
    have := (hvals_pre j).1
    simp only [C, Circuit.size, List.length_append, List.length_map]
    omega
  · omega
  · rw [hC_not]; exact hfb
  · intro l
    refine ⟨?_, fun j => ?_⟩
    · change (W (gs ++ D.gates.map remapGate) (prefixInput n l)).getD (remapIdx out) false = R l
      rw [hremap_eval D.gates hRD l out hout_lt]
      exact hD_eval l
    · change (W (gs ++ D.gates.map remapGate) (prefixInput n l)).getD (tap j) false = decide (j ∈ X l)
      rw [W_append_old gs (D.gates.map remapGate) (prefixInput n l) (tap j)
            (by rw [prefixInput_len]; exact (hvals_pre j).1)]
      exact (hvals_pre j).2 l

section Protocol
variable {d : Nat} {α β : Type*}

def Row (p : α → β → Fin d) (i j : Fin d) : Prop := ∃ a b c, p a b=i ∧ p a c=j
def Col (p : α → β → Fin d) (i j : Fin d) : Prop := ∃ a c b, p a b=i ∧ p c b=j
def Cut (E : Fin d → Fin d → Prop) (S : Finset (Fin d)) : Prop :=
  ∃ U : Finset (Fin d), U.Nonempty ∧ U ⊂ S ∧ ∀ i∈U, ∀ j∈S\U, ¬ E i j

theorem cut_mono {E F : Fin d → Fin d → Prop} {S : Finset (Fin d)} (h : Cut F S)
    (incl : ∀ i∈S, ∀ j∈S, E i j → F i j) : Cut E S := by
  obtain ⟨U,hu,hp,hn⟩ := h
  exact ⟨U,hu,hp,fun i hi j hj e => hn i hi j hj (incl i (hp.1 hi) j (Finset.mem_sdiff.mp hj).1 e)⟩

theorem inherit_cut {p p' : α → β → Fin d} {S : Finset (Fin d)}
    (eq : ∀ a b, p a b ∈ S → p a b = p' a b) (h : Cut (Row p') S ∨ Cut (Col p') S) :
    Cut (Row p) S ∨ Cut (Col p) S := by
  rcases h with h | h
  · left; apply cut_mono h
    rintro i hi j hj ⟨a,b,c,he,hf⟩
    exact ⟨a,b,c,(eq a b (he ▸ hi)).symm.trans he,(eq a c (hf ▸ hj)).symm.trans hf⟩
  · right; apply cut_mono h
    rintro i hi j hj ⟨a,c,b,he,hf⟩
    exact ⟨a,c,b,(eq a b (he ▸ hi)).symm.trans he,(eq c b (hf ▸ hj)).symm.trans hf⟩

def side (gate leftHi leftLo : Bool) := if gate then leftHi else !leftLo

def route (T : ROTree d) (h l : Finset (Fin d)) : Fin d :=
  match T with
  | .var j _ => j
  | .bin g A B => if side g (A.eval h) (A.eval l) then route A h l else route B h l

theorem route_mem (T : ROTree d) (h l : Finset (Fin d)) : route T h l ∈ T.vars := by
  induction T with
  | var j b => simp [route,ROTree.vars]
  | bin g A B ih jh => simp only [route,ROTree.vars];split <;> simp [ih,jh]

theorem route_sound (T : ROTree d) (pos : T.allPos) (h l : Finset (Fin d))
    (hh : T.eval h=true) (hl : T.eval l=false) : route T h l ∈ h\l := by
  induction T with
  | var j b =>
    have hb : b=false := pos
    subst b; simpa [ROTree.eval,route,Finset.mem_sdiff] using And.intro hh hl
  | bin g A B ih jh =>
    obtain ⟨pa,pb⟩ := pos
    cases g <;> cases a : A.eval h <;> cases b : A.eval l <;>
      simp_all [ROTree.eval,route,side]

theorem routed_split (T : ROTree d) (ro : T.readOnce) (H : α → Finset (Fin d)) (L : β → Finset (Fin d))
    (S : Finset (Fin d)) (sub : S⊆T.vars) (big : 2≤S.card) :
    Cut (Row (fun a b => route T (H a) (L b))) S ∨ Cut (Col (fun a b => route T (H a) (L b))) S := by
  induction T with
  | var j b =>
    have h := Finset.card_le_card sub
    simp [ROTree.vars] at h; omega
  | bin g A B ih jh =>
    obtain ⟨ha,hb,dis⟩ := ro
    let p (a : α) (b : β) := route (.bin g A B) (H a) (L b)
    let left (a : α) (b : β) := side g (A.eval (H a)) (A.eval (L b))
    have pl (a : α) (b : β) : p a b ∈ A.vars → left a b=true ∧ p a b=route A (H a) (L b) := by
      dsimp only [p,route,left];split
      · intro _; exact ⟨by assumption,rfl⟩
      · intro he; exact (Finset.disjoint_left.mp dis he (route_mem B _ _)).elim
    have pr (a : α) (b : β) : p a b ∈ B.vars → left a b=false ∧ p a b=route B (H a) (L b) := by
      dsimp only [p,route,left];split
      · intro he; exact (Finset.disjoint_left.mp dis (route_mem A _ _) he).elim
      · intro _; exact ⟨by simp_all,rfl⟩
    change Cut (Row p) S ∨ Cut (Col p) S
    by_cases hA : S⊆A.vars
    · exact inherit_cut (fun a b h => (pl a b (hA h)).2) (ih ha hA)
    by_cases hB : S⊆B.vars
    · exact inherit_cut (fun a b h => (pr a b (hB h)).2) (jh hb hB)
    let U := S∩A.vars
    have hu : U.Nonempty := by
      obtain ⟨i,hi,hn⟩ := Finset.not_subset.mp hB
      exact ⟨i,Finset.mem_inter.mpr ⟨hi,(Finset.mem_union.mp (sub hi)).resolve_right hn⟩⟩
    have proper : U ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left,fun e => hA (e ▸ Finset.inter_subset_right (s₁:=S) (s₂:=A.vars))⟩
    have vr {j} (hj : j∈S\U) : j∈B.vars := by
      obtain ⟨h,nU⟩ := Finset.mem_sdiff.mp hj
      exact (Finset.mem_union.mp (sub h)).resolve_left fun a => nU (Finset.mem_inter.mpr ⟨h,a⟩)
    cases g with
    | true =>
      left; refine ⟨U,hu,proper,?_⟩
      rintro i hi j hj ⟨a,b,c,he,hf⟩
      have t := (pl a b (he ▸ (Finset.mem_inter.mp hi).2)).1
      have f := (pr a c (hf ▸ vr hj)).1
      change A.eval (H a)=true at t
      change A.eval (H a)=false at f
      simp_all
    | false =>
      right; refine ⟨U,hu,proper,?_⟩
      rintro i hi j hj ⟨a,c,b,he,hf⟩
      have t := (pl a b (he ▸ (Finset.mem_inter.mp hi).2)).1
      have f := (pr c b (hf ▸ vr hj)).1
      change (!A.eval (L b))=true at t
      change (!A.eval (L b))=false at f
      simp_all
end Protocol

section Rectangles
variable {d : Nat} {α β : Type*}

def ExactRect (p : α → β → Fin d) (A : Set α) (B : Set β) (S : Finset (Fin d)) : Prop :=
  (∀ a∈A, ∀ b∈B, p a b∈S) ∧ ∀ i∈S, ∃ a∈A, ∃ b∈B, p a b=i

lemma transpose_rect {p : α → β → Fin d} {A : Set α} {B : Set β} {S : Finset (Fin d)}
    (r : ExactRect p A B S) : ExactRect (fun b a => p a b) B A S := by
  refine ⟨fun b hb a ha => r.1 a ha b hb, ?_⟩
  intro i hi; obtain ⟨a,ha,b,hb,e⟩ := r.2 i hi; exact ⟨b,hb,a,ha,e⟩

lemma slice_rows {p : α → β → Fin d} {A : Set α} {B : Set β} {S U : Finset (Fin d)}
    (rect : ExactRect p A B S) (us : U⊆S)
    (sep : ∀ i∈U,∀ j∈S\U, ¬ Row p i j) :
    ∃ A₁ A₂ : Set α, (∀ a∈A,a∈A₁ ∨ a∈A₂) ∧ ExactRect p A₁ B U ∧ ExactRect p A₂ B (S\U) := by
  classical
  let sel (a : α) := ∃ b∈B,p a b∈U
  let A₁ : Set α := {a | a∈A ∧ sel a}
  let A₂ : Set α := {a | a∈A ∧ ¬ sel a}
  have into {a b} (ha : a∈A) (hb : b∈B) (yes : sel a) : p a b∈U := by
    obtain ⟨b',_,hit⟩ := yes
    by_contra no
    exact sep _ hit _ (Finset.mem_sdiff.mpr ⟨rect.1 _ ha _ hb,no⟩) ⟨a,b',b,rfl,rfl⟩
  refine ⟨A₁,A₂,fun a ha => (em (sel a)).elim (fun h => Or.inl ⟨ha,h⟩) (fun h => Or.inr ⟨ha,h⟩),?_,?_⟩
  · refine ⟨fun a (ha : a∈A₁) b hb => into ha.1 hb ha.2,?_⟩
    intro i hi; obtain ⟨a,ha,b,hb,e⟩ := rect.2 i (us hi)
    exact ⟨a,⟨ha,b,hb,e ▸ hi⟩,b,hb,e⟩
  · refine ⟨fun a (ha : a∈A₂) b hb => Finset.mem_sdiff.mpr ⟨rect.1 _ ha.1 _ hb,fun h => ha.2 ⟨b,hb,h⟩⟩,?_⟩
    intro i hi; obtain ⟨hs,hn⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨a,ha,b,hb,e⟩ := rect.2 i hs
    exact ⟨a,⟨ha,fun yes => hn (e ▸ into ha hb yes)⟩,b,hb,e⟩

end Rectangles

section BuildProtocol
variable {d : Nat} {α β : Type*}

def Realizes (H : α → Finset (Fin d)) (L : β → Finset (Fin d)) (A : Set α) (B : Set β) (S : Finset (Fin d)) : Prop :=
  ∃ T : ROTree d,T.readOnce ∧ T.allPos ∧ T.vars⊆S ∧ (∀ a∈A,T.eval (H a)=true) ∧ (∀ b∈B,T.eval (L b)=false)

lemma build_rect (H : α → Finset (Fin d)) (L : β → Finset (Fin d)) (p : α → β → Fin d)
    (ok : ∀ a b, p a b∈H a\L b) (splits : ∀ S : Finset (Fin d),2≤S.card → Cut (Row p) S ∨ Cut (Col p) S)
    (S : Finset (Fin d)) : ∀ (A : Set α) (B : Set β), S.Nonempty → ExactRect p A B S → Realizes H L A B S := by
  classical
  induction S using Finset.strongInductionOn
  case _ S ih =>
    intro A B ne rect
    by_cases small : S.card=1
    · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp small
      obtain ⟨a,ha,b,hb,_⟩ := rect.2 i (Finset.mem_singleton_self _)
      refine ⟨.var i false, trivial,rfl,Finset.Subset.rfl,?_,?_⟩
      · intro a' h'
        have e := Finset.mem_singleton.mp (rect.1 a' h' b hb)
        have hit := (Finset.mem_sdiff.mp (ok a' b)).1
        simpa [ROTree.eval, e] using hit
      · intro b' h'
        have e := Finset.mem_singleton.mp (rect.1 a ha b' h')
        have hit := (Finset.mem_sdiff.mp (ok a b')).2
        simpa [ROTree.eval,e] using hit
    have big : 2≤S.card := by have := Finset.card_pos.mpr ne; omega
    obtain row | col := splits S big
    · obtain ⟨U,hu,us,sep⟩ := row
      have vs := Finset.sdiff_ssubset us.1 hu
      have hv : (S\U).Nonempty := Finset.sdiff_nonempty.mpr us.2
      obtain ⟨A₁,A₂,part,ra,rb⟩ := slice_rows rect us.1 sep
      obtain ⟨T,rt,pt,st,ht,lt⟩ := ih U us _ _ hu ra
      obtain ⟨V,rv,pv,sv,hv',lv⟩ := ih (S\U) vs _ _ hv rb
      refine ⟨.bin true T V,⟨rt,rv,Finset.disjoint_left.mpr fun z hz hz' => (Finset.mem_sdiff.mp (sv hz')).2 (st hz)⟩,
        ⟨pt,pv⟩,Finset.union_subset (st.trans us.1) (sv.trans Finset.sdiff_subset),?_,?_⟩
      · intro a ha; rcases part a ha with h|h
        · simp [ROTree.eval,ht a h]
        · simp [ROTree.eval,hv' a h]
      · intro b hb; simp [ROTree.eval,lt b hb,lv b hb]
    · obtain ⟨U,hu,us,sep⟩ := col
      have vs := Finset.sdiff_ssubset us.1 hu
      have hv : (S\U).Nonempty := Finset.sdiff_nonempty.mpr us.2
      have flip : ∀ i∈U,∀ j∈S\U, ¬ Row (fun b a => p a b) i j := by
        rintro i hi j hj ⟨b,a,c,he,hf⟩; exact sep i hi j hj ⟨a,c,b,he,hf⟩
      obtain ⟨B₁,B₂,part,ra,rb⟩ := slice_rows (transpose_rect rect) us.1 flip
      obtain ⟨T,rt,pt,st,ht,lt⟩ := ih U us _ _ hu (transpose_rect ra)
      obtain ⟨V,rv,pv,sv,hv',lv⟩ := ih (S\U) vs _ _ hv (transpose_rect rb)
      refine ⟨.bin false T V,⟨rt,rv,Finset.disjoint_left.mpr fun z hz hz' => (Finset.mem_sdiff.mp (sv hz')).2 (st hz)⟩,
        ⟨pt,pv⟩,Finset.union_subset (st.trans us.1) (sv.trans Finset.sdiff_subset),?_,?_⟩
      · intro a ha; simp [ROTree.eval,ht a ha,hv' a ha]
      · intro b hb; rcases part b hb with h|h
        · simp [ROTree.eval,lt b h]
        · simp [ROTree.eval,lv b h]

end BuildProtocol

theorem verified : (∀ (n d b : Nat) (color : Fin n → Fin d) (X : Fin (n+1) → Finset (Fin d))
    (R : Fin (n+1) → Bool), 0 < d → Function.Surjective color →
  (∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) →
  (∀ i, R i.castSucc ≠ R i.succ ∧ R i.succ = decide (color i ∈ X i.succ)) →
  let falls := ((Finset.univ : Finset (Fin n)).filter (fun i =>
    R i.castSucc = true ∧ R i.succ = false)).card
  let fits := ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (root : Nat) (tap : Fin d → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    root < n+2+C.size ∧ (∀ j, tap j < n+2+C.size) ∧
    C.size - PEqualNP.NotBracket.notCount C ≤ n-1 ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    ∀ l, let w := C.wires (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false,true])
         w.getD root false = R l ∧ ∀ j, w.getD (tap j) false = decide (j ∈ X l)
  let cell := fun (h l : Fin (n+1)) => R h = true ∧ R l = false
  let splittable := fun (edge : Fin d → Fin d → Prop) (S : Finset (Fin d)) =>
    ∃ U : Finset (Fin d), U.Nonempty ∧ U ⊂ S ∧ ∀ i ∈ U, ∀ j ∈ S \ U, ¬ edge i j
  fits ↔ falls ≤ b ∧ ∃ pick : Fin (n+1) → Fin (n+1) → Fin d,
    (∀ h l, cell h l → pick h l ∈ X h \ X l) ∧
    let row := fun i j => ∃ h l t, cell h l ∧ cell h t ∧ pick h l = i ∧ pick h t = j
    let col := fun i j => ∃ h l t, cell h l ∧ cell t l ∧ pick h l = i ∧ pick t l = j
    ∀ S : Finset (Fin d), 2 ≤ S.card → splittable row S ∨ splittable col S) := by
  intro n d b color X R hd sur step align falling fits cell splittable
  constructor
  · rintro ⟨C,o,tap,fan,rb,ho,ht,pos,neg,hw⟩
    obtain ⟨fb,T,rt,pt,vt,ev⟩ := physical_to_tree color X R hd sur step align C o tap fan rb ho ht pos neg hw
    let p (h l : Fin (n+1)) := route T (X h) (X l)
    refine ⟨fb,p,?_,?_⟩
    · intro h l good
      exact route_sound T pt _ _ ((ev h).trans good.1) ((ev l).trans good.2)
    · intro row col S hs
      have sub : S⊆T.vars := by rw [vt];exact Finset.subset_univ _
      rcases routed_split T rt X X S sub hs with c|c
      · left; apply cut_mono c
        rintro i _ j _ ⟨h,l,t,_,_,hi,hj⟩; exact ⟨h,l,t,hi,hj⟩
      · right; apply cut_mono c
        rintro i _ j _ ⟨h,l,t,_,_,hi,hj⟩; exact ⟨h,t,l,hi,hj⟩
  · rintro ⟨fb,p,ok,splits⟩
    let Hi := {i : Fin (n+1) // R i = true}
    let Lo := {i : Fin (n+1) // R i = false}
    let g (h : Hi) (l : Lo) := p h.1 l.1
    let Xh (h : Hi) := X h.1
    let Xl (l : Lo) := X l.1
    have ok' (a : Hi) (b : Lo) : g a b ∈ Xh a \ Xl b := ok _ _ ⟨a.2,b.2⟩
    have spl' (S : Finset (Fin d)) (h : 2≤S.card) : Cut (Row g) S ∨ Cut (Col g) S := by
      rcases splits S h with c|c
      · left; apply cut_mono c
        rintro i _ j _ ⟨a,l,t,e,f⟩; exact ⟨a.1,l.1,t.1,⟨a.2,l.2⟩,⟨a.2,t.2⟩,e,f⟩
      · right; apply cut_mono c
        rintro i _ j _ ⟨a,c,l,e,f⟩; exact ⟨a.1,l.1,c.1,⟨a.2,l.2⟩,⟨c.2,l.2⟩,e,f⟩
    classical
    let S : Finset (Fin d) := Finset.univ.filter fun i => ∃ a l, g a l=i
    have rect : ExactRect g Set.univ Set.univ S := by
      refine ⟨fun a _ l _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,l,rfl⟩,?_⟩
      intro i hi;obtain ⟨a,l,e⟩ := (Finset.mem_filter.mp hi).2
      exact ⟨a,Set.mem_univ _,l,Set.mem_univ _,e⟩
    have ne : S.Nonempty := by
      obtain ⟨i,_⟩ := sur ⟨0,hd⟩
      have dif := (align i).1
      obtain ⟨a,la,c,lc⟩ : ∃ a, R a=true ∧ ∃ c,R c=false := by
        cases e:R i.castSucc <;> cases f:R i.succ
        · exact (dif (e.trans f.symm)).elim
        · exact ⟨_,f,_,e⟩
        · exact ⟨_,e,_,f⟩
        · exact (dif (e.trans f.symm)).elim
      exact ⟨_,rect.1 ⟨a,la⟩ (Set.mem_univ _) ⟨c,lc⟩ (Set.mem_univ _)⟩
    obtain ⟨T,rt,pt,_,th,tl⟩ := build_rect Xh Xl g ok' spl' S _ _ ne rect
    have ev (l : Fin (n+1)) : T.eval (X l)=R l := by
      cases e:R l with
      | true => exact th ⟨l,e⟩ (Set.mem_univ _)
      | false => exact tl ⟨l,e⟩ (Set.mem_univ _)
    obtain ⟨extra,hEq,hLen,hOut,hFD,hRD,hND,hDE⟩ := ROTree.compileAux_spec T pt []
      (fun _ x => absurd x (by simp)) (fun _ x => absurd x (by simp)) rfl
    apply monotoneFit_to_physical color X R hd sur step align fb ⟨(T.compileAux []).1,0⟩ (T.compileAux []).2 hFD hRD hOut _ hND
    · exact fun l => (hDE (X l)).trans (ev l)
    · have hbc := ROTree.binCount_add_one rt
      have hvc : T.vars.card ≤ d := by simpa using Finset.card_le_univ T.vars
      change (T.compileAux []).1.length ≤ d-1
      rw [hEq,List.nil_append,hLen];omega

end PEqualNP.Outside.L_lib_1388
theorem PEqualNP.Outside.L_lib_1388 : (∀ (n d b : Nat) (color : Fin n → Fin d) (X : Fin (n+1) → Finset (Fin d))
    (R : Fin (n+1) → Bool), 0 < d → Function.Surjective color →
  (∀ i j, (decide (j ∈ X i.castSucc) ≠ decide (j ∈ X i.succ)) ↔ color i = j) →
  (∀ i, R i.castSucc ≠ R i.succ ∧ R i.succ = decide (color i ∈ X i.succ)) →
  let falls := ((Finset.univ : Finset (Fin n)).filter (fun i =>
    R i.castSucc = true ∧ R i.succ = false)).card
  let fits := ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (root : Nat) (tap : Fin d → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    root < n+2+C.size ∧ (∀ j, tap j < n+2+C.size) ∧
    C.size - PEqualNP.NotBracket.notCount C ≤ n-1 ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
    ∀ l, let w := C.wires (List.ofFn (fun i : Fin n => decide (i.val < l.val)) ++ [false,true])
         w.getD root false = R l ∧ ∀ j, w.getD (tap j) false = decide (j ∈ X l)
  let cell := fun (h l : Fin (n+1)) => R h = true ∧ R l = false
  let splittable := fun (edge : Fin d → Fin d → Prop) (S : Finset (Fin d)) =>
    ∃ U : Finset (Fin d), U.Nonempty ∧ U ⊂ S ∧ ∀ i ∈ U, ∀ j ∈ S \ U, ¬ edge i j
  fits ↔ falls ≤ b ∧ ∃ pick : Fin (n+1) → Fin (n+1) → Fin d,
    (∀ h l, cell h l → pick h l ∈ X h \ X l) ∧
    let row := fun i j => ∃ h l t, cell h l ∧ cell h t ∧ pick h l = i ∧ pick h t = j
    let col := fun i j => ∃ h l t, cell h l ∧ cell t l ∧ pick h l = i ∧ pick t l = j
    ∀ S : Finset (Fin d), 2 ≤ S.card → splittable row S ∨ splittable col S) := by
  exact PEqualNP.Outside.L_lib_1388.verified

import PEqualNP.Defs

-- L-meta-25491: take a least ReadsBack circuit D (the L_meta_18153 elimination pass, here also emitting ReadsBack, normalizes).
-- A row nobody reads contradicts incomparability by monotonicity. A row read twice, or read once by an AND or a
-- one-wire OR, is off after deleting it: its readers (and the reader of the off gate) are off or copies, and the
-- pass drops two gates; an off gate nobody reads is pruned against minimality, and the output cannot be it.

namespace PEqualNP.Outside.L_meta_25491_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- copied from PEqualNP.Outside.L_meta_18153 (lean/PEqualNP/Outside/L_meta_18153.lean); emit/engine3 extended with ReadsBack
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_init (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_init [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_init gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_init gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_init _ _ _ _ (h t rfl)

theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h1' h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, by simpa using h1', ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by simp; exact ⟨hr t rfl, hs' q rfl⟩)
            (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by simp; exact ⟨hr t rfl, hs' q rfl⟩)
            (by intro y _; simp [GateOp.eval, rv])
  · simp at hl

theorem engine {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he he' hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · intro i hi t ht
          rw [List.getElem_append] at ht
          split_ifs at ht with hih
          · exact h5 i hih t ht
          · have hmem : e[i - hs.length]'(by simp at hi; omega) ∈ e := List.mem_iff_getElem.mpr ⟨_, _, rfl⟩
            have := he' _ hmem t ht
            omega
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e2', e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e2' e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, ?_, h2, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm

-- end of the copy

theorem gv (N : ℕ) (C : Circuit) (hb : ReadsBack N C) (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) :
    (run C.gates x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  have hw := run_gate C.gates x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => if_pos (hb j hj i hi)

theorem past (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (run gs x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [run_length]; exact hi)

-- copied from PEqualNP.Outside.L_meta_25479_aux (state/runs/prep_L_meta_25479.lean)
theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n + v.val
      · simp [hv]
      · have hv' : ¬ i - n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

theorem only_reader (C : Circuit) (i j k : ℕ) (hj : j < C.size) (hk : k < C.size)
    (hc : readsIn C (Finset.range C.size) i = 1)
    (hij : i ∈ (gateAt C j).inputs) (hik : i ∈ (gateAt C k).inputs) : j = k := by
  by_contra h
  have hs : ({j, k} : Finset ℕ) ⊆ Finset.range C.size := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  have hsum : (∑ g ∈ ({j, k} : Finset ℕ), (gateAt C g).inputs.count i) ≤
      readsIn C (Finset.range C.size) i :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair h, hc] at hsum
  have ha := List.count_pos_iff.mpr hij
  have hb := List.count_pos_iff.mpr hik
  omega
-- end of the copy

theorem wi (gs : List Gate) {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n + m) :
    (run gs (PEqualNP.Represents.oneEach u v)).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  rw [run_input _ _ _ (by rw [oneEach_length]; exact hi), oneEach_getD]

theorem sa_val {n : ℕ} (u : Fin (n + 1)) (a : Fin n) :
    ((u.succAbove a : Fin (n + 1)) : ℕ) = if (a : ℕ) < u then (a : ℕ) else a + 1 := by
  by_cases h : (a : ℕ) < u
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; simp [h]

theorem gok (C : Circuit) (hC : Monotone2 C) (j : ℕ) (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧ (gateAt C j).inputs.length ≤ 2 := by
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have := hC _ (List.getElem_mem hj)
  rw [he]
  exact ⟨by simpa using this.1, this.2⟩

/-- A gate reading an off wire is off or copies one of its operands. -/
theorem shape (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (hl : l.length ≤ 2)
    (a : ℕ) (ha : a ∈ l) :
    (∀ f : ℕ → Bool, f a = false → op.eval (l.map f) = false) ∨
      ∃ w ∈ l, ∀ f : ℕ → Bool, f a = false → op.eval (l.map f) = f w := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at ha
  · simp at ha; subst ha
    left; intro f hf; rcases hop with rfl | rfl <;> simp [GateOp.eval, hf]
  · simp at ha
    rcases hop with rfl | rfl
    · left; intro f hf; rcases ha with rfl | rfl <;> simp [GateOp.eval, hf]
    · right
      rcases ha with rfl | rfl
      · exact ⟨y, by simp, fun f hf => by simp [GateOp.eval, hf]⟩
      · exact ⟨x, by simp, fun f hf => by simp [GateOp.eval, hf]⟩
  · simp at hl

theorem and_off (l : List ℕ) (a : ℕ) (ha : a ∈ l) (f : ℕ → Bool) (hf : f a = false) :
    GateOp.and.eval (l.map f) = false := by
  simp only [GateOp.eval, List.all_eq_false]
  exact ⟨f a, List.mem_map.mpr ⟨a, ha, rfl⟩, by simp [hf]⟩

theorem or_off (l : List ℕ) (a : ℕ) (hl : ∀ i ∈ l, i = a) (f : ℕ → Bool) (hf : f a = false) :
    GateOp.or.eval (l.map f) = false := by
  simp only [GateOp.eval, List.any_eq_false]
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  rw [hl i hi, hf]; simp

theorem allu (l : List ℕ) (hl : l.length ≤ 2) (u : ℕ) (hu : u ∈ l)
    (h : ¬(l.count u = 1 ∧ ∃ w, l = [u, w] ∨ l = [w, u])) : ∀ i ∈ l, i = u := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at hu
  · simp at hu; subst hu; simp
  · simp at hu
    rcases hu with rfl | rfl
    · by_cases hy : y = u
      · subst hy; simp
      · exact absurd ⟨by simp [List.count_cons, hy], y, Or.inl rfl⟩ h
    · by_cases hx : x = u
      · subst hx; simp
      · exact absurd ⟨by simp [List.count_cons, hx], x, Or.inr rfl⟩ h
  · simp at hl

theorem op_le (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (f g : ℕ → Bool)
    (h : ∀ i ∈ l, f i = true → g i = true) : op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id]
    intro hf i hi; exact h i hi (hf i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨g i, ⟨i, hi, rfl⟩, h i hi hb⟩

/-- A circuit on the oneEach inputs keeps its function through the pass: ReadsBack, and the gates of
`F` (each off or a copy there) are gone. -/
theorem same_rep (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit) (hC : Monotone2 C)
    (hr : PEqualNP.Represents.Represents G C) (ht : ∃ a c, G a c = true) (hf : ∃ a c, G a c = false)
    (F : Finset ℕ)
    (hF : ∀ j ∈ F, j < C.gates.length ∧
      ((∃ b, ∀ p : Fin n × Fin m, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + m + j) false = b) ∨
      ∃ w < n + m + j, ∀ p : Fin n × Fin m, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + m + j) false =
        (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD w false)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (n + m) D ∧ D.size + F.card ≤ C.size ∧
      PEqualNP.Represents.Represents G D := by
  obtain ⟨D, h1, h2, h3, h4⟩ := engine (X := Fin n × Fin m) (n + m) (n + m) C
    (fun p => PEqualNP.Represents.oneEach p.1 p.2) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
    (fun p => oneEach_length _ _) (fun p => oneEach_length _ _) F hC
    (fun w _ => Or.inr ⟨w, by omega, fun _ => rfl⟩)
    (by
      rintro ⟨b, hb⟩
      obtain ⟨a, c, hac⟩ := ht
      obtain ⟨a', c', hac'⟩ := hf
      have e1 : G a c = b := (hr a c).symm.trans (hb (a, c))
      have e2 : G a' c' = b := (hr a' c').symm.trans (hb (a', c'))
      rw [e1] at hac; rw [e2] at hac'; rw [hac] at hac'; exact absurd hac' (by simp)) hF
  exact ⟨D, h1, h2, h3, fun a c => (h4 (a, c)).trans (hr a c)⟩

/-- Deleting row `u` through the pass, the gates of `F` (each off or a copy with row `u` off) gone. -/
theorem del_rep (n m : ℕ) (G : Fin (n + 1) → Fin m → Bool) (u : Fin (n + 1)) (C : Circuit) (hC : Monotone2 C)
    (hr : PEqualNP.Represents.Represents G C) (ht : ∃ a c, G (u.succAbove a) c = true)
    (hf : ∃ a c, G (u.succAbove a) c = false) (F : Finset ℕ)
    (hF : ∀ j ∈ F, j < C.gates.length ∧
      ((∃ b, ∀ p : Fin n × Fin m,
        (run C.gates (PEqualNP.Represents.oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + j) false = b) ∨
      ∃ w < n + 1 + m + j, ∀ p : Fin n × Fin m,
        (run C.gates (PEqualNP.Represents.oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + j) false =
        (run C.gates (PEqualNP.Represents.oneEach (u.succAbove p.1) p.2)).getD w false)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + F.card ≤ C.size ∧
      PEqualNP.Represents.Represents (fun a c => G (u.succAbove a) c) D := by
  have hu := u.isLt
  obtain ⟨D, h1, _, h3, h4⟩ := engine (X := Fin n × Fin m) (n + 1 + m) (n + m) C
    (fun p => PEqualNP.Represents.oneEach (u.succAbove p.1) p.2) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
    (fun p => oneEach_length _ _) (fun p => oneEach_length _ _) F hC
    (by
      intro w hw
      rcases lt_trichotomy w u with h | h | h
      · refine Or.inr ⟨w, by omega, fun p => ?_⟩
        have := p.1.isLt; have := p.2.isLt
        simp only [oneEach_getD]
        rw [decide_eq_decide, sa_val]
        split_ifs <;> omega
      · refine Or.inl ⟨false, fun p => ?_⟩
        have := p.1.isLt; have := p.2.isLt
        simp only [oneEach_getD, decide_eq_false_iff_not]
        rw [sa_val]
        split_ifs <;> omega
      · refine Or.inr ⟨w - 1, by omega, fun p => ?_⟩
        have := p.1.isLt; have := p.2.isLt
        simp only [oneEach_getD]
        rw [decide_eq_decide, sa_val]
        split_ifs <;> omega)
    (by
      rintro ⟨b, hb⟩
      obtain ⟨a, c, hac⟩ := ht
      obtain ⟨a', c', hac'⟩ := hf
      have e1 : G (u.succAbove a) c = b := (hr _ c).symm.trans (hb (a, c))
      have e2 : G (u.succAbove a') c' = b := (hr _ c').symm.trans (hb (a', c'))
      rw [e1] at hac; rw [e2] at hac'; rw [hac] at hac'; exact absurd hac' (by simp)) hF
  exact ⟨D, h1, h3, fun a c => (h4 (a, c)).trans (hr _ c)⟩

/-- A gate nobody reads, not the output, can be made an empty OR. -/
theorem prune (N : ℕ) (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack N C) (j : ℕ) (hj : j < C.gates.length)
    (hdead : ∀ k < C.gates.length, N + j ∉ (gateAt C k).inputs) (ho : C.output ≠ N + j) :
    Monotone2 ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ ∧ ReadsBack N ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ ∧
      (⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ : Circuit).size = C.size ∧
      (∀ x : List Bool, x.length = N → (⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ : Circuit).eval x = C.eval x) ∧
      (∀ x : List Bool, x.length = N → (run (C.gates.set j ⟨GateOp.or, []⟩) x).getD (N + j) false = false) := by
  set C' : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ with hC'
  have hlen : C'.gates.length = C.gates.length := by simp [C']
  have hg : ∀ k, gateAt C' k = if k = j then ⟨GateOp.or, []⟩ else gateAt C k := by
    intro k
    simp only [gateAt, C', List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hk : k = j
    · subst hk; simp [hj]
    · simp [hk, Ne.symm hk]
  have hm' : Monotone2 C' := by
    intro g hg'
    rcases List.mem_or_eq_of_mem_set hg' with h | h
    · exact hm g h
    · subst h; simp
  have hb' : ReadsBack N C' := by
    intro k hk i hi
    rw [hg] at hi
    split_ifs at hi with h
    · simp at hi
    · exact hb k (by rw [hlen] at hk; exact hk) i hi
  have agree : ∀ x : List Bool, x.length = N → ∀ i, i ≠ N + j →
      (run C'.gates x).getD i false = (run C.gates x).getD i false := by
    intro x hx i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hlo : i < N
      · rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
      by_cases hhi : N + C.gates.length ≤ i
      · rw [past _ _ _ (by rw [hlen]; omega), past _ _ _ (by omega)]
      have hk : i - N < C.gates.length := by omega
      have hik : i = N + (i - N) := by omega
      rw [hik, gv N C' hb' x hx _ (by rw [hlen]; exact hk), gv N C hb x hx _ hk, hg, if_neg (by omega)]
      congr 1
      refine List.map_congr_left fun i' hi' => ih i' ?_ ?_
      · have := hb _ hk i' hi'; omega
      · rintro rfl; exact hdead _ hk hi'
  refine ⟨hm', hb', by simp [Circuit.size, C'], fun x hx => agree x hx _ ho, fun x hx => ?_⟩
  change (run C'.gates x).getD (N + j) false = false
  rw [gv N C' hb' x hx j (by rw [hlen]; exact hj), hg, if_pos rfl]
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_25491_aux

open PEqualNP.Outside.L_meta_25491_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25491 : ∀ (n m s : ℕ) (G : Fin (n + 1) → Fin m → Bool),
  2 ≤ n →
  (∀ u v : Fin (n + 1), u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false) →
  PEqualNP.Represents.RepSizeAtMost G s →
  (∃ u : Fin (n + 1), ∃ t : ℕ, t + 2 ≤ s ∧
    PEqualNP.Represents.RepSizeAtMost (fun a c => G (u.succAbove a) c) t) ∨
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 1 + m) C ∧
    PEqualNP.Represents.Represents G C ∧
    ∀ u : Fin (n + 1),
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) u.val = 1 ∧
      ∃ (j : Fin C.gates.length) (w : ℕ),
        (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ((C.gates.get j).inputs = [u.val, w] ∨ (C.gates.get j).inputs = [w, u.val])) := by
  classical
  intro n m s G hn hinc hrep
  obtain ⟨C0, hC0m, hC0s, hC0r⟩ := hrep
  have ev : ∀ (C : Circuit) (x : List Bool), C.eval x = (run C.gates x).getD C.output false := fun _ _ => rfl
  obtain ⟨c01, hc01, _⟩ := hinc ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
  have ht : ∃ a c, G a c = true := ⟨_, c01, hc01⟩
  have hf : ∃ a c, G a c = false := by
    obtain ⟨c, _, h⟩ := hinc ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
    exact ⟨_, c, h⟩
  obtain ⟨D0, h01, h02, h03, h04⟩ := same_rep (n + 1) m G C0 hC0m hC0r ht hf ∅ (by simp)
  have hex : ∃ k, ∃ D : Circuit, Monotone2 D ∧ ReadsBack (n + 1 + m) D ∧ D.size ≤ k ∧ Represents G D :=
    ⟨C0.size, D0, h01, h02, by simpa using h03, h04⟩
  have hs0 : Nat.find hex ≤ s :=
    (Nat.find_min' hex ⟨D0, h01, h02, by simpa using h03, h04⟩).trans hC0s
  obtain ⟨D, hDm, hDb, hDs, hDr⟩ := Nat.find_spec hex
  have hmin : ∀ D' : Circuit, Monotone2 D' → ReadsBack (n + 1 + m) D' → Represents G D' →
      Nat.find hex ≤ D'.size := fun D' a b c => Nat.find_min' hex ⟨D', a, b, le_rfl, c⟩
  by_cases hgood : ∀ u : Fin (n + 1), readsIn D (Finset.range D.size) u.val = 1 ∧
      ∃ (j : Fin D.gates.length) (w : ℕ), (D.gates.get j).op = GateOp.or ∧
        ((D.gates.get j).inputs = [u.val, w] ∨ (D.gates.get j).inputs = [w, u.val])
  · exact Or.inr ⟨D, hDm, hDs.trans hs0, hDb, hDr, hgood⟩
  left
  obtain ⟨u, hu⟩ := not_forall.mp hgood
  refine ⟨u, ?_⟩
  have huN := u.isLt
  -- the deleted graph is not constant
  have hsa : ∀ a : Fin n, u.succAbove a ≠ u := fun a => Fin.succAbove_ne u a
  obtain ⟨cd, hcd1, hcd2⟩ := hinc (u.succAbove ⟨0, by omega⟩) (u.succAbove ⟨1, by omega⟩) (by
    intro h
    have := Fin.succAbove_right_injective h
    simp [Fin.ext_iff] at this)
  have ht' : ∃ a c, G (u.succAbove a) c = true := ⟨_, cd, hcd1⟩
  have hf' : ∃ a c, G (u.succAbove a) c = false := ⟨_, cd, hcd2⟩
  -- row u is off on the inputs of the deleted graph
  have hoffu : ∀ p : Fin n × Fin m,
      (run D.gates (oneEach (u.succAbove p.1) p.2)).getD u false = false := by
    intro p
    rw [wi _ _ _ _ (by omega)]
    have := hsa p.1
    simp only [decide_eq_false_iff_not, not_or]
    refine ⟨fun h => this (Fin.ext h.symm), by omega⟩
  have hlenS : ∀ p : Fin n × Fin m, (oneEach (u.succAbove p.1) p.2).length = (n + 1 + m) := fun p => oneEach_length _ _
  -- a gate reading a wire off on all those inputs is off or a copy there
  have readerF : ∀ j, j < D.gates.length → ∀ a ∈ (gateAt D j).inputs,
      (∀ p : Fin n × Fin m, (run D.gates (oneEach (u.succAbove p.1) p.2)).getD a false = false) →
      ((∃ b, ∀ p : Fin n × Fin m, (run D.gates (oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + j) false = b) ∨
      ∃ w < n + 1 + m + j, ∀ p : Fin n × Fin m, (run D.gates (oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + j) false =
        (run D.gates (oneEach (u.succAbove p.1) p.2)).getD w false) := by
    intro j hj a ha hoff
    obtain ⟨hop, hl⟩ := gok D hDm j hj
    rcases shape _ hop _ hl a ha with h | ⟨w, hw, h⟩
    · exact Or.inl ⟨false, fun p => by rw [gv (n + 1 + m) D hDb _ (hlenS p) j hj]; exact h _ (hoff p)⟩
    · exact Or.inr ⟨w, hDb j hj w hw, fun p => by rw [gv (n + 1 + m) D hDb _ (hlenS p) j hj]; exact h _ (hoff p)⟩
  have fin2 : ∀ j k : ℕ, j ≠ k → j < D.gates.length → k < D.gates.length →
      ((∃ b, ∀ p : Fin n × Fin m, (run D.gates (oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + j) false = b) ∨
      ∃ w < n + 1 + m + j, ∀ p : Fin n × Fin m, (run D.gates (oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + j) false =
        (run D.gates (oneEach (u.succAbove p.1) p.2)).getD w false) →
      ((∃ b, ∀ p : Fin n × Fin m, (run D.gates (oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + k) false = b) ∨
      ∃ w < n + 1 + m + k, ∀ p : Fin n × Fin m, (run D.gates (oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + k) false =
        (run D.gates (oneEach (u.succAbove p.1) p.2)).getD w false) →
      ∃ t : ℕ, t + 2 ≤ s ∧ RepSizeAtMost (fun a c => G (u.succAbove a) c) t := by
    intro j k hjk hj hk Fj Fk
    obtain ⟨D', h1, h2, h3⟩ := del_rep n m G u D hDm hDr ht' hf' {j, k} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨hj, Fj⟩
      · exact ⟨hk, Fk⟩)
    rw [Finset.card_pair hjk] at h2
    refine ⟨D'.size, ?_, D', h1, le_rfl, h3⟩
    have : D.size ≤ s := hDs.trans hs0
    omega
  by_cases hA : ∃ j, j < D.gates.length ∧ u.val ∈ (gateAt D j).inputs
  swap
  · -- no reader of row u: monotonicity contradicts incomparability
    exfalso
    push_neg at hA
    set v := u.succAbove ⟨0, by omega⟩ with hv
    have hvu : v ≠ u := hsa _
    have le : ∀ c : Fin m, ∀ i, i ≠ u.val → (run D.gates (oneEach u c)).getD i false = true →
        (run D.gates (oneEach v c)).getD i false = true := by
      intro c i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi h
        by_cases hlo : i < (n + 1 + m)
        · rw [wi _ _ _ _ hlo] at h ⊢
          simp only [decide_eq_true_eq] at h ⊢
          omega
        by_cases hhi : (n + 1 + m) + D.gates.length ≤ i
        · rw [past _ _ _ (by rw [oneEach_length]; omega)] at h; exact absurd h (by simp)
        have hk : i - (n + 1 + m) < D.gates.length := by omega
        have hik : i = (n + 1 + m) + (i - (n + 1 + m)) := by omega
        rw [hik, gv (n + 1 + m) D hDb _ (oneEach_length _ _) _ hk] at h ⊢
        refine op_le _ (gok D hDm _ hk).1 _ _ _ (fun i' hi' => ih i' ?_ ?_) h
        · have := hDb _ hk i' hi'; omega
        · rintro rfl; exact hA _ hk hi'
    by_cases ho : D.output = u.val
    · obtain ⟨c, hc1, _⟩ := hinc v u hvu
      rw [← hDr, ev, ho, wi _ _ _ _ (by omega)] at hc1
      simp only [decide_eq_true_eq] at hc1
      have : (v : ℕ) ≠ u := fun h => hvu (Fin.ext h)
      omega
    · obtain ⟨c, hc1, hc2⟩ := hinc u v (Ne.symm hvu)
      rw [← hDr, ev] at hc1 hc2
      rw [le c _ ho hc1] at hc2
      exact absurd hc2 (by simp)
  obtain ⟨j, hj, hju⟩ := hA
  by_cases hB : ∃ k, k < D.gates.length ∧ k ≠ j ∧ u.val ∈ (gateAt D k).inputs
  · obtain ⟨k, hk, hkj, hku⟩ := hB
    exact fin2 j k (Ne.symm hkj) hj hk (readerF j hj _ hju hoffu) (readerF k hk _ hku hoffu)
  push_neg at hB
  have hcount : readsIn D (Finset.range D.size) u.val = (gateAt D j).inputs.count u.val := by
    unfold readsIn
    refine Finset.sum_eq_single j (fun k hk hkj => List.count_eq_zero.mpr (hB k (Finset.mem_range.mp hk) hkj))
      (fun h => absurd (Finset.mem_range.mpr hj) h)
  -- gate j is off whenever row u is off
  have hzero : ∀ x : List Bool, x.length = (n + 1 + m) → (run D.gates x).getD u false = false →
      (run D.gates x).getD ((n + 1 + m) + j) false = false := by
    intro x hx hxu
    rw [gv (n + 1 + m) D hDb x hx j hj]
    obtain ⟨hop, hl⟩ := gok D hDm j hj
    rcases hop with hop | hop
    · rw [hop]; exact and_off _ _ hju _ hxu
    · rw [hop]
      refine or_off _ u.val (allu _ hl _ hju fun ⟨h1, w, h2⟩ => hu ⟨hcount.trans h1, ⟨j, hj⟩, w, ?_⟩) _ hxu
      have he : D.gates.get ⟨j, hj⟩ = gateAt D j := (List.getD_eq_getElem _ _ hj).symm
      rw [he]
      exact ⟨hop, h2⟩
  have Fj : (∃ b, ∀ p : Fin n × Fin m, (run D.gates (oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + j) false = b) ∨
      ∃ w < n + 1 + m + j, ∀ p : Fin n × Fin m, (run D.gates (oneEach (u.succAbove p.1) p.2)).getD (n + 1 + m + j) false =
        (run D.gates (oneEach (u.succAbove p.1) p.2)).getD w false :=
    Or.inl ⟨false, fun p => hzero _ (hlenS p) (hoffu p)⟩
  by_cases hC : ∃ k, k < D.gates.length ∧ (n + 1 + m) + j ∈ (gateAt D k).inputs
  · obtain ⟨k, hk, hkj⟩ := hC
    have hjk : j ≠ k := by
      rintro rfl
      have := hDb j hj _ hkj
      omega
    exact fin2 j k hjk hj hk Fj (readerF k hk _ hkj fun p => hzero _ (hlenS p) (hoffu p))
  push_neg at hC
  exfalso
  by_cases ho : D.output = (n + 1 + m) + j
  · set v := u.succAbove ⟨0, by omega⟩ with hv
    have hvu : v ≠ u := hsa _
    obtain ⟨c, hc1, _⟩ := hinc v u hvu
    rw [← hDr, ev, ho, hzero _ (oneEach_length _ _) (by
      rw [wi _ _ _ _ (by omega)]
      simp only [decide_eq_false_iff_not, not_or]
      exact ⟨fun h => hvu (Fin.ext h.symm), by omega⟩)] at hc1
    exact absurd hc1 (by simp)
  · obtain ⟨p1, p2, p3, p4, p5⟩ := prune (n + 1 + m) D hDm hDb j hj hC ho
    obtain ⟨D'', q1, q2, q3, q4⟩ := same_rep (n + 1) m G _ p1
      (fun a c => (p4 _ (oneEach_length _ _)).trans (hDr a c)) ht hf {j}
      (by
        intro i hi
        rw [Finset.mem_singleton] at hi
        subst hi
        exact ⟨by simpa using hj, Or.inl ⟨false, fun p => p5 _ (oneEach_length _ _)⟩⟩)
    have := hmin D'' q1 q2 q4
    rw [Finset.card_singleton, p3] at q3
    omega

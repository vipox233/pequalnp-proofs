import Mathlib
import PEqualNP.Defs

-- The simulation engine (run, emit, engine3 and their helpers) is copied from the merged proof
-- of L-meta-18153 by rogatov.

namespace PEqualNP.Outside.L_meta_28073

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
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
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
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

theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi

def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_prefix _ _ _ _ (h t rfl)

theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
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
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl

theorem engine3 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + F.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
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
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
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
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
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
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
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
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm


open PEqualNP.Represents

theorem eval_run (C : Circuit) (x : List Bool) : C.eval x = (run C.gates x).getD C.output false :=
  rfl

theorem mono2_ops (C : Circuit) (hC : Monotone2 C) :
    ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have := (hC g hg).1
  simpa using this

theorem eval_mono (C : Circuit) (hC : Monotone2 C) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) (hx : C.eval x = true) :
    C.eval y = true :=
  mono C.gates x y hl h (mono2_ops C hC) C.output hx

theorem eval_false (C : Circuit) (hC : Monotone2 C) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) (hy : C.eval y = false) :
    C.eval x = false := by
  cases hx : C.eval x
  · rfl
  · rw [eval_mono C hC x y hl h hx] at hy
    exact hy

theorem ext_getD (l1 l2 : List Bool) (hl : l1.length = l2.length)
    (h : ∀ w, l1.getD w false = l2.getD w false) : l1 = l2 := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem ne_const {X : Type} (f : X → Bool) (x1 x2 : X) (h1 : f x1 = true) (h2 : f x2 = false) :
    ¬ ∃ b, ∀ x, f x = b := by
  rintro ⟨b, hb⟩
  rw [hb] at h1 h2
  rw [h1] at h2
  exact absurd h2 (by decide)

def inp (N : ℕ) (P : ℕ → Bool) : List Bool := List.ofFn fun i : Fin N => P i.val

theorem inp_len (N : ℕ) (P : ℕ → Bool) : (inp N P).length = N := by simp [inp]

theorem inp_getD (N : ℕ) (P : ℕ → Bool) (w : ℕ) :
    (inp N P).getD w false = (decide (w < N) && P w) := by
  rw [List.getD_eq_getElem?_getD]
  unfold inp
  by_cases h : w < N <;> simp [h]

theorem one_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem one_getD {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = decide (w = u.val ∨ w = n + v.val) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD]
  have hu := u.isLt
  have hv := v.isLt
  by_cases h1 : w < n
  · rw [List.getElem?_append_left (by simpa using h1)]
    simp [h1, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    by_cases h2 : w < n + m
    · simp [Fin.ext_iff]
      rw [dif_pos (by omega)]
      simp only [Option.getD_some]
      rw [← Bool.decide_or, decide_eq_decide]
      omega
    · simp [Fin.ext_iff]
      rw [dif_neg (by omega)]
      simp
      omega

theorem agree (c : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, c ∉ g.inputs) (x y : List Bool)
    (hl : x.length = y.length) (h : ∀ w, w ≠ c → x.getD w false = y.getD w false) :
    ∀ w, w ≠ c → (run gs x).getD w false = (run gs y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h' => hg g' (by simp [h']))
    intro w hw
    rw [run_snoc, run_snoc]
    have l1 := run_length gs x
    have l2 := run_length gs y
    have hgc : c ∉ g.inputs := hg g (by simp)
    have ev : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) := by
      congr 1
      refine List.map_congr_left fun i hi => ih' i ?_
      rintro rfl
      exact hgc hi
    rcases Nat.lt_trichotomy w (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega)]
      exact ih' w hw
    · rw [show w = (run gs x).length by omega, getD_at,
        show (run gs x).length = (run gs y).length by omega, getD_at]
      exact ev
    · rw [List.getD_eq_default _ _ (by rw [List.length_append, l1]; simp; omega),
        List.getD_eq_default _ _ (by rw [List.length_append, l2]; simp; omega)]

theorem gate_fold (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (hl : ins.length ≤ 2) (c : ℕ) (hc : c ∈ ins) :
    (∀ V : ℕ → Bool, V c = false → op.eval (ins.map V) = false) ∨
      ∃ o, ∀ V : ℕ → Bool, V c = false → op.eval (ins.map V) = V o := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hc
  · simp at hc
    subst hc
    left
    intro V hV
    rcases hop with rfl | rfl <;> simp [GateOp.eval, hV]
  · simp at hc
    rcases hop with rfl | rfl
    · left
      intro V hV
      rcases hc with rfl | rfl <;> simp [GateOp.eval, hV]
    · right
      rcases hc with rfl | rfl
      · exact ⟨b, fun V hV => by simp [GateOp.eval, hV]⟩
      · exact ⟨a, fun V hV => by simp [GateOp.eval, hV]⟩
  · simp at hl

theorem del1 {X : Type} (N c : ℕ) (C : Circuit) (hC : Monotone2 C) (src : X → List Bool)
    (hsrc : ∀ x, (src x).length = N) (hc : c < N) (hoff : ∀ x, (src x).getD c false = false)
    (hne : ¬ ∃ b, ∀ x, C.eval (src x) = b)
    (y z : List Bool) (hy : y.length = z.length)
    (hyz : ∀ w, w ≠ c → y.getD w false = z.getD w false) (hdep : C.eval y ≠ C.eval z) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧ ∀ x, D.eval (src x) = C.eval (src x) := by
  classical
  have hout : C.output ≠ c := by
    intro hoc
    refine hne ⟨false, fun x => ?_⟩
    rw [eval_run, hoc, run_input _ _ _ (by rw [hsrc]; exact hc)]
    exact hoff x
  have hex : ∃ j, j < C.gates.length ∧ c ∈ (C.gates.getD j ⟨GateOp.and, []⟩).inputs := by
    by_contra hno
    push_neg at hno
    apply hdep
    rw [eval_run, eval_run]
    refine agree c C.gates ?_ y z hy hyz C.output hout
    intro g hg hcg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact hno j hj (by rw [List.getD_eq_getElem _ _ hj]; exact hcg)
  obtain ⟨hjl, hjc⟩ := Nat.find_spec hex
  have hjc' : c ∈ C.gates[Nat.find hex].inputs := by
    rwa [List.getD_eq_getElem _ _ hjl] at hjc
  have hg := hC _ (List.getElem_mem hjl)
  have hop : C.gates[Nat.find hex].op = GateOp.and ∨ C.gates[Nat.find hex].op = GateOp.or := by
    simpa using hg.1
  obtain ⟨D, hD, hsz, hev⟩ := engine3 N N C src src hsrc hsrc {Nat.find hex} hC
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩) hne (by
      intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      refine ⟨hjl, ?_⟩
      have rg : ∀ x, (run C.gates (src x)).getD (N + Nat.find hex) false =
          C.gates[Nat.find hex].op.eval (C.gates[Nat.find hex].inputs.map fun i =>
            if i < N + Nat.find hex then (run C.gates (src x)).getD i false else false) := by
        intro x
        have := run_gate C.gates (src x) (Nat.find hex) hjl
        rw [hsrc] at this
        exact this
      have hV : ∀ x, (fun i => if i < N + Nat.find hex then (run C.gates (src x)).getD i false
          else false) c = false := by
        intro x
        simp only
        rw [if_pos (by omega), run_input _ _ _ (by rw [hsrc]; exact hc)]
        exact hoff x
      rcases gate_fold _ hop _ hg.2 c hjc' with h | ⟨o, h⟩
      · left
        exact ⟨false, fun x => by rw [rg x]; exact h _ (hV x)⟩
      · by_cases ho : o < N + Nat.find hex
        · right
          refine ⟨o, ho, fun x => ?_⟩
          rw [rg x, h _ (hV x)]
          rw [if_pos ho]
        · left
          refine ⟨false, fun x => ?_⟩
          rw [rg x, h _ (hV x)]
          rw [if_neg ho])
  exact ⟨D, hD, by simpa using hsz, hev⟩

def chainG (N : ℕ) : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | k, p, c :: cs => ⟨GateOp.or, [p, c]⟩ :: chainG N (k + 1) (N + k) cs

theorem chainG_len (N : ℕ) : ∀ (cs : List ℕ) (k p : ℕ), (chainG N k p cs).length = cs.length
  | [], _, _ => rfl
  | c :: cs, k, p => by simp [chainG, chainG_len N cs]

theorem chainG_ok (N : ℕ) : ∀ (cs : List ℕ) (k p : ℕ), ∀ g ∈ chainG N k p cs,
    g.op = GateOp.or ∧ g.inputs.length = 2
  | [], _, _ => by simp [chainG]
  | c :: cs, k, p => by
    intro g hg
    simp only [chainG, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact chainG_ok N cs (k + 1) (N + k) g hg

def finW (N k p : ℕ) (cs : List ℕ) : ℕ := if cs = [] then p else N + k + cs.length - 1

theorem finW_lt (N k p : ℕ) (cs : List ℕ) (hp : p < N + k) : finW N k p cs < N + k + cs.length := by
  cases cs with
  | nil => simp [finW]; omega
  | cons c cs => simp [finW]

theorem any_congr' (cs : List ℕ) (f g : ℕ → Bool) (h : ∀ c ∈ cs, f c = g c) :
    cs.any f = cs.any g := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.any_cons]
    rw [h c (by simp), ih (fun c' hc' => h c' (by simp [hc']))]

theorem chainG_run (N : ℕ) : ∀ (cs : List ℕ) (k p : ℕ) (w : List Bool), w.length = N + k →
    p < N + k → (∀ c ∈ cs, c < N + k) →
    (run (chainG N k p cs) w).length = N + k + cs.length ∧
    (∀ i, i < N + k → (run (chainG N k p cs) w).getD i false = w.getD i false) ∧
    (run (chainG N k p cs) w).getD (finW N k p cs) false =
      (w.getD p false || cs.any (fun c => w.getD c false))
  | [], k, p, w, hw, hp, _ => by
    refine ⟨by simp [chainG, run, hw], fun i _ => rfl, ?_⟩
    simp [chainG, run, finW]
  | c :: cs, k, p, w, hw, hp, hc => by
    have hc0 : c < N + k := hc c (by simp)
    have e : run (chainG N k p (c :: cs)) w =
        run (chainG N (k + 1) (N + k) cs) (w ++ [w.getD p false || w.getD c false]) := by
      simp [chainG, run, GateOp.eval]
    have hw' : (w ++ [w.getD p false || w.getD c false]).length = N + (k + 1) := by
      simp [hw]; omega
    obtain ⟨i1, i2, i3⟩ := chainG_run N cs (k + 1) (N + k) _ hw' (by omega)
      (fun c' hc' => by have := hc c' (by simp [hc']); omega)
    have pre : ∀ i, i < N + k → (w ++ [w.getD p false || w.getD c false]).getD i false =
        w.getD i false := fun i hi => getD_lt _ _ _ (by omega)
    rw [e]
    refine ⟨by rw [i1]; simp; omega, fun i hi => by rw [i2 i (by omega), pre i hi], ?_⟩
    have hf : finW N k p (c :: cs) = finW N (k + 1) (N + k) cs := by
      cases cs with
      | nil => simp [finW]
      | cons d ds => simp [finW]; omega
    rw [hf, i3]
    have at0 : (w ++ [w.getD p false || w.getD c false]).getD (N + k) false =
        (w.getD p false || w.getD c false) := by
      rw [show N + k = w.length by omega, getD_at]
    rw [at0, any_congr' cs _ (fun c => w.getD c false)
      (fun c' hc' => pre c' (hc c' (by simp [hc'])))]
    simp [Bool.or_assoc]

theorem eval_pre (P : List Gate) (D : Circuit) (y : List Bool) :
    (⟨P ++ D.gates, D.output⟩ : Circuit).eval y = D.eval (run P y) := by
  show (run (P ++ D.gates) y).getD D.output false = (run D.gates (run P y)).getD D.output false
  simp [run, List.foldl_append]

theorem mono_pre (N k p : ℕ) (cs : List ℕ) (D : Circuit) (hD : Monotone2 D) :
    Monotone2 (⟨chainG N k p cs ++ D.gates, D.output⟩ : Circuit) := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · have := chainG_ok N cs k p g hg
    exact ⟨by simp [this.1], by omega⟩
  · exact hD g hg

def E (n m t : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (i : Fin (n + t)) (j : Fin m) : Bool :=
  if h : i.val < n then A ⟨i.val, h⟩ j else A u j

theorem E_lt (n m t : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (i : Fin (n + t)) (j : Fin m)
    (h : i.val < n) : E n m t A u i j = A ⟨i.val, h⟩ j := dif_pos h

theorem E_ge (n m t : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (i : Fin (n + t)) (j : Fin m)
    (h : ¬ i.val < n) : E n m t A u i j = A u j := dif_neg h

theorem E_cast (n m t : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (i : Fin n) (j : Fin m) :
    E n m t A u (Fin.castAdd t i) j = A i j := by
  rw [E_lt _ _ _ _ _ _ _ (by simp)]
  rfl

theorem rep_empty {n m : ℕ} (A : Fin n → Fin m → Bool) (h : ∀ i j, A i j = false) (s : ℕ) :
    RepSizeAtMost A s := by
  refine ⟨⟨[], n + m⟩, fun g hg => by simp at hg, by simp [Circuit.size], fun i j => ?_⟩
  rw [eval_run, h]
  show (oneEach i j).getD (n + m) false = false
  rw [one_getD, decide_eq_false_iff_not]
  have := i.isLt
  have := j.isLt
  omega

theorem lay_rows (n m t : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (D : Circuit)
    (hD : Monotone2 D)
    (hDr : ∀ (i : Fin (n + t)) (j : Fin m), i.val < n → D.eval (oneEach i j) = E n m t A u i j)
    (i1 : Fin n) (j1 : Fin m) (h1 : A i1 j1 = true) (i2 : Fin n) (j2 : Fin m)
    (h2 : A i2 j2 = false) :
    ∃ D2 : Circuit, Monotone2 D2 ∧ D2.size ≤ D.size ∧ Represents A D2 := by
  have hv : ∀ (i : Fin n) (j : Fin m), D.eval (oneEach (Fin.castAdd t i) j) = A i j := by
    intro i j
    rw [hDr _ _ (by simp), E_cast]
  obtain ⟨D2, hD2, hs, hev⟩ := engine3 (n + t + m) (n + m) D
    (fun x : Fin n × Fin m => oneEach (Fin.castAdd t x.1) x.2) (fun x => oneEach x.1 x.2)
    (fun x => one_len _ _) (fun x => one_len _ _) ∅ hD
    (by
      intro w hw
      rcases Nat.lt_or_ge w n with h | h
      · right
        refine ⟨w, by omega, fun x => ?_⟩
        rw [one_getD, one_getD, decide_eq_decide]
        simp only [Fin.coe_castAdd]
        omega
      · rcases Nat.lt_or_ge w (n + t) with h' | h'
        · left
          refine ⟨false, fun x => ?_⟩
          rw [one_getD, decide_eq_false_iff_not]
          simp only [Fin.coe_castAdd]
          have := x.1.isLt
          omega
        · right
          refine ⟨w - t, by omega, fun x => ?_⟩
          rw [one_getD, one_getD, decide_eq_decide]
          simp only [Fin.coe_castAdd]
          have := x.1.isLt
          omega)
    (ne_const _ (i1, j1) (i2, j2) (by simp only; rw [hv]; exact h1)
      (by simp only; rw [hv]; exact h2))
    (by simp)
  refine ⟨D2, hD2, by simpa using hs, fun i j => ?_⟩
  have := hev (i, j)
  simp only at this
  rw [this, hv]

theorem low_strict (n m t : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (i0 : Fin n) (j0 : Fin m)
    (hu : A u j0 = true) (hi : A i0 j0 = false) (s : ℕ)
    (h : RepSizeAtMost (E n m t A u) s) : ∃ b, RepSizeAtMost A b ∧ b + t ≤ s := by
  obtain ⟨C, hC, hs, hr⟩ := h
  have key : ∀ k, k ≤ t → ∃ D : Circuit, Monotone2 D ∧ D.size + k ≤ C.size ∧
      ∀ (i : Fin (n + t)) (j : Fin m), i.val < n + t - k →
        D.eval (oneEach i j) = E n m t A u i j := by
    intro k
    induction k with
    | zero => intro _; exact ⟨C, hC, by simp, fun i j _ => hr i j⟩
    | succ k ih =>
      intro hk
      obtain ⟨D, hD, hDs, hDr⟩ := ih (by omega)
      have hu' : (Fin.castAdd t u).val < n + t - (k + 1) := by
        simp only [Fin.coe_castAdd]; have := u.isLt; omega
      have hi' : (Fin.castAdd t i0).val < n + t - (k + 1) := by
        simp only [Fin.coe_castAdd]; have := i0.isLt; omega
      have ei : D.eval (oneEach (Fin.castAdd t i0) j0) = false := by
        rw [hDr _ _ (by omega), E_cast]; exact hi
      obtain ⟨D', hD', hD's, hD'r⟩ :=
        del1 (X := {p : Fin (n + t) × Fin m // p.1.val < n + t - (k + 1)})
        (n + t + m) (n + t - (k + 1)) D hD (fun p => oneEach p.1.1 p.1.2)
        (fun p => one_len _ _) (by omega)
        (fun p => by
          have := p.2
          rw [one_getD, decide_eq_false_iff_not]
          omega)
        (ne_const _ ⟨(Fin.castAdd t u, j0), hu'⟩ ⟨(Fin.castAdd t i0, j0), hi'⟩
          (by simp only; rw [hDr _ _ (by omega), E_cast]; exact hu)
          (by simp only; exact ei))
        (oneEach (⟨n + t - (k + 1), by omega⟩ : Fin (n + t)) j0)
        (inp (n + t + m) (fun w => decide (w = n + t + j0.val)))
        (by rw [one_len, inp_len])
        (by
          intro w hw
          rw [one_getD, inp_getD, ← Bool.decide_and, decide_eq_decide]
          dsimp only
          have := j0.isLt
          omega)
        (by
          rw [hDr _ _ (by dsimp only; omega), E_ge _ _ _ _ _ _ _ (by dsimp only; omega), hu]
          rw [eval_false D hD _ (oneEach (Fin.castAdd t i0) j0) (by rw [inp_len, one_len])
            (by
              intro w hw
              rw [inp_getD] at hw
              rw [one_getD]
              simp at hw ⊢
              omega) ei]
          decide)
      exact ⟨D', hD', by omega, fun i j hij => (hD'r ⟨(i, j), hij⟩).trans (hDr i j (by omega))⟩
  obtain ⟨D, hD, hDs, hDr⟩ := key t le_rfl
  obtain ⟨D2, hD2, hs2, hr2⟩ :=
    lay_rows n m t A u D hD (fun i j hi => hDr i j (by omega)) u j0 hu i0 j0 hi
  exact ⟨D2.size, ⟨D2, hD2, le_rfl, hr2⟩, by omega⟩

theorem low_weak (n m t : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (i2 : Fin n) (j2 : Fin m)
    (h2 : A i2 j2 = false) (s : ℕ) (h : RepSizeAtMost (E n m t A u) s) : RepSizeAtMost A s := by
  by_cases ht : ∃ i j, A i j = true
  · obtain ⟨i1, j1, h1⟩ := ht
    obtain ⟨C, hC, hs, hr⟩ := h
    obtain ⟨D2, hD2, hs2, hr2⟩ := lay_rows n m t A u C hC (fun i j _ => hr i j) i1 j1 h1 i2 j2 h2
    exact ⟨D2, hD2, by omega, hr2⟩
  · exact rep_empty A (fun i j => by simpa using fun h => ht ⟨i, j, h⟩) s

theorem any_rows (n t i J : ℕ) (hJ : n + t ≤ J) (hi : i < n + t) :
    ((List.range t).map (fun k => n + k)).any (fun c => decide (c = i ∨ c = J)) =
      decide (n ≤ i) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at ha
    rw [decide_eq_true_iff] at h
    omega
  · intro h
    exact ⟨i, List.mem_map.2 ⟨i - n, List.mem_range.2 (by omega), by omega⟩, by simp⟩

theorem up_copies (n m t : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (b : ℕ)
    (i1 : Fin n) (j1 : Fin m) (h1 : A i1 j1 = true) (i2 : Fin n) (j2 : Fin m)
    (h2 : A i2 j2 = false) (h : RepSizeAtMost A b) : RepSizeAtMost (E n m t A u) (b + t) := by
  obtain ⟨C, hC, hs, hr⟩ := h
  let cs : List ℕ := (List.range t).map (fun k => n + k)
  have hcsl : cs.length = t := by simp [cs]
  have hcs : ∀ c ∈ cs, c < n + t + m + 0 := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_range] at ha
    omega
  let rowOf : Fin (n + t) → Fin n := fun i => if h : i.val < n then ⟨i.val, h⟩ else u
  have hE : ∀ i j, E n m t A u i j = A (rowOf i) j := by
    intro i j
    simp only [E, rowOf]
    split_ifs <;> rfl
  have hrow : ∀ i : Fin (n + t), (rowOf i).val = if i.val < n then i.val else u.val := by
    intro i
    simp only [rowOf]
    split_ifs <;> rfl
  have hrc : ∀ i : Fin n, rowOf (Fin.castAdd t i) = i := by
    intro i
    simp only [rowOf]
    rw [dif_pos (by simp)]
    rfl
  let ch := chainG (n + t + m) 0 u.val cs
  have hch := fun x : Fin (n + t) × Fin m => chainG_run (n + t + m) cs 0 u.val (oneEach x.1 x.2)
    (by rw [one_len]; omega) (by have := u.isLt; omega) hcs
  obtain ⟨D, hD, hDs, hev⟩ := engine3 (n + m) (n + t + m + t) C
    (fun x : Fin (n + t) × Fin m => oneEach (rowOf x.1) x.2) (fun x => run ch (oneEach x.1 x.2))
    (fun x => one_len _ _) (fun x => by rw [(hch x).1, hcsl]; omega) ∅ hC
    (by
      intro w hw
      right
      rcases Nat.lt_or_ge w n with hwn | hwn
      · by_cases hwu : w = u.val
        · refine ⟨finW (n + t + m) 0 u.val cs, by
            have := finW_lt (n + t + m) 0 u.val cs (by omega); omega, fun x => ?_⟩
          rw [(hch x).2.2, one_getD, one_getD, hwu]
          rw [any_congr' cs _ (fun c => decide (c = x.1.val ∨ c = n + t + x.2.val))
            (fun c _ => one_getD _ _ c)]
          rw [any_rows n t x.1.val (n + t + x.2.val) (by omega) x.1.isLt, hrow]
          have := x.1.isLt
          have := u.isLt
          split_ifs with hh
          · rw [← Bool.decide_or, decide_eq_decide]; omega
          · rw [← Bool.decide_or, decide_eq_decide]; omega
        · refine ⟨w, by omega, fun x => ?_⟩
          rw [(hch x).2.1 w (by omega), one_getD, one_getD, hrow]
          have := x.1.isLt
          have := u.isLt
          split_ifs with hh
          · rw [decide_eq_decide]; omega
          · rw [decide_eq_decide]; omega
      · refine ⟨w + t, by omega, fun x => ?_⟩
        rw [(hch x).2.1 (w + t) (by omega), one_getD, one_getD, hrow]
        have := x.1.isLt
        have := u.isLt
        split_ifs with hh
        · rw [decide_eq_decide]; omega
        · rw [decide_eq_decide]; omega)
    (ne_const _ (Fin.castAdd t i1, j1) (Fin.castAdd t i2, j2)
      (by simp only; rw [hrc, hr]; exact h1) (by simp only; rw [hrc, hr]; exact h2))
    (by simp)
  refine ⟨⟨ch ++ D.gates, D.output⟩, mono_pre _ _ _ _ D hD, ?_, fun i j => ?_⟩
  · simp only [Circuit.size, Finset.card_empty, Nat.add_zero] at hDs hs ⊢
    rw [List.length_append, chainG_len, hcsl]
    omega
  · rw [eval_pre]
    have := hev (i, j)
    simp only at this
    rw [this, hr, hE]

theorem del_cols (n m : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (j0 c' : Fin m)
    (hj0 : A u j0 = true) (hc' : A u c' = false) :
    ∀ (cs : List (Fin m)) (S : Finset (Fin m)), cs.Nodup → (∀ c ∈ cs, c ∉ S) →
    (∀ c ∈ cs, c ≠ j0 ∧ A u c = true) → j0 ∉ S → c' ∉ S →
    ∀ D : Circuit, Monotone2 D → (∀ i j, j ∉ S → D.eval (oneEach i j) = A i j) →
    ∃ D' : Circuit, Monotone2 D' ∧ D'.size + cs.length ≤ D.size ∧
      ∀ i j, j ∉ S → j ∉ cs → D'.eval (oneEach i j) = A i j := by
  intro cs
  induction cs with
  | nil =>
    intro S _ _ _ _ _ D hD hDr
    exact ⟨D, hD, by simp, fun i j hj _ => hDr i j hj⟩
  | cons c cs ih =>
    intro S hnd hcS hcs hj0S hc'S D hD hDr
    have hcS' : c ∉ S := hcS c (by simp)
    obtain ⟨hcj0, hcu⟩ := hcs c (by simp)
    have hcc' : c' ≠ c := by
      rintro rfl
      rw [hc'] at hcu
      exact absurd hcu (by decide)
    have ec : D.eval (oneEach u c') = false := by rw [hDr _ _ hc'S]; exact hc'
    obtain ⟨D1, hD1, hD1s, hD1r⟩ := del1 (X := {p : Fin n × Fin m // p.2 ∉ S ∧ p.2 ≠ c})
      (n + m) (n + c.val) D hD (fun p => oneEach p.1.1 p.1.2) (fun p => one_len _ _)
      (by have := c.isLt; omega)
      (fun p => by
        have h1 := p.2.2
        have h2 := p.1.1.isLt
        rw [one_getD, decide_eq_false_iff_not]
        rintro (h | h)
        · omega
        · exact h1 (Fin.ext (by omega)))
      (ne_const _ ⟨(u, j0), hj0S, fun h => hcj0 h.symm⟩ ⟨(u, c'), hc'S, hcc'⟩
        (by simp only; rw [hDr _ _ hj0S]; exact hj0) (by simp only; exact ec))
      (oneEach u c) (inp (n + m) (fun w => decide (w = u.val))) (by rw [one_len, inp_len])
      (by
        intro w hw
        rw [one_getD, inp_getD, ← Bool.decide_and, decide_eq_decide]
        have := u.isLt
        omega)
      (by
        rw [hDr _ _ hcS', hcu, eval_false D hD _ (oneEach u c') (by rw [inp_len, one_len])
          (by
            intro w hw
            rw [inp_getD] at hw
            rw [one_getD]
            simp at hw ⊢
            omega) ec]
        decide)
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨D', hD', hD's, hD'r⟩ := ih (insert c S) hnd'.2
      (fun c2 hc2 => by
        rw [Finset.mem_insert]
        rintro (h | h)
        · rw [h] at hc2; exact hnd'.1 hc2
        · exact hcS c2 (by simp [hc2]) h)
      (fun c2 hc2 => hcs c2 (by simp [hc2]))
      (by
        rw [Finset.mem_insert]
        rintro (h | h)
        · exact hcj0 h.symm
        · exact hj0S h)
      (by
        rw [Finset.mem_insert]
        rintro (h | h)
        · exact hcc' h
        · exact hc'S h)
      D1 hD1 (fun i j hj => by
        rw [Finset.mem_insert, not_or] at hj
        exact (hD1r ⟨(i, j), hj.2, hj.1⟩).trans (hDr i j hj.2))
    refine ⟨D', hD', by simp only [List.length_cons]; omega, fun i j hj hjc => ?_⟩
    rw [List.mem_cons, not_or] at hjc
    exact hD'r i j (by rw [Finset.mem_insert, not_or]; exact ⟨hjc.1, hj⟩) hjc.2

theorem up_weak (n m t : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n)
    (hfull : ∀ j, A u j = true → ∀ i, A i j = true) (i2 : Fin n) (j2 : Fin m)
    (h2 : A i2 j2 = false) (b : ℕ) (h : RepSizeAtMost A b) : RepSizeAtMost (E n m t A u) b := by
  classical
  obtain ⟨C, hC, hs, hr⟩ := h
  have hzero : ∃ c', A u c' = false := by
    by_contra hz
    simp only [not_exists, Bool.not_eq_false] at hz
    rw [hfull j2 (hz j2) i2] at h2
    exact absurd h2 (by decide)
  obtain ⟨c', hc'⟩ := hzero
  have hEu : ∀ (i : Fin (n + t)) (j : Fin m), ¬ (i.val < n ∧ i.val ≠ u.val) →
      E n m t A u i j = A u j := by
    intro i j hi
    by_cases hin : i.val < n
    · rw [E_lt _ _ _ _ _ _ _ hin]
      have : (⟨i.val, hin⟩ : Fin n) = u := Fin.ext (by by_contra hc; exact hi ⟨hin, hc⟩)
      rw [this]
    · exact E_ge _ _ _ _ _ _ _ hin
  have hE0 : ∀ (i : Fin (n + t)) (j : Fin m) (hi : i.val < n),
      E n m t A u i j = A ⟨i.val, hi⟩ j := fun i j hi => E_lt _ _ _ _ _ _ _ hi
  by_cases hJ : ∃ j0, A u j0 = true
  · obtain ⟨j0, hj0⟩ := hJ
    let cs := ((Finset.univ.filter fun j => A u j = true).erase j0).toList
    have hmem : ∀ c, c ∈ cs ↔ c ≠ j0 ∧ A u c = true := by intro c; simp [cs]
    obtain ⟨D1, hD1, hD1s, hD1r⟩ := del_cols n m A u j0 c' hj0 hc' cs ∅ (Finset.nodup_toList _)
      (fun c _ => by simp) (fun c hc => (hmem c).1 hc) (by simp) (by simp) C hC
      (fun i j _ => hr i j)
    let g : Fin m → Fin m := fun j => if A u j = true then j0 else j
    have hgv : ∀ j, (g j).val = if A u j = true then j0.val else j.val := by
      intro j
      simp only [g]
      split_ifs <;> rfl
    have hg : ∀ j, g j ∉ cs := by
      intro j hj
      rw [hmem] at hj
      simp only [g] at hj
      split_ifs at hj with h
      · exact hj.1 rfl
      · exact h hj.2
    have hD1' : ∀ i j, D1.eval (oneEach i (g j)) = A i (g j) :=
      fun i j => hD1r i (g j) (by simp) (hg j)
    let N := n + t + m
    let ccs : List ℕ := cs.map (fun c => n + t + c.val)
    have hccs : ∀ c ∈ ccs, c < N + 0 := by
      intro c hc
      obtain ⟨d, _, rfl⟩ := List.mem_map.1 hc
      have := d.isLt
      omega
    let ch := chainG N 0 (n + t + j0.val) ccs
    have hch := fun x : Fin (n + t) × Fin m => chainG_run N ccs 0 (n + t + j0.val)
      (oneEach x.1 x.2) (by rw [one_len]; omega) (by have := j0.isLt; omega) hccs
    have hfin : ∀ x : Fin (n + t) × Fin m,
        (run ch (oneEach x.1 x.2)).getD (finW N 0 (n + t + j0.val) ccs) false = A u x.2 := by
      intro x
      rw [(hch x).2.2, one_getD]
      rw [any_congr' ccs _ (fun c => decide (c = n + t + x.2.val)) (fun c hc => by
        obtain ⟨d, _, rfl⟩ := List.mem_map.1 hc
        rw [one_getD, decide_eq_decide]
        have := x.1.isLt
        omega)]
      have e1 : decide (n + t + j0.val = x.1.val ∨ n + t + j0.val = n + t + x.2.val) =
          decide (x.2 = j0) := by
        rw [decide_eq_decide, Fin.ext_iff]
        have := x.1.isLt
        omega
      have e2 : ccs.any (fun c => decide (c = n + t + x.2.val)) = decide (x.2 ∈ cs) := by
        rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
        constructor
        · rintro ⟨c, hc, hce⟩
          obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
          rw [decide_eq_true_iff] at hce
          have : d = x.2 := Fin.ext (by omega)
          rw [← this]
          exact hd
        · intro hx
          exact ⟨n + t + x.2.val, List.mem_map.2 ⟨x.2, hx, rfl⟩, by simp⟩
      rw [e1, e2]
      by_cases hx : x.2 = j0
      · rw [hx, hj0]
        simp
      · rw [decide_eq_false hx, Bool.false_or]
        simp only [hmem]
        cases hA : A u x.2 <;> simp [hx]
    let src : Fin (n + t) × Fin m → List Bool := fun x => inp (n + m) (fun w =>
      decide ((w = x.1.val ∧ x.1.val < n ∧ w ≠ u.val) ∨ (w = u.val ∧ A u x.2 = true) ∨
        w = n + (g x.2).val))
    have hval : ∀ i j, D1.eval (src (i, j)) = E n m t A u i j := by
      intro i j
      have hi := i.isLt
      have hj := j.isLt
      have hu := u.isLt
      have hgj := hgv j
      have hgl := (g j).isLt
      have hj0l := j0.isLt
      by_cases hiu : i.val < n ∧ i.val ≠ u.val
      · rw [hE0 i j hiu.1]
        by_cases hA : A u j = true
        · rw [hfull j hA]
          have hgj' : g j = j0 := by simp only [g]; rw [if_pos hA]
          apply eval_mono D1 hD1 (oneEach (⟨i.val, hiu.1⟩ : Fin n) (g j)) (src (i, j))
            (by rw [one_len, inp_len])
          · intro w hw
            rw [one_getD, hgj'] at hw
            simp only [src]
            rw [inp_getD, hgj']
            simp at hw ⊢
            omega
          · rw [hD1', hgj']
            exact hfull j0 hj0 _
        · have hgj' : g j = j := by simp only [g]; rw [if_neg hA]
          have hsrc : src (i, j) = oneEach (⟨i.val, hiu.1⟩ : Fin n) j := by
            apply ext_getD _ _ (by rw [inp_len, one_len])
            intro w
            simp only [src]
            rw [inp_getD, one_getD, hgj', Bool.eq_iff_iff]
            simp [hA]
            omega
          rw [hsrc]
          have := hD1' (⟨i.val, hiu.1⟩ : Fin n) j
          rw [hgj'] at this
          exact this
      · rw [hEu i j hiu]
        by_cases hA : A u j = true
        · have hgj' : g j = j0 := by simp only [g]; rw [if_pos hA]
          have hsrc : src (i, j) = oneEach u j0 := by
            apply ext_getD _ _ (by rw [inp_len, one_len])
            intro w
            simp only [src]
            rw [inp_getD, one_getD, hgj', Bool.eq_iff_iff]
            simp [hA]
            omega
          rw [hsrc, hA]
          have := hD1' u j
          rw [hgj', hj0] at this
          exact this
        · have hgj' : g j = j := by simp only [g]; rw [if_neg hA]
          rw [eq_false_of_ne_true hA]
          apply eval_false D1 hD1 _ (oneEach u j) (by rw [inp_len, one_len])
          · intro w hw
            simp only [src] at hw
            rw [inp_getD, hgj'] at hw
            rw [one_getD]
            simp [hA] at hw ⊢
            omega
          · have := hD1' u j
            rw [hgj'] at this
            rw [this]
            exact eq_false_of_ne_true hA
    obtain ⟨D, hD, hDs, hev⟩ := engine3 (n + m) (N + ccs.length) D1 src
      (fun x => run ch (oneEach x.1 x.2)) (fun x => inp_len _ _)
      (fun x => by rw [(hch x).1]; omega) ∅ hD1
      (by
        intro w hw
        have hu := u.isLt
        have hj0l := j0.isLt
        have hfl := finW_lt N 0 (n + t + j0.val) ccs (by omega)
        rcases Nat.lt_or_ge w n with hwn | hwn
        · by_cases hwu : w = u.val
          · right
            refine ⟨finW N 0 (n + t + j0.val) ccs, by omega, fun x => ?_⟩
            rw [hfin]
            simp only [src]
            rw [inp_getD, hwu]
            have := (g x.2).isLt
            cases hA : A u x.2 <;> simp <;> omega
          · right
            refine ⟨w, by omega, fun x => ?_⟩
            rw [(hch x).2.1 w (by omega), one_getD]
            simp only [src]
            rw [inp_getD]
            have := (g x.2).isLt
            have := x.1.isLt
            rw [Bool.eq_iff_iff]
            cases hA : A u x.2 <;> simp <;> omega
        · obtain ⟨c, hc⟩ : ∃ c : Fin m, w = n + c.val :=
            ⟨⟨w - n, by omega⟩, by show w = n + (w - n); omega⟩
          have hgx := fun x : Fin (n + t) × Fin m => hgv x.2
          by_cases hcj : c = j0
          · right
            refine ⟨finW N 0 (n + t + j0.val) ccs, by omega, fun x => ?_⟩
            rw [hfin]
            simp only [src]
            rw [inp_getD, hc, hcj]
            have h3 := hgx x
            have h4 : A u x.2 = false → x.2.val ≠ j0.val := fun h e => by
              rw [Fin.ext e, hj0] at h
              exact absurd h (by decide)
            cases hA : A u x.2 <;> simp [hA] at h3 h4 ⊢ <;> omega
          · by_cases hcc : c ∈ cs
            · left
              refine ⟨false, fun x => ?_⟩
              simp only [src]
              rw [inp_getD, hc]
              obtain ⟨hc1, hc2⟩ := (hmem c).1 hcc
              have h3 := hgx x
              have h4 : A u x.2 = false → x.2.val ≠ c.val := fun h e => by
                rw [Fin.ext e, hc2] at h
                exact absurd h (by decide)
              have h5 : c.val ≠ j0.val := fun e => hc1 (Fin.ext e)
              cases hA : A u x.2 <;> simp [hA] at h3 h4 ⊢ <;> omega
            · right
              have hcu : A u c = false := by
                cases h : A u c
                · rfl
                · exact absurd ((hmem c).2 ⟨hcj, h⟩) hcc
              refine ⟨n + t + c.val, by omega, fun x => ?_⟩
              rw [(hch x).2.1 _ (by omega), one_getD]
              simp only [src]
              rw [inp_getD, hc]
              have h3 := hgx x
              have h4 : A u x.2 = true → x.2.val ≠ c.val := fun h e => by
                rw [Fin.ext e, hcu] at h
                exact absurd h (by decide)
              have h5 : c.val ≠ j0.val := fun e => hcj (Fin.ext e)
              have := x.1.isLt
              rw [Bool.eq_iff_iff]
              cases hA : A u x.2 <;> simp [hA] at h3 h4 ⊢ <;> omega)
      (ne_const _ (Fin.castAdd t u, j0) (Fin.castAdd t u, c')
        (by rw [hval, E_cast]; exact hj0) (by rw [hval, E_cast]; exact hc'))
      (by simp)
    refine ⟨⟨ch ++ D.gates, D.output⟩, mono_pre _ _ _ _ D hD, ?_, fun i j => ?_⟩
    · simp only [Circuit.size, Finset.card_empty, Nat.add_zero] at hDs hD1s hs ⊢
      rw [List.length_append, chainG_len]
      have : ccs.length = cs.length := by simp [ccs]
      omega
    · rw [eval_pre]
      have := hev (i, j)
      simp only at this
      rw [this, hval]
  · simp only [not_exists, Bool.not_eq_true] at hJ
    by_cases ht : ∃ i j, A i j = true
    · obtain ⟨i1, j1, h1⟩ := ht
      let src : Fin (n + t) × Fin m → List Bool := fun x => inp (n + m) (fun w =>
        decide ((w = x.1.val ∧ x.1.val < n ∧ w ≠ u.val) ∨ w = n + x.2.val))
      have hval : ∀ i j, C.eval (src (i, j)) = E n m t A u i j := by
        intro i j
        have hi := i.isLt
        have hj := j.isLt
        have hu := u.isLt
        by_cases hiu : i.val < n ∧ i.val ≠ u.val
        · rw [hE0 i j hiu.1]
          have hsrc : src (i, j) = oneEach (⟨i.val, hiu.1⟩ : Fin n) j := by
            apply ext_getD _ _ (by rw [inp_len, one_len])
            intro w
            simp only [src]
            rw [inp_getD, one_getD, Bool.eq_iff_iff]
            simp
            omega
          rw [hsrc, hr]
        · rw [hEu i j hiu, hJ]
          apply eval_false C hC _ (oneEach u j) (by rw [inp_len, one_len])
          · intro w hw
            simp only [src] at hw
            rw [inp_getD] at hw
            rw [one_getD]
            simp at hw ⊢
            omega
          · rw [hr, hJ]
      obtain ⟨D, hD, hDs, hev⟩ := engine3 (n + m) (n + t + m) C src (fun x => oneEach x.1 x.2)
        (fun x => inp_len _ _) (fun x => one_len _ _) ∅ hC
        (by
          intro w hw
          have hu := u.isLt
          rcases Nat.lt_or_ge w n with hwn | hwn
          · by_cases hwu : w = u.val
            · left
              refine ⟨false, fun x => ?_⟩
              simp only [src]
              rw [inp_getD, hwu]
              simp <;> omega
            · right
              refine ⟨w, by omega, fun x => ?_⟩
              simp only [src]
              rw [inp_getD, one_getD, Bool.eq_iff_iff]
              have := x.1.isLt
              simp <;> omega
          · right
            refine ⟨w + t, by omega, fun x => ?_⟩
            simp only [src]
            rw [inp_getD, one_getD, Bool.eq_iff_iff]
            have := x.1.isLt
            simp <;> omega)
        (ne_const _ (Fin.castAdd t i1, j1) (Fin.castAdd t u, j1)
          (by rw [hval, E_cast]; exact h1)
          (by rw [hval, E_cast]; exact hJ j1))
        (by simp)
      refine ⟨D, hD, by
        simp only [Circuit.size, Finset.card_empty, Nat.add_zero] at hDs hs ⊢; omega,
        fun i j => ?_⟩
      have := hev (i, j)
      simp only at this
      rw [this, hval]
    · simp only [not_exists, Bool.not_eq_true] at ht
      exact rep_empty _ (fun i j => by
        by_cases hi : i.val < n
        · rw [E_lt _ _ _ _ _ _ _ hi]; exact ht _ _
        · rw [E_ge _ _ _ _ _ _ _ hi]; exact ht _ _) b

theorem final (n m : Nat) (A : Fin n → Fin m → Bool) (u : Fin n) (i2 : Fin n) (j2 : Fin m)
    (h2 : A i2 j2 = false) (t s : Nat) :
    RepSizeAtMost (E n m t A u) s ↔ ∃ b : Nat, RepSizeAtMost A b ∧
      b + (if ∃ (j : Fin m) (i : Fin n), A u j = true ∧ A i j = false then t else 0) ≤ s := by
  by_cases hs : ∃ (j : Fin m) (i : Fin n), A u j = true ∧ A i j = false
  · rw [if_pos hs]
    obtain ⟨j0, i0, hu, hi⟩ := hs
    constructor
    · exact low_strict n m t A u i0 j0 hu hi s
    · rintro ⟨b, hb, hle⟩
      obtain ⟨C, hC, hCs, hCr⟩ := up_copies n m t A u b u j0 hu i0 j0 hi hb
      exact ⟨C, hC, by omega, hCr⟩
  · rw [if_neg hs]
    constructor
    · intro h
      exact ⟨s, low_weak n m t A u i2 j2 h2 s h, by omega⟩
    · rintro ⟨b, hb, hle⟩
      have hfull : ∀ j, A u j = true → ∀ i, A i j = true := by
        intro j hj i
        by_contra hc
        exact hs ⟨j, i, hj, by simpa using hc⟩
      obtain ⟨C, hC, hCs, hCr⟩ := up_weak n m t A u hfull i2 j2 h2 b hb
      exact ⟨C, hC, by omega, hCr⟩

end PEqualNP.Outside.L_meta_28073

open PEqualNP.Outside.L_meta_28073 in
theorem PEqualNP.Outside.L_meta_28073 : ∀ (n m : Nat) (A : Fin n → Fin m → Bool) (u : Fin n),
  (∃ i j, A i j = false) →
  ∀ (t s : Nat),
    let expanded := fun (i : Fin (n + t)) (j : Fin m) =>
      if h : i.val < n then A ⟨i.val, h⟩ j else A u j
    let extra := if ∃ (j : Fin m) (i : Fin n), A u j = true ∧ A i j = false
      then t else 0
    PEqualNP.Represents.RepSizeAtMost expanded s ↔
      ∃ b : Nat, PEqualNP.Represents.RepSizeAtMost A b ∧ b + extra ≤ s := by
  intro n m A u hf t s expanded extra
  obtain ⟨i2, j2, h2⟩ := hf
  exact final n m A u i2 j2 h2 t s

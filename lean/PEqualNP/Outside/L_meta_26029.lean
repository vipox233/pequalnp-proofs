import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26029_aux.Small.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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
theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_init _ _ _ _ (h t rfl)

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

theorem sa_val {n : ℕ} (u : Fin (n + 1)) (a : Fin n) :
    ((u.succAbove a : Fin (n + 1)) : ℕ) = if (a : ℕ) < u then (a : ℕ) else a + 1 := by
  by_cases h : (a : ℕ) < u
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; simp [h]

def reads (g : Gate) (w : ℕ) : Prop :=
  (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)

def Good (P : Prop) (g : Gate) : Prop :=
  ((g.op = .not ∧ ∃ a, g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a ≠ b ∧ g.inputs = [a,b])) ∧
    (P → g.op = .and ∨ g.op = .or)

theorem good_shape {P : Prop} {g : Gate} (h : Good P g) :
    (g.op = .not → g.inputs.length = 1) ∧
    (g.op ≠ .not → g.inputs.length = 2 ∧ g.inputs.Nodup) := by
  rcases h.1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,hn,ha⟩
  · simp [ho,ha]
  · rcases ho with ho|ho <;> simp [ho,ha,hn]

theorem good_fan {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) : FanInTwo C := by
  intro g hg
  rcases (h g hg).1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [ho,ha]
  · rcases ho with ho|ho <;> simp [ho,ha]

theorem good_mono {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) :
    P → Monotone2 C := by
  intro p g hg
  exact ⟨by simpa using (h g hg).2 p,(good_fan h g hg).2⟩

theorem good_read {P : Prop} {g : Gate} (h : Good P g) (w : ℕ) : reads g w ↔ w ∈ g.inputs := by
  rcases h.1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [reads,ho,ha,eq_comm]
  · rcases ho with ho|ho <;> simp [reads,ho]

end PEqualNP.Outside.L_meta_26029_aux.Small.Normalize

namespace PEqualNP.Outside.L_meta_26029_aux.Small.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem emit (P : Prop) (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hmon : P → op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, Good P g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
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
  by_cases hn : op = GateOp.not
  · subst op
    rcases rs with _ | ⟨r, rs⟩
    · exact keep (.inl true) (by simp) (by intro y hy; rfl)
    · have hr := hv r (by simp)
      rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y hy; rfl)
      · exact add ⟨.not,[t]⟩ ⟨Or.inl ⟨rfl,t,rfl⟩,hmon⟩ (by simpa using hr t rfl)
          (by intro y hy; rfl)
  have hop' : op = GateOp.and ∨ op = GateOp.or := by tauto
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop' with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop' with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop' with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.and,[t,q]⟩ ⟨Or.inr ⟨Or.inl rfl,t,q,same,rfl⟩,fun _ => Or.inl rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.or,[t,q]⟩ ⟨Or.inr ⟨Or.inr rfl,t,q,same,rfl⟩,fun _ => Or.inr rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
  · simp at hl

theorem engine {X : Type} (P : Prop) (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : FanInTwo C) (hmon : P → Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
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
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, Good P g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
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
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e2', e3, e4⟩ := emit P M hs C.gates[k].op hop (fun p => by simpa using (hmon p _ (List.getElem_mem hk')).1) (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
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
    · exact h1
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm

end PEqualNP.Outside.L_meta_26029_aux.Small.Normalize

namespace PEqualNP.Outside.L_meta_26029_aux.Small.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def collapses {X : Type} (W : X → ℕ → Bool) (top : ℕ) (out : X → Bool) : Prop :=
  (∃ b, ∀ x, out x = b) ∨ ∃ w < top, ∀ x, out x = W x w

theorem read_pair (l : List ℕ) (w : ℕ) (hlen : l.length ≤ 2) (hw : w ∈ l) :
    l = [w] ∨ ∃ v, l = [w,v] ∨ l = [v,w] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d,tail⟩⟩⟩
  · simp at hw
  · have e : w=a := by simpa using hw
    exact Or.inl (by rw [e])
  · rcases List.mem_cons.mp hw with e | h
    · exact Or.inr ⟨b,Or.inl (by rw [e])⟩
    · have e : w=b := by simpa using h
      exact Or.inr ⟨a,Or.inr (by rw [e])⟩
  · simp at hlen

theorem not_value {X : Type} (W : X → ℕ → Bool) (g : Gate) {w : ℕ} {b : Bool}
    (op : g.op = .not) (r : reads g w) (fixed : ∀ x, W x w = b) (x : X) :
    g.op.eval (g.inputs.map (W x)) = !b := by
  have he : g.inputs.head? = some w := by simpa [reads,op] using r
  cases h : g.inputs with
  | nil => simp [h] at he
  | cons a tail =>
    have e : a=w := by simpa [h] using he
    simp [op,h,GateOp.eval,e,fixed]

theorem dominant {X : Type} (W : X → ℕ → Bool) (g : Gate) (w : ℕ)
    (hlen : g.inputs.length ≤ 2) (r : reads g w) (op : g.op = .and ∨ g.op = .not)
    (fixed : ∀ x, W x w = false) :
    ∃ b, ∀ x, g.op.eval (g.inputs.map (W x)) = b := by
  rcases op with h|h
  · have mem : w ∈ g.inputs := by simpa [reads,h] using r
    refine ⟨false,fun x => ?_⟩
    rcases read_pair _ w hlen mem with e | ⟨v,e|e⟩ <;> simp [h,e,GateOp.eval,fixed]
  · exact ⟨true,not_value W g h r fixed⟩

theorem when_read {X : Type} (W : X → ℕ → Bool) (g : Gate) (top w : ℕ) (b : Bool)
    (ok : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (before : ∀ t ∈ g.inputs, t < top) (r : reads g w) (fixed : ∀ x, W x w = b) :
    collapses W top (fun x => g.op.eval (g.inputs.map (W x))) := by
  by_cases hn : g.op = .not
  · exact Or.inl ⟨!b,not_value W g hn r fixed⟩
  have hop : g.op = .and ∨ g.op = .or := by tauto
  have mem : w ∈ g.inputs := by simpa [reads,hn] using r
  rcases read_pair _ w hlen mem with e | ⟨v,e⟩
  · refine Or.inl ⟨b,fun x => ?_⟩
    rcases hop with ho|ho <;> simp [ho,e,GateOp.eval,fixed]
  · have hv : v < top := before v (by rcases e with h|h <;> simp [h])
    rcases hop with h|h
    · cases b
      · refine Or.inl ⟨false,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
    · cases b
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inl ⟨true,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]

def toNat {s : ℕ} (K : Finset (Fin s)) : Finset ℕ := K.map ⟨Fin.val,Fin.val_injective⟩

theorem marked {X : Type} (N : ℕ) (C : Circuit) (src : X → List Bool)
    (hs : ∀ x, (src x).length=N) (u : ℕ) (hu : u<N) (hu0 : ∀ x, (src x).getD u false=false)
    (fan : FanInTwo C) (back : ReadsBack N C) (K : Finset (Fin C.gates.length))
    (mark : ∀ j ∈ K, reads (C.gates.get j) u ∨ ∃ i : Fin C.gates.length, i<j ∧
      reads (C.gates.get i) u ∧ ((C.gates.get i).op=.and ∨ (C.gates.get i).op=.not) ∧
      reads (C.gates.get j) (N+i.val)) :
    ∀ k ∈ toNat K, k < C.gates.length ∧
      collapses (fun x w => (run C.gates (src x)).getD w false) (N+k)
        (fun x => (run C.gates (src x)).getD (N+k) false) := by
  let W := fun (x : X) (w : ℕ) => (run C.gates (src x)).getD w false
  have raw (x : X) : W x u = false :=
    (run_input _ _ _ (by rw [hs]; exact hu)).trans (hu0 x)
  have atGate (j : Fin C.gates.length) : gateAt C j.val=C.gates.get j :=
    List.getD_eq_getElem _ _ j.isLt
  have ev (j : Fin C.gates.length) (x : X) :
      W x (N+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (W x)) := by
    simpa only [W,atGate j] using gv N C back (src x) (hs x) j.val j.isLt
  intro k hk
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hk
  refine ⟨j.isLt,?_⟩
  change collapses W (N+j.val) (fun x => W x (N+j.val))
  have same := funext (ev j)
  rw [same]
  have ok := fan (C.gates.get j) (List.get_mem _ _)
  have before (t : ℕ) (ht : t∈(C.gates.get j).inputs) : t<N+j.val :=
    back j.val j.isLt t (by rwa [atGate])
  have folded (w : ℕ) (b : Bool) (r : reads (C.gates.get j) w) (h : ∀ x, W x w=b) :=
    when_read W _ (N+j.val) w b (by simpa using ok.1) ok.2 before r h
  rcases mark j hj with direct | ⟨i,_,ri,oi,rj⟩
  · exact folded u false direct raw
  · have fi := fan (C.gates.get i) (List.get_mem _ _)
    obtain ⟨b,hb⟩ := dominant W _ u fi.2 ri oi raw
    exact folded (N+i.val) b rj (fun x => (ev i x).trans (hb x))

end PEqualNP.Outside.L_meta_26029_aux.Small.Normalize

namespace PEqualNP.Outside.L_meta_26029_aux.Small.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def oldFace {n m : ℕ} (u : Fin (n+1)) (x : List Bool) : Option (Fin n × Fin m) → List Bool
  | none => x
  | some p => oneEach (u.succAbove p.1) p.2

def newFace {n m : ℕ} (u : Fin (n+1)) (x : List Bool) : Option (Fin n × Fin m) → List Bool
  | none => List.ofFn (fun j : Fin (n+m) => x.getD (if j.val<u.val then j.val else j.val+1) false)
  | some p => oneEach p.1 p.2

theorem old_len {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.length=n+1+m)
    (p : Option (Fin n × Fin m)) : (oldFace u x p).length=n+1+m := by
  cases p <;> simp [oldFace,oneEach_length,hx]

theorem new_len {n m : ℕ} (u : Fin (n+1)) (x : List Bool)
    (p : Option (Fin n × Fin m)) : (newFace u x p).length=n+m := by
  cases p <;> simp [newFace,oneEach_length]

theorem off_face {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.getD u.val false=false)
    (p : Option (Fin n × Fin m)) : (oldFace u x p).getD u.val false=false := by
  cases p with
  | none => exact hx
  | some p =>
    simp only [oldFace,oneEach_getD,decide_eq_false_iff_not,sa_val]
    have := u.isLt
    split_ifs <;> omega

theorem face_inputs {n m : ℕ} (u : Fin (n+1)) (x : List Bool) (hx : x.getD u.val false=false)
    (w : ℕ) (hw : w<n+1+m) :
    (∃ b, ∀ p : Option (Fin n × Fin m), (oldFace u x p).getD w false = b) ∨
    ∃ t, t<n+m ∧ ∀ p : Option (Fin n × Fin m), (oldFace u x p).getD w false =
      (newFace u x p).getD t false := by
  have hu := u.isLt
  rcases lt_trichotomy w u.val with h | h | h
  · have ht : w<n+m := by omega
    refine Or.inr ⟨w,ht,?_⟩
    intro p
    cases p with
    | none => simp [oldFace,newFace,ht,h]
    | some p =>
      have := p.1.isLt
      have := p.2.isLt
      simp only [oldFace,newFace,oneEach_getD,decide_eq_decide,sa_val]
      split_ifs <;> omega
  · subst w
    exact Or.inl ⟨false,off_face u x hx⟩
  · have ht : w-1<n+m := by omega
    have hn : ¬ w-1<u.val := by omega
    have eq : w-1+1=w := by omega
    refine Or.inr ⟨w-1,ht,?_⟩
    intro p
    cases p with
    | none => simp [oldFace,newFace,ht,hn,eq]
    | some p =>
      have := p.1.isLt
      have := p.2.isLt
      simp only [oldFace,newFace,oneEach_getD,decide_eq_decide,sa_val]
      split_ifs <;> omega

end PEqualNP.Outside.L_meta_26029_aux.Small.Normalize

namespace PEqualNP.Outside.L_meta_26029_aux.Small.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem blank_dead_signed (P : Prop) (N : ℕ) (C : Circuit)
    (hc : FanInTwo C) (hm : P → Monotone2 C) (hb : ReadsBack N C)
    (j : ℕ) (hj : j < C.gates.length)
    (hdead : ∀ k < C.gates.length, N + j ∉ (gateAt C k).inputs) (ho : C.output ≠ N + j) :
    let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
    FanInTwo E ∧ (P → Monotone2 E) ∧ ReadsBack N E ∧ E.size = C.size ∧
      (∀ x : List Bool, x.length = N → E.eval x = C.eval x) ∧
      (∀ x : List Bool, x.length = N → (run E.gates x).getD (N + j) false = false) := by
  let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
  have hlen : E.gates.length = C.gates.length := by simp [E]
  have hg : ∀ k, gateAt E k = if k = j then ⟨GateOp.or, []⟩ else gateAt C k := by
    intro k
    simp only [gateAt, E, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hk : k = j
    · subst hk; simp [hj]
    · simp [hk, Ne.symm hk]
  have hc' : FanInTwo E := by
    intro g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hc g h
    · subst h; simp
  have hm' : P → Monotone2 E := by
    intro hP g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hm hP g h
    · subst h; simp
  have hb' : ReadsBack N E := by
    intro k hk i hi
    rw [hg] at hi
    split_ifs at hi with h
    · simp at hi
    · exact hb k (by rw [hlen] at hk; exact hk) i hi
  have agree : ∀ x : List Bool, x.length = N → ∀ i, i ≠ N + j →
      (run E.gates x).getD i false = (run C.gates x).getD i false := by
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
      rw [hik, gv N E hb' x hx _ (by rw [hlen]; exact hk), gv N C hb x hx _ hk, hg,
        if_neg (by omega)]
      congr 1
      refine List.map_congr_left fun i' hi' => ih i' ?_ ?_
      · have := hb _ hk i' hi'; omega
      · rintro rfl; exact hdead _ hk hi'
  refine ⟨hc', hm', hb', hlen, fun x hx => agree x hx _ ho, fun x hx => ?_⟩
  change (run E.gates x).getD (N + j) false = false
  rw [gv N E hb' x hx j (by rw [hlen]; exact hj), hg, if_pos rfl]
  simp [GateOp.eval]

theorem finish_live {X : Type} (P : Prop) (M : ℕ) (y : X → List Bool)
    (hy : ∀ x, (y x).length = M) (f : X → Bool)
    (hnc : ¬ ∃ b : Bool, ∀ x, f x = b) (C : Circuit)
    (hg : ∀ g ∈ C.gates, Good P g) (hb : ReadsBack M C) (hf : ∀ x, C.eval (y x) = f x) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size ≤ C.size ∧
      (∀ x, D.eval (y x) = f x) ∧
      ∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧
      D.size ≤ k ∧ ∀ x, D.eval (y x) = f x := ⟨C.size, C, hg, hb, le_rfl, hf⟩
  obtain ⟨D, hgood, hback, hsize, hval⟩ := Nat.find_spec hex
  have hmin0 : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hg, hb, le_rfl, hf⟩
  refine ⟨D, hgood, hback, hsize.trans hmin0, hval, ?_⟩
  intro i hout
  by_contra hn
  have dead : ∀ k < D.gates.length, M + i.val ∉ (gateAt D k).inputs := by
    intro k hk hpin
    have hh := hback k hk _ hpin
    have later : i < (⟨k, hk⟩ : Fin D.gates.length) := by
      change i.val < k
      omega
    have eqg : D.gates.get ⟨k, hk⟩ = gateAt D k := (List.getD_eq_getElem _ _ hk).symm
    have hgk : Good P (D.gates.get ⟨k, hk⟩) := hgood _ (List.getElem_mem hk)
    have hread : reads (D.gates.get ⟨k, hk⟩) (M + i.val) ↔
        M + i.val ∈ (D.gates.get ⟨k, hk⟩).inputs := by
      apply good_read
      exact hgk
    exact hn ⟨⟨k, hk⟩, later, hread.2 (by rwa [eqg])⟩
  let E : Circuit := ⟨D.gates.set i.val ⟨GateOp.or, []⟩, D.output⟩
  have hdf : FanInTwo D := by apply good_fan; exact hgood
  have hdm : P → Monotone2 D := by
    intro hP
    apply good_mono <;> assumption
  obtain ⟨hef, hem, _, hes, heq, hzero⟩ :=
    blank_dead_signed P M D hdf hdm hback i.val i.isLt dead hout.symm
  have heval (x : X) : E.eval (y x) = f x := (heq _ (hy x)).trans (hval x)
  have hmarked : ∀ j ∈ ({i.val} : Finset ℕ), j < E.gates.length ∧
      ((∃ b, ∀ x, (run E.gates (y x)).getD (M + j) false = b) ∨
       ∃ w < M + j, ∀ x, (run E.gates (y x)).getD (M + j) false =
         (run E.gates (y x)).getD w false) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst j
    exact ⟨by simpa [E] using i.isLt, Or.inl ⟨false, fun x => hzero _ (hy x)⟩⟩
  obtain ⟨J, hJg, hJb, hJs, hJv⟩ := engine P M M E y y hy hy {i.val} hef hem
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩)
    (fun ⟨b, h⟩ => hnc ⟨b, fun x => (heval x).symm.trans (h x)⟩) hmarked
  have lower : Nat.find hex ≤ J.size :=
    Nat.find_min' hex ⟨J, hJg, hJb, le_rfl, fun x => (hJv x).trans (heval x)⟩
  rw [Finset.card_singleton] at hJs
  change E.size = D.size at hes
  omega

end PEqualNP.Outside.L_meta_26029_aux.Small.Normalize

namespace PEqualNP.Outside.L_meta_26029_aux.Small.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
noncomputable def listed (p : GateOp → Nat) (gs : List Gate) : Nat := (gs.map (fun g=>p g.op)).sum
noncomputable def remaining (p : GateOp → Nat) (C : Circuit) (F : Finset Nat) (k : Nat) : Nat :=
  ∑ j∈Finset.range k, if j∈F then 0 else p (gateAt C j).op

theorem full_price (p : GateOp → Nat) (C : Circuit) : remaining p C ∅ C.size=listed p C.gates := by
  have appendOne (l : List Gate) (g : Gate) : listed p (l++[g])=listed p l+p g.op := by
    simp [listed]
  have below (k : Nat) (h : k≤C.gates.length) : remaining p C ∅ k=listed p (C.gates.take k) := by
    induction k with
    | zero => simp [remaining,listed]
    | succ k ih =>
      have low : k<C.gates.length:=by omega
      rw [List.take_succ_eq_append_getElem low]
      change (∑j∈Finset.range (k+1),if j∈(∅ : Finset Nat) then 0 else p (gateAt C j).op)=_
      rw [Finset.sum_range_succ]
      change remaining p C ∅ k+_=_
      rw [ih (by omega)]
      rw [show gateAt C k=C.gates[k] from List.getD_eq_getElem _ _ low,appendOne] <;> simp
  simpa [Circuit.size] using below C.gates.length le_rfl

theorem blank_price (p : GateOp → Nat) (C : Circuit) (i : Fin C.gates.length) :
    let E : Circuit:=⟨C.gates.set i.val ⟨GateOp.or,[]⟩,C.output⟩
    remaining p E {i.val} E.size≤listed p C.gates := by
  intro E
  rw [←full_price p C]
  have sizes : E.size=C.size := by simp [E,Circuit.size]
  unfold remaining; rw [sizes]; apply Finset.sum_le_sum
  intro j hj
  have low : j<C.gates.length:=Finset.mem_range.mp hj
  have newer : j<E.gates.length := by simpa [E] using low
  by_cases same : j=i.val
  · simp [same]
  · have ne : i.val≠j:=Ne.symm same
    simp [E,gateAt,List.getD_eq_getElem _ _ low,List.getD_eq_getElem _ _ newer,low,same,ne,List.getElem_set]

theorem emission_price (p : GateOp → Nat) (e : List Gate) (op : GateOp) (len : e.length≤1) (same : ∀g∈e,g.op=op) :
    listed p e≤p op := by
  cases e with
  | nil => simp [listed]
  | cons g tail =>
    have h:=same g List.mem_cons_self
    have empty : tail=[] := List.length_eq_zero_iff.mp (by change tail.length+1≤1 at len;omega)
    subst tail; simp [listed,h]

theorem emitWeighted (P : Prop) (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hmon : P → op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, g.op=op → Good P g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g∈e,g.op=op) ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g same h1 h1' h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using same, by simpa using h1, by simpa using h1', ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  by_cases hn : op = GateOp.not
  · subst op
    rcases rs with _ | ⟨r, rs⟩
    · exact keep (.inl true) (by simp) (by intro y hy; rfl)
    · have hr := hv r (by simp)
      rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y hy; rfl)
      · exact add ⟨.not,[t]⟩ rfl ⟨Or.inl ⟨rfl,t,rfl⟩,hmon⟩ (by simpa using hr t rfl)
          (by intro y hy; rfl)
  have hop' : op = GateOp.and ∨ op = GateOp.or := by tauto
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop' with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop' with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop' with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.and,[t,q]⟩ rfl ⟨Or.inr ⟨Or.inl rfl,t,q,same,rfl⟩,fun _ => Or.inl rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.or,[t,q]⟩ rfl ⟨Or.inr ⟨Or.inr rfl,t,q,same,rfl⟩,fun _ => Or.inr rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
  · simp at hl

theorem engineWeighted {X : Type} (P : Prop) (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : FanInTwo C) (hmon : P → Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧ (∀ p, listed p D.gates≤remaining p C F C.size) ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ p, listed p hs≤remaining p C F (k)) ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, by simp, by simp [listed,remaining], ?_, ?_⟩
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
      obtain ⟨hs, m, h1, h5, h2, spent, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, Good P g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ p, listed p e≤(if k∈F then 0 else p (gateAt C k).op)) →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ p, listed p hs≤remaining p C F (k + 1)) ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he he' hr hlen charge hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · intro p
          change listed p (hs++e)≤remaining p C F (k+1)
          have lhs : listed p (hs++e)=listed p hs+listed p e := by simp [listed]
          rw [lhs,remaining,Finset.sum_range_succ]
          exact Nat.add_le_add (spent p) (charge p)
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
        · exact fin (.inl b) [] (by simp) (by simp) (by simp) (by simp [hkF]) (by simp [listed,hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (by simp [listed,hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, sameOps, e2, e2', e3, e4⟩ := emitWeighted P M hs C.gates[k].op hop (fun p => by simpa using (hmon p _ (List.getElem_mem hk')).1) (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e2' e3 (by simp [hkF]; exact e1) (by intro p; rw [if_neg hkF,show gateAt C k=C.gates[k] from List.getD_eq_getElem _ _ hk']; exact emission_price p e C.gates[k].op e1 sameOps) (fun x => ?_)
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
  obtain ⟨hs, m, h1, h5, h2, spent, h3, h4⟩ := key C.gates.length le_rfl
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
  · refine ⟨⟨hs, t⟩, ?_, ?_, h2, spent, fun x => ?_⟩
    · exact h1
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm

theorem finishWeighted {X : Type} (P : Prop) (M : ℕ) (y : X → List Bool)
    (hy : ∀ x, (y x).length = M) (f : X → Bool)
    (hnc : ¬ ∃ b : Bool, ∀ x, f x = b) (C : Circuit)
    (hg : ∀ g ∈ C.gates, Good P g) (hb : ReadsBack M C) (hf : ∀ x, C.eval (y x) = f x) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size ≤ C.size ∧ (∀ p, listed p D.gates≤listed p C.gates) ∧
      (∀ x, D.eval (y x) = f x) ∧
      ∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧
      D.size ≤ k ∧ (∀ p, listed p D.gates≤listed p C.gates) ∧ ∀ x, D.eval (y x) = f x := ⟨C.size, C, hg, hb, le_rfl, fun _=>le_rfl, hf⟩
  obtain ⟨D, hgood, hback, hsize, hprice, hval⟩ := Nat.find_spec hex
  have hmin0 : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hg, hb, le_rfl, fun _=>le_rfl, hf⟩
  refine ⟨D, hgood, hback, hsize.trans hmin0, hprice, hval, ?_⟩
  intro i hout
  by_contra hn
  have dead : ∀ k < D.gates.length, M + i.val ∉ (gateAt D k).inputs := by
    intro k hk hpin
    have hh := hback k hk _ hpin
    have later : i < (⟨k, hk⟩ : Fin D.gates.length) := by
      change i.val < k
      omega
    have eqg : D.gates.get ⟨k, hk⟩ = gateAt D k := (List.getD_eq_getElem _ _ hk).symm
    have hgk : Good P (D.gates.get ⟨k, hk⟩) := hgood _ (List.getElem_mem hk)
    have hread : reads (D.gates.get ⟨k, hk⟩) (M + i.val) ↔
        M + i.val ∈ (D.gates.get ⟨k, hk⟩).inputs := by
      apply good_read
      exact hgk
    exact hn ⟨⟨k, hk⟩, later, hread.2 (by rwa [eqg])⟩
  let E : Circuit := ⟨D.gates.set i.val ⟨GateOp.or, []⟩, D.output⟩
  have hdf : FanInTwo D := by apply good_fan; exact hgood
  have hdm : P → Monotone2 D := by
    intro hP
    apply good_mono <;> assumption
  obtain ⟨hef, hem, _, hes, heq, hzero⟩ :=
    blank_dead_signed P M D hdf hdm hback i.val i.isLt dead hout.symm
  have heval (x : X) : E.eval (y x) = f x := (heq _ (hy x)).trans (hval x)
  have hmarked : ∀ j ∈ ({i.val} : Finset ℕ), j < E.gates.length ∧
      ((∃ b, ∀ x, (run E.gates (y x)).getD (M + j) false = b) ∨
       ∃ w < M + j, ∀ x, (run E.gates (y x)).getD (M + j) false =
         (run E.gates (y x)).getD w false) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst j
    exact ⟨by simpa [E] using i.isLt, Or.inl ⟨false, fun x => hzero _ (hy x)⟩⟩
  obtain ⟨J, hJg, hJb, hJs, hpriceJ, hJv⟩ := engineWeighted P M M E y y hy hy {i.val} hef hem
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩)
    (fun ⟨b, h⟩ => hnc ⟨b, fun x => (heval x).symm.trans (h x)⟩) hmarked
  have lower : Nat.find hex ≤ J.size :=
    Nat.find_min' hex ⟨J, hJg, hJb, le_rfl, fun p=>(hpriceJ p).trans ((blank_price p D i).trans (hprice p)), fun x => (hJv x).trans (heval x)⟩
  rw [Finset.card_singleton] at hJs
  change E.size = D.size at hes
  omega

end PEqualNP.Outside.L_meta_26029_aux.Small.Normalize

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

def FixedAt {X : Type} (W : X → Nat → Bool) (i : Nat) := ∃ b, ∀ x, W x i = b
noncomputable def inputsFixed {X : Type} (W : X → Nat → Bool) (g : Gate) :=
  g.inputs.toFinset.filter (FixedAt W)
noncomputable def eliminated {X : Type} (N : Nat) (C : Circuit) (W : X → Nat → Bool) :=
  (Finset.range C.size).filter (fun j=> FixedAt W (N+j) ∨ ∃ i∈(gateAt C j).inputs, FixedAt W i)
noncomputable def bin (op : GateOp) : Nat := if op=.not then 0 else 1
noncomputable def inv (op : GateOp) : Nat := if op=.not then 1 else 0

theorem countLocal {X : Type} (W : X → Nat → Bool) (g : Gate) (o : Nat)
    (shape : Good False g) (evaluate : ∀x, W x o=g.op.eval (g.inputs.map (W x))) :
    (inputsFixed W g).card ≤ (if FixedAt W o then 1 else 0)+
      (if FixedAt W o ∨ ∃ i∈g.inputs, FixedAt W i then bin g.op else 0) := by
  classical
  have singleton (i : Nat) : (Finset.filter (FixedAt W) {i}) = (if FixedAt W i then {i} else ∅) := by
    by_cases h : FixedAt W i <;> ext v <;> simp [h] <;> aesop
  rcases shape.1 with ⟨op,a,inputs⟩|⟨op,a,b,ab,inputs⟩
  · by_cases ha : FixedAt W a
    · obtain ⟨v,hv⟩:=ha
      have fa : FixedAt W a:=⟨v,hv⟩
      have out : FixedAt W o:=⟨!v,fun x=>by simp [evaluate x,op,inputs,GateOp.eval,hv]⟩
      simp [inputsFixed,inputs,singleton,fa,out,bin,op]
    · simp [inputsFixed,inputs,singleton,ha]
  · have budget : bin g.op=1 := by rcases op with e|e <;> simp [bin,e]
    by_cases fa : FixedAt W a <;> by_cases fb : FixedAt W b
    · obtain ⟨u,hu⟩:=fa
      obtain ⟨v,hv⟩:=fb
      have ca : FixedAt W a:=⟨u,hu⟩
      have cb : FixedAt W b:=⟨v,hv⟩
      have out : FixedAt W o:=⟨g.op.eval [u,v],fun x=>by simp [evaluate x,inputs,hu,hv]⟩
      simp [inputsFixed,inputs,ca,cb,out,budget,ab,Finset.filter_insert,singleton]
    · by_cases c : FixedAt W o <;> simp [inputsFixed,inputs,fa,fb,budget,Finset.filter_insert,singleton,c]
    · by_cases c : FixedAt W o <;> simp [inputsFixed,inputs,fa,fb,budget,Finset.filter_insert,singleton,c]
    · simp [inputsFixed,inputs,fa,fb,Finset.filter_insert,singleton]

theorem cancelConstants {X : Type} (N : Nat) (C : Circuit) (W : X→Nat→Bool)
    (shape : ∀g∈C.gates, Good False g)
    (evaluate : ∀j<C.size,∀x,W x (N+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map (W x)))
    (A : Finset Nat) (raw : ∀i∈A,i<N)
    (seen : ∀i∈A,FixedAt W i ∧ ∃j<C.size,i∈(gateAt C j).inputs)
    (live : ∀j<C.size, FixedAt W (N+j) → ∃k<C.size,N+j∈(gateAt C k).inputs) :
    A.card + remaining bin C (eliminated N C W) C.size ≤ listed bin C.gates := by
  classical
  let I:=Finset.range C.size
  let T:=I.filter (fun j=>FixedAt W (N+j))
  let B:=T.image (fun j=>N+j)
  let F:=eliminated N C W
  let pieces:=fun j=>inputsFixed W (gateAt C j)
  have source {w} (h : FixedAt W w) (use : ∃j<C.size,w∈(gateAt C j).inputs) : w∈I.biUnion pieces := by
    obtain ⟨j,less,pin⟩:=use
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr less,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr pin,h⟩⟩
  have sub : A∪B⊆I.biUnion pieces := by
    intro w hw
    rcases Finset.mem_union.mp hw with ha|hb
    · exact source (seen _ ha).1 (seen _ ha).2
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hb
      obtain ⟨idx,fixed⟩:=Finset.mem_filter.mp hj
      exact source fixed (live j (Finset.mem_range.mp idx) fixed)
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi h
    obtain ⟨j,_,wire⟩:=Finset.mem_image.mp h
    have below:=raw i hi;change N+j=i at wire;omega
  have first:=(Finset.card_le_card sub).trans (Finset.card_biUnion_le)
  have inj : Function.Injective (fun j : Nat=>N+j):=fun _ _ e=>Nat.add_left_cancel e
  rw [Finset.card_union_of_disjoint dis,show B.card=T.card from Finset.card_image_of_injective _ inj] at first
  let dropped:=fun j=>if j∈F then bin (gateAt C j).op else 0
  have charge (j) (hj : j∈I) : (pieces j).card ≤ (if FixedAt W (N+j) then 1 else 0)+dropped j := by
    have idx:=Finset.mem_range.mp hj
    have eqg : gateAt C j=C.gates[j] := List.getD_eq_getElem _ _ idx
    have good : Good False (gateAt C j):=eqg ▸ shape _ (List.getElem_mem idx)
    simpa [pieces,dropped,F,eliminated,idx] using countLocal W (gateAt C j) (N+j) good (evaluate j idx)
  have total:=Finset.sum_le_sum charge
  rw [Finset.sum_add_distrib,←show T.card=(∑j∈I,if FixedAt W (N+j) then 1 else 0) from Finset.card_filter _ _] at total
  have both : (∑j∈I,dropped j)+remaining bin C F C.size=listed bin C.gates := by
    rw [←full_price bin C]
    unfold remaining;rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _;by_cases mem : j∈F <;> simp [dropped,mem]
  change A.card+remaining bin C F C.size≤_
  omega
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

theorem readFn {n : Nat} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false=x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]; simp

theorem rawReader {n : Nat} (C : Circuit) (back : ReadsBack n C) (s : Fin n)
    (out : C.output ≠ s.val) (x : Fin n→Bool)
    (diff : C.eval (List.ofFn (Function.update x s false)) ≠ C.eval (List.ofFn (Function.update x s true))) :
    ∃j<C.size,s.val∈(gateAt C j).inputs := by
  classical
  by_contra! absent
  let a:=List.ofFn (Function.update x s false)
  let b:=List.ofFn (Function.update x s true)
  have la : a.length=n:=List.length_ofFn
  have lb : b.length=n:=List.length_ofFn
  have same (w : Nat) (off : w≠s.val) : (run C.gates a).getD w false=(run C.gates b).getD w false := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases raw : w<n
      · let i : Fin n:=⟨w,raw⟩
        have ne : i≠s:=fun he=>off (congrArg Fin.val he)
        rw [run_input _ _ _ (by rwa [la]),run_input _ _ _ (by rwa [lb])]
        change (List.ofFn _).getD i.val false=(List.ofFn _).getD i.val false
        rw [readFn,readFn];simp [Function.update_of_ne ne]
      by_cases far : n+C.size≤w
      · rw [past C.gates a _ (by rwa [la]),past C.gates b _ (by rwa [lb])]
      let j:=w-n
      have add : n+j=w:=Nat.add_sub_of_le (by omega)
      have idx : j<C.size:=by dsimp [j];omega
      rw [←add,gv n C back a la j idx,gv n C back b lb j idx]
      congr 1
      apply List.map_congr_left
      intro v pin
      exact ih v (by have h:=back j idx v pin;omega) (fun h=>absent j idx (h ▸ pin))
  exact diff (same C.output out)

theorem initial {n : Nat} (C : Circuit) (fan : FanInTwo C)
    (f : (Fin n→Bool)→Bool) (rep : ∀x, C.eval (List.ofFn x)=f x)
    (nc : ¬∃b,∀x,f x=b) :
    ∃D : Circuit,(∀g∈D.gates,Good False g) ∧ ReadsBack n D ∧
      (∀p,listed p D.gates≤listed p C.gates) ∧ (∀x,D.eval (List.ofFn x)=f x) ∧
      ∀ i : Fin D.gates.length,n+i.val≠D.output → ∃ j : Fin D.gates.length,i<j ∧ reads (D.gates.get j) (n+i.val) := by
  obtain ⟨E,good,back,_,prices,value⟩:=engineWeighted False n n C (fun x : Fin n→Bool=>List.ofFn x) (fun x=>List.ofFn x)
    (fun _=>List.length_ofFn) (fun _=>List.length_ofFn) ∅ fan False.elim
    (fun w h=>Or.inr ⟨w,h,fun _=>rfl⟩) (fun ⟨b,v⟩=>nc ⟨b,fun x=>(rep x).symm.trans (v x)⟩) (by simp)
  obtain ⟨D,g,b,_,costs,eq,live⟩:=finishWeighted False n (fun x=>List.ofFn x) (fun _=>List.length_ofFn) f nc E
    good back (fun x=>(value x).trans (rep x))
  exact ⟨D,g,b,fun p=>(costs p).trans ((prices p).trans_eq (full_price p C)),eq,live⟩

theorem costs (C : Circuit) : listed inv C.gates=(C.gates.filter (fun g=>decide (g.op=GateOp.not))).length ∧
    listed bin C.gates=C.size-(C.gates.filter (fun g=>decide (g.op=GateOp.not))).length := by
  have h (gs : List Gate) : listed inv gs=(gs.filter (fun g=>decide (g.op=GateOp.not))).length ∧
      listed inv gs+listed bin gs=gs.length := by
    induction gs with
    | nil => simp [listed]
    | cons g gs ih =>
      by_cases yes : g.op=GateOp.not <;> simp [listed,inv,bin,yes] at ih ⊢ <;> omega
  obtain ⟨e,s⟩:=h C.gates
  exact ⟨e,by change _=C.gates.length-_;omega⟩
noncomputable def plug {n k : Nat} (wire : Fin k→Fin n) (fixed : Fin n→Bool) (y : Fin k→Bool) (i : Fin n) :=
  if i∈Finset.univ.image wire then decide (∃j,wire j=i ∧ y j=true) else fixed i

theorem onWire {n k : Nat} (wire : Fin k→Fin n) (fixed : Fin n→Bool) (inj : Function.Injective wire)
    (y : Fin k→Bool) (j : Fin k) : plug wire fixed y (wire j)=y j := by
  have inside : wire j∈Finset.univ.image wire:=Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have eq : (∃z,wire z=wire j ∧ y z=true) ↔ y j=true := by
    constructor
    · rintro ⟨z,h,v⟩;exact inj h ▸ v
    · exact fun v=>⟨j,rfl,v⟩
  simp [plug,inside,eq]

theorem restrict {n k : Nat} (C : Circuit) (fan : FanInTwo C) (wire : Fin k→Fin n) (fixed : Fin n→Bool)
    (inj : Function.Injective wire) (f : (Fin n→Bool)→Bool) (rep : ∀x,C.eval (List.ofFn x)=f x)
    (outside : ∀i, i∉Finset.univ.image wire → ∃x,f (Function.update x i false)≠f (Function.update x i true))
    (varies : ∃a b,f (plug wire fixed a)≠f (plug wire fixed b)) :
    ∃D : Circuit,FanInTwo D ∧ listed bin D.gates+
             (n-k) ≤ listed bin C.gates ∧ listed inv D.gates≤listed inv C.gates ∧ ∀y,D.eval (List.ofFn y)=f (plug wire fixed y) := by
  classical
  obtain ⟨a,b,diff⟩:=varies
  have nc : ¬∃v,∀x,f x=v := fun ⟨v,h⟩=>diff ((h _).trans (h _).symm)
  obtain ⟨E,good,back,prices,ef,live⟩:=initial C fan f rep nc
  let X:=Fin k→Bool
  let src : X→List Bool:=fun y=>List.ofFn (plug wire fixed y)
  let W:=fun (y : X) w=>(run E.gates (src y)).getD w false
  have val (j : Nat) (idx : j<E.size) (y : X) : W y (n+j)=(gateAt E j).op.eval ((gateAt E j).inputs.map (W y)):=
    gv n E back (src y) List.length_ofFn j idx
  have out (y : X) : W y E.output=f (plug wire fixed y):=ef _
  have varying : ¬FixedAt W E.output := fun ⟨v,c⟩=>diff ((out a).symm.trans ((c a).trans ((c b).symm.trans (out b))))
  let image:=Finset.univ.image wire
  let ess:=(Finset.univ : Finset (Fin n)).filter (fun i=>∃x,f (Function.update x i false)≠f (Function.update x i true))
  let miss:=ess\image
  let A:=miss.image Fin.val
  have low (w) (hw : w∈A) : w<n := by obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hw;exact i.isLt
  have gateGood j (h : j<E.size) : Good False (gateAt E j) := by
    rw [show gateAt E j=E.gates[j] from List.getD_eq_getElem _ _ h];exact good _ (List.getElem_mem h)
  have rawValue (i : Fin n) (y : X) : W y i.val=plug wire fixed y i := by
    unfold W; rw [run_input _ _ _ (by simpa [src] using i.isLt)];exact readFn _ _
  have seen (w) (hw : w∈A) : FixedAt W w ∧ ∃j<E.size,w∈(gateAt E j).inputs := by
    obtain ⟨i,mem,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨active,off⟩:=Finset.mem_sdiff.mp mem
    have c : FixedAt W i.val:=⟨fixed i,fun y=>by rw [rawValue];exact if_neg off⟩
    have ne : E.output≠i.val:=fun eq=>varying (eq ▸ c)
    obtain ⟨x,hx⟩:=(Finset.mem_filter.mp active).2
    exact ⟨c,rawReader E back i ne x (by simpa only [ef] using hx)⟩
  have used (j) (idx : j<E.size) (fix : FixedAt W (n+j)) : ∃l<E.size,n+j∈(gateAt E l).inputs := by
    have ne : n+j≠E.output:=fun eq=>varying (eq ▸ fix)
    obtain ⟨l,_,read⟩:=live ⟨j,idx⟩ ne
    have e : E.gates.get l=gateAt E l.val:=(List.getD_eq_getElem _ _ l.isLt).symm
    rw [e] at read
    exact ⟨l.val,l.isLt,(good_read (gateGood _ l.isLt) _).mp read⟩
  let F:=eliminated n E W
  have charged:=cancelConstants n E W good val A low seen used
  have mark (j) (hj : j∈F) : j<E.gates.length ∧ collapses W (n+j) (fun x=>W x (n+j)) := by
    obtain ⟨idx,why⟩:=Finset.mem_filter.mp hj
    have h:=Finset.mem_range.mp idx
    refine ⟨h,?_⟩
    rcases why with c|⟨w,mem,v,z⟩
    · exact Or.inl c
    · let g:=gateAt E j
      have shape:=gateGood j h
      have fanE:=good_fan good
      have belongs : g∈E.gates:=by rw [show g=E.gates[j] from List.getD_eq_getElem _ _ h];exact List.getElem_mem _
      have ops : g.op=.and ∨ g.op=.or ∨ g.op=.not := by rcases shape.1 with ⟨op,_⟩|⟨op,_⟩ <;> tauto
      have fold:=when_read W g (n+j) w v ops (fanE g belongs).2 (back j h) ((good_read shape w).mpr mem) z
      simpa only [val j h] using fold
  have inputs (w : Nat) (h : w<n) : (∃v,∀y,(src y).getD w false=v) ∨ ∃t,t<k ∧ ∀y,(src y).getD w false=(List.ofFn y).getD t false := by
    let i : Fin n:=⟨w,h⟩
    by_cases mem : i∈image
    · obtain ⟨j,_,e⟩:=Finset.mem_image.mp mem
      exact Or.inr ⟨j.val,j.isLt,fun y=>(readFn _ i).trans (e ▸ (onWire wire fixed inj y j).trans (readFn y j).symm)⟩
    · exact Or.inl ⟨fixed i,fun y=>(readFn _ i).trans (if_neg mem)⟩
  obtain ⟨D,dgood,_,_,dcost,deval⟩:=engineWeighted False n k E src (fun y=>List.ofFn y)
    (fun _=>List.length_ofFn) (fun _=>List.length_ofFn) F (good_fan good) False.elim inputs
    (fun ⟨v,h⟩=>varying ⟨v,h⟩) mark
  have cov : ess⊆miss∪image := by
    intro i hi;by_cases mem : i∈image
    · exact Finset.mem_union_right _ mem
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,mem⟩)
  have many:=(Finset.card_le_card cov).trans (Finset.card_union_le _ _)
  have im : image.card=k:=by simp [image,Finset.card_image_of_injective _ inj]
  have am : A.card=miss.card:=Finset.card_image_of_injective _ Fin.val_injective
  have saved:=dcost bin
  change A.card+remaining bin E F E.size≤listed bin E.gates at charged
  have ib := prices bin
  have inversion : remaining inv E F E.size≤listed inv E.gates := by
    rw [←full_price inv E];unfold remaining;apply Finset.sum_le_sum
    intro j _;by_cases mem : j∈F <;> simp [mem]
  have offeq : miss = Finset.univ \ image := by
    ext z
    simp only [miss, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨And.right, fun h => ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,outside z h⟩,h⟩⟩
  have missing : miss.card = n-k := by simp [offeq, Finset.card_sdiff, im]
  exact ⟨D,good_fan dgood,by omega,
    (dcost inv).trans (inversion.trans (prices inv)),fun y=>(deval y).trans (ef _)⟩
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (Normalize.run gs x).getD i false = true → (Normalize.run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [Normalize.run_snoc, Normalize.run_snoc, getD_snoc, getD_snoc, Normalize.run_length, Normalize.run_length,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega
end PEqualNP.Outside.L_meta_26029_aux.Small
namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical

def left {n : Nat} (m : Nat) (i : Fin n) : Fin (n+m) := i.castAdd m
def right (n : Nat) {m : Nat} (j : Fin m) : Fin (n+m) := j.natAdd n
def two {n : Nat} (i j w : Fin n) := decide (w=i ∨ w=j)
def one {n : Nat} (j w : Fin n) := decide (w=j)
def fn {n : Nat} (C : Circuit) (x : Fin n → Bool) := C.eval (List.ofFn x)

theorem atPair {n m : Nat} {A : Fin n→Fin m→Bool} {C : Circuit} (rep : Represents A C) (i : Fin n) (j : Fin m) :
    fn C (two (left m i) (right n j))=A i j := by
  rw [←rep i j,oneEach_eq]
  congr 1
  funext w
  simp [two,left,right,Fin.ext_iff]

theorem monoFn {n : Nat} {C : Circuit} (hc : Monotone2 C) {x y : Fin n→Bool}
    (h : ∀i,x i=true → y i=true) : fn C x=true → fn C y=true := by
  apply mono C.gates (fun g hg=>(hc g hg).1) _ _ (by simp) _ C.output
  intro w
  by_cases hw : w<n
  · let i : Fin n:=⟨w,hw⟩
    exact (by simpa only [readFn] using h i : (List.ofFn x).getD i.val false=true → (List.ofFn y).getD i.val false=true)
  · simp [List.getD_eq_getElem?_getD,hw]

theorem pivot {n : Nat} {C : Circuit} (hc : Monotone2 C) (i j i' : Fin n) (ne : i≠j)
    (yes : fn C (two i j)=true) (no : fn C (two i' j)=false) :
    ∃x,fn C (Function.update x i false)≠fn C (Function.update x i true) := by
  refine ⟨one j,?_⟩
  have off : Function.update (one j) i false=one j := by
    funext w;by_cases e : w=i
    · subst w;simp [one,ne]
    · simp [Function.update_of_ne e]
  have on : Function.update (one j) i true=two i j := by
    funext w;by_cases e : w=i
    · subst w;simp [two]
    · simp [Function.update_of_ne e,two,one,e]
  rw [off,on,yes]
  intro h
  have v:=monoFn hc (x:=one j) (y:=two i' j) (by intro w; simp [one,two];tauto) h
  rw [no] at v
  contradiction

def wire {n m a b : Nat} (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m) (w : Fin (a+b)) : Fin (n+m) :=
  finSumFinEquiv (Sum.map x y (finSumFinEquiv.symm w))

theorem wireInj {n m a b : Nat} (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m) : Function.Injective (wire x y) :=
  finSumFinEquiv.injective.comp ((Sum.map_injective.mpr ⟨x.injective,y.injective⟩).comp finSumFinEquiv.symm.injective)

@[simp] theorem wireLeft {n m a b : Nat} (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m) (i : Fin a) :
    wire x y (left b i)=left m (x i) := by
  change finSumFinEquiv (Sum.map x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))))=_
  rw [Equiv.symm_apply_apply];rfl

@[simp] theorem wireRight {n m a b : Nat} (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m) (j : Fin b) :
    wire x y (right a j)=right n (y j) := by
  change finSumFinEquiv (Sum.map x y (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))))=_
  rw [Equiv.symm_apply_apply];rfl

theorem plugTwo {n k : Nat} (g : Fin k→Fin n) (inj : Function.Injective g) (i j : Fin k) :
    plug g (fun _=>false) (two i j) = two (g i) (g j) := by
  funext w
  by_cases h : w∈Finset.univ.image g
  · obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp h
    rw [onWire _ _ inj]
    simp [two,inj.eq_iff]
  · have off (q : Fin k) : w≠g q:=fun e=>h (e ▸ Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩)
    simp [plug,h,two,off]

end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
theorem positiveRestriction : ∀ (n m a b : Nat) (A : Fin n → Fin m → Bool)
    (x : Fin a ↪ Fin n) (y : Fin b ↪ Fin m),
  (∃ i k j l, A (x i) (y j) ≠ A (x k) (y l)) →
  (∀ i, (∀ h, x h ≠ i) → ∃ k j, A i j = true ∧ A k j = false) →
  (∀ j, (∀ h, y h ≠ j) → ∃ l i, A i j = true ∧ A i l = false) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.Represents.Represents (fun i j => A (x i) (y j)) D ∧
      D.size + (n-a) + (m-b) ≤ C.size := by
  classical
  intro n m a b A x y varied rows cols C hc rep
  let g:=wire x y
  have inj : Function.Injective g:=wireInj x y
  have pair (i : Fin a) (j : Fin b) :
      fn C (plug g (fun _=>false) (two (left b i) (right a j))) = A (x i) (y j) := by
    rw [plugTwo _ inj];simpa [g] using atPair rep (x i) (y j)
  obtain ⟨i,k,j,l,hv⟩:=varied
  have extv : ∃p q, fn C (plug g (fun _=>false) p)≠fn C (plug g (fun _=>false) q) :=
    ⟨two (left b i) (right a j),two (left b k) (right a l),by rwa [pair,pair]⟩
  have miss (w : Fin (n+m)) (off : w∉Finset.univ.image g) :
      ∃z, fn C (Function.update z w false)≠fn C (Function.update z w true) := by
    have dif (q : Fin (a+b)) : g q≠w:=fun e=>off (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,e⟩)
    induction w using Fin.addCases with
    | left u =>
      obtain ⟨v,c,hy,hn⟩:=rows u (by intro q e; apply dif (left b q);change wire x y (left b q)=_;rw [wireLeft,e];rfl)
      apply pivot hc (left m u) (right n c) (left m v)
      · intro e;have v:=congrArg Fin.val e;change u.val=n+c.val at v;omega
      · exact (atPair rep _ _).trans hy
      · exact (atPair rep _ _).trans hn
    | right v =>
      obtain ⟨u,r,hy,hn⟩:=cols v (by intro q e; apply dif (right a q);change wire x y (right a q)=_;rw [wireRight,e];rfl)
      have comm {N : Nat} (z w : Fin N) : two z w=two w z:=by funext i;simp [two,or_comm]
      apply pivot hc (right n v) (left m r) (right n u)
      · intro e;have h:=congrArg Fin.val e;change n+v.val=r.val at h;omega
      · rw [comm];exact (atPair rep _ _).trans hy
      · rw [comm];exact (atPair rep _ _).trans hn
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro q h
    obtain ⟨op,len⟩:=hc q h
    refine ⟨?_,len⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    tauto
  obtain ⟨D,df,bs,ins,vals⟩:=restrict C fan g (fun _=>false) inj (fn C) (fun _=>rfl) miss extv
  have noC : ∀q∈C.gates,q.op≠PEqualNP.CircuitLowerBounds.GateOp.not := by
    intro q h;have ops:=(hc q h).1;simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops;rcases ops with e|e <;> simp [e]
  have cz : (C.gates.filter (fun q=>decide (q.op=PEqualNP.CircuitLowerBounds.GateOp.not))).length=0 := by
    rw [List.length_eq_zero_iff,List.filter_eq_nil_iff];simpa using noC
  rw [(costs C).1,cz,(costs D).1] at ins
  have dz := Nat.eq_zero_of_le_zero ins
  have noD : ∀q∈D.gates,q.op≠PEqualNP.CircuitLowerBounds.GateOp.not := by
    rw [List.length_eq_zero_iff,List.filter_eq_nil_iff] at dz;simpa using dz
  have md : PEqualNP.MetaComplexity.Monotone2 D := by
    intro q h;rcases df q h with ⟨op,len⟩
    refine ⟨?_,len⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    have hn:=noD q h
    tauto
  have hi:=Fintype.card_le_of_injective x x.injective
  have hj:=Fintype.card_le_of_injective y y.injective
  simp only [Fintype.card_fin] at hi hj
  rw [(costs D).2,(costs C).2,cz,dz] at bs
  refine ⟨D,md,?_,by omega⟩
  intro u v
  have e := atPair (A:=fun u v=>D.eval (PEqualNP.Represents.oneEach u v)) (C:=D) (fun _ _=>rfl) u v
  exact e.symm.trans ((vals (two (left b u) (right a v))).trans (pair u v))

end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical
theorem signedRestriction {n k : Nat} (C : Circuit) (fan : FanInTwo C) (wire : Fin k→Fin n) (fixed : Fin n→Bool)
    (inj : Function.Injective wire) (f : (Fin n→Bool)→Bool) (rep : ∀x,C.eval (List.ofFn x)=f x)
    (varies : ∃a b,f (plug wire fixed a)≠f (plug wire fixed b)) :
    ∃D : Circuit,FanInTwo D ∧ listed bin D.gates+
      ((Finset.univ : Finset (Fin n)).filter (fun i=>∃x,f (Function.update x i false)≠f (Function.update x i true))).card≤
      listed bin C.gates+k ∧ listed inv D.gates≤listed inv C.gates ∧ ∀y,D.eval (List.ofFn y)=f (plug wire fixed y) := by
  classical
  obtain ⟨a,b,diff⟩:=varies
  have nc : ¬∃v,∀x,f x=v := fun ⟨v,h⟩=>diff ((h _).trans (h _).symm)
  obtain ⟨E,good,back,prices,ef,live⟩:=initial C fan f rep nc
  let X:=Fin k→Bool
  let src : X→List Bool:=fun y=>List.ofFn (plug wire fixed y)
  let W:=fun (y : X) w=>(run E.gates (src y)).getD w false
  have val (j : Nat) (idx : j<E.size) (y : X) : W y (n+j)=(gateAt E j).op.eval ((gateAt E j).inputs.map (W y)):=
    gv n E back (src y) List.length_ofFn j idx
  have out (y : X) : W y E.output=f (plug wire fixed y):=ef _
  have varying : ¬FixedAt W E.output := fun ⟨v,c⟩=>diff ((out a).symm.trans ((c a).trans ((c b).symm.trans (out b))))
  let image:=Finset.univ.image wire
  let ess:=(Finset.univ : Finset (Fin n)).filter (fun i=>∃x,f (Function.update x i false)≠f (Function.update x i true))
  let miss:=ess\image
  let A:=miss.image Fin.val
  have low (w) (hw : w∈A) : w<n := by obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hw;exact i.isLt
  have gateGood j (h : j<E.size) : Good False (gateAt E j) := by
    rw [show gateAt E j=E.gates[j] from List.getD_eq_getElem _ _ h];exact good _ (List.getElem_mem h)
  have rawValue (i : Fin n) (y : X) : W y i.val=plug wire fixed y i := by
    unfold W; rw [run_input _ _ _ (by simpa [src] using i.isLt)];exact readFn _ _
  have seen (w) (hw : w∈A) : FixedAt W w ∧ ∃j<E.size,w∈(gateAt E j).inputs := by
    obtain ⟨i,mem,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨active,off⟩:=Finset.mem_sdiff.mp mem
    have c : FixedAt W i.val:=⟨fixed i,fun y=>by rw [rawValue];exact if_neg off⟩
    have ne : E.output≠i.val:=fun eq=>varying (eq ▸ c)
    obtain ⟨x,hx⟩:=(Finset.mem_filter.mp active).2
    exact ⟨c,rawReader E back i ne x (by simpa only [ef] using hx)⟩
  have used (j) (idx : j<E.size) (fix : FixedAt W (n+j)) : ∃l<E.size,n+j∈(gateAt E l).inputs := by
    have ne : n+j≠E.output:=fun eq=>varying (eq ▸ fix)
    obtain ⟨l,_,read⟩:=live ⟨j,idx⟩ ne
    have e : E.gates.get l=gateAt E l.val:=(List.getD_eq_getElem _ _ l.isLt).symm
    rw [e] at read
    exact ⟨l.val,l.isLt,(good_read (gateGood _ l.isLt) _).mp read⟩
  let F:=eliminated n E W
  have charged:=cancelConstants n E W good val A low seen used
  have mark (j) (hj : j∈F) : j<E.gates.length ∧ collapses W (n+j) (fun x=>W x (n+j)) := by
    obtain ⟨idx,why⟩:=Finset.mem_filter.mp hj
    have h:=Finset.mem_range.mp idx
    refine ⟨h,?_⟩
    rcases why with c|⟨w,mem,v,z⟩
    · exact Or.inl c
    · let g:=gateAt E j
      have shape:=gateGood j h
      have fanE:=good_fan good
      have belongs : g∈E.gates:=by rw [show g=E.gates[j] from List.getD_eq_getElem _ _ h];exact List.getElem_mem _
      have ops : g.op=.and ∨ g.op=.or ∨ g.op=.not := by rcases shape.1 with ⟨op,_⟩|⟨op,_⟩ <;> tauto
      have fold:=when_read W g (n+j) w v ops (fanE g belongs).2 (back j h) ((good_read shape w).mpr mem) z
      simpa only [val j h] using fold
  have inputs (w : Nat) (h : w<n) : (∃v,∀y,(src y).getD w false=v) ∨ ∃t,t<k ∧ ∀y,(src y).getD w false=(List.ofFn y).getD t false := by
    let i : Fin n:=⟨w,h⟩
    by_cases mem : i∈image
    · obtain ⟨j,_,e⟩:=Finset.mem_image.mp mem
      exact Or.inr ⟨j.val,j.isLt,fun y=>(readFn _ i).trans (e ▸ (onWire wire fixed inj y j).trans (readFn y j).symm)⟩
    · exact Or.inl ⟨fixed i,fun y=>(readFn _ i).trans (if_neg mem)⟩
  obtain ⟨D,dgood,_,_,dcost,deval⟩:=engineWeighted False n k E src (fun y=>List.ofFn y)
    (fun _=>List.length_ofFn) (fun _=>List.length_ofFn) F (good_fan good) False.elim inputs
    (fun ⟨v,h⟩=>varying ⟨v,h⟩) mark
  have cov : ess⊆miss∪image := by
    intro i hi;by_cases mem : i∈image
    · exact Finset.mem_union_right _ mem
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,mem⟩)
  have many:=(Finset.card_le_card cov).trans (Finset.card_union_le _ _)
  have im : image.card=k:=by simp [image,Finset.card_image_of_injective _ inj]
  have am : A.card=miss.card:=Finset.card_image_of_injective _ Fin.val_injective
  have saved:=dcost bin
  change A.card+remaining bin E F E.size≤listed bin E.gates at charged
  have ib := prices bin
  have inversion : remaining inv E F E.size≤listed inv E.gates := by
    rw [←full_price inv E];unfold remaining;apply Finset.sum_le_sum
    intro j _;by_cases mem : j∈F <;> simp [mem]
  exact ⟨D,good_fan dgood,by change listed bin D.gates+ess.card≤_;omega,
    (dcost inv).trans (inversion.trans (prices inv)),fun y=>(deval y).trans (ef _)⟩
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical
namespace Check

def options {w : Nat} (signed : Bool) (B : List (BitVec w)) : List (BitVec w) :=
  ((B.flatMap fun a=>B.flatMap fun b=>[a &&& b,a ||| b]) ++ (if signed then B.map (fun a=>~~~a) else [])).eraseDups

def can {w : Nat} (signed : Bool) (T : BitVec w) : Nat → List (BitVec w) → Bool
  | 0,B => B.contains T
  | s+1,B => B.contains T || (options signed B).any fun v=>if v∈B then can signed T s B else can signed T s (v::B)

def wop {w : Nat} (op : GateOp) (xs : List (BitVec w)) : BitVec w :=
  match op,xs with
  | .and,[] => BitVec.allOnes w
  | .and,[v] => v
  | .and,v::h::_ => v &&& h
  | .or,[] => 0
  | .or,[v] => v
  | .or,v::h::_ => v ||| h
  | .not,[] => BitVec.allOnes w
  | .not,v::_ => ~~~v
  | _,_ => 0

theorem optionAnd {w : Nat} (s : Bool) (B : List (BitVec w)) {a b : BitVec w} (ha : a∈B) (hb : b∈B) :
    a &&& b ∈ options s B ∧ a ||| b ∈ options s B := by
  simp only [options,List.mem_eraseDups,List.mem_append]
  constructor <;> left <;> apply List.mem_flatMap.mpr <;> refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩ <;> simp

theorem optionNot {w : Nat} (B : List (BitVec w)) {a : BitVec w} (ha : a∈B) :
    ~~~a ∈ options true B := by simp [options,ha]

theorem choice {w : Nat} (s : Bool) (B : List (BitVec w)) (zero : 0∈B) (ones : BitVec.allOnes w∈B)
    (g : Gate) (ops : g.op=.and ∨ g.op=.or ∨ (s=true ∧ g.op=.not)) (ar : g.inputs.length≤2)
    (W : List (BitVec w)) (covered : ∀v∈W,v∈B) :
    wop g.op (g.inputs.map fun i=>W.getD i 0) ∈ options s B := by
  have read (i : Nat) : W.getD i 0∈B := by
    by_cases h : i<W.length
    · rw [List.getD_eq_getElem _ _ h];exact covered _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)];exact zero
  have refl (v : BitVec w) (m : v∈B) : v∈options s B := by simpa using (optionAnd s B m m).1
  rcases g with ⟨op,ls⟩
  change op=.and ∨ op=.or ∨ (s=true ∧ op=.not) at ops
  change ls.length≤2 at ar
  rcases ls with _|⟨a,_|⟨b,_|⟨c,rest⟩⟩⟩
  · rcases ops with rfl|rfl|⟨rfl,rfl⟩ <;> first | exact refl _ zero | exact refl _ ones
  · rcases ops with rfl|rfl|⟨rfl,rfl⟩ <;> first | exact refl _ (read a) | exact optionNot _ (read a)
  · rcases ops with rfl|rfl|⟨rfl,rfl⟩
    · exact (optionAnd _ _ (read a) (read b)).1
    · exact (optionAnd _ _ (read a) (read b)).2
    · exact optionNot _ (read a)
  · simp at ar

def sim {w : Nat} : List Gate → List (BitVec w) → List (BitVec w)
  | [],W=>W
  | g::gs,W=>sim gs (W++[wop g.op (g.inputs.map fun i=>W.getD i 0)])

theorem sound {w : Nat} (s : Bool) (T : BitVec w) (gs : List Gate)
    (op : ∀g∈gs,g.op=.and ∨ g.op=.or ∨ s=true ∧ g.op=.not) (fan : ∀g∈gs,g.inputs.length≤2)
    (W B : List (BitVec w)) (zero : 0∈B) (ones : BitVec.allOnes w∈B)
    (covered : ∀v∈W,v∈B) (k : Nat) (budget : gs.length≤k) (hit : T∈sim gs W) : can s T k B=true := by
  induction k generalizing gs W B with
  | zero =>
    have nil : gs=[]:=List.length_eq_zero_iff.mp (by omega)
    subst gs
    simpa [can] using covered T hit
  | succ k ih =>
    rw [can,Bool.or_eq_true]
    rcases gs with _|⟨g,gs⟩
    · left; simpa using covered T hit
    right
    let v:=wop g.op (g.inputs.map fun i=>W.getD i 0)
    have member:=choice s B zero ones g (op _ (by simp)) (fan _ (by simp)) W covered
    apply List.any_eq_true.mpr
    refine ⟨v,member,?_⟩
    split_ifs with h
    · exact ih gs (fun q hq=>op q (List.mem_cons_of_mem _ hq)) (fun q hq=>fan q (List.mem_cons_of_mem _ hq)) (W++[v]) B zero ones (fun q hq=> (List.mem_append.mp hq).elim (covered q) (fun e=>(List.mem_singleton.mp e) ▸ h)) (by simpa using budget) hit
    · apply ih gs (fun q hq=>op q (List.mem_cons_of_mem _ hq)) (fun q hq=>fan q (List.mem_cons_of_mem _ hq)) (W++[v]) (v::B) (List.mem_cons_of_mem _ zero) (List.mem_cons_of_mem _ ones)
      · intro q hq
        rcases List.mem_append.mp hq with hq|eq
        · exact List.mem_cons_of_mem _ (covered q hq)
        · simp [List.mem_singleton.mp eq]
      · simpa using budget
      · exact hit

def bit {w : Nat} (r : Nat) (x : BitVec w) := x.getLsbD r

theorem bitWop {w : Nat} (r : Nat) (hr : r<w) (g : Gate)
    (ops : g.op=.and ∨ g.op=.or ∨ g.op=.not) (ar : g.inputs.length≤2) (W : List (BitVec w)) :
    bit r (wop g.op (g.inputs.map fun i=>W.getD i 0)) =
    g.op.eval (g.inputs.map fun i=>bit r (W.getD i 0)) := by
  rcases g with ⟨op,ls⟩
  change op=.and ∨ op=.or ∨ op=.not at ops
  change ls.length≤2 at ar
  rcases ls with _|⟨a,_|⟨b,_|⟨c,rest⟩⟩⟩
  · rcases ops with rfl|rfl|rfl <;> simp [wop,bit,GateOp.eval,hr]
  · rcases ops with rfl|rfl|rfl <;> simp [wop,bit,GateOp.eval,hr]
  · rcases ops with rfl|rfl|rfl <;> simp [wop,bit,GateOp.eval,hr]
  · simp at ar

theorem runBit {w : Nat} (r : Nat) (hr : r<w) (gs : List Gate)
    (fan : ∀g∈gs,g.inputs.length≤2) (op : ∀g∈gs,g.op=.and ∨ g.op=.or ∨ g.op=.not)
    (W : List (BitVec w)) : (sim gs W).map (bit r) = Normalize.run gs (W.map (bit r)) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    rw [sim,ih (fun q h=>fan q (List.mem_cons_of_mem _ h)) (fun q h=>op q (List.mem_cons_of_mem _ h))]
    simp only [List.map_append,List.map_cons,List.map_nil,bitWop r hr g (op _ (by simp)) (fan _ (by simp))]
    unfold Normalize.run
    simp only [List.foldl_cons]
    congr 2
    congr 1
    congr 1
    apply List.map_congr_left
    intro i _
    by_cases h : i<W.length
    · rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (by simpa using h)];simp
    · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)];simp [bit]

theorem mux6 : can true (6 : BitVec 4) 3 [0,15,12,5,10] = false := by decide +kernel
theorem mux9 : can true (9 : BitVec 4) 3 [0,15,12,5,10] = false := by decide +kernel

theorem bitGet {w : Nat} (r : Nat) (W : List (BitVec w)) (j : Nat) :
    bit r (W.getD j 0) = (W.map (bit r)).getD j false := by
  by_cases h : j<W.length
  · rw [List.getD_eq_getElem _ _ h,List.getD_eq_getElem _ _ (by simpa using h)];simp
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)];simp [bit]

theorem readout {w : Nat} (s : Bool) (C : Circuit) (W B : List (BitVec w)) (k : Nat)
    (op : ∀g∈C.gates,g.op=.and ∨ g.op=.or ∨ s=true ∧ g.op=.not) (fan : ∀g∈C.gates,g.inputs.length≤2)
    (cov : ∀v∈W,v∈B) (h0 : 0∈B) (h1 : BitVec.allOnes w∈B) (budget : C.size≤k)
    (T : BitVec w) (nt : T≠0) (target : ∀r : Fin w,C.eval (W.map (bit r.val))=bit r.val T) :
    can s T k B=true := by
  let L := sim C.gates W
  have o : L.getD C.output 0 = T := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    change bit r (L.getD C.output 0)=bit r T
    rw [bitGet]
    dsimp only [L]
    rw [runBit r hr C.gates fan (fun g h=>by rcases op g h with e|e|⟨_,e⟩ <;> tauto)]
    exact target ⟨r,hr⟩
  have hi : C.output<L.length := by
    by_contra! h
    rw [List.getD_eq_default _ _ h] at o
    exact nt o.symm
  rw [List.getD_eq_getElem _ _ hi] at o
  exact sound s T C.gates op fan W B h0 h1 cov k budget (o ▸ List.getElem_mem hi)

def data3 (r : Fin 4) (i : Fin 3) : Bool := bit r.val (([12,5,10] : List (BitVec 4)).getD i.val 0)
theorem fourForMux (C : Circuit) (fan : FanInTwo C) (T : BitVec 4) (hT : T=6 ∨ T=9)
    (evals : ∀r : Fin 4, C.eval (List.ofFn (data3 r))=bit r.val T) : 4 ≤ C.size := by
  by_contra! bad
  have eq (r : Fin 4) : ([12,5,10] : List (BitVec 4)).map (bit r.val)=List.ofFn (data3 r) := by
    fin_cases r <;> decide +kernel
  have hit:= readout true C [12,5,10] [0,15,12,5,10] 3
    (fun g hg=>by simpa using (fan g hg).1) (fun g hg=>(fan g hg).2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega) T
    (by rcases hT with rfl|rfl <;> decide) (fun r=>(eq r ▸ evals r))
  rcases hT with rfl|rfl <;> first | rw [mux6] at hit;contradiction | rw [mux9] at hit;contradiction

end Check
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical

def active {N : Nat} (C : Circuit) (i : Fin N) := ∃x,fn C (Function.update x i false)≠fn C (Function.update x i true)
noncomputable def E (N : Nat) (C : Circuit) := (Finset.univ : Finset (Fin N)).filter (active C)

theorem ignoreRaw {N : Nat} {C : Circuit} (i j : Fin N) (ne : i≠j) (off : ¬active C i) :
    fn C (one j)=fn C (two i j) := by
  have eq := not_exists.mp off (one j)
  rw [not_not] at eq
  have ff : Function.update (one j) i false=one j := by
    funext w;by_cases h:w=i
    · subst w;simp [one,ne]
    · simp [Function.update_of_ne h]
  have tt : Function.update (one j) i true=two i j := by
    funext w;by_cases h:w=i
    · subst w;simp [two]
    · simp [Function.update_of_ne h,one,two,h]
  rwa [ff,tt] at eq

theorem plugOne {n k : Nat} (g : Fin k→Fin n) (inj : Function.Injective g) (i : Fin k) :
    plug g (fun _=>false) (one i)=one (g i) := by
  have h {N : Nat} (z : Fin N) : one z=two z z := by funext w;simp [one,two]
  rw [h,plugTwo _ inj,←h]

theorem charge {N k : Nat} (C : Circuit) (fan : FanInTwo C) (g : Fin k→Fin N) (inj : Function.Injective g)
    (fixed : Fin N→Bool) (vary : ∃x y,fn C (plug g fixed x)≠fn C (plug g fixed y)) :
    ∃D : Circuit, FanInTwo D ∧ D.size+(E N C).card≤C.size+k ∧ ∀y,fn D y=fn C (plug g fixed y) := by
  obtain ⟨D,h,bs,inv,rep⟩:=signedRestriction C fan g fixed inj (fn C) (fun _=>rfl) vary
  rw [(costs C).2,(costs D).2] at bs
  rw [(costs C).1,(costs D).1] at inv
  have ee : (E N C).card=((Finset.univ : Finset (Fin N)).filter (fun i=>∃x,fn C (Function.update x i false)≠fn C (Function.update x i true))).card := by
    congr 1;ext i;simp [E,active]
  rw [ee]
  have clen : (C.gates.filter (fun g=>decide (g.op=GateOp.not))).length≤C.size := List.length_filter_le _ _
  have dlen : (D.gates.filter (fun g=>decide (g.op=GateOp.not))).length≤D.size := List.length_filter_le _ _
  exact ⟨D,h,by omega,rep⟩

theorem priceRow {N n m : Nat} (R : Fin n→Fin N) (K : Fin m→Fin N) (ki : Function.Injective K)
    (sep : ∀r c,R r≠K c) (A : Fin n→Fin m→Bool) (C : Circuit) (fan : FanInTwo C)
    (rep : ∀i j, fn C (two (R i) (K j))=A i j) (p q : Fin n) (j l : Fin m) (off : ¬active C (R p))
    (p0 : A p j=false) (p1 : A p l=true) (q1 : A q j=true) (q0 : A q l=false) :
    (E N C).card+1≤C.size := by
  classical
  have jl : j≠l := by rintro rfl;rw [p0] at p1;contradiction
  let g : Fin 3→Fin N:=![R q,K j,K l]
  have inj : Function.Injective g := by
    intro a b eq
    fin_cases a <;> fin_cases b <;> simp [g] at eq ⊢ <;> first
      | exact (sep _ _ eq).elim
      | exact (sep _ _ eq.symm).elim
      | exact (jl (ki eq)).elim
      | exact (jl (ki eq.symm)).elim
  have ev (r : Fin 4) : fn C (plug g (fun _=>false) (Check.data3 r))=Check.bit r.val (6 : BitVec 4) := by
    fin_cases r
    · change fn C (plug g _ (Check.data3 0))=false
      rw [show Check.data3 0=one 1 from by decide +kernel,plugOne _ inj]
      exact (ignoreRaw _ _ (sep p j) off).trans ((rep p j).trans p0)
    · change fn C (plug g _ (Check.data3 1))=true
      rw [show Check.data3 1=one 2 from by decide +kernel,plugOne _ inj]
      exact (ignoreRaw _ _ (sep p l) off).trans ((rep p l).trans p1)
    · change fn C (plug g _ (Check.data3 2))=true
      rw [show Check.data3 2=two 0 1 from by decide +kernel,plugTwo _ inj]
      exact (rep q j).trans q1
    · change fn C (plug g _ (Check.data3 3))=false
      rw [show Check.data3 3=two 0 2 from by decide +kernel,plugTwo _ inj]
      exact (rep q l).trans q0
  have varies : ∃x y,fn C (plug g (fun _=>false) x)≠fn C (plug g (fun _=>false) y) := by
    refine ⟨Check.data3 0,Check.data3 1,?_⟩;rw [ev,ev];decide
  obtain ⟨D,df,cost,repD⟩:=charge C fan g inj _ varies
  have b:=Check.fourForMux D df _ (Or.inl rfl) (fun r=>(repD _).trans (ev r))
  omega

theorem essentialsCost {N : Nat} (hn : 0<N) (C : Circuit) (fan : FanInTwo C)
    (all : ∀i : Fin N,active C i) : N≤C.size+1 := by
  let i : Fin N:=⟨0,hn⟩
  obtain ⟨x,h⟩:=all i
  let g : Fin 1→Fin N:=fun _=>i
  have inj : Function.Injective g:=fun _ _ _=>Subsingleton.elim _ _
  have plugVal (v : Bool) : plug g x (fun _=>v)=Function.update x i v := by
    funext w
    by_cases e:w=i
    · subst w;rw [Function.update_self];exact onWire g x inj (fun _=>v) 0
    · have off : w∉Finset.univ.image g:=by simpa [g] using e
      unfold plug
      rw [if_neg off,Function.update_of_ne e]
  have varies : ∃a b,fn C (plug g x a) ≠ fn C (plug g x b) := ⟨fun _=>false,fun _=>true,by rwa [plugVal,plugVal]⟩
  obtain ⟨D,_,cost,_⟩:=charge C fan g inj x varies
  have c : (E N C).card=N:=by simp [E,all]
  rw [c] at cost;omega

end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical

noncomputable def fam {n : Nat} (i j : Fin n) : Bool :=
  (if i.val = 1 ∨ j.val = 1 then decide (i.val = 3 ∨ j.val = 3) else decide (i.val = 2 ∨ j.val = 2)) || decide (4 ≤ i.val ∧ i = j)
theorem symmetric {n : Nat} (i j : Fin n) : fam i j=fam j i := by
  by_cases e:i=j
  · subst j;rfl
  · simp [fam,e,Ne.symm e,or_comm]
def small {n : Nat} (hn : 4 ≤ n) (k : Fin 4) : Fin n := ⟨k.val,by omega⟩

theorem patterns {n : Nat} (hn : 4 ≤ n) (i : Fin n) : ∃j c d, fam i c=false ∧ fam i d=true ∧ fam j c=true ∧ fam j d=false := by
  let z:=small hn 0
  let o:=small hn 1
  let t:=small hn 2
  let h:=small hn 3
  rcases Nat.lt_or_ge i.val 4 with lo|hi
  · interval_cases iv : i.val
    · exact ⟨o,h,t,by simp [fam,z,o,t,h,small,Fin.ext_iff,iv]⟩
    · exact ⟨z,t,h,by simp [fam,z,o,t,h,small,Fin.ext_iff,iv]⟩
    · exact ⟨h,o,z,by simp [fam,z,o,t,h,small,Fin.ext_iff,iv]⟩
    · exact ⟨t,z,o,by simp [fam,z,o,t,h,small,Fin.ext_iff,iv]⟩
  · exact ⟨o,h,t,by simp [fam,o,h,t,small,Fin.ext_iff,show i.val≠1 by omega,show i.val≠2 by omega,show i.val≠3 by omega,hi]⟩

theorem distinctRows {n : Nat} (hn : 4 ≤ n) : Function.Injective (@fam n) := by
  intro i j e
  apply Fin.ext
  have val (k : Fin n) := congrFun e k
  by_cases a : i.val<4 <;> by_cases b : j.val<4
  · interval_cases iv:i.val <;> interval_cases jv:j.val <;> first
      | omega
      | solve | have h:=val (small hn 0);simp [fam,iv,jv,small,Fin.ext_iff] at h
      | solve | have h:=val (small hn 1);simp [fam,iv,jv,small,Fin.ext_iff] at h
      | solve | have h:=val (small hn 2);simp [fam,iv,jv,small,Fin.ext_iff] at h
      | solve | have h:=val (small hn 3);simp [fam,iv,jv,small,Fin.ext_iff] at h
  · have B : j.val≥4:=by omega
    have h:=val j
    interval_cases iv:i.val <;> simp [fam,iv,B,show j.val≠1 by omega,show j.val≠2 by omega,show j.val≠3 by omega] at h
    all_goals first | omega | have h:=val (small hn 0);simp [fam,iv,small,Fin.ext_iff,show j.val≠1 by omega,show j.val≠2 by omega,show j.val≠3 by omega,show j.val≠0 by omega] at h
  · have B : i.val≥4:=by omega
    have h:=val i
    interval_cases jv:j.val <;> simp [fam,jv,B,show i.val≠1 by omega,show i.val≠2 by omega,show i.val≠3 by omega] at h
    all_goals first | omega | have h:=val (small hn 0);simp [fam,jv,small,Fin.ext_iff,show i.val≠1 by omega,show i.val≠2 by omega,show i.val≠3 by omega,show i.val≠0 by omega] at h
  · by_contra neq
    have B : i.val≥4:=by omega
    have h:=val i
    simp [fam,B,Fin.ext_iff,ne_comm.mp neq,show i.val≠1 by omega,show i.val≠2 by omega,show j.val≠1 by omega,show j.val≠2 by omega] at h

theorem atMostOne {N n m : Nat} (R : Fin n→Fin N) (K : Fin m→Fin N)
    (sep : ∀r c,R r≠K c) (A : Fin n→Fin m→Bool) (C : Circuit)
    (rep : ∀i j, fn C (two (R i) (K j))=A i j) (distinct : Function.Injective A) :
    (Finset.univ.filter fun i=>¬active C (R i)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply distinct;funext c
  have a:=(Finset.mem_filter.mp hi).2
  have b:=(Finset.mem_filter.mp hj).2
  exact (rep i c).symm.trans ((ignoreRaw _ _ (sep i c) a).symm.trans ((ignoreRaw _ _ (sep j c) b).trans (rep j c)))

theorem signedLower {n : Nat} (hn : 4 ≤ n) (C : Circuit) (fan : FanInTwo C) (rep : Represents (@fam n) C) :
    2*n-1≤C.size := by
  classical
  let R : Fin n→Fin (n+n):=left n
  let K : Fin n→Fin (n+n):=right n
  have sep (i j : Fin n) : R i≠K j := by intro e;have q:=congrArg Fin.val e;change i.val=n+j.val at q;omega
  have repR (i j : Fin n) : fn C (two (R i) (K j)) = fam i j := atPair rep i j
  have repK (i j : Fin n) : fn C (two (K i) (R j)) = fam i j := by
    rw [show two (K i) (R j)=two (R j) (K i) by funext w;simp only [two,or_comm]]
    exact (repR _ _).trans (symmetric _ _)
  let S:=E (n+n) C
  let L:=Finset.univ.filter fun i=>¬active C (R i)
  let J:=Finset.univ.filter fun i=>¬active C (K i)
  have ll : L.card≤1:=atMostOne R K sep fam C repR (distinctRows hn)
  have jj : J.card≤1:=atMostOne K R (fun i j=>(sep j i).symm) fam C repK (distinctRows hn)
  have cover : Finset.univ⊆(S ∪ L.image R) ∪ J.image K := by
    intro w _
    by_cases a : active C w
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a⟩))
    induction w using Fin.addCases with
    | left i => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a⟩,rfl⟩))
    | right i => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a⟩,rfl⟩)
  have count:=(Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have lb:=Finset.card_union_le S (L.image R)
  have lc:=Finset.card_image_le (s:=L) (f:=R)
  have jc:=Finset.card_image_le (s:=J) (f:=K)
  simp only [Finset.card_univ,Fintype.card_fin] at count
  by_cases a : ∀i : Fin (n+n),active C i
  · have h:=essentialsCost (N:=n+n) (by omega) C fan a;omega
  push_neg at a
  obtain ⟨i,off⟩:=a
  have price (i : Fin (n+n)) (off : ¬active C i) : S.card+1≤C.size := by
    induction i using Fin.addCases with
    | left r =>
      obtain ⟨q,j,l,p0,p1,q1,q0⟩:=patterns hn r
      exact priceRow R K (fun _ _ e=>Fin.ext (by have h:=congrArg Fin.val e;dsimp [K,right] at h;omega)) sep fam C fan repR r q j l off p0 p1 q1 q0
    | right c =>
      obtain ⟨q,j,l,p0,p1,q1,q0⟩:=patterns hn c
      exact priceRow K R (fun i j e=>Fin.ext (show i.val=j.val from congrArg (fun w : Fin (n+n)=>w.val) e)) (fun i j=>(sep j i).symm) fam C fan repK c q j l off p0 p1 q1 q0
  have h:=price i off;omega
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
namespace Nine
open Check
abbrev Mask:=BitVec 9
def t : Mask := 244
def subset (a b : Mask) := a &&& b == a
def fits (P U : Mask) (B : List Mask) :=
  let ands := B.filter fun a=>subset P a
  let ors := B.filter fun a=>subset a U
  (ands.any fun a=>ands.any fun b=>subset (a &&& b) U) || (ors.any fun a=>ors.any fun b=>subset P (a ||| b))
def cut (B : List Mask) := B.any fun h=>
  ((h≠0 && subset h t) && fits (t &&& ~~~h) t B) ||
  ((h≠511 && subset t h) && fits t (t ||| ~~~h) B) || (h==t)
def test2 (B : List Mask) := cut B || fits t t B
def check : Nat→List Mask→Bool
  | 0,B=>test2 B
  | k+1,B=>check k B || (options false B).any fun v=> !(B.contains v) && check k (v::B)
def raw : List Mask := [7,56,448,73,146,292]
def start : List Mask := [0,511]++raw
end Nine
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace Nine
open Check
def core (i j : Fin 3) := bit (3*i.val+j.val) t
def rr (r : Fin 9) : Fin 3 := ⟨r.val/3,by omega⟩
def cc (r : Fin 9) : Fin 3 := ⟨r.val % 3,Nat.mod_lt _ (by decide)⟩
theorem raws : ∀r : Fin 9,raw.map (bit r.val)=oneEach (rr r) (cc r) := by decide +kernel
theorem idx : ∀r : Fin 9,3*(rr r).val+(cc r).val=r.val := by decide +kernel
theorem positiveCore (unreachable : can false t 6 start=false) (D : Circuit) (m : Monotone2 D) (rep : Represents core D) : 7≤D.size := by
  apply Nat.le_of_not_gt
  intro low
  have val (r : Fin 9) : D.eval (raw.map (bit r.val)) = bit r.val t := by
    rw [raws,rep,core,idx]
  have seen:=readout false D raw start 6 (fun g h=>by simpa using (m g h).1) (fun g h=>(m g h).2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (Nat.le_of_lt_succ low) t (by decide +kernel) val
  exact Bool.noConfusion (unreachable.symm.trans seen)
end Nine

def center {n : Nat} (hn : 4 ≤ n) : Fin 3 ↪ Fin n :=
  ⟨fun i=>⟨i.val+1,by omega⟩,fun a b h=>Fin.ext (by have h':=congrArg Fin.val h;dsimp at h';omega)⟩
theorem coreEq {n : Nat} (hn : 4 ≤ n) (i j : Fin 3) : fam (center hn i) (center hn j)=Nine.core i j := by
  have val (q : Fin 3) : (center hn q).val=q.val+1 := rfl
  have low : ¬ 4 ≤ (center hn i).val := by rw [val];omega
  simp only [fam,low,false_and,decide_false,Bool.or_false,val]
  fin_cases i <;> fin_cases j <;> rfl
theorem positiveLower {n : Nat} (hn : 4 ≤ n) (unreachable : Check.can false Nine.t 6 Nine.start=false) :
    ¬ RepSizeAtMost (@fam n) (2*n) := by
  rintro ⟨C,m,size,rep⟩
  let g:=center hn
  have nonc : ∃i k j l, fam (g i) (g j)≠fam (g k) (g l) := by
    refine ⟨0,0,0,2,?_⟩
    rw [show g=center hn from rfl,coreEq,coreEq]
    decide +kernel
  have row (p : Fin n) : ∃q j,fam p j=true ∧ fam q j=false := by
    obtain ⟨q,c,d,_,p1,_,q0⟩:=patterns hn p;exact ⟨q,d,p1,q0⟩
  have col (p : Fin n) : ∃q j,fam j p=true ∧ fam j q=false := by
    obtain ⟨q,j,yes,no⟩:=row p;exact ⟨q,j,(symmetric j p).trans yes,(symmetric j q).trans no⟩
  obtain ⟨D,md,rd,small⟩:=positiveRestriction n n 3 3 fam g g nonc (fun i _=>row i) (fun j _=>col j) C m rep
  have floor:=Nine.positiveCore unreachable D md (fun i j=>(rd i j).trans (coreEq hn i j))
  omega
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace Builder
abbrev Net := List Gate
open scoped Classical
noncomputable def numNot (N : Net) := (N.filter fun g=>decide (g.op=GateOp.not)).length
def has {n : Nat} (N : Net) (f : Fin n→Fin n→Bool) :=
  ∃i,i<n+n+N.length ∧ ∀r c,(Normalize.run N (oneEach r c)).getD i false=f r c
def keeps {n : Nat} (A B : Net) := ∀f : Fin n→Fin n→Bool,has A f→has B f
structure valid (N : Net) : Prop where
  fan : FanInTwo ⟨N,0⟩
def Extends {n : Nat} (A B : Net) (size inv : Nat) :=
  B.length=A.length+size ∧ numNot B=numNot A+inv ∧ @keeps n A B
theorem reflP {n : Nat} (N : Net) : @Extends n N N 0 0 := ⟨rfl,rfl,fun _ h=>h⟩
theorem transP {n : Nat} {A B C : Net} {k l i j : Nat} (h : @Extends n A B k i) (h' : @Extends n B C l j) :
    @Extends n A C (k+l) (i+j) := ⟨by rw [h'.1,h.1];omega,by rw [h'.2.1,h.2.1];omega,fun _ f=>h'.2.2 _ (h.2.2 _ f)⟩
theorem congrH {n : Nat} {N : Net} {f g : Fin n→Fin n→Bool} (h : has N f) (e : ∀a b, f a b=g a b) : has N g := by
  obtain ⟨i,hi,v⟩:=h;exact ⟨i,hi,fun a b=>(v a b).trans (e a b)⟩
theorem rawRow {n : Nat} (r : Fin n) : has [] (fun u (_ : Fin n)=>decide (u=r)) := by
  refine ⟨r.val,by omega,?_⟩
  intro u v
  change (oneEach u v).getD r.val false=_
  rw [oneEach_eq,inp_getD]
  simp [Fin.ext_iff,show r.val<n+n by omega,show r.val≠n+v.val by omega,eq_comm]
theorem rawCol {n : Nat} (c : Fin n) : has [] (fun (_ : Fin n) v=>decide (v=c)) := by
  refine ⟨n+c.val,by omega,?_⟩
  intro u v
  change (oneEach u v).getD (n+c.val) false=_
  rw [oneEach_eq,inp_getD]
  simp [Fin.ext_iff,show n+c.val<n+n by omega,show n+c.val≠u.val by omega,eq_comm]
theorem blank : valid [] := ⟨by intro g h;cases h⟩

theorem step {n : Nat} (A : Net) (v : valid A) (g : Gate)
    (op : g.op=.and ∨ g.op=.or ∨ g.op=.not) (ar : g.inputs.length≤2) :
    let B:=A++[g]
    valid B ∧ @Extends n A B 1 (if g.op=.not then 1 else 0) ∧
      @has n B (fun r c=>g.op.eval (g.inputs.map fun i=>(Normalize.run A (oneEach r c)).getD i false)) := by
  dsimp only
  have len (r c : Fin n) : (Normalize.run A (oneEach r c)).length=n+n+A.length := by
    rw [Normalize.run_length];simp [oneEach]
  refine ⟨⟨?_⟩,⟨by simp,?_,?_⟩,⟨n+n+A.length,by simp,?_⟩⟩
  · intro q qg
    change q∈A++[g] at qg
    rcases List.mem_append.mp qg with old|new
    · exact v.fan _ old
    · exact (List.mem_singleton.mp new) ▸ ⟨op,ar⟩
  · by_cases h:g.op=.not <;> simp [numNot,h]
  · rintro f ⟨i,hi,he⟩
    refine ⟨i,by simp;omega,fun r c=>?_⟩
    rw [Normalize.run_snoc,Normalize.getD_lt _ _ _ (by rwa [len])]
    exact he r c
  · intro r c;rw [Normalize.run_snoc,←len,Normalize.getD_at]

theorem binary {n : Nat} {A : Net} (v : valid A) {f h : Fin n→Fin n→Bool} (hf : has A f) (hh : has A h) (both : Bool) :
    ∃ B : Net, valid B ∧ @Extends n A B 1 0 ∧ has B (fun r c=>if both then f r c && h r c else f r c || h r c) := by
  obtain ⟨i,_,ei⟩:=hf;obtain ⟨j,_,ej⟩:=hh
  let g : Gate:=⟨if both then .and else .or,[i,j]⟩
  obtain ⟨vb,p,b⟩:=step (n:=n) A v g (by cases both <;> simp [g]) (by simp [g])
  exact ⟨_,vb,by cases both <;> simpa [g] using p,congrH b (by intro r c;cases both <;> simp [g,GateOp.eval,←ei r c,←ej r c])⟩
theorem neg {n : Nat} {A : Net} (v : valid A) {f : Fin n→Fin n→Bool} (hf : has A f) :
    ∃ B : Net, valid B ∧ @Extends n A B 1 1 ∧ has B (fun r c=> !(f r c)) := by
  obtain ⟨i,_,ei⟩:=hf
  let g : Gate:=⟨.not,[i]⟩
  obtain ⟨vb,p,b⟩:=step (n:=n) A v g (by simp [g]) (by simp [g])
  exact ⟨_,vb,by simpa [g] using p,congrH b (by intro r c;simp [g,GateOp.eval,←ei r c])⟩

def diag {n : Nat} (L : List (Fin n)) (f : Fin n→Fin n→Bool) (r c : Fin n) :=
  f r c || decide (r∈L ∧ r=c)
theorem extendTail {n : Nat} (L : List (Fin n)) (A : Net) (va : valid A) (old : @keeps n [] A)
    {f : Fin n→Fin n→Bool} (h : has A f) :
    ∃B : Net,valid B ∧ @Extends n A B (2*L.length) 0 ∧ has B (diag L f) := by
  induction L generalizing A f with
  | nil => exact ⟨A,va,reflP _,congrH h (by simp [diag])⟩
  | cons i L ih =>
    obtain ⟨B,vb,p1,h1⟩:=binary va (old _ (rawRow i)) (old _ (rawCol i)) true
    obtain ⟨D,vd,p2,h2⟩:=binary vb (p1.2.2 _ h) h1 false
    obtain ⟨F,vf,p3,h3⟩:=ih D vd (fun _ w=>p2.2.2 _ (p1.2.2 _ (old _ w))) h2
    refine ⟨F,vf,?_,congrH h3 ?_⟩
    · simpa [List.length_cons,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using transP (transP p1 p2) p3
    · intro r c
      simp [diag]
      by_cases ri : r=i <;> by_cases ci : c=i <;> by_cases rc : r=c <;> simp_all [Bool.or_assoc]

end Builder
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace Builder
def base {n : Nat} (r c : Fin n) := if r.val = 1 ∨ c.val = 1 then decide (r.val=3 ∨ c.val=3) else decide (r.val=2 ∨ c.val=2)
def tails (n : Nat) : List (Fin n) := (List.finRange (n-4)).map (fun k=>⟨4+k.val,by omega⟩)
theorem memT {n : Nat} (i : Fin n) : i∈tails n ↔ 4 ≤ i.val := by
  simp only [tails,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨k,e⟩;have h:=congrArg Fin.val e;change 4+k.val=i.val at h;omega
  · intro h;exact ⟨⟨i.val-4,by omega⟩,Fin.ext (by dsimp;omega)⟩
theorem lenT (n : Nat) : (tails n).length=n-4 := by simp [tails]
theorem extendLump {n : Nat} (L : List (Fin n)) (A : Net) (va : valid A) (old : @keeps n [] A)
    (row : Bool) {f : Fin n→Fin n→Bool} (h : has A f) :
    ∃B : Net,valid B ∧ @Extends n A B L.length 0 ∧
      has B (fun r c=>f r c || decide ((if row then r else c)∈L)) := by
  induction L generalizing A f with
  | nil => exact ⟨A,va,reflP _,congrH h (by simp)⟩
  | cons i L ih =>
    have raw : has [] (fun (r c : Fin n)=>decide ((if row then r else c)=i)) := by
      cases row
      · exact rawCol i
      · exact rawRow i
    obtain ⟨B,vb,p,b⟩:=binary va h (old _ raw) false
    obtain ⟨D,vd,p2,b2⟩:=ih B vb (fun f h=>p.2.2 _ (old _ h)) b
    exact ⟨D,vd,by simpa [List.length_cons,Nat.add_comm] using transP p p2,congrH b2 (by intro r c;simp [Bool.or_assoc])⟩
theorem signedBase {n : Nat} (hn : 4 ≤ n) :
    ∃B : Net, valid B ∧ @Extends n [] B 7 1 ∧ has B (@base n) := by
  have r1 := (rawRow (small hn 1))
  have c1 := (rawCol (small hn 1))
  have r2 := (rawRow (small hn 2))
  have c2 := (rawCol (small hn 2))
  have r3 := (rawRow (small hn 3))
  have c3 := (rawCol (small hn 3))
  obtain ⟨G0,v0,p0,w0⟩:=binary blank r1 c1 false
  obtain ⟨G1,v1,p1,w1⟩:=binary v0 (p0.2.2 _ r2) (p0.2.2 _ c2) false
  obtain ⟨G2,v2,p2,w2⟩:=binary v1 (p1.2.2 _ (p0.2.2 _ r3)) (p1.2.2 _ (p0.2.2 _ c3)) false
  obtain ⟨G3,v3,p3,w3⟩:=neg v2 (p2.2.2 _ (p1.2.2 _ w0))
  obtain ⟨G4,v4,p4,w4⟩:=binary v3 (p3.2.2 _ (p2.2.2 _ (p1.2.2 _ w0))) (p3.2.2 _ w2) true
  obtain ⟨G5,v5,p5,w5⟩:=binary v4 (p4.2.2 _ w3) (p4.2.2 _ (p3.2.2 _ (p2.2.2 _ w1))) true
  obtain ⟨G6,v6,p6,w6⟩:=binary v5 (p5.2.2 _ w4) w5 false
  refine ⟨_,v6,(transP (transP (transP (transP (transP (transP p0 p1) p2) p3) p4) p5) p6),congrH w6 ?_⟩
  intro r c
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.false_eq_true,if_false,if_true,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',Bool.or_eq_false_iff,decide_eq_true_eq,decide_eq_false_iff_not,small,Fin.ext_iff,Fin.reduceFinMk,base]
  split_ifs <;> simp_all <;> omega
theorem positiveBase {n : Nat} (hn : 4 ≤ n) (A : Net) (va : valid A) (old : @keeps n [] A) (r0 : has A (fun (r _ : Fin n)=>decide (r.val=0 ∨ 4 ≤ r.val))) (c0 : has A (fun (_ c : Fin n)=>decide (c.val=0 ∨ 4 ≤ c.val))) :
    ∃B : Net, valid B ∧ @Extends n A B 9 0 ∧ has B (@base n) := by
  have r1 := old _ (rawRow (small hn 1))
  have c1 := old _ (rawCol (small hn 1))
  have r2 := old _ (rawRow (small hn 2))
  have c2 := old _ (rawCol (small hn 2))
  have r3 := old _ (rawRow (small hn 3))
  have c3 := old _ (rawCol (small hn 3))
  obtain ⟨G0,v0,p0,w0⟩:=binary va r1 c2 false
  obtain ⟨G1,v1,p1,w1⟩:=binary v0 (p0.2.2 _ r2) (p0.2.2 _ c1) false
  obtain ⟨G2,v2,p2,w2⟩:=binary v1 (p1.2.2 _ (p0.2.2 _ r0)) (p1.2.2 _ (p0.2.2 _ r2)) false
  obtain ⟨G3,v3,p3,w3⟩:=binary v2 (p2.2.2 _ (p1.2.2 _ (p0.2.2 _ c0))) (p2.2.2 _ (p1.2.2 _ (p0.2.2 _ c2))) false
  obtain ⟨G4,v4,p4,w4⟩:=binary v3 (p3.2.2 _ w2) w3 true
  obtain ⟨G5,v5,p5,w5⟩:=binary v4 (p4.2.2 _ (p3.2.2 _ (p2.2.2 _ (p1.2.2 _ (p0.2.2 _ c3))))) w4 false
  obtain ⟨G6,v6,p6,w6⟩:=binary v5 (p5.2.2 _ (p4.2.2 _ (p3.2.2 _ (p2.2.2 _ (p1.2.2 _ (p0.2.2 _ r3)))))) w5 false
  obtain ⟨G7,v7,p7,w7⟩:=binary v6 (p6.2.2 _ (p5.2.2 _ (p4.2.2 _ (p3.2.2 _ (p2.2.2 _ (p1.2.2 _ w0)))))) (p6.2.2 _ (p5.2.2 _ (p4.2.2 _ (p3.2.2 _ (p2.2.2 _ w1))))) false
  obtain ⟨G8,v8,p8,w8⟩:=binary v7 (p7.2.2 _ w6) w7 true
  refine ⟨_,v8,(transP (transP (transP (transP (transP (transP (transP (transP p0 p1) p2) p3) p4) p5) p6) p7) p8),congrH w8 ?_⟩
  intro r c
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.false_eq_true,if_false,if_true,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',Bool.or_eq_false_iff,decide_eq_true_eq,decide_eq_false_iff_not,small,Fin.ext_iff,Fin.reduceFinMk,base]
  split_ifs <;> simp_all <;> omega
end Builder
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace Builder
open scoped Classical

theorem noNot {N : Net} : numNot N=0 ↔ ∀g∈N,g.op≠GateOp.not := by
  simp [numNot,List.filter_eq_nil_iff]
theorem uniqueN (N : Net) (h : numNot N=1) : ∃!j : Fin N.length,(N.get j).op=.not := by
  induction N with
  | nil => simp [numNot] at h
  | cons g gs ih =>
    by_cases yes : g.op=.not
    · have zero : numNot gs=0 := by simpa [numNot,yes] using h
      refine ⟨0,yes,?_⟩
      intro j use
      refine Fin.cases ?_ (fun i u=>?_) j use
      · intro _;rfl
      · exact False.elim ((noNot.mp zero (gs.get i) (List.get_mem ..)) u)
    · have one : numNot gs=1 := by simpa [numNot,yes] using h
      obtain ⟨j,op,un⟩:=ih one
      refine ⟨j.succ,op,?_⟩
      intro k use
      refine Fin.cases ?_ (fun i u=>?_) k use
      · exact fun u=>(yes u).elim
      · exact congrArg Fin.succ (un i u)

theorem finalVal {n : Nat} (r c : Fin n) : diag (tails n) base r c=fam r c := by
  simp [diag,base,fam,memT]

theorem signedU {n : Nat} (hn : 4 ≤ n) :
    ∃ C : Circuit, FanInTwo C ∧ Represents (@fam n) C ∧ C.size=2*n-1 ∧ ∃! j : Fin C.gates.length, (C.gates.get j).op=GateOp.not := by
  obtain ⟨A,va,p,h⟩:=signedBase hn
  obtain ⟨D,vd,p',d⟩:=extendTail (tails n) A va p.2.2 h
  obtain ⟨i,_,eval⟩:=congrH d finalVal
  have s:=p.1
  have t:=p'.1
  simp only [List.length_nil,Nat.zero_add,lenT] at s t
  have nz : numNot D=1 := by rw [p'.2.1,p.2.1];rfl
  exact ⟨⟨D,i⟩,vd.fan,eval,by change D.length=_;omega,uniqueN D nz⟩

theorem positiveU {n : Nat} (hn : 4 ≤ n) : RepSizeAtMost (@fam n) (4*n-7) := by
  obtain ⟨A,va,p,r⟩:=extendLump (tails n) [] blank (fun _ h=>h) true (rawRow (small hn 0))
  obtain ⟨B,vb,p',c⟩:=extendLump (tails n) A va p.2.2 false (p.2.2 _ (rawCol (small hn 0)))
  have row : has B (fun (r _ : Fin n)=>decide (r.val=0 ∨ 4 ≤ r.val)) := by
    apply congrH (p'.2.2 _ r)
    intro i j;simp [memT,small,Fin.ext_iff]
  have col : has B (fun (_ c : Fin n)=>decide (c.val=0 ∨ 4 ≤ c.val)) := by
    apply congrH c;intro i j;simp [memT,small,Fin.ext_iff]
  have pp:=transP p p'
  obtain ⟨D,vd,core,cv⟩:=positiveBase hn B vb pp.2.2 row col
  have pcore:=transP pp core
  obtain ⟨F,vf,tail,ev⟩:=extendTail (tails n) D vd pcore.2.2 cv
  obtain ⟨out,_,v⟩:=congrH ev finalVal
  have all:=transP pcore tail
  have len:=all.1
  simp only [List.length_nil,Nat.zero_add,lenT] at len
  have free : numNot F=0 := by rw [all.2.1];rfl
  refine ⟨⟨F,out⟩,?_,by change F.length≤_;omega,v⟩
  intro g hg
  obtain ⟨op,ar⟩:=vf.fan g hg
  have nn:=noNot.mp free g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
  exact ⟨by change g.op=.and ∨ g.op=.or;tauto,ar⟩

end Builder
end PEqualNP.Outside.L_meta_26029_aux.Small

namespace PEqualNP.Outside.L_meta_26029_aux.Forest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

def compute (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => x.getD i false)

def step (x : List Bool) (g : Gate) : List Bool := x ++ [compute x g]

theorem snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

def Below (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem compute_monotone {x y : List Bool} (h : Below x y) {g : Gate}
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    compute x g = true → compute y g = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with e | e
  · simp only [compute, e, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h0 a ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact h i (h0 _ ⟨i, hi, rfl⟩)
  · simp only [compute, e, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨a, ⟨i, hi, rfl⟩, ea⟩
    exact ⟨y.getD i false, ⟨i, hi, rfl⟩, h i ea⟩

theorem fold_monotone (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {x y : List Bool} (he : x.length = y.length) (h : Below x y) :
    Below (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    have hnext : Below (step x g) (step y g) := by
      intro i hi
      simp only [step, snoc, ← he] at hi ⊢
      split_ifs at hi ⊢
      · exact h i hi
      · exact compute_monotone h (hg g (by simp)) hi
    exact ih (fun a ha => hg a (List.mem_cons_of_mem _ ha)) (by simp [step, he]) hnext

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl step x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, step, ih]; omega

theorem setD (l : List Bool) (k i : ℕ) :
    (l.set k false).getD i false = if i = k then false else l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h : k = i
  · subst h; simp only [ite_true]; split_ifs <;> rfl
  · simp [h, Ne.symm h]

theorem each_value {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  apply Bool.eq_iff_iff.2
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem pre (gs : List Gate) : ∀ (x : List Bool) (w : ℕ), w < x.length →
    (gs.foldl step x).getD w false = x.getD w false := by
  induction gs with
  | nil => intro x w _; rfl
  | cons g gs ih =>
    intro x w h
    rw [List.foldl_cons, ih _ _ (by simp [step]; omega), step, snoc, ite_eq_left h]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl step w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
      intro i hi
      simp only [step, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (step (gs.foldl step w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false) := by
        simp only [step, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen, compute, List.getD_eq_getElem?_getD]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

theorem gate_formula (C : Circuit) {N j : ℕ} (x : List Bool)
    (hx : x.length = N) (hj : j < C.gates.length) :
    (C.gates.foldl step x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < N + j then (C.gates.foldl step x).getD i false else false) := by
  have h := foldl_char C.gates x j hj
  rw [hx] at h
  exact h

def before (C : Circuit) (N j w : ℕ) : Prop := w ∈ (gateAt C j).inputs ∧ w < N + j

def closed (N : ℕ) (C : Circuit) (L : Finset ℕ) : Prop :=
  (∀ j ∈ L, j < C.gates.length) ∧
    ∀ j ∈ L, ∀ i, before C N j (N + i) → i ∈ L

theorem minimal_closed (N : ℕ) (C : Circuit) (r : ℕ) (hr : r < C.gates.length) :
    ∃ L : Finset ℕ, r ∈ L ∧ closed N C L ∧
      ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i) := by
  classical
  let A := Finset.range C.gates.length
  have hc : closed N C A := by
    refine ⟨fun j hj => Finset.mem_range.mp hj, ?_⟩
    intro j hj i hi
    have hlt := Finset.mem_range.mp hj
    have hs := hi.2
    exact Finset.mem_range.mpr (by omega)
  let candidates := A.powerset.filter fun L => r ∈ L ∧ closed N C L
  have hA : A ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), Finset.mem_range.mpr hr, hc⟩
  obtain ⟨L, hL, hmin⟩ := candidates.exists_min_image Finset.card ⟨A, hA⟩
  obtain ⟨hsub, hrL, hclose⟩ := Finset.mem_filter.mp hL
  refine ⟨L, hrL, hclose, ?_⟩
  intro i hi hir
  by_contra hn
  have hs : L.erase i ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_erase.mpr ⟨Ne.symm hir, hrL⟩, ?_⟩
    · exact (Finset.erase_subset _ _).trans (Finset.mem_powerset.mp hsub)
    · constructor
      · intro j hj
        exact hclose.1 j (Finset.mem_of_mem_erase hj)
      · intro j hj k hkj
        have hj' := Finset.mem_of_mem_erase hj
        refine Finset.mem_erase.mpr ⟨?_, hclose.2 j hj' k hkj⟩
        rintro rfl
        exact hn ⟨j, hj', hkj⟩
  have h := hmin _ hs
  have hpos := Finset.card_pos.mpr ⟨i, hi⟩
  rw [Finset.card_erase_of_mem hi] at h
  omega

def inputSlots (N : ℕ) (C : Circuit) (j : ℕ) : Finset (ℕ × ℕ) :=
  ((gateAt C j).inputs.toFinset.filter (· < N + j)).image (Prod.mk j)

def slots (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (ℕ × ℕ) :=
  L.biUnion (inputSlots N C)

theorem mem_slot {N : ℕ} {C : Circuit} {L : Finset ℕ} {j w : ℕ} :
    (j,w) ∈ slots N C L ↔ j ∈ L ∧ before C N j w := by
  constructor
  · intro h
    obtain ⟨j', hj', hh⟩ := Finset.mem_biUnion.mp h
    obtain ⟨w', hw', he⟩ := Finset.mem_image.mp hh
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    have ⟨hi,hl⟩ := Finset.mem_filter.mp hw'
    exact ⟨hj', List.mem_toFinset.mp hi, hl⟩
  · rintro ⟨hj, hw, hl⟩
    exact Finset.mem_biUnion.mpr
      ⟨j,hj,Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw,hl⟩,rfl⟩⟩

def used (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  (slots N C L).image Prod.snd

theorem mem_used {N : ℕ} {C : Circuit} {L : Finset ℕ} {w : ℕ} :
    w ∈ used N C L ↔ ∃ j ∈ L, before C N j w := by
  constructor
  · intro h
    obtain ⟨⟨j,i⟩, hslot, e⟩ := Finset.mem_image.mp h
    change i = w at e
    subst i
    exact ⟨j,(mem_slot.mp hslot).1,(mem_slot.mp hslot).2⟩
  · rintro ⟨j,hj,hw⟩
    exact Finset.mem_image.mpr ⟨(j,w),mem_slot.mpr ⟨hj,hw⟩,rfl⟩

theorem closed_values {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (he : ∀ i ∈ used N C L, x.getD i false = y.getD i false) :
    ∀ j ∈ L, (C.gates.foldl step x).getD (N + j) false =
      (C.gates.foldl step y).getD (N + j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    rw [gate_formula C x hx (hL.1 j hj), gate_formula C y hy (hL.1 j hj)]
    congr 1
    apply List.map_congr_left
    intro w hw
    split_ifs with hb <;> try rfl
    by_cases hi : w < N
    · rw [pre _ _ _ (by omega : w < x.length), pre _ _ _ (by omega : w < y.length)]
      exact he w (mem_used.mpr ⟨j,hj,hw,hb⟩)
    · let i := w - N
      have e : N + i = w := by dsimp [i]; omega
      have hil : i < j := by omega
      rw [← e] at hw hb ⊢
      exact ih i hil (hL.2 j hj i ⟨hw,hb⟩)

theorem needed {N : ℕ} {C : Circuit} (hC : Monotone2 C) {L : Finset ℕ}
    (hL : closed N C L) {r : ℕ} (hr : r ∈ L) (hout : C.output = N + r)
    {x y : List Bool} (hx : x.length = N) (hy : y.length = N) (i : ℕ)
    (he : Below (x.set i false) y) (ht : C.eval x = true) (hf : C.eval y = false) :
    i ∈ used N C L := by
  by_contra h
  have hr' : C.eval x = C.eval (x.set i false) := by
    change (C.gates.foldl step x).getD C.output false =
      (C.gates.foldl step (x.set i false)).getD C.output false
    rw [hout]
    refine closed_values hL x (x.set i false) hx (by simp [hx]) ?_ r hr
    intro a ha
    have hn : a ≠ i := fun e => h (e ▸ ha)
    rw [setD, ite_eq_right hn]
  have hmono := fold_monotone C.gates (fun a ha => (hC a ha).1)
    (show (x.set i false).length = y.length by simp [hx, hy]) he C.output
  have hv : C.eval y = true := hmono (hr'.symm.trans ht)
  rw [hf] at hv
  contradiction

theorem inputSlots_card (N : ℕ) (C : Circuit) (j : ℕ) :
    (inputSlots N C j).card = ((gateAt C j).inputs.toFinset.filter (· < N + j)).card :=
  Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)

theorem output_shape {n m : ℕ} (C : Circuit) (hC : Monotone2 C)
    (hsmall : C.gates.length ≤ n + m - 1) (hraw : n + m ≤ C.output)
    (hout : C.output < n + m + C.gates.length)
    (hsupport : ∀ (L : Finset ℕ) (r : ℕ), closed (n + m) C L → r ∈ L →
      C.output = n + m + r → Finset.range (n + m) ⊆ used (n + m) C L) :
    C.gates.length = n + m - 1 ∧
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      ReadsBack (n + m) C ∧ (∀ i, readsIn C (Finset.range C.gates.length) i ≤ 1) ∧
      C.output < (n + m) + C.gates.length ∧ readsIn C (Finset.range C.gates.length) C.output = 0 := by
  classical
  let r := C.output - (n + m)
  have er : C.output = (n + m) + r := by dsimp [r]; omega
  have hr : r < C.gates.length := by dsimp [r]; omega
  obtain ⟨L, hrL, hL, huse⟩ := minimal_closed (n + m) C r hr
  have hused := hsupport L r hL hrL er
  let necessary := Finset.range (n + m)
  let inside : Finset ℕ := (L.erase r).image ((n + m) + ·)
  let required := necessary ∪ inside
  have hnec : ∀ w ∈ necessary, w < n + m := fun _ h => Finset.mem_range.mp h
  have hdis : Disjoint necessary inside := by
    apply Finset.disjoint_left.mpr
    intro w hw hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    have := hnec _ hw
    omega
  have hreq : required ⊆ used (n + m) C L := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hused hw
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hj
      exact mem_used.mpr (huse j hmem hne)
  have hsize : required.card = n + m + (L.card - 1) := by
    unfold required inside
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b hi => by omega), Finset.card_erase_of_mem hrL]
    exact congrArg (· + (L.card - 1)) (Finset.card_range (n + m))
  have hfit (j : ℕ) (hj : j < C.gates.length) :
      (gateAt C j).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (gateAt C j).inputs.length ≤ 2 := by
    apply hC
    rw [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hwsize (j : ℕ) (hj : j ∈ L) : (inputSlots (n + m) C j).card ≤ 2 := by
    rw [inputSlots_card]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((List.toFinset_card_le _).trans (hfit _ (hL.1 j hj)).2)
  have hle := Finset.card_biUnion_le_card_mul L (inputSlots (n + m) C) 2 hwsize
  change (slots (n + m) C L).card ≤ L.card * 2 at hle
  have hcap := Finset.card_image_le (s := slots (n + m) C L) (f := Prod.snd)
  change (used (n + m) C L).card ≤ (slots (n + m) C L).card at hcap
  have hn := Finset.card_le_card hreq
  have hLsub : L ⊆ Finset.range C.gates.length := fun j hj => Finset.mem_range.mpr (hL.1 j hj)
  have hLc : L.card ≤ C.gates.length := by simpa using Finset.card_le_card hLsub
  have hp := Finset.card_pos.mpr ⟨r, hrL⟩
  have heL : L.card = n + m - 1 := by omega
  have hfull : L = Finset.range C.gates.length :=
    Finset.eq_of_subset_of_card_le hLsub (by rw [Finset.card_range]; omega)
  have hunique : Set.InjOn Prod.snd (slots (n + m) C L : Set (ℕ × ℕ)) :=
    Finset.injOn_of_card_image_eq (show (used (n + m) C L).card = (slots (n + m) C L).card by omega)
  have heUsed : required = used (n + m) C L := Finset.eq_of_subset_of_card_le hreq (by omega)
  have slot_full (j : ℕ) (hj : j ∈ L) : (inputSlots (n + m) C j).card = 2 := by
    have hsum := Finset.card_biUnion_le (s := L) (t := inputSlots (n + m) C)
    change (slots (n + m) C L).card ≤ ∑ k ∈ L, (inputSlots (n + m) C k).card at hsum
    have hsum' : (∑ k ∈ L.erase j, (inputSlots (n + m) C k).card) ≤
        (L.erase j).card * 2 := by
      calc
        _ ≤ ∑ _ ∈ L.erase j, (2 : ℕ) := by
          exact Finset.sum_le_sum fun k hk => hwsize k (Finset.mem_of_mem_erase hk)
        _ = _ := by simp
    have hsplit := Finset.sum_erase_add L (fun k => (inputSlots (n + m) C k).card) hj
    rw [Finset.card_erase_of_mem hj] at hsum'
    have h2 := hwsize j hj
    omega
  have local_size (j : ℕ) (hj : j < C.gates.length) :
      (gateAt C j).inputs.length = 2 ∧ (gateAt C j).inputs.Nodup ∧
        ∀ w ∈ (gateAt C j).inputs, w < (n + m) + j := by
    have hm : j ∈ L := hfull.symm ▸ Finset.mem_range.mpr hj
    have ha := slot_full j hm
    rw [inputSlots_card] at ha
    let us := (gateAt C j).inputs.toFinset
    have hb := List.toFinset_card_le (gateAt C j).inputs
    have hc := Finset.card_le_card (Finset.filter_subset (· < (n + m) + j) us)
    have hl := (hfit j hj).2
    change us.card ≤ (gateAt C j).inputs.length at hb
    change (us.filter (· < (n + m) + j)).card = 2 at ha
    have he : (gateAt C j).inputs.length = 2 := by omega
    have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset (· < (n + m) + j) us)
      (by omega : us.card ≤ (us.filter (· < (n + m) + j)).card)
    obtain ⟨a,b,hlist⟩ := List.length_eq_two.mp he
    refine ⟨he, ?_, ?_⟩
    · have hne : a ≠ b := by
        rintro rfl
        simp [us,hlist] at hc ha
        omega
      simp [hlist, hne]
    · intro w hw
      have hi : w ∈ us := List.mem_toFinset.mpr hw
      rw [← heq] at hi
      exact (Finset.mem_filter.mp hi).2
  have unique_gate {j k w : ℕ} (hj : j < C.gates.length) (hk : k < C.gates.length)
      (hw : w ∈ (gateAt C j).inputs) (hv : w ∈ (gateAt C k).inputs) : j = k := by
    have h1 : (j,w) ∈ slots (n + m) C L :=
      mem_slot.mpr ⟨hfull.symm ▸ Finset.mem_range.mpr hj, hw, (local_size j hj).2.2 w hw⟩
    have h2 : (k,w) ∈ slots (n + m) C L :=
      mem_slot.mpr ⟨hfull.symm ▸ Finset.mem_range.mpr hk, hv, (local_size k hk).2.2 w hv⟩
    exact congrArg Prod.fst (hunique h1 h2 rfl)
  refine ⟨by omega, ?_, fun j hj => (local_size j hj).2.2, ?_, hout, ?_⟩
  · intro g hg
    obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hg
    have hgj' : gateAt C j = g := by rw [gateAt, List.getD_eq_getElem _ _ hj, hgj]
    have hop := (hfit j hj).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hgj'] at hop
    exact ⟨hop, hgj' ▸ (local_size j hj).1⟩
  · intro w
    unfold readsIn
    by_cases h : ∃ j < C.gates.length, w ∈ (gateAt C j).inputs
    · obtain ⟨j,hj,hw⟩ := h
      rw [Finset.sum_eq_single j]
      · exact List.nodup_iff_count_le_one.mp (local_size j hj).2.1 w
      · intro k hk hkj
        exact List.count_eq_zero.mpr fun hn => hkj (unique_gate (Finset.mem_range.mp hk) hj hn hw)
      · intro hn
        exact (hn (Finset.mem_range.mpr hj)).elim
    · have hz : ∑ j ∈ Finset.range C.gates.length, (gateAt C j).inputs.count w = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact List.count_eq_zero.mpr fun hw => h ⟨j, Finset.mem_range.mp hj, hw⟩
      rw [hz]
      decide
  · unfold readsIn
    apply Finset.sum_eq_zero
    intro j hj
    apply List.count_eq_zero.mpr
    intro he
    have hj' := Finset.mem_range.mp hj
    have hh : C.output ∈ used (n + m) C L :=
      mem_used.mpr ⟨j, hfull.symm ▸ hj, he, (local_size j hj').2.2 _ he⟩
    rw [← heUsed] at hh
    rcases Finset.mem_union.mp hh with hh | hh
    · have := hnec _ hh
      omega
    · obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hh
      have hn := (Finset.mem_erase.mp hi).1
      omega

variable {α : Type} [DecidableEq α]

def bits (s : Finset α) (i : α) : Bool := decide (i ∈ s)

def Local (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

def hits (f : (α → Bool) → Bool) (a : α) : Prop := f (bits {a}) = true

def edge (f : (α → Bool) → Bool) (a b : α) : Prop := f (bits {a, b}) = true

def Rectangles (f : (α → Bool) → Bool) : Prop :=
  ∀ a b c d, f (bits {a}) = false → f (bits {b}) = false →
    f (bits {c}) = false → f (bits {d}) = false →
    edge f a b → edge f c b → edge f c d → edge f a d

def Spec (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  s.Nonempty ∧ Local s f ∧ f (bits ∅) = false ∧ f (fun _ => true) = true ∧ Rectangles f

theorem pair_without {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f) {a b : α}
    (ha : a ∉ s) : f (bits {a, b}) = f (bits {b}) := by
  apply hf
  intro i hi
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  simp [bits, hia]

theorem single_without {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f) {a : α}
    (ha : a ∉ s) : f (bits {a}) = f (bits ∅) := by
  apply hf
  intro i hi
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  simp [bits, hia]

theorem hit_in {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f)
    (hzero : f (bits ∅) = false) {a : α} (ha : hits f a) : a ∈ s := by
  by_contra h
  change f (bits {a}) = true at ha
  rw [single_without hf h, hzero] at ha
  contradiction

theorem edge_comm {f : (α → Bool) → Bool} {a b : α} : edge f a b ↔ edge f b a := by
  simp only [edge, Finset.pair_comm a b]

theorem edge_inside {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f)
    {a b : α} (ha : f (bits {a}) = false) (hb : f (bits {b}) = false)
    (hab : edge f a b) : a ∈ s ∧ b ∈ s := by
  have left {i j : α} (h0 : f (bits {j}) = false) (h : edge f i j) : i ∈ s := by
    by_contra hi
    change f (bits {i, j}) = true at h
    rw [pair_without hf hi, h0] at h
    contradiction
  exact ⟨left hb hab, left ha (edge_comm.mp hab)⟩

theorem or_rectangles {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (rf : Rectangles f) (rg : Rectangles g) : Rectangles (fun x => f x || g x) := by
  intro a b c d ha hb hc hd hab hcb hcd
  have sf {i : α} (h : (f (bits {i}) || g (bits {i})) = false) :
      f (bits {i}) = false := (Bool.or_eq_false_iff.mp h).1
  have sg {i : α} (h : (f (bits {i}) || g (bits {i})) = false) :
      g (bits {i}) = false := (Bool.or_eq_false_iff.mp h).2
  have hnot {i : α} (hi : i ∈ s) (hj : i ∈ t) : False := Finset.disjoint_left.mp hdis hi hj
  change (f (bits {a, b}) || g (bits {a, b})) = true at hab
  change (f (bits {c, b}) || g (bits {c, b})) = true at hcb
  change (f (bits {c, d}) || g (bits {c, d})) = true at hcd
  have hresult : edge f a d ∨ edge g a d := by
    rcases Bool.or_eq_true_iff.mp hab with hab | hab
    · have hb' := (edge_inside hf (sf ha) (sf hb) hab).2
      have hcb' : edge f c b := (Bool.or_eq_true_iff.mp hcb).resolve_right
        (fun h => hnot hb' (edge_inside hg (sg hc) (sg hb) h).2)
      have hc' := (edge_inside hf (sf hc) (sf hb) hcb').1
      have hcd' : edge f c d := (Bool.or_eq_true_iff.mp hcd).resolve_right
        (fun h => hnot hc' (edge_inside hg (sg hc) (sg hd) h).1)
      exact Or.inl (rf a b c d (sf ha) (sf hb) (sf hc) (sf hd) hab hcb' hcd')
    · have hb' := (edge_inside hg (sg ha) (sg hb) hab).2
      have hcb' : edge g c b := (Bool.or_eq_true_iff.mp hcb).resolve_left
        (fun h => hnot (edge_inside hf (sf hc) (sf hb) h).2 hb')
      have hc' := (edge_inside hg (sg hc) (sg hb) hcb').1
      have hcd' : edge g c d := (Bool.or_eq_true_iff.mp hcd).resolve_left
        (fun h => hnot (edge_inside hf (sf hc) (sf hd) h).1 hc')
      exact Or.inr (rg a b c d (sg ha) (sg hb) (sg hc) (sg hd) hab hcb' hcd')
  exact Bool.or_eq_true_iff.mpr hresult

theorem and_edge {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (zf : f (bits ∅) = false) (zg : g (bits ∅) = false) (a b : α) :
    edge (fun x => f x && g x) a b ↔
      (hits f a ∧ hits g b) ∨ (hits f b ∧ hits g a) := by
  have dis {i : α} (hs : i ∈ s) (ht : i ∈ t) : False := Finset.disjoint_left.mp hdis hs ht
  have lands {r : Finset α} {h : (α → Bool) → Bool} (hl : Local r h)
      (hz : h (bits ∅) = false) {i j : α} (hij : edge h i j) : i ∈ r ∨ j ∈ r := by
    by_contra hn
    change h (bits {i, j}) = true at hij
    rw [pair_without hl (fun hi => hn (Or.inl hi)),
      single_without hl (fun hj => hn (Or.inr hj)), hz] at hij
    contradiction
  have align {i j : α} (hi : i ∈ s) (hj : j ∈ t) :
      (edge f i j ∧ edge g i j) ↔ hits f i ∧ hits g j := by
    have e₁ : f (bits {i, j}) = f (bits {i}) := by
      rw [Finset.pair_comm i j, pair_without hf (fun hs => dis hs hj)]
    have e₂ : g (bits {i, j}) = g (bits {j}) := pair_without hg (fun ht => dis hi ht)
    unfold edge hits
    rw [e₁, e₂]
  change (f (bits {a, b}) && g (bits {a, b})) = true ↔ _
  rw [Bool.and_eq_true]
  constructor
  · intro h
    rcases lands hf zf h.1 with ha | hb
    · have hb' := (lands hg zg h.2).resolve_left (fun ha' => dis ha ha')
      exact Or.inl ((align ha hb').mp h)
    · have ha' := (lands hg zg h.2).resolve_right (fun hb' => dis hb hb')
      exact Or.inr ((align hb ha').mp ⟨edge_comm.mp h.1, edge_comm.mp h.2⟩)
  · rintro (h | h)
    · exact (align (hit_in hf zf h.1) (hit_in hg zg h.2)).mpr h
    · have hh := (align (hit_in hf zf h.1) (hit_in hg zg h.2)).mpr h
      exact ⟨edge_comm.mp hh.1, edge_comm.mp hh.2⟩

theorem and_rectangles {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (zf : f (bits ∅) = false) (zg : g (bits ∅) = false) :
    Rectangles (fun x => f x && g x) := by
  intro a b c d _ _ _ _ hab hcb hcd
  have ha (i j : α) := and_edge hdis hf hg zf zg i j
  have hn {i : α} (h₁ : hits f i) (h₂ : hits g i) : False :=
    Finset.disjoint_left.mp hdis (hit_in hf zf h₁) (hit_in hg zg h₂)
  apply (ha a d).mpr
  rcases (ha a b).mp hab with hab | hab
  · have hcb := ((ha c b).mp hcb).resolve_right (fun h => hn h.1 hab.2)
    have hcd := ((ha c d).mp hcd).resolve_right (fun h => hn hcb.1 h.2)
    exact Or.inl ⟨hab.1, hcd.2⟩
  · have hcb := ((ha c b).mp hcb).resolve_left (fun h => hn hab.1 h.2)
    have hcd := ((ha c d).mp hcd).resolve_left (fun h => hn h.1 hcb.2)
    exact Or.inr ⟨hcd.1, hab.2⟩

def connect (isAnd : Bool) (f g : (α → Bool) → Bool) (x : α → Bool) : Bool :=
  if isAnd then f x && g x else f x || g x

theorem combined_spec {s t : Finset α} {f g : (α → Bool) → Bool}
    (isAnd : Bool) (hdis : Disjoint s t) (hf : Spec s f) (hg : Spec t g) :
    Spec (s ∪ t) (connect isAnd f g) := by
  rcases hf with ⟨⟨a, ha⟩, lf, zf, onesF, rf⟩
  rcases hg with ⟨_, lg, zg, onesG, rg⟩
  refine ⟨⟨a, Finset.mem_union_left _ ha⟩, ?_, ?_, ?_, ?_⟩
  · intro x y h
    simp only [connect, lf x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      lg x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  · cases isAnd <;> simp [connect, zf, zg]
  · cases isAnd <;> simp [connect, onesF, onesG]
  · cases isAnd with
    | false => exact or_rectangles hdis lf lg rf rg
    | true => exact and_rectangles hdis lf lg zf zg

theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_initial {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_keeps F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_initial hpre (by simp; omega), ← hPl]
  simp

def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wireAt (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < x.length + j then (C.wires x).getD i false else false) := by
  obtain ⟨value,pre,len⟩ := foldl_snoc_split readGate C.gates x j hj false
  rw [show (C.wires x).getD (x.length + j) false = _ from value]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i _
  split
  · exact (getD_of_initial pre (by omega) false).symm
  · apply List.getD_eq_default
    unfold readGate at len
    omega

def wire (N : ℕ) (C : Circuit) (i : ℕ) (x : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem wire_input (N : ℕ) (C : Circuit) (i : ℕ) (hi : i < N) :
    wire N C i = fun x => x ⟨i, hi⟩ := by
  funext x
  have hl : i < (List.ofFn x).length := by simpa using hi
  have hp : List.ofFn x <+: C.wires (List.ofFn x) := foldl_snoc_keeps readGate C.gates _
  rw [wire, getD_of_initial hp hl false, List.getD_eq_getElem _ _ hl]
  exact List.getElem_ofFn hl

theorem wire_gate {N : ℕ} (C : Circuit) (hback : ReadsBack N C) (j a b : ℕ)
    (hj : j < C.gates.length) (hins : (gateAt C j).inputs = [a, b])
    (hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) :
    ∃ isAnd, wire N C (N + j) = connect isAnd (wire N C a) (wire N C b) := by
  have ha := hback j hj a (by simp [hins])
  have hb := hback j hj b (by simp [hins])
  have hat : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have ev (x : Fin N → Bool) :
      wire N C (N + j) x =
        (gateAt C j).op.eval [wire N C a x, wire N C b x] := by
    have he := wireAt C (List.ofFn x) j hj
    rw [List.length_ofFn, ← hat, hins] at he
    simpa only [wire, List.map_cons, List.map_nil, ite_eq_left ha, ite_eq_left hb] using he
  rcases hop with h | h
  · refine ⟨true, funext fun x => ?_⟩
    rw [ev, h]
    simp [GateOp.eval, connect]
  · refine ⟨false, funext fun x => ?_⟩
    rw [ev, h]
    simp [GateOp.eval, connect]

theorem variable_spec (i : α) : Spec {i} (fun x => x i) := by
  refine ⟨⟨i, by simp⟩, fun x y h => h i (by simp), by simp [bits], rfl, ?_⟩
  intro a b c d ha hb _ _ hab _ _
  simp [bits, edge] at ha hb hab
  tauto

theorem read_mono (C : Circuit) {p q : ℕ} (hpq : p ≤ q) (i : ℕ) :
    readsIn C (Finset.range p) i ≤ readsIn C (Finset.range q) i := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hpq) (fun _ _ _ => Nat.zero_le _)

def Live (N : ℕ) (C : Circuit) (k i : ℕ) : Prop :=
  i < N + k ∧ readsIn C (Finset.range k) i = 0

theorem label_invariant (N : ℕ) (C : Circuit)
    (hgate : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hback : ReadsBack N C)
    (hbound : ∀ i < N + C.gates.length, readsIn C (Finset.range C.gates.length) i ≤ 1) :
    ∀ k ≤ C.gates.length, ∃ label : ℕ → Finset (Fin N),
      (∀ i, Live N C k i → Spec (label i) (wire N C i)) ∧
      (∀ i j, Live N C k i → Live N C k j → i ≠ j → Disjoint (label i) (label j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    let label (i : ℕ) : Finset (Fin N) := if h : i < N then {⟨i, h⟩} else ∅
    have singleton (i : ℕ) (hi : Live N C 0 i) :
        label i = {⟨i, by simpa using hi.1⟩} := by
      have h : i < N := by simpa using hi.1
      simp [label, h]
    refine ⟨label, ?_, ?_⟩
    · intro i hi
      have hi' : i < N := by simpa using hi.1
      rw [singleton i hi, wire_input N C i hi']
      exact variable_spec _
    · intro i j hi hj hij
      rw [singleton i hi, singleton j hj]
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact hij (congrArg Fin.val ((Finset.mem_singleton.mp ha).symm.trans (Finset.mem_singleton.mp hb)))
  | succ k ih =>
    intro hk
    obtain ⟨label, hlabel, hd⟩ := ih (by omega)
    have hg : k < C.gates.length := by omega
    have hat : gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hg
    have good := hgate (gateAt C k) (by rw [hat]; exact List.getElem_mem _)
    obtain ⟨a, b, hin⟩ := List.length_eq_two.mp good.2
    have count_step (i : ℕ) : readsIn C (Finset.range (k + 1)) i =
        readsIn C (Finset.range k) i + ([a, b] : List ℕ).count i := by
      rw [readsIn, Finset.sum_range_succ]
      change readsIn C (Finset.range k) i + (gateAt C k).inputs.count i = _
      rw [hin]
    have aEarlier := hback k hg a (by simp [hin])
    have bEarlier := hback k hg b (by simp [hin])
    have readBound (i : ℕ) (hi : i < N + k) :
        readsIn C (Finset.range (k + 1)) i ≤ 1 :=
      (read_mono C hk i).trans (hbound i (by omega))
    have ac := readBound a aEarlier
    have bc := readBound b bEarlier
    rw [count_step] at ac bc
    have ap : 0 < ([a, b] : List ℕ).count a := List.count_pos_iff.mpr (by simp)
    have bp : 0 < ([a, b] : List ℕ).count b := List.count_pos_iff.mpr (by simp)
    have ha : Live N C k a := ⟨aEarlier, by omega⟩
    have hb : Live N C k b := ⟨bEarlier, by omega⟩
    have hab : a ≠ b := by
      intro h
      subst b
      simp at ac
    have hdis := hd a b ha hb hab
    obtain ⟨isAnd, hwire⟩ := wire_gate C hback k a b hg hin good.1
    have vertex (i : ℕ) (hi : Live N C (k + 1) i) :
        i ≠ a ∧ i ≠ b := by
      have hcount := hi.2
      rw [count_step] at hcount
      constructor
      · intro h; subst i; omega
      · intro h; subst i; omega
    have earlier (i : ℕ) (hi : Live N C (k + 1) i) (he : i ≠ N + k) :
        Live N C k i := by
      obtain ⟨hl, hr⟩ := hi
      rw [count_step] at hr
      exact ⟨by omega, by omega⟩
    let next (i : ℕ) := if i = N + k then label a ∪ label b else label i
    have root : Spec (label a ∪ label b) (wire N C (N + k)) := by
      rw [hwire]
      exact combined_spec isAnd hdis (hlabel a ha) (hlabel b hb)
    refine ⟨next, ?_, ?_⟩
    · intro i hi
      by_cases he : i = N + k
      · subst i
        simpa [next] using root
      · simpa [next, he] using hlabel i (earlier i hi he)
    · intro i j hi hj hij
      have join_disjoint (p : ℕ) (hp : Live N C (k + 1) p) (he : p ≠ N + k) :
          Disjoint (label a ∪ label b) (label p) :=
        Finset.disjoint_union_left.mpr
          ⟨hd a p ha (earlier p hp he) (vertex p hp).1.symm,
            hd b p hb (earlier p hp he) (vertex p hp).2.symm⟩
      by_cases hi' : i = N + k
      · subst i
        simpa [next, hij.symm] using join_disjoint j hj hij.symm
      · by_cases hj' : j = N + k
        · subst j
          simpa [next, hi'] using (join_disjoint i hi hi').symm
        · simpa [next, hi', hj'] using hd i j (earlier i hi hi') (earlier j hj hj') hij

def row {n m : ℕ} (u : Fin n) : Fin (n + m) := ⟨u.val, by have := u.isLt; omega⟩

def col {n m : ℕ} (v : Fin m) : Fin (n + m) := ⟨n + v.val, by have := v.isLt; omega⟩

theorem oneEach_bits {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = List.ofFn (bits {row u, col v}) := by
  apply List.ext_getElem (by simp [oneEach])
  intro i hi hj
  rw [← List.getD_eq_getElem _ false hi, ← List.getD_eq_getElem _ false hj, each_value]
  have hlt : i < n + m := by simpa using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hlt, bits, row, col, Fin.ext_iff]

theorem wire_mono {N : ℕ} (C : Circuit) (hC : Monotone2 C) (i : ℕ)
    {S T : Finset (Fin N)} (hs : S ⊆ T) :
    wire N C i (bits S) = true → wire N C i (bits T) = true := by
  apply fold_monotone C.gates (fun g hg => (hC g hg).1) (by simp) _ i
  intro j hj
  by_cases h : j < N
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h,
      Option.getD_some, bits, decide_eq_true_eq] at hj ⊢
    exact hs hj
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg h,
      Option.getD_none, Bool.false_eq_true] at hj

theorem support_all {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hrow : ∀ a : Fin n, ∃ b : Fin n, b ≠ a ∧ ∃ v : Fin m, A a v = true ∧ A b v = false)
    (hcol : ∀ v : Fin m, ∃ w : Fin m, w ≠ v ∧ ∃ a : Fin n, A a v = true ∧ A a w = false)
    (C : Circuit) (hC : Monotone2 C) (hG : Represents A C)
    {L : Finset ℕ} {r : ℕ} (hL : closed (n + m) C L) (hr : r ∈ L)
    (hout : C.output = n + m + r) :
    Finset.range (n + m) ⊆ used (n + m) C L := by
  intro i hi
  have hil := Finset.mem_range.mp hi
  by_cases hin : i < n
  · let a : Fin n := ⟨i, hin⟩
    obtain ⟨b, _, v, ht, hf⟩ := hrow a
    refine needed hC hL hr hout (x := oneEach a v) (y := oneEach b v)
      (by simp [oneEach]) (by simp [oneEach]) i ?_ ((hG a v).trans ht) ((hG b v).trans hf)
    intro w hw
    rw [setD] at hw
    by_cases e : w = i
    · simp [e] at hw
    · simp only [ite_eq_right e, each_value, decide_eq_true_eq] at hw
      rw [each_value, decide_eq_true_eq]
      rcases hw with hw | hw
      · exact (e hw).elim
      · exact Or.inr hw
  · let v : Fin m := ⟨i - n, by omega⟩
    have ev : n + v.val = i := by dsimp [v]; omega
    obtain ⟨w, _, a, ht, hf⟩ := hcol v
    refine needed hC hL hr hout (x := oneEach a v) (y := oneEach a w)
      (by simp [oneEach]) (by simp [oneEach]) i ?_ ((hG a v).trans ht) ((hG a w).trans hf)
    intro j hj
    rw [setD] at hj
    by_cases e : j = i
    · simp [e] at hj
    · simp only [ite_eq_right e, each_value, decide_eq_true_eq, ev] at hj
      rw [each_value, decide_eq_true_eq]
      rcases hj with hj | hj
      · exact Or.inl hj
      · exact (e hj).elim

theorem root_bounds {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hn : 2 ≤ n)
    (hrow : ∀ a : Fin n, ∃ b : Fin n, b ≠ a ∧ ∃ v : Fin m, A a v = true ∧ A b v = false)
    (hcol : ∀ v : Fin m, ∃ w : Fin m, w ≠ v ∧ ∃ a : Fin n, A a v = true ∧ A a w = false)
    (C : Circuit) (hG : Represents A C) :
    n + m ≤ C.output ∧ C.output < n + m + C.gates.length := by
  have raw (u : Fin n) (v : Fin m) (hi : C.output < n + m) :
      C.eval (oneEach u v) = (oneEach u v).getD C.output false := by
    exact pre _ _ _ (by simpa [oneEach] using hi)
  constructor
  · by_contra! h
    by_cases hin : C.output < n
    · let a : Fin n := ⟨C.output, hin⟩
      obtain ⟨b, hne, _, _⟩ := hrow a
      obtain ⟨_, _, v, ht, _⟩ := hrow b
      have he := (hG b v).trans ht
      rw [raw _ _ h, each_value, decide_eq_true_eq] at he
      rcases he with he | he
      · exact hne (Fin.ext he.symm)
      · omega
    · let v : Fin m := ⟨C.output - n, by omega⟩
      have ev : n + v.val = C.output := by dsimp [v]; omega
      obtain ⟨w, hne, _, _⟩ := hcol v
      obtain ⟨_, _, a, ht, _⟩ := hcol w
      have he := (hG a w).trans ht
      rw [raw _ _ h, each_value, decide_eq_true_eq] at he
      rcases he with he | he
      · have := a.isLt; omega
      · exact hne (Fin.ext (by omega))
  · by_contra! h
    let a : Fin n := ⟨0, by omega⟩
    obtain ⟨_, _, v, ht, _⟩ := hrow a
    have he := (hG a v).trans ht
    change (C.gates.foldl step (oneEach a v)).getD C.output false = true at he
    rw [getD_ge _ _ (by rw [len]; simpa [oneEach] using h)] at he
    contradiction

def comparable {ι κ : Type} (A : ι → κ → Bool) (a b : ι) : Prop :=
  (∀ j, A a j = true → A b j = true) ∨ (∀ j, A b j = true → A a j = true)

theorem incomparable_partner {ι κ : Type} [Fintype ι] (A : ι → κ → Bool)
    (hι : 3 ≤ Fintype.card ι)
    (sparse : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (i : ι) : ∃ j, j ≠ i ∧ ¬ comparable A i j := by
  classical
  by_contra! h
  let S := (Finset.univ : Finset ι).erase i
  have hs : 1 < S.card := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hs
  have hai := (Finset.mem_erase.mp ha).1
  have hbi := (Finset.mem_erase.mp hb).1
  exact hab (sparse i a b hai hbi (h a hai) (h b hbi))

theorem line_witness {ι κ : Type} [Fintype ι] (A : ι → κ → Bool)
    (hι : 3 ≤ Fintype.card ι)
    (sparse : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (i : ι) : ∃ k, k ≠ i ∧ ∃ j, A i j = true ∧ A k j = false := by
  obtain ⟨k, hk, hic⟩ := incomparable_partner A hι sparse i
  refine ⟨k, hk, ?_⟩
  by_contra! h
  apply hic
  left
  intro j hj
  by_cases h' : A k j = true
  · exact h'
  · exact False.elim (h j hj (Bool.eq_false_iff.mpr h'))

theorem line_not_full {ι κ : Type} [Fintype ι] (A : ι → κ → Bool)
    (hι : 3 ≤ Fintype.card ι)
    (sparse : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (i : ι) : ¬ ∀ j, A i j = true := by
  intro full
  obtain ⟨k, _, hic⟩ := incomparable_partner A hι sparse i
  exact hic (.inr fun j _ => full j)

theorem deduce_matching {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hrow : Function.Injective A) (hcol : Function.Injective (fun j i => A i j))
    (rowNonempty : ∀ i, ∃ j, A i j = true)
    (colNonempty : ∀ j, ∃ i, A i j = true)
    (rectangle : ∀ a b c d, A a b = true → A c b = true → A c d = true → A a d = true) :
    ∃ e : Fin n ≃ Fin m, ∀ i j, A i j = decide (e i = j) := by
  classical
  have sameRow (i k : Fin n) (j : Fin m) (hi : A i j = true) (hk : A k j = true) : i = k := by
    apply hrow
    funext l
    cases hi' : A i l <;> cases hk' : A k l <;> try rfl
    · exact hi'.symm.trans (rectangle i j k l hi hk hk')
    · exact (rectangle k j i l hk hi hi').symm.trans hk'
  have sameCol (j l : Fin m) (i : Fin n) (hj : A i j = true) (hl : A i l = true) : j = l := by
    apply hcol
    funext k
    change A k j = A k l
    cases hj' : A k j <;> cases hl' : A k l <;> try rfl
    · exact hj'.symm.trans (rectangle k l i j hl' hl hj)
    · exact (rectangle k j i l hj' hj hl).symm.trans hl'
  let f := fun i => Classical.choose (rowNonempty i)
  have hf (i : Fin n) : A i (f i) = true := Classical.choose_spec (rowNonempty i)
  have bij : Function.Bijective f := by
    constructor
    · intro i k h
      exact sameRow i k (f i) (hf i) (h.symm ▸ hf k)
    · intro j
      obtain ⟨i, hi⟩ := colNonempty j
      exact ⟨i, sameCol _ _ _ (hf i) hi⟩
  refine ⟨Equiv.ofBijective f bij, fun i j => ?_⟩
  change A i j = decide (f i = j)
  by_cases h : f i = j
  · simpa [h] using hf i
  · have hh : A i j = false := Bool.eq_false_iff.mpr fun h' => h (sameCol _ _ _ (hf i) h')
    simp [h,hh]

end PEqualNP.Outside.L_meta_26029_aux.Forest

namespace PEqualNP.Outside.L_meta_26029_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity Forest
def Partners {ι κ : Type} (A : ι→κ→Bool) := ∀ i,∃ j,¬comparable A i j
theorem sample {ι κ : Type} {A : ι→κ→Bool} {i k : ι} (nc : ¬comparable A i k) :
    ∃j l,A i j=false ∧ A i l=true ∧ A k j=true ∧ A k l=false := by
  classical
  have a : ¬∀j,A k j=true → A i j=true:=fun e=>nc (Or.inr e)
  have b : ¬∀j,A i j=true → A k j=true:=fun e=>nc (Or.inl e)
  push_neg at a b
  obtain ⟨j,p,q⟩:=a
  obtain ⟨l,r,s⟩:=b
  exact ⟨j,l,Bool.eq_false_iff.mpr q,r,p,Bool.eq_false_iff.mpr s⟩
theorem witness {ι κ : Type} (A : ι→κ→Bool) (partners : Partners A) (i : ι) :
    ∃ k,k≠i ∧ ∃j,A i j=true ∧ A k j=false := by
  obtain ⟨k,nc⟩:=partners i
  obtain ⟨j,l,p,q,r,s⟩:=sample nc
  exact ⟨k,by rintro rfl;rw [q] at s;contradiction,l,q,s⟩
theorem notFull {ι κ : Type} (A : ι→κ→Bool) (partners : Partners A) (i : ι) : ¬∀j,A i j=true := by
  obtain ⟨k,nc⟩:=partners i
  exact fun full=>nc (Or.inr (fun j _=>full j))

theorem tightMono {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hi : Function.Injective A) (hj : Function.Injective (fun j i => A i j))
    (sr : Partners A) (sc : Partners (fun j i=>A i j))
    (C : Circuit) (mono : Monotone2 C) (repr : Represents A C)
    (small : C.size ≤ n + m - 1) :
    n + m - 1 ≤ C.size ∧ ∃ e : Fin n ≃ Fin m, ∀ i j, A i j = decide (e i = j) := by
  have hr := witness A sr
  have hc := witness (fun j i => A i j) sc
  obtain ⟨hraw, hout⟩ := root_bounds (by omega) hr hc C repr
  obtain ⟨hsize, hgate, hback, hread, hvalid, hunread⟩ :=
    output_shape C mono small hraw hout
      (fun L r hL hmem he => support_all hr hc C mono repr hL hmem he)
  refine ⟨le_of_eq hsize.symm, ?_⟩
  obtain ⟨label, hs, _⟩ := label_invariant (n + m) C hgate hback (fun i _ => hread i) _ le_rfl
  let F := wire (n + m) C C.output
  have rect := (hs C.output ⟨hvalid, hunread⟩).2.2.2.2
  have edge_eq (u : Fin n) (v : Fin m) : F (bits {row u, col v}) = A u v := by
    change C.eval (List.ofFn (bits {row u, col v})) = _
    rw [← oneEach_bits]
    exact repr u v
  have rowFalse (u : Fin n) : F (bits ({row u} : Finset (Fin (n + m)))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    apply notFull A sr u
    intro v
    rw [← edge_eq u v]
    exact wire_mono C mono C.output (Finset.singleton_subset_iff.mpr (by simp)) h
  have colFalse (v : Fin m) : F (bits ({col v} : Finset (Fin (n + m)))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    apply notFull (fun j i => A i j) sc v
    intro u
    rw [← edge_eq u v]
    exact wire_mono C mono C.output (Finset.singleton_subset_iff.mpr (by simp)) h
  apply deduce_matching A hi hj
  · intro i
    obtain ⟨_, _, j, hj, _⟩ := hr i
    exact ⟨j, hj⟩
  · intro j
    obtain ⟨_, _, i, hi, _⟩ := hc j
    exact ⟨i, hi⟩
  · intro a b c d hab hcb hcd
    have he (u : Fin n) (v : Fin m) : edge F (row u) (col v) ↔ A u v = true := by
      unfold edge
      rw [edge_eq]
    exact (he a d).1 (rect (row a) (col b) (row c) (col d) (rowFalse a) (colFalse b)
      (rowFalse c) (colFalse d) ((he a b).2 hab) ((he c b).2 hcb) ((he c d).2 hcd))

end PEqualNP.Outside.L_meta_26029_aux

namespace PEqualNP.Outside.L_meta_26029_aux
open Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical
def HasNot (C : Circuit) := ∃g∈C.gates,g.op=GateOp.not
theorem fullCost {N : Nat} (hn : 0<N) (C : Circuit) (fan : FanInTwo C) (hnot : HasNot C)
    (all : ∀i : Fin N,active C i) : N≤C.size := by
  let i : Fin N:=⟨0,hn⟩
  obtain ⟨x,h⟩:=all i
  let g : Fin 1→Fin N:=fun _=>i
  have inj : Function.Injective g:=fun _ _ _=>Subsingleton.elim _ _
  have plugVal (v : Bool) : plug g x (fun _=>v)=Function.update x i v := by
    funext w
    by_cases e:w=i
    · subst w;rw [Function.update_self];exact onWire g x inj (fun _=>v) 0
    · have off : w∉Finset.univ.image g:=by simpa [g] using e
      unfold plug
      rw [if_neg off,Function.update_of_ne e]
  have varies : ∃a b,fn C (plug g x a) ≠ fn C (plug g x b) := ⟨fun _=>false,fun _=>true,by rwa [plugVal,plugVal]⟩
  obtain ⟨D,_,cost,_,_⟩:=signedRestriction C fan g x inj (fn C) (fun _=>rfl) varies
  have ec : ((Finset.univ : Finset (Fin N)).filter (fun i=>∃y,fn C (Function.update y i false)≠fn C (Function.update y i true))).card=N := by
    have a (j : Fin N) : ∃y,fn C (Function.update y j false)≠fn C (Function.update y j true):=all j
    simp [a]
  rw [ec,(costs C).2] at cost
  obtain ⟨z,mz,ez⟩:=hnot
  have mem : z∈C.gates.filter (fun a=>decide (a.op=GateOp.not)):=List.mem_filter.mpr ⟨mz,by simp [ez]⟩
  have pos:=List.length_pos_of_mem mem
  have le : (C.gates.filter (fun a=>decide (a.op=GateOp.not))).length≤C.size:=List.length_filter_le _ _
  omega
theorem boundary {n m : Nat} (hn : 3 ≤ n) (hm : 3 ≤ m) (A : Fin n→Fin m→Bool)
    (di : Function.Injective A) (dj : Function.Injective (fun j i=>A i j))
    (ri : Partners A) (cj : Partners (fun j i=>A i j)) (C : Circuit) (fan : FanInTwo C)
    (rep : Represents A C) (small : C.size≤n+m-1) : C.size=n+m-1 ∧ (HasNot C→
      ∃(r : Fin n) (c : Fin m), ¬active C (left m r) ∧ ¬active C (right n c) ∧ n+m≤(E (n+m) C).card+2) := by
  classical
  let R : Fin n→Fin (n+m):=left m
  let K : Fin m→Fin (n+m):=right n
  have sep (i : Fin n) (j : Fin m) : R i≠K j := by intro e;have q:=congrArg Fin.val e;change i.val=n+j.val at q;omega
  have repR (i : Fin n) (j : Fin m) : fn C (two (R i) (K j)) = A i j := atPair rep i j
  have repK (i : Fin m) (j : Fin n) : fn C (two (K i) (R j)) = A j i := by
    rw [show two (K i) (R j)=two (R j) (K i) by funext w;simp only [two,or_comm]]
    exact repR _ _
  let S:=E (n+m) C
  let L:=Finset.univ.filter fun i=>¬active C (R i)
  let J:=Finset.univ.filter fun i=>¬active C (K i)
  have ll : L.card≤1:=atMostOne R K sep A C repR di
  have jj : J.card≤1:=atMostOne K R (fun i j=>(sep j i).symm) (fun j i=>A i j) C repK dj
  have cover : Finset.univ⊆(S ∪ L.image R) ∪ J.image K := by
    intro w _
    by_cases a : active C w
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a⟩))
    induction w using Fin.addCases with
    | left i => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a⟩,rfl⟩))
    | right i => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a⟩,rfl⟩)
  have count:=(Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have lb:=Finset.card_union_le S (L.image R)
  have lc:=Finset.card_image_le (s:=L) (f:=R)
  have jc:=Finset.card_image_le (s:=J) (f:=K)
  simp only [Finset.card_univ,Fintype.card_fin] at count
  have price (i : Fin (n+m)) (off : ¬active C i) : S.card+1≤C.size := by
    induction i using Fin.addCases with
    | left r =>
      obtain ⟨q,nc⟩:=ri r
      obtain ⟨j,l,p0,p1,q1,q0⟩:=sample nc
      exact priceRow R K (fun _ _ e=>Fin.ext (by have h:=congrArg Fin.val e;dsimp [K,right] at h;omega)) sep A C fan repR r q j l off p0 p1 q1 q0
    | right c =>
      obtain ⟨q,nc⟩:=cj c
      obtain ⟨j,l,p0,p1,q1,q0⟩:=sample nc
      exact priceRow K R (fun i j e=>Fin.ext (show i.val=j.val from congrArg (fun w : Fin (n+m)=>w.val) e)) (fun i j=>(sep j i).symm) (fun j i=>A i j) C fan repK c q j l off p0 p1 q1 q0
  by_cases full : ∀i : Fin (n+m),active C i
  · have lo:=essentialsCost (N:=n+m) (by omega) C fan full
    exact ⟨by omega,fun h=>False.elim (by have t:=fullCost (N:=n+m) (by omega) C fan h full;omega)⟩
  push_neg at full
  obtain ⟨i,off⟩:=full
  have saved:=price i off
  have lr : 0<L.card:=by omega
  have jr : 0<J.card:=by omega
  obtain ⟨r,hr⟩:=Finset.card_pos.mp lr
  obtain ⟨c,hc⟩:=Finset.card_pos.mp jr
  exact ⟨by omega,fun _=>⟨r,c,(Finset.mem_filter.mp hr).2,(Finset.mem_filter.mp hc).2,by change n+m≤S.card+2;omega⟩⟩
end PEqualNP.Outside.L_meta_26029_aux

namespace PEqualNP.Outside.L_meta_26029_aux
open Small
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical

structure Frame {n m : Nat} (A : Fin n→Fin m→Bool) where
  N : Nat
  C : Circuit
  R : Fin n→Fin N
  K : Fin m→Fin N
  ir : Function.Injective R
  ic : Function.Injective K
  sep : ∀i j,R i≠K j
  r0 : Fin n
  c0 : Fin m
  orow : ¬active C (R r0)
  ocol : ¬active C (K c0)
  eval : ∀i j,fn C (two (R i) (K j))=A i j
  fan : FanInTwo C
  price : C.size≤(E N C).card+1

def Frame.swap {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) : Frame (fun j i=>A i j) where
  N:=F.N
  C:=F.C
  R:=F.K
  K:=F.R
  ir:=F.ic
  ic:=F.ir
  sep:=fun j i=>(F.sep i j).symm
  r0:=F.c0
  c0:=F.r0
  orow:=F.ocol
  ocol:=F.orow
  eval:=fun j i=>by rw [show two (F.K j) (F.R i)=two (F.R i) (F.K j) by funext w;simp only [two,or_comm]];exact F.eval i j
  fan:=F.fan
  price:=F.price

theorem dropRaw {n : Nat} {C : Circuit} {p : Fin n} (off : ¬active C p) (x : Fin n→Bool) :
    fn C (Function.update x p false)=fn C x := by
  have e:=not_exists.mp off x
  rw [not_not] at e
  cases b:x p with
  | true => rw [← b,Function.update_eq_self] at e;exact e
  | false => rw [← b,Function.update_eq_self]

def code {a b : Nat} (i : Fin (a+1)) (j : Fin (b+1)) : Fin (a+b)→Bool :=
  Fin.addCases (fun k=>decide (k.succ=i)) (fun k=>decide (k.succ=j))
def sampled {a b : Nat} (N : Nat) (u : Fin (a+1)→Fin N) (v : Fin (b+1)→Fin N) : Fin (a+b)→Fin N :=
  Fin.addCases (fun k=>u k.succ) (fun k=>v k.succ)
theorem sampleInj {a b N : Nat} (u : Fin (a+1)→Fin N) (v : Fin (b+1)→Fin N) (iu : Function.Injective u) (iv : Function.Injective v)
    (sep : ∀i j,u i≠v j) : Function.Injective (sampled N u v) := by
  intro i j h
  induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp only [sampled,Fin.addCases_left,Fin.addCases_right] at h
  · exact congrArg (Fin.castAdd b) (Fin.succ_injective _ (iu h))
  · exact (sep _ _ h).elim
  · exact (sep _ _ h.symm).elim
  · exact congrArg (Fin.natAdd a) (Fin.succ_injective _ (iv h))
theorem masked {a b N : Nat} (u : Fin (a+1)→Fin N) (v : Fin (b+1)→Fin N) (iu : Function.Injective u) (iv : Function.Injective v)
    (sep : ∀i j,u i≠v j) (i : Fin (a+1)) (j : Fin (b+1)) :
    plug (sampled N u v) (fun _=>false) (code i j) =
      Function.update (Function.update (two (u i) (v j)) (u 0) false) (v 0) false := by
  classical
  let g:=sampled N u v
  have gi:=sampleInj u v iu iv sep
  funext w
  by_cases hit : w∈Finset.univ.image g
  · obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hit
    rw [onWire _ _ gi]
    induction k using Fin.addCases with
    | left k =>
      simp only [g,sampled,Fin.addCases_left]
      simp [code,Function.update_of_ne (sep _ _),Function.update_of_ne (fun h=>Fin.succ_ne_zero _ (iu h)),two,iu.eq_iff,sep]
    | right k =>
      simp only [g,sampled,Fin.addCases_right]
      simp [code,Function.update_of_ne (fun h=>Fin.succ_ne_zero _ (iv h)),Function.update_of_ne (Ne.symm (sep _ _)),two,iv.eq_iff,fun i j=>(sep i j).symm]
  · change plug g _ _ w=_
    rw [plug,if_neg hit]
    by_cases a0:w=u 0
    · subst w;simp [Function.update_of_ne (sep _ _)]
    by_cases b0:w=v 0
    · subst w;simp
    rw [Function.update_of_ne b0,Function.update_of_ne a0]
    have ru : w≠u i := by
      intro e
      cases i using Fin.cases with
      | zero => exact a0 e
      | succ k => exact hit (Finset.mem_image.mpr ⟨Fin.castAdd b k,Finset.mem_univ _,by simpa [g,sampled] using e.symm⟩)
    have cv : w≠v j := by
      intro e
      cases j using Fin.cases with
      | zero=> exact b0 e
      | succ k=>exact hit (Finset.mem_image.mpr ⟨Fin.natAdd a k,Finset.mem_univ _,by simpa [g,sampled] using e.symm⟩)
    simp [two,ru,cv]
theorem projected {n m a b : Nat} {A : Fin n→Fin m→Bool} (F : Frame A)
    (x : Fin (a+1)→Fin n) (y : Fin (b+1)→Fin m) (ix : Function.Injective x) (iy : Function.Injective y)
    (ox : x 0=F.r0) (oy : y 0=F.c0)
    (varies : ∃i k j l,A (x i) (y j)≠A (x k) (y l)) :
    ∃D : Circuit, FanInTwo D ∧ D.size≤a+b+1 ∧ ∀i j,fn D (code i j)=A (x i) (y j) := by
  let u:=F.R ∘ x
  let v:=F.K ∘ y
  have iu:=F.ir.comp ix
  have iv:=F.ic.comp iy
  have sep (i j) : u i≠v j:=F.sep _ _
  let g:=sampled F.N u v
  have ev (i j) : fn F.C (plug g (fun _=>false) (code i j))=A (x i) (y j) := by
    rw [masked u v iu iv sep]
    have ou : ¬active F.C (u 0) := by simpa [u,ox] using F.orow
    have ov : ¬active F.C (v 0) := by simpa [v,oy] using F.ocol
    rw [dropRaw ov,dropRaw ou];exact F.eval _ _
  obtain ⟨i,k,j,l,neq⟩:=varies
  obtain ⟨D,fan,price,rep⟩:=charge F.C F.fan g (sampleInj u v iu iv sep) (fun _=>false)
    (show ∃v w,fn F.C (plug g (fun _=>false) v)≠fn F.C (plug g (fun _=>false) w) from
      ⟨code i j,code k l,by rwa [ev,ev]⟩)
  exact ⟨D,fan,by have :=F.price;omega,fun i j=>(rep _).trans (ev i j)⟩

def table (r c : Nat) (M : Nat) (i : Fin r) (j : Fin c) : Bool := M.testBit (c*i.val+j.val)

theorem exclude {w n m a b k : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (M : Nat)
    (raw : List (BitVec w)) (T : BitVec w) (nz : T≠0)
    (ban : Small.Check.can true T k (0::BitVec.allOnes w::raw)=false)
    (budget : a+b+1≤k)
    (target : ∀l : Fin w,∃i : Fin (a+1),∃j : Fin (b+1),raw.map (Small.Check.bit l.val)=List.ofFn (code i j) ∧
       Small.Check.bit l.val T=table _ _ M i j)
    (diffR : Function.Injective (table (a+1) (b+1) M)) (diffC : Function.Injective (fun j i=>table (a+1) (b+1) M i j))
    (varies : ∃i k j l,table (a+1) (b+1) M i j≠table (a+1) (b+1) M k l)
    (x : Fin (a+1)→Fin n) (y : Fin (b+1)→Fin m) (ox : x 0=F.r0) (oy : y 0=F.c0) :
    ¬∀i j,A (x i) (y j)=table _ _ M i j := by
  intro eqT
  have rx : Function.Injective x := by
    intro i k he;apply diffR;funext j;rw [←eqT,←eqT,he]
  have cy : Function.Injective y := by
    intro j l he;apply diffC;funext i;exact (eqT i j).symm.trans ((congrArg (A (x i)) he).trans (eqT i l))
  obtain ⟨i,k',j,l,diff⟩:=varies
  obtain ⟨D,fan,size,rep⟩:=projected F x y rx cy ox oy ⟨i,k',j,l,by simpa only [eqT] using diff⟩
  have seen:=Small.Check.readout true D raw (0::BitVec.allOnes w::raw) k
    (fun g h=>by simpa using (fan g h).1) (fun g h=>(fan g h).2)
    (fun v m=>by simp [m]) List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) (size.trans budget) T nz
    (fun q=>by obtain ⟨r,c,eq,tw⟩:=target q;rw [eq,tw,←eqT];exact rep r c)
  exact Bool.noConfusion (ban.symm.trans seen)
end PEqualNP.Outside.L_meta_26029_aux

namespace PEqualNP.Outside.L_meta_26029_aux.CheckGroups
theorem join {α : Type} (xs : List α) (size : Nat) (f : α → Bool)
    (a : (xs.take size).any f=false) (b : (xs.drop size).any f=false) : xs.any f=false := by
  calc
    xs.any f = ((xs.take size)++(xs.drop size)).any f := congrArg (fun ys : List α=>ys.any f) (List.take_append_drop size xs).symm
    _ = false := by simp only [List.any_append,a,b,Bool.or_self]
end PEqualNP.Outside.L_meta_26029_aux.CheckGroups

namespace PEqualNP.Outside.L_meta_26029_aux.LiveSigned
open Small.Check
variable {w : Nat}
abbrev V (w : Nat) := BitVec w
inductive Takes : Finset (V w) → V w → Prop
  | inv (a : V w) : Takes {a} (~~~a)
  | conj (a b : V w) (h : a ≠ b) : Takes {a,b} (a &&& b)
  | disj (a b : V w) (h : a ≠ b) : Takes {a,b} (a ||| b)

def live (t : V w) : Nat → Finset (V w) → Prop
  | 0,s => s={t}
  | k+1,s => live t k s ∨ ∃ p z r, Takes p z ∧ z ∉ s ∧ s=p∪r ∧ live t k (insert z r)

theorem growLive {t : V w} {k : Nat} {B : List (V w)} {z : V w}
    (opt : z∈options true B) (s : Finset (V w)) (ss : s⊆(z::B).toFinset) (cont : live t k s) :
    ∃o⊆B.toFinset, live t (k+1) o := by
  by_cases sub : s⊆B.toFinset
  · exact ⟨_,sub,Or.inl cont⟩
  have mz : z∈s := by
    by_contra hn
    exact sub (by intro u m; have e:=ss m; simp only [List.toFinset_cons,Finset.mem_insert] at e
                  exact e.resolve_left (by rintro rfl;exact hn m))
  have nz : z∉B := by
    intro h; apply sub; simpa [Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)] using ss
  let r:=s.erase z
  have rs : r⊆B.toFinset := by
    intro u hu
    have m:=Finset.mem_erase.mp hu
    have f:=ss m.2
    rw [List.toFinset_cons] at f
    exact (Finset.mem_insert.mp f).resolve_left m.1
  have hit {p : Finset (V w)} (inB : p⊆B.toFinset) (step : Takes p z) :
      ∃o⊆B.toFinset, live t (k+1) o := by
    have subo := Finset.union_subset inB rs
    refine ⟨p∪r,subo,Or.inr ⟨p,z,r,step,fun h=>nz (List.mem_toFinset.mp (subo h)),rfl,?_⟩⟩
    simpa [r,Finset.insert_erase mz] using cont
  simp only [options,List.mem_eraseDups,List.mem_append,List.mem_flatMap,List.mem_cons,
    List.not_mem_nil,or_false,if_true,List.mem_map] at opt
  rcases opt with ⟨a,ha,b,hb,e|e⟩|⟨a,ha,e⟩
  · subst z
    have ne : a ≠ b := by rintro rfl;exact nz (by simpa using ha)
    exact hit (p:={a,b}) (Finset.insert_subset (List.mem_toFinset.mpr ha) (Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hb))) (.conj a b ne)
  · subst z
    have ne : a ≠ b := by rintro rfl;exact nz (by simpa using ha)
    exact hit (p:={a,b}) (Finset.insert_subset (List.mem_toFinset.mpr ha) (Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hb))) (.disj a b ne)
  · subst z
    exact hit (p:={a}) (by simp [ha]) (.inv a)

theorem compress {t : V w} (k : Nat) (B : List (V w)) (run : can true t k B=true) :
    ∃s⊆B.toFinset, live t k s := by
  induction k generalizing B with
  | zero => exact ⟨{t},Finset.singleton_subset_iff.mpr (by simpa [can] using run),rfl⟩
  | succ k ih =>
    have old (h : t∈B) : ∃s⊆B.toFinset,live t (k+1) s := by
      have base : ∀k,live t k {t} := by intro k; induction k with | zero=>rfl | succ _ ih=>exact Or.inl ih
      exact ⟨{t},by simp [h],base _⟩
    rw [can,Bool.or_eq_true,List.contains_iff_mem,List.any_eq_true] at run
    rcases run with h|⟨z,hz,go⟩
    · exact old h
    split_ifs at go with mem
    · obtain ⟨s,ss,h⟩:=ih B go;exact ⟨s,ss,Or.inl h⟩
    obtain ⟨s,ss,h⟩:=ih (z::B) go
    exact growLive hz s ss h

theorem liveCard {t : V w} {k : Nat} {s : Finset (V w)} (h : live t k s) : s.card≤k+1 := by
  induction k generalizing s with
  | zero=>change s={t} at h;simp [h]
  | succ k ih=>
    rcases h with skip|⟨p,z,r,op,hz,rfl,cont⟩
    · exact (ih skip).trans (by omega)
    have nz : z∉r := by intro m;exact hz (Finset.mem_union_right _ m)
    have bound:=ih cont
    rw [Finset.card_insert_of_notMem nz] at bound
    have pc : p.card ≤ 2 := by
      cases op with
      | inv a=>simp
      | conj a b h | disj a b h=>simp [h]
    have := Finset.card_union_le p r
    omega

def sep (p : Nat) (v : V w) := (v.toNat ^^^ (v.toNat >>> p)) &&& (2^p-1)
def cover (p : Nat) (ws : List (V w)) := ws.foldr (fun v z=>sep p v ||| z) 0
def diff (p i : Nat) (v : V w) := v.getLsbD i ≠ v.getLsbD (p+i)
instance diffDec (p i : Nat) (v : V w) : Decidable (diff p i v) := by
  unfold diff
  infer_instance
theorem sep_iff (p i : Nat) (v : V w) (hi : i<p) :
    (sep p v).testBit i=true ↔ diff p i v := by
  simp [sep,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one,hi,diff,BitVec.getLsbD, Nat.add_comm i p]
theorem cover_iff (p i : Nat) (hi : i<p) (ws : List (V w)) :
    (cover p ws).testBit i=true ↔ ∃v∈ws,diff p i v := by
  induction ws with
  | nil=>simp [cover]
  | cons a l ih=>
    change ((sep p a ||| cover p l).testBit i=true) ↔ _
    simp [Nat.testBit_or,sep_iff p i a hi,ih]

theorem sepLive {p i : Nat} {t : V w} {k : Nat} {s : Finset (V w)}
    (h : live t k s) (different : diff p i t) (bound : p+i<w) : ∃v∈s,diff p i v := by
  induction k generalizing s with
  | zero=>change s={t} at h;exact ⟨t,by simp [h],different⟩
  | succ k ih=>
    rcases h with skip|⟨xs,z,r,op,_,rfl,cont⟩
    · exact ih skip
    obtain ⟨v,m,hv⟩:=ih cont
    rcases Finset.mem_insert.mp m with rfl|mm
    · cases op with
      | inv a=>
        exact ⟨a,by simp,fun eq=>hv (by simp only [BitVec.getLsbD_not,decide_eq_true bound,decide_eq_true (show i<w by omega),Bool.true_and,eq])⟩
      | conj a b _=>
        by_cases ea:diff p i a
        · exact ⟨a,by simp,ea⟩
        exact ⟨b,by simp,fun eq=>hv (by simp [diff,BitVec.getLsbD_and,not_ne_iff.mp ea,eq])⟩
      | disj a b _=>
        by_cases ea:diff p i a
        · exact ⟨a,by simp,ea⟩
        exact ⟨b,by simp,fun eq=>hv (by simp [diff,BitVec.getLsbD_or,not_ne_iff.mp ea,eq])⟩
    · exact ⟨v,Finset.mem_union_right _ mm,hv⟩

theorem coverLive {p : Nat} {t : V w} {k : Nat} {ws : List (V w)}
    (h : live t k ws.toFinset) (dif : ∀i<p,diff p i t) (width : 2*p≤w) :
    (cover p ws &&& (2^p-1)) = 2^p-1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and,Nat.testBit_two_pow_sub_one]
  by_cases hi:i<p
  · obtain ⟨v,m,dv⟩:=sepLive h (dif i hi) (by omega)
    simp [hi,(cover_iff p i hi ws).mpr ⟨v,List.mem_toFinset.mp m,dv⟩]
  · simp [hi]

end PEqualNP.Outside.L_meta_26029_aux.LiveSigned
namespace PEqualNP.Outside.L_meta_26029_aux.LiveSigned

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

end PEqualNP.Outside.L_meta_26029_aux.LiveSigned
namespace PEqualNP.Outside.L_meta_26029_aux.LiveSigned
variable {w : Nat}
def rising (p i : Nat) (v : V w) := v.getLsbD i=false ∧ v.getLsbD (p+i)=true
instance risingDec (p i : Nat) (v : V w) : Decidable (rising p i v) := by
  unfold rising
  infer_instance
def rises (p : Nat) (v : V w) := (v.toNat >>> p) &&& (v.toNat ^^^ (2^p-1))
def ups (p : Nat) (ws : List (V w)) := ws.foldr (fun v z=>rises p v ||| z) 0
theorem rises_iff (p i : Nat) (v : V w) (hi : i<p) :
    (rises p v).testBit i=true ↔ rising p i v := by
  simp [rises,rising,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one,
    hi,BitVec.getLsbD,Nat.add_comm i p,and_comm]
theorem ups_iff (p i : Nat) (ws : List (V w)) (hi : i<p) :
    (ups p ws).testBit i=true ↔ ∃v∈ws,rising p i v := by
  induction ws with
  | nil=>simp [ups]
  | cons a l ih=>change ((rises p a ||| ups p l).testBit i=true) ↔ _;simp [Nat.testBit_or,rises_iff p i a hi,ih]
theorem risingGate {p i : Nat} {a b : V w} (s : Bool)
    (h : rising p i (if s then a ||| b else a &&& b)) : rising p i a ∨ rising p i b := by
  cases s <;> simp only [rising,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] at h ⊢ <;>
    cases ha : a.getLsbD i <;> cases hA : a.getLsbD (p+i) <;>
    cases hb : b.getLsbD i <;> cases hB : b.getLsbD (p+i) <;> simp_all

theorem riseLive {p i : Nat} {t : V w} {k : Nat} {s : Finset (V w)}
    (h : live t k s) (tight : s.card=k+1) (up : rising p i t) : ∃v∈s,rising p i v := by
  induction k generalizing s with
  | zero=>change s={t} at h;exact ⟨t,by simp [h],up⟩
  | succ k ih=>
    rcases h with skip|⟨xs,z,r,op,nz,rfl,cont⟩
    · have := liveCard skip;omega
    have hr:= liveCard cont
    have zr : z∉r := fun m=>nz (Finset.mem_union_right _ m)
    rw [Finset.card_insert_of_notMem zr] at hr
    have hu:=Finset.card_union_le xs r
    have hc : xs.card≤2 := by
      cases op with
      | inv a=>simp
      | conj a b ne | disj a b ne=>simp [ne]
    have two : xs.card=2 := by omega
    have eq : (insert z r).card=k+1 := by rw [Finset.card_insert_of_notMem zr];omega
    obtain ⟨v,m,hv⟩:=ih cont eq
    rcases Finset.mem_insert.mp m with rfl|mm
    · cases op with
      | inv a=>simp at two
      | conj a b ne=>
        rcases risingGate (a:=a) (b:=b) false hv with ha|hb
        · exact ⟨a,by simp,ha⟩
        · exact ⟨b,by simp,hb⟩
      | disj a b ne=>
        rcases risingGate (a:=a) (b:=b) true hv with ha|hb
        · exact ⟨a,by simp,ha⟩
        · exact ⟨b,by simp,hb⟩
    · exact ⟨v,Finset.mem_union_right _ mm,hv⟩
theorem upLive {p : Nat} {t : V w} {k : Nat} {ws : List (V w)}
    (h : live t k ws.toFinset) (up : ∀i<p,rising p i t) (tight : ws.toFinset.card=k+1) :
    (ups p ws &&& (2^p-1)) = 2^p-1 := by
  apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,Nat.testBit_two_pow_sub_one]
  by_cases hi:i<p
  · obtain ⟨v,m,pos⟩:=riseLive h tight (up i hi)
    simp [hi,(ups_iff p i ws hi).mpr ⟨v,List.mem_toFinset.mp m,pos⟩]
  · simp [hi]
end PEqualNP.Outside.L_meta_26029_aux.LiveSigned
namespace PEqualNP.Outside.L_meta_26029_aux.LiveSigned
open Small.Check
variable {w : Nat}

theorem keepOne {ws r : List (V w)} {a : V w} {need : Finset (V w)}
    (hp : ws.Perm (a::r)) (hn : ws.Nodup) (hs : ws.toFinset=insert a need) :
    ∃kept ∈ [r, a::r],kept.Nodup ∧ kept.toFinset=need := by
  have ha := hp.nodup_iff.mp hn
  have er : ws.toFinset = insert a r.toFinset := by ext v; simp [hp.mem_iff]
  by_cases h : a∈need
  · refine ⟨a::r,by simp,ha,?_⟩
    simpa [h] using er.symm.trans hs
  · refine ⟨r,by simp,(List.nodup_cons.mp ha).2,?_⟩
    ext v
    have e : v∈insert a r.toFinset ↔ v∈insert a need := by rw [←er,hs]
    by_cases same:v=a
    · subst v;simp [h,(List.nodup_cons.mp ha).1]
    · simpa [same] using e

def extend (ws : List (V w)) (next : List (V w) → Bool) (z : V w) (tails : List (List (V w))) :=
  !ws.contains z && tails.any (fun r=>next (z::r))

def guess (p : Nat) (t : V w) : Nat → List (V w) → Bool
  | 0,ws=>ws.contains t
  | k+1,ws=>
    ws.contains t ||
    ((decide (ws.length ≤ k+2) && ((cover p ws &&& (2^p-1) == 2^p-1) && (ws.length != k+2 || (ups p ws &&& (2^p-1) == 2^p-1)))) &&
      ((singles ws).any (fun (a,r)=> extend ws (guess p t k) (~~~a) [r,a::r]) ||
       (pairs ws).any (fun (a,b,r)=>
         extend ws (guess p t k) (a &&& b) (keepChoices a b r) ||
         extend ws (guess p t k) (a ||| b) (keepChoices a b r))))

theorem first {t : V w} {k : Nat} {s : Finset (V w)} (h : live t (k+1) s) :
    s={t} ∨ ∃p z r,Takes p z ∧ z∉s ∧ s=p∪r ∧ live t k (insert z r) := by
  induction k with
  | zero=>exact h
  | succ k ih=>
    rcases h with skip|step
    · rcases ih skip with done|⟨p,z,r,op,nz,eq,cont⟩
      · exact Or.inl done
      · exact Or.inr ⟨p,z,r,op,nz,eq,Or.inl cont⟩
    · exact Or.inr step

theorem guess_live {t : V w} {p : Nat} (dif : ∀i<p,diff p i t) (width : 2*p≤w) (up : ∀i<p,rising p i t)
    (k : Nat) (ws : List (V w)) (nod : ws.Nodup) (L : live t k ws.toFinset) : guess p t k ws=true := by
  induction k generalizing ws with
  | zero=>
    change ws.toFinset={t} at L
    exact List.contains_iff_mem.mpr (List.mem_toFinset.mp (L ▸ Finset.mem_singleton_self t))
  | succ k ih=>
    rw [guess,Bool.or_eq_true]
    rcases first L with done|⟨pars,z,r,op,nz,eq,cont⟩
    · exact Or.inl (List.contains_iff_mem.mpr (List.mem_toFinset.mp (done ▸ Finset.mem_singleton_self t)))
    apply Or.inr
    have bound:=liveCard L
    rw [List.toFinset_card_of_nodup nod] at bound
    have caps : (decide (ws.length ≤ k+2) && ((cover p ws &&& (2^p-1) == 2^p-1) && (ws.length != k+2 || (ups p ws &&& (2^p-1) == 2^p-1))))=true := by
      by_cases q:ws.length=k+2
      · have tight : ws.toFinset.card=k+2 := by rw [List.toFinset_card_of_nodup nod,q]
        simp [q,coverLive L dif width,upLive L up tight]
      · simp [q,show ws.length≤k+2 by omega,coverLive L dif width]
    rw [caps,Bool.true_and,Bool.or_eq_true]
    have extendOK (tails : List (List (V w))) (good : ∃kept∈tails,kept.Nodup ∧ kept.toFinset=r) :
        extend ws (guess p t k) z tails=true := by
      obtain ⟨kept,mem,nd,eqr⟩:=good
      have zr : z∉r := fun m=>nz (eq ▸ Finset.mem_union_right _ m)
      have zk : z∉kept := fun m=>zr (eqr ▸ List.mem_toFinset.mpr m)
      have hl : live t k (z::kept).toFinset := by simpa [eqr] using cont
      have yes:=ih (z::kept) (List.nodup_cons.mpr ⟨zk,nd⟩) hl
      have nw : z∉ws:=fun m=>nz (List.mem_toFinset.mpr m)
      simpa [extend,nw] using (List.any_eq_true.mpr ⟨kept,mem,yes⟩ :
        tails.any (fun kept=>guess p t k (z::kept))=true)
    cases op with
    | inv a=>
      have hs : ws.toFinset=insert a r := by simpa using eq
      obtain ⟨rest,mem,perm⟩:=pick_one (ws:=ws) (a:=a) (List.mem_toFinset.mp (hs ▸ Finset.mem_insert_self ..))
      exact Or.inl (List.any_eq_true.mpr ⟨(a,rest),mem,extendOK _ (keepOne perm nod hs)⟩)
    | conj a b ne | disj a b ne=>
      all_goals
        have hs : ws.toFinset=insert a (insert b r) := by simpa using eq
        have am : a∈ws := List.mem_toFinset.mp (hs ▸ Finset.mem_insert_self ..)
        have bm : b∈ws := List.mem_toFinset.mp (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
        obtain ⟨rest,pos,perm⟩:=pick_two am bm ne
        apply Or.inr
        apply List.any_eq_true.mpr
        rcases pos with pos|pos
        · refine ⟨(a,b,rest),pos,?_⟩
          first | exact Bool.or_eq_true_iff.mpr (Or.inl (extendOK _ (recover_kept perm nod hs)))
                | exact Bool.or_eq_true_iff.mpr (Or.inr (extendOK _ (recover_kept perm nod hs)))
        · refine ⟨(b,a,rest),pos,?_⟩
          have sw := recover_kept (perm.trans (List.Perm.swap ..)) nod (hs.trans (Finset.insert_comm ..))
          first | exact Bool.or_eq_true_iff.mpr (Or.inl (by simpa only [BitVec.and_comm b a] using extendOK _ sw))
                | exact Bool.or_eq_true_iff.mpr (Or.inr (by simpa only [BitVec.or_comm b a] using extendOK _ sw))

def search (p : Nat) (t : V w) (k : Nat) (inputs : List (V w)) :=
  inputs.sublists.any (guess p t k)
theorem checked (p : Nat) (t : V w) (k : Nat) (inputs : List (V w)) (nod : inputs.Nodup)
    (dif : ∀i : Fin p,diff p i.val t) (width : 2*p≤w) (up : ∀i : Fin p,rising p i.val t) (test : search p t k inputs=false) : can true t k inputs=false := by
  apply Bool.eq_false_iff.mpr;intro yes
  obtain ⟨s,ss,hl⟩:=compress k inputs yes
  let ws:=inputs.filter (· ∈ s)
  have eq : ws.toFinset=s := by
    ext x
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun h=>List.mem_toFinset.mp (ss h)
  have nd : ws.Nodup := nod.filter _
  have ok:=guess_live (fun i hi=>dif ⟨i,hi⟩) width (fun i hi=>up ⟨i,hi⟩) k ws nd (eq.symm ▸ hl)
  have y : search p t k inputs=true := List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),ok⟩
  exact Bool.noConfusion (test.symm.trans y)
end PEqualNP.Outside.L_meta_26029_aux.LiveSigned

namespace PEqualNP.Outside.L_meta_26029_aux
open Small
structure Rule where
  a : Nat
  b : Nat
  M : Nat
  deriving DecidableEq
def rules : List Rule := [⟨1,1,6⟩,⟨1,1,9⟩,⟨1,2,29⟩,⟨2,2,172⟩,⟨2,3,616⟩,⟨2,3,710⟩,⟨2,3,584⟩,⟨2,3,620⟩,⟨2,3,1708⟩,⟨2,3,740⟩]
def Avoids {n m : Nat} (A : Fin n→Fin m→Bool) (r : Fin n) (c : Fin m) (rule : Rule) :=
  ∀(x : Fin (rule.a+1)→Fin n) (y : Fin (rule.b+1)→Fin m),x 0=r → y 0=c →
    ¬∀i j,A (x i) (y j)=table _ _ rule.M i j
def Laws {n m : Nat} (A : Fin n→Fin m→Bool) (r : Fin n) (c : Fin m) :=
  ∀rule∈rules,Avoids A r c rule ∧ Avoids (fun j i=>A i j) c r rule
theorem lawsMap {n m u v : Nat} {A : Fin n→Fin m→Bool} {r : Fin n} {c : Fin m} (law : Laws A r c)
    (x : Fin (u+1)→Fin n) (y : Fin (v+1)→Fin m) (ox : x 0=r) (oy : y 0=c) :
    Laws (fun i j=>A (x i) (y j)) 0 0 := by
  intro q mq
  obtain ⟨h,k⟩:=law q mq
  constructor
  · intro a b ha hb;exact h (x ∘ a) (y ∘ b) (by simp [ha,ox]) (by simp [hb,oy])
  · intro a b ha hb;exact k (y ∘ a) (x ∘ b) (by simp [ha,oy]) (by simp [hb,ox])
def raw0 : List (BitVec 8) := [172, 92]
def tar0 : BitVec 8 := 240
def raw1 : List (BitVec 8) := [172, 163]
def tar1 : BitVec 8 := 240
def raw2 : List (BitVec 16) := [52464, 34831, 8944]
def tar2 : BitVec 16 := 65280
def raw3 : List (BitVec 40) := [439804235520, 586406686720, 586405646320, 366504509440]
def tar3 : BitVec 40 := 1099510579200
def raw4 : List (BitVec 64) := [7378697627766878208, 9838263507981697024, 12297829379609723120, 4919131752095551232, 1229782941988487168]
def tar4 : BitVec 64 := 18446744069414584320
def raw5 : List (BitVec 70) := [457003208006343588864, 609337610709482078208, 647421211342319616000, 228501604004211458048, 304668805370847691744]
def tar5 : BitVec 70 := 1180591620683051565056
def raw6 : List (BitVec 54) := [5146970964622848, 10293942062678016, 10293941928751160, 5146970979041728, 2573485599850496]
def tar6 : BitVec 54 := 18014398375264256
def raw7 : List (BitVec 70) := [457003208006343588864, 609337610709482078208, 761672013343904236512, 342752406005797093376, 76167201367677435904]
def tar7 : BitVec 70 := 1180591620683051565056
def raw8 : List (BitVec 72) := [899498377676383580160, 3597993510774169927680, 1499163962793944682432, 2473620538610025234432, 749581981464618074112]
def tar8 : BitVec 72 := 4722366482800925736960
def raw9 : List (BitVec 70) := [533170409340733980672, 609337610709482078208, 685504812009513812960, 190418003337016246272, 304668805370847722496]
def tar9 : BitVec 70 := 1180591620683051565056
def Numeric := Small.Check.can true tar0 3 (0 :: BitVec.allOnes 8 :: raw0)=false ∧
  Small.Check.can true tar1 3 (0 :: BitVec.allOnes 8 :: raw1)=false ∧
  Small.Check.can true tar2 4 (0 :: BitVec.allOnes 16 :: raw2)=false ∧
  Small.Check.can true tar3 5 (0 :: BitVec.allOnes 40 :: raw3)=false ∧
  Small.Check.can true tar4 6 (0 :: BitVec.allOnes 64 :: raw4)=false ∧
  Small.Check.can true tar5 6 (0 :: BitVec.allOnes 70 :: raw5)=false ∧
  Small.Check.can true tar6 6 (0 :: BitVec.allOnes 54 :: raw6)=false ∧
  Small.Check.can true tar7 6 (0 :: BitVec.allOnes 70 :: raw7)=false ∧
  Small.Check.can true tar8 6 (0 :: BitVec.allOnes 72 :: raw8)=false ∧
  Small.Check.can true tar9 6 (0 :: BitVec.allOnes 70 :: raw9)=false
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result0 : LiveSigned.search 4 tar0 3 (0 :: BitVec.allOnes 8 :: raw0)=false := by decide +kernel
theorem num0 : Small.Check.can true tar0 3 (0 :: BitVec.allOnes 8 :: raw0)=false :=
  LiveSigned.checked 4 tar0 3 (0 :: BitVec.allOnes 8 :: raw0) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result1 : LiveSigned.search 4 tar1 3 (0 :: BitVec.allOnes 8 :: raw1)=false := by decide +kernel
theorem num1 : Small.Check.can true tar1 3 (0 :: BitVec.allOnes 8 :: raw1)=false :=
  LiveSigned.checked 4 tar1 3 (0 :: BitVec.allOnes 8 :: raw1) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result2 : LiveSigned.search 8 tar2 4 (0 :: BitVec.allOnes 16 :: raw2)=false := by decide +kernel
theorem num2 : Small.Check.can true tar2 4 (0 :: BitVec.allOnes 16 :: raw2)=false :=
  LiveSigned.checked 8 tar2 4 (0 :: BitVec.allOnes 16 :: raw2) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result3 : LiveSigned.search 20 tar3 5 (0 :: BitVec.allOnes 40 :: raw3)=false := by decide +kernel
theorem num3 : Small.Check.can true tar3 5 (0 :: BitVec.allOnes 40 :: raw3)=false :=
  LiveSigned.checked 20 tar3 5 (0 :: BitVec.allOnes 40 :: raw3) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result4part0 : (((0 :: BitVec.allOnes 64 :: raw4)).sublists.take 16).any (LiveSigned.guess 32 tar4 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result4part1 : ((((0 :: BitVec.allOnes 64 :: raw4)).sublists.drop 16).take 16).any (LiveSigned.guess 32 tar4 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result4part2 : ((((0 :: BitVec.allOnes 64 :: raw4)).sublists.drop 32).take 16).any (LiveSigned.guess 32 tar4 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result4part3 : ((((0 :: BitVec.allOnes 64 :: raw4)).sublists.drop 48).take 16).any (LiveSigned.guess 32 tar4 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result4part4 : ((((0 :: BitVec.allOnes 64 :: raw4)).sublists.drop 64).take 16).any (LiveSigned.guess 32 tar4 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result4part5 : ((((0 :: BitVec.allOnes 64 :: raw4)).sublists.drop 80).take 16).any (LiveSigned.guess 32 tar4 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result4part6 : ((((0 :: BitVec.allOnes 64 :: raw4)).sublists.drop 96).take 16).any (LiveSigned.guess 32 tar4 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result4part7 : (((0 :: BitVec.allOnes 64 :: raw4)).sublists.drop 112).any (LiveSigned.guess 32 tar4 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result4 : LiveSigned.search 32 tar4 6 (0 :: BitVec.allOnes 64 :: raw4)=false := by
  apply CheckGroups.join _ 16 _ result4part0
  apply CheckGroups.join _ 16 _ result4part1
  apply CheckGroups.join _ 16 _ result4part2
  apply CheckGroups.join _ 16 _ result4part3
  apply CheckGroups.join _ 16 _ result4part4
  apply CheckGroups.join _ 16 _ result4part5
  apply CheckGroups.join _ 16 _ result4part6
  exact result4part7
theorem num4 : Small.Check.can true tar4 6 (0 :: BitVec.allOnes 64 :: raw4)=false :=
  LiveSigned.checked 32 tar4 6 (0 :: BitVec.allOnes 64 :: raw4) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result5part0 : (((0 :: BitVec.allOnes 70 :: raw5)).sublists.take 16).any (LiveSigned.guess 35 tar5 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result5part1 : ((((0 :: BitVec.allOnes 70 :: raw5)).sublists.drop 16).take 16).any (LiveSigned.guess 35 tar5 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result5part2 : ((((0 :: BitVec.allOnes 70 :: raw5)).sublists.drop 32).take 16).any (LiveSigned.guess 35 tar5 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result5part3 : ((((0 :: BitVec.allOnes 70 :: raw5)).sublists.drop 48).take 16).any (LiveSigned.guess 35 tar5 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result5part4 : ((((0 :: BitVec.allOnes 70 :: raw5)).sublists.drop 64).take 16).any (LiveSigned.guess 35 tar5 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result5part5 : ((((0 :: BitVec.allOnes 70 :: raw5)).sublists.drop 80).take 16).any (LiveSigned.guess 35 tar5 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result5part6 : ((((0 :: BitVec.allOnes 70 :: raw5)).sublists.drop 96).take 16).any (LiveSigned.guess 35 tar5 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result5part7 : (((0 :: BitVec.allOnes 70 :: raw5)).sublists.drop 112).any (LiveSigned.guess 35 tar5 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result5 : LiveSigned.search 35 tar5 6 (0 :: BitVec.allOnes 70 :: raw5)=false := by
  apply CheckGroups.join _ 16 _ result5part0
  apply CheckGroups.join _ 16 _ result5part1
  apply CheckGroups.join _ 16 _ result5part2
  apply CheckGroups.join _ 16 _ result5part3
  apply CheckGroups.join _ 16 _ result5part4
  apply CheckGroups.join _ 16 _ result5part5
  apply CheckGroups.join _ 16 _ result5part6
  exact result5part7
theorem num5 : Small.Check.can true tar5 6 (0 :: BitVec.allOnes 70 :: raw5)=false :=
  LiveSigned.checked 35 tar5 6 (0 :: BitVec.allOnes 70 :: raw5) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result6part0 : (((0 :: BitVec.allOnes 54 :: raw6)).sublists.take 16).any (LiveSigned.guess 27 tar6 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result6part1 : ((((0 :: BitVec.allOnes 54 :: raw6)).sublists.drop 16).take 16).any (LiveSigned.guess 27 tar6 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result6part2 : ((((0 :: BitVec.allOnes 54 :: raw6)).sublists.drop 32).take 16).any (LiveSigned.guess 27 tar6 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result6part3 : ((((0 :: BitVec.allOnes 54 :: raw6)).sublists.drop 48).take 16).any (LiveSigned.guess 27 tar6 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result6part4 : ((((0 :: BitVec.allOnes 54 :: raw6)).sublists.drop 64).take 16).any (LiveSigned.guess 27 tar6 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result6part5 : ((((0 :: BitVec.allOnes 54 :: raw6)).sublists.drop 80).take 16).any (LiveSigned.guess 27 tar6 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result6part6 : ((((0 :: BitVec.allOnes 54 :: raw6)).sublists.drop 96).take 16).any (LiveSigned.guess 27 tar6 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result6part7 : (((0 :: BitVec.allOnes 54 :: raw6)).sublists.drop 112).any (LiveSigned.guess 27 tar6 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result6 : LiveSigned.search 27 tar6 6 (0 :: BitVec.allOnes 54 :: raw6)=false := by
  apply CheckGroups.join _ 16 _ result6part0
  apply CheckGroups.join _ 16 _ result6part1
  apply CheckGroups.join _ 16 _ result6part2
  apply CheckGroups.join _ 16 _ result6part3
  apply CheckGroups.join _ 16 _ result6part4
  apply CheckGroups.join _ 16 _ result6part5
  apply CheckGroups.join _ 16 _ result6part6
  exact result6part7
theorem num6 : Small.Check.can true tar6 6 (0 :: BitVec.allOnes 54 :: raw6)=false :=
  LiveSigned.checked 27 tar6 6 (0 :: BitVec.allOnes 54 :: raw6) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result7part0 : (((0 :: BitVec.allOnes 70 :: raw7)).sublists.take 16).any (LiveSigned.guess 35 tar7 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result7part1 : ((((0 :: BitVec.allOnes 70 :: raw7)).sublists.drop 16).take 16).any (LiveSigned.guess 35 tar7 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result7part2 : ((((0 :: BitVec.allOnes 70 :: raw7)).sublists.drop 32).take 16).any (LiveSigned.guess 35 tar7 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result7part3 : ((((0 :: BitVec.allOnes 70 :: raw7)).sublists.drop 48).take 16).any (LiveSigned.guess 35 tar7 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result7part4 : ((((0 :: BitVec.allOnes 70 :: raw7)).sublists.drop 64).take 16).any (LiveSigned.guess 35 tar7 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result7part5 : ((((0 :: BitVec.allOnes 70 :: raw7)).sublists.drop 80).take 16).any (LiveSigned.guess 35 tar7 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result7part6 : ((((0 :: BitVec.allOnes 70 :: raw7)).sublists.drop 96).take 16).any (LiveSigned.guess 35 tar7 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result7part7 : (((0 :: BitVec.allOnes 70 :: raw7)).sublists.drop 112).any (LiveSigned.guess 35 tar7 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result7 : LiveSigned.search 35 tar7 6 (0 :: BitVec.allOnes 70 :: raw7)=false := by
  apply CheckGroups.join _ 16 _ result7part0
  apply CheckGroups.join _ 16 _ result7part1
  apply CheckGroups.join _ 16 _ result7part2
  apply CheckGroups.join _ 16 _ result7part3
  apply CheckGroups.join _ 16 _ result7part4
  apply CheckGroups.join _ 16 _ result7part5
  apply CheckGroups.join _ 16 _ result7part6
  exact result7part7
theorem num7 : Small.Check.can true tar7 6 (0 :: BitVec.allOnes 70 :: raw7)=false :=
  LiveSigned.checked 35 tar7 6 (0 :: BitVec.allOnes 70 :: raw7) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result8part0 : (((0 :: BitVec.allOnes 72 :: raw8)).sublists.take 16).any (LiveSigned.guess 36 tar8 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result8part1 : ((((0 :: BitVec.allOnes 72 :: raw8)).sublists.drop 16).take 16).any (LiveSigned.guess 36 tar8 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result8part2 : ((((0 :: BitVec.allOnes 72 :: raw8)).sublists.drop 32).take 16).any (LiveSigned.guess 36 tar8 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result8part3 : ((((0 :: BitVec.allOnes 72 :: raw8)).sublists.drop 48).take 16).any (LiveSigned.guess 36 tar8 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result8part4 : ((((0 :: BitVec.allOnes 72 :: raw8)).sublists.drop 64).take 16).any (LiveSigned.guess 36 tar8 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result8part5 : ((((0 :: BitVec.allOnes 72 :: raw8)).sublists.drop 80).take 16).any (LiveSigned.guess 36 tar8 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result8part6 : ((((0 :: BitVec.allOnes 72 :: raw8)).sublists.drop 96).take 16).any (LiveSigned.guess 36 tar8 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result8part7 : (((0 :: BitVec.allOnes 72 :: raw8)).sublists.drop 112).any (LiveSigned.guess 36 tar8 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result8 : LiveSigned.search 36 tar8 6 (0 :: BitVec.allOnes 72 :: raw8)=false := by
  apply CheckGroups.join _ 16 _ result8part0
  apply CheckGroups.join _ 16 _ result8part1
  apply CheckGroups.join _ 16 _ result8part2
  apply CheckGroups.join _ 16 _ result8part3
  apply CheckGroups.join _ 16 _ result8part4
  apply CheckGroups.join _ 16 _ result8part5
  apply CheckGroups.join _ 16 _ result8part6
  exact result8part7
theorem num8 : Small.Check.can true tar8 6 (0 :: BitVec.allOnes 72 :: raw8)=false :=
  LiveSigned.checked 36 tar8 6 (0 :: BitVec.allOnes 72 :: raw8) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result9part0 : (((0 :: BitVec.allOnes 70 :: raw9)).sublists.take 16).any (LiveSigned.guess 35 tar9 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result9part1 : ((((0 :: BitVec.allOnes 70 :: raw9)).sublists.drop 16).take 16).any (LiveSigned.guess 35 tar9 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result9part2 : ((((0 :: BitVec.allOnes 70 :: raw9)).sublists.drop 32).take 16).any (LiveSigned.guess 35 tar9 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result9part3 : ((((0 :: BitVec.allOnes 70 :: raw9)).sublists.drop 48).take 16).any (LiveSigned.guess 35 tar9 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result9part4 : ((((0 :: BitVec.allOnes 70 :: raw9)).sublists.drop 64).take 16).any (LiveSigned.guess 35 tar9 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result9part5 : ((((0 :: BitVec.allOnes 70 :: raw9)).sublists.drop 80).take 16).any (LiveSigned.guess 35 tar9 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result9part6 : ((((0 :: BitVec.allOnes 70 :: raw9)).sublists.drop 96).take 16).any (LiveSigned.guess 35 tar9 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result9part7 : (((0 :: BitVec.allOnes 70 :: raw9)).sublists.drop 112).any (LiveSigned.guess 35 tar9 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result9 : LiveSigned.search 35 tar9 6 (0 :: BitVec.allOnes 70 :: raw9)=false := by
  apply CheckGroups.join _ 16 _ result9part0
  apply CheckGroups.join _ 16 _ result9part1
  apply CheckGroups.join _ 16 _ result9part2
  apply CheckGroups.join _ 16 _ result9part3
  apply CheckGroups.join _ 16 _ result9part4
  apply CheckGroups.join _ 16 _ result9part5
  apply CheckGroups.join _ 16 _ result9part6
  exact result9part7
theorem num9 : Small.Check.can true tar9 6 (0 :: BitVec.allOnes 70 :: raw9)=false :=
  LiveSigned.checked 35 tar9 6 (0 :: BitVec.allOnes 70 :: raw9) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) result9
theorem numeric : Numeric := ⟨num0,num1,num2,num3,num4,num5,num6,num7,num8,num9⟩
theorem ban0 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar0 3 (0 :: BitVec.allOnes 8 :: raw0)=false) :
    Avoids A F.r0 F.c0 ⟨1,1,6⟩ := by
  intro x y ox oy
  exact exclude F 6 raw0 tar0 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem ban1 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar1 3 (0 :: BitVec.allOnes 8 :: raw1)=false) :
    Avoids A F.r0 F.c0 ⟨1,1,9⟩ := by
  intro x y ox oy
  exact exclude F 9 raw1 tar1 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem ban2 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar2 4 (0 :: BitVec.allOnes 16 :: raw2)=false) :
    Avoids A F.r0 F.c0 ⟨1,2,29⟩ := by
  intro x y ox oy
  exact exclude F 29 raw2 tar2 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem ban3 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar3 5 (0 :: BitVec.allOnes 40 :: raw3)=false) :
    Avoids A F.r0 F.c0 ⟨2,2,172⟩ := by
  intro x y ox oy
  exact exclude F 172 raw3 tar3 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem ban4 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar4 6 (0 :: BitVec.allOnes 64 :: raw4)=false) :
    Avoids A F.r0 F.c0 ⟨2,3,616⟩ := by
  intro x y ox oy
  exact exclude F 616 raw4 tar4 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem ban5 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar5 6 (0 :: BitVec.allOnes 70 :: raw5)=false) :
    Avoids A F.r0 F.c0 ⟨2,3,710⟩ := by
  intro x y ox oy
  exact exclude F 710 raw5 tar5 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem ban6 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar6 6 (0 :: BitVec.allOnes 54 :: raw6)=false) :
    Avoids A F.r0 F.c0 ⟨2,3,584⟩ := by
  intro x y ox oy
  exact exclude F 584 raw6 tar6 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem ban7 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar7 6 (0 :: BitVec.allOnes 70 :: raw7)=false) :
    Avoids A F.r0 F.c0 ⟨2,3,620⟩ := by
  intro x y ox oy
  exact exclude F 620 raw7 tar7 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem ban8 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar8 6 (0 :: BitVec.allOnes 72 :: raw8)=false) :
    Avoids A F.r0 F.c0 ⟨2,3,1708⟩ := by
  intro x y ox oy
  exact exclude F 1708 raw8 tar8 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem ban9 {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (cert : Small.Check.can true tar9 6 (0 :: BitVec.allOnes 70 :: raw9)=false) :
    Avoids A F.r0 F.c0 ⟨2,3,740⟩ := by
  intro x y ox oy
  exact exclude F 740 raw9 tar9 (by decide +kernel) cert (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) x y ox oy
theorem lawsOf {n m : Nat} {A : Fin n→Fin m→Bool} (F : Frame A) (num : Numeric) : Laws A F.r0 F.c0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩:=num
  intro q m
  simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨ban0 F h0,ban0 F.swap h0⟩
  · exact ⟨ban1 F h1,ban1 F.swap h1⟩
  · exact ⟨ban2 F h2,ban2 F.swap h2⟩
  · exact ⟨ban3 F h3,ban3 F.swap h3⟩
  · exact ⟨ban4 F h4,ban4 F.swap h4⟩
  · exact ⟨ban5 F h5,ban5 F.swap h5⟩
  · exact ⟨ban6 F h6,ban6 F.swap h6⟩
  · exact ⟨ban7 F h7,ban7 F.swap h7⟩
  · exact ⟨ban8 F h8,ban8 F.swap h8⟩
  · exact ⟨ban9 F h9,ban9 F.swap h9⟩
end PEqualNP.Outside.L_meta_26029_aux

namespace PEqualNP.Outside.L_meta_26029_aux
structure Ticket where
  id : Fin 10
  tr : Bool
  x : List Nat
  y : List Nat
  deriving Inhabited

def sel {n : Nat} [NeZero n] (ls : List Nat) {m : Nat} (i : Fin (m+1)) : Fin n :=
  if i.val=0 then 0 else Fin.ofNat n (ls.getD (i.val-1) 0)
def getRule (q : Ticket) := rules.getD q.id.val ⟨0,0,0⟩
def hit {n m : Nat} [NeZero n] [NeZero m] (A : Fin n→Fin m→Bool) (q : Ticket) : Bool :=
  let P:=getRule q
  if q.tr then decide (∀ (i : Fin (P.a+1)) (j : Fin (P.b+1)),A (sel q.y j) (sel q.x i)=table _ _ P.M i j)
  else decide (∀ (i : Fin (P.a+1)) (j : Fin (P.b+1)),A (sel q.x i) (sel q.y j)=table _ _ P.M i j)
theorem safe {n m : Nat} [NeZero n] [NeZero m] {A : Fin n→Fin m→Bool} (law : Laws A 0 0) (q : Ticket) :
    hit A q=false := by
  have listed : ∀i : Fin 10,rules.getD i.val ⟨0,0,0⟩∈rules := by decide +kernel
  obtain ⟨row,col⟩:=law (getRule q) (listed q.id)
  unfold hit
  cases q.tr <;> simp only [Bool.false_eq_true,if_false,if_true,decide_eq_false_iff_not]
  · exact row (sel q.x) (sel q.y) (by simp [sel]) (by simp [sel])
  · exact col (sel q.x) (sel q.y) (by simp [sel]) (by simp [sel])
def shapeMasks : Array Nat := #[
8580,8581,8582,8583,8596,8597,8598,8599,
8612,8613,8614,8615,8628,8629,8630,8631,
9604,9605,9606,9607,9620,9621,9622,9623,
9636,9637,9638,9639,9652,9653,9654,9655,
10628,10629,10630,10631,10644,10645,10646,10647,
10660,10661,10662,10663,10676,10677,10678,10679,
11652,11653,11654,11655,11668,11669,11670,11671,
11684,11685,11686,11687,11700,11701,11702,11703,
24964,24965,24966,24967,24980,24981,24982,24983,
24996,24997,24998,24999,25012,25013,25014,25015,
25988,25989,25990,25991,26004,26005,26006,26007,
26020,26021,26022,26023,26036,26037,26038,26039,
27012,27013,27014,27015,27028,27029,27030,27031,
27044,27045,27046,27047,27060,27061,27062,27063,
28036,28037,28038,28039,28052,28053,28054,28055,
28068,28069,28070,28071,28084,28085,28086,28087,
41348,41349,41350,41351,41364,41365,41366,41367,
41380,41381,41382,41383,41396,41397,41398,41399,
42372,42373,42374,42375,42388,42389,42390,42391,
42404,42405,42406,42407,42420,42421,42422,42423,
43396,43397,43398,43399,43412,43413,43414,43415,
43428,43429,43430,43431,43444,43445,43446,43447,
44420,44421,44422,44423,44436,44437,44438,44439,
44452,44453,44454,44455,44468,44469,44470,44471,
57732,57733,57734,57735,57748,57749,57750,57751,
57764,57765,57766,57767,57780,57781,57782,57783,
58756,58757,58758,58759,58772,58773,58774,58775,
58788,58789,58790,58791,58804,58805,58806,58807,
59780,59781,59782,59783,59796,59797,59798,59799,
59812,59813,59814,59815,59828,59829,59830,59831,
60804,60805,60806,60807,60820,60821,60822,60823,
60836,60837,60838,60839,60852,60853,60854,60855]
def shapeCases : Array Ticket := #[
⟨0,false,[2],[2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨2,false,[1],[3,1]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨2,false,[1],[3,2]⟩,
⟨3,false,[2,1],[3,2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨2,false,[1],[3,1]⟩,
⟨3,false,[2,1],[1,2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨2,false,[1],[3,2]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨2,false,[1],[3,1]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨2,false,[1],[3,2]⟩,
⟨3,false,[2,3],[1,2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨2,false,[1],[3,1]⟩,
⟨3,false,[2,1],[1,2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨2,false,[1],[3,2]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨2,false,[1],[3,1]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨2,false,[1],[3,2]⟩,
⟨3,false,[2,1],[3,2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨2,false,[1],[3,1]⟩,
⟨3,false,[2,1],[1,2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨2,false,[1],[3,2]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨2,false,[1],[3,1]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨2,false,[1],[3,2]⟩,
⟨0,false,[],[]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨2,false,[1],[3,1]⟩,
⟨3,false,[2,1],[1,2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨2,false,[1],[3,2]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨1,false,[3],[3]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[3]⟩,
⟨3,false,[2,1],[3,2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨1,false,[3],[3]⟩,
⟨3,false,[2,1],[1,2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[3]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨1,false,[3],[3]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[3]⟩,
⟨3,false,[2,3],[1,2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨1,false,[3],[3]⟩,
⟨3,false,[2,1],[1,2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[3]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨1,false,[3],[3]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[3]⟩,
⟨3,false,[2,1],[3,2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨1,false,[3],[3]⟩,
⟨3,false,[2,1],[1,2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[3]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨1,false,[3],[3]⟩,
⟨0,false,[2],[2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[3]⟩,
⟨9,false,[3,1],[3,2,1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[1]⟩,⟨1,false,[3],[3]⟩,
⟨3,false,[2,1],[1,2]⟩,⟨1,false,[1],[1]⟩,⟨0,false,[2],[1]⟩,⟨1,false,[1],[3]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[1]⟩,⟨0,false,[1],[2]⟩,⟨1,false,[3],[3]⟩]
def typeCases : Array Ticket := #[
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨6,false,[1,2],[4,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨6,false,[1,2],[4,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨6,false,[1,2],[4,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨5,false,[1,2],[5,3,2]⟩,⟨0,false,[],[]⟩,⟨5,false,[1,2],[5,3,2]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨7,false,[1,2],[6,3,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[2,1],[6,4,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[2,1],[6,4,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨7,false,[2,1],[6,5,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨8,false,[1,2],[6,5,3]⟩,⟨0,false,[],[]⟩,⟨7,false,[1,2],[6,3,1]⟩,⟨0,false,[],[]⟩,⟨5,false,[1,2],[5,3,2]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[2,1],[6,4,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨5,false,[2,1],[3,5,4]⟩,⟨0,false,[],[]⟩,⟨4,false,[2,1],[6,4,1]⟩,⟨0,false,[],[]⟩,⟨5,false,[1,2],[5,3,2]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨6,false,[1,2],[4,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨6,false,[1,2],[4,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨6,false,[1,2],[4,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨5,false,[1,2],[5,3,2]⟩,⟨0,false,[],[]⟩,⟨5,false,[1,2],[5,3,2]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨7,false,[1,2],[6,3,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[2,1],[6,4,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[2,1],[6,4,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨7,false,[2,1],[6,5,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨8,false,[1,2],[6,5,3]⟩,⟨0,false,[],[]⟩,⟨7,false,[1,2],[6,3,1]⟩,⟨0,false,[],[]⟩,⟨5,false,[1,2],[5,3,2]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[2,1],[6,4,1]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩,
⟨0,false,[],[]⟩,⟨5,false,[2,1],[3,5,4]⟩,⟨0,false,[],[]⟩,⟨4,false,[2,1],[6,4,1]⟩,⟨0,false,[],[]⟩,⟨5,false,[1,2],[5,3,2]⟩,⟨0,false,[],[]⟩,⟨4,false,[1,2],[6,2,1]⟩]
def shapeTab (v : Fin 256) : Fin 4→Fin 4→Bool := table 4 4 (shapeMasks.getD v.val 0)
theorem shapeCheck : ∀v : Fin 256, shapeMasks.getD v.val 0=28036 ∨ hit (shapeTab v) (shapeCases.getD v.val default)=true := by decide +kernel
def pack8 (a b c d e f g h : Bool) : Fin 256 :=
  Fin.ofNat 256 (a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat+32*f.toNat+64*g.toNat+128*h.toNat)
def shapeData (a b c d e f g h : Bool) : Fin 4→Fin 4→Bool :=
  ![![a,b,true,false],![c,d,false,true],![true,false,e,f],![false,true,g,h]]
theorem shapeDecode : ∀a b c d e f g h,∀i j,shapeData a b c d e f g h i j =
    shapeTab (pack8 a b c d e f g h) i j := by decide +kernel
theorem forced {B : Fin 4→Fin 4→Bool} (law : Laws B 0 0)
    (p : B 0 2=true) (q : B 1 2=false) (r : B 0 3=false) (s : B 1 3=true)
    (p' : B 2 0=true) (q' : B 2 1=false) (r' : B 3 0=false) (s' : B 3 1=true) :
    ∀i j,B i j=table 4 4 28036 i j := by
  let v:=pack8 (B 0 0) (B 0 1) (B 1 0) (B 1 1) (B 2 2) (B 2 3) (B 3 2) (B 3 3)
  have eq : B=shapeTab v := by
    funext i j
    rw [←shapeDecode]
    fin_cases i <;> fin_cases j <;> first | rfl | assumption
  rcases shapeCheck v with good|bad
  · rw [eq];intro i j;unfold shapeTab;rw [good]
  · rw [←eq,safe law] at bad;contradiction

def tag (a b c : Bool) : Fin 8 := Fin.ofNat 8 (a.toNat+2*b.toNat+4*c.toNat)
def setId (f : Fin 8→Bool) := pack8 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
def tagBit (t : Fin 8) (r : Fin 3) := t.val.testBit r.val
theorem decodeTag : ∀a b c,∀i,tagBit (tag a b c) i=(![a,b,c] : Fin 3→Bool) i := by decide +kernel
theorem decodeSet0 : ∀a b c d e f g h,∀i : Fin 8,
    (pack8 a b c d e f g h).val.testBit i.val=(![a,b,c,d,e,f,g,h] : Fin 8→Bool) i := by decide +kernel
theorem decodeSet (p : Fin 8→Bool) (i : Fin 8) : (setId p).val.testBit i.val=p i := by
  unfold setId;rw [decodeSet0];fin_cases i <;> rfl
def typeTab (s : Fin 256) (r : Fin 3) (j : Fin 8) := s.val.testBit j.val && tagBit j r
def typeBad (s : Fin 256) := s.val.testBit 0 && @decide (¬Forest.comparable (typeTab s) 0 1 ∧
    ¬Forest.comparable (typeTab s) 0 2 ∧ typeTab s 1≠typeTab s 2) (by unfold Forest.comparable; infer_instance)
theorem typeCheck : ∀s : Fin 256,typeBad s=true → hit (typeTab s) (typeCases.getD s.val default)=true := by decide +kernel
theorem noTypes {s : Fin 256} (law : Laws (typeTab s) 0 0) (z : s.val.testBit 0=true) (h : ¬Forest.comparable (typeTab s) 0 1)
    (k : ¬Forest.comparable (typeTab s) 0 2) : typeTab s 1=typeTab s 2 := by
  by_contra diff
  have eq:=typeCheck s (by simp [typeBad,z,h,k,diff])
  rw [safe law] at eq;contradiction
end PEqualNP.Outside.L_meta_26029_aux

namespace PEqualNP.Outside.L_meta_26029_aux.LiveMono
open Small.Check
variable {w : Nat}
abbrev V (w : Nat) := BitVec w
inductive Takes : Finset (V w) → V w → Prop
  | conj (a b : V w) (h : a ≠ b) : Takes {a,b} (a &&& b)
  | disj (a b : V w) (h : a ≠ b) : Takes {a,b} (a ||| b)

def live (t : V w) : Nat → Finset (V w) → Prop
  | 0,s => s={t}
  | k+1,s => live t k s ∨ ∃ p z r, Takes p z ∧ z ∉ s ∧ s=p∪r ∧ live t k (insert z r)

theorem growLive {t : V w} {k : Nat} {B : List (V w)} {z : V w}
    (opt : z∈options false B) (s : Finset (V w)) (ss : s⊆(z::B).toFinset) (cont : live t k s) :
    ∃o⊆B.toFinset, live t (k+1) o := by
  by_cases sub : s⊆B.toFinset
  · exact ⟨_,sub,Or.inl cont⟩
  have mz : z∈s := by
    by_contra hn
    exact sub (by intro u m; have e:=ss m; simp only [List.toFinset_cons,Finset.mem_insert] at e
                  exact e.resolve_left (by rintro rfl;exact hn m))
  have nz : z∉B := by
    intro h; apply sub; simpa [Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)] using ss
  let r:=s.erase z
  have rs : r⊆B.toFinset := by
    intro u hu
    have m:=Finset.mem_erase.mp hu
    have f:=ss m.2
    rw [List.toFinset_cons] at f
    exact (Finset.mem_insert.mp f).resolve_left m.1
  have hit {p : Finset (V w)} (inB : p⊆B.toFinset) (step : Takes p z) :
      ∃o⊆B.toFinset, live t (k+1) o := by
    have subo := Finset.union_subset inB rs
    refine ⟨p∪r,subo,Or.inr ⟨p,z,r,step,fun h=>nz (List.mem_toFinset.mp (subo h)),rfl,?_⟩⟩
    simpa [r,Finset.insert_erase mz] using cont
  simp only [options,List.mem_eraseDups,List.mem_append,List.mem_flatMap,List.mem_cons,
    List.not_mem_nil,or_false,if_false,Bool.false_eq_true,List.mem_map] at opt
  rcases opt with ⟨a,ha,b,hb,e|e⟩
  · subst z
    have ne : a ≠ b := by rintro rfl;exact nz (by simpa using ha)
    exact hit (p:={a,b}) (Finset.insert_subset (List.mem_toFinset.mpr ha) (Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hb))) (.conj a b ne)
  · subst z
    have ne : a ≠ b := by rintro rfl;exact nz (by simpa using ha)
    exact hit (p:={a,b}) (Finset.insert_subset (List.mem_toFinset.mpr ha) (Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hb))) (.disj a b ne)

theorem compress {t : V w} (k : Nat) (B : List (V w)) (run : can false t k B=true) :
    ∃s⊆B.toFinset, live t k s := by
  induction k generalizing B with
  | zero => exact ⟨{t},Finset.singleton_subset_iff.mpr (by simpa [can] using run),rfl⟩
  | succ k ih =>
    have old (h : t∈B) : ∃s⊆B.toFinset,live t (k+1) s := by
      have base : ∀k,live t k {t} := by intro k; induction k with | zero=>rfl | succ _ ih=>exact Or.inl ih
      exact ⟨{t},by simp [h],base _⟩
    rw [can,Bool.or_eq_true,List.contains_iff_mem,List.any_eq_true] at run
    rcases run with h|⟨z,hz,go⟩
    · exact old h
    split_ifs at go with mem
    · obtain ⟨s,ss,h⟩:=ih B go;exact ⟨s,ss,Or.inl h⟩
    obtain ⟨s,ss,h⟩:=ih (z::B) go
    exact growLive hz s ss h

theorem liveCard {t : V w} {k : Nat} {s : Finset (V w)} (h : live t k s) : s.card≤k+1 := by
  induction k generalizing s with
  | zero=>change s={t} at h;simp [h]
  | succ k ih=>
    rcases h with skip|⟨p,z,r,op,hz,rfl,cont⟩
    · exact (ih skip).trans (by omega)
    have nz : z∉r := by intro m;exact hz (Finset.mem_union_right _ m)
    have bound:=ih cont
    rw [Finset.card_insert_of_notMem nz] at bound
    have pc : p.card ≤ 2 := by
      cases op with
      | conj a b h | disj a b h=>simp [h]
    have := Finset.card_union_le p r
    omega

open LiveSigned
theorem riseLive {p i : Nat} {t : V w} {k : Nat} {s : Finset (V w)}
    (h : live t k s) (up : rising p i t) : ∃v∈s,rising p i v := by
  induction k generalizing s with
  | zero=>change s={t} at h;exact ⟨t,by simp [h],up⟩
  | succ k ih=>
    rcases h with skip|⟨xs,z,r,op,nz,rfl,cont⟩
    · exact ih skip
    obtain ⟨v,m,hv⟩:=ih cont
    rcases Finset.mem_insert.mp m with rfl|mm
    · cases op with
      | conj a b ne=>
        rcases risingGate (a:=a) (b:=b) false hv with ha|hb
        · exact ⟨a,by simp,ha⟩
        · exact ⟨b,by simp,hb⟩
      | disj a b ne=>
        rcases risingGate (a:=a) (b:=b) true hv with ha|hb
        · exact ⟨a,by simp,ha⟩
        · exact ⟨b,by simp,hb⟩
    · exact ⟨v,Finset.mem_union_right _ mm,hv⟩
theorem upLive {p : Nat} {t : V w} {k : Nat} {ws : List (V w)}
    (h : live t k ws.toFinset) (up : ∀i<p,rising p i t) :
    (ups p ws &&& (2^p-1)) = 2^p-1 := by
  apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,Nat.testBit_two_pow_sub_one]
  by_cases hi:i<p
  · obtain ⟨v,m,pos⟩:=riseLive h (up i hi)
    simp [hi,(ups_iff p i ws hi).mpr ⟨v,List.mem_toFinset.mp m,pos⟩]
  · simp [hi]
def guess (p : Nat) (t : V w) : Nat → List (V w) → Bool
  | 0,ws=>ws.contains t
  | k+1,ws=>
    ws.contains t ||
    ((decide (ws.length ≤ k+2) && (ups p ws &&& (2^p-1) == 2^p-1)) &&
      ((pairs ws).any (fun (a,b,r)=>
         extend ws (guess p t k) (a &&& b) (keepChoices a b r) ||
         extend ws (guess p t k) (a ||| b) (keepChoices a b r))))

theorem first {t : V w} {k : Nat} {s : Finset (V w)} (h : live t (k+1) s) :
    s={t} ∨ ∃p z r,Takes p z ∧ z∉s ∧ s=p∪r ∧ live t k (insert z r) := by
  induction k with
  | zero=>exact h
  | succ k ih=>
    rcases h with skip|step
    · rcases ih skip with done|⟨p,z,r,op,nz,eq,cont⟩
      · exact Or.inl done
      · exact Or.inr ⟨p,z,r,op,nz,eq,Or.inl cont⟩
    · exact Or.inr step

theorem guess_live {t : V w} {p : Nat} (up : ∀i<p,rising p i t)
    (k : Nat) (ws : List (V w)) (nod : ws.Nodup) (L : live t k ws.toFinset) : guess p t k ws=true := by
  induction k generalizing ws with
  | zero=>
    change ws.toFinset={t} at L
    exact List.contains_iff_mem.mpr (List.mem_toFinset.mp (L ▸ Finset.mem_singleton_self t))
  | succ k ih=>
    rw [guess,Bool.or_eq_true]
    rcases first L with done|⟨pars,z,r,op,nz,eq,cont⟩
    · exact Or.inl (List.contains_iff_mem.mpr (List.mem_toFinset.mp (done ▸ Finset.mem_singleton_self t)))
    apply Or.inr
    have bound:=liveCard L
    rw [List.toFinset_card_of_nodup nod] at bound
    have caps : (decide (ws.length ≤ k+2) && (ups p ws &&& (2^p-1) == 2^p-1))=true := by
      simp [show ws.length≤k+2 by omega,upLive L up]
    rw [caps,Bool.true_and]
    have extendOK (tails : List (List (V w))) (good : ∃kept∈tails,kept.Nodup ∧ kept.toFinset=r) :
        extend ws (guess p t k) z tails=true := by
      obtain ⟨kept,mem,nd,eqr⟩:=good
      have zr : z∉r := fun m=>nz (eq ▸ Finset.mem_union_right _ m)
      have zk : z∉kept := fun m=>zr (eqr ▸ List.mem_toFinset.mpr m)
      have hl : live t k (z::kept).toFinset := by simpa [eqr] using cont
      have yes:=ih (z::kept) (List.nodup_cons.mpr ⟨zk,nd⟩) hl
      have nw : z∉ws:=fun m=>nz (List.mem_toFinset.mpr m)
      simpa [extend,nw] using (List.any_eq_true.mpr ⟨kept,mem,yes⟩ :
        tails.any (fun kept=>guess p t k (z::kept))=true)
    cases op with
    | conj a b ne | disj a b ne=>
      all_goals
        have hs : ws.toFinset=insert a (insert b r) := by simpa using eq
        have am : a∈ws := List.mem_toFinset.mp (hs ▸ Finset.mem_insert_self ..)
        have bm : b∈ws := List.mem_toFinset.mp (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
        obtain ⟨rest,pos,perm⟩:=pick_two am bm ne
        apply List.any_eq_true.mpr
        rcases pos with pos|pos
        · refine ⟨(a,b,rest),pos,?_⟩
          first | exact Bool.or_eq_true_iff.mpr (Or.inl (extendOK _ (recover_kept perm nod hs)))
                | exact Bool.or_eq_true_iff.mpr (Or.inr (extendOK _ (recover_kept perm nod hs)))
        · refine ⟨(b,a,rest),pos,?_⟩
          have sw := recover_kept (perm.trans (List.Perm.swap ..)) nod (hs.trans (Finset.insert_comm ..))
          first | exact Bool.or_eq_true_iff.mpr (Or.inl (by simpa only [BitVec.and_comm b a] using extendOK _ sw))
                | exact Bool.or_eq_true_iff.mpr (Or.inr (by simpa only [BitVec.or_comm b a] using extendOK _ sw))

def search (p : Nat) (t : V w) (k : Nat) (inputs : List (V w)) :=
  inputs.sublists.any (guess p t k)
theorem checked (p : Nat) (t : V w) (k : Nat) (inputs : List (V w)) (nod : inputs.Nodup)
    (up : ∀i : Fin p,rising p i.val t) (test : search p t k inputs=false) : can false t k inputs=false := by
  apply Bool.eq_false_iff.mpr;intro yes
  obtain ⟨s,ss,hl⟩:=compress k inputs yes
  let ws:=inputs.filter (· ∈ s)
  have eq : ws.toFinset=s := by
    ext x
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun h=>List.mem_toFinset.mp (ss h)
  have nd : ws.Nodup := nod.filter _
  have ok:=guess_live (fun i hi=>up ⟨i,hi⟩) k ws nd (eq.symm ▸ hl)
  have y : search p t k inputs=true := List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),ok⟩
  exact Bool.noConfusion (test.symm.trans y)
def monRaw : List (BitVec 40) := [35468084223, 212808530944, 851235012608, 283744697375, 638425498592, 177341431808]
def monTarget : BitVec 40 := 1099510579200
def monStart := (0 :: BitVec.allOnes 40 :: monRaw)
def cell (r : Fin 40) : Fin 9 := [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 8, 8, 8, 8, 8, 2, 4, 5, 6, 7, 2, 4, 5, 6, 7, 2, 4, 5, 6, 7, 2, 4, 5, 6, 7][r.val]!
def rr (r : Fin 40) : Fin 3 := Small.Nine.rr (cell r)
def cc (r : Fin 40) : Fin 3 := Small.Nine.cc (cell r)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart0 : ((monStart).sublists.take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart1 : (((monStart).sublists.drop 16).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart2 : (((monStart).sublists.drop 32).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart3 : (((monStart).sublists.drop 48).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart4 : (((monStart).sublists.drop 64).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart5 : (((monStart).sublists.drop 80).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart6 : (((monStart).sublists.drop 96).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart7 : (((monStart).sublists.drop 112).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart8 : (((monStart).sublists.drop 128).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart9 : (((monStart).sublists.drop 144).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart10 : (((monStart).sublists.drop 160).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart11 : (((monStart).sublists.drop 176).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart12 : (((monStart).sublists.drop 192).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart13 : (((monStart).sublists.drop 208).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart14 : (((monStart).sublists.drop 224).take 16).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstructionpart15 : ((monStart).sublists.drop 240).any (LiveMono.guess 20 monTarget 6)=false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem obstruction : search 20 monTarget 6 monStart=false := by
  apply CheckGroups.join _ 16 _ obstructionpart0
  apply CheckGroups.join _ 16 _ obstructionpart1
  apply CheckGroups.join _ 16 _ obstructionpart2
  apply CheckGroups.join _ 16 _ obstructionpart3
  apply CheckGroups.join _ 16 _ obstructionpart4
  apply CheckGroups.join _ 16 _ obstructionpart5
  apply CheckGroups.join _ 16 _ obstructionpart6
  apply CheckGroups.join _ 16 _ obstructionpart7
  apply CheckGroups.join _ 16 _ obstructionpart8
  apply CheckGroups.join _ 16 _ obstructionpart9
  apply CheckGroups.join _ 16 _ obstructionpart10
  apply CheckGroups.join _ 16 _ obstructionpart11
  apply CheckGroups.join _ 16 _ obstructionpart12
  apply CheckGroups.join _ 16 _ obstructionpart13
  apply CheckGroups.join _ 16 _ obstructionpart14
  exact obstructionpart15
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity
theorem coreFloor (D : Circuit) (md : Monotone2 D) (rep : Represents Small.Nine.core D) : 7≤D.size := by
  have unreachable:=checked 20 monTarget 6 monStart (by decide +kernel) (by decide +kernel) obstruction
  have rawEval : ∀r : Fin 40,monRaw.map (Small.Check.bit r.val)=PEqualNP.Represents.oneEach (rr r) (cc r) := by decide +kernel
  have tarEval : ∀r : Fin 40,Small.Nine.core (rr r) (cc r)=Small.Check.bit r.val monTarget := by decide +kernel
  apply Nat.le_of_not_gt
  intro low
  have val (r : Fin 40) : D.eval (monRaw.map (Small.Check.bit r.val))=Small.Check.bit r.val monTarget := by
    rw [rawEval,rep,tarEval]
  have seen:=Small.Check.readout false D monRaw monStart 6 (fun g h=>by simpa using (md g h).1) (fun g h=>(md g h).2)
    (fun v hv=>List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)) List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self) (Nat.le_of_lt_succ low) monTarget (by decide +kernel) val
  exact Bool.noConfusion (unreachable.symm.trans seen)
end PEqualNP.Outside.L_meta_26029_aux.LiveMono

namespace PEqualNP.Outside.L_meta_26029_aux
open Small Forest
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

theorem four {n m : Nat} {A : Fin n→Fin m→Bool} {r₀ r₁ : Fin n} {c₀ c₁ : Fin m} (law : Laws A r₀ c₀)
    (hr : ¬comparable A r₀ r₁) (hc : ¬comparable (fun j i=>A i j) c₀ c₁) :
    ∃(x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m),
      x 0=r₀ ∧ x 1=r₁ ∧ y 0=c₀ ∧ y 1=c₁ ∧ ∀i j,A (x i) (y j)=table 4 4 28036 i j := by
  obtain ⟨c3,c2,h03,h02,h13,h12⟩:=sample hr
  obtain ⟨r3,r2,h30,h20,h31,h21⟩:=sample hc
  let x : Fin 4→Fin n:=![r₀,r₁,r2,r3]
  let y : Fin 4→Fin m:=![c₀,c₁,c2,c3]
  have val:=forced (lawsMap (u:=3) (v:=3) law x y rfl rfl) h02 h12 h03 h13 h20 h21 h30 h31
  have ri : Function.Injective (table 4 4 28036):=by decide +kernel
  have ci : Function.Injective (fun (j i : Fin 4)=>table 4 4 28036 i j):=by decide +kernel
  have ix : Function.Injective x := by
    intro i k eq;apply ri;funext j;exact (val i j).symm.trans ((congrArg (fun w=>A w (y j)) eq).trans (val k j))
  have iy : Function.Injective y := by
    intro j l eq;apply ci;funext i;exact (val i j).symm.trans ((congrArg (A (x i)) eq).trans (val i l))
  exact ⟨⟨x,ix⟩,⟨y,iy⟩,rfl,rfl,rfl,rfl,val⟩
theorem baseFalse {n m : Nat} {A : Fin n→Fin m→Bool} {r p : Fin n} {c : Fin m} (law : Laws A r c)
    (cols : Partners (fun j i=>A i j)) (nc : ¬comparable A r p) : A r c=false ∧ A p c=false := by
  obtain ⟨q,hq⟩:=cols c
  obtain ⟨x,y,h0,h1,k0,k1,val⟩:=four law nc hq
  have a:=val 0 0
  have b:=val 1 0
  rw [h0,k0] at a;rw [h1,k0] at b
  exact ⟨a,b⟩

theorem pullCompare {n m : Nat} {A : Fin n→Fin m→Bool} (x : Fin 3→Fin n) (h : Fin m→Fin 8)
    (s : Fin 256) (val : ∀i j,typeTab s i (h j)=A (x i) j) {i k : Fin 3} (cmp : comparable (typeTab s) i k) :
    comparable A (x i) (x k) := by
  rcases cmp with g|g
  · exact Or.inl (fun j v=>(val k j).symm ▸ g (h j) ((val i j) ▸ v))
  · exact Or.inr (fun j v=>(val i j).symm ▸ g (h j) ((val k j) ▸ v))

theorem uniquePartner {n m : Nat} {A : Fin n→Fin m→Bool} {r p q : Fin n} {c : Fin m} (law : Laws A r c)
    (di : Function.Injective A) (cols : Partners (fun j i=>A i j)) (hp : ¬comparable A r p) (hq : ¬comparable A r q) : p=q := by
  classical
  obtain ⟨r0,p0⟩:=baseFalse law cols hp
  have q0:=(baseFalse law cols hq).2
  let x : Fin 3→Fin n:=![r,p,q]
  let h (j : Fin m) := tag (A r j) (A p j) (A q j)
  have h0 : h c=0 := by simp [h,r0,p0,q0,tag]
  let present (t : Fin 8) := decide (∃j,h j=t)
  let s:=setId present
  have mem (t : Fin 8) : s.val.testBit t.val=true ↔ ∃j,h j=t := by
    dsimp only [s];rw [decodeSet];simp [present]
  have decoded (i : Fin 3) (j : Fin m) : tagBit (h j) i=A (x i) j := by
    dsimp only [h];rw [decodeTag];fin_cases i <;> rfl
  have val (i j) : typeTab s i (h j)=A (x i) j := by
    unfold typeTab;rw [(mem _).mpr ⟨j,rfl⟩,Bool.true_and,decoded]
  have clear (i : Fin 3) : A (x i) c=false := by fin_cases i <;> first | exact r0 | exact p0 | exact q0
  let y (t : Fin 8) := if t=0 then c else if e : ∃j,h j=t then Classical.choose e else c
  have y0 : y 0=c := by simp [y]
  have projected (i : Fin 3) (t : Fin 8) : A (x i) (y t)=typeTab s i t := by
    by_cases zero : t=0
    · subst t;rw [y0,←val i c,h0]
    by_cases existsTag : ∃j,h j=t
    · have eq:=Classical.choose_spec existsTag
      rw [show y t=Classical.choose existsTag by simp [y,zero,existsTag],←val i _,eq]
    · have off : s.val.testBit t.val=false := Bool.eq_false_iff.mpr (fun t0=>existsTag ((mem _).mp t0))
      simp [y,zero,existsTag,typeTab,off,clear]
  have lm:=lawsMap (u:=2) (v:=7) law x y rfl y0
  have matrix : (fun i j=>A (x i) (y j))=typeTab s := funext (fun i=>funext (projected i))
  rw [matrix] at lm
  have hnc : ¬comparable (typeTab s) 0 1:=fun g=>hp (pullCompare x h s val g)
  have knc : ¬comparable (typeTab s) 0 2:=fun g=>hq (pullCompare x h s val g)
  have e:=noTypes lm ((mem 0).mpr ⟨c,h0⟩) hnc knc
  apply di;funext j
  exact (val 1 j).symm.trans ((congrFun e (h j)).trans (val 2 j))

theorem positiveCost {n m : Nat} (hn : 3 ≤ n) (hm : 3 ≤ m) {A : Fin n→Fin m→Bool}
    (rp : Partners A) (cp : Partners (fun j i=>A i j))
    (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m) (mat : ∀i j,A (x i) (y j)=table 4 4 28036 i j) :
    ¬RepSizeAtMost A (n+m) := by
  let h : Fin 3 ↪ Fin 4:=⟨Fin.succ,Fin.succ_injective _⟩
  let xx:=h.trans x
  let yy:=h.trans y
  have eq (i j : Fin 3) : A (xx i) (yy j)=Small.Nine.core i j := by
    change A (x i.succ) (y j.succ)=_
    rw [mat];exact (by decide +kernel : ∀i j : Fin 3,table 4 4 28036 i.succ j.succ=Small.Nine.core i j) i j
  have varies : ∃i k j l,A (xx i) (yy j)≠A (xx k) (yy l) := by
    refine ⟨0,0,0,2,?_⟩;rw [eq,eq];decide +kernel
  rintro ⟨C,mono,size,rep⟩
  obtain ⟨D,md,rd,cost⟩:=Small.positiveRestriction n m 3 3 A xx yy varies
    (fun i _=>by obtain ⟨k,_,j,p,q⟩:=witness A rp i;exact ⟨k,j,p,q⟩)
    (fun j _=>by obtain ⟨l,_,i,p,q⟩:=witness (fun j i=>A i j) cp j;exact ⟨l,i,p,q⟩) C mono rep
  have floor:=LiveMono.coreFloor D md (fun i j=>(rd i j).trans (eq i j))
  omega
theorem finalResult (numericProof : Numeric) {n m : Nat} (hn : 3 ≤ n) (hm : 3 ≤ m) (A : Fin n→Fin m→Bool)
    (di : Function.Injective A) (dj : Function.Injective (fun j i=>A i j)) (ri : Partners A) (cj : Partners (fun j i=>A i j))
    (C : Circuit) (fan : FanInTwo C) (rep : Represents A C) (small : C.size≤n+m-1) :
    C.size=n+m-1 ∧ (HasNot C→∃(x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m),
       (∀i,¬comparable A (x 0) i ↔ i=x 1) ∧ (∀j,¬comparable (fun j i=>A i j) (y 0) j ↔ j=y 1) ∧
       ∀i j,A (x i) (y j)=table 4 4 28036 i j) ∧
    (HasNot C→¬RepSizeAtMost A (n+m)) ∧ (¬HasNot C→∃e : Fin n ≃ Fin m,∀i j,A i j=decide (e i=j)) := by
  obtain ⟨size,anchors⟩:=boundary hn hm A di dj ri cj C fan rep small
  have has (notGate : HasNot C) : ∃(x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m),
       (∀i,¬comparable A (x 0) i ↔ i=x 1) ∧ (∀j,¬comparable (fun j i=>A i j) (y 0) j ↔ j=y 1) ∧
       ∀i j,A (x i) (y j)=table 4 4 28036 i j := by
    obtain ⟨r,c,offR,offC,count⟩:=anchors notGate
    let F : Frame A := ⟨n+m,C,Small.left m,Small.right n,
      fun _ _ e=>Fin.ext (congrArg (fun w : Fin (n+m)=>w.val) e),fun _ _ e=>Fin.ext (Nat.add_left_cancel (congrArg (fun w : Fin (n+m)=>w.val) e)),
      fun i j e=>by have eq:=congrArg Fin.val e;change i.val=n+j.val at eq;omega,
      r,c,offR,offC,Small.atPair rep,fan,by omega⟩
    have law : Laws A r c:=lawsOf F numericProof
    have dual : Laws (fun j i=>A i j) c r:=lawsOf F.swap numericProof
    obtain ⟨r1,pr⟩:=ri r
    obtain ⟨c1,pc⟩:=cj c
    obtain ⟨x,y,h0,h1,k0,k1,mat⟩:=four law pr pc
    refine ⟨x,y,?_,?_,mat⟩
    · rw [h0,h1];intro i
      exact ⟨fun q=>uniquePartner law di cj q pr,fun e=>e ▸ pr⟩
    · rw [k0,k1];intro j
      exact ⟨fun q=>uniquePartner dual dj ri q pc,fun e=>e ▸ pc⟩
  refine ⟨size,has,?_,?_⟩
  · intro h;obtain ⟨x,y,_,_,mat⟩:=has h
    exact positiveCost hn hm ri cj x y mat
  · intro no
    have mono : Monotone2 C := by
      intro g hg
      obtain ⟨op,ar⟩:=fan g hg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
      refine ⟨?_,ar⟩
      change g.op=.and ∨ g.op=.or
      rcases op with p|p|p
      · exact Or.inl p
      · exact Or.inr p
      · exact False.elim (no ⟨g,hg,p⟩)
    exact (tightMono A hn hm di dj ri cj C mono rep small).2
end PEqualNP.Outside.L_meta_26029_aux

open PEqualNP.Outside.L_meta_26029_aux in
theorem PEqualNP.Outside.L_meta_26029 : ∀ (n m : Nat) (A : Fin n → Fin m → Bool), 3 ≤ n → 3 ≤ m →
  let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
  let cc := fun j l : Fin m => colLE j l ∨ colLE l j
  Function.Injective A → Function.Injective (fun j i => A i j) →
  (∀ i, ∃ k, ¬ rc i k) → (∀ j, ∃ l, ¬ cc j l) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  C.size ≤ n + m - 1 →
  let hasNot := ∃ gate ∈ C.gates, gate.op = PEqualNP.CircuitLowerBounds.GateOp.not
  C.size = n + m - 1 ∧
    (hasNot → ∃ (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m),
      (∀ i, ¬ rc (x 0) i ↔ i = x 1) ∧ (∀ j, ¬ cc (y 0) j ↔ j = y 1) ∧
      ∀ i j : Fin 4, A (x i) (y j) = (28036 : Nat).testBit (4*i.val+j.val)) ∧
    (hasNot → ¬ PEqualNP.Represents.RepSizeAtMost A (n+m)) ∧
    (¬ hasNot → ∃ e : Fin n ≃ Fin m, ∀ i j, A i j = decide (e i = j)) := by
  intro n m A hn hm
  dsimp only
  intro di dj ri cj C fan rep bound
  exact finalResult numeric hn hm A di dj ri cj C fan rep bound

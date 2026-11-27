import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25646_aux.Normalize
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

end PEqualNP.Outside.L_meta_25646_aux.Normalize

namespace PEqualNP.Outside.L_meta_25646_aux.Normalize
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

end PEqualNP.Outside.L_meta_25646_aux.Normalize

namespace PEqualNP.Outside.L_meta_25646_aux.Normalize
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

end PEqualNP.Outside.L_meta_25646_aux.Normalize

namespace PEqualNP.Outside.L_meta_25646_aux.Normalize
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

end PEqualNP.Outside.L_meta_25646_aux.Normalize

namespace PEqualNP.Outside.L_meta_25646_aux.Normalize

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

end PEqualNP.Outside.L_meta_25646_aux.Normalize

namespace PEqualNP.Outside.L_meta_25646_aux.Pins
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_count (l : List ℕ) (N : ℕ) (h : ∀ i ∈ l, i < N) :
    ∑ w ∈ Finset.range N, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a < N := h a (by simp)
    rw [List.length_cons, ← ih (fun i hi => h i (by simp [hi]))]
    simp [List.count_cons, Finset.sum_add_distrib, ha]

theorem key (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) :
    (∑ w ∈ Finset.range m, readsIn C (Finset.range C.size) w) +
      (∑ j ∈ Finset.range C.size, readsIn C (Finset.range C.size) (m + j)) =
    ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length := by
  rw [← Finset.sum_range_add]
  unfold readsIn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => sum_count _ _ fun i hi => ?_
  have h1 : j < C.size := Finset.mem_range.mp hj
  have := hrb j h1 i hi
  omega

theorem slots (C : Circuit)
    (hg : ∀ g ∈ C.gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    (∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length) +
      (@Finset.filter ℕ (fun k => (gateAt C k).op = GateOp.not) (fun d1 => Classical.propDecidable _)
        (Finset.range C.size)).card = C.size + C.size := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.sum_congr rfl (g := fun _ => 2) ?_]
  · simp [Circuit.size]
    omega
  · intro j hj
    have hj' : j < C.gates.length := Finset.mem_range.mp hj
    have hmem : gateAt C j ∈ C.gates := by
      simp only [gateAt, List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem hj'
    rcases hg _ hmem with ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem tail (s : ℕ) (f : ℕ → ℕ) (hs : 0 < s) (h : ∀ j < s, (f j = 0 ↔ j + 1 = s)) :
    (∑ j ∈ Finset.range (s - 1), (f j - 1)) + (s - 1) = ∑ j ∈ Finset.range s, f j := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hk : f k = 0 := (h k (by omega)).2 rfl
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ, hk, Nat.add_zero]
  have : ∀ j ∈ Finset.range k, f j - 1 + 1 = f j := fun j hj => by
    have hj' : j < k := Finset.mem_range.mp hj
    have : f j ≠ 0 := fun h0 => by have := (h j (by omega)).1 h0; omega
    omega
  rw [← Finset.sum_congr rfl this, Finset.sum_add_distrib]
  simp

end PEqualNP.Outside.L_meta_25646_aux.Pins

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def gates69 (C : Circuit) := Finset.range C.size
def reads69 (C : Circuit) (w : Nat) := readsIn C (gates69 C) w
noncomputable def neg69 (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>(gateAt C k).op=.not)
noncomputable def special (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact ((Finset.range (N+C.size)).filter (fun w=>2≤reads69 C w)) ∪
    (neg69 C).image (fun k=>N+k)
noncomputable def ordinary (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>N+k∉special N C)
noncomputable def exits69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈gates69 C \ ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∉special N C))
noncomputable def entries69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∈special N C))
def once69 (N : Nat) (C : Circuit) := (Finset.range N).filter (fun w=>reads69 C w=1)
def shapes69 (C : Circuit) : Prop := ∀g∈C.gates,
  ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)

def tree69 (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ ordinary N C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ reads69 C w=1 ∧ C.output≠w)

theorem ordinary_reads69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    reads69 C (N+k)≤1 := by
  classical
  obtain ⟨hk,hn⟩:=Finset.mem_filter.mp h
  have lt : k<C.size := Finset.mem_range.mp hk
  by_contra! many
  exact hn (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩))

theorem ordinary_index69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp h).1

end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def color69 (N : Nat) (C : Circuit) (w : Nat) : Bool :=
  if w∈special N C then true else if w<N then false else
    (gateAt C (w-N)).inputs.any (fun v => if hv : v<w then color69 N C v else false)
termination_by w

noncomputable def split69 (N : Nat) (C : Circuit) :=
  (ordinary N C).filter (fun j=>2≤((gateAt C j).inputs.filter (color69 N C)).length)

noncomputable def keep69 (N : Nat) (C : Circuit) := ordinary N C \ split69 N C

theorem color_special {N w : Nat} {C : Circuit} (h : w∈special N C) : color69 N C w=true := by
  rw [color69,ite_eq_left h]

theorem color_raw {N w : Nat} {C : Circuit} (hw : w<N) (h : w∉special N C) :
    color69 N C w=false := by rw [color69,ite_eq_right h,ite_eq_left hw]

theorem color_ordinary_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈ordinary N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true := by
  have ns := (Finset.mem_filter.mp hj).2
  rw [color69,ite_eq_right ns,ite_eq_right (by omega : ¬N+j<N),Nat.add_sub_cancel_left,List.any_eq_true]
  apply exists_congr
  intro w
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩

theorem color_keep_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈keep69 N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true :=
  color_ordinary_iff back (Finset.mem_sdiff.mp hj).1

theorem marked_keep_slots {N j : Nat} {C : Circuit} (hj : j∈keep69 N C) :
    ((gateAt C j).inputs.filter (color69 N C)).length≤1 := by
  obtain ⟨ord,no⟩ := Finset.mem_sdiff.mp hj
  by_contra! two
  exact no (Finset.mem_filter.mpr ⟨ord,two⟩)

theorem color_split_all {N j : Nat} {C : Circuit} (sh : shapes69 C) (hj : j∈split69 N C) :
    ∀ w∈(gateAt C j).inputs,color69 N C w=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  have jlt : j<C.gates.length := ordinary_index69 ord
  have mem : gateAt C j∈C.gates := by simp [gateAt,jlt]
  have len : (gateAt C j).inputs.length≤2 := by rcases sh _ mem with h|h <;> omega
  apply List.length_filter_eq_length_iff.mp
  have hl := List.length_filter_le (p:=color69 N C) (l:=(gateAt C j).inputs)
  omega

theorem color_split_self {N j : Nat} {C : Circuit} (back : ReadsBack N C) (hj : j∈split69 N C) :
    color69 N C (N+j)=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  apply (color_ordinary_iff back ord).2
  rw [←List.countP_pos_iff,List.countP_eq_length_filter]
  omega

private lemma maskedCount69 (l : List Nat) (A : Finset Nat) :
    l.countP (fun w=>decide (w∈A)) = ∑w∈A,l.count w := by
  classical
  let f := l.filter (fun w=>decide (w∈A))
  have sub : f.toFinset ⊆ A := by
    intro w hw
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change f.length=_
  calc
    _ = ∑w∈f.toFinset,f.count w := (List.sum_toFinset_count_eq_length f).symm
    _ = ∑w∈A,f.count w := Finset.sum_subset sub (fun _ _ h =>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))
    _ = _ := Finset.sum_congr rfl (fun w hw=>List.count_filter (by simpa using hw))

private lemma countCover69 (l : List Nat) (p s a : Nat→Bool)
    (cover : ∀w∈l,p w=true → s w=true ∨ a w=true) : l.countP p≤l.countP s+l.countP a := by
  induction l with
  | nil => simp
  | cons w ws ih =>
    have tail := ih (fun v hv=>cover v (List.mem_cons_of_mem _ hv))
    have head := cover w List.mem_cons_self
    cases hp : p w <;> cases hs : s w <;> cases ha : a w <;> simp_all [List.countP_cons] <;> omega

private theorem countedSlots69 {N : Nat} {C : Circuit} (P A : Finset Nat)
    (p : Nat→Bool) (pg : P⊆ordinary N C) (ag : A⊆ordinary N C)
    (cover : ∀ j∈P, ∀w∈(gateAt C j).inputs,p w=true →
      w∈special N C ∨ w∈A.image (fun t=>N+t)) :
    (∑j∈P,(gateAt C j).inputs.countP p)≤entries69 N C+A.card := by
  classical
  let I := A.image (fun j=>N+j)
  let specialSlot := fun w=>decide (w∈special N C)
  have each (j : Nat) (hj : j∈P) : (gateAt C j).inputs.countP p ≤
      (gateAt C j).inputs.countP specialSlot + ∑w∈I,(gateAt C j).inputs.count w := by
    rw [←maskedCount69]
    apply countCover69
    intro w hw hp
    exact (cover j hj w hw hp).imp (fun h=>by simpa [specialSlot] using h) (fun h=>by simpa [I] using h)
  have sl : (∑ j∈P,(gateAt C j).inputs.countP specialSlot) ≤ entries69 N C :=
    Finset.sum_le_sum_of_subset_of_nonneg pg (fun _ _ _ => Nat.zero_le _)
  have rest (w : Nat) (hw : w∈I) : (∑ j∈P,(gateAt C j).inputs.count w) ≤ 1 := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    apply le_trans (b:=reads69 C (N+j)) _ (ordinary_reads69 (ag hj))
    unfold reads69 readsIn
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
    exact fun q hq=>(Finset.mem_filter.mp (pg hq)).1
  have total := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_comm (s:=P) (t:=I)] at total
  have pool := Finset.sum_le_sum rest
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at pool
  have cap : I.card≤A.card := Finset.card_image_le
  omega

theorem splitCard69 {N : Nat} {C : Circuit} (_sh : shapes69 C) (back : ReadsBack N C) :
    (split69 N C).card≤entries69 N C := by
  classical
  let A := (ordinary N C).filter (fun j=>color69 N C (N+j)=true)
  have cover (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (hl : color69 N C w=true) : w∈special N C ∨ w∈A.image (fun t=>N+t) := by
    by_cases sp : w∈special N C
    · exact Or.inl sp
    right
    have wire : w<N+j := back j (ordinary_index69 hj) w hw
    have mid : N≤w := by by_contra! z;rw [color_raw z sp] at hl;contradiction
    have eq : N+(w-N)=w := by omega
    have idx : w-N<C.size := by have := ordinary_index69 hj;omega
    have good : w-N∈ordinary N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,by simpa only [eq] using sp⟩
    exact Finset.mem_image.mpr ⟨w-N,Finset.mem_filter.mpr ⟨good,by simpa only [eq] using hl⟩,eq⟩
  have account := countedSlots69 (ordinary N C) A (color69 N C) (fun _ h=>h)
    (fun _ h=>(Finset.mem_filter.mp h).1) cover
  have pay (j : Nat) (hj : j∈ordinary N C) :
      (if color69 N C (N+j)=true then 1 else 0) +
      (if 2≤((gateAt C j).inputs.filter (color69 N C)).length then 1 else 0) ≤
      (gateAt C j).inputs.countP (color69 N C) := by
    rw [List.countP_eq_length_filter]
    by_cases many : 2≤((gateAt C j).inputs.filter (color69 N C)).length
    · rw [ite_eq_left many];split <;> omega
    rw [ite_eq_right many]
    split
    · next hc =>
      have has := (color_ordinary_iff back hj).1 hc
      have pos := List.countP_pos_iff.mpr has
      rw [List.countP_eq_length_filter] at pos
      omega
    · omega
  have total := Finset.sum_le_sum pay
  rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter] at total
  change A.card+(split69 N C).card≤_ at total
  omega

theorem entrySlotsBound69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) :
    (∑j∈keep69 N C,(gateAt C j).inputs.countP
      (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))) ≤ 2*entries69 N C := by
  classical
  have cap := countedSlots69 (keep69 N C) (split69 N C)
    (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
    (fun _ h=>(Finset.mem_sdiff.mp h).1) (fun _ h=>(Finset.mem_filter.mp h).1) (by
      intro j hj w hw h
      rcases of_decide_eq_true h with s|⟨low,idx⟩
      · exact Or.inl s
      · exact Or.inr (Finset.mem_image.mpr ⟨w-N,idx,by omega⟩))
  have splitBound := splitCard69 sh back
  omega

end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def pool69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  once69 N C ∪ P.image (fun k=>N+k)

def branch69 (N : Nat) (C : Circuit) (P : Finset Nat) (x y : Nat) : Prop :=
  x∈pool69 N C P ∧ ∃k∈P, y=N+k ∧ x∈(gateAt C k).inputs

abbrev walk69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  Relation.ReflTransGen (branch69 N C P)

def sink69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Prop :=
  ∀ y, ¬ branch69 N C P x y

noncomputable def owner69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Nat := by
  classical exact if h : ∃y,walk69 N C P x y ∧ sink69 N C P y then h.choose else x

noncomputable def roots69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  (once69 N C).image (owner69 N C P)

noncomputable def src69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (once69 N C).filter (fun w=>owner69 N C P w=z)

noncomputable def reg69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact P.filter (fun k=>owner69 N C P (N+k)=z)

noncomputable def outside69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (reg69 N C P z).biUnion fun k =>
    (gateAt C k).inputs.toFinset.filter (fun w=>w∉pool69 N C P)

noncomputable def slots69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Nat := by
  classical exact ∑ k∈reg69 N C P z,(gateAt C k).inputs.countP (fun w=>decide (w∉pool69 N C P))

variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem reads_le_one69 (hp : P⊆ordinary N C) {w : Nat} (hw : w∈pool69 N C P) : reads69 C w≤1 := by
  rcases Finset.mem_union.mp hw with h | h
  · exact (Finset.mem_filter.mp h).2.le
  · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp h;exact ordinary_reads69 (hp hk)

theorem reader69 {w i j : Nat} (one : reads69 C w≤1) (hi : i<C.size) (hj : j<C.size)
    (a : w∈(gateAt C i).inputs) (b : w∈(gateAt C j).inputs) : i=j := by
  by_contra ne
  have h:=Finset.add_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _)
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) ne
  have ai:=List.count_pos_iff.mpr a
  have bj:=List.count_pos_iff.mpr b
  change _ ≤ reads69 C w at h
  omega

theorem next_unique69 (hp : P⊆ordinary N C) : Relator.RightUnique (branch69 N C P) := by
  rintro w x y ⟨hw,i,hi,rfl,a⟩ ⟨_,j,hj,rfl,b⟩
  rw [reader69 (reads_le_one69 hp hw) (ordinary_index69 (hp hi)) (ordinary_index69 (hp hj)) a b]

theorem next_lt69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (h : branch69 N C P x y) : x<y ∧ y<N+C.size := by
  obtain ⟨_,k,hk,rfl,inp⟩:=h
  have lt:=ordinary_index69 (hp hk)
  exact ⟨back k lt x inp,by omega⟩

theorem walk_in69 {x y : Nat} (h : walk69 N C P x y) (hx : x∈pool69 N C P) :
    y∈pool69 N C P := by
  induction h with
  | refl => exact hx
  | tail _ e _ =>
    obtain ⟨_,k,hk,rfl,_⟩ := e
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)

theorem owner_spec69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (w : Nat) :
    walk69 N C P w (owner69 N C P w) ∧ sink69 N C P (owner69 N C P w) := by
  classical
  have exists' (i : Nat) : ∀x,N+C.size-x=i → ∃y,walk69 N C P x y ∧ sink69 N C P y := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro x eq
      by_cases e : ∃y,branch69 N C P x y
      · obtain ⟨y,hy⟩:=e
        obtain ⟨lt,bound⟩:=next_lt69 hp back hy
        obtain ⟨v,path,sink⟩:=ih (N+C.size-y) (by omega) y rfl
        exact ⟨v,path.head hy,sink⟩
      · exact ⟨x,.refl,fun y h=> e ⟨y,h⟩⟩
  have h:=exists' _ w rfl
  simpa only [owner69,dif_pos h] using h.choose_spec

theorem owner_same69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (e : branch69 N C P x y) : owner69 N C P x = owner69 N C P y := by
  have a := owner_spec69 hp back x
  have b := owner_spec69 hp back y
  have term {u v : Nat} (s : sink69 N C P u) (path : walk69 N C P u v) : u=v := by
    rcases path.cases_head with eq|⟨z,e,_⟩
    · exact eq
    · exact (s z e).elim
  rcases Relation.ReflTransGen.total_of_right_unique (next_unique69 hp)
    a.1 (b.1.head e) with h|h
  · exact term a.2 h
  · exact (term b.2 h).symm

theorem fiber69 (z w : Nat) :
    w∈src69 N C P z ∪ (reg69 N C P z).image (fun k=>N+k) ↔
      w∈pool69 N C P ∧ owner69 N C P w=z := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with a|b
    · obtain ⟨h,e⟩:=Finset.mem_filter.mp a;exact ⟨Finset.mem_union_left _ h,e⟩
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      obtain ⟨h,e⟩:=Finset.mem_filter.mp hk;exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ h),e⟩
  · rintro ⟨pool,e⟩
    rcases Finset.mem_union.mp pool with a|b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨a,e⟩)
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hk,e⟩))

theorem root_info69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    z∈pool69 N C P ∧ sink69 N C P z ∧ owner69 N C P z=z ∧ (src69 N C P z).Nonempty := by
  obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
  have sp:=owner_spec69 hp back u
  refine ⟨walk_in69 sp.1 (Finset.mem_union_left _ hu),sp.2,?_,⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩⟩
  have p:=(owner_spec69 hp back (owner69 N C P u)).1
  rcases p.cases_head with eq|⟨x,step,_⟩
  · exact eq.symm
  · exact (sp.2 x step).elim

end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem root_zero69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    readsIn C (reg69 N C P z) z=0 := by
  obtain ⟨pool,sink,_,_⟩:=root_info69 hp back hz
  apply Finset.sum_eq_zero
  intro j hj;apply List.count_eq_zero.mpr
  intro h;exact sink (N+j) ⟨pool,j,(Finset.mem_filter.mp hj).1,rfl,h⟩

theorem local_read69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z w : Nat}
    (pool : w∈pool69 N C P) (ow : owner69 N C P w=z) (other : w≠z) :
    readsIn C (reg69 N C P z) w=1 ∧ reads69 C w=1 := by
  obtain ⟨way,_⟩:=owner_spec69 hp back w
  rw [ow] at way
  obtain ⟨_,⟨_,k,hk,rfl,hit⟩,_⟩:=way.cases_head.resolve_left other
  have eq := owner_same69 hp back (show branch69 N C P w (N+k) from ⟨pool,k,hk,rfl,hit⟩)
  have mem : k∈reg69 N C P z := Finset.mem_filter.mpr ⟨hk,eq.symm.trans ow⟩
  have le : (gateAt C k).inputs.count w ≤ readsIn C (reg69 N C P z) w :=
    Finset.single_le_sum (fun l _=>Nat.zero_le ((gateAt C l).inputs.count w)) mem
  have bound : readsIn C (reg69 N C P z) w ≤ reads69 C w :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun j hj =>
      Finset.mem_range.mpr (ordinary_index69 (hp (Finset.mem_filter.mp hj).1))) (fun _ _ _=>Nat.zero_le _)
  have counted:=List.count_pos_iff.mpr hit;have all:=reads_le_one69 hp pool
  omega

theorem pool_bound69 (hp : P⊆ordinary N C) {w : Nat} (pool : w∈pool69 N C P) : w<N+C.size := by
  rcases Finset.mem_union.mp pool with h|h
  · have lt:=Finset.mem_range.mp (Finset.mem_filter.mp h).1;omega
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h;have:=ordinary_index69 (hp hj);omega

theorem walk_le69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat} (path : walk69 N C P x y) :
    x≤y := by
  induction path with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (next_lt69 hp back e).1.le

theorem outside_mem69 {z w : Nat} :
    w∈outside69 N C P z ↔ w∉pool69 N C P ∧ ∃k∈reg69 N C P z,w∈(gateAt C k).inputs := by
  classical
  simp only [outside69,Finset.mem_biUnion,Finset.mem_filter,List.mem_toFinset]
  grind

private theorem read_le_slots69 {z w : Nat} (out : w∉pool69 N C P) :
    readsIn C (reg69 N C P z) w ≤ slots69 N C P z := by
  classical
  apply Finset.sum_le_sum
  intro k _
  induction (gateAt C k).inputs with
  | nil => simp
  | cons a l ih =>
    simp only [decide_not] at ih
    by_cases eq : a=w
    · subst a;simp [List.count_cons,List.countP_cons,out,ih]
    · by_cases pa:a∈pool69 N C P <;> simp [List.count_cons,List.countP_cons,eq,pa,ih] <;> omega

theorem out_pos69 {z w : Nat} (h : w∈outside69 N C P z) :
    0<readsIn C (reg69 N C P z) w ∧ readsIn C (reg69 N C P z) w≤ slots69 N C P z := by
  obtain ⟨no,k,hk,hx⟩:=outside_mem69.mp h
  exact ⟨(List.count_pos_iff.mpr hx).trans_le
    (Finset.single_le_sum (fun j _=>Nat.zero_le ((gateAt C j).inputs.count w)) hk),read_le_slots69 no⟩

theorem outside_card69 {z : Nat} : (outside69 N C P z).card ≤ slots69 N C P z := by
  classical
  unfold outside69 slots69
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro k _
  have h (l : List Nat) : (l.toFinset.filter (fun w=>w∉pool69 N C P)).card ≤
      l.countP (fun w=>decide (w∉pool69 N C P)) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [decide_not] at ih
      by_cases hw:w∈pool69 N C P
      · simpa [Finset.filter_insert,hw,List.countP_cons] using ih
      · simp [Finset.filter_insert,hw,List.countP_cons]
        exact (Finset.card_insert_le _ _).trans (by omega)
  exact h _

theorem outside_empty69 {z : Nat} : outside69 N C P z=∅ ↔ slots69 N C P z=0 := by
  classical
  constructor
  · intro empty;apply Finset.sum_eq_zero;intro k hk
    apply List.countP_eq_zero.mpr
    intro w hw
    simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_not]
    by_contra out
    have h : w∈outside69 N C P z := outside_mem69.mpr ⟨out,k,hk,hw⟩
    simp [empty] at h
  · intro z0;apply Finset.card_eq_zero.mp;have le:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z);omega

theorem subtree69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (sh : shapes69 C)
    (last : C.output+1=N+C.size) {z : Nat} (hz : z∈roots69 N C P)
    (slot : slots69 N C P z≤1) : tree69 N C (src69 N C P z) (outside69 N C P z) := by
  classical
  obtain ⟨zp,sink,zown,nonempty⟩:=root_info69 hp back hz
  have bound:=pool_bound69 hp zp
  refine ⟨reg69 N C P z,z,fun j hj=>hp (Finset.mem_filter.mp hj).1,
    (fiber69 z z).mpr ⟨zp,zown⟩,root_zero69 hp back hz,?_,?_,?_⟩
  · intro w hw
    obtain ⟨out,k,hk,read⟩:=outside_mem69.mp hw
    have lt:=back k (ordinary_index69 (hp (Finset.mem_filter.mp hk).1)) w read
    have path:=(owner_spec69 hp back (N+k)).1
    rw [(Finset.mem_filter.mp hk).2] at path
    have cmp:=walk_le69 hp back path
    obtain ⟨pos,le⟩:=out_pos69 hw
    exact ⟨fun h=>out ((fiber69 z w).mp h).1,by omega,by omega⟩
  · intro j hj
    obtain ⟨keep,own⟩:=Finset.mem_filter.mp hj
    have ord:=hp keep;have jl:=ordinary_index69 ord
    have mem : gateAt C j∈C.gates := by have h:j<C.gates.length:=jl;simp [gateAt,h]
    rcases sh _ mem with ao | no
    · refine ⟨ao.1,ao.2,?_⟩
      intro w wh
      by_cases pooled:w∈pool69 N C P
      · exact Or.inl ((fiber69 z w).mpr ⟨pooled,(owner_same69 hp back ⟨pooled,j,keep,rfl,wh⟩).trans own⟩)
      · exact Or.inr (outside_mem69.mpr ⟨pooled,j,hj,wh⟩)
    · have ns: N+j∉special N C := (Finset.mem_filter.mp ord).2
      apply (ns (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (show j∈neg69 C from Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jl,no.1⟩)))).elim
  · intro w hw diff
    obtain ⟨pool,own⟩:=(fiber69 z w).mp hw
    obtain ⟨loc,all⟩:=local_read69 hp back pool own diff
    have path:=(owner_spec69 hp back w).1
    rw [own] at path
    have le:=walk_le69 hp back path
    exact ⟨loc,all,by omega⟩

end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C:Circuit}
lemma keepSub69 : keep69 N C ⊆ ordinary N C := Finset.sdiff_subset
lemma colorOnce69 {w:Nat} (h:w∈once69 N C) : color69 N C w=false := by
  obtain ⟨hw,one⟩:=Finset.mem_filter.mp h
  have lo:=Finset.mem_range.mp hw
  apply color_raw lo
  intro hs
  rcases Finset.mem_union.mp hs with rep|notw
  · have high:2≤reads69 C w := (Finset.mem_filter.mp rep).2
    omega
  · obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp notw;omega
lemma colorOuter69 (back:ReadsBack N C) {j w:Nat} (hp:j∈keep69 N C) (hit:w∈(gateAt C j).inputs)
    (out:w∉pool69 N C (keep69 N C)) : color69 N C w=true := by
  classical
  have jj:=ordinary_index69 (keepSub69 hp)
  have wr:=back j jj w hit
  by_cases hs:w∈special N C
  · exact color_special hs
  by_cases low:w<N
  · have used:0<reads69 C w := by
      have h:=Finset.single_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr jj)
      have count:=List.count_pos_iff.mpr hit
      change _≤reads69 C w at h
      omega
    have one:reads69 C w=1 := by
      by_contra! ne
      apply hs
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩)
    exact (out (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr low,one⟩))).elim
  · let k:=w-N
    have eq:N+k=w := by dsimp [k];omega
    have ord:k∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [k];omega),by rwa [eq]⟩
    by_cases sp:k∈split69 N C
    · exact eq ▸ color_split_self back sp
    · have kkeep:k∈keep69 N C:=Finset.mem_sdiff.mpr ⟨ord,sp⟩
      exact (out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,kkeep,eq⟩))).elim

lemma markedInputs69 (back:ReadsBack N C) {j:Nat} (h:j∈keep69 N C) :
    (gateAt C j).inputs.countP (color69 N C) = if color69 N C (N+j) then 1 else 0 := by
  have le:=marked_keep_slots h
  rw [←List.countP_eq_length_filter] at le
  have pos := color_keep_iff back h
  rw [←List.countP_pos_iff] at pos
  cases hx:color69 N C (N+j)
  · change (gateAt C j).inputs.countP (color69 N C)=0
    by_contra! ne
    have eq:=pos.mpr (by omega)
    rw [hx] at eq;contradiction
  · change (gateAt C j).inputs.countP (color69 N C)=1
    have hp:=pos.mp hx
    omega

lemma splitInputCount69 (L:List Nat) (p:Nat→Bool) (pool A:Finset Nat)
    (spec:∀w∈L, (p w=true ↔ w∉pool ∨ w∈A) ∧ (w∈A → w∈pool)) :
    L.countP p = L.countP (fun w=>decide (w∉pool)) + ∑w∈A,L.count w := by
  classical
  induction L with
  | nil => simp
  | cons x xs ih =>
    have t:=ih (fun w hw=>spec w (List.mem_cons_of_mem _ hw))
    simp only [List.countP_cons,List.count_cons,Finset.sum_add_distrib]
    have a:=spec x (by simp)
    by_cases xA:x∈A <;> by_cases xp:x∈pool <;> cases xx:p x <;>
      simp_all <;> omega
end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem conserved69 {N z:Nat} {C:Circuit} (back:ReadsBack N C)
    (hz:z∈roots69 N C (keep69 N C))
    (lr:∀ j∈reg69 N C (keep69 N C) z,
      readsIn C (reg69 N C (keep69 N C) z) (N+j)=if N+j=z then 0 else 1) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  classical
  let P:=keep69 N C
  let pool:=pool69 N C P
  let rg:=reg69 N C P z
  let hot:=rg.filter (fun j=>color69 N C (N+j)=true)
  let A:=hot.image (fun j=>N+j)
  have acard:A.card=hot.card:=Finset.card_image_of_injective _ (fun _ _ e=>Nat.add_left_cancel e)
  have rgKeep (j:Nat) (hj:j∈rg):j∈P:=(Finset.mem_filter.mp hj).1
  have memA {w:Nat} : w∈A ↔ w∈pool ∧ owner69 N C P w=z ∧ color69 N C w=true := by
    constructor
    · intro h;obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h
      obtain ⟨jr,marked⟩:=Finset.mem_filter.mp hj
      exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (rgKeep _ jr)),(Finset.mem_filter.mp jr).2,marked⟩
    · rintro ⟨h,o,t⟩
      rcases Finset.mem_union.mp h with raw|gate
      · exact (by rw [colorOnce69 raw] at t; contradiction : False).elim
      · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp gate
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hj,o⟩,t⟩,rfl⟩
  have inEq (j:Nat) (hj:j∈rg) :
      (gateAt C j).inputs.countP (color69 N C) =
        (gateAt C j).inputs.countP (fun w=>decide (w∉pool)) + ∑w∈A,(gateAt C j).inputs.count w := by
    apply splitInputCount69
    intro w hit
    have memPool (h:w∈pool) : owner69 N C P w=z := by
      have p:=owner_same69 (P:=P) keepSub69 back (show branch69 N C P w (N+j) from ⟨h,j,rgKeep _ hj,rfl,hit⟩)
      exact p.trans (Finset.mem_filter.mp hj).2
    refine ⟨⟨fun t=>?_,?_⟩,fun h=>(memA.mp h).1⟩
    · by_cases pw:w∈pool
      · exact Or.inr (memA.mpr ⟨pw,memPool pw,t⟩)
      · exact Or.inl pw
    · rintro (out|inside)
      · exact colorOuter69 back (rgKeep _ hj) hit out
      · exact (memA.mp inside).2.2
  have calcAll : hot.card=slots69 N C P z+∑w∈A,readsIn C rg w := by
    calc
      hot.card = ∑j∈rg, if color69 N C (N+j) then 1 else 0 := by simp only [hot,Finset.card_filter]
      _ = ∑j∈rg,(gateAt C j).inputs.countP (color69 N C) :=
        Finset.sum_congr rfl (fun j hj=>(markedInputs69 back (rgKeep _ hj)).symm)
      _ = _ := by
        rw [Finset.sum_congr rfl inEq,Finset.sum_add_distrib]
        congr 1;exact Finset.sum_comm
  have lower : (∑w∈A,readsIn C rg w)+(if z∈A then 1 else 0)=A.card := by
    calc
      _ = (∑w∈A,if w=z then 0 else 1) + (∑w∈A,if w=z then 1 else 0) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro w hw;obtain ⟨j,m,rfl⟩:=Finset.mem_image.mp hw
          exact lr _ (Finset.mem_filter.mp m).1
        · simp
      _ = ∑_w∈A,1 := by
        rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro w _;split <;> simp_all
      _ = _ := by simp
  have root:=root_info69 (P:=P) keepSub69 back hz
  have za : z∈A ↔ color69 N C z=true := ⟨fun h=>(memA.mp h).2.2,fun h=>memA.mpr ⟨root.1,root.2.2.1,h⟩⟩
  change slots69 N C P z=_
  simp only [za] at lower
  omega
end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem fiberSlots69 {N z:Nat} {C:Circuit} (back:ReadsBack N C) (hz:z∈roots69 N C (keep69 N C)) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  apply conserved69 back hz
  intro j hj
  by_cases eq:N+j=z
  · rw [eq,ite_eq_left rfl]
    exact root_zero69 keepSub69 back hz
  · rw [ite_eq_right eq]
    obtain ⟨m,e⟩:=Finset.mem_filter.mp hj
    have pool:N+j∈pool69 N C (keep69 N C):=Finset.mem_union_right _ (Finset.mem_image_of_mem _ m)
    exact (local_read69 keepSub69 back pool e eq).1
end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_reads_mask69 (l : List Nat) (A : Finset Nat) :
    (∑w∈A,l.count w) = l.countP (fun w=>decide (w∈A)) := by
  classical
  let f:=l.filter (fun w=>decide (w∈A))
  have sub:f.toFinset⊆A := fun _ hw=>of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change _=f.length
  calc
    _ = ∑w∈A,f.count w := Finset.sum_congr rfl (fun w hw=>(List.count_filter (by simpa using hw)).symm)
    _ = ∑w∈f.toFinset,f.count w := (Finset.sum_subset sub (fun _ _ h=>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))).symm
    _ = _ := List.sum_toFinset_count_eq_length f

private theorem pure_sink69 {N z : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j))
    (hz : z∈roots69 N C (keep69 N C)) (zero : slots69 N C (keep69 N C) z=0) (out : z≠C.output) :
    z∉special N C ∧ ∃k∈gates69 C \ ordinary N C, z∈(gateAt C k).inputs := by
  classical
  obtain ⟨pool,sink,_,_⟩:=root_info69 keepSub69 back hz
  have slot:=fiberSlots69 back hz
  have off : color69 N C z=false := by cases h:color69 N C z <;> simp_all
  have ns : z∉special N C := fun h => by have a:=color_special h;rw [off] at a;contradiction
  have pos : 0<reads69 C z := by
    rcases Finset.mem_union.mp pool with raw|internal
    · have one : reads69 C z=1 := (Finset.mem_filter.mp raw).2;omega
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp internal
      have lt:=ordinary_index69 (keepSub69 hj)
      exact live j lt (by omega)
  have seek : ∃ k∈gates69 C, z∈(gateAt C k).inputs := by
    by_contra! no
    have none : reads69 C z=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
    omega
  obtain ⟨k,hk,hit⟩:=seek
  refine ⟨ns,k,Finset.mem_sdiff.mpr ⟨hk,?_⟩,hit⟩
  intro ord
  by_cases split:k∈split69 N C
  · have on:=color_split_all sh split z hit
    rw [off] at on;contradiction
  · exact sink (N+k) ⟨pool,k,Finset.mem_sdiff.mpr ⟨ord,split⟩,rfl,hit⟩

theorem pure_count69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)).card ≤ exits69 N C+1 := by
  classical
  let T:=(roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)
  let A:=T.erase C.output
  let gs:=gates69 C \ ordinary N C
  have obs (w : Nat) (hw:w∈A) : w∉special N C ∧ ∃k∈gs, w∈(gateAt C k).inputs := by
    obtain ⟨different,hh⟩:=Finset.mem_erase.mp hw
    obtain ⟨inR,zero⟩:=Finset.mem_filter.mp hh
    exact pure_sink69 sh back last live inR zero different
  have each (w:Nat) (hw:w∈A) : 1 ≤ ∑k∈gs,(gateAt C k).inputs.count w := by
    obtain ⟨k,hk,hit⟩:=(obs w hw).2
    exact (List.count_pos_iff.mpr hit).trans_le
      (Finset.single_le_sum (fun t _=>Nat.zero_le ((gateAt C t).inputs.count w)) hk)
  have bound : A.card≤exits69 N C := by
    calc
      _ = ∑ _∈A,1 := by simp
      _ ≤ ∑w∈A,∑k∈gs,(gateAt C k).inputs.count w := Finset.sum_le_sum each
      _ = ∑k∈gs,∑w∈A,(gateAt C k).inputs.count w := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        rw [sum_reads_mask69]
        exact List.countP_mono_left (fun w _ h => decide_eq_true ((obs w (of_decide_eq_true h)).1))
  change T.card≤exits69 N C+1
  have incl : T⊆insert C.output A := by
    intro z mem;by_cases e:z=C.output
    · exact Finset.mem_insert.mpr (Or.inl e)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨e,mem⟩))
  have step:=Finset.card_le_card incl
  have cap:=Finset.card_insert_le C.output A
  change T.card≤(insert C.output A).card at step
  omega
end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem mixed_count69 {N:Nat} {C:Circuit} (sh:shapes69 C) (back:ReadsBack N C) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)).card≤2*entries69 N C := by
  classical
  let P:=keep69 N C
  let R:=(roots69 N C P).filter (fun z=>slots69 N C P z≠0)
  let f:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∉pool69 N C P))
  let g:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
  have per (j:Nat) (hj:j∈P): f j≤g j := by
    apply List.countP_mono_left
    intro w hw out'
    have out:w∉pool69 N C P:=of_decide_eq_true out'
    apply decide_eq_true
    by_cases sp:w∈special N C
    · exact Or.inl sp
    · have color:=colorOuter69 back hj hw out
      have nle : N≤w:=by by_contra! h;rw [color_raw h sp] at color;contradiction
      have eq:N+(w-N)=w:=by omega
      have ji:=ordinary_index69 (keepSub69 hj)
      have wi:=back j ji w hw
      have ord:w-N∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [eq]⟩
      refine Or.inr ⟨nle,?_⟩
      by_contra ns
      have inside:w-N∈P:=Finset.mem_sdiff.mpr ⟨ord,ns⟩
      exact out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,inside,eq⟩))
  have lower (z:Nat) (hz:z∈R) : 1≤ slots69 N C P z := by
    have neq:slots69 N C P z≠0:=(Finset.mem_filter.mp hz).2
    omega
  change R.card≤_
  calc
    R.card = ∑_z∈R,1 := by simp
    _ ≤ ∑z∈R,slots69 N C P z := Finset.sum_le_sum lower
    _ = ∑j∈P.filter (fun i=>owner69 N C P (N+i)∈R), f j :=
      Finset.sum_fiberwise_eq_sum_filter P R (fun j=>owner69 N C P (N+j)) f
    _ ≤ ∑j∈P,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)
    _ ≤ ∑j∈P,g j := Finset.sum_le_sum per
    _ ≤ _ := entrySlotsBound69 sh back
end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux.Partition
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem finish69 (N : Nat) (C : Circuit) (sh : shapes69 C) (back : ReadsBack N C)
    (_pos : 0<C.size) (last : C.output+1=N+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ∃ pure chains : List (Finset Nat),
      pure.length≤exits69 N C+1 ∧ chains.length≤2*entries69 N C ∧
      (pure++chains).Pairwise (fun A B=>Disjoint A B) ∧
      (pure++chains).toFinset.biUnion (fun S=>S)=once69 N C ∧
      (∀S∈pure,S.Nonempty ∧ tree69 N C S ∅) ∧
      (∀S∈chains,S.Nonempty ∧ ∃b : Nat,tree69 N C S {b}) := by
  classical
  let P:=keep69 N C
  let roots:=roots69 N C P
  let Q:=roots.filter (fun z=>slots69 N C P z=0)
  let M:=roots.filter (fun z=>slots69 N C P z≠0)
  let leaf:=src69 N C P
  let qr:=Q.toList
  let mr:=M.toList
  have qmem (z:Nat) : z∈qr ↔ z∈roots ∧ slots69 N C P z=0 := by simp [qr,Q]
  have mmem (z:Nat) : z∈mr ↔ z∈roots ∧ slots69 N C P z≠0 := by simp [mr,M]
  have covered (z:Nat) : z∈qr++mr ↔ z∈roots := by
    rw [List.mem_append,qmem,mmem];tauto
  have nd : (qr++mr).Nodup := by
    refine List.nodup_append.mpr ⟨Q.nodup_toList,M.nodup_toList,?_⟩
    intro x hx y hy e;subst y;exact (mmem x|>.mp hy).2 ((qmem x|>.mp hx).2)
  have fiber {w z:Nat}: w∈leaf z ↔ w∈once69 N C ∧ owner69 N C P w=z := Finset.mem_filter
  have facts {z:Nat} (hz:z∈roots) : (leaf z).Nonempty ∧
      tree69 N C (leaf z) (outside69 N C P z) := by
    have count:=fiberSlots69 back hz
    have le : slots69 N C P z≤1 := by rw [count];split <;> decide
    exact ⟨(root_info69 keepSub69 back hz).2.2.2,subtree69 keepSub69 back sh last hz le⟩
  refine ⟨qr.map leaf,mr.map leaf,?_,?_,?_,?_,?_,?_⟩
  · simpa only [qr,List.length_map,Finset.length_toList] using pure_count69 sh back last live
  · simpa only [mr,List.length_map,Finset.length_toList] using mixed_count69 sh back
  · rw [←List.map_append,List.pairwise_map]
    apply nd.imp
    intro a b diff
    apply Finset.disjoint_left.mpr
    intro w ha hb;exact diff ((fiber.mp ha).2.symm.trans (fiber.mp hb).2)
  · rw [←List.map_append]
    ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨_,⟨z,_,rfl⟩,hit⟩;exact (fiber.mp hit).1
    · intro raw
      let z:=owner69 N C P w
      have root:z∈roots:=Finset.mem_image_of_mem _ raw
      exact ⟨leaf z,⟨z,(covered z).mpr root,rfl⟩,fiber.mpr ⟨raw,rfl⟩⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,zero⟩:=(qmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    rw [outside_empty69.mpr zero] at tree
    exact ⟨ne,tree⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,nz⟩:=(mmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    have card : (outside69 N C P z).card=1 := by
      have cap:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z)
      have count:=fiberSlots69 back rt
      have nonempty : (outside69 N C P z).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (fun h=>nz (outside_empty69.mp h))
      have pos:=Finset.card_pos.mpr nonempty
      change slots69 N C P z=_ at count
      split at count <;> omega
    obtain ⟨b,eq⟩:=Finset.card_eq_one.mp card
    exact ⟨ne,b,eq ▸ tree⟩
end PEqualNP.Outside.L_meta_25646_aux.Partition

namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

abbrev Active (C : Circuit) := readsIn C (Finset.range C.size)
def DifferentRows {n m : ℕ} (G : Fin n → Fin m → Bool) := ∀ a b, a≠b → ∃ c, G a c≠G b c
def DifferentCols {n m : ℕ} (G : Fin n → Fin m → Bool) := ∀ c d, c≠d → ∃ a, G a c≠G a d

theorem output_not_raw {n m : ℕ} {G : Fin n → Fin m → Bool} {C : Circuit} (rep : Represents G C)
    (horizontal : ∃ a c d, G a c ≠ G a d) (vertical : ∃ a b c, G a c ≠ G b c) : n+m≤C.output := by
  by_contra! small
  have readRaw (a c) : G a c=decide (C.output=a.val ∨ C.output=n+c.val) := by
    rw [←rep a c]
    change (Normalize.run C.gates (oneEach a c)).getD C.output false=_
    rw [Normalize.run_input _ _ _ (by rwa [Normalize.oneEach_length]),Normalize.oneEach_getD]
  by_cases l : C.output<n
  · obtain ⟨a,c,d,diff⟩ := horizontal
    apply diff
    rw [readRaw,readRaw]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]; omega
  · obtain ⟨a,b,c,diff⟩ := vertical
    have ha := a.isLt; have hb := b.isLt
    apply diff
    rw [readRaw,readRaw]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]; omega

theorem wire_positive {C : Circuit} {w j : ℕ} (hj : j<C.size) (hw : w∈(gateAt C j).inputs) :
    0<Active C w := lt_of_lt_of_le (List.count_pos_iff.mpr hw) (Finset.single_le_sum
      (f:=fun k => (gateAt C k).inputs.count w) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj))

theorem normalized {n m : ℕ} {G : Fin n → Fin m → Bool} (C : Circuit) (fan : FanInTwo C) (mono : Monotone2 C)
    (rep : Represents G C) (horizontal : ∃ a c d, G a c ≠ G a d) (vertical : ∃ a b c, G a c ≠ G b c) :
    ∃ D : Circuit, D.size≤C.size ∧ Monotone2 D ∧ Represents G D ∧ ReadsBack (n+m) D ∧
      (∀ g∈D.gates, ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)) ∧
      0<D.size ∧ D.output+1=n+m+D.size ∧ (∀ j<D.size, j+1<D.size → 0<Active D (n+m+j)) := by
  classical
  let N := n+m
  let y (p : Fin n × Fin m) := oneEach p.1 p.2
  let f (p : Fin n × Fin m) := G p.1 p.2
  have len (p) : (y p).length=N := Normalize.oneEach_length _ _
  have nc : ¬∃ b : Bool, ∀ p, f p=b := by
    rintro ⟨z,h⟩
    obtain ⟨a,b,c,ne⟩ := vertical
    exact ne ((h (a,c)).trans (h (b,c)).symm)
  obtain ⟨E,shape,back,sz,values⟩ := Normalize.engine True N N C y y len len ∅ fan (fun _ => mono)
    (fun w hw => Or.inr ⟨w,hw,fun _ => rfl⟩)
    (fun ⟨z,h⟩ => nc ⟨z,fun p => (rep p.1 p.2).symm.trans (h p)⟩) (by simp)
  have esize : E.size≤C.size := by simpa only [Finset.card_empty,Nat.add_zero] using sz
  obtain ⟨D,dshape,db,ds,dv,live⟩ := Normalize.finish_live True N y len f nc E shape back
    (fun p => (values p).trans (rep p.1 p.2))
  have dr : Represents G D := fun a c => dv (a,c)
  have out := output_not_raw dr horizontal vertical
  have bound : D.output<N+D.size := by
    by_contra! high
    apply nc; refine ⟨false,?_⟩; intro p
    rw [←dv p]
    change (Normalize.run D.gates (y p)).getD D.output false=false
    exact Normalize.past _ _ _ (by rw [len]; exact high)
  have pos : 0<D.size := by dsimp [N] at bound; omega
  let last : Fin D.gates.length := ⟨D.size-1,by change D.size-1<D.size; omega⟩
  have final : N+last.val=D.output := by
    by_contra no
    obtain ⟨j,lt,_⟩ := live last no
    have hj := j.isLt
    change D.size-1<j.val at lt
    change j.val<D.size at hj
    omega
  have lastEq : D.output+1=N+D.size := by change N+(D.size-1)=D.output at final; omega
  refine ⟨D,ds.trans esize,Normalize.good_mono dshape trivial,dr,db,?_,pos,lastEq,?_⟩
  · intro g hg
    rcases (dshape g hg).1 with ⟨op,a,h⟩|⟨op,a,b,_,h⟩
    · exact Or.inr ⟨op,by simp [h]⟩
    · exact Or.inl ⟨op,by simp [h]⟩
  · intro j hj nonfinal
    have ne : N+j≠D.output := by omega
    obtain ⟨p,_,usage⟩ := live ⟨j,hj⟩ ne
    have ray : (D.gates.get p)=gateAt D p.val := (List.getD_eq_getElem _ _ p.isLt).symm
    change Normalize.reads (D.gates.get p) (N+j) at usage
    rw [ray] at usage
    apply wire_positive p.isLt
    rcases usage with ⟨_,h⟩|⟨_,h⟩
    · cases l : (gateAt D p.val).inputs with
      | nil => simp [l] at h
      | cons a tail =>
        simp [l] at h
        exact List.mem_cons.mpr (Or.inl h.symm)
    · exact h

theorem observed_agree {N : ℕ} {C : Circuit} (back : ReadsBack N C) (x y : List Bool)
    (lx : x.length=N) (ly : y.length=N)
    (h : ∀ i<N, 0<Active C i → x.getD i false=y.getD i false) :
    ∀ w, N≤w → (Normalize.run C.gates x).getD w false=(Normalize.run C.gates y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro ge
    by_cases far : N+C.size≤w
    · rw [Normalize.past C.gates x _ (by rw [lx]; exact far),Normalize.past C.gates y _ (by rw [ly]; exact far)]
    let j := w-N
    have eq : N+j=w := Nat.add_sub_of_le ge
    have len : j<C.size := by dsimp [j]; omega
    rw [←eq,Normalize.gv N C back x lx j len,Normalize.gv N C back y ly j len]
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases raw : i<N
    · rw [Normalize.run_input _ _ _ (by rwa [lx]),Normalize.run_input _ _ _ (by rwa [ly])]
      exact h i raw (wire_positive len hi)
    · have smaller := back j len i hi
      exact ih i (by omega) (by omega)

end PEqualNP.Outside.L_meta_25646_aux
namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def used (N : ℕ) (C : Circuit) := ((Finset.range N).filter (fun w => 1≤Active C w)).card
def surplus (N : ℕ) (C : Circuit) := ∑ w∈Finset.range (N+C.size), (Active C w-1)
noncomputable def budget (N : ℕ) (C : Circuit) := surplus N C+(Partition.neg69 C).card

theorem active_last {N : ℕ} (C : Circuit) (back : ReadsBack N C) (pos : 0<C.size)
    (live : ∀ j<C.size, j+1<C.size → 0<Active C (N+j)) :
    ∀ j<C.size, Active C (N+j)=0 ↔ j+1=C.size := by
  intro j hj
  constructor
  · intro zero
    by_contra ne
    have := live j hj (by omega)
    omega
  · intro last
    apply Finset.sum_eq_zero
    intro k hk
    apply List.count_eq_zero.mpr
    intro hit
    have kk := Finset.mem_range.mp hk
    have earlier := back k kk _ hit
    omega

theorem budget_eq {N : ℕ} (C : Circuit) (shape : Partition.shapes69 C) (back : ReadsBack N C)
    (pos : 0<C.size) (live : ∀ j<C.size, j+1<C.size → 0<Active C (N+j)) :
    C.size+1=used N C+budget N C := by
  classical
  let v := Active C
  let rawExtra := ∑ w∈Finset.range N,(v w-1)
  let gateExtra := ∑ j∈Finset.range C.size,(v (N+j)-1)
  have raw : (∑ w∈Finset.range N,v w)=used N C+rawExtra := by
    unfold used; rw [Finset.card_filter]
    dsimp only [rawExtra]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; change v i=(if 1≤v i then 1 else 0)+(v i-1); split_ifs <;> omega
  have zero := active_last C back pos live
  have last : v (N+(C.size-1))=0 := (zero _ (by omega)).mpr (by omega)
  have ex : gateExtra=∑ j∈Finset.range (C.size-1),(v (N+j)-1) := by
    dsimp only [gateExtra]
    conv_lhs => congr; rw [show C.size=(C.size-1)+1 by omega]
    rw [Finset.sum_range_succ,last]; simp
  have endCount := Pins.tail C.size (fun j => v (N+j)) pos zero
  have all := Pins.key N C back
  have slots := Pins.slots C shape
  change (∑ j∈Finset.range C.size,(gateAt C j).inputs.length)+(Partition.neg69 C).card=C.size+C.size at slots
  change (∑ w∈Finset.range N,v w)+(∑ j∈Finset.range C.size,v (N+j))= _ at all
  have extra : surplus N C=rawExtra+gateExtra := Finset.sum_range_add _ _ _
  dsimp only [budget]; rw [extra]; omega

theorem many_count (S : Finset ℕ) (f : ℕ → ℕ) :
    (S.filter (fun w => 2≤f w)).card ≤ ∑ w∈S,(f w-1) := by
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro w _; split_ifs <;> omega

theorem special_count (N : ℕ) (C : Circuit) : (Partition.special N C).card≤budget N C := by
  classical
  unfold Partition.special budget
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ Finset.card_image_le)
  exact many_count _ _

theorem special_range (N : ℕ) (C : Circuit) : Partition.special N C ⊆ Finset.range (N+C.size) := by
  classical
  intro w hw
  rcases Finset.mem_union.mp hw with h|h
  · exact (Finset.mem_filter.mp h).1
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp h
    have klt : k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (by omega)

theorem slot_limits (N : ℕ) (C : Circuit) (shape : Partition.shapes69 C) :
    Partition.exits69 N C≤2*budget N C ∧ Partition.entries69 N C≤2*budget N C := by
  classical
  let R := Finset.range C.size
  let O := Partition.ordinary N C
  let S := Partition.special N C
  let v := Active C
  let X := R \ O
  have cardS : S.card≤budget N C := special_count N C
  have subX : X.image (fun j => N+j) ⊆ S := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨mem,absent⟩ := Finset.mem_sdiff.mp hj
    by_contra no
    exact absent (Finset.mem_filter.mpr ⟨mem,no⟩)
  have cx : X.card≤S.card := by
    have h := Finset.card_le_card subX
    have inj : Function.Injective (fun j : ℕ => N+j) := fun _ _ eq => Nat.add_left_cancel eq
    rwa [Finset.card_image_of_injective _ inj] at h
  constructor
  · change (∑ j∈X,(gateAt C j).inputs.countP (fun w => decide (w∉S)))≤2*budget N C
    calc
      _ ≤ ∑ _j∈X, 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have low : j<C.gates.length := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
        have gmem : gateAt C j∈C.gates := by rw [gateAt,List.getD_eq_getElem _ _ low]; exact List.getElem_mem low
        have le : (gateAt C j).inputs.length≤2 := by rcases shape _ gmem with h|h <;> omega
        exact (List.countP_le_length ..).trans le
      _ ≤ _ := by simp; omega
  · have inc : O⊆R := Finset.filter_subset _ _
    have sub := special_range N C
    have cap : (∑ w∈S,v w) ≤ S.card+surplus N C := by
      calc
        _ ≤ ∑ w∈S, (1+(v w-1)) := by apply Finset.sum_le_sum; intro w _; omega
        _ = S.card+∑ w∈S,(v w-1) := by simp [Finset.sum_add_distrib]
        _ ≤ _ := Nat.add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)) _
    change (∑ j∈O,(gateAt C j).inputs.countP (fun w => decide (w∈S)))≤2*budget N C
    calc
      _ ≤ ∑ j∈R, (gateAt C j).inputs.countP (fun w => decide (w∈S)) :=
        Finset.sum_le_sum_of_subset_of_nonneg inc (fun _ _ _ => Nat.zero_le _)
      _ = ∑ w∈S,v w := by
        simp_rw [←Partition.sum_reads_mask69]
        exact Finset.sum_comm
      _ ≤ _ := by have le : surplus N C ≤ budget N C := Nat.le_add_right _ _; omega

theorem union_bound (L : List (Finset ℕ)) (p : ℕ) (bound : ∀ S∈L, S.card≤p) :
    (L.toFinset.biUnion id).card≤p*L.length := by
  classical
  induction L with
  | nil => simp
  | cons S l ih =>
    have first := bound S (by simp)
    have tail := ih (fun A h => bound A (by simp [h]))
    rw [List.toFinset_cons,Finset.biUnion_insert,List.length_cons,Nat.mul_succ]
    have h := Finset.card_union_le S (l.toFinset.biUnion id)
    change (S∪l.toFinset.biUnion id).card≤_
    omega

theorem account (N : ℕ) (C : Circuit) (p c : ℕ) (shape : Partition.shapes69 C) (back : ReadsBack N C)
    (pos : 0<C.size) (last : C.output+1=N+C.size) (live : ∀ j<C.size, j+1<C.size → 0<Active C (N+j))
    (pureLimit : ∀ S, S⊆Finset.range N → Partition.tree69 N C S ∅ → S.card≤p)
    (chainLimit : ∀ S b, S⊆Finset.range N → Partition.tree69 N C S {b} → S.card≤c) :
    used N C≤(2*p+4*c+1)*budget N C+p := by
  classical
  let v := Active C
  let K := budget N C
  obtain ⟨ep,en⟩ := slot_limits N C shape
  obtain ⟨P,Q,pq,qq,_,allSets,pureTrees,chainTrees⟩ := Partition.finish69 N C shape back pos last live
  have raw {S} (mem : S∈P++Q) : S⊆Finset.range N := by
    intro w hw
    have h : w∈(P++Q).toFinset.biUnion id := Finset.mem_biUnion.mpr ⟨S,List.mem_toFinset.mpr mem,hw⟩
    rw [show (P++Q).toFinset.biUnion id=Partition.once69 N C from allSets] at h
    exact (Finset.mem_filter.mp h).1
  have pc := union_bound P p (fun S h => pureLimit S (raw (List.mem_append_left _ h)) (pureTrees S h).2)
  have qc := union_bound Q c (fun S h => by
    obtain ⟨_,b,tree⟩ := chainTrees S h
    exact chainLimit S b (raw (List.mem_append_right _ h)) tree)
  have union : (Partition.once69 N C).card ≤ (P.toFinset.biUnion id).card+(Q.toFinset.biUnion id).card := by
    rw [←allSets,List.toFinset_append,Finset.union_biUnion]
    exact Finset.card_union_le _ _
  have pp : P.length≤2*K+1 := by omega
  have cc : Q.length≤4*K := by omega
  have pl := Nat.mul_le_mul_left p pp
  have cl := Nat.mul_le_mul_left c cc
  have excess : ((Finset.range N).filter (fun i => 2≤v i)).card≤K := by
    have h := many_count (Finset.range N) v
    have sub : Finset.range N ⊆ Finset.range (N+C.size) := Finset.range_mono (Nat.le_add_right _ _)
    have s : (∑ i∈Finset.range N,(v i-1)) ≤ surplus N C :=
      Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
    have k : surplus N C≤K := Nat.le_add_right _ _
    omega
  have split : used N C=(Partition.once69 N C).card+((Finset.range N).filter (fun i => 2≤v i)).card := by
    unfold used Partition.once69
    rw [Finset.card_filter,Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (if 1≤v i then 1 else 0)=(if v i=1 then 1 else 0)+(if 2≤v i then 1 else 0)
    split_ifs <;> omega
  change used N C≤(2*p+4*c+1)*K+p
  rw [split]
  nlinarith

end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem raw_parts {n m : ℕ} (S : Finset ℕ) (sub : S⊆Finset.range (n+m)) :
    ∃ (R : Finset (Fin n)) (B : Finset (Fin m)),
      R.image (fun a => a.val) ∪ B.image (fun c => n+c.val)=S ∧ S.card=R.card+B.card := by
  classical
  let R := Finset.univ.filter (fun a : Fin n => a.val∈S)
  let B := Finset.univ.filter (fun c : Fin m => n+c.val∈S)
  have joined : R.image (fun a => a.val) ∪ B.image (fun c => n+c.val)=S := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with h|h
      · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp ha).2
      · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp hc).2
    · intro hi
      have bound := Finset.mem_range.mp (sub hi)
      by_cases low : i<n
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨⟨i,low⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩)
      · have eq : n+(i-n)=i := by omega
        let c : Fin m := ⟨i-n,by omega⟩
        have cv : n+c.val=i := eq
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,cv ▸ hi⟩,cv⟩)
  have separate : Disjoint (R.image (fun a => a.val)) (B.image (fun c => n+c.val)) := by
    apply Finset.disjoint_left.mpr
    rintro i hi hj
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hi
    obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hj
    have small := a.isLt
    change n+c.val=i at hc
    change a.val=i at ha
    omega
  refine ⟨R,B,joined,?_⟩
  rw [←joined,Finset.card_union_of_disjoint separate,Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (show Function.Injective (fun c : Fin m => n+c.val) from
      fun _ _ eq => Fin.ext (Nat.add_left_cancel eq))]

end PEqualNP.Outside.L_meta_25646_aux
namespace PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
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

theorem gv (N : ℕ) (C : Circuit) (hb : ReadsBack N C) (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) :
    (run C.gates x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  have hw := run_gate C.gates x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => ite_eq_left (hb j hj i hi)

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

def inside (N : ℕ) (region : Finset ℕ) (w : ℕ) : Prop := N≤w ∧ w-N∈region
def V (C : Circuit) (x : List Bool) (i : ℕ) := (run C.gates x).getD i false

structure Layout (N : ℕ) (C : Circuit) (src reg ent : Finset ℕ) (top : ℕ) : Prop where
  back : ReadsBack N C
  valid : reg ⊆ Finset.range C.size
  member : top∈reg
  one : ent.card≤1
  ports : ∀ w∈ent, w<N+top ∧ w∉src ∧ ¬inside N reg w
  interior : ∀ j∈reg, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    ∀ w∈(gateAt C j).inputs, w∈src ∨ inside N reg w ∨ w∈ent
  exterior : ∀ j<C.size, j∉reg → ∀ w∈(gateAt C j).inputs, w∉src ∧ (inside N reg w → w=N+top)
  output : C.output∉src
  visible : inside N reg C.output → C.output=N+top

variable {N top : ℕ} {C : Circuit} {src reg ent : Finset ℕ}

theorem gate_mono (g : Gate) (op : g.op=.and ∨ g.op=.or) {x y : ℕ → Bool}
    (le : ∀ i∈g.inputs, x i=true → y i=true) :
    g.op.eval (g.inputs.map x)=true → g.op.eval (g.inputs.map y)=true := by
  rcases op with op|op <;> rw [op]
  · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id]
    exact fun h i hi => le i hi (h i hi)
  · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id]
    rintro ⟨i,hi,h⟩; exact ⟨i,hi,le i hi h⟩

theorem inside_mono (L : Layout N C src reg ent top) (x y : List Bool) (hx : x.length=N) (hy : y.length=N)
    (hs : ∀ i∈src, V C x i=true → V C y i=true) (he : ∀ i∈ent, V C x i=true → V C y i=true) :
    ∀ i, inside N reg i → V C x i=true → V C y i=true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rintro ⟨ge,mem⟩
    let j := i-N
    have jmem : j∈reg := mem
    have jlen : j<C.gates.length := Finset.mem_range.mp (L.valid jmem)
    have idx : N+j=i := Nat.add_sub_of_le ge
    have vx : V C x i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C x)) := idx ▸ gv N C L.back x hx j jlen
    have vy : V C y i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C y)) := idx ▸ gv N C L.back y hy j jlen
    rw [vx,vy]
    apply gate_mono _ (L.interior j jmem).1
    intro w hw
    rcases (L.interior j jmem).2 w hw with h|h|h
    · exact hs w h
    · exact ih w (idx ▸ L.back j jlen w hw) h
    · exact he w h

theorem outside_agree (L : Layout N C src reg ent top) (x y : List Bool) (hx : x.length=N) (hy : y.length=N)
    (raw : ∀ i<N, i∉src → V C x i=V C y i) (cap : ℕ)
    (ht : N+top<cap → V C x (N+top)=V C y (N+top)) :
    ∀ i<cap, i∉src → ¬inside N reg i → V C x i=V C y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro bound hs hi
    by_cases low : i<N
    · exact raw i low hs
    by_cases far : N+C.gates.length ≤ i
    · have a := past C.gates x i (by rwa [hx])
      have b := past C.gates y i (by rwa [hy])
      exact a.trans b.symm
    let j := i-N
    have jlen : j<C.gates.length := by dsimp [j]; omega
    have idx : N+j=i := by dsimp [j]; omega
    have jr : j∉reg := fun h => hi ⟨by omega,h⟩
    have vx : V C x i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C x)) := idx ▸ gv N C L.back x hx j jlen
    have vy : V C y i = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C y)) := idx ▸ gv N C L.back y hy j jlen
    rw [vx,vy]; congr 1
    apply List.map_congr_left
    intro w hw
    have smaller : w < i := idx ▸ L.back j jlen w hw
    have cut := L.exterior j jlen jr w hw
    by_cases h : inside N reg w
    · have eq := cut.2 h
      rw [eq]; exact ht (by omega)
    · exact ih w smaller (by omega) cut.1 h

noncomputable def port (ent : Finset ℕ) (v : ℕ → Bool) : Bool := decide (∃ i∈ent, v i=true)

theorem port_le (one : ent.card≤1) (x y : ℕ → Bool) (h : port ent x=true → port ent y=true) :
    ∀ i∈ent, x i=true → y i=true := by
  classical
  intro i hi xi
  have a : port ent x=true := by simpa only [port,decide_eq_true_eq] using (show ∃ j∈ent, x j=true from ⟨i,hi,xi⟩)
  have b := h a
  obtain ⟨j,hj,yj⟩ := of_decide_eq_true b
  exact (Finset.card_le_one.mp one j hj i hi) ▸ yj

noncomputable def low {β : Type} (bad : Finset β) (bit out : β → Bool) :=
  decide (∃ c, c∉bad ∧ bit c=false ∧ out c=true)
noncomputable def high {β : Type} (bad : Finset β) (out : β → Bool) :=
  decide (∃ c, c∉bad ∧ out c=true)

theorem low_high {β : Type} (bad : Finset β) (bit out : β → Bool) :
    low bad bit out=true → high bad out=true := by
  simp only [low,high,decide_eq_true_eq]
  rintro ⟨c,h,_,v⟩; exact ⟨c,h,v⟩

theorem reproduce {β : Type} (bad : Finset β) (bit out : β → Bool)
    (mono : ∀ c∉bad, ∀ c'∉bad, (bit c=true → bit c'=true) → out c=true → out c'=true)
    (c : β) (hc : c∉bad) : out c = if bit c then high bad out else low bad bit out := by
  apply Bool.eq_iff_iff.mpr
  cases h : bit c with
  | false =>
    simp only [Bool.false_eq_true,ite_false,low,decide_eq_true_eq]
    constructor
    · exact fun yes => ⟨c,hc,h,yes⟩
    · rintro ⟨w,hw,h0,yes⟩; exact mono w hw c hc (by simp [h0]) yes
  | true =>
    simp only [ite_true,high,decide_eq_true_eq]
    constructor
    · exact fun yes => ⟨c,hc,yes⟩
    · rintro ⟨w,hw,yes⟩; exact mono w hw c hc (fun _ => h) yes

theorem pairs : ∀ a b c d : Bool, (a=true → b=true) → (c=true → d=true) →
    a.toNat+b.toNat=c.toNat+d.toNat → a=c ∧ b=d := by decide

theorem side_bound {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    (L : Layout N C src reg ent top) (S : Finset α) (bad : Finset β)
    (A : α → β → Bool) (xs : α → β → List Bool) (len : ∀ a c, (xs a c).length=N)
    (sem : ∀ a c, C.eval (xs a c)=A a c)
    (outside : ∀ a∈S, ∀ b∈S, ∀ c∉bad, ∀ i<N, i∉src → V C (xs a c) i=V C (xs b c) i)
    (privatePins : ∀ a∈S, ∀ c∉bad, ∀ c'∉bad, ∀ i∈src, V C (xs a c) i=V C (xs a c') i)
    : (S.image (fun a => (Finset.univ \ bad).filter (fun c => A a c=true))).card ≤ 2+ent.card := by
  classical
  let bit := fun a c => port ent (V C (xs a c))
  let out := fun a c => V C (xs a c) (N+top)
  have imem : inside N reg (N+top) := ⟨by omega,by simpa using L.member⟩
  have localEval (a) (ha : a∈S) (c) (hc : c∉bad) :
      out a c = if bit a c then high bad (out a) else low bad (bit a) (out a) := by
    apply reproduce
    · intro q hq w hw le
      exact inside_mono L _ _ (len a q) (len a w)
        (fun i hi v => (privatePins a ha q hq w hw i hi) ▸ v) (port_le L.one _ _ le) _ imem
    · exact hc
  have sameBit (a) (ha : a∈S) (b) (hb : b∈S) (c) (hc : c∉bad) : bit a c=bit b c := by
    apply Bool.eq_iff_iff.mpr
    simp only [bit,port,decide_eq_true_eq]
    have atEntry (i) (hi : i∈ent) : V C (xs a c) i=V C (xs b c) i :=
      outside_agree L _ _ (len a c) (len b c) (outside a ha b hb c hc) (N+top) (by omega)
        i (L.ports i hi).1 (L.ports i hi).2.1 (L.ports i hi).2.2
    constructor <;> rintro ⟨i,hi,yes⟩
    · exact ⟨i,hi,(atEntry i hi) ▸ yes⟩
    · exact ⟨i,hi,(atEntry i hi).symm ▸ yes⟩
  let lo := fun a => low bad (bit a) (out a)
  let hi := fun a => high bad (out a)
  let code := fun a => if ent=∅ then (lo a).toNat else (lo a).toNat+(hi a).toNat
  have maxBit (b : Bool) : b.toNat≤1 := by cases b <;> decide
  have bound (a : α) : code a<2+ent.card := by
    have l := maxBit (lo a); have h := maxBit (hi a)
    dsimp only [code]
    split_ifs with empty
    · omega
    · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty); omega
  let profile := fun a : α => (⟨code a,bound a⟩ : Fin (2+ent.card))
  let face := fun a => (Finset.univ \ bad).filter (fun c => A a c=true)
  have same (a) (ha : a∈S) (b) (hb : b∈S) (eq : profile a=profile b) : face a=face b := by
    have keys : code a=code b := congrArg Fin.val eq
    have outsideCol (c : β) (hc : c∉bad) : A a c=A b c := by
      have agreePort := sameBit a ha b hb c hc
      have agreeTop : out a c=out b c := by
        rw [localEval a ha c hc,localEval b hb c hc,agreePort]
        by_cases empty : ent=∅
        · have zero : bit b c=false := by simp [bit,port,empty]
          simp only [zero,Bool.false_eq_true,ite_false]
          have k : (lo a).toNat=(lo b).toNat := by simpa only [code,empty,ite_true] using keys
          exact (by cases h : lo a <;> cases j : lo b <;> simp_all : lo a=lo b)
        · have k : (lo a).toNat+(hi a).toNat=(lo b).toNat+(hi b).toNat := by simpa only [code,empty,ite_false] using keys
          obtain ⟨lowEq,highEq⟩ := pairs _ _ _ _ (low_high bad (bit a) (out a)) (low_high bad (bit b) (out b)) k
          split <;> assumption
      rw [←sem,←sem]
      change V C (xs a c) C.output = V C (xs b c) C.output
      by_cases interior : inside N reg C.output
      · rw [L.visible interior]; exact agreeTop
      · exact outside_agree L _ _ (len a c) (len b c) (outside a ha b hb c hc) (C.output+1)
          (fun _ => agreeTop) _ (by omega) L.output interior
    ext c
    by_cases mem : c∈bad
    · simp [face,mem]
    · simp [face,mem,outsideCol c mem]
  let decode (z : Fin (2+ent.card)) := if h : ∃ a∈S, profile a=z then face h.choose else ∅
  have sub : S.image face ⊆ Finset.univ.image decode := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨profile a,Finset.mem_univ _,?_⟩
    have h : ∃ b∈S, profile b=profile a := ⟨a,ha,rfl⟩
    simpa only [decode,dif_pos h] using same h.choose h.choose_spec.1 a ha h.choose_spec.2
  exact (Finset.card_le_card sub).trans ((Finset.card_image_le).trans (by simp))

theorem axis {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    (L : Layout N C src reg ent top) (S : Finset α) (bad : Finset β)
    (A : α → β → Bool) (xs : α → β → List Bool) (len : ∀ a c, (xs a c).length=N)
    (sem : ∀ a c, C.eval (xs a c)=A a c)
    (left : α → ℕ) (right : β → ℕ) (ltL : ∀ a, left a<N) (ltR : ∀ b, right b<N)
    (injR : Function.Injective right) (disjoint : ∀ a b, left a≠right b)
    (hs : src=S.image left ∪ bad.image right)
    (atRaw : ∀ a c i, i<N → V C (xs a c) i = decide (i=left a ∨ i=right c))
    : (S.image (fun a => (Finset.univ \ bad).filter (fun c => A a c=true))).card ≤ 2+ent.card := by
  apply side_bound L S bad A xs len sem
  · intro a ha b hb c _ i hi off
    have na : i≠left a := fun eq => off (hs ▸ eq ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem left ha))
    have nb : i≠left b := fun eq => off (hs ▸ eq ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem left hb))
    simp [atRaw a c i hi,atRaw b c i hi,na,nb]
  · intro a _ c hc c' hc' i hi
    rw [hs] at hi
    rcases Finset.mem_union.mp hi with l|r
    · obtain ⟨a',_,rfl⟩ := Finset.mem_image.mp l
      simp [atRaw,ltL,disjoint]
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp r
      have p : right b≠right c := fun eq => hc (injR eq ▸ hb)
      have q : right b≠right c' := fun eq => hc' (injR eq ▸ hb)
      simp [atRaw,ltR,p,q]

theorem both_axes {n m : ℕ} (G : Fin n → Fin m → Bool) (C : Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (reg ent : Finset ℕ) (top : ℕ)
    (L : Layout (n+m) C (R.image Fin.val ∪ B.image (fun j => n+j.val)) reg ent top)
    (rep : Represents G C) :
    (R.image (fun a => (Finset.univ \ B).filter (fun c => G a c=true))).card≤2+ent.card ∧
    (B.image (fun c => (Finset.univ \ R).filter (fun a => G a c=true))).card≤2+ent.card := by
  classical
  let N := n+m
  have lowVal (u : Fin n) (v : Fin m) (i : ℕ) (hi : i<N) :
      V C (oneEach u v) i=decide (i=u.val ∨ i=n+v.val) := by
    change (run C.gates (oneEach u v)).getD i false=_
    rw [run_input _ _ _ (by rwa [oneEach_length]),oneEach_getD]
  have hr (i : Fin n) : i.val<N := by dsimp [N]; have := i.isLt; omega
  have hc (j : Fin m) : n+j.val<N := by dsimp [N]; have := j.isLt; omega
  have dis (i : Fin n) (j : Fin m) : i.val≠n+j.val := by have := i.isLt; omega
  constructor
  · exact axis L R B G oneEach oneEach_length rep (fun i => i.val) (fun j => n+j.val)
      hr hc (fun _ _ eq => Fin.ext (Nat.add_left_cancel eq)) dis rfl lowVal
  · exact axis L B R (fun j i => G i j) (fun j i => oneEach i j) (fun j i => oneEach_length i j)
      (fun j i => rep i j) (fun j => n+j.val) (fun i => i.val) hc hr Fin.val_injective
      (fun j i => (dis i j).symm) (Finset.union_comm _ _)
      (fun j i k hk => by simpa only [or_comm] using lowVal i j k hk)

end PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

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

def wireSet (N : ℕ) (S reg : Finset ℕ) := S ∪ reg.image (fun j => N+j)
def edge (N : ℕ) (C : Circuit) (reg : Finset ℕ) (w z : ℕ) : Prop :=
  ∃ j∈reg, z=N+j ∧ w∈(gateAt C j).inputs
abbrev reach (N : ℕ) (C : Circuit) (reg : Finset ℕ) := Relation.ReflTransGen (edge N C reg)
noncomputable def leaves {α : Type} (N : ℕ) (C : Circuit) (reg : Finset ℕ) (f : α → ℕ)
    (S : Finset α) (z : ℕ) := S.filter fun a => reach N C reg (f a) z
noncomputable def stages (N : ℕ) (C : Circuit) (reg : Finset ℕ) (z : ℕ) :=
  reg.filter fun j => reach N C reg (N+j) z

structure Tree (N : ℕ) (C : Circuit) (sources reg : Finset ℕ) (root : ℕ) (ext : Finset ℕ) : Prop where
  rawLt : ∀ i∈sources, i<N
  back : ReadsBack N C
  valid : reg ⊆ Finset.range C.size
  rootMem : root∈wireSet N sources reg
  gates : ∀ j∈reg, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀ i∈(gateAt C j).inputs, i∈wireSet N sources reg ∨ i∈ext
  portData : ∀ w∈ext, w∉wireSet N sources reg ∧ w<root ∧ readsIn C reg w=1
  endReads : readsIn C reg root=0
  uniq : ∀ w∈wireSet N sources reg, w≠root →
    readsIn C reg w=1 ∧ readsIn C (Finset.range C.size) w=1 ∧ C.output≠w

variable {N root : ℕ} {C : Circuit} {s r ext : Finset ℕ}

theorem tail_step {a b : ℕ} (h : reach N C r a b) (ne : a≠b) :
    ∃ w, reach N C r a w ∧ edge N C r w b := by
  cases h with
  | refl => contradiction
  | tail h last => exact ⟨_,h,last⟩

theorem head_step {a b : ℕ} (h : reach N C r a b) (ne : a≠b) :
    ∃ w, edge N C r a w ∧ reach N C r w b := by
  induction h with
  | refl => contradiction
  | @tail b c h last ih =>
    by_cases zero : a=b
    · subst b; exact ⟨c,last,.refl⟩
    · obtain ⟨w,e,p⟩ := ih zero
      exact ⟨w,e,p.tail last⟩

theorem edge_lt (T : Tree N C s r root ext) {a b : ℕ} (h : edge N C r a b) : a<b := by
  obtain ⟨j,hj,rfl,hr⟩ := h
  exact T.back j (Finset.mem_range.mp (T.valid hj)) a hr

theorem wire_bound (T : Tree N C s r root ext) {w : ℕ} (h : w∈wireSet N s r) : w<N+C.size := by
  rcases Finset.mem_union.mp h with h|h
  · have := T.rawLt w h; omega
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    have := Finset.mem_range.mp (T.valid hj); omega

theorem exists_reader {reg : Finset ℕ} {w : ℕ} (pos : 0<readsIn C reg w) :
    ∃ j∈reg,w∈(gateAt C j).inputs := by
  classical
  by_contra no
  have z : readsIn C reg w=0 := Finset.sum_eq_zero fun j hj =>
    List.count_eq_zero.mpr (fun h => no ⟨j,hj,h⟩)
  omega

theorem root_ends (T : Tree N C s r root ext) {j : ℕ} (hj : j∈r) : root∉(gateAt C j).inputs := by
  intro h
  have le : (gateAt C j).inputs.count root≤readsIn C r root :=
    Finset.single_le_sum (f:=fun j => (gateAt C j).inputs.count root) (fun _ _ => Nat.zero_le _) hj
  have pos := List.count_pos_iff.mpr h
  have z := T.endReads; omega

theorem to_root (T : Tree N C s r root ext) (w : ℕ) (hw : w∈wireSet N s r) : reach N C r w root := by
  by_cases terminal : w=root
  · subst w; exact .refl
  · obtain ⟨once,_,_⟩ := T.uniq w hw terminal
    obtain ⟨j,hj,reads⟩ := exists_reader (show 0<readsIn C r w by omega)
    have e : edge N C r w (N+j) := ⟨j,hj,rfl,reads⟩
    have member : N+j∈wireSet N s r := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
    exact (Relation.ReflTransGen.single e).trans (to_root T _ member)
termination_by N+C.size-w
decreasing_by
  have := edge_lt T e
  have := wire_bound T member
  omega

theorem no_escape (T : Tree N C s r root ext) {w z j : ℕ} (hw : w∈wireSet N s r)
    (path : reach N C r w z) (neq : w≠z) (hj : j<C.size) (hr : w∈(gateAt C j).inputs) :
    j∈stages N C r z := by
  obtain ⟨next,⟨k,hk,rfl,read⟩,p⟩ := head_step path neq
  have nonroot : w≠root := fun e => root_ends T hk (e ▸ read)
  have eq := only_reader C w j k hj (Finset.mem_range.mp (T.valid hk)) (T.uniq w hw nonroot).2.1 hr read
  subst j; exact Finset.mem_filter.mpr ⟨hk,p⟩

theorem hidden (T : Tree N C s r root ext) {w z : ℕ} (hw : w∈wireSet N s r)
    (path : reach N C r w z) (neq : w≠z) : C.output≠w := by
  obtain ⟨next,⟨j,hj,_,read⟩,_⟩ := head_step path neq
  exact (T.uniq w hw (fun e => root_ends T hj (e ▸ read))).2.2

theorem path_le (T : Tree N C s r root ext) {a b : ℕ} (p : reach N C r a b) : a≤b := by
  induction p with
  | refl => rfl
  | tail h last ih => exact ih.trans (edge_lt T last).le

theorem at_most_one (T : Tree N C s r root ext) {v j : ℕ} (hj : j∈r)
    (h : v∈(gateAt C j).inputs) : readsIn C r v≤1 := by
  rcases (T.gates j hj).2.2 v h with w|e
  · by_cases terminal : v=root
    · subst v; rw [T.endReads]; decide
    · exact (T.uniq v w terminal).1.le
  · exact (T.portData v e).2.2.le

theorem deterministic (T : Tree N C s r root ext) {a b c : ℕ} (ab : edge N C r a b)
    (ac : edge N C r a c) : b=c := by
  obtain ⟨j,jr,rfl,aj⟩ := ab
  obtain ⟨k,kr,rfl,ak⟩ := ac
  congr 1
  by_contra ne
  have sub : ({j,k} : Finset ℕ) ⊆ r := by
    intro i hi; simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    exact hi.elim (fun h => h ▸ jr) (fun h => h ▸ kr)
  have sum : (∑ g∈({j,k} : Finset ℕ), (gateAt C g).inputs.count a) ≤ readsIn C r a :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair ne] at sum
  have p := List.count_pos_iff.mpr aj; have q := List.count_pos_iff.mpr ak
  have bound := at_most_one T jr aj; omega

theorem comparable (T : Tree N C s r root ext) {u a b : ℕ} (pa : reach N C r u a)
    (pb : reach N C r u b) : reach N C r a b ∨ reach N C r b a := by
  by_cases ua : u=a
  · subst a; exact Or.inl pb
  by_cases ub : u=b
  · subst b; exact Or.inr pa
  obtain ⟨w,uw,wa⟩ := head_step pa ua
  obtain ⟨v,uv,vb⟩ := head_step pb ub
  have eq := deterministic T uw uv
  subst v
  exact comparable T wa vb
termination_by N+C.size-u
decreasing_by
  have lt := edge_lt T uw
  obtain ⟨j,hj,eq,_⟩ := uw
  have := Finset.mem_range.mp (T.valid hj)
  omega

theorem distinct_operands (T : Tree N C s r root ext) {k a b : ℕ} (hk : k∈r)
    (ops : (gateAt C k).inputs=[a,b]) : a≠b := by
  intro eq; subst b
  have h : a∈(gateAt C k).inputs := by simp [ops]
  have two : (gateAt C k).inputs.count a=2 := by simp [ops]
  have le : (gateAt C k).inputs.count a ≤ readsIn C r a :=
    Finset.single_le_sum (f:=fun j => (gateAt C j).inputs.count a) (fun _ _ => Nat.zero_le _) hk
  have cap := at_most_one T hk h; omega

theorem branch (T : Tree N C s r root ext) {a b z : ℕ} (az : edge N C r a z)
    (bz : edge N C r b z) (diff : a≠b) (u : ℕ) : ¬reach N C r u a ∨ ¬reach N C r u b := by
  by_contra two
  push_neg at two
  have no {x y : ℕ} (xz : edge N C r x z) (yz : edge N C r y z) (xy : x≠y) (p : reach N C r x y) : False := by
    obtain ⟨w,xw,wy⟩ := head_step p xy
    have eq := deterministic T xz xw
    have le := path_le T wy; have lt := edge_lt T yz; omega
  rcases comparable T two.1 two.2 with h|h
  · exact no az bz diff h
  · exact no bz az diff.symm h

theorem binary_list {α : Type} (l : List α) (h : l.length=2) : ∃ a b, l=[a,b] := by
  obtain _|⟨a,l⟩ := l <;> simp_all
  obtain _|⟨b,l⟩ := l <;> simp_all

end PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart

namespace PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart.Shape

abbrev Signal := Finset ℕ → Bool
def pair (f : Signal) (a c : ℕ) : Prop :=
  f {a}=false ∧ f {c}=false ∧ f {a,c}=true
def Closed (P : ℕ → ℕ → Prop) := ∀ a b x y, P a x → P b x → P b y → P a y
theorem yes_or (a b : Bool) : (a || b)=true ↔ a=true ∨ b=true := by cases a <;> cases b <;> decide
theorem yes_and (a b : Bool) : (a && b)=true ↔ a=true ∧ b=true := by cases a <;> cases b <;> decide
structure Model (f : Signal) (A : Set ℕ) : Prop where
  mono : ∀ U V : Finset ℕ, U ⊆ V → f U=true → f V=true
  agree : ∀ U V : Finset ℕ, (∀ i∈A, i∈U ↔ i∈V) → f U=f V
  rect : Closed (pair f)

theorem widen {f : Signal} {A B : Set ℕ} (F : Model f A) (h : A⊆B) : Model f B :=
  ⟨F.mono,fun U V e => F.agree U V (fun i hi => e i (h hi)),F.rect⟩

theorem fixed (v : Bool) : Model (fun _ => v) ∅ := by
  refine ⟨fun _ _ _ h => h,fun _ _ _ => rfl,?_⟩
  intro a b x y first _ _
  exact False.elim (Bool.false_ne_true (first.1.symm.trans first.2.2))

theorem input (i : ℕ) : Model (fun U => decide (i∈U)) {i} := by
  classical
  constructor
  · intro U V sub yes; exact decide_eq_true (sub (of_decide_eq_true yes))
  · intro U V h; apply Bool.eq_iff_iff.mpr; simpa only [decide_eq_true_eq] using h i (Set.mem_singleton i)
  · intro a b x y p _ _
    obtain ⟨l,r,z⟩ := p
    simp only [decide_eq_false_iff_not,Finset.mem_singleton,decide_eq_true_eq,
      Finset.mem_insert] at l r z
    exact False.elim (z.elim l r)

theorem singleton_agree {f : Signal} {A : Set ℕ} (F : Model f A) {a x : ℕ} (h : x∉A) :
    f {a,x}=f {a} := by
  apply F.agree
  intro i hi
  have ne : i≠x := fun eq => h (eq ▸ hi)
  simp [ne]

theorem absent {f : Signal} {A : Set ℕ} (F : Model f A) {a : ℕ} (h : a∉A) : f {a}=f ∅ := by
  apply F.agree
  intro i hi
  have ne : i≠a := fun eq => h (eq ▸ hi)
  simp [ne]

theorem endpoints {f : Signal} {A : Set ℕ} (F : Model f A) {a x : ℕ} (p : pair f a x) : a∈A ∧ x∈A := by
  constructor
  · by_contra h
    have e : f {a,x}=f {x} := by rw [Finset.pair_comm]; exact singleton_agree F h
    exact Bool.false_ne_true (p.2.1.symm.trans (e.symm.trans p.2.2))
  · by_contra h
    exact Bool.false_ne_true (p.1.symm.trans ((singleton_agree F h).symm.trans p.2.2))

theorem combine {P Q : ℕ → ℕ → Prop} (p : Closed P) (q : Closed Q)
    (row : ∀ i x y, P i x → Q i y → False) (col : ∀ a b x, P a x → Q b x → False) :
    Closed (fun i j => P i j ∨ Q i j) := by
  intro a b x y ax bx byy
  rcases ax with h|h
  · rcases bx with h2|h2
    · rcases byy with h3|h3
      · exact Or.inl (p _ _ _ _ h h2 h3)
      · exact False.elim (row _ _ _ h2 h3)
    · exact False.elim (col _ _ _ h h2)
  · rcases bx with h2|h2
    · exact False.elim (col _ _ _ h2 h)
    · rcases byy with h3|h3
      · exact False.elim (row _ _ _ h3 h2)
      · exact Or.inr (q _ _ _ _ h h2 h3)

theorem or_model {f g : Signal} {A B : Set ℕ} (F : Model f A) (H : Model g B)
    (dis : ∀ i∈A, i∉B) : Model (fun U => f U || g U) (A∪B) := by
  refine ⟨?_,?_,?_⟩
  · intro U V sub h
    simp only [Bool.or_eq_true] at h ⊢
    exact h.imp (F.mono U V sub) (H.mono U V sub)
  · intro U V h
    rw [F.agree U V (fun i hi => h i (Or.inl hi)),H.agree U V (fun i hi => h i (Or.inr hi))]
  · have liftPair {a x} (p : pair (fun U => f U || g U) a x) : pair f a x ∨ pair g a x := by
      obtain ⟨pa,px,pax⟩ := p
      simp only [Bool.or_eq_false_iff] at pa px
      simp only [Bool.or_eq_true] at pax
      exact pax.imp (fun z => ⟨pa.1,px.1,z⟩) (fun z => ⟨pa.2,px.2,z⟩)
    have closed := combine F.rect H.rect
      (fun i x y l r => dis i (endpoints F l).1 (endpoints H r).1)
      (fun a b x l r => dis x (endpoints F l).2 (endpoints H r).2)
    intro a b x y ax bx byy
    refine ⟨ax.1,byy.2.1,?_⟩
    apply (yes_or _ _).mpr
    exact (closed a b x y (liftPair ax) (liftPair bx) (liftPair byy)).imp (fun h => h.2.2) (fun h => h.2.2)

theorem hits {f : Signal} {A : Set ℕ} (F : Model f A) (base : f ∅=false)
    {a x} (h : f {a,x}=true) : a∈A ∨ x∈A := by
  by_contra! miss
  have z := (singleton_agree F miss.2).trans ((absent F miss.1).trans base)
  exact Bool.false_ne_true (z.symm.trans h)

theorem and_model {f g : Signal} {A B : Set ℕ} (F : Model f A) (H : Model g B)
    (dis : ∀ i∈A, i∉B) : Model (fun U => f U && g U) (A∪B) := by
  have constant {v : Signal} {S : Set ℕ} (M : Model v S) (h : v ∅=true) (U) : v U=true :=
    M.mono ∅ U (Finset.empty_subset _) h
  cases bf : f ∅ with
  | true =>
    have eq : (fun U => f U && g U)=g := by funext U; simp [constant F bf U]
    rw [eq]; exact widen H (fun _ h => Or.inr h)
  | false =>
    cases bg : g ∅ with
    | true =>
      have eq : (fun U => f U && g U)=f := by funext U; simp [constant H bg U]
      rw [eq]; exact widen F (fun _ h => Or.inl h)
    | false =>
      have unique (i) (p : f {i}=true) (q : g {i}=true) : False := by
        have mem {v : Signal} {S : Set ℕ} (M : Model v S) (z : v ∅=false) (t : v {i}=true) : i∈S := by
          by_contra no; exact Bool.false_ne_true (z.symm.trans ((absent M no).symm.trans t))
        exact dis i (mem F bf p) (mem H bg q)
      let P := fun i j : ℕ => f {i}=true ∧ g {j}=true
      let Q := fun i j : ℕ => g {i}=true ∧ f {j}=true
      have pc : Closed P := fun _ _ _ _ ax _ byy => ⟨ax.1,byy.2⟩
      have qc : Closed Q := fun _ _ _ _ ax _ byy => ⟨ax.1,byy.2⟩
      have closed := combine pc qc (fun i _ _ p q => unique i p.1 q.1) (fun _ _ j p q => unique j q.2 p.2)
      have classify {a x} (h : pair (fun U => f U && g U) a x) : P a x ∨ Q a x := by
        obtain ⟨_,_,hit⟩ := h
        obtain ⟨l,r⟩ := (yes_and _ _).mp hit
        have slice {v : Signal} {S : Set ℕ} (M : Model v S) {i j : ℕ} (ni : i∉S) (vij : v {i,j}=true) :
            v {j}=true := by
          rw [Finset.pair_comm,singleton_agree M ni] at vij
          exact vij
        rcases hits F bf l with aA|xA
        · rcases hits H bg r with aB|xB
          · exact False.elim (dis a aA aB)
          · exact Or.inl ⟨(singleton_agree F (fun h => dis x h xB)).symm.trans l,slice H (dis a aA) r⟩
        · rcases hits H bg r with aB|xB
          · exact Or.inr ⟨(singleton_agree H (dis x xA)).symm.trans r,slice F (fun h => dis a h aB) l⟩
          · exact False.elim (dis x xA xB)
      refine ⟨?_,?_,?_⟩
      · intro U V sub h
        obtain ⟨l,r⟩ := (yes_and _ _).mp h
        exact (yes_and _ _).mpr ⟨F.mono U V sub l,H.mono U V sub r⟩
      · intro U V h
        rw [F.agree U V (fun i hi => h i (Or.inl hi)),H.agree U V (fun i hi => h i (Or.inr hi))]
      · intro a b x y ax bx byy
        refine ⟨ax.1,byy.2.1,(yes_and _ _).mpr ?_⟩
        have subL : ({a} : Finset ℕ)⊆{a,y} := by simp
        have subR : ({y} : Finset ℕ)⊆{a,y} := by simp
        rcases closed a b x y (classify ax) (classify bx) (classify byy) with h|h
        · exact ⟨F.mono _ _ subL h.1,H.mono _ _ subR h.2⟩
        · exact ⟨F.mono _ _ subR h.2,H.mono _ _ subL h.1⟩

end PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart.Shape

namespace PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
variable {N root : ℕ} {C : Circuit} {s r e : Finset ℕ}

theorem whole_layout (T : Tree N C s r root e) (one : e.card≤1) {k : ℕ}
    (hk : k∈r) (eq : root=N+k) : Cut.Layout N C s r e k := by
  have insideWire {w} (h : Cut.inside N r w) : w∈wireSet N s r := by
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,h.2,Nat.add_sub_of_le h.1⟩)
  have privateRead {w j} (h : w∈wireSet N s r) (ne : w≠root) (hj : j<C.size)
      (read : w∈(gateAt C j).inputs) : j∈r :=
    (Finset.mem_filter.mp (no_escape T h (to_root T w h) ne hj read)).1
  refine ⟨T.back,T.valid,hk,one,?_,?_,?_,?_,?_⟩
  · intro w hw
    obtain ⟨away,low,_⟩ := T.portData w hw
    exact ⟨eq ▸ low,fun hs => away (Finset.mem_union_left _ hs),fun h => away (insideWire h)⟩
  · intro j hj
    refine ⟨(T.gates j hj).1,?_⟩
    intro w hw
    rcases (T.gates j hj).2.2 w hw with a|b
    · rcases Finset.mem_union.mp a with hs|hr
      · exact Or.inl hs
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
        exact Or.inr (Or.inl ⟨by omega,by simpa using hi⟩)
    · exact Or.inr (Or.inr b)
  · intro j hj out w hw
    constructor
    · intro hs
      have low := T.rawLt w hs
      exact out (privateRead (Finset.mem_union_left _ hs) (by omega) hj hw)
    · intro within
      by_contra ne
      exact out (privateRead (insideWire within) (fun h => ne (h.trans eq)) hj hw)
  · intro hs
    have low := T.rawLt _ hs
    exact (T.uniq _ (Finset.mem_union_left _ hs) (by omega)).2.2 rfl
  · intro inside
    by_contra ne
    exact (T.uniq _ (insideWire inside) (fun h => ne (h.trans eq))).2.2 rfl

def sample (N : ℕ) (S U : Finset ℕ) : List Bool :=
  List.ofFn fun i : Fin N => decide (i.val∈S ∧ i.val∈U)
theorem sample_length (N : ℕ) (S U : Finset ℕ) : (sample N S U).length=N := by simp [sample]
theorem sample_read (N : ℕ) (S U : Finset ℕ) (i : ℕ) (h : i<N) :
    (sample N S U).getD i false=decide (i∈S ∧ i∈U) := by
  simp [sample,List.getD_eq_getElem?_getD,List.getElem?_ofFn,h]
def sig (N : ℕ) (C : Circuit) (s : Finset ℕ) (w : ℕ) (U : Finset ℕ) :=
  Cut.V C (sample N s U) w
theorem sig_raw {i : ℕ} (low : i<N) (U : Finset ℕ) :
    sig N C s i U=decide (i∈s ∧ i∈U) := by
  change (Cut.run C.gates (sample N s U)).getD i false=_
  rw [Cut.run_input _ _ _ (by rwa [sample_length]),sample_read _ _ _ _ low]

theorem raw_same (U V : Finset ℕ) (i : ℕ) (low : i<N) (away : i∉s) :
    Cut.V C (sample N s U) i=Cut.V C (sample N s V) i := by
  change sig _ _ _ _ _=sig _ _ _ _ _
  rw [sig_raw low,sig_raw low]; simp [away]

theorem port_value {k : ℕ} (L : Cut.Layout N C s r e k) {w : ℕ} (hw : w∈e) (U : Finset ℕ) :
    sig N C s w U=sig N C s w ∅ := by
  exact Cut.outside_agree L _ _ (sample_length _ _ _) (sample_length _ _ _) (raw_same U ∅)
    (N+k) (by omega) w (L.ports w hw).1 (L.ports w hw).2.1 (L.ports w hw).2.2

theorem readout {k : ℕ} (L : Cut.Layout N C s r e k) :
    ∃ out : Bool → Bool, ∀ U, sig N C s C.output U=out (sig N C s (N+k) U) := by
  classical
  let head := sig N C s (N+k)
  let endVal := sig N C s C.output
  have single (U V) (h : head U=head V) : endVal U=endVal V := by
    by_cases inner : Cut.inside N r C.output
    · simpa only [endVal,L.visible inner] using h
    · exact Cut.outside_agree L _ _ (sample_length _ _ _) (sample_length _ _ _) (raw_same U V)
        (C.output+1) (fun _ => h) _ (by omega) L.output inner
  let out (b) := if h : ∃ U, head U=b then endVal h.choose else false
  refine ⟨out,?_⟩
  intro U
  have h : ∃ V, head V=head U := ⟨U,rfl⟩
  change endVal U=out (head U)
  simpa only [out,dif_pos h] using single U h.choose h.choose_spec.symm

def support (N : ℕ) (C : Circuit) (s r : Finset ℕ) (w : ℕ) : Set ℕ :=
  {i | i∈s ∧ reach N C r i w}

theorem structural (T : Tree N C s r root e) {k : ℕ} (L : Cut.Layout N C s r e k)
    (w : ℕ) : w∈wireSet N s r ∨ w∈e → Shape.Model (sig N C s w) (support N C s r w) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rintro (hw|port)
    · rcases Finset.mem_union.mp hw with raw|gateMem
      · have eq : sig N C s w=(fun U => decide (w∈U)) := by
          funext U; simp [sig_raw (T.rawLt w raw),raw]
        rw [eq]
        apply Shape.widen (Shape.input w)
        intro u hu
        obtain rfl : u=w := Set.mem_singleton_iff.mp hu
        exact ⟨raw,.refl⟩
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp gateMem
        obtain ⟨a,b,ops⟩ := binary_list _ (T.gates j hj).2.1
        have ha : a∈(gateAt C j).inputs := by simp [ops]
        have hb : b∈(gateAt C j).inputs := by simp [ops]
        have len := Finset.mem_range.mp (T.valid hj)
        have A := ih a (T.back j len a ha) ((T.gates j hj).2.2 a ha)
        have B := ih b (T.back j len b hb) ((T.gates j hj).2.2 b hb)
        have ea : edge N C r a (N+j) := ⟨j,hj,rfl,ha⟩
        have eb : edge N C r b (N+j) := ⟨j,hj,rfl,hb⟩
        have dis (i) (la : i∈support N C s r a) (lb : i∈support N C s r b) : False :=
          (branch T ea eb (distinct_operands T hj ops) i).elim (fun no => no la.2) (fun no => no lb.2)
        have sub : support N C s r a ∪ support N C s r b ⊆ support N C s r (N+j) := by
          intro i hi
          rcases hi with l|h
          · exact ⟨l.1,l.2.tail ea⟩
          · exact ⟨h.1,h.2.tail eb⟩
        have val U : sig N C s (N+j) U=(gateAt C j).op.eval [sig N C s a U,sig N C s b U] := by
          have v := Cut.gv N C T.back (sample N s U) (sample_length _ _ _) j len
          simpa only [sig,Cut.V,ops,List.map_cons,List.map_nil] using v
        rcases (T.gates j hj).1 with op|op
        · have eq : sig N C s (N+j)=(fun U => sig N C s a U && sig N C s b U) := by
            funext U; simp [val,op,GateOp.eval]
          rw [eq]; exact Shape.widen (Shape.and_model A B dis) sub
        · have eq : sig N C s (N+j)=(fun U => sig N C s a U || sig N C s b U) := by
            funext U; simp [val,op,GateOp.eval]
          rw [eq]; exact Shape.widen (Shape.or_model A B dis) sub
    · have eq : sig N C s w=(fun _ => sig N C s w ∅) := funext (port_value L port)
      rw [eq]
      exact Shape.widen (Shape.fixed _) (Set.empty_subset _)

end PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart

namespace PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem one_pair {n m : ℕ} (u : Fin n) (c : Fin m) (S : Finset ℕ) (hu : u.val∈S) (hc : n+c.val∈S) :
    sample (n+m) S {u.val,n+c.val}=oneEach u c := by
  apply List.ext_getElem (by rw [sample_length,Cut.oneEach_length])
  intro i hi hj
  have low : i<n+m := by simpa only [sample_length] using hi
  rw [←List.getD_eq_getElem _ false hi,←List.getD_eq_getElem _ false hj,
    sample_read _ _ _ _ low,Cut.oneEach_getD]
  congr 1
  apply propext
  simp only [Finset.mem_insert,Finset.mem_singleton]
  exact ⟨And.right,fun h => ⟨h.elim (fun eq => eq ▸ hu) (fun eq => eq ▸ hc),h⟩⟩

end PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart

namespace PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def bits (N : ℕ) (U : Finset ℕ) := sample N (Finset.range N) U
def value (N : ℕ) (C : Circuit) (w : ℕ) (U : Finset ℕ) := Cut.V C (bits N U) w

theorem pair_in {s : Finset ℕ} {a b : ℕ} (ha : a∈s) (hb : b∈s) : ({a,b} : Finset ℕ)⊆s := by
  intro i hi
  rcases Finset.mem_insert.mp hi with h|h
  · exact h ▸ ha
  · exact (Finset.mem_singleton.mp h) ▸ hb

theorem raw_value {N : ℕ} (C : Circuit) {i : ℕ} (low : i<N) (U : Finset ℕ) :
    value N C i U=decide (i∈U) := by
  change sig N C (Finset.range N) i U=_
  simpa only [Finset.mem_range,low,true_and] using (sig_raw (C:=C) (s:=Finset.range N) low U)

theorem values_order {N : ℕ} (C : Circuit) (mono : Monotone2 C) (back : ReadsBack N C)
    {U W : Finset ℕ} (incl : U⊆W) : ∀ i, value N C i U=true → value N C i W=true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases low : i<N
    · rw [raw_value C low,raw_value C low,decide_eq_true_eq,decide_eq_true_eq]; exact fun h => incl h
    by_cases far : N+C.size ≤ i
    · intro hx
      have h := Cut.past C.gates (bits N U) i (by rw [show (bits N U).length=N from sample_length ..]; exact far)
      exact False.elim (Bool.false_ne_true (h.symm.trans hx))
    let j := i-N
    have eq : N+j=i := Nat.add_sub_of_le (by omega)
    have len : j<C.size := by dsimp [j]; omega
    have gm : gateAt C j∈C.gates := by
      have l : j<C.gates.length := len
      rw [gateAt,List.getD_eq_getElem _ _ l]; exact List.getElem_mem l
    change (Cut.run C.gates (bits N U)).getD i false=true → (Cut.run C.gates (bits N W)).getD i false=true
    rw [←eq,Cut.gv N C back (bits N U) (sample_length ..) j len,Cut.gv N C back (bits N W) (sample_length ..) j len]
    apply Cut.gate_mono _ (mono _ gm).1
    intro v hv; exact ih v (eq ▸ back j len v hv)

theorem outside_order {N : ℕ} {C : Circuit} {s reg e : Finset ℕ} {k : ℕ}
    (L : Cut.Layout N C s reg e k) (mono : Monotone2 C) (U W : Finset ℕ)
    (raw : ∀ i<N, i∉s → value N C i U=true → value N C i W=true)
    (top : value N C (N+k) U=true → value N C (N+k) W=true) :
    value N C C.output U=true → value N C C.output W=true := by
  by_cases bound : Cut.inside N reg C.output
  · simpa only [L.visible bound] using top
  have aux (i : ℕ) : i∉s → ¬Cut.inside N reg i → value N C i U=true → value N C i W=true := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro off outside
      by_cases low : i<N
      · exact raw i low off
      by_cases far : N+C.size ≤ i
      · intro hx
        have h := Cut.past C.gates (bits N U) i (by rw [show (bits N U).length=N from sample_length ..]; exact far)
        exact False.elim (Bool.false_ne_true (h.symm.trans hx))
      let j := i-N
      have eq : N+j=i := Nat.add_sub_of_le (by omega)
      have len : j<C.size := by dsimp [j]; omega
      have gm : gateAt C j∈C.gates := by
        have l : j<C.gates.length := len
        rw [gateAt,List.getD_eq_getElem _ _ l]; exact List.getElem_mem l
      have jr : j∉reg := fun h => outside ⟨by omega,h⟩
      change (Cut.run C.gates (bits N U)).getD i false=true → (Cut.run C.gates (bits N W)).getD i false=true
      rw [←eq,Cut.gv N C L.back (bits N U) (sample_length ..) j len,Cut.gv N C L.back (bits N W) (sample_length ..) j len]
      apply Cut.gate_mono _ (mono _ gm).1
      intro v hv
      have cut := L.exterior j len jr v hv
      by_cases inner : Cut.inside N reg v
      · rw [cut.2 inner]; exact top
      · exact ih v (eq ▸ L.back j len v hv) cut.1 inner
  exact aux _ L.output bound

theorem matrix_read {n m : ℕ} (G : Fin n → Fin m → Bool) {C : Circuit} (rep : Represents G C)
    (a : Fin n) (c : Fin m) : value (n+m) C C.output {a.val,n+c.val}=G a c := by
  have hi : a.val∈Finset.range (n+m) := Finset.mem_range.mpr (by have := a.isLt; omega)
  have hj : n+c.val∈Finset.range (n+m) := Finset.mem_range.mpr (by have := c.isLt; omega)
  change Cut.V C (sample (n+m) (Finset.range (n+m)) _) C.output=_
  rw [one_pair a c _ hi hj]; exact rep a c

end PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart

namespace PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def onLeaves (N : ℕ) (C : Circuit) (s : Finset ℕ) (U : Finset ℕ) :=
  s.filter (fun w => value N C w U=true)

theorem expose {N root : ℕ} {C : Circuit} {s r e : Finset ℕ} (T : Tree N C s r root e)
    (w : ℕ) (hw : w∈wireSet N s r ∨ w∈e) : ∃ f : Shape.Signal,
    Shape.Model f (support N C (s∪e) r w) ∧ ∀ U, value N C w U=f (onLeaves N C (s∪e) U) := by
  classical
  have terminal (w) (h : w∈s∪e) : ∃ f : Shape.Signal,
      Shape.Model f (support N C (s∪e) r w) ∧ ∀ U, value N C w U=f (onLeaves N C (s∪e) U) := by
    refine ⟨_,Shape.widen (Shape.input w) ?_,?_⟩
    · intro i hi
      obtain rfl : i=w := Set.mem_singleton_iff.mp hi
      exact ⟨h,.refl⟩
    · intro U
      simp only [onLeaves,Finset.mem_filter,h,true_and]
      cases value N C w U <;> decide
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with marked|portWire
    · rcases Finset.mem_union.mp marked with raw|gateMem
      · exact terminal _ (Finset.mem_union_left _ raw)
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp gateMem
        obtain ⟨a,b,ops⟩ := binary_list _ (T.gates j hj).2.1
        have ha : a∈(gateAt C j).inputs := by simp [ops]
        have hb : b∈(gateAt C j).inputs := by simp [ops]
        have len := Finset.mem_range.mp (T.valid hj)
        obtain ⟨f,F,fv⟩ := ih a (T.back j len a ha) ((T.gates j hj).2.2 a ha)
        obtain ⟨g,H,gv⟩ := ih b (T.back j len b hb) ((T.gates j hj).2.2 b hb)
        have ea : edge N C r a (N+j) := ⟨j,hj,rfl,ha⟩
        have eb : edge N C r b (N+j) := ⟨j,hj,rfl,hb⟩
        have dis (i) (la : i∈support N C (s∪e) r a) (lb : i∈support N C (s∪e) r b) : False :=
          (branch T ea eb (distinct_operands T hj ops) i).elim (fun no => no la.2) (fun no => no lb.2)
        have sub : support N C (s∪e) r a ∪ support N C (s∪e) r b ⊆ support N C (s∪e) r (N+j) := by
          intro i hi
          rcases hi with l|h
          · exact ⟨l.1,l.2.tail ea⟩
          · exact ⟨h.1,h.2.tail eb⟩
        have calcVal U : value N C (N+j) U=(gateAt C j).op.eval
            [f (onLeaves N C (s∪e) U),g (onLeaves N C (s∪e) U)] := by
          rw [←fv,←gv]
          have h := Cut.gv N C T.back (bits N U) (sample_length ..) j len
          simpa only [value,Cut.V,ops,List.map_cons,List.map_nil] using h
        rcases (T.gates j hj).1 with op|op
        · exact ⟨_,Shape.widen (Shape.and_model F H dis) sub,fun U => by simp [calcVal,op,GateOp.eval]⟩
        · exact ⟨_,Shape.widen (Shape.or_model F H dis) sub,fun U => by simp [calcVal,op,GateOp.eval]⟩
    · exact terminal _ (Finset.mem_union_right _ portWire)

end PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart

namespace PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

structure Face (s e : Finset ℕ) (O : Shape.Signal) where
  f : Shape.Signal
  A : Set ℕ
  model : Shape.Model f A
  flags : Finset ℕ → Finset ℕ
  flagSub : ∀ W, flags W⊆e
  compare : ∀ W, Disjoint W s → ∀ U V, U⊆s → V⊆s →
    (f (U∪flags W)=true → f (V∪flags W)=true) → O (W∪U)=true → O (W∪V)=true

theorem exterior_value {N root : ℕ} {C : Circuit} {s r e : Finset ℕ} (T : Tree N C s r root e)
    {k : ℕ} (L : Cut.Layout N C s r e k) (mono : Monotone2 C) :
    Nonempty (Face s e (value N C C.output)) := by
  classical
  have inRoot : N+k∈wireSet N s r := Finset.mem_union_right _ (Finset.mem_image_of_mem _ L.member)
  obtain ⟨f,M,eval⟩ := expose T (N+k) (Or.inl inRoot)
  let flags := onLeaves N C e
  have mask W (dis : Disjoint W s) U (hu : U⊆s) :
      onLeaves N C (s∪e) (W∪U)=U∪flags W := by
    have portEq (i) (hi : i∈e) : value N C i (W∪U)=value N C i W := by
      apply Cut.outside_agree L _ _ (sample_length ..) (sample_length ..) _ (N+k) (by omega)
        i (L.ports i hi).1 (L.ports i hi).2.1 (L.ports i hi).2.2
      intro j low off
      change value N C j (W∪U)=value N C j W
      rw [raw_value C low,raw_value C low]
      simp [show j∉U from fun h => off (hu h)]
    ext i
    by_cases si : i∈s
    · have notW : i∉W := fun h => Finset.disjoint_left.mp dis h si
      have notE : i∉e := fun h => (L.ports i h).2.1 si
      simp [onLeaves,flags,si,notW,notE,raw_value C (T.rawLt i si)]
    · have notU : i∉U := fun h => si (hu h)
      by_cases ei : i∈e
      · simp [onLeaves,flags,si,notU,ei,portEq i ei]
      · simp [onLeaves,flags,si,notU,ei]
  refine ⟨⟨f,_,M,flags,fun _ => Finset.filter_subset _ _,?_⟩⟩
  intro W dis U V hu hv top
  apply outside_order L mono
  · intro i low off
    rw [raw_value C low,raw_value C low,decide_eq_true_eq,decide_eq_true_eq]
    simp only [Finset.mem_union]
    intro h; exact Or.inl (h.resolve_right fun h => off (hu h))
  · simpa only [eval,mask W dis U hu,mask W dis V hv] using top

theorem force (p q u v : Bool) (pass : (p=true → q=true) → u=true → v=true)
    (yes : u=true) (no : v=false) : p=true ∧ q=false := by
  cases p <;> cases q <;> simp_all

theorem linear : ∀ a b c d : Bool, (a=true → b=true) → (c=true → d=true) →
    ((a=true → c=true) ∧ (b=true → d=true)) ∨ ((c=true → a=true) ∧ (d=true → b=true)) := by decide

variable {s e : Finset ℕ} {O : Shape.Signal}

theorem flag_cases (F : Face s e O) (one : e.card≤1) (W) : F.flags W=∅ ∨ F.flags W=e := by
  by_cases empty : F.flags W=∅
  · exact Or.inl empty
  · right
    apply Finset.eq_of_subset_of_card_le (F.flagSub W)
    have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    omega

theorem face_chain (F : Face s e O) (one : e.card≤1) (a b : ℕ) (ha : a∈s) (hb : b∈s) :
    (∀ z∉s, O {a,z}=true → O {b,z}=true) ∨ (∀ z∉s, O {b,z}=true → O {a,z}=true) := by
  have increase (v : ℕ) : F.f {v}=true → F.f ({v}∪e)=true := F.model.mono _ _ Finset.subset_union_left
  have transport (v w) (hv : v∈s) (hw : w∈s) (lo : F.f {v}=true → F.f {w}=true)
      (hi : F.f ({v}∪e)=true → F.f ({w}∪e)=true) :
      ∀ z∉s, O {v,z}=true → O {w,z}=true := by
    intro z hz
    have step := F.compare {z} (by simpa using hz) {v} {w}
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_subset_iff.mpr hw) (by
        rcases flag_cases F one {z} with h|h
        · simpa only [h,Finset.union_empty] using lo
        · simpa only [h] using hi)
    simpa only [Finset.singleton_union,Finset.pair_comm z] using step
  rcases linear _ _ _ _ (increase a) (increase b) with forward|reverse
  · exact Or.inl (transport a b ha hb forward.1 forward.2)
  · exact Or.inr (transport b a hb ha reverse.1 reverse.2)

theorem face_no_triangle (F : Face s e O) (one : e.card≤1)
    (a x i j : ℕ) (ha : a∈s) (hx : x∈s) (hi : i∉s) (hj : j∉s)
    (a0 : O {a}=false) (x0 : O {x}=false) (i0 : O {i}=false) (j0 : O {j}=false)
    (ax : O {a,x}=true) (aj : O {a,j}=true) (ix : O {i,x}=true) : False := by
  classical
  let t := F.flags ∅
  let r := F.flags {i}
  let c := F.flags {j}
  have constraints (W) (dis : Disjoint W s) (U V) (su : U⊆s) (sv : V⊆s)
      (yes : O (W∪U)=true) (no : O (W∪V)=false) :
      F.f (U∪F.flags W)=true ∧ F.f (V∪F.flags W)=false :=
    force _ _ _ _ (F.compare W dis U V su sv) yes no
  have haX : ({a,x} : Finset ℕ)⊆s := pair_in ha hx
  have hA : ({a} : Finset ℕ)⊆s := Finset.singleton_subset_iff.mpr ha
  have hX : ({x} : Finset ℕ)⊆s := Finset.singleton_subset_iff.mpr hx
  have H := constraints ∅ (by simp) {a,x} {a} haX hA (by simpa using ax) (by simpa using a0)
  have X := constraints ∅ (by simp) {a,x} {x} haX hX (by simpa using ax) (by simpa using x0)
  have J := constraints {j} (by simpa using hj) {a} ∅ hA (by simp)
    (by simpa only [Finset.singleton_union,Finset.pair_comm j] using aj) (by simpa using j0)
  have I := constraints {i} (by simpa using hi) {x} ∅ hX (by simp)
    (by simpa using ix) (by simpa using i0)
  change F.f ({a,x}∪t)=true ∧ F.f ({a}∪t)=false at H
  change F.f ({a,x}∪t)=true ∧ F.f ({x}∪t)=false at X
  change F.f ({a}∪c)=true ∧ F.f (∅∪c)=false at J
  change F.f ({x}∪r)=true ∧ F.f (∅∪r)=false at I
  have empty : t=∅ := by
    rcases flag_cases F one ∅ with off|on
    · exact off
    · change t=e at on
      have more : {a}∪c⊆{a}∪t := by
        rw [on]
        exact Finset.union_subset_union (Finset.Subset.refl _) (F.flagSub {j})
      have pos := F.model.mono _ _ more J.1
      exact False.elim (Bool.false_ne_true (H.2.symm.trans pos))
  rw [empty,Finset.union_empty,Finset.union_empty] at H X
  have allC : c=e := by
    rcases flag_cases F one {j} with off|on
    · change c=∅ at off
      simp only [off,Finset.union_empty,H.2,Bool.false_eq_true,false_and] at J
    · exact on
  have allR : r=e := by
    rcases flag_cases F one {i} with off|on
    · change r=∅ at off
      simp only [off,Finset.union_empty,X.2,Bool.false_eq_true,false_and] at I
    · exact on
  have nonemptyE : e.Nonempty := by
    by_contra no
    have zero := Finset.not_nonempty_iff_eq_empty.mp no
    simp only [allC,zero,Finset.union_empty,H.2,Bool.false_eq_true,false_and] at J
  have card : e.card=1 := by have p := Finset.card_pos.mpr nonemptyE; omega
  obtain ⟨z,ez⟩ := Finset.card_eq_one.mp card
  simp only [allC,ez,Finset.singleton_union,Finset.empty_union] at J
  simp only [allR,ez,Finset.singleton_union,Finset.empty_union] at I
  have xa : Shape.pair F.f a x := ⟨H.2,X.2,H.1⟩
  have zx : Shape.pair F.f z x := ⟨I.2,X.2,by simpa only [Finset.pair_comm z x] using I.1⟩
  have za : Shape.pair F.f z a := ⟨J.2,H.2,by simpa only [Finset.pair_comm z a] using J.1⟩
  have aa := (F.model.rect a z x a xa zx za).2.2
  have aYes : F.f {a}=true := by simpa using aa
  exact Bool.false_ne_true (H.2.symm.trans aYes)

end PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart

namespace PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem bits_eq_sample {N : ℕ} (s U : Finset ℕ) (sub : U⊆s) : bits N U=sample N s U := by
  unfold bits sample
  congr 1
  funext i
  by_cases hit : i.val∈U
  · simp [hit,sub hit,i.isLt]
  · simp [hit]

theorem inside_closed {N root : ℕ} {C : Circuit} {s r e : Finset ℕ} (T : Tree N C s r root e)
    {k : ℕ} (L : Cut.Layout N C s r e k) (mono : Monotone2 C) :
    ∀ a∈s, ∀ b∈s, ∀ x∈s, ∀ y∈s,
      value N C C.output {a}=false → value N C C.output {b}=false →
      value N C C.output {x}=false → value N C C.output {y}=false →
      value N C C.output {a,x}=true → value N C C.output {b,x}=true → value N C C.output {b,y}=true →
      value N C C.output {a,y}=true := by
  classical
  let O := value N C C.output
  let f := sig N C s (N+k)
  have model := structural T L (N+k) (Or.inl (Finset.mem_union_right _ (Finset.mem_image_of_mem _ L.member)))
  have cmp (U V) (hu : U⊆s) (hv : V⊆s) (le : f U=true → f V=true) : O U=true → O V=true := by
    apply outside_order L mono
    · intro w low off
      rw [raw_value C low,raw_value C low,decide_eq_true_eq,decide_eq_true_eq]
      exact fun h => False.elim (off (hu h))
    · change Cut.V C (bits N U) (N+k)=true → Cut.V C (bits N V) (N+k)=true
      rw [bits_eq_sample s U hu,bits_eq_sample s V hv]
      exact le
  intro a ha b hb x hx y hy a0 b0 x0 y0 ax bx byy
  have make (u v) (hu : u∈s) (hv : v∈s) (offU : O {u}=false) (offV : O {v}=false)
      (hit : O {u,v}=true) : Shape.pair f u v := by
    have both : ({u,v} : Finset ℕ)⊆s := pair_in hu hv
    have A := force _ _ _ _ (cmp _ _ both (Finset.singleton_subset_iff.mpr hu)) hit offU
    have B := force _ _ _ _ (cmp _ _ both (Finset.singleton_subset_iff.mpr hv)) hit offV
    exact ⟨A.2,B.2,A.1⟩
  have diag := model.rect a b x y (make a x ha hx a0 x0 ax) (make b x hb hx b0 x0 bx) (make b y hb hy b0 y0 byy)
  exact cmp {a,x} {a,y} (pair_in ha hx) (pair_in ha hy) (fun _ => diag.2.2) ax

theorem single_zeros {n m : ℕ} {C : Circuit} (G : Fin n → Fin m → Bool)
    (rz : ∀ a, ∃ c, G a c=false) (cz : ∀ c, ∃ a, G a c=false)
    (mono : Monotone2 C) (back : ReadsBack (n+m) C) (rep : Represents G C) :
    (∀ a : Fin n, value (n+m) C C.output {a.val}=false) ∧
    (∀ c : Fin m, value (n+m) C C.output {n+c.val}=false) := by
  have zero (w : ℕ) (U : Finset ℕ) (hw : w∈U) (z : value (n+m) C C.output U=false) :
      value (n+m) C C.output {w}=false := by
    cases v : value (n+m) C C.output {w} with
    | false => rfl
    | true =>
      have yes := values_order C mono back (Finset.singleton_subset_iff.mpr hw) C.output v
      exact False.elim (Bool.false_ne_true (z.symm.trans yes))
  constructor
  · intro a; obtain ⟨c,h⟩ := rz a
    exact zero _ {a.val,n+c.val} (by simp) ((matrix_read G rep a c).trans h)
  · intro c; obtain ⟨a,h⟩ := cz c
    exact zero _ {a.val,n+c.val} (by simp) ((matrix_read G rep a c).trans h)

theorem neg_sets {α β : Type} [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : α → β → Bool) (B : Finset β) (a b : α)
    (order : (∀ c∉B, G a c=true → G b c=true) ∨ (∀ c∉B, G b c=true → G a c=true)) :
    (Finset.univ \ B).filter (fun c => G a c=false) ⊆ (Finset.univ \ B).filter (fun c => G b c=false) ∨
    (Finset.univ \ B).filter (fun c => G b c=false) ⊆ (Finset.univ \ B).filter (fun c => G a c=false) := by
  have reverse (i j : α) (forward : ∀ c∉B, G i c=true → G j c=true) :
      (Finset.univ \ B).filter (fun c => G j c=false) ⊆ (Finset.univ \ B).filter (fun c => G i c=false) := by
    intro c hc
    obtain ⟨outside,off⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨outside,?_⟩
    cases h : G i c with
    | false => rfl
    | true => exact False.elim (Bool.false_ne_true (off.symm.trans (forward c (Finset.mem_sdiff.mp outside).2 h)))
  exact order.elim (fun h => Or.inr (reverse a b h)) (fun h => Or.inl (reverse b a h))

end PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart

namespace PEqualNP.Outside.L_meta_25646_aux.Local
open PEqualNP.Outside.L_meta_25646_aux.Local.CircuitPart PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem privateTree : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (root : ℕ),
  let raw := n + m
  let sources := R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)
  let wires := sources ∪ region.image (fun idx => raw + idx)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let extR := fun (i : Fin n) => (Finset.univ \ B).filter (fun outColumn : Fin m => G i outColumn = false)
  let extC := fun (j : Fin m) => (Finset.univ \ R).filter (fun outRow : Fin n => G outRow j = false)
  (∀ a, ∃ c, G a c = false) → (∀ c, ∃ a, G a c = false) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry.card ≤ 1 → (∀ w ∈ entry, w ∉ wires ∧ w < root ∧ localReads w = 1) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w ∈ entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  (∀ a ∈ R, ∀ b ∈ R, extR a ⊆ extR b ∨ extR b ⊆ extR a) ∧
  (∀ x ∈ B, ∀ y ∈ B, extC x ⊆ extC y ∨ extC y ⊆ extC x) ∧
  (∀ a ∈ R, ∀ b ∈ R, ∀ x ∈ B, ∀ y ∈ B,
    G a x = true → G b x = true → G b y = true → G a y = true) ∧
  (∀ a ∈ R, ∀ x ∈ B, G a x = true →
    (∀ j ∉ B, G a j = false) ∨ (∀ i ∉ R, G i x = false)) := by
  classical
  intro n m G C R B r e root
  dsimp only
  intro rz cz mono back rep valid rootIn one ports gates last uses
  let N := n+m
  let l := fun a : Fin n => a.val
  let q := fun x : Fin m => n+x.val
  let S := R.image l ∪ B.image q
  let O := value N C C.output
  have cross (a : Fin n) (x : Fin m) : l a≠q x := by have := a.isLt; dsimp [l,q]; omega
  have left (a : Fin n) : l a∈S ↔ a∈R := by
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h|h
      · obtain ⟨b,hb,eq⟩ := Finset.mem_image.mp h
        exact Fin.val_injective eq ▸ hb
      · obtain ⟨x,_,eq⟩ := Finset.mem_image.mp h
        exact False.elim (cross a x eq.symm)
    · exact fun h => Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  have right (x : Fin m) : q x∈S ↔ x∈B := by
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h|h
      · obtain ⟨a,_,eq⟩ := Finset.mem_image.mp h
        exact False.elim (cross a x eq)
      · obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp h
        change n+y.val=n+x.val at eq
        exact Fin.ext (Nat.add_left_cancel eq) ▸ hy
    · exact fun h => Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  have low (i) (h : i∈S) : i<N := by
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h; dsimp [l,N]; have := a.isLt; omega
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp h; dsimp [q,N]; have := x.isLt; omega
  have T : Tree N C S r root e := ⟨low,back,valid,rootIn,gates,ports,last,uses⟩
  have val (a x) : value N C C.output {l a,q x}=G a x := matrix_read G rep a x
  obtain ⟨zR,zC⟩ := single_zeros G rz cz mono back rep
  rcases Finset.mem_union.mp T.rootMem with raw|gate
  · have same (i) (hi : i∈S) : i=root := by
      by_contra neq
      have small := low _ raw
      obtain ⟨_,_,j,_,eq,_⟩ := tail_step (to_root T i (Finset.mem_union_left _ hi)) neq
      omega
    have lr (a b : Fin n) (ha : a∈R) (hb : b∈R) : a=b :=
      Fin.ext ((same _ ((left _).mpr ha)).trans (same _ ((left _).mpr hb)).symm)
    have cr (x y : Fin m) (hx : x∈B) (hy : y∈B) : x=y :=
      Fin.ext (Nat.add_left_cancel ((same _ ((right _).mpr hx)).trans (same _ ((right _).mpr hy)).symm))
    have never (a x) (ha : a∈R) (hx : x∈B) : False :=
      cross a x ((same _ ((left _).mpr ha)).trans (same _ ((right _).mpr hx)).symm)
    refine ⟨?_,?_,?_,?_⟩
    · intro a ha b hb; rw [lr a b ha hb]; exact Or.inl (Finset.Subset.refl _)
    · intro x hx y hy; rw [cr x y hx hy]; exact Or.inl (Finset.Subset.refl _)
    · intro a ha b hb x hx; exact False.elim (never a x ha hx)
    · intro a ha x hx; exact False.elim (never a x ha hx)
  · obtain ⟨k,hk,eq⟩ := Finset.mem_image.mp gate
    have L := whole_layout T one hk eq.symm
    obtain ⟨F⟩ := exterior_value T L mono
    refine ⟨?_,?_,?_,?_⟩
    · intro a ha b hb
      apply neg_sets G B a b
      rcases face_chain F one (l a) (l b) ((left _).mpr ha) ((left _).mpr hb) with p|p
      · left; intro y hy; simpa only [val] using p (q y) (fun h => hy ((right y).mp h))
      · right; intro y hy; simpa only [val] using p (q y) (fun h => hy ((right y).mp h))
    · intro x hx y hy
      apply neg_sets (fun c a => G a c) R x y
      rcases face_chain F one (q x) (q y) ((right _).mpr hx) ((right _).mpr hy) with p|p
      · left; intro a ha
        simpa only [Finset.pair_comm (q x) (l a),Finset.pair_comm (q y) (l a),val] using
          p (l a) (fun h => ha ((left a).mp h))
      · right; intro a ha
        simpa only [Finset.pair_comm (q x) (l a),Finset.pair_comm (q y) (l a),val] using
          p (l a) (fun h => ha ((left a).mp h))
    · intro a ha b hb x hx y hy ax bx byy
      rw [←val] at ax bx byy ⊢
      exact inside_closed T L mono (l a) ((left _).mpr ha) (l b) ((left _).mpr hb) (q x) ((right _).mpr hx)
        (q y) ((right _).mpr hy) (zR a) (zR b) (zC x) (zC y) ax bx byy
    · intro a ha x hx ax
      by_contra! bad
      obtain ⟨⟨j,hj,aj⟩,⟨i,hi,ix⟩⟩ := bad
      have yesR : G a j=true := by cases h : G a j <;> simp_all
      have yesC : G i x=true := by cases h : G i x <;> simp_all
      exact face_no_triangle F one (l a) (q x) (l i) (q j)
        ((left _).mpr ha) ((right _).mpr hx) (fun h => hi ((left _).mp h)) (fun h => hj ((right _).mp h))
        (zR a) (zC x) (zR i) (zC j) ((val a x).trans ax) ((val a j).trans yesR) ((val i x).trans yesC)

end PEqualNP.Outside.L_meta_25646_aux.Local
namespace PEqualNP.Outside.L_meta_25646_aux.Local
open scoped Classical

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def neg (G : α → β → Bool) (a : α) := Finset.univ.filter (fun x => G a x=false)
def ext (G : α → β → Bool) (B : Finset β) (a : α) := (Finset.univ \ B).filter (fun x => G a x=false)
def pos (G : α → β → Bool) (B : Finset β) (a : α) := B.filter (fun x => G a x=true)
def flip (G : α → β → Bool) := fun (x : β) (a : α) => G a x
def GoodRows (G : α → β → Bool) := ∀ a, 2≤(neg G a).card
def NoFour (G : α → β → Bool) := ∀ a b, a≠b → ((neg G a)∩(neg G b)).card≤1
def Chain (G : α → β → Bool) (R : Finset α) (B : Finset β) :=
  ∀ a∈R, ∀ b∈R, ext G B a⊆ext G B b ∨ ext G B b⊆ext G B a
def Rect (G : α → β → Bool) (R : Finset α) (B : Finset β) :=
  ∀ a∈R, ∀ b∈R, ∀ x∈B, ∀ y∈B, G a x=true → G b x=true → G b y=true → G a y=true
def Cross (G : α → β → Bool) (R : Finset α) (B : Finset β) :=
  ∀ a∈R, ∀ x∈B, G a x=true → (∀ j∉B, G a j=false) ∨ (∀ i∉R, G i x=false)
def Unique (G : α → β → Bool) (R : Finset α) (B : Finset β) :=
  ∀ a∈R, ∀ b∈R, ∀ x∈B, G a x=true → G b x=true → a=b
def Hex (G : α → β → Bool) := ∃ (rows : Fin 3 → α) (cols : Fin 3 → β),
  Function.Injective rows ∧ Function.Injective cols ∧ ∀ i j, i≠j → G (rows i) (cols j)=false
def few (G : α → β → Bool) (R : Finset α) := R.filter (fun a => (pos G Finset.univ a).card≤3)

theorem flip_four {G : α → β → Bool} (h : NoFour G) : NoFour (flip G) := by
  intro x y xy
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ab
  have va := Finset.mem_inter.mp ha
  have vb := Finset.mem_inter.mp hb
  have ax : G a x=false := (Finset.mem_filter.mp va.1).2
  have ay : G a y=false := (Finset.mem_filter.mp va.2).2
  have bx : G b x=false := (Finset.mem_filter.mp vb.1).2
  have byy : G b y=false := (Finset.mem_filter.mp vb.2).2
  have incl : ({x,y} : Finset β)⊆(neg G a)∩(neg G b) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with eq|eq
    · subst z; simp [neg,ax,bx]
    · obtain rfl := Finset.mem_singleton.mp eq; simp [neg,ay,byy]
  have cap := Finset.card_le_card incl
  rw [Finset.card_pair xy] at cap
  have one := h a b ab; omega

theorem flip_rect {G : α → β → Bool} {R : Finset α} {B : Finset β} (h : Rect G R B) : Rect (flip G) B R := by
  intro x hx y hy a ha b hb xa ya yb
  exact h b hb a ha y hy x hx yb ya xa

theorem flip_cross {G : α → β → Bool} {R : Finset α} {B : Finset β} (h : Cross G R B) : Cross (flip G) B R :=
  fun x hx a ha yes => (h a ha x hx yes).symm

theorem flip_hex {G : α → β → Bool} (h : Hex (flip G)) : Hex G := by
  obtain ⟨c,r,hc,hr,h⟩ := h
  exact ⟨r,c,hr,hc,fun i j ne => h j i ne.symm⟩

theorem inside_unique {G : α → β → Bool} {R : Finset α} {B : Finset β}
    (deg : GoodRows G) (noFour : NoFour G) (chain : Chain G R B) (rect : Rect G R B) : Unique G R B := by
  have orient (a) (ha : a∈R) (b) (hb : b∈R) (x) (hx : x∈B) (ax : G a x=true) (bx : G b x=true)
      (sub : ext G B a⊆ext G B b) : a=b := by
    by_contra ne
    have incl : neg G a⊆neg G b := by
      intro y hy
      have off := (Finset.mem_filter.mp hy).2
      apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,?_⟩
      by_cases inside : y∈B
      · cases on : G b y with
        | false => rfl
        | true => exact False.elim (Bool.false_ne_true (off.symm.trans (rect a ha b hb x hx y inside ax bx on)))
      · have member : y∈ext G B a := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,inside⟩,off⟩
        exact (Finset.mem_filter.mp (sub member)).2
    have h := noFour a b ne
    rw [Finset.inter_eq_left.mpr incl] at h
    have lower := deg a; omega
  intro a ha b hb x hx ax bx
  rcases chain a ha b hb with h|h
  · exact orient a ha b hb x hx ax bx h
  · exact (orient b hb a ha x hx bx ax h).symm

structure Side (G : α → β → Bool) (R : Finset α) (B : Finset β) : Prop where
  deg : GoodRows G
  noFour : NoFour G
  chain : Chain G R B
  byCol : Unique G R B
  byRow : Unique (flip G) B R
  cross : Cross G R B

theorem pos_small {G : α → β → Bool} {R : Finset α} {B : Finset β} (H : Side G R B)
    {a} (ha : a∈R) : (pos G B a).card≤1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨bx,px⟩ := Finset.mem_filter.mp hx
  obtain ⟨byy,py⟩ := Finset.mem_filter.mp hy
  exact H.byRow x bx y byy a ha px py

theorem nested {G : α → β → Bool} {R : Finset α} {B : Finset β} (H : Side G R B)
    {a b} (ha : a∈R) (hb : b∈R) (order : (ext G B a).card≤(ext G B b).card) : ext G B a⊆ext G B b := by
  rcases H.chain a ha b hb with h|h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h order).ge

theorem pair_facts {G : α → β → Bool} {R : Finset α} {B : Finset β} (H : Side G R B)
    {a b : α} (ha : a∈R) (hb : b∈R) (ne : a≠b) (sub : ext G B a⊆ext G B b) :
    (neg G a).card=2 ∧ (∃ x∈B, G a x=false ∧ G b x=true) ∧ (∃ y, G a y=false ∧ G b y=false) := by
  classical
  let both := neg G a ∩ neg G b
  let positive := pos G B b
  have cover : neg G a⊆both∪positive := by
    intro x hx
    have ax := (Finset.mem_filter.mp hx).2
    cases bx : G b x with
    | false => exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,bx⟩⟩)
    | true =>
      apply Finset.mem_union_right _
      refine Finset.mem_filter.mpr ⟨?_,bx⟩
      by_contra outside
      have mem : x∈ext G B a := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,outside⟩,ax⟩
      exact Bool.false_ne_true ((Finset.mem_filter.mp (sub mem)).2.symm.trans bx)
  have u := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have atMost : both.card≤1 := H.noFour a b ne
  have singleton : positive.card≤1 := pos_small H hb
  have two := H.deg a
  refine ⟨by omega,?_,?_⟩
  · by_contra! missing
    have incl : neg G a⊆both := by
      intro x hx
      rcases Finset.mem_union.mp (cover hx) with h|h
      · exact h
      · obtain ⟨inside,bx⟩ := Finset.mem_filter.mp h
        exact False.elim (by have no := missing x inside (Finset.mem_filter.mp hx).2; simp_all)
    have h := Finset.card_le_card incl
    omega
  · have one : 0<both.card := by omega
    obtain ⟨y,hy⟩ := Finset.card_pos.mp one
    obtain ⟨first,second⟩ := Finset.mem_inter.mp hy
    exact ⟨y,(Finset.mem_filter.mp first).2,(Finset.mem_filter.mp second).2⟩

theorem choice_count (K : Finset α) (Q : Finset β) (P : α → β → Prop)
    (existsP : ∀ a∈K, ∃ b∈Q, P a b)
    (unique : ∀ a∈K, ∀ b∈K, ∀ x∈Q, P a x → P b x → a=b) : K.card≤Q.card := by
  classical
  let pick (a : {v // v∈K}) := (existsP a.val a.property).choose
  have sp (a) : pick a∈Q ∧ P a.val (pick a) := (existsP a.val a.property).choose_spec
  have inj : Function.Injective pick := by
    intro a b eq
    exact Subtype.ext (unique _ a.property _ b.property _ (sp a).1 (sp a).2 (eq ▸ (sp b).2))
  have cover : K.attach.image pick ⊆ Q := by
    intro z hz
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hz
    exact (sp a).1
  have le := Finset.card_le_card cover
  simpa only [Finset.card_image_of_injective _ inj,Finset.card_attach] using le

end PEqualNP.Outside.L_meta_25646_aux.Local

namespace PEqualNP.Outside.L_meta_25646_aux.Local
open scoped Classical
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {G : α → β → Bool} {R : Finset α} {B : Finset β}

theorem rest_info (H : Side G R B) (hr : R.Nonempty) : ∃ a∈R,
    (∀ b∈R.erase a, (ext G B a).card≤(ext G B b).card) ∧
    (∀ b∈R.erase a, (neg G a).card=2 ∧ (∃ x∈B, G a x=false ∧ G b x=true) ∧ (∃ y, G a y=false ∧ G b y=false)) := by
  obtain ⟨a,ha,least⟩ := Finset.exists_min_image R (fun z => (ext G B z).card) hr
  refine ⟨a,ha,fun b hb => least b (Finset.mem_erase.mp hb).2,?_⟩
  intro b hb
  obtain ⟨neq,mem⟩ := Finset.mem_erase.mp hb
  exact pair_facts H ha mem neq.symm (nested H ha mem (least b mem))

theorem three_limit (H : Side G R B) : R.card≤3 := by
  classical
  by_cases many : 1<R.card
  · obtain ⟨a,ha,_,facts⟩ := rest_info H (Finset.card_pos.mp (by omega))
    have er := Finset.card_erase_add_one ha
    have existsB : 0<(R.erase a).card := by omega
    obtain ⟨b,hb⟩ := Finset.card_pos.mp existsB
    have bound := (facts b hb).1
    let P (z : α) (x : β) := x∈B ∧ G z x=true
    have count := choice_count (R.erase a) (neg G a) P (by
      intro z hz
      obtain ⟨x,inB,off,on⟩ := (facts z hz).2.1
      exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,off⟩,inB,on⟩) (by
      intro z hz w hw x _ px py
      exact H.byCol z (Finset.mem_erase.mp hz).2 w (Finset.mem_erase.mp hw).2 x px.1 px.2 py.2)
    omega
  · omega

theorem at_degree_three (H : Side G R B) (deg : ∀ a,3≤(neg G a).card) : R.card≤1 := by
  by_contra! many
  obtain ⟨a,ha,_,facts⟩ := rest_info H (Finset.card_pos.mp (by omega))
  have er := Finset.card_erase_add_one ha
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0<(R.erase a).card by omega)
  have two := (facts b hb).1
  have three := deg a; omega

theorem three_inj {γ : Type} (x y z : γ) (xy : x≠y) (xz : x≠z) (yz : y≠z) :
    Function.Injective (![x,y,z] : Fin 3 → γ) := by
  intro i j eq
  fin_cases i <;> fin_cases j <;> simp_all

theorem three_hex (H : Side G R B) (three : 2<R.card) : Hex G := by
  classical
  obtain ⟨a,ha,_,facts⟩ := rest_info H (Finset.card_pos.mp (by omega))
  let K := R.erase a
  have cK : K.card+1=R.card := Finset.card_erase_add_one ha
  have nonemp : K.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b,hb,least⟩ := Finset.exists_min_image K (fun k => (ext G B k).card) nonemp
  have cS := Finset.card_erase_add_one hb
  obtain ⟨c,mem⟩ := Finset.card_pos.mp (show 0<(K.erase b).card by omega)
  obtain ⟨cb,hc⟩ := Finset.mem_erase.mp mem
  have ab := (Finset.mem_erase.mp hb).1.symm
  have ac := (Finset.mem_erase.mp hc).1.symm
  have br := (Finset.mem_erase.mp hb).2
  have cr := (Finset.mem_erase.mp hc).2
  obtain ⟨x,hx,ax,bx⟩ := (facts b hb).2.1
  obtain ⟨y,hy,ay,cy⟩ := (facts c hc).2.1
  obtain ⟨z,bz,cz⟩ := (pair_facts H br cr cb.symm (nested H br cr (least c hc))).2.2
  have xy : x≠y := fun eq => cb.symm (H.byCol b br c cr x hx bx (eq ▸ cy))
  have zx : z≠x := by intro eq; subst z; rw [bx] at bz; contradiction
  have zy : z≠y := by intro eq; subst z; rw [cy] at cz; contradiction
  have byy : G b y=false := by
    cases value : G b y with
    | false => rfl
    | true => exact False.elim (cb.symm (H.byCol b br c cr y hy value cy))
  have cx : G c x=false := by
    cases value : G c x with
    | false => rfl
    | true => exact False.elim (cb (H.byCol c cr b br x hx value bx))
  refine ⟨![a,b,c],![z,x,y],three_inj a b c ab ac cb.symm,three_inj z x y zx zy xy,?_⟩
  intro i j ne
  fin_cases i <;> fin_cases j <;> simp_all

theorem closed_few (H : Side G R B) {a} (ha : a∈R) (closed : ∀ j∉B, G a j=false) :
    a∈few G R := by
  refine Finset.mem_filter.mpr ⟨ha,?_⟩
  have incl : pos G Finset.univ a⊆pos G B a := by
    intro x hx
    have yes := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨?_,yes⟩
    by_contra off
    exact Bool.false_ne_true ((closed x off).symm.trans yes)
  exact (Finset.card_le_card incl).trans ((pos_small H ha).trans (by decide))

theorem charge (H : Side G R B) (V : Side (flip G) B R) :
    R.card≤1+(few G R).card+(few (flip G) B).card := by
  classical
  by_cases empty : R=∅
  · simp [empty]
  obtain ⟨a,ha,_,facts⟩ := rest_info H (Finset.nonempty_iff_ne_empty.mpr empty)
  let K := R.erase a
  let F := few G R
  let Q := few (flip G) B
  have er : K.card+1=R.card := Finset.card_erase_add_one ha
  have bound : (K \ F).card≤Q.card := by
    apply choice_count _ _ (fun b x => G b x=true)
    · intro b hb
      obtain ⟨bk,notFew⟩ := Finset.mem_sdiff.mp hb
      have br := (Finset.mem_erase.mp bk).2
      obtain ⟨x,inside,_,yes⟩ := (facts b bk).2.1
      rcases H.cross b br x inside yes with row|col
      · exact False.elim (notFew (closed_few H br row))
      · exact ⟨x,closed_few V inside col,yes⟩
    · intro b hb c hc x hx byy cy
      have br := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hb).1).2
      have cr := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hc).1).2
      exact H.byCol b br c cr x (Finset.mem_filter.mp hx).1 byy cy
  have cover : K⊆F∪(K\F) := by
    intro x hx
    by_cases hf : x∈F
    · exact Finset.mem_union_left _ hf
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx,hf⟩)
  have cap := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  change R.card≤1+F.card+Q.card
  omega

end PEqualNP.Outside.L_meta_25646_aux.Local

namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.Outside.L_meta_25646_aux.Local in
theorem treeBound : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (root : ℕ),
  let raw := n + m
  let sources := R.image (fun src => src.val) ∪ B.image (fun dest => n + dest.val)
  let wires := sources ∪ region.image (fun idx => raw + idx)
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
  let allReads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let nbrR := fun (sourceRow : Fin n) => Finset.univ.filter (fun destCol : Fin m => G sourceRow destCol = false)
  let nbrC := fun (sourceCol : Fin m) => Finset.univ.filter (fun destRow : Fin n => G destRow sourceCol = false)
  let hexagon := ∃ (rows : Fin 3 → Fin n) (cols : Fin 3 → Fin m),
    Function.Injective rows ∧ Function.Injective cols ∧
    ∀ i j : Fin 3, i ≠ j → G (rows i) (cols j) = false
  (∀ a, 2 ≤ (nbrR a).card) → (∀ c, 2 ≤ (nbrC c).card) →
  (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → root ∈ wires →
  entry.card ≤ 1 → (∀ w ∈ entry, w ∉ wires ∧ w < root ∧ localReads w = 1) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    (gate k).inputs.length = 2 ∧ ∀ w ∈ (gate k).inputs, w ∈ wires ∨ w ∈ entry) →
  localReads root = 0 →
  (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ allReads w = 1 ∧ C.output ≠ w) →
  let fewR := R.filter (fun r => (Finset.univ.filter (fun positiveCol : Fin m => G r positiveCol = true)).card ≤ 3)
  let fewC := B.filter (fun c => (Finset.univ.filter (fun positiveRow : Fin n => G positiveRow c = true)).card ≤ 3)
  R.card + B.card ≤ 2 + 2 * (fewR.card + fewC.card) ∧
  (R.card ≤ 3 ∧ B.card ≤ 3) ∧
  (¬hexagon → R.card ≤ 2 ∧ B.card ≤ 2) ∧
  ((∀ a, 3 ≤ (nbrR a).card) → (∀ c, 3 ≤ (nbrC c).card) → R.card ≤ 1 ∧ B.card ≤ 1) := by
  classical
  intro n m G C R B region entry root
  dsimp only
  intro dR dC noFour mono back rep valid member one ports gates last uses
  have nr : GoodRows G := dR
  have nc : GoodRows (PEqualNP.Outside.L_meta_25646_aux.Local.flip G) := dC
  have nf : NoFour G := noFour
  have anyZero {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      (G : α → β → Bool) (d : GoodRows G) : ∀ a, ∃ c, G a c=false := by
    intro a
    have deg := d a
    obtain ⟨c,hit⟩ := Finset.card_pos.mp (show 0<(neg G a).card by omega)
    exact ⟨c,(Finset.mem_filter.mp hit).2⟩
  obtain ⟨r,c,rect,cross⟩ := privateTree n m G C R B region entry root
    (anyZero G nr) (anyZero (PEqualNP.Outside.L_meta_25646_aux.Local.flip G) nc) mono back rep valid member one ports gates last uses
  have fr : Rect G R B := rect
  have cr : Cross G R B := cross
  have chainR : Chain G R B := r
  have chainC : Chain (PEqualNP.Outside.L_meta_25646_aux.Local.flip G) B R := c
  have oneR := inside_unique nr nf chainR fr
  have oneC := inside_unique nc (flip_four nf) chainC (flip_rect fr)
  let H : Side G R B := ⟨nr,nf,chainR,oneR,oneC,cr⟩
  let V : Side (PEqualNP.Outside.L_meta_25646_aux.Local.flip G) B R := ⟨nc,flip_four nf,chainC,oneC,oneR,flip_cross cr⟩
  refine ⟨?_,⟨three_limit H,three_limit V⟩,?_,?_⟩
  · have rows := charge H V
    have cols := charge V H
    change B.card≤1+(few (PEqualNP.Outside.L_meta_25646_aux.Local.flip G) B).card+(few G R).card at cols
    change R.card+B.card≤2+2*((few G R).card+(few (PEqualNP.Outside.L_meta_25646_aux.Local.flip G) B).card)
    omega
  · intro noHex
    change ¬Hex G at noHex
    constructor
    · by_contra! big; exact noHex (three_hex H big)
    · by_contra! big; exact noHex (flip_hex (three_hex V big))
  · intro highR highC
    exact ⟨at_degree_three H highR,at_degree_three V highC⟩

end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
open scoped Classical

theorem finite_table {n m : ℕ} (small : m≤7) (bound : n+2*((m-3).choose 2-1) ≤ m.choose 2) : n+m≤18 := by
  interval_cases m <;> norm_num [Nat.choose] at bound ⊢ <;> omega

theorem pair_pool {n m : ℕ} (G : Fin n → Fin m → Bool) (noFour : Local.NoFour G) :
    (∑ a : Fin n,(Local.neg G a).card.choose 2) ≤ m.choose 2 := by
  classical
  let P (a : Fin n) := (Local.neg G a).powersetCard 2
  have dis : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint P := by
    intro a _ b _ ne
    refine Finset.disjoint_left.mpr ?_
    intro s hs ht
    obtain ⟨left,card⟩ := Finset.mem_powersetCard.mp hs
    obtain ⟨right,_⟩ := Finset.mem_powersetCard.mp ht
    have sub : s⊆(Local.neg G a)∩(Local.neg G b) := fun i hi => Finset.mem_inter.mpr ⟨left hi,right hi⟩
    have cap := Finset.card_le_card sub
    have one := noFour a b ne
    omega
  have incl : Finset.univ.biUnion P⊆(Finset.univ : Finset (Fin m)).powersetCard 2 := by
    intro s hs
    obtain ⟨a,_,mem⟩ := Finset.mem_biUnion.mp hs
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(Finset.mem_powersetCard.mp mem).2⟩
  have cap := Finset.card_le_card incl
  rw [Finset.card_biUnion dis] at cap
  simpa only [P,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin] using cap

theorem few_side_small {n m : ℕ} (G : Fin n → Fin m → Bool) (rows : Local.GoodRows G)
    (noFour : Local.NoFour G) (many : 1<(Local.few G Finset.univ).card) : n+m≤18 := by
  classical
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp many
  let A := Local.pos G Finset.univ a
  let B := Local.pos G Finset.univ b
  have sa : A.card≤3 := (Finset.mem_filter.mp ha).2
  have sb : B.card≤3 := (Finset.mem_filter.mp hb).2
  let shared := Local.neg G a ∩ Local.neg G b
  have one : shared.card≤1 := noFour a b ab
  have cover : (Finset.univ : Finset (Fin m))⊆(A∪B)∪shared := by
    intro x _
    cases ax : G a x <;> cases bx : G b x <;> simp [A,B,shared,Local.pos,Local.neg,ax,bx]
  have count := Finset.card_le_card cover
  rw [Finset.card_univ,Fintype.card_fin] at count
  have sumAB := Finset.card_union_le A B
  have all := Finset.card_union_le (A∪B) shared
  have small : m≤7 := by omega
  have degreeLow (i : Fin n) (few : (Local.pos G Finset.univ i).card≤3) : m-3≤(Local.neg G i).card := by
    have all : (Finset.univ : Finset (Fin m))⊆(Local.pos G Finset.univ i)∪(Local.neg G i) := by
      intro x _; cases h : G i x <;> simp [Local.pos,Local.neg,h]
    have total := (Finset.card_le_card all).trans (Finset.card_union_le _ _)
    rw [Finset.card_univ,Fintype.card_fin] at total; omega
  let k := (m-3).choose 2
  have binom {i : Fin n} (few : (Local.pos G Finset.univ i).card≤3) : k≤(Local.neg G i).card.choose 2 := by
    obtain ⟨s,sub,card⟩ := Finset.exists_subset_card_eq (degreeLow i few)
    have below : s.powersetCard 2⊆(Local.neg G i).powersetCard 2 := by
      intro u hu
      obtain ⟨inside,cu⟩ := Finset.mem_powersetCard.mp hu
      exact Finset.mem_powersetCard.mpr ⟨inside.trans sub,cu⟩
    have count := Finset.card_le_card below
    simpa only [Finset.card_powersetCard,card] using count
  let P : Finset (Fin n) := {a,b}
  have calcCount (i : Fin n) : 1+(if i∈P then k-1 else 0)≤(Local.neg G i).card.choose 2 := by
    have base := Nat.choose_pos (rows i)
    by_cases hi : i∈P
    · have gain : k≤(Local.neg G i).card.choose 2 := by
        rcases Finset.mem_insert.mp hi with h|h
        · subst i; exact binom sa
        · obtain rfl := Finset.mem_singleton.mp h; exact binom sb
      simp only [hi,ite_true]; omega
    · simp only [hi,ite_false,Nat.add_zero]; omega
  have calcAll := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => calcCount i)
  have weight : (∑ i : Fin n, if i∈P then k-1 else 0)=2*(k-1) := by
    rw [←Finset.sum_filter]
    have same : Finset.univ.filter (fun i => i∈P)=P := by ext i; simp
    rw [same]; simp [P,Finset.card_pair ab,Nat.mul_comm]
  rw [Finset.sum_add_distrib,weight] at calcAll
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.mul_one] at calcAll
  exact finite_table small (calcAll.trans (pair_pool G noFour))

end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem graph_data {n m : ℕ} (G : Fin n → Fin m → Bool) (nonzero : 0<n+m)
    (r : Local.GoodRows G) (c : Local.GoodRows (Local.flip G)) (four : Local.NoFour G) :
    (∀ a, ∃ x, G a x=false) ∧ (∀ x, ∃ a, G a x=false) ∧
    (∀ a, ∃ x, G a x=true) ∧ (∀ x, ∃ a, G a x=true) ∧
    (∃ a x y, G a x≠G a y) ∧ (∃ a b x, G a x≠G b x) := by
  classical
  have dim {i j : ℕ} (H : Fin i → Fin j → Bool) (good : Local.GoodRows H) (nonempty : 0 < i) : 2≤j := by
    let a : Fin i := ⟨0,nonempty⟩
    have h := good a; have cap := (Local.neg H a).card_le_univ
    simp only [Fintype.card_fin] at cap; omega
  have rn : 0<n := by by_contra! small; have h := dim (Local.flip G) c (by omega); omega
  have mz := dim G r rn
  have nz := dim (Local.flip G) c (by omega)
  have data {i j : ℕ} (H : Fin i → Fin j → Bool) (good : Local.GoodRows H) (nf : Local.NoFour H)
      (two : 2 ≤ i) : (∀ a, ∃ b, H a b=false) ∧ (∀ a, ∃ b, H a b=true) := by
    constructor
    · intro a
      have deg := good a
      obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(Local.neg H a).card by omega)
      exact ⟨x,(Finset.mem_filter.mp hx).2⟩
    · intro a
      let b : Fin i := if a.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
      have ne : a≠b := by
        intro eq
        have v := congrArg Fin.val eq
        by_cases zero : a.val=0 <;> simp [b,zero] at v <;> omega
      by_contra! none
      have whole : Local.neg H a=Finset.univ := by ext x; cases h : H a x <;> simp_all [Local.neg]
      have small := nf a b ne
      rw [whole,Finset.univ_inter] at small
      have many := good b; omega
  obtain ⟨r0,r1⟩ := data G r four nz
  obtain ⟨c0,c1⟩ := data (Local.flip G) c (Local.flip_four four) mz
  let a : Fin n := ⟨0,by omega⟩
  let x : Fin m := ⟨0,by omega⟩
  obtain ⟨l,hl⟩ := r0 a
  obtain ⟨q,hq⟩ := r1 a
  obtain ⟨b,hb⟩ := c0 x
  obtain ⟨v,hv⟩ := c1 x
  exact ⟨r0,c0,r1,c1,⟨a,l,q,by rw [hl,hq]; decide⟩,⟨b,v,x,by
    change G b x=false at hb; change G v x=true at hv; rw [hb,hv]; decide⟩⟩

theorem all_used {n m : ℕ} (G : Fin n → Fin m → Bool) (D : Circuit)
    (mono : Monotone2 D) (back : ReadsBack (n+m) D) (rep : Represents G D) (out : n+m≤D.output)
    (r0 : ∀ a, ∃ c, G a c=false) (c0 : ∀ c, ∃ a, G a c=false)
    (r1 : ∀ a, ∃ c, G a c=true) (c1 : ∀ c, ∃ a, G a c=true) : used (n+m) D=n+m := by
  classical
  let N := n+m
  let O := Local.CircuitPart.value N D D.output
  obtain ⟨zR,zC⟩ := Local.CircuitPart.single_zeros G r0 c0 mono back rep
  have forced (w v : ℕ) (yes : O {w,v}=true) (zero : O {v}=false) : 0<Active D w := by
    by_contra! no
    have same := observed_agree back (Local.CircuitPart.bits N {w,v}) (Local.CircuitPart.bits N {v})
      (Local.CircuitPart.sample_length ..) (Local.CircuitPart.sample_length ..) (fun i low hit => by
        have ne : i≠w := by intro eq; subst i; omega
        unfold Local.CircuitPart.bits
        rw [Local.CircuitPart.sample_read _ _ _ _ low,Local.CircuitPart.sample_read _ _ _ _ low]
        simp [ne]) D.output out
    change O {w,v}=O {v} at same
    rw [yes,zero] at same; contradiction
  have all (w : ℕ) (hw : w∈Finset.range N) : 1≤Active D w := by
    have small : w<n+m := Finset.mem_range.mp hw
    by_cases row : w<n
    · let a : Fin n := ⟨w,row⟩
      obtain ⟨x,hx⟩ := r1 a
      exact forced w (n+x.val) ((Local.CircuitPart.matrix_read G rep a x).trans hx) (zC x)
    · let x : Fin m := ⟨w-n,by omega⟩
      have eq : n+x.val=w := by change n+(w-n)=w; omega
      obtain ⟨a,ha⟩ := c1 x
      rw [←eq]
      apply forced (n+x.val) a.val _ (zR a)
      rw [Finset.pair_comm]
      exact (Local.CircuitPart.matrix_read G rep a x).trans ha
  change ((Finset.range N).filter (fun i => 1≤Active D i)).card=N
  rw [Finset.filter_eq_self.mpr all,Finset.card_range]

end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def sharedRaw (N : ℕ) (C : Circuit) := (Finset.range N).filter (fun i => 2≤Active C i)

theorem combined (N : ℕ) (C : Circuit) (shape : Partition.shapes69 C) :
    (sharedRaw N C).card+2*Partition.exits69 N C+4*Partition.entries69 N C ≤ 12*budget N C := by
  classical
  let X := Finset.range C.size \ Partition.ordinary N C
  let J := X.image (fun j => N+j)
  let R := sharedRaw N C
  let S := Partition.special N C
  have lower : R∪J⊆S := by
    intro w hw
    rcases Finset.mem_union.mp hw with raw|gate
    · obtain ⟨small,reads⟩ := Finset.mem_filter.mp raw
      have le := Finset.mem_range.mp small
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),reads⟩)
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp gate
      obtain ⟨mem,absent⟩ := Finset.mem_sdiff.mp hj
      by_contra no
      exact absent (Finset.mem_filter.mpr ⟨mem,no⟩)
  have dis : Disjoint R J := by
    apply Finset.disjoint_left.mpr
    intro w raw gate
    have low : w<N := Finset.mem_range.mp (Finset.mem_filter.mp raw).1
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp gate
    change N+j=w at eq; omega
  have together := (Finset.card_le_card lower).trans (special_count N C)
  have inj : Function.Injective (fun j : ℕ => N+j) := fun _ _ eq => Nat.add_left_cancel eq
  rw [Finset.card_union_of_disjoint dis,show J.card=X.card from Finset.card_image_of_injective _ inj] at together
  have exits : Partition.exits69 N C≤2*X.card := by
    change (∑ j∈X,(gateAt C j).inputs.countP (fun w => decide (w∉S))) ≤ _
    calc
      _ ≤ ∑ _j∈X, 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have len : j<C.gates.length := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
        have gm : gateAt C j∈C.gates := by rw [gateAt,List.getD_eq_getElem _ _ len]; exact List.getElem_mem len
        have cap : (gateAt C j).inputs.length≤2 := by rcases shape _ gm with h|h <;> omega
        exact (List.countP_le_length ..).trans cap
      _ = _ := by simp [Nat.mul_comm]
  have entries := (slot_limits N C shape).2
  change R.card+_+_≤_
  omega

theorem marked_union (L : List (Finset ℕ)) (H : Finset ℕ)
    (separate : L.Pairwise Disjoint) (small : ∀ S∈L, S.card≤2+2*(S∩H).card) :
    (L.toFinset.biUnion id).card≤2*L.length+2*((L.toFinset.biUnion id)∩H).card := by
  classical
  induction L with
  | nil => simp
  | cons S l ih =>
    obtain ⟨bySet,rest⟩ := List.pairwise_cons.mp separate
    have bound := small S (by simp)
    have tail := ih rest (fun t ht => small t (by simp [ht]))
    let A := l.toFinset.biUnion id
    have dis : Disjoint S A := by
      apply Finset.disjoint_left.mpr
      intro w ws wa
      obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp wa
      exact Finset.disjoint_left.mp (bySet t (List.mem_toFinset.mp ht)) ws hit
    have di : Disjoint (S∩H) (A∩H) := by
      apply Finset.disjoint_left.mpr
      intro w hs ha
      exact Finset.disjoint_left.mp dis (Finset.mem_inter.mp hs).1 (Finset.mem_inter.mp ha).1
    rw [List.toFinset_cons,Finset.biUnion_insert,List.length_cons]
    change (S∪A).card≤2*(l.length+1)+2*((S∪A)∩H).card
    rw [Finset.card_union_of_disjoint dis,Finset.union_inter_distrib_right,Finset.card_union_of_disjoint di]
    change A.card≤2*l.length+2*(A∩H).card at tail
    omega

theorem counted (N : ℕ) (C : Circuit) (H : Finset ℕ) (shape : Partition.shapes69 C)
    (back : ReadsBack N C) (pos : 0<C.size) (last : C.output+1=N+C.size)
    (live : ∀ j<C.size, j+1<C.size → 0<Active C (N+j))
    (small : ∀ S E, S⊆Finset.range N → E.card≤1 → Partition.tree69 N C S E → S.card≤2+2*(S∩H).card) :
    used N C≤12*budget N C+2+2*H.card := by
  classical
  obtain ⟨P,Q,ex,en,dis,all,pureT,entryT⟩ := Partition.finish69 N C shape back pos last live
  have bounds : ∀ S∈P++Q, S.card≤2+2*(S∩H).card := by
    intro S mem
    have sub : S⊆Finset.range N := by
      intro w hw
      have incl : w∈(P++Q).toFinset.biUnion id := Finset.mem_biUnion.mpr ⟨S,List.mem_toFinset.mpr mem,hw⟩
      rw [show (P++Q).toFinset.biUnion id=Partition.once69 N C from all] at incl
      exact (Finset.mem_filter.mp incl).1
    rcases List.mem_append.mp mem with p|q
    · exact small S ∅ sub (by simp) (pureT S p).2
    · obtain ⟨_,b,h⟩ := entryT S q
      exact small S {b} sub (by simp) h
  have count := marked_union (P++Q) H dis bounds
  rw [show (P++Q).toFinset.biUnion id=Partition.once69 N C from all,List.length_append] at count
  have excess := combined N C shape
  have marked := Finset.card_le_card (Finset.inter_subset_right (s₁:=Partition.once69 N C) (s₂:=H))
  have split : used N C=(Partition.once69 N C).card+(sharedRaw N C).card := by
    unfold used Partition.once69 sharedRaw
    rw [Finset.card_filter,Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (if 1≤Active C i then 1 else 0)=(if Active C i=1 then 1 else 0)+(if 2≤Active C i then 1 else 0)
    split_ifs <;> omega
  omega

end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def marks {n m : ℕ} (G : Fin n → Fin m → Bool) :=
  (Local.few G Finset.univ).image (fun a => a.val) ∪
  (Local.few (Local.flip G) Finset.univ).image (fun c => n+c.val)

theorem mark_size {n m : ℕ} (G : Fin n → Fin m → Bool) :
    (marks G).card≤(Local.few G Finset.univ).card+(Local.few (Local.flip G) Finset.univ).card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

theorem mark_local {n m : ℕ} (G : Fin n → Fin m → Bool) (R : Finset (Fin n)) (B : Finset (Fin m))
    (S : Finset ℕ) (join : R.image (fun a => a.val) ∪ B.image (fun c => n+c.val)=S) :
    (Local.few G R).card+(Local.few (Local.flip G) B).card≤(S∩marks G).card := by
  classical
  let A := (Local.few G R).image (fun a => a.val)
  let H := (Local.few (Local.flip G) B).image (fun c => n+c.val)
  have subset : A∪H⊆S∩marks G := by
    intro w hw
    rw [←join]
    rcases Finset.mem_union.mp hw with left|right
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp left
      obtain ⟨ar,small⟩ := Finset.mem_filter.mp ha
      have globalA : a∈Local.few G Finset.univ := Finset.mem_filter.mpr ⟨Finset.mem_univ _,small⟩
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ ar),
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ globalA)⟩
    · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp right
      obtain ⟨cb,small⟩ := Finset.mem_filter.mp hc
      have globalC : c∈Local.few (Local.flip G) Finset.univ := Finset.mem_filter.mpr ⟨Finset.mem_univ _,small⟩
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ cb),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ globalC)⟩
  have dis : Disjoint A H := by
    refine Finset.disjoint_left.mpr ?_
    intro w left right
    obtain ⟨a,_,eq⟩ := Finset.mem_image.mp left
    obtain ⟨c,_,eq'⟩ := Finset.mem_image.mp right
    change a.val=w at eq; change n+c.val=w at eq'
    have small := a.isLt; omega
  have le := Finset.card_le_card subset
  have inj : Function.Injective (fun c : Fin m => n+c.val) := fun _ _ h => Fin.ext (Nat.add_left_cancel h)
  simpa only [Finset.card_union_of_disjoint dis,A,H,Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ inj] using le

theorem caps {n m : ℕ} (G : Fin n → Fin m → Bool) (D : Circuit)
    (rd : Local.GoodRows G) (cd : Local.GoodRows (Local.flip G)) (nf : Local.NoFour G)
    (mono : Monotone2 D) (back : ReadsBack (n+m) D) (rep : Represents G D)
    (S E : Finset ℕ) (sub : S⊆Finset.range (n+m)) (one : E.card≤1) (tree : Partition.tree69 (n+m) D S E) :
    S.card≤6 ∧ S.card≤2+2*(S∩marks G).card ∧
    ((∀ a,3≤(Local.neg G a).card) → (∀ c,3≤(Local.neg (Local.flip G) c).card) → S.card≤2) := by
  classical
  obtain ⟨R,B,join,card⟩ := raw_parts S sub
  obtain ⟨region,root,h⟩ := tree
  dsimp only at h
  obtain ⟨inside,member,last,ports,gates,uses⟩ := h
  have t := treeBound n m G D R B region E root
  dsimp only at t
  rw [join] at t
  obtain ⟨weighted,three,_,high⟩ := t rd cd nf mono back rep
    (fun _ hi => Finset.mem_range.mpr (Partition.ordinary_index69 (inside hi))) member one ports gates last uses
  have seen := mark_local G R B S join
  change R.card+B.card≤2+2*((Local.few G R).card+(Local.few (Local.flip G) B).card) at weighted
  refine ⟨by omega,by omega,?_⟩
  intro rows cols
  obtain ⟨s1,s2⟩ := high rows cols; omega

end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
def broadTree (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ Partition.gates69 C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ Partition.reads69 C w=1 ∧ C.output≠w)

theorem broadCaps {n m : ℕ} (G : Fin n → Fin m → Bool) (D : Circuit)
    (rd : Local.GoodRows G) (cd : Local.GoodRows (Local.flip G)) (nf : Local.NoFour G)
    (mono : Monotone2 D) (back : ReadsBack (n+m) D) (rep : Represents G D)
    (S E : Finset ℕ) (sub : S⊆Finset.range (n+m)) (one : E.card≤1) (tree : broadTree (n+m) D S E) :
    S.card≤6 ∧ S.card≤2+2*(S∩marks G).card ∧
    ((∀ a,3≤(Local.neg G a).card) → (∀ c,3≤(Local.neg (Local.flip G) c).card) → S.card≤2) := by
  classical
  obtain ⟨R,B,join,card⟩ := raw_parts S sub
  obtain ⟨region,root,h⟩ := tree
  dsimp only at h
  obtain ⟨inside,member,last,ports,gates,uses⟩ := h
  have t := treeBound n m G D R B region E root
  dsimp only at t
  rw [join] at t
  obtain ⟨weighted,three,_,high⟩ := t rd cd nf mono back rep
    inside member one ports gates last uses
  have seen := mark_local G R B S join
  change R.card+B.card≤2+2*((Local.few G R).card+(Local.few (Local.flip G) B).card) at weighted
  refine ⟨by omega,by omega,?_⟩
  intro rows cols
  obtain ⟨s1,s2⟩ := high rows cols; omega

end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
def CutPartition : Prop := ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
  let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
  let markedReads := ∑ w ∈ shared, reads w
  let once := (Finset.range n).filter (fun w => reads w = 1)
  let tree := fun (S E : Finset ℕ) => ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
    region ⊆ gates ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w)
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  0 < C.size → C.output + 1 = n + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads (n + j)) →
  ∃ (pure chains : List (Finset ℕ)) (markedComponents : ℕ),
    pure.length + markedComponents ≤ sharedGates.card + neg.card + 1 ∧
    chains.length + markedComponents ≤ 2 * (markedReads + neg.card) ∧
    (0 < markedReads + neg.card → 0 < markedComponents) ∧
    (pure ++ chains).Pairwise (fun A B => Disjoint A B) ∧
    (pure ++ chains).toFinset.biUnion (fun S => S) = once ∧
    (∀ S ∈ pure, S.Nonempty ∧ tree S ∅) ∧
    (∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, tree S {b})
end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
open scoped Classical
theorem pair_pressure {n m : ℕ} (G : Fin n → Fin m → Bool) (rows : Local.GoodRows G)
    (noFour : Local.NoFour G) (many : 1<(Local.few G Finset.univ).card) : m≤7 ∧ n+(Local.few G Finset.univ).card*((m-3).choose 2-1) ≤ m.choose 2 := by
  classical
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp many
  let A := Local.pos G Finset.univ a
  let B := Local.pos G Finset.univ b
  have sa : A.card≤3 := (Finset.mem_filter.mp ha).2
  have sb : B.card≤3 := (Finset.mem_filter.mp hb).2
  let shared := Local.neg G a ∩ Local.neg G b
  have one : shared.card≤1 := noFour a b ab
  have cover : (Finset.univ : Finset (Fin m))⊆(A∪B)∪shared := by
    intro x _
    cases ax : G a x <;> cases bx : G b x <;> simp [A,B,shared,Local.pos,Local.neg,ax,bx]
  have count := Finset.card_le_card cover
  rw [Finset.card_univ,Fintype.card_fin] at count
  have sumAB := Finset.card_union_le A B
  have all := Finset.card_union_le (A∪B) shared
  have small : m≤7 := by omega
  have degreeLow (i : Fin n) (few : (Local.pos G Finset.univ i).card≤3) : m-3≤(Local.neg G i).card := by
    have all : (Finset.univ : Finset (Fin m))⊆(Local.pos G Finset.univ i)∪(Local.neg G i) := by
      intro x _; cases h : G i x <;> simp [Local.pos,Local.neg,h]
    have total := (Finset.card_le_card all).trans (Finset.card_union_le _ _)
    rw [Finset.card_univ,Fintype.card_fin] at total; omega
  let k := (m-3).choose 2
  have binom {i : Fin n} (few : (Local.pos G Finset.univ i).card≤3) : k≤(Local.neg G i).card.choose 2 := by
    obtain ⟨s,sub,card⟩ := Finset.exists_subset_card_eq (degreeLow i few)
    have below : s.powersetCard 2⊆(Local.neg G i).powersetCard 2 := by
      intro u hu
      obtain ⟨inside,cu⟩ := Finset.mem_powersetCard.mp hu
      exact Finset.mem_powersetCard.mpr ⟨inside.trans sub,cu⟩
    have count := Finset.card_le_card below
    simpa only [Finset.card_powersetCard,card] using count
  let P := Local.few G Finset.univ
  have per (i : Fin n) : 1+(if i∈P then k-1 else 0)≤(Local.neg G i).card.choose 2 := by
    have base := Nat.choose_pos (rows i)
    by_cases mem : i∈P
    · have l := binom ((Finset.mem_filter.mp mem).2)
      simp only [mem,ite_true]; omega
    · simp only [mem,ite_false,Nat.add_zero]; omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  have weight : (∑ i : Fin n, if i∈P then k-1 else 0)=P.card*(k-1) := by
    rw [←Finset.sum_filter]
    have e : Finset.univ.filter (fun i => i∈P)=P := by ext i; simp
    rw [e]; simp
  rw [Finset.sum_add_distrib,weight] at total
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.mul_one] at total
  exact ⟨small,total.trans (pair_pool G noFour)⟩

theorem degree_cap {n m : ℕ} (G : Fin n → Fin m → Bool) (rows : Local.GoodRows G)
    (nf : Local.NoFour G) (c : Fin m) : (Local.neg (Local.flip G) c).card ≤ m-1 := by
  classical
  let P := Local.neg (Local.flip G) c
  let F := fun a : Fin n => (Local.neg G a).erase c
  have common {a : Fin n} (h : a∈P) : c∈Local.neg G a :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩
  have dis : (↑P : Set (Fin n)).PairwiseDisjoint F := by
    intro a ha b hb ab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have cx := Finset.mem_erase.mp hx
    have cy := Finset.mem_erase.mp hy
    exact cx.1 (Finset.card_le_one.mp (nf a b ab) _ (Finset.mem_inter.mpr ⟨cx.2,cy.2⟩)
      _ (Finset.mem_inter.mpr ⟨common ha,common hb⟩))
  have sub : P.biUnion F⊆Finset.univ.erase c := by
    intro x hx
    obtain ⟨a,_,hit⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hit).1,Finset.mem_univ _⟩
  have le := Finset.card_le_card sub
  rw [Finset.card_biUnion dis,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin] at le
  have each (a : Fin n) (ha : a∈P) : 1≤(F a).card := by
    change 1≤((Local.neg G a).erase c).card
    rw [Finset.card_erase_of_mem (common ha)]
    have h := rows a; omega
  have card := Finset.sum_le_sum each
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.mul_one] at card
  exact card.trans le

theorem pressure_table {n m t : ℕ} (small : m≤7) (large : 17≤n+m)
    (p : n+t*((m-3).choose 2-1) ≤ m.choose 2) : t≤2 ∧ 3+(m-1)<n := by
  interval_cases m <;> norm_num [Nat.choose] at p ⊢ <;> omega

theorem two_same_side {n m : ℕ} (G : Fin n → Fin m → Bool) (rows : Local.GoodRows G)
    (nf : Local.NoFour G) (large : 17≤n+m) (many : 1<(Local.few G Finset.univ).card) :
    (Local.few G Finset.univ).card≤2 ∧ Local.few (Local.flip G) Finset.univ=∅ := by
  classical
  obtain ⟨small,p⟩ := pair_pressure G rows nf many
  obtain ⟨count,wide⟩ := pressure_table small large p
  refine ⟨count,Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro c hc
  have low : (Local.pos (Local.flip G) Finset.univ c).card≤3 := (Finset.mem_filter.mp hc).2
  have cap := degree_cap G rows nf c
  have cover : (Finset.univ : Finset (Fin n))⊆Local.pos (Local.flip G) Finset.univ c ∪ Local.neg (Local.flip G) c := by
    intro a _
    cases h : G a c
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have total := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ,Fintype.card_fin] at total; omega

theorem large_marks {n m : ℕ} (G : Fin n → Fin m → Bool) (rows : Local.GoodRows G)
    (cols : Local.GoodRows (Local.flip G)) (nf : Local.NoFour G) (large : 17≤n+m) :
    (marks G).card≤2 := by
  have cap := mark_size G
  by_cases a : 1<(Local.few G Finset.univ).card
  · obtain ⟨small,empty⟩ := two_same_side G rows nf large a
    rw [empty,Finset.card_empty] at cap; omega
  by_cases b : 1<(Local.few (Local.flip G) Finset.univ).card
  · obtain ⟨small,empty⟩ := two_same_side (Local.flip G) cols (Local.flip_four nf) (by omega) b
    change Local.few G Finset.univ=∅ at empty
    rw [empty,Finset.card_empty] at cap; omega
  omega

end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def hits (N : ℕ) (C : Circuit) := (Finset.range (N+C.size)).filter (fun w=>2≤Active C w)
def gatesHit (N : ℕ) (C : Circuit) := (Finset.range C.size).filter (fun j=>2≤Active C (N+j))
def hitUses (N : ℕ) (C : Circuit) := ∑ w∈hits N C,Active C w

theorem noNegs (C : Circuit) (mono : Monotone2 C) : Partition.neg69 C=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨mem,op⟩ := Finset.mem_filter.mp hj
  have lt : j<C.gates.length := Finset.mem_range.mp mem
  have gm : gateAt C j∈C.gates := by rw [gateAt,List.getD_eq_getElem _ _ lt]; exact List.getElem_mem lt
  have yes:=(mono _ gm).1
  change (gateAt C j).op=GateOp.not at op
  rw [op] at yes; simp at yes

theorem weights (N : ℕ) (C : Circuit) (mono : Monotone2 C) :
    (sharedRaw N C).card+(gatesHit N C).card≤budget N C ∧
    hitUses N C≤2*budget N C ∧ budget N C≤hitUses N C := by
  classical
  have k : budget N C=surplus N C := by simp [budget,noNegs C mono]
  let R:=sharedRaw N C
  let J:=(gatesHit N C).image (fun j=>N+j)
  have dis : Disjoint R J := by
    apply Finset.disjoint_left.mpr
    intro w hw hj
    have lo := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
    obtain ⟨j,_,e⟩:=Finset.mem_image.mp hj
    change N+j=w at e; omega
  have incl : R∪J⊆hits N C := by
    intro w hw
    rcases Finset.mem_union.mp hw with a|b
    · obtain ⟨rn,v⟩:=Finset.mem_filter.mp a
      have low:=Finset.mem_range.mp rn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),v⟩
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp b
      obtain ⟨mem,v⟩:=Finset.mem_filter.mp hj
      have low:=Finset.mem_range.mp mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),v⟩
  have card := Finset.card_le_card incl
  have inj : Function.Injective (fun j : ℕ => N+j):=fun _ _ e => Nat.add_left_cancel e
  rw [Finset.card_union_of_disjoint dis,show J.card=(gatesHit N C).card from Finset.card_image_of_injective _ inj] at card
  have maxHit : (hits N C).card ≤ surplus N C := many_count _ _
  have exactSum : (∑w∈hits N C,(Active C w-1))=surplus N C := by
    unfold hits surplus
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw out
    have h : ¬2≤Active C w := fun p=>out (Finset.mem_filter.mpr ⟨hw,p⟩)
    omega
  have total : hitUses N C=(hits N C).card+surplus N C := by
    calc
      hitUses N C = ∑ w∈hits N C, (1+(Active C w-1)) := by
        apply Finset.sum_congr rfl
        intro w hw
        have h : 2≤Active C w := (Finset.mem_filter.mp hw).2
        omega
      _ = _ := by rw [Finset.sum_add_distrib,exactSum]; simp
  change R.card+_≤_ ∧ _
  omega

theorem refinedCount (parts : CutPartition) (N : ℕ) (C : Circuit) (H : Finset ℕ)
    (mono : Monotone2 C) (shape : Partition.shapes69 C) (back : ReadsBack N C) (pos : 0<C.size)
    (last : C.output+1=N+C.size) (live : ∀j<C.size, j+1<C.size → 0<Active C (N+j))
    (small : ∀ S E, S⊆Finset.range N → E.card≤1 → broadTree N C S E → S.card≤2+2*(S∩H).card) :
    ∃ e : ℕ, (0<budget N C → 0<e) ∧ used N C+4*e≤10*budget N C+2+2*H.card := by
  classical
  obtain ⟨P,Q,e,p,q,yes,dis,all,pureT,entryT⟩ := parts N C shape back pos last live
  change P.length+e≤(gatesHit N C).card+(Partition.neg69 C).card+1 at p
  change Q.length+e≤2*(hitUses N C+(Partition.neg69 C).card) at q
  change (0<hitUses N C+(Partition.neg69 C).card → 0<e) at yes
  simp only [noNegs C mono,Finset.card_empty,Nat.add_zero] at p q yes
  have bounds : ∀ S∈P++Q, S.card≤2+2*(S∩H).card := by
    intro S mem
    have sub : S⊆Finset.range N := by
      intro w hw
      have incl : w∈(P++Q).toFinset.biUnion id := Finset.mem_biUnion.mpr ⟨S,List.mem_toFinset.mpr mem,hw⟩
      rw [show (P++Q).toFinset.biUnion id=Partition.once69 N C from all] at incl
      exact (Finset.mem_filter.mp incl).1
    rcases List.mem_append.mp mem with s|t
    · exact small S ∅ sub (by simp) (pureT S s).2
    · obtain ⟨_,b,h⟩:=entryT S t; exact small S {b} sub (by simp) h
  have count:=marked_union (P++Q) H dis bounds
  rw [show (P++Q).toFinset.biUnion id=Partition.once69 N C from all,List.length_append] at count
  have marked:=Finset.card_le_card (Finset.inter_subset_right (s₁:=Partition.once69 N C) (s₂:=H))
  have ⟨gates,uses,nonzero⟩:=weights N C mono
  have split : used N C=(Partition.once69 N C).card+(sharedRaw N C).card := by
    unfold used Partition.once69 sharedRaw
    rw [Finset.card_filter,Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; change (if 1≤Active C i then 1 else 0)=(if Active C i=1 then 1 else 0)+(if 2≤Active C i then 1 else 0)
    split_ifs <;> omega
  exact ⟨e,fun positive=>yes (by omega),by omega⟩
end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

theorem refined (parts : CutPartition) {n m : ℕ} (G : Fin n → Fin m → Bool) (C : Circuit)
    (r : Local.GoodRows G) (c : Local.GoodRows (Local.flip G)) (nf : Local.NoFour G)
    (mono : Monotone2 C) (rep : Represents G C) :
    11*(n+m)≤10*C.size+16 ∧ (17≤n+m → 11*(n+m)≤10*C.size+12) ∧
    ((∀a,3≤(Local.neg G a).card) → (∀x,3≤(Local.neg (Local.flip G) x).card) → 11*(n+m)≤10*C.size+8) := by
  classical
  by_cases empty : n+m=0
  · constructor
    · omega
    · constructor <;> intros <;> omega
  obtain ⟨r0,c0,r1,c1,horiz,vert⟩:=graph_data G (by omega) r c nf
  have fan : FanInTwo C := by
    intro g hg; obtain ⟨h,le⟩:=mono g hg
    refine ⟨?_,le⟩
    rcases h with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Set.mem_singleton_iff.mp h))
  obtain ⟨D,small,mon,repD,back,shape,positive,last,live⟩:=normalized C fan mono rep horiz vert
  have base:=budget_eq D shape back positive live
  have all:=all_used G D mon back repD (output_not_raw repD horiz vert) r0 c0 r1 c1
  let K:=budget (n+m) D
  change D.size+1=used (n+m) D+K at base
  have cap:=broadCaps G D r c nf mon back repD
  have old:=caps G D r c nf mon back repD
  have lowK (zero : K=0) : n+m≤6 := by
    have rough:=account (n+m) D 6 6 shape back positive last live
      (fun S sub tree=>(old S ∅ sub (by simp) tree).1)
      (fun S b sub tree=>(old S {b} sub (by simp) tree).1)
    change used (n+m) D≤(2*6+4*6+1)*K+6 at rough
    omega
  have largeBound (large : 17≤n+m) : 11*(n+m)≤10*C.size+12 := by
    have limited:=large_marks G r c nf large
    obtain ⟨e,charged,bound⟩:=refinedCount parts (n+m) D (marks G) mon shape back positive last live
      (fun S E sub one tree=>(cap S E sub one tree).2.1)
    change used (n+m) D+4*e≤10*K+2+2*(marks G).card at bound
    by_cases no : K=0
    · have h:=lowK no; omega
    · have positiveK : 0<K:=by omega
      have h:=charged positiveK; omega
  constructor
  · by_cases large : 17≤n+m
    · have h:=largeBound large; omega
    · by_cases zero : K=0
      · have h:=lowK zero; omega
      · omega
  refine ⟨largeBound,?_⟩
  intro highR highC
  obtain ⟨e,charged,bound⟩:=refinedCount parts (n+m) D ∅ mon shape back positive last live (fun S E sub one tree=>by
    simpa using (cap S E sub one tree).2.2 highR highC)
  change used (n+m) D+4*e≤10*K+2+2*(∅ : Finset ℕ).card at bound
  simp only [Finset.card_empty,Nat.mul_zero,Nat.add_zero] at bound
  by_cases no : K=0
  · obtain ⟨a,x,y,_⟩:=horiz
    have h:=highR a
    have len:=(Local.neg G a).card_le_univ
    simp only [Fintype.card_fin] at len
    omega
  · have positiveK : 0<K:=by omega
    have h:=charged positiveK; omega
end PEqualNP.Outside.L_meta_25646_aux

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def gates69 (C : Circuit) := Finset.range C.size
def reads69 (C : Circuit) (w : Nat) := readsIn C (gates69 C) w
noncomputable def neg69 (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>(gateAt C k).op=.not)
noncomputable def special (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact ((Finset.range (N+C.size)).filter (fun w=>2≤reads69 C w)) ∪
    (neg69 C).image (fun k=>N+k)
noncomputable def ordinary (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>N+k∉special N C)
noncomputable def exits69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈gates69 C \ ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∉special N C))
noncomputable def entries69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∈special N C))
def once69 (N : Nat) (C : Circuit) := (Finset.range N).filter (fun w=>reads69 C w=1)
def shapes69 (C : Circuit) : Prop := ∀g∈C.gates,
  ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)

def tree69 (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ ordinary N C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ reads69 C w=1 ∧ C.output≠w)

theorem ordinary_reads69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    reads69 C (N+k)≤1 := by
  classical
  obtain ⟨hk,hn⟩:=Finset.mem_filter.mp h
  have lt : k<C.size := Finset.mem_range.mp hk
  by_contra! many
  exact hn (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩))

theorem ordinary_index69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp h).1

end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def color69 (N : Nat) (C : Circuit) (w : Nat) : Bool :=
  if w∈special N C then true else if w<N then false else
    (gateAt C (w-N)).inputs.any (fun v => if hv : v<w then color69 N C v else false)
termination_by w

noncomputable def split69 (N : Nat) (C : Circuit) :=
  (ordinary N C).filter (fun j=>2≤((gateAt C j).inputs.filter (color69 N C)).length)

noncomputable def keep69 (N : Nat) (C : Circuit) := ordinary N C \ split69 N C

theorem color_special {N w : Nat} {C : Circuit} (h : w∈special N C) : color69 N C w=true := by
  rw [color69,ite_eq_left h]

theorem color_raw {N w : Nat} {C : Circuit} (hw : w<N) (h : w∉special N C) :
    color69 N C w=false := by rw [color69,ite_eq_right h,ite_eq_left hw]

theorem color_ordinary_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈ordinary N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true := by
  have ns := (Finset.mem_filter.mp hj).2
  rw [color69,ite_eq_right ns,ite_eq_right (by omega : ¬N+j<N),Nat.add_sub_cancel_left,List.any_eq_true]
  apply exists_congr
  intro w
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩

theorem color_keep_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈keep69 N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true :=
  color_ordinary_iff back (Finset.mem_sdiff.mp hj).1

theorem marked_keep_slots {N j : Nat} {C : Circuit} (hj : j∈keep69 N C) :
    ((gateAt C j).inputs.filter (color69 N C)).length≤1 := by
  obtain ⟨ord,no⟩ := Finset.mem_sdiff.mp hj
  by_contra! two
  exact no (Finset.mem_filter.mpr ⟨ord,two⟩)

theorem color_split_all {N j : Nat} {C : Circuit} (sh : shapes69 C) (hj : j∈split69 N C) :
    ∀ w∈(gateAt C j).inputs,color69 N C w=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  have jlt : j<C.gates.length := ordinary_index69 ord
  have mem : gateAt C j∈C.gates := by simp [gateAt,jlt]
  have len : (gateAt C j).inputs.length≤2 := by rcases sh _ mem with h|h <;> omega
  apply List.length_filter_eq_length_iff.mp
  have hl := List.length_filter_le (p:=color69 N C) (l:=(gateAt C j).inputs)
  omega

theorem color_split_self {N j : Nat} {C : Circuit} (back : ReadsBack N C) (hj : j∈split69 N C) :
    color69 N C (N+j)=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  apply (color_ordinary_iff back ord).2
  rw [←List.countP_pos_iff,List.countP_eq_length_filter]
  omega

lemma maskedCount69 (l : List Nat) (A : Finset Nat) :
    l.countP (fun w=>decide (w∈A)) = ∑w∈A,l.count w := by
  classical
  let f := l.filter (fun w=>decide (w∈A))
  have sub : f.toFinset ⊆ A := by
    intro w hw
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change f.length=_
  calc
    _ = ∑w∈f.toFinset,f.count w := (List.sum_toFinset_count_eq_length f).symm
    _ = ∑w∈A,f.count w := Finset.sum_subset sub (fun _ _ h =>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))
    _ = _ := Finset.sum_congr rfl (fun w hw=>List.count_filter (by simpa using hw))

lemma countCover69 (l : List Nat) (p s a : Nat→Bool)
    (cover : ∀w∈l,p w=true → s w=true ∨ a w=true) : l.countP p≤l.countP s+l.countP a := by
  induction l with
  | nil => simp
  | cons w ws ih =>
    have tail := ih (fun v hv=>cover v (List.mem_cons_of_mem _ hv))
    have head := cover w List.mem_cons_self
    cases hp : p w <;> cases hs : s w <;> cases ha : a w <;> simp_all [List.countP_cons] <;> omega

theorem countedSlots69 {N : Nat} {C : Circuit} (P A : Finset Nat)
    (p : Nat→Bool) (pg : P⊆ordinary N C) (ag : A⊆ordinary N C)
    (cover : ∀ j∈P, ∀w∈(gateAt C j).inputs,p w=true →
      w∈special N C ∨ w∈A.image (fun t=>N+t)) :
    (∑j∈P,(gateAt C j).inputs.countP p)≤entries69 N C+A.card := by
  classical
  let I := A.image (fun j=>N+j)
  let specialSlot := fun w=>decide (w∈special N C)
  have each (j : Nat) (hj : j∈P) : (gateAt C j).inputs.countP p ≤
      (gateAt C j).inputs.countP specialSlot + ∑w∈I,(gateAt C j).inputs.count w := by
    rw [←maskedCount69]
    apply countCover69
    intro w hw hp
    exact (cover j hj w hw hp).imp (fun h=>by simpa [specialSlot] using h) (fun h=>by simpa [I] using h)
  have sl : (∑ j∈P,(gateAt C j).inputs.countP specialSlot) ≤ entries69 N C :=
    Finset.sum_le_sum_of_subset_of_nonneg pg (fun _ _ _ => Nat.zero_le _)
  have rest (w : Nat) (hw : w∈I) : (∑ j∈P,(gateAt C j).inputs.count w) ≤ 1 := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    apply le_trans (b:=reads69 C (N+j)) _ (ordinary_reads69 (ag hj))
    unfold reads69 readsIn
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
    exact fun q hq=>(Finset.mem_filter.mp (pg hq)).1
  have total := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_comm (s:=P) (t:=I)] at total
  have pool := Finset.sum_le_sum rest
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at pool
  have cap : I.card≤A.card := Finset.card_image_le
  omega

theorem splitCard69 {N : Nat} {C : Circuit} (_sh : shapes69 C) (back : ReadsBack N C) :
    (split69 N C).card≤entries69 N C := by
  classical
  let A := (ordinary N C).filter (fun j=>color69 N C (N+j)=true)
  have cover (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (hl : color69 N C w=true) : w∈special N C ∨ w∈A.image (fun t=>N+t) := by
    by_cases sp : w∈special N C
    · exact Or.inl sp
    right
    have wire : w<N+j := back j (ordinary_index69 hj) w hw
    have mid : N≤w := by by_contra! z;rw [color_raw z sp] at hl;contradiction
    have eq : N+(w-N)=w := by omega
    have idx : w-N<C.size := by have := ordinary_index69 hj;omega
    have good : w-N∈ordinary N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,by simpa only [eq] using sp⟩
    exact Finset.mem_image.mpr ⟨w-N,Finset.mem_filter.mpr ⟨good,by simpa only [eq] using hl⟩,eq⟩
  have account := countedSlots69 (ordinary N C) A (color69 N C) (fun _ h=>h)
    (fun _ h=>(Finset.mem_filter.mp h).1) cover
  have pay (j : Nat) (hj : j∈ordinary N C) :
      (if color69 N C (N+j)=true then 1 else 0) +
      (if 2≤((gateAt C j).inputs.filter (color69 N C)).length then 1 else 0) ≤
      (gateAt C j).inputs.countP (color69 N C) := by
    rw [List.countP_eq_length_filter]
    by_cases many : 2≤((gateAt C j).inputs.filter (color69 N C)).length
    · rw [ite_eq_left many];split <;> omega
    rw [ite_eq_right many]
    split
    · next hc =>
      have has := (color_ordinary_iff back hj).1 hc
      have pos := List.countP_pos_iff.mpr has
      rw [List.countP_eq_length_filter] at pos
      omega
    · omega
  have total := Finset.sum_le_sum pay
  rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter] at total
  change A.card+(split69 N C).card≤_ at total
  omega

theorem entrySlotsBound69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) :
    (∑j∈keep69 N C,(gateAt C j).inputs.countP
      (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))) ≤ 2*entries69 N C := by
  classical
  have cap := countedSlots69 (keep69 N C) (split69 N C)
    (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
    (fun _ h=>(Finset.mem_sdiff.mp h).1) (fun _ h=>(Finset.mem_filter.mp h).1) (by
      intro j hj w hw h
      rcases of_decide_eq_true h with s|⟨low,idx⟩
      · exact Or.inl s
      · exact Or.inr (Finset.mem_image.mpr ⟨w-N,idx,by omega⟩))
  have splitBound := splitCard69 sh back
  omega

end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def pool69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  once69 N C ∪ P.image (fun k=>N+k)

def branch69 (N : Nat) (C : Circuit) (P : Finset Nat) (x y : Nat) : Prop :=
  x∈pool69 N C P ∧ ∃k∈P, y=N+k ∧ x∈(gateAt C k).inputs

abbrev walk69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  Relation.ReflTransGen (branch69 N C P)

def sink69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Prop :=
  ∀ y, ¬ branch69 N C P x y

noncomputable def owner69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Nat := by
  classical exact if h : ∃y,walk69 N C P x y ∧ sink69 N C P y then h.choose else x

noncomputable def roots69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  (once69 N C).image (owner69 N C P)

noncomputable def src69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (once69 N C).filter (fun w=>owner69 N C P w=z)

noncomputable def reg69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact P.filter (fun k=>owner69 N C P (N+k)=z)

noncomputable def outside69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (reg69 N C P z).biUnion fun k =>
    (gateAt C k).inputs.toFinset.filter (fun w=>w∉pool69 N C P)

noncomputable def slots69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Nat := by
  classical exact ∑ k∈reg69 N C P z,(gateAt C k).inputs.countP (fun w=>decide (w∉pool69 N C P))

variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem reads_le_one69 (hp : P⊆ordinary N C) {w : Nat} (hw : w∈pool69 N C P) : reads69 C w≤1 := by
  rcases Finset.mem_union.mp hw with h | h
  · exact (Finset.mem_filter.mp h).2.le
  · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp h;exact ordinary_reads69 (hp hk)

theorem reader69 {w i j : Nat} (one : reads69 C w≤1) (hi : i<C.size) (hj : j<C.size)
    (a : w∈(gateAt C i).inputs) (b : w∈(gateAt C j).inputs) : i=j := by
  by_contra ne
  have h:=Finset.add_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _)
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) ne
  have ai:=List.count_pos_iff.mpr a
  have bj:=List.count_pos_iff.mpr b
  change _ ≤ reads69 C w at h
  omega

theorem next_unique69 (hp : P⊆ordinary N C) : Relator.RightUnique (branch69 N C P) := by
  rintro w x y ⟨hw,i,hi,rfl,a⟩ ⟨_,j,hj,rfl,b⟩
  rw [reader69 (reads_le_one69 hp hw) (ordinary_index69 (hp hi)) (ordinary_index69 (hp hj)) a b]

theorem next_lt69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (h : branch69 N C P x y) : x<y ∧ y<N+C.size := by
  obtain ⟨_,k,hk,rfl,inp⟩:=h
  have lt:=ordinary_index69 (hp hk)
  exact ⟨back k lt x inp,by omega⟩

theorem walk_in69 {x y : Nat} (h : walk69 N C P x y) (hx : x∈pool69 N C P) :
    y∈pool69 N C P := by
  induction h with
  | refl => exact hx
  | tail _ e _ =>
    obtain ⟨_,k,hk,rfl,_⟩ := e
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)

theorem owner_spec69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (w : Nat) :
    walk69 N C P w (owner69 N C P w) ∧ sink69 N C P (owner69 N C P w) := by
  classical
  have exists' (i : Nat) : ∀x,N+C.size-x=i → ∃y,walk69 N C P x y ∧ sink69 N C P y := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro x eq
      by_cases e : ∃y,branch69 N C P x y
      · obtain ⟨y,hy⟩:=e
        obtain ⟨lt,bound⟩:=next_lt69 hp back hy
        obtain ⟨v,path,sink⟩:=ih (N+C.size-y) (by omega) y rfl
        exact ⟨v,path.head hy,sink⟩
      · exact ⟨x,.refl,fun y h=> e ⟨y,h⟩⟩
  have h:=exists' _ w rfl
  simpa only [owner69,dif_pos h] using h.choose_spec

theorem owner_same69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (e : branch69 N C P x y) : owner69 N C P x = owner69 N C P y := by
  have a := owner_spec69 hp back x
  have b := owner_spec69 hp back y
  have term {u v : Nat} (s : sink69 N C P u) (path : walk69 N C P u v) : u=v := by
    rcases path.cases_head with eq|⟨z,e,_⟩
    · exact eq
    · exact (s z e).elim
  rcases Relation.ReflTransGen.total_of_right_unique (next_unique69 hp)
    a.1 (b.1.head e) with h|h
  · exact term a.2 h
  · exact (term b.2 h).symm

theorem fiber69 (z w : Nat) :
    w∈src69 N C P z ∪ (reg69 N C P z).image (fun k=>N+k) ↔
      w∈pool69 N C P ∧ owner69 N C P w=z := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with a|b
    · obtain ⟨h,e⟩:=Finset.mem_filter.mp a;exact ⟨Finset.mem_union_left _ h,e⟩
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      obtain ⟨h,e⟩:=Finset.mem_filter.mp hk;exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ h),e⟩
  · rintro ⟨pool,e⟩
    rcases Finset.mem_union.mp pool with a|b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨a,e⟩)
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hk,e⟩))

theorem root_info69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    z∈pool69 N C P ∧ sink69 N C P z ∧ owner69 N C P z=z ∧ (src69 N C P z).Nonempty := by
  obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
  have sp:=owner_spec69 hp back u
  refine ⟨walk_in69 sp.1 (Finset.mem_union_left _ hu),sp.2,?_,⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩⟩
  have p:=(owner_spec69 hp back (owner69 N C P u)).1
  rcases p.cases_head with eq|⟨x,step,_⟩
  · exact eq.symm
  · exact (sp.2 x step).elim

end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem root_zero69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    readsIn C (reg69 N C P z) z=0 := by
  obtain ⟨pool,sink,_,_⟩:=root_info69 hp back hz
  apply Finset.sum_eq_zero
  intro j hj;apply List.count_eq_zero.mpr
  intro h;exact sink (N+j) ⟨pool,j,(Finset.mem_filter.mp hj).1,rfl,h⟩

theorem local_read69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z w : Nat}
    (pool : w∈pool69 N C P) (ow : owner69 N C P w=z) (other : w≠z) :
    readsIn C (reg69 N C P z) w=1 ∧ reads69 C w=1 := by
  obtain ⟨way,_⟩:=owner_spec69 hp back w
  rw [ow] at way
  obtain ⟨_,⟨_,k,hk,rfl,hit⟩,_⟩:=way.cases_head.resolve_left other
  have eq := owner_same69 hp back (show branch69 N C P w (N+k) from ⟨pool,k,hk,rfl,hit⟩)
  have mem : k∈reg69 N C P z := Finset.mem_filter.mpr ⟨hk,eq.symm.trans ow⟩
  have le : (gateAt C k).inputs.count w ≤ readsIn C (reg69 N C P z) w :=
    Finset.single_le_sum (fun l _=>Nat.zero_le ((gateAt C l).inputs.count w)) mem
  have bound : readsIn C (reg69 N C P z) w ≤ reads69 C w :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun j hj =>
      Finset.mem_range.mpr (ordinary_index69 (hp (Finset.mem_filter.mp hj).1))) (fun _ _ _=>Nat.zero_le _)
  have counted:=List.count_pos_iff.mpr hit;have all:=reads_le_one69 hp pool
  omega

theorem pool_bound69 (hp : P⊆ordinary N C) {w : Nat} (pool : w∈pool69 N C P) : w<N+C.size := by
  rcases Finset.mem_union.mp pool with h|h
  · have lt:=Finset.mem_range.mp (Finset.mem_filter.mp h).1;omega
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h;have:=ordinary_index69 (hp hj);omega

theorem walk_le69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat} (path : walk69 N C P x y) :
    x≤y := by
  induction path with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (next_lt69 hp back e).1.le

theorem outside_mem69 {z w : Nat} :
    w∈outside69 N C P z ↔ w∉pool69 N C P ∧ ∃k∈reg69 N C P z,w∈(gateAt C k).inputs := by
  classical
  simp only [outside69,Finset.mem_biUnion,Finset.mem_filter,List.mem_toFinset]
  grind

theorem read_le_slots69 {z w : Nat} (out : w∉pool69 N C P) :
    readsIn C (reg69 N C P z) w ≤ slots69 N C P z := by
  classical
  apply Finset.sum_le_sum
  intro k _
  induction (gateAt C k).inputs with
  | nil => simp
  | cons a l ih =>
    simp only [decide_not] at ih
    by_cases eq : a=w
    · subst a;simp [List.count_cons,List.countP_cons,out,ih]
    · by_cases pa:a∈pool69 N C P <;> simp [List.count_cons,List.countP_cons,eq,pa,ih] <;> omega

theorem out_pos69 {z w : Nat} (h : w∈outside69 N C P z) :
    0<readsIn C (reg69 N C P z) w ∧ readsIn C (reg69 N C P z) w≤ slots69 N C P z := by
  obtain ⟨no,k,hk,hx⟩:=outside_mem69.mp h
  exact ⟨(List.count_pos_iff.mpr hx).trans_le
    (Finset.single_le_sum (fun j _=>Nat.zero_le ((gateAt C j).inputs.count w)) hk),read_le_slots69 no⟩

theorem outside_card69 {z : Nat} : (outside69 N C P z).card ≤ slots69 N C P z := by
  classical
  unfold outside69 slots69
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro k _
  have h (l : List Nat) : (l.toFinset.filter (fun w=>w∉pool69 N C P)).card ≤
      l.countP (fun w=>decide (w∉pool69 N C P)) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [decide_not] at ih
      by_cases hw:w∈pool69 N C P
      · simpa [Finset.filter_insert,hw,List.countP_cons] using ih
      · simp [Finset.filter_insert,hw,List.countP_cons]
        exact (Finset.card_insert_le _ _).trans (by omega)
  exact h _

theorem outside_empty69 {z : Nat} : outside69 N C P z=∅ ↔ slots69 N C P z=0 := by
  classical
  constructor
  · intro empty;apply Finset.sum_eq_zero;intro k hk
    apply List.countP_eq_zero.mpr
    intro w hw
    simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_not]
    by_contra out
    have h : w∈outside69 N C P z := outside_mem69.mpr ⟨out,k,hk,hw⟩
    simp [empty] at h
  · intro z0;apply Finset.card_eq_zero.mp;have le:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z);omega

theorem subtree69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (sh : shapes69 C)
    (last : C.output+1=N+C.size) {z : Nat} (hz : z∈roots69 N C P)
    (slot : slots69 N C P z≤1) : tree69 N C (src69 N C P z) (outside69 N C P z) := by
  classical
  obtain ⟨zp,sink,zown,nonempty⟩:=root_info69 hp back hz
  have bound:=pool_bound69 hp zp
  refine ⟨reg69 N C P z,z,fun j hj=>hp (Finset.mem_filter.mp hj).1,
    (fiber69 z z).mpr ⟨zp,zown⟩,root_zero69 hp back hz,?_,?_,?_⟩
  · intro w hw
    obtain ⟨out,k,hk,read⟩:=outside_mem69.mp hw
    have lt:=back k (ordinary_index69 (hp (Finset.mem_filter.mp hk).1)) w read
    have path:=(owner_spec69 hp back (N+k)).1
    rw [(Finset.mem_filter.mp hk).2] at path
    have cmp:=walk_le69 hp back path
    obtain ⟨pos,le⟩:=out_pos69 hw
    exact ⟨fun h=>out ((fiber69 z w).mp h).1,by omega,by omega⟩
  · intro j hj
    obtain ⟨keep,own⟩:=Finset.mem_filter.mp hj
    have ord:=hp keep;have jl:=ordinary_index69 ord
    have mem : gateAt C j∈C.gates := by have h:j<C.gates.length:=jl;simp [gateAt,h]
    rcases sh _ mem with ao | no
    · refine ⟨ao.1,ao.2,?_⟩
      intro w wh
      by_cases pooled:w∈pool69 N C P
      · exact Or.inl ((fiber69 z w).mpr ⟨pooled,(owner_same69 hp back ⟨pooled,j,keep,rfl,wh⟩).trans own⟩)
      · exact Or.inr (outside_mem69.mpr ⟨pooled,j,hj,wh⟩)
    · have ns: N+j∉special N C := (Finset.mem_filter.mp ord).2
      apply (ns (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (show j∈neg69 C from Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jl,no.1⟩)))).elim
  · intro w hw diff
    obtain ⟨pool,own⟩:=(fiber69 z w).mp hw
    obtain ⟨loc,all⟩:=local_read69 hp back pool own diff
    have path:=(owner_spec69 hp back w).1
    rw [own] at path
    have le:=walk_le69 hp back path
    exact ⟨loc,all,by omega⟩

end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C:Circuit}
lemma keepSub69 : keep69 N C ⊆ ordinary N C := Finset.sdiff_subset
lemma colorOnce69 {w:Nat} (h:w∈once69 N C) : color69 N C w=false := by
  obtain ⟨hw,one⟩:=Finset.mem_filter.mp h
  have lo:=Finset.mem_range.mp hw
  apply color_raw lo
  intro hs
  rcases Finset.mem_union.mp hs with rep|notw
  · have high:2≤reads69 C w := (Finset.mem_filter.mp rep).2
    omega
  · obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp notw;omega
lemma colorOuter69 (back:ReadsBack N C) {j w:Nat} (hp:j∈keep69 N C) (hit:w∈(gateAt C j).inputs)
    (out:w∉pool69 N C (keep69 N C)) : color69 N C w=true := by
  classical
  have jj:=ordinary_index69 (keepSub69 hp)
  have wr:=back j jj w hit
  by_cases hs:w∈special N C
  · exact color_special hs
  by_cases low:w<N
  · have used:0<reads69 C w := by
      have h:=Finset.single_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr jj)
      have count:=List.count_pos_iff.mpr hit
      change _≤reads69 C w at h
      omega
    have one:reads69 C w=1 := by
      by_contra! ne
      apply hs
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩)
    exact (out (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr low,one⟩))).elim
  · let k:=w-N
    have eq:N+k=w := by dsimp [k];omega
    have ord:k∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [k];omega),by rwa [eq]⟩
    by_cases sp:k∈split69 N C
    · exact eq ▸ color_split_self back sp
    · have kkeep:k∈keep69 N C:=Finset.mem_sdiff.mpr ⟨ord,sp⟩
      exact (out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,kkeep,eq⟩))).elim

lemma markedInputs69 (back:ReadsBack N C) {j:Nat} (h:j∈keep69 N C) :
    (gateAt C j).inputs.countP (color69 N C) = if color69 N C (N+j) then 1 else 0 := by
  have le:=marked_keep_slots h
  rw [←List.countP_eq_length_filter] at le
  have pos := color_keep_iff back h
  rw [←List.countP_pos_iff] at pos
  cases hx:color69 N C (N+j)
  · change (gateAt C j).inputs.countP (color69 N C)=0
    by_contra! ne
    have eq:=pos.mpr (by omega)
    rw [hx] at eq;contradiction
  · change (gateAt C j).inputs.countP (color69 N C)=1
    have hp:=pos.mp hx
    omega

lemma splitInputCount69 (L:List Nat) (p:Nat→Bool) (pool A:Finset Nat)
    (spec:∀w∈L, (p w=true ↔ w∉pool ∨ w∈A) ∧ (w∈A → w∈pool)) :
    L.countP p = L.countP (fun w=>decide (w∉pool)) + ∑w∈A,L.count w := by
  classical
  induction L with
  | nil => simp
  | cons x xs ih =>
    have t:=ih (fun w hw=>spec w (List.mem_cons_of_mem _ hw))
    simp only [List.countP_cons,List.count_cons,Finset.sum_add_distrib]
    have a:=spec x (by simp)
    by_cases xA:x∈A <;> by_cases xp:x∈pool <;> cases xx:p x <;>
      simp_all <;> omega
end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem conserved69 {N z:Nat} {C:Circuit} (back:ReadsBack N C)
    (hz:z∈roots69 N C (keep69 N C))
    (lr:∀ j∈reg69 N C (keep69 N C) z,
      readsIn C (reg69 N C (keep69 N C) z) (N+j)=if N+j=z then 0 else 1) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  classical
  let P:=keep69 N C
  let pool:=pool69 N C P
  let rg:=reg69 N C P z
  let hot:=rg.filter (fun j=>color69 N C (N+j)=true)
  let A:=hot.image (fun j=>N+j)
  have acard:A.card=hot.card:=Finset.card_image_of_injective _ (fun _ _ e=>Nat.add_left_cancel e)
  have rgKeep (j:Nat) (hj:j∈rg):j∈P:=(Finset.mem_filter.mp hj).1
  have memA {w:Nat} : w∈A ↔ w∈pool ∧ owner69 N C P w=z ∧ color69 N C w=true := by
    constructor
    · intro h;obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h
      obtain ⟨jr,marked⟩:=Finset.mem_filter.mp hj
      exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (rgKeep _ jr)),(Finset.mem_filter.mp jr).2,marked⟩
    · rintro ⟨h,o,t⟩
      rcases Finset.mem_union.mp h with raw|gate
      · exact (by rw [colorOnce69 raw] at t; contradiction : False).elim
      · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp gate
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hj,o⟩,t⟩,rfl⟩
  have inEq (j:Nat) (hj:j∈rg) :
      (gateAt C j).inputs.countP (color69 N C) =
        (gateAt C j).inputs.countP (fun w=>decide (w∉pool)) + ∑w∈A,(gateAt C j).inputs.count w := by
    apply splitInputCount69
    intro w hit
    have memPool (h:w∈pool) : owner69 N C P w=z := by
      have p:=owner_same69 (P:=P) keepSub69 back (show branch69 N C P w (N+j) from ⟨h,j,rgKeep _ hj,rfl,hit⟩)
      exact p.trans (Finset.mem_filter.mp hj).2
    refine ⟨⟨fun t=>?_,?_⟩,fun h=>(memA.mp h).1⟩
    · by_cases pw:w∈pool
      · exact Or.inr (memA.mpr ⟨pw,memPool pw,t⟩)
      · exact Or.inl pw
    · rintro (out|inside)
      · exact colorOuter69 back (rgKeep _ hj) hit out
      · exact (memA.mp inside).2.2
  have calcAll : hot.card=slots69 N C P z+∑w∈A,readsIn C rg w := by
    calc
      hot.card = ∑j∈rg, if color69 N C (N+j) then 1 else 0 := by simp only [hot,Finset.card_filter]
      _ = ∑j∈rg,(gateAt C j).inputs.countP (color69 N C) :=
        Finset.sum_congr rfl (fun j hj=>(markedInputs69 back (rgKeep _ hj)).symm)
      _ = _ := by
        rw [Finset.sum_congr rfl inEq,Finset.sum_add_distrib]
        congr 1;exact Finset.sum_comm
  have lower : (∑w∈A,readsIn C rg w)+(if z∈A then 1 else 0)=A.card := by
    calc
      _ = (∑w∈A,if w=z then 0 else 1) + (∑w∈A,if w=z then 1 else 0) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro w hw;obtain ⟨j,m,rfl⟩:=Finset.mem_image.mp hw
          exact lr _ (Finset.mem_filter.mp m).1
        · simp
      _ = ∑_w∈A,1 := by
        rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro w _;split <;> simp_all
      _ = _ := by simp
  have root:=root_info69 (P:=P) keepSub69 back hz
  have za : z∈A ↔ color69 N C z=true := ⟨fun h=>(memA.mp h).2.2,fun h=>memA.mpr ⟨root.1,root.2.2.1,h⟩⟩
  change slots69 N C P z=_
  simp only [za] at lower
  omega
end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem fiberSlots69 {N z:Nat} {C:Circuit} (back:ReadsBack N C) (hz:z∈roots69 N C (keep69 N C)) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  apply conserved69 back hz
  intro j hj
  by_cases eq:N+j=z
  · rw [eq,ite_eq_left rfl]
    exact root_zero69 keepSub69 back hz
  · rw [ite_eq_right eq]
    obtain ⟨m,e⟩:=Finset.mem_filter.mp hj
    have pool:N+j∈pool69 N C (keep69 N C):=Finset.mem_union_right _ (Finset.mem_image_of_mem _ m)
    exact (local_read69 keepSub69 back pool e eq).1
end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_reads_mask69 (l : List Nat) (A : Finset Nat) :
    (∑w∈A,l.count w) = l.countP (fun w=>decide (w∈A)) := by
  classical
  let f:=l.filter (fun w=>decide (w∈A))
  have sub:f.toFinset⊆A := fun _ hw=>of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change _=f.length
  calc
    _ = ∑w∈A,f.count w := Finset.sum_congr rfl (fun w hw=>(List.count_filter (by simpa using hw)).symm)
    _ = ∑w∈f.toFinset,f.count w := (Finset.sum_subset sub (fun _ _ h=>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))).symm
    _ = _ := List.sum_toFinset_count_eq_length f

theorem pure_sink69 {N z : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j))
    (hz : z∈roots69 N C (keep69 N C)) (zero : slots69 N C (keep69 N C) z=0) (out : z≠C.output) :
    z∉special N C ∧ ∃k∈gates69 C \ ordinary N C, z∈(gateAt C k).inputs := by
  classical
  obtain ⟨pool,sink,_,_⟩:=root_info69 keepSub69 back hz
  have slot:=fiberSlots69 back hz
  have off : color69 N C z=false := by cases h:color69 N C z <;> simp_all
  have ns : z∉special N C := fun h => by have a:=color_special h;rw [off] at a;contradiction
  have pos : 0<reads69 C z := by
    rcases Finset.mem_union.mp pool with raw|internal
    · have one : reads69 C z=1 := (Finset.mem_filter.mp raw).2;omega
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp internal
      have lt:=ordinary_index69 (keepSub69 hj)
      exact live j lt (by omega)
  have seek : ∃ k∈gates69 C, z∈(gateAt C k).inputs := by
    by_contra! no
    have none : reads69 C z=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
    omega
  obtain ⟨k,hk,hit⟩:=seek
  refine ⟨ns,k,Finset.mem_sdiff.mpr ⟨hk,?_⟩,hit⟩
  intro ord
  by_cases split:k∈split69 N C
  · have on:=color_split_all sh split z hit
    rw [off] at on;contradiction
  · exact sink (N+k) ⟨pool,k,Finset.mem_sdiff.mpr ⟨ord,split⟩,rfl,hit⟩

theorem pure_count69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)).card ≤ exits69 N C+1 := by
  classical
  let T:=(roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)
  let A:=T.erase C.output
  let gs:=gates69 C \ ordinary N C
  have obs (w : Nat) (hw:w∈A) : w∉special N C ∧ ∃k∈gs, w∈(gateAt C k).inputs := by
    obtain ⟨different,hh⟩:=Finset.mem_erase.mp hw
    obtain ⟨inR,zero⟩:=Finset.mem_filter.mp hh
    exact pure_sink69 sh back last live inR zero different
  have each (w:Nat) (hw:w∈A) : 1 ≤ ∑k∈gs,(gateAt C k).inputs.count w := by
    obtain ⟨k,hk,hit⟩:=(obs w hw).2
    exact (List.count_pos_iff.mpr hit).trans_le
      (Finset.single_le_sum (fun t _=>Nat.zero_le ((gateAt C t).inputs.count w)) hk)
  have bound : A.card≤exits69 N C := by
    calc
      _ = ∑ _∈A,1 := by simp
      _ ≤ ∑w∈A,∑k∈gs,(gateAt C k).inputs.count w := Finset.sum_le_sum each
      _ = ∑k∈gs,∑w∈A,(gateAt C k).inputs.count w := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        rw [sum_reads_mask69]
        exact List.countP_mono_left (fun w _ h => decide_eq_true ((obs w (of_decide_eq_true h)).1))
  change T.card≤exits69 N C+1
  have incl : T⊆insert C.output A := by
    intro z mem;by_cases e:z=C.output
    · exact Finset.mem_insert.mpr (Or.inl e)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨e,mem⟩))
  have step:=Finset.card_le_card incl
  have cap:=Finset.card_insert_le C.output A
  change T.card≤(insert C.output A).card at step
  omega
end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem mixed_count69 {N:Nat} {C:Circuit} (sh:shapes69 C) (back:ReadsBack N C) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)).card≤2*entries69 N C := by
  classical
  let P:=keep69 N C
  let R:=(roots69 N C P).filter (fun z=>slots69 N C P z≠0)
  let f:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∉pool69 N C P))
  let g:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
  have per (j:Nat) (hj:j∈P): f j≤g j := by
    apply List.countP_mono_left
    intro w hw out'
    have out:w∉pool69 N C P:=of_decide_eq_true out'
    apply decide_eq_true
    by_cases sp:w∈special N C
    · exact Or.inl sp
    · have color:=colorOuter69 back hj hw out
      have nle : N≤w:=by by_contra! h;rw [color_raw h sp] at color;contradiction
      have eq:N+(w-N)=w:=by omega
      have ji:=ordinary_index69 (keepSub69 hj)
      have wi:=back j ji w hw
      have ord:w-N∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [eq]⟩
      refine Or.inr ⟨nle,?_⟩
      by_contra ns
      have inside:w-N∈P:=Finset.mem_sdiff.mpr ⟨ord,ns⟩
      exact out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,inside,eq⟩))
  have lower (z:Nat) (hz:z∈R) : 1≤ slots69 N C P z := by
    have neq:slots69 N C P z≠0:=(Finset.mem_filter.mp hz).2
    omega
  change R.card≤_
  calc
    R.card = ∑_z∈R,1 := by simp
    _ ≤ ∑z∈R,slots69 N C P z := Finset.sum_le_sum lower
    _ = ∑j∈P.filter (fun i=>owner69 N C P (N+i)∈R), f j :=
      Finset.sum_fiberwise_eq_sum_filter P R (fun j=>owner69 N C P (N+j)) f
    _ ≤ ∑j∈P,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)
    _ ≤ ∑j∈P,g j := Finset.sum_le_sum per
    _ ≤ _ := entrySlotsBound69 sh back
end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem finish69 (N : Nat) (C : Circuit) (sh : shapes69 C) (back : ReadsBack N C)
    (_pos : 0<C.size) (last : C.output+1=N+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ∃ pure chains : List (Finset Nat),
      pure.length≤exits69 N C+1 ∧ chains.length≤2*entries69 N C ∧
      (pure++chains).Pairwise (fun A B=>Disjoint A B) ∧
      (pure++chains).toFinset.biUnion (fun S=>S)=once69 N C ∧
      (∀S∈pure,S.Nonempty ∧ tree69 N C S ∅) ∧
      (∀S∈chains,S.Nonempty ∧ ∃b : Nat,tree69 N C S {b}) := by
  classical
  let P:=keep69 N C
  let roots:=roots69 N C P
  let Q:=roots.filter (fun z=>slots69 N C P z=0)
  let M:=roots.filter (fun z=>slots69 N C P z≠0)
  let leaf:=src69 N C P
  let qr:=Q.toList
  let mr:=M.toList
  have qmem (z:Nat) : z∈qr ↔ z∈roots ∧ slots69 N C P z=0 := by simp [qr,Q]
  have mmem (z:Nat) : z∈mr ↔ z∈roots ∧ slots69 N C P z≠0 := by simp [mr,M]
  have covered (z:Nat) : z∈qr++mr ↔ z∈roots := by
    rw [List.mem_append,qmem,mmem];tauto
  have nd : (qr++mr).Nodup := by
    refine List.nodup_append.mpr ⟨Q.nodup_toList,M.nodup_toList,?_⟩
    intro x hx y hy e;subst y;exact (mmem x|>.mp hy).2 ((qmem x|>.mp hx).2)
  have fiber {w z:Nat}: w∈leaf z ↔ w∈once69 N C ∧ owner69 N C P w=z := Finset.mem_filter
  have facts {z:Nat} (hz:z∈roots) : (leaf z).Nonempty ∧
      tree69 N C (leaf z) (outside69 N C P z) := by
    have count:=fiberSlots69 back hz
    have le : slots69 N C P z≤1 := by rw [count];split <;> decide
    exact ⟨(root_info69 keepSub69 back hz).2.2.2,subtree69 keepSub69 back sh last hz le⟩
  refine ⟨qr.map leaf,mr.map leaf,?_,?_,?_,?_,?_,?_⟩
  · simpa only [qr,List.length_map,Finset.length_toList] using pure_count69 sh back last live
  · simpa only [mr,List.length_map,Finset.length_toList] using mixed_count69 sh back
  · rw [←List.map_append,List.pairwise_map]
    apply nd.imp
    intro a b diff
    apply Finset.disjoint_left.mpr
    intro w ha hb;exact diff ((fiber.mp ha).2.symm.trans (fiber.mp hb).2)
  · rw [←List.map_append]
    ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨_,⟨z,_,rfl⟩,hit⟩;exact (fiber.mp hit).1
    · intro raw
      let z:=owner69 N C P w
      have root:z∈roots:=Finset.mem_image_of_mem _ raw
      exact ⟨leaf z,⟨z,(covered z).mpr root,rfl⟩,fiber.mpr ⟨raw,rfl⟩⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,zero⟩:=(qmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    rw [outside_empty69.mpr zero] at tree
    exact ⟨ne,tree⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,nz⟩:=(mmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    have card : (outside69 N C P z).card=1 := by
      have cap:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z)
      have count:=fiberSlots69 back rt
      have nonempty : (outside69 N C P z).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (fun h=>nz (outside_empty69.mp h))
      have pos:=Finset.card_pos.mpr nonempty
      change slots69 N C P z=_ at count
      split at count <;> omega
    obtain ⟨b,eq⟩:=Finset.card_eq_one.mp card
    exact ⟨ne,b,eq ▸ tree⟩
end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem splitStrict44 {N : Nat} {C : Circuit} (_sh : shapes69 C) (back : ReadsBack N C) (pos : 0<entries69 N C) :
    (split69 N C).card<entries69 N C := by
  classical
  let A := (ordinary N C).filter (fun j=>color69 N C (N+j)=true)
  have cover (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (hl : color69 N C w=true) : w∈special N C ∨ w∈A.image (fun t=>N+t) := by
    by_cases sp : w∈special N C
    · exact Or.inl sp
    right
    have wire : w<N+j := back j (ordinary_index69 hj) w hw
    have mid : N≤w := by by_contra! z;rw [color_raw z sp] at hl;contradiction
    have eq : N+(w-N)=w := by omega
    have idx : w-N<C.size := by have := ordinary_index69 hj;omega
    have good : w-N∈ordinary N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,by simpa only [eq] using sp⟩
    exact Finset.mem_image.mpr ⟨w-N,Finset.mem_filter.mpr ⟨good,by simpa only [eq] using hl⟩,eq⟩
  by_cases ne : A.Nonempty
  case neg =>
    have emp : split69 N C=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun j hj =>
      ne ⟨j,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,color_split_self back hj⟩⟩)
    simpa [emp] using pos
  let top := A.max' ne
  have incl : A.erase top⊆ordinary N C := fun j hj=>(Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).1
  have cover' (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (on : color69 N C w=true) : w∈special N C ∨ w∈(A.erase top).image (fun t=>N+t) := by
    rcases cover j hj w hw on with h|h
    · exact Or.inl h
    · obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp h
      have later : N+t<N+j := back j (ordinary_index69 hj) _ hw
      have marked : j∈A:=Finset.mem_filter.mpr ⟨hj,(color_ordinary_iff back hj).mpr ⟨N+t,hw,on⟩⟩
      have limit : j≤top := Finset.le_max' _ _ marked
      exact Or.inr (Finset.mem_image.mpr ⟨t,Finset.mem_erase.mpr ⟨by omega,ht⟩,rfl⟩)
  have account := countedSlots69 (ordinary N C) (A.erase top) (color69 N C) (fun _ h=>h) incl cover'
  rw [Finset.card_erase_of_mem (Finset.max'_mem A ne)] at account
  have nonzero:=Finset.card_pos.mpr ne

  have pay (j : Nat) (hj : j∈ordinary N C) :
      (if color69 N C (N+j)=true then 1 else 0) +
      (if 2≤((gateAt C j).inputs.filter (color69 N C)).length then 1 else 0) ≤
      (gateAt C j).inputs.countP (color69 N C) := by
    rw [List.countP_eq_length_filter]
    by_cases many : 2≤((gateAt C j).inputs.filter (color69 N C)).length
    · rw [ite_eq_left many];split <;> omega
    rw [ite_eq_right many]
    split
    · next hc =>
      have has := (color_ordinary_iff back hj).1 hc
      have pos := List.countP_pos_iff.mpr has
      rw [List.countP_eq_length_filter] at pos
      omega
    · omega
  have total := Finset.sum_le_sum pay
  rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter] at total
  change A.card+(split69 N C).card≤_ at total
  omega

theorem entryStrict44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) (pos : 0<entries69 N C) :
    (∑j∈keep69 N C,(gateAt C j).inputs.countP
      (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))) < 2*entries69 N C := by
  classical
  have cap := countedSlots69 (keep69 N C) (split69 N C)
    (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
    (fun _ h=>(Finset.mem_sdiff.mp h).1) (fun _ h=>(Finset.mem_filter.mp h).1) (by
      intro j hj w hw h
      rcases of_decide_eq_true h with s|⟨low,idx⟩
      · exact Or.inl s
      · exact Or.inr (Finset.mem_image.mpr ⟨w-N,idx,by omega⟩))
  have splitBound := splitStrict44 sh back pos
  omega

theorem mixedStrict44 {N:Nat} {C:Circuit} (sh:shapes69 C) (back:ReadsBack N C) (pos : 0<entries69 N C) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)).card<2*entries69 N C := by
  classical
  let P:=keep69 N C
  let R:=(roots69 N C P).filter (fun z=>slots69 N C P z≠0)
  let f:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∉pool69 N C P))
  let g:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
  have per (j:Nat) (hj:j∈P): f j≤g j := by
    apply List.countP_mono_left
    intro w hw out'
    have out:w∉pool69 N C P:=of_decide_eq_true out'
    apply decide_eq_true
    by_cases sp:w∈special N C
    · exact Or.inl sp
    · have color:=colorOuter69 back hj hw out
      have nle : N≤w:=by by_contra! h;rw [color_raw h sp] at color;contradiction
      have eq:N+(w-N)=w:=by omega
      have ji:=ordinary_index69 (keepSub69 hj)
      have wi:=back j ji w hw
      have ord:w-N∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [eq]⟩
      refine Or.inr ⟨nle,?_⟩
      by_contra ns
      have inside:w-N∈P:=Finset.mem_sdiff.mpr ⟨ord,ns⟩
      exact out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,inside,eq⟩))
  have lower (z:Nat) (hz:z∈R) : 1≤ slots69 N C P z := by
    have neq:slots69 N C P z≠0:=(Finset.mem_filter.mp hz).2
    omega
  change R.card<_
  calc
    R.card = ∑_z∈R,1 := by simp
    _ ≤ ∑z∈R,slots69 N C P z := Finset.sum_le_sum lower
    _ = ∑j∈P.filter (fun i=>owner69 N C P (N+i)∈R), f j :=
      Finset.sum_fiberwise_eq_sum_filter P R (fun j=>owner69 N C P (N+j)) f
    _ ≤ ∑j∈P,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)
    _ ≤ ∑j∈P,g j := Finset.sum_le_sum per
    _ < _ := entryStrict44 sh back pos

end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def shared44 (N : Nat) (C : Circuit) :=
  (Finset.range (N+C.size)).filter (fun w=>2≤reads69 C w)
def sharedG44 (N : Nat) (C : Circuit) :=
  (gates69 C).filter (fun j=>2≤reads69 C (N+j))
def marked44 (N : Nat) (C : Circuit) := ∑ w∈shared44 N C,reads69 C w
def lift44 (N : Nat) (C : Circuit) (w : Nat) :=
  if w<N ∨ w∈shared44 N C then w else w+C.size
def down44 (N : Nat) (C : Circuit) (w : Nat) :=
  if w<N+C.size then w else w-C.size
def exposed44 (N : Nat) (C : Circuit) (g : Gate) : Gate := ⟨g.op,g.inputs.map (lift44 N C)⟩
def splitC (N : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (exposed44 N C),C.output+C.size⟩

@[simp] theorem split_size {N : Nat} {C : Circuit} : (splitC N C).size=C.size := by
  simp [splitC,Circuit.size]
theorem project44 {N : Nat} {C : Circuit} (w : Nat) : down44 N C (lift44 N C w)=w := by
  unfold lift44 down44
  by_cases h : w<N ∨ w∈shared44 N C
  · rw [if_pos h,if_pos]; rcases h with h|h
    · omega
    · exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
  · rw [if_neg h,if_neg] <;> omega
theorem inj44 (N : Nat) (C : Circuit) : Function.Injective (lift44 N C) := by
  intro x y e; simpa only [project44] using congrArg (down44 N C) e
theorem at44 {N : Nat} {C : Circuit} {j : Nat} (h : j<C.size) :
    gateAt (splitC N C) j=exposed44 N C (gateAt C j) := by
  have a : j<C.gates.length := h
  simp [gateAt,splitC,List.getD_eq_getElem,a]
theorem shapes44 {N : Nat} {C : Circuit} (sh : shapes69 C) : shapes69 (splitC N C) := by
  intro g hg
  obtain ⟨old,mem,rfl⟩:=List.mem_map.mp hg
  simpa [exposed44] using sh old mem
theorem back44 {N : Nat} {C : Circuit} (back : ReadsBack N C) : ReadsBack (N+C.size) (splitC N C) := by
  intro j hj w hw
  have ji : j<C.size := by simpa [splitC,Circuit.size] using hj
  rw [at44 ji] at hw
  obtain ⟨x,hit,rfl⟩ := List.mem_map.mp hw
  have lt := back j ji x hit
  unfold lift44; split <;> omega
theorem op_count44 {N : Nat} {C : Circuit} (l : List Nat) (w : Nat) :
    (l.map (lift44 N C)).count (lift44 N C w)=l.count w := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases e : x=w
    · subst x; simp [List.count_cons,ih]
    · have ne : lift44 N C x≠lift44 N C w := fun h=>e (inj44 N C h)
      simp [List.count_cons,ih,ne,e]
theorem local44 {N : Nat} {C : Circuit} {T : Finset Nat} (sub : T⊆gates69 C) (w : Nat) :
    readsIn (splitC N C) T (lift44 N C w)=readsIn C T w := by
  apply Finset.sum_congr rfl
  intro j hj; rw [at44 (Finset.mem_range.mp (sub hj))]
  exact op_count44 _ _
theorem reads44 {N : Nat} {C : Circuit} (w : Nat) :
    reads69 (splitC N C) (lift44 N C w)=reads69 C w := by
  unfold reads69 gates69; rw [split_size]; exact local44 (fun _ h=>h) _
theorem absent44 {N : Nat} {C : Circuit} {w : Nat} (never : ∀x,lift44 N C x≠w) :
    reads69 (splitC N C) w=0 := by
  unfold reads69 readsIn gates69
  rw [split_size]
  apply Finset.sum_eq_zero
  intro j hj
  have ji : j<C.size := Finset.mem_range.mp hj
  rw [at44 ji]
  apply List.count_eq_zero.mpr
  intro hit
  obtain ⟨x,_,e⟩ := List.mem_map.mp hit
  exact never x e
theorem dead44 {N : Nat} {C : Circuit} {j : Nat} (hj : j∈sharedG44 N C) :
    reads69 (splitC N C) (N+C.size+j)=0 := by
  obtain ⟨bound,many⟩:=Finset.mem_filter.mp hj
  have ji : j<C.size := Finset.mem_range.mp bound
  have mem : N+j∈shared44 N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩
  apply absent44; intro x e
  have orig := congrArg (down44 N C) e
  rw [project44,down44,if_neg (by omega)] at orig
  have eq : x=N+j := by omega
  rw [eq,lift44,if_pos (Or.inr mem)] at e; omega
theorem gate_reads44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    reads69 (splitC N C) (N+C.size+j)=(if j∈sharedG44 N C then 0 else reads69 C (N+j)) := by
  by_cases g : j∈sharedG44 N C
  · rw [if_pos g]; exact dead44 g
  · rw [if_neg g]
    have h : N+j∉shared44 N C := fun mem=>g (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ji,(Finset.mem_filter.mp mem).2⟩)
    simpa [lift44,h,Nat.add_right_comm] using (reads44 (N:=N) (C:=C) (N+j))
theorem gate_one44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    reads69 (splitC N C) (N+C.size+j)≤1 := by
  rw [gate_reads44 ji]; split
  · omega
  · next h => by_contra! many; exact h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ji,many⟩)

theorem raw_reads44 {N : Nat} {C : Circuit} {w : Nat} (hw : w<N+C.size) :
    reads69 (splitC N C) w=(if w<N ∨ w∈shared44 N C then reads69 C w else 0) := by
  by_cases h : w<N ∨ w∈shared44 N C
  · simpa [lift44,h] using (reads44 (N:=N) (C:=C) w)
  · rw [if_neg h]
    apply absent44; intro x e
    have p:=congrArg (down44 N C) e
    rw [project44,down44,if_pos hw] at p
    subst x; rw [lift44,if_neg h] at e
    have ge : N≤w := by omega
    omega
theorem once44 (N : Nat) (C : Circuit) : once69 (N+C.size) (splitC N C)=once69 N C := by
  ext w
  constructor
  · intro mem
    obtain ⟨lt,one⟩ := Finset.mem_filter.mp mem
    have range:=Finset.mem_range.mp lt
    rw [raw_reads44 range] at one
    by_cases low : w<N
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr low,by simpa [low] using one⟩
    · by_cases shared : w∈shared44 N C
      · have many := (Finset.mem_filter.mp shared).2
        simp [low,shared] at one; omega
      · simp [low,shared] at one
  · intro mem
    obtain ⟨lt,one⟩ := Finset.mem_filter.mp mem
    have low:=Finset.mem_range.mp lt
    have wide : w<N+C.size:=by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr wide,by simpa [raw_reads44 wide,low] using one⟩
theorem neg44 (N : Nat) (C : Circuit) : neg69 (splitC N C)=neg69 C := by
  ext j
  simp only [neg69,gates69,split_size,Finset.mem_filter,Finset.mem_range]
  by_cases h : j<C.size
  · simp [h,at44 h,exposed44]
  · simp [h]
theorem flagged44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    N+C.size+j∈special (N+C.size) (splitC N C) ↔ j∈neg69 C := by
  constructor
  · intro m
    rcases Finset.mem_union.mp m with hi|hn
    · have l := gate_one44 (N:=N) ji; have b := (Finset.mem_filter.mp hi).2; omega
    · obtain ⟨k,hk,e⟩:=Finset.mem_image.mp hn
      have eq : k=j:=Nat.add_left_cancel e
      subst k; rwa [neg44] at hk
  · intro hn; apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j,by rwa [neg44],rfl⟩
theorem ord44 {N : Nat} {C : Circuit} {j : Nat} (ji : j<C.size) :
    j∈ordinary (N+C.size) (splitC N C) ↔ j∉neg69 C := by
  change (_∈(gates69 _).filter _) ↔ _
  simp [gates69,ji,flagged44 ji]
theorem special_wire44 {N : Nat} {C : Circuit} {w : Nat} (hw : w<N+C.size) :
    lift44 N C w∈special (N+C.size) (splitC N C) → w∈shared44 N C ∨ w∈(neg69 C).image (fun k=>N+k) := by
  intro h
  rcases Finset.mem_union.mp h with many|neg
  · have b : 2≤reads69 (splitC N C) (lift44 N C w):=(Finset.mem_filter.mp many).2
    rw [reads44] at b
    exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw,b⟩)
  · obtain ⟨j,hj,e⟩:=Finset.mem_image.mp neg
    rw [neg44] at hj
    have k:=congrArg (down44 N C) e
    change down44 N C (N+C.size+j)=down44 N C (lift44 N C w) at k
    rw [project44,down44,if_neg (by omega)] at k
    exact Or.inr (Finset.mem_image.mpr ⟨j,hj,by omega⟩)

end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
theorem entries44 {N : Nat} {C : Circuit} (back : ReadsBack N C) :
    entries69 (N+C.size) (splitC N C)≤ marked44 N C+(neg69 C).card := by
  classical
  let D:=splitC N C
  let O:=ordinary (N+C.size) D
  let S:=shared44 N C
  let I:=(neg69 C).image (fun k=>N+k) \ S
  let X:=S∪I
  have each (j : Nat) (hj : j∈O) :
      (gateAt D j).inputs.countP (fun w=>decide (w∈special (N+C.size) D)) ≤
        (gateAt C j).inputs.countP (fun x=>decide (x∈X)) := by
    have ji : j<C.size := by simpa only [D,split_size] using ordinary_index69 hj
    rw [show gateAt D j=exposed44 N C (gateAt C j) from at44 ji]
    change ((gateAt C j).inputs.map (lift44 N C)).countP _≤_
    rw [List.countP_map]
    apply List.countP_mono_left
    intro x hx use
    have low:=back j ji x hx
    have mark : lift44 N C x∈special (N+C.size) D:=of_decide_eq_true use
    rcases special_wire44 (by omega : x<N+C.size) mark with s|n
    · exact decide_eq_true (Finset.mem_union_left _ s)
    · apply decide_eq_true
      by_cases hit : x∈S
      · exact Finset.mem_union_left _ hit
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨n,hit⟩)
  have subO : O⊆gates69 C := by
    intro j hj
    have lt := ordinary_index69 hj
    exact Finset.mem_range.mpr (by simpa only [D,split_size] using lt)
  have mass : (∑ w∈I,reads69 C w)≤(neg69 C).card := by
    have per (w : Nat) (mem : w∈I) : reads69 C w≤1 := by
      obtain ⟨im,out⟩:=Finset.mem_sdiff.mp mem
      obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp im
      have ki : k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      by_contra! many; exact out (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩)
    have total:=Finset.sum_le_sum per
    simp only [Finset.sum_const,smul_eq_mul,mul_one] at total
    exact total.trans ((Finset.card_le_card Finset.sdiff_subset).trans Finset.card_image_le)
  have dis : Disjoint S I := Finset.disjoint_left.mpr (fun _ hw hx=>(Finset.mem_sdiff.mp hx).2 hw)
  calc
    _ ≤ ∑j∈O,(gateAt C j).inputs.countP (fun x=>decide (x∈X)) := Finset.sum_le_sum each
    _ ≤ ∑j∈gates69 C,(gateAt C j).inputs.countP (fun x=>decide (x∈X)) :=
      Finset.sum_le_sum_of_subset_of_nonneg subO (fun _ _ _=>Nat.zero_le _)
    _ = ∑w∈X,reads69 C w := by simp_rw [maskedCount69];exact Finset.sum_comm
    _ ≤ _ := by rw [Finset.sum_union dis]; exact Nat.add_le_add_left mass _

noncomputable def rootsPure (N : Nat) (C : Circuit) := (roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)
noncomputable def rootsMixed (N : Nat) (C : Circuit) := (roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)
noncomputable def correction (N : Nat) (C : Circuit) := if 0< marked44 N C+(neg69 C).card then 1 else 0
theorem mixed44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) :
    (rootsMixed (N+C.size) (splitC N C)).card+correction N C≤2*(marked44 N C+(neg69 C).card) := by
  classical
  have cap := entries44 back
  have old:=mixed_count69 (shapes44 sh) (back44 back)
  by_cases pos : 0<entries69 (N+C.size) (splitC N C)
  · have gain := mixedStrict44 (shapes44 sh) (back44 back) pos
    unfold rootsMixed correction; split <;> omega
  · unfold rootsMixed correction; split <;> omega

end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
noncomputable def places44 (N : Nat) (C : Circuit) :=
  insert (splitC N C).output
    (((sharedG44 N C).image (fun j=>N+C.size+j)) ∪
      ((neg69 C).image (fun j=>(gateAt (splitC N C) j).inputs.headD 0)))

theorem stop44 {N : Nat} {C : Circuit} (sh : shapes69 C) (last : C.output+1=N+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j))
    {z : Nat} (bounded : z<N+C.size+(splitC N C).size)
    (realRaw : z<N+C.size → 0<reads69 (splitC N C) z)
    (stopped : ∀j∈ordinary (N+C.size) (splitC N C),z∉(gateAt (splitC N C) j).inputs) :
    z∈places44 N C := by
  classical
  let D:=splitC N C
  by_cases read : 0<reads69 D z
  · have hit : ∃j∈gates69 D,z∈(gateAt D j).inputs := by
      by_contra! no
      have zero : reads69 D z=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
      omega
    obtain ⟨j,hj,pin⟩:=hit
    have ji : j<C.size := by simpa only [D,split_size] using Finset.mem_range.mp hj
    have neg : j∈neg69 C := by
      by_contra notNeg
      exact stopped j ((ord44 ji).mpr notNeg) pin
    have valid : j<D.gates.length := by simpa [D,splitC,Circuit.size] using ji
    have gm : gateAt D j∈D.gates := by rw [gateAt,List.getD_eq_getElem _ _ valid];exact List.getElem_mem valid
    have nn : j∈neg69 D := by simpa only [D,neg44] using neg
    have op : (gateAt D j).op=.not := (Finset.mem_filter.mp nn).2
    have len : (gateAt D j).inputs.length=1 := by
      rcases shapes44 sh _ gm with ⟨ops,_⟩|⟨_,one⟩
      · rw [op] at ops; simp at ops
      · exact one
    have head {l : List Nat} (len : l.length=1) (mem : z∈l) : l.headD 0=z := by
      cases l with
      | nil => simp at mem
      | cons a tail =>
        cases tail with
        | nil => simpa using (List.mem_singleton.mp mem).symm
        | cons b rest => simp at len
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,neg,head len pin⟩))
  · have lo : N+C.size≤z := by by_contra! h; exact read (realRaw h)
    let j:=z-(N+C.size)
    have ident : N+C.size+j=z := by dsimp [j]; omega
    have ji : j<C.size := by rw [split_size] at bounded; omega
    by_cases share : j∈sharedG44 N C
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,share,ident⟩))
    · have h:=gate_reads44 (N:=N) (C:=C) ji
      rw [if_neg share,ident] at h
      have endGate : j+1=C.size := by
        by_contra ne
        have pos:=live j ji (by omega)
        change ¬0<reads69 (splitC N C) z at read; omega
      have out : z=(splitC N C).output := by change z=C.output+C.size;omega
      exact Finset.mem_insert.mpr (Or.inl out)

theorem silent44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    {z : Nat} (hz : z∈rootsPure N C) :
    color69 N C z=false ∧ (∀j∈ordinary N C,z∉(gateAt C j).inputs) := by
  obtain ⟨rt,zero⟩:=Finset.mem_filter.mp hz
  have off : color69 N C z=false := by
    have slot:=fiberSlots69 back rt
    cases h:color69 N C z <;> simp_all
  obtain ⟨pool,sink,_,_⟩:=root_info69 keepSub69 back rt
  refine ⟨off,?_⟩
  intro j hj pin
  by_cases join : j∈split69 N C
  · have yes:=color_split_all sh join z pin
    rw [off] at yes;contradiction
  · exact sink (N+j) ⟨pool,j,Finset.mem_sdiff.mpr ⟨hj,join⟩,rfl,pin⟩

theorem places_card (N : Nat) (C : Circuit) : (places44 N C).card≤(sharedG44 N C).card+(neg69 C).card+1 :=
  (Finset.card_insert_le ..).trans (Nat.add_le_add_right
    ((Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)) 1)

theorem pure_subset44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    rootsPure (N+C.size) (splitC N C)⊆places44 N C := by
  intro z hz
  have b:=back44 back
  have rt:=(Finset.mem_filter.mp hz).1
  have pool:=(root_info69 keepSub69 b rt).1
  apply stop44 sh last live (pool_bound69 keepSub69 pool) _ (silent44 (shapes44 sh) b hz).2
  intro raw
  rcases Finset.mem_union.mp pool with src|gate
  · have one:=(Finset.mem_filter.mp src).2;omega
  · obtain ⟨j,_,e⟩:=Finset.mem_image.mp gate
    change N+C.size+j=z at e; omega

theorem pure44 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    (rootsPure (N+C.size) (splitC N C)).card+correction N C≤(sharedG44 N C).card+(neg69 C).card+1 := by
  classical
  let M:=N+C.size
  let D:=splitC N C
  let R:=rootsPure M D
  let A:=(Finset.range (M+D.size)).filter (fun w=>color69 M D w=true)
  have sub : R⊆places44 N C := pure_subset44 sh back last live
  have cap:=places_card N C
  by_cases active : 0< marked44 N C+(neg69 C).card
  case neg =>
    have c:=Finset.card_le_card sub
    simpa [correction,active] using c.trans cap
  have existsMark : A.Nonempty := by
    by_cases ne : (neg69 C).Nonempty
    · obtain ⟨j,hj⟩:=ne
      have ji : j<C.size := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have specialJ:=(flagged44 (N:=N) ji).mpr hj
      refine ⟨M+j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,color_special specialJ⟩⟩
      change M+j<M+(splitC N C).size;rw [split_size];omega
    · have full : (shared44 N C).Nonempty := by
        by_contra none
        have a:=Finset.not_nonempty_iff_eq_empty.mp ne
        have b:=Finset.not_nonempty_iff_eq_empty.mp none
        simp [marked44,a,b] at active
      obtain ⟨w,hw⟩:=full
      have lo : w<M := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
      have many : 2≤reads69 D w := by
        change 2≤reads69 (splitC N C) w
        rw [raw_reads44 lo,if_pos (Or.inr hw)]
        exact (Finset.mem_filter.mp hw).2
      have wr : w<M+D.size := by omega
      have mark : w∈special M D := Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr wr,many⟩)
      exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr wr,color_special mark⟩⟩
  let z:=A.max' existsMark
  have mz : z∈A := Finset.max'_mem _ _
  obtain ⟨rz,on⟩:=Finset.mem_filter.mp mz
  have bounded : z<M+D.size:=Finset.mem_range.mp rz
  have noOrd : ∀j∈ordinary M D,z∉(gateAt D j).inputs := by
    intro j hj use
    have ji:=ordinary_index69 hj
    have lit:=(color_ordinary_iff (back44 back) hj).mpr ⟨z,use,on⟩
    have marked : M+j∈A:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),lit⟩
    have greatest : M+j≤z:=Finset.le_max' _ _ marked
    have prior : z<M+j:=back44 back j ji z use
    omega
  have raw (low : z<M) : 0<reads69 D z := by
    have flag : z∈special M D := by
      by_contra no
      have off:=color_raw low no
      change color69 M D z=true at on
      rw [off] at on;contradiction
    rcases Finset.mem_union.mp flag with many|gate
    · have h:=(Finset.mem_filter.mp many).2;omega
    · obtain ⟨j,_,eq⟩:=Finset.mem_image.mp gate
      change M+j=z at eq;omega
  have allocation : z∈places44 N C := stop44 sh last live bounded raw noOrd
  have separate : z∉R := by
    intro hz
    have off:=(silent44 (shapes44 sh) (back44 back) hz).1
    change color69 M D z=false at off
    change color69 M D z=true at on
    rw [off] at on;contradiction
  have enlargement:=Finset.card_le_card (Finset.insert_subset allocation sub)
  rw [Finset.card_insert_of_notMem separate] at enlargement
  simpa [correction,active] using enlargement.trans cap

end PEqualNP.Outside.L_meta_25646_aux.Cut

namespace PEqualNP.Outside.L_meta_25646_aux.Cut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped Classical
def tree44 (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ gates69 C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ reads69 C w=1 ∧ C.output≠w)

def up44 (N : Nat) (C : Circuit) (w : Nat) := if w<N then w else w+C.size
theorem up_order44 {N : Nat} {C : Circuit} {w v : Nat} : up44 N C w≤up44 N C v ↔ w≤v := by
  unfold up44; split <;> split <;> omega
theorem undo44 {N : Nat} {C : Circuit} (w : Nat) : down44 N C (up44 N C w)=w := by
  unfold up44 down44; split <;> split <;> omega
theorem raw_gate44 {N j : Nat} {C : Circuit} : up44 N C (N+j)=N+C.size+j := by
  unfold up44;rw [if_neg (by omega)];omega
theorem mapped44 {N : Nat} {C : Circuit} {S T : Finset Nat} (sub : S⊆Finset.range N) :
    (S∪T.image (fun k=>N+k)).image (up44 N C)=S∪T.image (fun k=>N+C.size+k) := by
  ext y
  constructor
  · intro h
    obtain ⟨w,mem,rfl⟩:=Finset.mem_image.mp h
    rcases Finset.mem_union.mp mem with r|g
    · have low:=Finset.mem_range.mp (sub r); rw [up44,if_pos low];exact Finset.mem_union_left _ r
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp g; rw [raw_gate44]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
  · intro h;rcases Finset.mem_union.mp h with r|g
    · exact Finset.mem_image.mpr ⟨y,Finset.mem_union_left _ r,if_pos (Finset.mem_range.mp (sub r))⟩
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp g
      exact Finset.mem_image.mpr ⟨N+j,Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj),raw_gate44⟩
theorem find_pin44 {C : Circuit} {T : Finset Nat} {w : Nat} (pos : 0<readsIn C T w) :
    ∃ j∈T,w∈(gateAt C j).inputs := by
  by_contra! no
  have zero : readsIn C T w=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
  omega

theorem projectTree44 {N : Nat} {C : Circuit} (back : ReadsBack N C) (size : 0<C.size)
    (last : C.output+1=N+C.size) {S E : Finset Nat} (sub : S⊆Finset.range N)
    (t : tree69 (N+C.size) (splitC N C) S E) : tree44 N C S (E.image (down44 N C)) := by
  classical
  let M:=N+C.size
  let D:=splitC N C
  obtain ⟨T,z,info⟩:=t
  dsimp only at info
  obtain ⟨ordinary,root,_,ports,gates,inside⟩:=info
  let W:=S∪T.image (fun k=>N+k)
  let V:=S∪T.image (fun k=>M+k)
  have idx : T⊆gates69 C := fun j hj => by
    have g:=ordinary_index69 (ordinary hj)
    exact Finset.mem_range.mpr (by simpa only [split_size] using g)
  have mapping : W.image (up44 N C)=V := mapped44 sub
  have phys {w : Nat} (mem : w∈W) : up44 N C w∈V := mapping ▸ Finset.mem_image_of_mem _ mem
  have pre {v : Nat} (mem : v∈V) : ∃w∈W,up44 N C w=v := Finset.mem_image.mp (mapping.symm ▸ mem)
  obtain ⟨r,hr,hrz⟩:=pre root
  have maxRoot : ∀w∈V,w≤z := by
    let v:=V.max' ⟨z,root⟩
    have mv : v∈V := Finset.max'_mem _ _
    have top (w : Nat) (hw : w∈V) : w≤v := Finset.le_max' _ _ hw
    have equals : v=z := by
      by_contra ne
      have pc : readsIn D T v=1 := (inside v mv ne).1
      obtain ⟨j,hj,use⟩:=find_pin44 (by omega : 0<readsIn D T v)
      have prior : v<M+j := back44 back j (ordinary_index69 (ordinary hj)) v use
      have limit:=top (M+j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
      omega
    intro w hw; exact (top w hw).trans_eq equals
  have oldBound {j w : Nat} (hj : j∈T) (pin : w∈(gateAt C j).inputs) : w<r := by
    have above:=maxRoot (M+j) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
    rw [←hrz,show M+j=up44 N C (N+j) from raw_gate44.symm] at above
    exact (back j (Finset.mem_range.mp (idx hj)) w pin).trans_le (up_order44.mp above)
  have entryPin {v : Nat} (one : readsIn D T v=1) : lift44 N C (down44 N C v)=v ∧ down44 N C v<r := by
    obtain ⟨j,hj,pin⟩:=find_pin44 (by omega : 0<readsIn D T v)
    have e : gateAt D j=exposed44 N C (gateAt C j) := at44 (Finset.mem_range.mp (idx hj))
    rw [e] at pin
    obtain ⟨w,use,rfl⟩:=List.mem_map.mp pin
    exact ⟨by rw [project44],by rw [project44];exact oldBound hj use⟩
  have coincide {w : Nat} (hw : w∈W) (diff : w≠r) : lift44 N C w=up44 N C w := by
    have ne : up44 N C w≠z := by intro eq;exact diff (by simpa only [undo44] using congrArg (down44 N C) (eq.trans hrz.symm))
    have on:=(inside _ (phys hw) ne).1
    have hit:=(entryPin on).1
    rwa [undo44] at hit
  refine ⟨T,r,idx,hr,?_,?_,?_,?_⟩
  · exact Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (fun pin=>(Nat.lt_irrefl r) (oldBound hj pin)))
  · intro b hb;obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hb
    obtain ⟨out,_,one⟩:=ports v hv
    obtain ⟨eq,lt⟩:=entryPin one
    refine ⟨?_,lt,?_⟩
    · intro hw
      have u:=coincide hw (Nat.ne_of_lt lt)
      exact out ((eq.symm.trans u).symm ▸ phys hw)
    · rw [←local44 (N:=N) idx,eq];exact one
  · intro j hj
    obtain ⟨op,len,pins⟩:=gates j hj
    have e : gateAt (splitC N C) j=exposed44 N C (gateAt C j) := at44 (Finset.mem_range.mp (idx hj))
    rw [e] at op len pins
    refine ⟨op,by simpa [exposed44] using len,?_⟩
    intro w use
    have choices:=pins (lift44 N C w) (List.mem_map.mpr ⟨w,use,rfl⟩)
    rcases choices with isWire|port
    · obtain ⟨a,ha,eq⟩:=pre isWire
      have same:=congrArg (down44 N C) eq
      rw [undo44,project44] at same
      exact Or.inl (same ▸ ha)
    · exact Or.inr (Finset.mem_image.mpr ⟨_,port,project44 w⟩)
  · intro w hw diff
    have eq:=coincide hw diff
    have ne : up44 N C w≠z := fun h=>diff (by simpa only [undo44] using congrArg (down44 N C) (h.trans hrz.symm))
    obtain ⟨one,all,other⟩:=inside _ (phys hw) ne
    rw [←eq] at one all
    refine ⟨(local44 idx w).symm.trans one,(reads44 w).symm.trans all,?_⟩
    intro o;apply other
    change C.output+C.size=up44 N C w
    rw [←o,up44,if_neg (by omega)]

end PEqualNP.Outside.L_meta_25646_aux.Cut
namespace PEqualNP.Outside.L_meta_25646_aux
open PEqualNP.Outside.L_meta_25646_aux.Cut in
theorem provedCut : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
  let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
  let markedReads := ∑ w ∈ shared, reads w
  let once := (Finset.range n).filter (fun w => reads w = 1)
  let tree := fun (S E : Finset ℕ) => ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
    region ⊆ gates ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w)
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  0 < C.size → C.output + 1 = n + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads (n + j)) →
  ∃ (pure chains : List (Finset ℕ)) (markedComponents : ℕ),
    pure.length + markedComponents ≤ sharedGates.card + neg.card + 1 ∧
    chains.length + markedComponents ≤ 2 * (markedReads + neg.card) ∧
    (0 < markedReads + neg.card → 0 < markedComponents) ∧
    (pure ++ chains).Pairwise (fun A B => Disjoint A B) ∧
    (pure ++ chains).toFinset.biUnion (fun S => S) = once ∧
    (∀ S ∈ pure, S.Nonempty ∧ tree S ∅) ∧
    (∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, tree S {b}) := by
  intro N C
  dsimp only
  intro sh back size last live
  classical
  let M:=N+C.size
  let D:=splitC N C
  have shape : shapes69 D:=shapes44 sh
  have earlier : PEqualNP.MetaComplexity.NestedCover.ReadsBack M D:=back44 back
  have lastD : D.output+1=M+D.size := by
    change C.output+C.size+1=N+C.size+(splitC N C).size
    rw [split_size];omega

  let P:=keep69 M D
  let roots:=roots69 M D P
  let Q:=roots.filter (fun z=>slots69 M D P z=0)
  let mixedRoots:=roots.filter (fun z=>slots69 M D P z≠0)
  let leaf:=src69 M D P
  let qr:=Q.toList
  let mr:=mixedRoots.toList
  have qmem (z:Nat) : z∈qr ↔ z∈roots ∧ slots69 M D P z=0 := by simp [qr,Q]
  have mmem (z:Nat) : z∈mr ↔ z∈roots ∧ slots69 M D P z≠0 := by simp [mr,mixedRoots]
  have covered (z:Nat) : z∈qr++mr ↔ z∈roots := by
    rw [List.mem_append,qmem,mmem];tauto
  have nd : (qr++mr).Nodup := by
    refine List.nodup_append.mpr ⟨Q.nodup_toList,mixedRoots.nodup_toList,?_⟩
    intro x hx y hy e;subst y;exact (mmem x|>.mp hy).2 ((qmem x|>.mp hx).2)
  have fiber {w z:Nat}: w∈leaf z ↔ w∈once69 M D ∧ owner69 M D P w=z := Finset.mem_filter
  have facts {z:Nat} (hz:z∈roots) : (leaf z).Nonempty ∧
      tree69 M D (leaf z) (outside69 M D P z) := by
    have count:=fiberSlots69 earlier hz
    have le : slots69 M D P z≤1 := by rw [count];split <;> decide
    exact ⟨(root_info69 keepSub69 earlier hz).2.2.2,subtree69 keepSub69 earlier shape lastD hz le⟩
  have raw (z : Nat) : leaf z⊆Finset.range N := by
    intro w hw
    have once : w∈once69 M D := (fiber.mp hw).1
    rw [show once69 M D=once69 N C from once44 N C] at once
    exact (Finset.mem_filter.mp once).1
  refine ⟨qr.map leaf,mr.map leaf,correction N C,?_,?_,?_,?_,?_,?_,?_⟩
  · change (Q.toList.map leaf).length+correction N C≤(sharedG44 N C).card+(neg69 C).card+1
    rw [List.length_map,Finset.length_toList]; exact pure44 sh back last live
  · change (mixedRoots.toList.map leaf).length+correction N C≤2*(marked44 N C+(neg69 C).card)
    rw [List.length_map,Finset.length_toList]; exact mixed44 sh back
  · intro pos
    change 0< marked44 N C+(neg69 C).card at pos
    simp [correction,pos]
  · rw [←List.map_append,List.pairwise_map]
    apply nd.imp
    intro a b diff
    apply Finset.disjoint_left.mpr
    intro w ha hb;exact diff ((fiber.mp ha).2.symm.trans (fiber.mp hb).2)
  · change ((qr.map leaf)++(mr.map leaf)).toFinset.biUnion id=once69 N C
    rw [←once44 N C,←List.map_append]
    ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨_,⟨z,_,rfl⟩,hit⟩;exact (fiber.mp hit).1
    · intro raw
      let z:=owner69 M D P w
      have root:z∈roots:=Finset.mem_image_of_mem _ raw
      exact ⟨leaf z,⟨z,(covered z).mpr root,rfl⟩,fiber.mpr ⟨raw,rfl⟩⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,zero⟩:=(qmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    rw [outside_empty69.mpr zero] at tree
    refine ⟨ne,?_⟩
    change tree44 N C (leaf z) ∅
    simpa only [Finset.image_empty] using projectTree44 back size last (raw z) tree
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,nz⟩:=(mmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    have card : (outside69 M D P z).card=1 := by
      have cap:=outside_card69 (N:=M) (C:=D) (P:=P) (z:=z)
      have count:=fiberSlots69 earlier rt
      have nonempty : (outside69 M D P z).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (fun h=>nz (outside_empty69.mp h))
      have pos:=Finset.card_pos.mpr nonempty
      change slots69 M D P z=_ at count
      split at count <;> omega
    obtain ⟨b,eq⟩:=Finset.card_eq_one.mp card
    rw [eq] at tree
    refine ⟨ne,down44 N C b,?_⟩
    change tree44 N C (leaf z) {down44 N C b}
    simpa only [Finset.image_singleton] using projectTree44 back size last (raw z) tree

end PEqualNP.Outside.L_meta_25646_aux

open PEqualNP.Outside.L_meta_25646_aux in
theorem PEqualNP.Outside.L_meta_25646 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let nbrR := fun (sourceRow : Fin n) => Finset.univ.filter (fun destCol : Fin m => G sourceRow destCol = false)
  let nbrC := fun (sourceCol : Fin m) => Finset.univ.filter (fun destRow : Fin n => G destRow sourceCol = false)
  (∀ a, 2 ≤ (nbrR a).card) → (∀ c, 2 ≤ (nbrC c).card) →
  (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.Represents.Represents G C →
  11 * (n + m) ≤ 10 * C.size + 16 ∧
  (17 ≤ n + m → 11 * (n + m) ≤ 10 * C.size + 12) ∧
  ((∀ a, 3 ≤ (nbrR a).card) → (∀ c, 3 ≤ (nbrC c).card) →
    11 * (n + m) ≤ 10 * C.size + 8) := by
  intro n m G C
  exact refined provedCut G C

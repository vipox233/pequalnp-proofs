import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25689_aux.Normalize
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

end PEqualNP.Outside.L_meta_25689_aux.Normalize

namespace PEqualNP.Outside.L_meta_25689_aux.Normalize
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

end PEqualNP.Outside.L_meta_25689_aux.Normalize

namespace PEqualNP.Outside.L_meta_25689_aux.Normalize
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

end PEqualNP.Outside.L_meta_25689_aux.Normalize

namespace PEqualNP.Outside.L_meta_25689_aux.Normalize
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

end PEqualNP.Outside.L_meta_25689_aux.Normalize

namespace PEqualNP.Outside.L_meta_25689_aux.Normalize

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

end PEqualNP.Outside.L_meta_25689_aux.Normalize

namespace PEqualNP.Outside.L_meta_25689_aux.Normalize
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

end PEqualNP.Outside.L_meta_25689_aux.Normalize

namespace PEqualNP.Outside.L_meta_25689_aux
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
end PEqualNP.Outside.L_meta_25689_aux

namespace PEqualNP.Outside.L_meta_25689_aux
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
end PEqualNP.Outside.L_meta_25689_aux

namespace PEqualNP.Outside.L_meta_25689_aux.OldParity
open PEqualNP PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

open PEqualNP.CircuitLowerBounds

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

open PEqualNP.CircuitLowerBounds

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega

theorem parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

theorem supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj

theorem exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

theorem three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount

theorem three_core (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (g0 : Gate) (h0 : gs[0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c) ∨
      ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1) = Stat.const c0 :=
    hrd (fixBit g0) 0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b 0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ 0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c

  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ 0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩

theorem stat_first (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b (n + 1) = (simplify g0.op n
      (g0.inputs.map fun a => (statAt n i b).getD a (Stat.const false))).2 := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  show (elim n ([] ++ g0 :: post) (statAt n i b, [])).1.getD (n + 1) (Stat.const false) = _
  rw [elim_split_getD n [] g0 post _ (n + 1) _ (by
    show n + 1 ≤ (statAt n i b).length + 0
    rw [statAt_length])]
  exact getD_snoc_len (statAt n i b) _ _ _ (statAt_length n i b)

theorem first_any (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1))
    (hshape : (g0.op = GateOp.not ∧ g0.inputs = [(i : ℕ)]) ∨
      ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs = [(i : ℕ), (i : ℕ)])) :
    ∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c := by
  intro c
  rcases hshape with ⟨hop, hin⟩ | ⟨hop | hop, hin⟩
  · refine ⟨!c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpNot]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpAnd]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpOr]

theorem single_reader (n : ℕ) (gs : List Gate) (o : ℕ) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i k : Fin (n + 1)) (hik : k ≠ i) (hop : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hin : g0.inputs = [(i : ℕ), (k : ℕ)]) (hoi : o ≠ i)
    (hno : ∀ p' g', gs[p']? = some g' → p' ≠ 0 → (i : ℕ) ∉ g'.inputs)
    (hdep : ∀ u : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false) : False := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
    intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno (q + 1) g (by simpa using hq) (by omega)
  let u : Fin (n + 1) → Bool := fun j => if j = k then fixBit g0 else false
  have huk : u k = fixBit g0 := by simp [u]
  have hu'k : Function.update u i (!u i) k = fixBit g0 := by
    rw [Function.update_of_ne hik]; exact huk
  apply hdep u
  show (wiresFrom post (List.ofFn (Function.update u i (!u i)) ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn (Function.update u i (!u i))).getD a false)])).getD
        o false
    = (wiresFrom post (List.ofFn u ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn u).getD a false)])).getD o false
  apply agree_except i post _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjl : j = n + 1
  · rw [hjl, getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hin]
    simp only [List.map_cons, List.map_nil, getD_ofFn, huk, hu'k]
    rcases hop with hop | hop
    · have hf : fixBit g0 = false := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
    · have hf : fixBit g0 = true := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
  · rw [getD_snoc_ne _ _ _ _ (by simpa using hjl), getD_snoc_ne _ _ _ _ (by simpa using hjl)]
    by_cases hlt : j < n + 1
    · have e1 : (List.ofFn (Function.update u i (!u i))).getD j false
          = Function.update u i (!u i) ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      have e2 : (List.ofFn u).getD j false = u ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      rw [e1, e2]
      exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem three_saved (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c) :
    ∃ (i : Fin (n + 1)) (b : Bool),
      (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    by_contra hns
    refine hdep i (fun _ => false) ?_
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
  have hoi : ∀ i : Fin (n + 1), o ≠ i :=
    fun i e => hout i false false (by rw [e]; exact stF_self n gs i false)
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := exists_reader (n + 1) 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        [] o (hoi 0) (hsupp 0)
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
      (by rw [hin]; exact List.mem_cons_self)
      (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inl ⟨hop, hin⟩)))
    exact ⟨⟨j, hj⟩, b, hb⟩
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
        (by rw [hin]; exact List.mem_cons_self)
        (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inr ⟨hop, hin⟩)))
      exact ⟨⟨j, hj⟩, b, hb⟩
    · by_cases hr : ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ j ∈ g'.inputs
      · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
          (by rw [hin]; exact List.mem_cons_self) (Or.inr hr)
        exact ⟨⟨j, hj⟩, b, hb⟩
      · exfalso
        exact single_reader n gs o g0 h0 ⟨j, hj⟩ ⟨k, hk⟩
          (fun e => hjk (congrArg Fin.val e).symm) hop hin (hoi ⟨j, hj⟩)
          (fun p' g' hp' hp0 hx => hr ⟨p', g', hp0, hp', hx⟩) (hdep ⟨j, hj⟩)

theorem par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this

theorem clean_step (n : ℕ) (c : Bool) (s : ℕ)
    (h : HasClean (n + 1 + 1) (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) s) :
    ∃ (c' : Bool) (s' : ℕ), s' + 3 ≤ s ∧
      HasClean (n + 1) (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) c') s' := by
  obtain ⟨gs, o, hcl, hsz, hev⟩ := h
  have hev' : ∀ x : Fin (n + 1 + 1) → Bool,
      (wiresFrom gs (List.ofFn x)).getD o false = xor (par (n + 1 + 1) x) c := hev
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have hinv : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      Inv (n + 1) (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.insertNth i b y : Fin (n + 1 + 1) → Bool)))
        (elim (n + 1) gs (statAt (n + 1) i b, [])) :=
    fun i b y => inv_elim (n + 1) _ (by simp) gs _ _ hok (inv_at (n + 1) i b y)
  have hval : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      (stF (n + 1) gs i b o).val (wiresFrom (elim (n + 1) gs (statAt (n + 1) i b, [])).2
        (List.ofFn y)) = xor (par (n + 1) y) (xor b c) := by
    intro i b y
    have := ((hinv i b y).2 o).2
    rw [hev', par_insertNth, Bool.xor_assoc] at this
    exact this
  have hout : ∀ (i : Fin (n + 1 + 1)) (b c' : Bool), stF (n + 1) gs i b o ≠ Stat.const c' := by
    intro i b c' hst
    have h1 := hval i b (Fin.snoc (fun _ => false) false)
    have h2 := hval i b (Fin.snoc (fun _ => false) true)
    rw [hst] at h1 h2
    have e := h1.symm.trans h2
    rw [par_snoc, par_snoc] at e
    revert e
    cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
  have hdep : ∀ (i : Fin (n + 1 + 1)) (u : Fin (n + 1 + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false := by
    intro i u
    rw [hev', hev', par_flip]
    cases par (n + 1 + 1) u <;> cases c <;> simp
  obtain ⟨i, b, hb⟩ := three_saved (n + 1) gs hcl o hdep hout
  cases hst : stF (n + 1) gs i b o with
  | const c' => exact absurd hst (hout i b c')
  | wire j =>
    refine ⟨xor b c, (elim (n + 1) gs (statAt (n + 1) i b, [])).2.length, by omega,
      (elim (n + 1) gs (statAt (n + 1) i b, [])).2, j, ?_, le_refl _, ?_⟩
    · exact clean_elim (n + 1) (List.ofFn fun _ : Fin (n + 1) => false) (by simp) gs _ _ hok
        (inv_at (n + 1) i b _) (by intro p g hp; simp at hp)
    · intro y
      have := hval i b y
      rw [hst] at this
      exact this

theorem par_lower3 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    obtain ⟨c', s', hs, h'⟩ := clean_step n c s h
    have := ih c' s' h'
    omega

theorem parity_lower3 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    3 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower3 n false s (clean_of (n + 1) _ s hnc h')
    omega

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Stat.wire k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Stat.const c) :
    (simplify g.op t (g.inputs.map F)).2 = Stat.wire t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpOr, hF, hF']

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Stat.const c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Stat.wire q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

theorem st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Stat.const c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Stat.const c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'

theorem four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount

def Red (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (i : Fin (n + 1)) (b : Bool) (gs' : List Gate) (o' : ℕ), CleanL n gs' ∧
    gs'.length + 4 ≤ gs.length ∧ ∀ y : Fin n → Bool, vl gs' y o' = vl gs (ins i b y) o

structure Min (n : ℕ) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL (n + 1) gs
  hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
    vl gs (Function.update u i (!u i)) o ≠ vl gs u o
  hnc : ∀ (i : Fin (n + 1)) (b : Bool), ∃ y y' : Fin n → Bool,
    vl gs (ins i b y) o ≠ vl gs (ins i b y') o
  m1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = c
  m2 : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
    ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = vl gs u j
  nored : ¬ Red n gs o

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

theorem Min.out (M : Min n gs o) (i : Fin (n + 1)) (b c : Bool) :
    stF n gs i b o ≠ Stat.const c := by
  intro h
  obtain ⟨y, y', hne⟩ := M.hnc i b
  exact hne ((st_val_const n gs M.hcl i b o c h y).trans
    (st_val_const n gs M.hcl i b o c h y').symm)

theorem Min.pass (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) :
    ∃ j, CleanL n (passG n gs i b) ∧
      ∀ y : Fin n → Bool, vl (passG n gs i b) y j = vl gs (ins i b y) o := by
  cases hst : stF n gs i b o with
  | const c => exact absurd hst (M.out i b c)
  | wire j =>
    refine ⟨j, ?_, fun y => (st_val_wire n gs M.hcl i b o j hst y).symm⟩
    exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (fun g hg => (clean_nok _ gs M.hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)

theorem Min.nf4 (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    False := by
  obtain ⟨j, hc, he⟩ := M.pass i b
  exact M.nored ⟨i, b, _, j, hc,
    four_count n gs M.hcl i b p1 p2 p3 p4 h12 h13 h14 h23 h24 h34 h1 h2 h3 h4, he⟩

theorem Min.ndup (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2)
    (h3 : RC n gs i b p3) (p j q k : ℕ) (hq : stF n gs i b p = Stat.wire q) (hnq : n ≤ q)
    (hk : stF n gs i b j = Stat.wire k) (hkq : k < q)
    (heq : ∀ y : Fin n → Bool, vl gs (ins i b y) p = vl gs (ins i b y) j) : False := by
  obtain ⟨jo, hc, he⟩ := M.pass i b
  have h3c : (passG n gs i b).length + 3 ≤ gs.length :=
    three_count n gs M.hcl i b p1 p2 p3 h12 h13 h23 h1 h2 h3
  have hqv : q < n + (passG n gs i b).length := by
    have h := ((inv_stF n gs M.hcl i b (fun _ => false)).2 p).1
    rw [show (elim n gs (statAt n i b, [])).1.getD p (Stat.const false) = Stat.wire q from hq]
      at h
    exact h
  have heq1 : ∀ y : Fin n → Bool,
      vl (passG n gs i b) y (n + (q - n)) = vl (passG n gs i b) y k := by
    intro y
    rw [show n + (q - n) = q by omega, ← st_val_wire n gs M.hcl i b p q hq y,
      ← st_val_wire n gs M.hcl i b j k hk y]
    exact heq y
  obtain ⟨y, y', hne⟩ := M.hnc i b
  obtain ⟨gs2, o2, hc2, hl2, he2⟩ := drop_alias n (passG n gs i b) hc jo (q - n) k (by omega)
    (by omega) heq1 ⟨y, y', by rw [he y, he y']; exact hne⟩
  exact M.nored ⟨i, b, gs2, o2, hc2, by omega, fun y => by rw [he2 y, he y]⟩

theorem Min.reader (M : Min n gs o) (i : Fin (n + 1)) (B : ℕ → Prop) (hi : B i) (ho : ¬ B o) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (n + 1 + p) ∧ ∃ a ∈ g.inputs, B a := by
  apply exists_reader (n + 1) i B hi gs o ho
  by_contra hns
  refine M.hdep i (fun _ => false) ?_
  exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ i := fun e => hns (e ▸ hk)
      simp [Function.update_of_ne this])

theorem Min.cb (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (B : ℕ → Prop) (hi : B i)
    (hB : ∀ a, B a → IsC n gs i b a) :
    ∃ h1 h2, h1 ≠ h2 ∧ ¬ B (n + 1 + h1) ∧ ¬ B (n + 1 + h2) ∧ RC n gs i b h1 ∧ RC n gs i b h2 := by
  have ho : ¬ B o := fun h => by
    obtain ⟨c, hc⟩ := hB o h
    exact M.out i b c hc
  obtain ⟨h1, g1, hg1, hB1, a1, ha1, hBa1⟩ := M.reader i B hi ho
  have r1 : RC n gs i b h1 := ⟨g1, hg1, a1, ha1, hB a1 hBa1⟩
  by_cases hex : ∃ h2 g2, h2 ≠ h1 ∧ gs[h2]? = some g2 ∧ ¬ B (n + 1 + h2) ∧ ∃ a ∈ g2.inputs, B a
  · obtain ⟨h2, g2, hne, hg2, hB2, a2, ha2, hBa2⟩ := hex
    exact ⟨h1, h2, Ne.symm hne, hB1, hB2, r1, ⟨g2, hg2, a2, ha2, hB a2 hBa2⟩⟩
  by_cases hc1 : IsC n gs i b (n + 1 + h1)
  · obtain ⟨h2, g2, hg2, hB2, a2, ha2, hBa2⟩ := M.reader i (fun a => B a ∨ a = n + 1 + h1)
      (Or.inl hi) (fun h => h.elim ho (fun e => by
        obtain ⟨c, hc⟩ := hc1
        exact M.out i b c (by rw [e]; exact hc)))
    have hB2' : ¬ (B (n + 1 + h2) ∨ n + 1 + h2 = n + 1 + h1) := hB2
    have hBa2' : B a2 ∨ a2 = n + 1 + h1 := hBa2
    refine ⟨h1, h2, fun e => hB2' (Or.inr (by rw [e])), hB1, fun h => hB2' (Or.inl h), r1,
      g2, hg2, a2, ha2, ?_⟩
    rcases hBa2' with h | h
    · exact hB a2 h
    · rw [h]; exact hc1
  · exfalso
    obtain ⟨c1, hc1'⟩ := hB a1 hBa1
    obtain ⟨hop, _, w, hw, hwn⟩ := st_shape n gs M.hcl i b h1 g1 hg1 a1 ha1 c1 hc1'
      (fun c' h => hc1 ⟨c', h⟩)
    have hBw : ¬ B w := fun h => by
      obtain ⟨c, hc⟩ := hB w h
      exact hwn c hc
    have hwlt : w < n + 1 + h1 := (M.hcl h1 g1 hg1).lt w hw
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    obtain ⟨u, hu⟩ := takes gs M.m1 w (by omega) (fixBit g1)
    apply M.hdep i u
    refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
    · intro j hj hBj
      rw [vl_input gs _ j hj, vl_input gs _ j hj]
      exact Function.update_of_ne
        (fun e => hBj (by rw [show j = (i : ℕ) from congrArg Fin.val e]; exact hi)) _ _
    · intro p g hp _ hBp hr hear
      obtain ⟨a, ha, hBa⟩ := hr
      have hp1 : p = h1 := by
        by_contra hne
        exact hex ⟨p, g, hne, hp, hBp, a, ha, hBa⟩
      rw [hp1] at hear ⊢
      rw [vl_abs gs M.hcl _ h1 g1 hg1 hop w hw (by rw [hear w hwlt hBw]; exact hu),
        vl_abs gs M.hcl u h1 g1 hg1 hop w hw hu]

theorem Min.one_const (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p q : ℕ) (hpq : p ≠ q)
    (gp gq : Gate) (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (cp : IsC n gs i b (n + 1 + p)) (cq : IsC n gs i b (n + 1 + q)) : False := by
  obtain ⟨h1, h2, h12, hB1, hB2, r1, r2⟩ := M.cb i b
    (fun a => a = (i : ℕ) ∨ a = n + 1 + p ∨ a = n + 1 + q) (Or.inl rfl) (by
      intro a ha
      rcases ha with e | e | e
      · rw [e]; exact ⟨b, stF_self n gs i b⟩
      · rw [e]; exact cp
      · rw [e]; exact cq)
  have hB1' : ¬ (n + 1 + h1 = (i : ℕ) ∨ n + 1 + h1 = n + 1 + p ∨ n + 1 + h1 = n + 1 + q) := hB1
  have hB2' : ¬ (n + 1 + h2 = (i : ℕ) ∨ n + 1 + h2 = n + 1 + p ∨ n + 1 + h2 = n + 1 + q) := hB2
  exact M.nf4 i b p q h1 h2 hpq (fun e => hB1' (Or.inr (Or.inl (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inl (by rw [e])))) (fun e => hB1' (Or.inr (Or.inr (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inr (by rw [e])))) h12
    (rc_of_const n gs M.hcl i b p gp hp cp) (rc_of_const n gs M.hcl i b q gq hq cq) r1 r2

theorem Min.reader_const (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hr : (i : ℕ) ∈ g.inputs) : IsC n gs i (fixBit g) (n + 1 + p) :=
  const_read n gs M.hcl i _ p g hp i hr (stF_self n gs i _)

theorem Min.no_not (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.not) (hr : (i : ℕ) ∈ g.inputs) : False := by
  have hin : g.inputs = [(i : ℕ)] := by
    rcases M.hcl p g hp with ⟨_, j, _, hin⟩ | ⟨h, _⟩
    · rw [hin] at hr
      have e : (i : ℕ) = j := by simpa using hr
      rw [hin, e]
    · rcases h with h | h <;> rw [hop] at h <;> cases h
  have hN : ∀ b, IsC n gs i b (n + 1 + p) := fun b =>
    st_allconst n gs M.hcl i b p g hp (fun a ha => by
      rw [hin] at ha
      have e : a = (i : ℕ) := by simpa using ha
      rw [e]; exact ⟨b, stF_self n gs i b⟩)
  have hNv : ∀ b, stF n gs i b (n + 1 + p) = Stat.const (!b) := by
    intro b
    obtain ⟨c, hc⟩ := hN b
    have h1 := st_val_const n gs M.hcl i b (n + 1 + p) c hc (fun _ => false)
    have h2 : vl gs (ins i b fun _ => false) (i : ℕ) = b := by
      rw [vl_input gs _ i i.isLt]; simp [ins]
    have h3 : c = !b := by
      rw [← h1, vl_gate gs M.hcl _ p g hp, hop, hin]
      simp [GateOp.eval, h2]
    rw [hc, h3]
  have ho : ¬ (o = (i : ℕ) ∨ o = n + 1 + p) := by
    intro h
    rcases h with e | e
    · exact M.out i false false (by rw [e]; exact stF_self n gs i false)
    · exact M.out i false _ (by rw [e]; exact hNv false)
  obtain ⟨q, gq, hq, hBq, a, ha, hBa⟩ :=
    M.reader i (fun a => a = (i : ℕ) ∨ a = n + 1 + p) (Or.inl rfl) ho
  have hBq' : ¬ (n + 1 + q = (i : ℕ) ∨ n + 1 + q = n + 1 + p) := hBq
  have hBa' : a = (i : ℕ) ∨ a = n + 1 + p := hBa
  have hpq : p ≠ q := fun e => hBq' (Or.inr (by rw [e]))
  have hcq : ∃ b, IsC n gs i b (n + 1 + q) := by
    rcases hBa' with e | e
    · exact ⟨fixBit gq, M.reader_const i q gq hq (e ▸ ha)⟩
    · refine ⟨!fixBit gq, const_read n gs M.hcl i _ q gq hq (n + 1 + p) (e ▸ ha) ?_⟩
      rw [hNv]; simp
  obtain ⟨b0, hb0⟩ := hcq
  exact M.one_const i b0 p q hpq g gq hp hq (hN b0) hb0

theorem Min.forced (M : Min n gs o) (X : Fin (n + 1)) (p q : ℕ) (gp : Gate)
    (hp : gs[p]? = some gp) (hXp : (X : ℕ) ∈ gp.inputs)
    (hR : ∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = p ∨ p' = q)
    (hqo : o ≠ n + 1 + q) (u : Fin (n + 1) → Bool)
    (hq : vl gs (Function.update u X (!u X)) (n + 1 + q) = vl gs u (n + 1 + q) ∨
      ∀ (p' : ℕ) (g' : Gate), gs[p']? = some g' → (n + 1 + q) ∉ g'.inputs) :
    vl gs u (n + 1 + p) = u X := by
  by_contra hne
  have hX : vl gs u X = u X := vl_input gs u X X.isLt
  have hX' : vl gs (Function.update u X (!u X)) X = !u X := by
    rw [vl_input gs _ X X.isLt]; simp
  have key : vl gs (Function.update u X (!u X)) (n + 1 + p) = vl gs u (n + 1 + p) := by
    rcases M.hcl p gp hp with ⟨hopn, _⟩ | ⟨hop, j, k, _, _, hin⟩
    · exact (M.no_not X p gp hp hopn hXp).elim
    · have e1 : ∀ v : Fin (n + 1) → Bool,
          vl gs v (n + 1 + p) = gp.op.eval [vl gs v j, vl gs v k] := by
        intro v
        rw [vl_gate gs M.hcl v p gp hp, hin]
        rfl
      rw [e1 u] at hne
      rw [e1 u, e1 (Function.update u X (!u X))]
      have hjk : (X : ℕ) = j ∨ (X : ℕ) = k := by rw [hin] at hXp; simpa using hXp
      rcases hjk with e | e
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) k = w'
        generalize vl gs u k = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) j = w'
        generalize vl gs u j = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
  apply M.hdep X u
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ) ∨ a = n + 1 + q) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ) ∨ j = n + 1 + q) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (Or.inl (congrArg Fin.val e))) _ _
  · intro p' g' hp' _ hB' hr hear
    have hB'' : ¬ (n + 1 + p' = (X : ℕ) ∨ n + 1 + p' = n + 1 + q) := hB'
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) ∨ a = n + 1 + q := hBa
    by_cases hx : (X : ℕ) ∈ g'.inputs
    · rcases hR p' g' hp' hx with e | e
      · rw [e]; exact key
      · exact absurd (Or.inr (by rw [e])) hB''
    · rcases hq with hq | hq
      · apply vl_congr gs M.hcl _ _ p' g' hp'
        intro a' ha'
        by_cases e1 : a' = n + 1 + q
        · rw [e1]; exact hq
        · exact hear a' ((M.hcl p' g' hp').lt a' ha')
            (fun hb => (hb : a' = (X : ℕ) ∨ a' = n + 1 + q).elim (fun e => hx (e ▸ ha')) e1)
      · rcases hBa' with e | e
        · exact absurd (e ▸ ha) hx
        · exact absurd (e ▸ ha) (hq p' g' hp')
  · exact fun (h : o = (X : ℕ) ∨ o = n + 1 + q) => h.elim
      (fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)) hqo

theorem Min.block2 (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z) (ho : ¬ B o)
    (u : Fin (n + 1) → Bool) (ha hb : ℕ) (ga gb : Gate) (hga : gs[ha]? = some ga)
    (hgb : gs[hb]? = some gb)
    (hout : ∀ p' g', gs[p']? = some g' → ¬ B (n + 1 + p') → (∃ a ∈ g'.inputs, B a) →
      p' = ha ∨ p' = hb)
    (hopa : ga.op = GateOp.and ∨ ga.op = GateOp.or) (w : ℕ) (hw : w ∈ ga.inputs) (hBw : ¬ B w)
    (hv : vl gs u w = fixBit ga)
    (hagree : ∀ a ∈ gb.inputs, B a → vl gs (Function.update u Z (!u Z)) a = vl gs u a) :
    False := by
  apply M.hdep Z u
  refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' _ hB' hr hear
    rcases hout p' g' hp' hB' hr with e | e
    · rw [e] at hear ⊢
      have hwlt : w < n + 1 + ha := (M.hcl ha ga hga).lt w hw
      rw [vl_abs gs M.hcl _ ha ga hga hopa w hw (by rw [hear w hwlt hBw]; exact hv),
        vl_abs gs M.hcl u ha ga hga hopa w hw hv]
    · rw [e] at hear ⊢
      apply vl_congr gs M.hcl _ _ hb gb hgb
      intro a haa
      by_cases hBa : B a
      · exact hagree a haa hBa
      · exact hear a ((M.hcl hb gb hgb).lt a haa) hBa

theorem Min.before (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z)
    (u : Fin (n + 1) → Bool) (w : ℕ) (hBw : ¬ B w)
    (hne : vl gs (Function.update u Z (!u Z)) w ≠ vl gs u w) :
    ∃ p' g', gs[p']? = some g' ∧ n + 1 + p' ≤ w ∧ ¬ B (n + 1 + p') ∧ ∃ a ∈ g'.inputs, B a := by
  by_contra hno
  apply hne
  refine agree_B gs M.hcl _ _ B (w + 1) ?_ ?_ w (by omega) hBw
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' hlt hB' hr _
    exact (hno ⟨p', g', hp', by omega, hB', hr⟩).elim

theorem Min.second (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs := by
  by_contra hno
  have hu : ∀ v : Fin (n + 1) → Bool, v Y = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun v hv => vl_abs gs M.hcl v pG gG hG hop Y hY (by rw [vl_input gs v Y Y.isLt]; exact hv)
  apply M.hdep X (fun _ => fixBit gG)
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ)) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ)) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (congrArg Fin.val e)) _ _
  · intro p g hp _ _ hr _
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) := hBa
    have hpG : p = pG := by
      by_contra hne
      exact hno ⟨p, g, hne, hp, hBa' ▸ ha⟩
    rw [hpG]
    rw [hu _ (by rw [Function.update_of_ne hXY.symm]), hu _ rfl]
  · exact fun (e : o = (X : ℕ)) => M.out X false false (by rw [e]; exact stF_self n gs X false)

theorem Min.side (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs ∧
      (∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) ∧
      IsC n gs X (!fixBit gG) (n + 1 + r) ∧ fixBit gr = !fixBit gG ∧
      (gr.op = GateOp.and ∨ gr.op = GateOp.or) ∧ (n + 1 + pG) ∉ gr.inputs := by
  have cG : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  obtain ⟨r, gr, hrG, hr, hXr⟩ := M.second X Y hXY pG gG hG hop hY
  have ncr : ¬ IsC n gs X (fixBit gG) (n + 1 + r) :=
    fun h => M.one_const X _ pG r (Ne.symm hrG) gG gr hG hr cG h
  have cr := M.reader_const X r gr hr hXr
  have hfr : fixBit gr = !fixBit gG := by
    by_contra hne
    apply ncr
    have e : fixBit gr = fixBit gG := by
      revert hne
      cases fixBit gr <;> cases fixBit gG <;> simp
    rw [← e]; exact cr
  have cr' : IsC n gs X (!fixBit gG) (n + 1 + r) := by rw [← hfr]; exact cr
  refine ⟨r, gr, hrG, hr, hXr, ?_, cr', hfr, ?_, ?_⟩
  · intro p' g' hp' hx
    by_contra hne
    have h1 : p' ≠ r := fun e => hne (Or.inl e)
    have h2 : p' ≠ pG := fun e => hne (Or.inr e)
    have cp := M.reader_const X p' g' hp' hx
    by_cases e : fixBit g' = fixBit gG
    · rw [e] at cp
      exact M.one_const X _ pG p' (Ne.symm h2) gG g' hG hp' cG cp
    · have e' : fixBit g' = !fixBit gG := by
        revert e
        cases fixBit g' <;> cases fixBit gG <;> simp
      rw [e'] at cp
      exact M.one_const X _ r p' (Ne.symm h1) gr g' hr hp' cr' cp
  · rcases M.hcl r gr hr with ⟨hopn, _⟩ | ⟨h, _⟩
    · exact (M.no_not X r gr hr hopn hXr).elim
    · exact h
  · intro hGr
    obtain ⟨c0, hc0⟩ := cG
    obtain ⟨_, _, w, hw, hwn⟩ := st_shape n gs M.hcl X (fixBit gG) r gr hr (n + 1 + pG) hGr c0 hc0
      (fun c' h => ncr ⟨c', h⟩)
    rcases two_inputs (M.hcl r gr hr) (X : ℕ) (n + 1 + pG) w hXr hGr
      (by have := X.isLt; omega) hw with e | e
    · exact hwn _ (by rw [e]; exact stF_self n gs X _)
    · exact hwn c0 (by rw [e]; exact hc0)

theorem Min.pair_false (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) : False := by
  have hXYn : (X : ℕ) ≠ (Y : ℕ) := fun e => hXY (Fin.ext e)
  obtain ⟨r, gr, hrG, hr, hXr, hRX, crX, hfr, hopr, hGr⟩ := M.side X Y hXY pG gG hG hop hX hY
  obtain ⟨r', gr', hr'G, hr', hYr', hRY, _, _, _, hGr'⟩ :=
    M.side Y X hXY.symm pG gG hG hop hY hX
  have cGX : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  have cGY : IsC n gs Y (fixBit gG) (n + 1 + pG) := M.reader_const Y pG gG hG hY
  have hoX : o ≠ (X : ℕ) := fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)
  have hoY : o ≠ (Y : ℕ) := fun e => M.out Y false false (by rw [e]; exact stF_self n gs Y false)
  have hoG : o ≠ n + 1 + pG := fun e => by
    have ⟨c, hc⟩ := cGX
    exact M.out X _ c (by rw [e]; exact hc)
  have hor : o ≠ n + 1 + r := fun e => by
    have ⟨c, hc⟩ := crX
    exact M.out X _ c (by rw [e]; exact hc)
  have hGv : ∀ (Z : Fin (n + 1)) (v : Fin (n + 1) → Bool), (Z : ℕ) ∈ gG.inputs →
      v Z = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun Z v hZ hv => vl_abs gs M.hcl v pG gG hG hop Z hZ (by rw [vl_input gs v Z Z.isLt]; exact hv)
  have hrX : ∀ v : Fin (n + 1) → Bool, v X = fixBit gr → vl gs v (n + 1 + r) = fixBit gr :=
    fun v hv => vl_abs gs M.hcl v r gr hr hopr X hXr (by rw [vl_input gs v X X.isLt]; exact hv)
  have hGin : ∀ w ∈ gG.inputs, w = (X : ℕ) ∨ w = (Y : ℕ) :=
    fun w hw => two_inputs (M.hcl pG gG hG) X Y w hX hY hXYn hw
  have fX : ∀ u : Fin (n + 1) → Bool, u Y = fixBit gG → vl gs u (n + 1 + r) = u X := fun u hu =>
    M.forced X r pG gr hr hXr hRX hoG u (Or.inl (by
      rw [hGv Y _ hY (by rw [Function.update_of_ne hXY.symm]; exact hu), hGv Y u hY hu]))
  have hex1 : ∃ (h1 : ℕ) (g1 : Gate), gs[h1]? = some g1 ∧ (n + 1 + pG) ∈ g1.inputs := by
    by_contra hno
    refine M.m2 r gr hr X (by have := X.isLt; omega) (fun u => ?_)
    rw [vl_input gs u X X.isLt]
    exact M.forced X r pG gr hr hXr hRX hoG u
      (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
  obtain ⟨h1, g1, hg1, hGh1⟩ := hex1
  have h1G : h1 ≠ pG := fun e => by
    have := (M.hcl h1 g1 hg1).lt _ hGh1
    omega
  have h1r : h1 ≠ r := fun e => hGr (gate_eq hg1 hr e ▸ hGh1)
  have h1r' : h1 ≠ r' := fun e => hGr' (gate_eq hg1 hr' e ▸ hGh1)
  by_cases hrr : r = r'
  swap
  · by_cases hrc : RC n gs Y (fixBit gG) r
    · exact M.nf4 Y (fixBit gG) pG r' h1 r (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm hrG)
        (Ne.symm h1r') (Ne.symm hrr) h1r ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩
        ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩ ⟨g1, hg1, _, hGh1, cGY⟩ hrc
    · obtain ⟨q, hnq, hq⟩ := st_fresh n gs M.hcl Y (fixBit gG) r gr hr
        (fun a ha c hc => hrc ⟨gr, hr, a, ha, c, hc⟩)
      obtain ⟨k, hk, hkX⟩ := st_other n gs Y (fixBit gG) X hXY
      refine M.ndup Y (fixBit gG) pG r' h1 (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm h1r')
        ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩ ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩
        ⟨g1, hg1, _, hGh1, cGY⟩ (n + 1 + r) X q k hq hnq hkX (by omega) (fun y => ?_)
      rw [vl_input gs _ X X.isLt]
      exact fX _ (by simp [ins])
  · have hRY' : ∀ p' g', gs[p']? = some g' → (Y : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG := by
      intro p' g' hp' hy
      rw [hrr]; exact hRY p' g' hp' hy
    have hex2 : ∃ (h2 : ℕ) (g2 : Gate), gs[h2]? = some g2 ∧ (n + 1 + r) ∈ g2.inputs := by
      by_contra hno
      refine M.m2 pG gG hG X (by have := X.isLt; omega) (fun u => ?_)
      rw [vl_input gs u X X.isLt]
      exact M.forced X pG r gG hG hX (fun p' g' hp' hx => (hRX p' g' hp' hx).symm) hor u
        (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
    obtain ⟨h2, g2, hg2, hrh2⟩ := hex2
    have hrG' : (n + 1 + r) ∉ gG.inputs := fun h => by
      rcases hGin _ h with e | e
      · have := X.isLt; omega
      · have := Y.isLt; omega
    have h2r : h2 ≠ r := fun e => by
      have := (M.hcl h2 g2 hg2).lt _ hrh2
      omega
    have h2G : h2 ≠ pG := fun e => hrG' (gate_eq hg2 hG e ▸ hrh2)
    have h1u : ∀ p' g', gs[p']? = some g' → (n + 1 + pG) ∈ g'.inputs → p' = h1 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      have e2 : p' ≠ r := fun e => hGr (gate_eq hp' hr e ▸ hin)
      exact M.nf4 X (fixBit gG) pG r h1 p' (Ne.symm hrG) (Ne.symm h1G) (Ne.symm e1)
        (Ne.symm h1r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g1, hg1, _, hGh1, cGX⟩ ⟨g', hp', _, hin, cGX⟩
    have h2u : ∀ p' g', gs[p']? = some g' → (n + 1 + r) ∈ g'.inputs → p' = h2 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => hrG' (gate_eq hp' hG e ▸ hin)
      have e2 : p' ≠ r := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      exact M.nf4 X (!fixBit gG) pG r h2 p' (Ne.symm hrG) (Ne.symm h2G) (Ne.symm e1)
        (Ne.symm h2r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g2, hg2, _, hrh2, crX⟩ ⟨g', hp', _, hin, crX⟩
    have n1X : ¬ IsC n gs X (fixBit gG) (n + 1 + h1) :=
      fun h => M.one_const X _ pG h1 (Ne.symm h1G) gG g1 hG hg1 cGX h
    have n2X : ¬ IsC n gs X (!fixBit gG) (n + 1 + h2) :=
      fun h => M.one_const X _ r h2 (Ne.symm h2r) gr g2 hr hg2 crX h
    have ⟨cg, hcg⟩ := cGX
    have ⟨cr, hcr⟩ := crX
    obtain ⟨hop1, hf1, w1, hw1, hw1n⟩ := st_shape n gs M.hcl X (fixBit gG) h1 g1 hg1 _ hGh1 cg hcg
      (fun c' h => n1X ⟨c', h⟩)
    obtain ⟨hop2, hf2, w2, hw2, hw2n⟩ := st_shape n gs M.hcl X (!fixBit gG) h2 g2 hg2 _ hrh2 cr
      hcr (fun c' h => n2X ⟨c', h⟩)
    have hcgv : cg = fixBit gG := by
      have h := st_val_const n gs M.hcl X (fixBit gG) (n + 1 + pG) cg hcg (fun _ => false)
      rw [hGv X _ hX (by simp [ins])] at h
      exact h.symm
    have hcrv : cr = fixBit gr := by
      have h := st_val_const n gs M.hcl X (!fixBit gG) (n + 1 + r) cr hcr (fun _ => false)
      rw [hrX _ (by simp [ins, hfr])] at h
      exact h.symm
    have f1 : fixBit g1 = !fixBit gG := by
      rw [hcgv] at hf1
      revert hf1
      cases fixBit g1 <;> cases fixBit gG <;> simp
    have f2 : fixBit g2 = fixBit gG := by
      rw [hcrv, hfr] at hf2
      revert hf2
      cases fixBit g2 <;> cases fixBit gG <;> simp
    have h12 : h1 ≠ h2 := fun e => by
      have e' : g1 = g2 := gate_eq hg1 hg2 e
      rw [e', f2] at f1
      revert f1
      cases fixBit gG <;> simp
    have hr1 : (n + 1 + r) ∉ g1.inputs := fun h => h12 (h2u h1 g1 hg1 h)
    have hG2 : (n + 1 + pG) ∉ g2.inputs := fun h => h12 (h1u h2 g2 hg2 h).symm
    have hX1 : (X : ℕ) ∉ g1.inputs := fun h => (hRX h1 g1 hg1 h).elim h1r h1G
    have hY1 : (Y : ℕ) ∉ g1.inputs := fun h => (hRY' h1 g1 hg1 h).elim h1r h1G
    have hX2 : (X : ℕ) ∉ g2.inputs := fun h => (hRX h2 g2 hg2 h).elim h2r h2G
    have hY2 : (Y : ℕ) ∉ g2.inputs := fun h => (hRY' h2 g2 hg2 h).elim h2r h2G
    have hBw1X : ¬ (w1 = (X : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw1Y : ¬ (w1 = (Y : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw2X : ¬ (w2 = (X : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hBw2Y : ¬ (w2 = (Y : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hout : ∀ (Z : Fin (n + 1)),
        (∀ p' g', gs[p']? = some g' → (Z : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) →
        ∀ p' g', gs[p']? = some g' →
          ¬ (n + 1 + p' = (Z : ℕ) ∨ n + 1 + p' = n + 1 + pG ∨ n + 1 + p' = n + 1 + r) →
          (∃ a ∈ g'.inputs, a = (Z : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) →
          p' = h1 ∨ p' = h2 := by
      intro Z hRZ p' g' hp' hB hr
      obtain ⟨a, ha, hBa⟩ := hr
      rcases hBa with e | e | e
      · exfalso
        rcases hRZ p' g' hp' (e ▸ ha) with e' | e'
        · exact hB (Or.inr (Or.inr (by rw [e'])))
        · exact hB (Or.inr (Or.inl (by rw [e'])))
      · exact Or.inl (h1u p' g' hp' (e ▸ ha))
      · exact Or.inr (h2u p' g' hp' (e ▸ ha))
    have hoBY : ¬ (o = (Y : ℕ) ∨ o = n + 1 + pG ∨ o = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hoY e
      · exact hoG e
      · exact hor e
    have A2 : ∀ u : Fin (n + 1) → Bool, vl gs u w2 = fixBit gG → u X = fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h2 h1 g2 g1 hg2 hg1 (fun p' g' hp' hB hr => (hout Y hRY' p' g' hp' hB hr).symm)
        hop2 w2 hw2 hBw2Y (by rw [f2]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY1
      · rw [e, hGv X _ hX (by rw [Function.update_of_ne hXY]; exact hx), hGv X u hX hx]
      · exact absurd (e ▸ ha) hr1
    have A4 : ∀ u : Fin (n + 1) → Bool, vl gs u w1 = !fixBit gG → u X = !fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h1 h2 g1 g2 hg1 hg2 (hout Y hRY') hop1 w1 hw1 hBw1Y (by rw [f1]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY2
      · exact absurd (e ▸ ha) hG2
      · rw [e, hrX _ (by rw [Function.update_of_ne hXY, hfr]; exact hx),
          hrX u (by rw [hfr]; exact hx)]
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    have hl2 : h2 < gs.length := (List.getElem?_eq_some_iff.1 hg2).1
    have hw1lt := (M.hcl h1 g1 hg1).lt w1 hw1
    have hw2lt := (M.hcl h2 g2 hg2).lt w2 hw2
    have lt12 : h1 < h2 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w2 (by omega) (fixBit gG)
      have hx : u X = !fixBit gG := by
        have h := A2 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w2 ≠ vl gs u w2 := fun e =>
        A2 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w2 hBw2X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    have lt21 : h2 < h1 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w1 (by omega) (!fixBit gG)
      have hx : u X = fixBit gG := by
        have h := A4 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w1 ≠ vl gs u w1 := fun e =>
        A4 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w1 hBw1X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    omega

theorem Min.contra (M : Min n gs o) : False := by
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases hgs : gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := M.reader 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        (fun (e : o = ((0 : Fin (n + 1)) : ℕ)) =>
          M.out 0 false false (by rw [e]; exact stF_self n gs 0 false))
      rw [hgs] at hp
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases M.hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact M.no_not ⟨j, by omega⟩ 0 g0 h0 hop (by rw [hin]; simp)
  · by_cases hjk : j = k
    · refine M.m2 0 g0 h0 j (by omega) (fun u => ?_)
      rw [vl_gate gs M.hcl u 0 g0 h0, hin, hjk]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
    · exact M.pair_false ⟨j, by omega⟩ ⟨k, by omega⟩ (fun e => hjk (congrArg Fin.val e)) 0 g0 h0
        hop (by rw [hin]; simp) (by rw [hin]; simp)

end

theorem par_lower4 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 4 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    classical
    have hex : ∃ t, HasClean (n + 1 + 1)
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) t := ⟨s, h⟩
    obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
    have hfs : Nat.find hex ≤ s := Nat.find_min' hex h
    have hev' : ∀ x : Fin (n + 1 + 1) → Bool, vl gs x o = xor (par (n + 1 + 1) x) c := hev
    have hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL (n + 1 + 1) gs' →
        (∀ x : Fin (n + 1 + 1) → Bool, vl gs' x o' = xor (par (n + 1 + 1) x) c) →
        gs.length ≤ gs'.length := by
      intro gs' o' hc' he'
      by_contra hlt
      exact Nat.find_min hex (m := gs'.length) (by omega) ⟨gs', o', hc', le_refl _, he'⟩
    suffices 4 * (n + 1) ≤ gs.length by omega
    by_contra hsmall
    have hncf : ∃ y y' : Fin (n + 1 + 1) → Bool, vl gs y o ≠ vl gs y' o := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      rw [hev', hev', par_snoc, par_snoc]
      cases par (n + 1) (fun _ => false) <;> cases c <;> simp
    have M : Min (n + 1) gs o :=
      { hcl := hcl
        hdep := by
          intro i u
          rw [hev', hev', par_flip]
          cases par (n + 1 + 1) u <;> cases c <;> simp
        hnc := by
          intro i b
          refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
          rw [hev', hev', par_insertNth, par_insertNth, par_snoc, par_snoc]
          cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
        m1 := by
          intro p g hp c' hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ := drop_const (n + 1 + 1) gs hcl o p c' hpl hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        m2 := by
          intro p g hp j hj hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ :=
            drop_alias (n + 1 + 1) gs hcl o p j hpl hj hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        nored := by
          rintro ⟨i, b, gs', o', hc', hl', he'⟩
          have h' : HasClean (n + 1)
              (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c)) gs'.length :=
            ⟨gs', o', hc', le_refl _, fun y => by
              show vl gs' y o' = _
              rw [he' y, hev', par_insertNth, Bool.xor_assoc]⟩
          have := ih _ _ h'
          omega }
    exact M.contra

theorem parity_lower4 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    4 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower4 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.Outside.L_meta_25689_aux.OldParity
namespace PEqualNP.Outside.L_meta_25689_aux.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

def applySign (s v : Bool) := if s then !v else v

noncomputable def trace (N : Nat) (C : Circuit) (w : Nat) : Nat × Bool :=
  if N≤w ∧ w-N<C.size then
    let g:=gateAt C (w-N)
    let v:=g.inputs.headD w
    if g.op=.not then
      if h : v<w then
        let a:=trace N C v
        (a.1,!a.2)
      else (w,false)
    else (w,false)
  else (w,false)
termination_by w
decreasing_by exact h

theorem low {N : Nat} (C : Circuit) {w : Nat} (h : w<N) : trace N C w=(w,false) := by
  rw [trace];simp [show ¬N≤w by omega]

theorem binary {N : Nat} {C : Circuit} {j : Nat} (h : j<C.size) (op : (gateAt C j).op≠.not) :
    trace N C (N+j)=(N+j,false) := by
  rw [trace];simp [h,op]

theorem unary {N : Nat} {C : Circuit} {j v : Nat} (h : j<C.size) (op : (gateAt C j).op=.not)
    (pin : (gateAt C j).inputs=[v]) (lt : v<N+j) :
    trace N C (N+j)=((trace N C v).1,!(trace N C v).2) := by
  rw [trace];simp [h,op,pin,lt]

theorem below (N : Nat) (C : Circuit) (w : Nat) : (trace N C w).1≤w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [trace]
    split <;> dsimp
    · split
      · split
        · rename_i small
          exact (ih _ small).trans (Nat.le_of_lt small)
        · rfl
      · rfl
    · rfl

theorem opAt {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (j : Nat) (h : j<C.size) :
    ((gateAt C j).op=.not ∧ ∃v,(gateAt C j).inputs=[v]) ∨
    (((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧ ∃a b,a≠b ∧ (gateAt C j).inputs=[a,b]) := by
  have mem : gateAt C j∈C.gates:=by rw [show gateAt C j=C.gates[j] from List.getD_eq_getElem _ _ h];exact List.getElem_mem h
  exact (good _ mem).1

theorem value {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (x : List Bool) (len : x.length=N) (w : Nat) (ok : w<N+C.size) :
    let V:=fun i=>(run C.gates x).getD i false
    V w=applySign (trace N C w).2 (V (trace N C w).1) := by
  dsimp only
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<N
    · rw [low C raw];rfl
    let j:=w-N
    have eq : N+j=w:=Nat.add_sub_of_le (by omega)
    have idx : j<C.size:=by dsimp [j];omega
    rcases opAt (N:=N) good j idx with ⟨op,v,pin⟩|⟨op,_⟩
    · have lt:=back j idx v (by simp [pin])
      rw [←eq,unary idx op pin lt,gv N C back x len j idx]
      have hv:=ih v (by omega) (by omega)
      cases s : (trace N C v).2 <;> simp [op,pin,GateOp.eval,applySign,s] at hv ⊢ <;> simp [hv]
    · have ne : (gateAt C j).op≠.not:=by rcases op with e|e <;> simp [e]
      rw [←eq,binary idx ne];rfl

theorem roots {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (w : Nat) (ok : w<N+C.size) : (trace N C w).1<N ∨
    ∃ j<C.size,(gateAt C j).op≠.not ∧ (trace N C w).1=N+j := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<N
    · exact Or.inl ((below N C w).trans_lt raw)
    let j:=w-N
    have eq : N+j=w:=Nat.add_sub_of_le (by omega)
    have idx : j<C.size:=by dsimp [j];omega
    rcases opAt (N:=N) good j idx with ⟨op,v,pin⟩|⟨op,_⟩
    · have lt:=back j idx v (by simp [pin])
      rw [←eq,unary idx op pin lt]
      exact ih v (by omega) (by omega)
    · have ne : (gateAt C j).op≠.not:=by rcases op with e|e <;> simp [e]
      exact Or.inr ⟨j,idx,ne,by rw [←eq,binary idx ne]⟩
end PEqualNP.Outside.L_meta_25689_aux.Lit

namespace PEqualNP.Outside.L_meta_25689_aux.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

abbrev V {N : Nat} (C : Circuit) (x : Fin N→Bool) (w : Nat) := (run C.gates (List.ofFn x)).getD w false
def ReadsStem (N : Nat) (C : Circuit) (j i : Nat) := ∃w∈(gateAt C j).inputs,(trace N C w).1=i

theorem rawV {N} (C : Circuit) (x : Fin N→Bool) (i : Fin N) : V C x i.val=x i := by
  rw [V,run_input _ _ _ (by simpa using i.isLt)];exact readFn x i

theorem literalV {N} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (x : Fin N→Bool) (w : Nat) (ok : w<N+C.size) (i : Fin N) (atRaw : (trace N C w).1=i.val) :
    V C x w=applySign (trace N C w).2 (x i) := by
  have v:=value good back (List.ofFn x) List.length_ofFn w ok
  change V C x w=applySign _ (V C x _) at v
  rwa [atRaw,rawV] at v

theorem agree {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (i : Fin N) (x y : Fin N→Bool) (same : ∀a,a≠i → x a=y a)
    (held : ∀j<C.size,(gateAt C j).op≠.not → ReadsStem N C j i.val → V C x (N+j)=V C y (N+j))
    (w : Nat) (ok : w<N+C.size) (off : (trace N C w).1≠i.val) : V C x w=V C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<N
    · rw [low C raw] at off
      let a : Fin N:=⟨w,raw⟩
      exact (rawV C x a).trans ((same a (fun e=>off (congrArg Fin.val e))).trans (rawV C y a).symm)
    let j:=w-N
    have eq : N+j=w:=Nat.add_sub_of_le (by omega)
    have idx : j<C.size:=by dsimp [j];omega
    rcases opAt (N:=N) good j idx with ⟨op,v,pin⟩|⟨op,_⟩
    · have lt:=back j idx v (by simp [pin])
      rw [←eq,unary idx op pin lt] at off
      have s:=ih v (by omega) (by omega) off
      rw [←eq];unfold V at s ⊢
      rw [gv N C back _ List.length_ofFn j idx,gv N C back _ List.length_ofFn j idx]
      simp [op,pin,GateOp.eval] <;> simpa [List.getD_eq_getElem?_getD] using s
    · have ne : (gateAt C j).op≠.not:=by rcases op with e|e <;> simp [e]
      by_cases present : ReadsStem N C j i.val
      · exact eq ▸ held j idx ne present
      rw [←eq];unfold V
      rw [gv N C back _ List.length_ofFn j idx,gv N C back _ List.length_ofFn j idx]
      congr 1
      apply List.map_congr_left
      intro v pin
      have lt:=back j idx v pin
      exact ih v (by omega) (by omega) (fun e=>present ⟨v,pin,e⟩)

theorem nextBinary {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (live : ∀i : Fin C.gates.length, N+i.val≠C.output → ∃ j : Fin C.gates.length,i<j ∧ reads (C.gates.get j) (N+i.val))
    (base : Nat) (notOut : (trace N C C.output).1≠base) (j : Nat) (idx : j<C.size)
    (root : (trace N C (N+j)).1=base) :
    ∃r<C.size,j<r ∧ (gateAt C r).op≠.not ∧ ReadsStem N C r base := by
  have ne : N+j≠C.output:=by intro eq;exact notOut (eq ▸ root)
  obtain ⟨r,after,later⟩:=live ⟨j,idx⟩ ne
  have opEq : C.gates.get r=gateAt C r.val:=(List.getD_eq_getElem _ _ r.isLt).symm
  rw [opEq] at later
  have member : gateAt C r.val∈C.gates:=by rw [←opEq];exact List.getElem_mem r.isLt
  have pin:=(good_read (good _ member) _).mp later
  have lt : j<r.val:=after
  rcases opAt (N:=N) good r.val r.isLt with ⟨op,v,hv⟩|⟨op,_⟩
  · have eq : N+j=v:=by simpa [hv] using pin
    have below:=back r.val r.isLt v (by simp [hv])
    have newRoot : (trace N C (N+r.val)).1=base:=by rw [unary r.isLt op hv below,←eq];exact root
    obtain ⟨k,hk,more,opr,read⟩:=nextBinary good back live base notOut r.val r.isLt newRoot
    exact ⟨k,hk,by omega,opr,read⟩
  · exact ⟨r.val,r.isLt,lt,by rcases op with h|h <;> simp [h],N+j,pin,root⟩
termination_by C.size-j
decreasing_by have h : r.val<C.size:=r.isLt;omega
end PEqualNP.Outside.L_meta_25689_aux.Lit

namespace PEqualNP.Outside.L_meta_25689_aux.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

theorem costElided (C : Circuit) (F : Finset Nat) (sites : ∀j∈F,j<C.size ∧ (gateAt C j).op≠.not) :
    remaining bin C F C.size+F.card=listed bin C.gates := by
  classical
  have filt : (Finset.range C.size).filter (·∈F)=F := by
    ext j;simp only [Finset.mem_filter,Finset.mem_range];exact ⟨fun h=>h.2,fun h=>⟨(sites j h).1,h⟩⟩
  have card : F.card=∑j∈Finset.range C.size,if j∈F then 1 else 0:=by rw [←Finset.card_filter,filt]
  rw [card,←full_price bin C];unfold remaining
  rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl
  intro j _
  by_cases mem : j∈F
  · simp [mem,bin,(sites j mem).2]
  · simp [mem]

theorem folded {X : Type} (n m : Nat) (C : Circuit) (fan : FanInTwo C)
    (src : X→List Bool) (dst : X→List Bool) (hs : ∀x,(src x).length=n) (ht : ∀x,(dst x).length=m)
    (raw : ∀ w<n,(∃b,∀x,(src x).getD w false=b) ∨ ∃t,t < m ∧ ∀x,(src x).getD w false=(dst x).getD t false)
    (nc : ¬∃b,∀x,C.eval (src x)=b) (F : Finset Nat) (sites : ∀j∈F,j<C.size ∧ (gateAt C j).op≠.not)
    (fold : ∀j∈F,collapses (fun x w=>(run C.gates (src x)).getD w false) (n+j)
      (fun x=>(run C.gates (src x)).getD (n+j) false)) :
    ∃D : Circuit,FanInTwo D ∧ listed bin D.gates+F.card≤listed bin C.gates ∧ ∀x,D.eval (dst x)=C.eval (src x) := by
  obtain ⟨D,good,_,_,prices,values⟩:=engineWeighted False n m C src dst hs ht F fan False.elim raw nc
    (fun j h=>⟨(sites j h).1,fold j h⟩)
  have spent:=prices bin
  have total:=costElided C F sites
  exact ⟨D,good_fan good,by omega,values⟩

theorem restrictRaw {n : Nat} (i : Fin (n+1)) (v : Bool) (w : Nat) (h : w<n+1) :
    (∃b,∀y : Fin n→Bool,(List.ofFn (Fin.insertNth i v y)).getD w false=b) ∨
    ∃t,t<n ∧ ∀y : Fin n→Bool,(List.ofFn (Fin.insertNth i v y)).getD w false=(List.ofFn y).getD t false := by
  let j : Fin (n+1):=⟨w,h⟩
  rcases Fin.eq_self_or_eq_succAbove i j with eq|⟨k,eq⟩
  · refine Or.inl ⟨v,fun y=>?_⟩
    change (List.ofFn _).getD j.val false=v
    rw [readFn,eq,Fin.insertNth_apply_same]
  · refine Or.inr ⟨k.val,k.isLt,fun y=>?_⟩
    change (List.ofFn _).getD j.val false=(List.ofFn _).getD k.val false
    rw [readFn,readFn,eq,Fin.insertNth_apply_succAbove]

theorem outputBound {N} (C : Circuit) (nc : ¬∃v,∀x : Fin N→Bool,C.eval (List.ofFn x)=v) : C.output<N+C.size := by
  by_contra! far
  exact nc ⟨false,fun x=>past C.gates (List.ofFn x) C.output (by rw [List.length_ofFn];exact far)⟩

theorem outputNotRaw {N} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (two : 2≤N) (ok : C.output<N+C.size)
    (sensitive : ∀i : Fin N,∀x : Fin N→Bool, V C (Function.update x i (!x i)) C.output≠V C x C.output) :
    ∀ i : Fin N,(trace N C C.output).1≠i.val := by
  intro i root
  let j : Fin N:=if i.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have ne : i≠j:=by
    intro eq;have h:=congrArg Fin.val eq;by_cases z : i.val=0 <;> simp [j,z] at h <;> omega
  let x : Fin N→Bool:=fun _=>false
  have y:=literalV good back (Function.update x j (!x j)) C.output ok i root
  have z:=literalV good back x C.output ok i root
  exact sensitive j x (by rw [y,z,Function.update_of_ne ne])
end PEqualNP.Outside.L_meta_25689_aux.Lit

namespace PEqualNP.Outside.L_meta_25689_aux.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

noncomputable def absorb (g : Gate) : Bool := decide (g.op=GateOp.or)

theorem apply_twice (s v : Bool) : applySign s (applySign s v)=v := by cases s <;> cases v <;> rfl

theorem controlled (g : Gate) (op : g.op=.and ∨ g.op=.or) (a b w : Nat) (pins : g.inputs=[a,b])
    (read : w∈g.inputs) (z : Nat→Bool) (value : z w=absorb g) : g.op.eval (g.inputs.map z)=absorb g := by
  have mem : w=a ∨ w=b:=by simpa [pins] using read
  rcases mem with h|h <;> subst w <;> rcases op with e|e <;> simp [absorb,e,pins,GateOp.eval] at value ⊢ <;> simp [value]

theorem binaryPins {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (j : Nat) (idx : j<C.size)
    (ne : (gateAt C j).op≠.not) : ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    ∃a b,a≠b ∧ (gateAt C j).inputs=[a,b] := by
  rcases opAt (N:=N) good j idx with ⟨h,_⟩|h
  · contradiction
  · exact h

theorem another {N : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack N C)
    (i k : Fin N) (ik : i≠k) (j v : Nat) (idx : j<C.size) (ne : (gateAt C j).op≠.not)
    (pin : v∈(gateAt C j).inputs) (other : (trace N C v).1=k.val)
    (ok : C.output<N+C.size) (off : (trace N C C.output).1≠i.val)
    (sensitive : ∀x : Fin N→Bool,V C (Function.update x i (!x i)) C.output≠V C x C.output) :
    ∃r<C.size,r≠j ∧ (gateAt C r).op≠.not ∧ ReadsStem N C r i.val := by
  classical
  by_contra! none
  let g:=gateAt C j
  let x : Fin N→Bool:=fun _=>applySign (trace N C v).2 (absorb g)
  let y:=Function.update x i (!x i)
  have limit : v<N+C.size:=by have l:=back j idx v pin;omega
  have xval : V C x v=absorb g:=(literalV good back x v limit k other).trans (apply_twice _ _)
  have yval : V C y v=absorb g := by
    rw [literalV good back y v limit k other]
    unfold y;rw [Function.update_of_ne (Ne.symm ik)];exact apply_twice _ _
  obtain ⟨op,a,b,_,inputs⟩:=binaryPins (N:=N) good j idx ne
  have killed (z : Fin N→Bool) (h : V C z v=absorb g) : V C z (N+j)=absorb g :=
    (gv N C back _ List.length_ofFn j idx).trans (controlled g op a b v inputs pin _ h)
  have held (r) (h : r<C.size) (no : (gateAt C r).op≠.not) (reads : ReadsStem N C r i.val) :
      V C y (N+r)=V C x (N+r) := by
    by_cases eq : r=j
    · subst r;exact (killed y yval).trans (killed x xval).symm
    · exact False.elim (none r h eq no reads)
  apply sensitive x
  exact agree good back i y x (fun a h=>Function.update_of_ne h _ _) held C.output ok off

theorem triple {n : Nat} {C : Circuit} (good : ∀g∈C.gates,Good False g) (back : ReadsBack (n+1) C)
    (live : ∀i : Fin C.gates.length,n+1+i.val≠C.output → ∃j : Fin C.gates.length,i<j ∧ reads (C.gates.get j) (n+1+i.val))
    (i : Fin (n+1)) (j r : Nat) (less : j<r) (idx : r<C.size)
    (jbin : (gateAt C j).op≠.not) (rbin : (gateAt C r).op≠.not)
    (first : ReadsStem (n+1) C j i.val) (second : ReadsStem (n+1) C r i.val)
    (outOK : C.output<n+1+C.size) (nc : ∀b,¬∃v,∀y : Fin n→Bool,V C (Fin.insertNth i b y) C.output=v) :
    ∃b,∃D : Circuit,FanInTwo D ∧ listed bin D.gates+3≤listed bin C.gates ∧
      ∀y : Fin n→Bool,D.eval (List.ofFn y)=C.eval (List.ofFn (Fin.insertNth i b y)) := by
  obtain ⟨v,vr,root⟩:=second
  let N:=n+1
  let val:=applySign (trace N C v).2 (absorb (gateAt C r))
  let src:=fun y : Fin n→Bool=>List.ofFn (Fin.insertNth i val y)
  let W:=fun (y : Fin n→Bool) w=>(run C.gates (src y)).getD w false
  have atI (w) (h : w<N+C.size) (eq : (trace N C w).1=i.val) (y : Fin n→Bool) :
      W y w=applySign (trace N C w).2 val := by
    have z:=literalV good back (Fin.insertNth i val y) w h i eq
    simpa only [Fin.insertNth_apply_same] using z
  obtain ⟨op,a,b,_,pins⟩:=binaryPins (N:=N) good r idx rbin
  have stable (y : Fin n→Bool) : W y (N+r)=absorb (gateAt C r) := by
    have h:=back r idx v vr
    exact (gv N C back _ List.length_ofFn r idx).trans (controlled _ op a b v pins vr (W y)
      ((atI v (by omega) root y).trans (apply_twice _ _)))
  have endRoot : (trace N C C.output).1≠N+r := by
    intro out
    apply nc val
    refine ⟨applySign (trace N C C.output).2 (absorb (gateAt C r)),fun y=>?_⟩
    have v:=value good back (src y) List.length_ofFn C.output outOK
    change W y C.output=applySign _ (W y _) at v
    rwa [out,stable y] at v
  obtain ⟨q,qidx,rq,qbin,w,wq,wroot⟩:=nextBinary good back live (N+r) endRoot r idx (by rw [binary idx rbin])
  let F : Finset Nat:={j,r,q}
  have ji : j<C.size:=by omega
  have sites (p) (hp : p∈F) : p<C.size ∧ (gateAt C p).op≠.not := by
    simp only [F,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with h|h|h <;> subst p <;> first | exact ⟨ji,jbin⟩ | exact ⟨idx,rbin⟩ | exact ⟨qidx,qbin⟩
  have touched (p) (hp : p∈F) : ∃t∈(gateAt C p).inputs,FixedAt W t := by
    simp only [F,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with eq|eq|eq
    · subst p
      obtain ⟨t,pin,rt⟩:=first
      exact ⟨t,pin,_,atI t (by have h:=back j ji t pin;omega) rt⟩
    · subst p
      exact ⟨v,vr,_,atI v (by have h:=back r idx v vr;omega) root⟩
    · subst p
      refine ⟨w,wq,applySign (trace N C w).2 (absorb (gateAt C r)),fun y=>?_⟩
      have limit:=back q qidx w wq
      have z:=value good back (src y) List.length_ofFn w (by omega)
      change W y w=applySign _ (W y _) at z
      rwa [wroot,stable y] at z
  have fold (p) (hp : p∈F) : collapses W (N+p) (fun y=>W y (N+p)) := by
    obtain ⟨h,nb⟩:=sites _ hp
    obtain ⟨t,pin,b,fixed⟩:=touched _ hp
    obtain ⟨op,a,b',_,inputs⟩:=binaryPins (N:=N) good p h nb
    have e : ∀y,W y (N+p)=(gateAt C p).op.eval ((gateAt C p).inputs.map (W y)):=fun y=>gv N C back _ List.length_ofFn p h
    have z:=when_read W (gateAt C p) (N+p) t b (by tauto) (by simp [inputs]) (back p h)
      (Or.inr ⟨nb,pin⟩) fixed
    simpa only [e] using z
  obtain ⟨D,fan,cost,sem⟩:=folded N n C (good_fan good) src List.ofFn (fun _=>List.length_ofFn)
    (fun _=>List.length_ofFn) (restrictRaw i val) (nc val) F sites fold
  have sc : F.card=3:=by simp [F,show j≠r by omega,show r≠q by omega,show j≠q by omega]
  exact ⟨val,D,fan,by rwa [sc] at cost,sem⟩

theorem minLive {N : Nat} (C : Circuit) (fan : FanInTwo C) (f : (Fin N→Bool)→Bool)
    (rep : ∀x,C.eval (List.ofFn x)=f x) (nc : ¬∃v,∀x,f x=v) :
    ∃E : Circuit,(∀g∈E.gates,Good False g) ∧ ReadsBack N E ∧ listed bin E.gates≤listed bin C.gates ∧
      (∀x,E.eval (List.ofFn x)=f x) ∧
      (∀ i : Fin E.gates.length,N+i.val≠E.output → ∃j : Fin E.gates.length,i<j ∧ reads (E.gates.get j) (N+i.val)) ∧
      ∀D : Circuit,FanInTwo D → (∀x,D.eval (List.ofFn x)=f x) → listed bin E.gates≤listed bin D.gates := by
  classical
  let possible:=fun s : Nat=>∃D : Circuit,FanInTwo D ∧ (∀x,D.eval (List.ofFn x)=f x) ∧ listed bin D.gates ≤ s
  have ex : ∃s,possible s:=⟨_,C,fan,rep,le_rfl⟩
  obtain ⟨D,dg,df,ds⟩:=Nat.find_spec ex
  obtain ⟨E,good,back,cost,ef,live⟩:=initial D dg f df nc
  have best (A : Circuit) (ag : FanInTwo A) (af : ∀x,A.eval (List.ofFn x)=f x) : listed bin E.gates≤listed bin A.gates :=
    (cost bin).trans (ds.trans (Nat.find_min' ex ⟨A,ag,af,le_rfl⟩))
  exact ⟨E,good,back,best C fan rep,ef,live,best⟩

theorem bottomStep {n : Nat} (E : Circuit) (good : ∀g∈E.gates,Good False g) (back : ReadsBack (n+1) E)
    (live : ∀i : Fin E.gates.length,n+1+i.val≠E.output → ∃j : Fin E.gates.length,i<j ∧ reads (E.gates.get j) (n+1+i.val))
    (size : 2≤n+1) (ok : E.output<n+1+E.size)
    (sens : ∀i : Fin (n+1),∀x : Fin (n+1)→Bool,V E (Function.update x i (!x i)) E.output ≠V E x E.output)
    (varies : ∀i b,¬∃v,∀y : Fin n→Bool,V E (Fin.insertNth i b y) E.output=v)
    (minimal : ∀D : Circuit,FanInTwo D → (∀x : Fin (n+1)→Bool,D.eval (List.ofFn x)=E.eval (List.ofFn x)) → listed bin E.gates≤listed bin D.gates) :
    ∃(i : Fin (n+1)) (b : Bool) (D : Circuit),FanInTwo D ∧ listed bin D.gates+3≤listed bin E.gates ∧
      ∀y : Fin n→Bool,D.eval (List.ofFn y)=E.eval (List.ofFn (Fin.insertNth i b y)) := by
  classical
  let N:=n+1
  have off:=outputNotRaw good back size ok sens
  have ex : ∃j,j<E.size ∧ (gateAt E j).op≠.not := by
    rcases roots good back E.output ok with h|⟨j,idx,binary,_⟩
    · exact False.elim (off ⟨_,h⟩ rfl)
    · exact ⟨j,idx,binary⟩
  let j:=Nat.find ex
  obtain ⟨hj,nb⟩:=Nat.find_spec ex
  change j<E.size at hj
  change (gateAt E j).op≠.not at nb
  obtain ⟨op,a,b,_,pins⟩:=binaryPins (N:=N) good j hj nb
  have av : a∈(gateAt E j).inputs:=by simp [pins]
  have bv : b∈(gateAt E j).inputs:=by simp [pins]
  have below (w) (mem : w∈(gateAt E j).inputs) : (trace N E w).1<N := by
    have low:=back j hj w mem
    rcases roots good back w (by omega) with h|⟨l,idx,nb,root⟩
    · exact h
    · have h : j≤l:=Nat.find_min' ex ⟨idx,nb⟩
      have first:=Lit.below N E w
      change (trace N E w).1=N+l at root
      change w<N+j at low;omega
  let i : Fin N:=⟨_,below a av⟩
  let k : Fin N:=⟨_,below b bv⟩
  by_cases same : i=k
  · have sa (x : Fin N→Bool) : V E x a=applySign (trace N E a).2 (x i):=literalV good back x a (by have h:=back j hj a av;omega) i rfl
    have sb (x : Fin N→Bool) : V E x b=applySign (trace N E b).2 (x i):=literalV good back x b (by have h:=back j hj b bv;omega) i (congrArg Fin.val same).symm
    have eval (x : Fin N→Bool) : V E x (N+j)=(gateAt E j).op.eval [V E x a,V E x b] := by
      simpa only [pins,List.map_cons,List.map_nil] using gv N E back (List.ofFn x) List.length_ofFn j hj
    have collapse : collapses (fun x : Fin N→Bool=>V E x) (N+j) (fun x=>V E x (N+j)) := by
      by_cases signs : (trace N E a).2=(trace N E b).2
      · refine Or.inr ⟨a,back j hj a av,fun x=>?_⟩
        change V E x (N+j)=V E x a
        rw [eval x,sa x,sb x,signs];rcases op with h|h <;> simp [h,GateOp.eval]
      · rcases op with h|h
        · refine Or.inl ⟨false,fun x=>?_⟩
          change V E x (N+j)=false
          rw [eval x,sa x,sb x,h];cases ha : (trace N E a).2 <;> cases hb : (trace N E b).2 <;> cases x i <;> simp_all [GateOp.eval,applySign]
        · refine Or.inl ⟨true,fun x=>?_⟩
          change V E x (N+j)=true
          rw [eval x,sa x,sb x,h];cases ha : (trace N E a).2 <;> cases hb : (trace N E b).2 <;> cases x i <;> simp_all [GateOp.eval,applySign]
    have nc : ¬∃v,∀x : Fin N→Bool,E.eval (List.ofFn x)=v := by
      rintro ⟨v,val⟩;let x : Fin N→Bool:=fun _=>false
      exact sens i x ((val _).trans (val x).symm)
    obtain ⟨D,fan,z,sem⟩:=folded N N E (good_fan good) (fun x : Fin N→Bool=>List.ofFn x) List.ofFn
      (fun _=>List.length_ofFn) (fun _=>List.length_ofFn) (fun w hw=>Or.inr ⟨w,hw,fun _=>rfl⟩) nc {j}
      (by simpa using And.intro hj nb) (by intro l hl;obtain rfl : l=j:=Finset.mem_singleton.mp hl;exact collapse)
    have m:=minimal D fan sem;rw [Finset.card_singleton] at z;omega
  · obtain ⟨r,ri,diff,rb,second⟩:=another good back i k same j b hj nb bv rfl ok (off i) (sens i)
    have least : j≤r:=Nat.find_min' ex ⟨ri,rb⟩
    exact ⟨i,triple good back live i j r (by omega) ri nb rb ⟨a,av,rfl⟩ second ok (varies i)⟩
end PEqualNP.Outside.L_meta_25689_aux.Lit

namespace PEqualNP.Outside.L_meta_25689_aux.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this

theorem parNC (n : Nat) (c : Bool) : ¬∃v,∀x : Fin (n+1)→Bool,xor (par (n+1) x) c=v := by
  rintro ⟨v,h⟩
  let u : Fin n→Bool:=fun _=>false
  have eq:=(h (Fin.snoc u false)).trans (h (Fin.snoc u true)).symm
  rw [par_snoc,par_snoc] at eq;cases bit : par n u <;> cases c <;> simp [bit] at eq

theorem parityBinary : ∀n c (C : Circuit),FanInTwo C →
    (∀x : Fin (n+1)→Bool,C.eval (List.ofFn x)=xor (par (n+1) x) c) →
    3*n≤listed bin C.gates := by
  intro n
  induction n with
  | zero => intro c C _ _;simp
  | succ n ih =>
    intro c C fan sem
    let N:=n+1+1
    let f:=fun x : Fin N→Bool=>xor (par N x) c
    obtain ⟨E,good,back,cost,eq,live,minimal⟩:=minLive C fan f sem (parNC (n+1) c)
    have nc : ¬∃v,∀x : Fin N→Bool,E.eval (List.ofFn x)=v :=
      fun ⟨v,h⟩=>parNC (n+1) c ⟨v,fun x=>(eq x).symm.trans (h x)⟩
    have depends (i : Fin N) (x : Fin N→Bool) : V E (Function.update x i (!x i)) E.output≠V E x E.output := by
      change E.eval (List.ofFn _ )≠E.eval (List.ofFn x)
      rw [eq,eq];unfold f;rw [par_flip];cases par N x <;> cases c <;> decide
    have restricted (i : Fin N) (b : Bool) : ¬∃v,∀y : Fin (n+1)→Bool,V E (Fin.insertNth i b y) E.output=v := by
      rintro ⟨v,h⟩
      apply parNC n (xor b c)
      refine ⟨v,fun y=>?_⟩
      have z:=h y
      change E.eval (List.ofFn (Fin.insertNth i b y))=v at z
      rw [eq] at z;unfold f at z;rwa [par_insertNth,Bool.xor_assoc] at z
    obtain ⟨i,b,D,fanD,saved,values⟩:=bottomStep E good back live (by omega) (outputBound E nc) depends restricted
      (fun D g sem=>minimal D g (fun x=>(sem x).trans (eq x)))
    have next (y : Fin (n+1)→Bool) : D.eval (List.ofFn y)=xor (par (n+1) y) (xor b c) := by
      rw [values,eq];unfold f;rw [par_insertNth,Bool.xor_assoc]
    have floor:=ih (xor b c) D fanD next
    omega
end PEqualNP.Outside.L_meta_25689_aux.Lit

namespace PEqualNP.Outside.L_meta_25689_aux.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

theorem parBit (n : Nat) (x : Fin n→Bool) :
    ((Finset.univ.filter fun i : Fin n=>x i).card).testBit 0=par n x := by
  simp [par,Nat.testBit_zero]

theorem flipBit {m : Nat} (j : Fin m) (x : Fin m→Bool) :
    par m (Function.update x j (!x j)) = !par m x := by
  cases m with
  | zero => exact j.elim0
  | succ m => exact par_flip m j x

theorem allBlockEss {n m : Nat} (owner : Fin n→Fin m) (block : Fin m→(Fin n→Bool)→Bool)
    (localRead : ∀j x y,(∀i,owner i=j → x i=y i) → block j x=block j y)
    (pos : ∀i,∃x,block (owner i) (Function.update x i false)=false ∧ block (owner i) (Function.update x i true)=true) :
    let f:=fun x=>par m (fun j=>block j x)
    ∀i,∃x,f (Function.update x i false)≠f (Function.update x i true) := by
  dsimp only
  intro i
  obtain ⟨x,zero,one⟩:=pos i
  let lo:=fun j=>block j (Function.update x i false)
  let hi:=fun j=>block j (Function.update x i true)
  have flip : hi=Function.update lo (owner i) (!(lo (owner i))) := by
    funext j;by_cases self : j=owner i
    · subst j;simp [hi,lo,zero,one]
    · rw [Function.update_of_ne self]
      apply localRead
      intro v hv
      have ne : v≠i:=fun e=>self (hv ▸ congrArg owner e)
      simp [Function.update_of_ne ne]
  refine ⟨x,?_⟩
  change par m lo ≠ par m hi
  rw [flip,flipBit];cases par m lo <;> decide

theorem face {n m : Nat} (owner : Fin n→Fin m) (block : Fin m→(Fin n→Bool)→Bool) (surj : Function.Surjective owner)
    (localRead : ∀j x y,(∀i,owner i=j → x i=y i) → block j x=block j y)
    (pos : ∀i,∃x,block (owner i) (Function.update x i false)=false ∧ block (owner i) (Function.update x i true)=true) :
    ∃ wire : Fin m→Fin n, ∃fixed : Fin n→Bool, Function.Injective wire ∧
      ∀j y,block j (plug wire fixed y)=y j := by
  classical
  let wire:=fun j=>(surj j).choose
  have section' (j) : owner (wire j)=j:=(surj j).choose_spec
  have inj : Function.Injective wire:=fun a b h=>(section' a).symm.trans ((congrArg owner h).trans (section' b))
  let witness:=fun j=>(pos (wire j)).choose
  let fixed:=fun i=>witness (owner i) i
  refine ⟨wire,fixed,inj,fun j y=>?_⟩
  have many : block j (plug wire fixed y) = block j (Function.update (witness j) (wire j) (y j)) := by
    apply localRead
    intro i member
    by_cases eq : i=wire j
    · subst i;rw [onWire wire fixed inj,Function.update_self]
    · have out : i∉Finset.univ.image wire := by
        intro h;obtain ⟨t,_,hit⟩:=Finset.mem_image.mp h
        have e : t=j:=(section' t).symm.trans ((congrArg owner hit).trans member)
        exact eq (hit.symm.trans (congrArg wire e))
      simp [plug,out,Function.update_of_ne eq,fixed,member]
  have h:=(pos (wire j)).choose_spec
  change block (owner (wire j)) (Function.update (witness j) (wire j) false)=false ∧
    block (owner (wire j)) (Function.update (witness j) (wire j) true)=true at h
  rw [section' j] at h
  rw [many];cases value : y j <;> first | exact h.1 | exact h.2

theorem allLower {n m : Nat} (mp : 0 < m) (owner : Fin n→Fin m) (block : Fin m→(Fin n→Bool)→Bool)
    (surj : Function.Surjective owner) (localRead : ∀j x y,(∀i,owner i=j → x i=y i) → block j x=block j y)
    (pos : ∀i,∃x,block (owner i) (Function.update x i false)=false ∧ block (owner i) (Function.update x i true)=true)
    (C : Circuit) (fan : FanInTwo C) (rep : ∀x,C.eval (List.ofFn x)=par m (fun j=>block j x)) :
    n-m+3*(m-1)≤listed bin C.gates ∧ n-m+4*(m-1)≤C.size := by
  classical
  obtain ⟨wire,fixed,inj,equals⟩:=face owner block surj localRead pos
  let f:=fun x=>par m (fun j=>block j x)
  have parEq (x : Fin m→Bool) : f (plug wire fixed x)=par m x:=congrArg (par m) (funext (fun j=>equals j x))
  have non : ∃a b : Fin m→Bool,f (plug wire fixed a)≠f (plug wire fixed b) := by
    let i : Fin m:=⟨0,mp⟩
    let a : Fin m→Bool:=fun _=>false
    refine ⟨Function.update a i (!a i),a,?_⟩
    rw [parEq,parEq,flipBit];cases par m a <;> decide
  obtain ⟨D,dFan,cost,invert,answer⟩:=restrict C fan wire fixed inj f rep non
  have all:=allBlockEss owner block localRead pos
  have all' : ((Finset.univ : Finset (Fin n)).filter (fun i=>∃x,f (Function.update x i false)≠f (Function.update x i true)))=Finset.univ := by
    ext i;simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true];exact all i
  rw [all',Finset.card_univ,Fintype.card_fin] at cost
  have lower : 3*(m-1)≤listed bin D.gates := by
    cases m with
    | zero => simp
    | succ k =>
      have z:=parityBinary k false D dFan (fun x=>by rw [answer,parEq];simp)
      simpa using z
  have need : 4*(m-1)≤D.size:=PEqualNP.Outside.L_meta_25689_aux.OldParity.parity_lower4 m D.size
    ⟨D,dFan,le_rfl,fun x=>(answer x).trans (parEq x)⟩
  have sums (E : Circuit) : listed bin E.gates+listed inv E.gates=E.size := by
    obtain ⟨a,b⟩:=costs E
    rw [a,b];apply Nat.sub_add_cancel
    exact List.length_filter_le _ _
  have le : m≤n:=by simpa using Fintype.card_le_of_injective wire inj
  have d:=sums D;have c:=sums C;omega
end PEqualNP.Outside.L_meta_25689_aux.Lit

namespace PEqualNP.Outside.L_meta_25689_aux.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

private theorem wires_append (gs hs : List Gate) (out : ℕ) (x : List Bool) :
    (⟨gs ++ hs, out⟩ : Circuit).wires x =
      hs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        ((⟨gs, 0⟩ : Circuit).wires x) := by
  simp [Circuit.wires, List.foldl_append]

private theorem wires_length (gs : List Gate) (out : ℕ) (x : List Bool) :
    ((⟨gs, out⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

private theorem wires_getD_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    ((⟨gs ++ hs, 0⟩ : Circuit).wires x).getD i false =
      ((⟨gs, 0⟩ : Circuit).wires x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    have hlen : i < ((⟨gs ++ hs, 0⟩ : Circuit).wires x).length := by
      rw [wires_length, List.length_append]; omega
    rw [← List.append_assoc, wires_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]
    exact ih

private theorem map_gates_sim (L1 M : ℕ) (ρ : ℕ → ℕ) (gs : List Gate) (x W2 : List Bool)
    (hxlen : x.length = L1)
    (hM : W2.length + gs.length ≤ M)
    (hρ_in : ∀ i < L1, (ρ i < W2.length ∧ W2.getD (ρ i) false = x.getD i false) ∨
                       (M ≤ ρ i ∧ x.getD i false = false))
    (hρ_ge : ∀ i, L1 ≤ i → ρ i = i - L1 + W2.length) :
    ∀ (i : ℕ),
      ((⟨gs.map (fun g => ⟨g.op, g.inputs.map ρ⟩), 0⟩ : Circuit).wires W2).getD (ρ i) false =
        ((⟨gs, 0⟩ : Circuit).wires x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [List.map_nil, Circuit.wires, List.foldl_nil]
    by_cases hi : i < L1
    · rcases hρ_in i hi with ⟨_, heq⟩ | ⟨hge, hfalse⟩
      · exact heq
      · have : W2.length ≤ ρ i := by simp at hM; omega
        rw [hfalse, List.getD_eq_getElem?_getD, List.getElem?_eq_none this]; rfl
    · have h1 : L1 ≤ i := by omega
      have h2 : W2.length ≤ ρ i := by rw [hρ_ge i h1]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : x.length ≤ i),
        List.getElem?_eq_none h2]
  | append_singleton gs g ih =>
    intro i
    have hM' : W2.length + gs.length ≤ M := by simp at hM; omega
    have ih' := ih hM'
    set gs' : List Gate := gs.map (fun g => ⟨g.op, g.inputs.map ρ⟩)
    set g' : Gate := ⟨g.op, g.inputs.map ρ⟩
    have hmap : (gs ++ [g]).map (fun g => ⟨g.op, g.inputs.map ρ⟩) = gs' ++ [g'] := by
      simp [gs', g']
    rw [hmap, wires_append, wires_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set W1 := (⟨gs, 0⟩ : Circuit).wires x
    set W2' := (⟨gs', 0⟩ : Circuit).wires W2
    have hW1len : W1.length = L1 + gs.length := by rw [wires_length, hxlen]
    have hW2'len : W2'.length = W2.length + gs.length := by
      rw [wires_length]; simp [gs']
    have hval_eq : g'.op.eval (g'.inputs.map fun k => W2'.getD k false) =
        g.op.eval (g.inputs.map fun k => W1.getD k false) := by
      simp only [g', List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      exact ih' k
    rw [hval_eq]
    by_cases hi_lt : i < L1 + gs.length
    · by_cases h1 : i < L1
      · rcases hρ_in i h1 with ⟨hρlt, _⟩ | ⟨hρge, hfalse⟩
        · have hL : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
              (l ++ [a]).getD k false = l.getD k false := by
            intro l a k hk
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
          rw [hL W2' _ (ρ i) (by omega), hL W1 _ i (by omega)]
          exact ih' i
        · have hW2_ge : (W2' ++ [g.op.eval (g.inputs.map fun k => W1.getD k false)]).length ≤ ρ i := by
            simp only [List.length_append, List.length_singleton, hW2'len]
            simp at hM; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hW2_ge]
          simp only [Option.getD_none]
          have hW1_get : (W1 ++ [g.op.eval (g.inputs.map fun k => W1.getD k false)]).getD i false = x.getD i false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < W1.length),
              ← List.getD_eq_getElem?_getD]
            have hpre := wires_getD_prefix [] gs x i (by simpa [hxlen] using h1)
            simpa [W1, Circuit.wires] using hpre
          rw [hW1_get, hfalse]
      · have hρi_lt : ρ i < W2'.length := by rw [hρ_ge i (by omega)]; omega
        have hL : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
            (l ++ [a]).getD k false = l.getD k false := by
          intro l a k hk
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
        rw [hL W2' _ (ρ i) hρi_lt, hL W1 _ i (by omega)]
        exact ih' i
    · by_cases hi_eq : i = L1 + gs.length
      · subst hi_eq
        have hρi_eq : ρ (L1 + gs.length) = W2'.length := by
          rw [hρ_ge _ (by omega)]; omega
        rw [hρi_eq, ← hW1len]
        simp [List.getD_eq_getElem?_getD]
      · have hρi_gt : W2'.length + 1 ≤ ρ i := by
          rw [hρ_ge i (by omega)]; omega
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp [hW1len]; omega : (W1 ++ [_]).length ≤ i),
          List.getElem?_eq_none (by simp [hW2'len]; omega : (W2' ++ [_]).length ≤ ρ i)]

theorem xorStepAlt (v : List Bool) (i j : ℕ) (hi : i < v.length) (hj : j < v.length) :
    (Normalize.run [⟨GateOp.or, [i, j]⟩, ⟨GateOp.and, [i, j]⟩, ⟨GateOp.not, [v.length + 1]⟩,
      ⟨GateOp.and, [v.length, v.length + 2]⟩] v).getD (v.length + 3) false
      = xor (v.getD i false) (v.getD j false) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [Normalize.run, GateOp.eval, A _ _ hi, A _ _ hj]
  cases v[i]?.getD false <;> cases v[j]?.getD false <;> rfl

theorem listMono (gs : List Gate) (mono : ∀g∈gs,g.op=.and ∨ g.op=.or) : listed bin gs=gs.length := by
  induction gs with
  | nil => simp [listed]
  | cons g l ih =>
    have ok:=mono g List.mem_cons_self
    have h:=ih (fun a ha=>mono a (List.mem_cons_of_mem _ ha))
    rcases ok with e|e <;> simp [listed,bin,e] at h ⊢ <;> omega

def appendShift (N k i : Nat) := if i<N then i else i+k
def translated (N k : Nat) (g : Gate) : Gate:=⟨g.op,g.inputs.map (appendShift N k)⟩
def filler : Gate:=⟨.or,[0,0]⟩

theorem appendBlock {n : Nat} (gs : List Gate) (P : Circuit) (mono : Monotone2 P)
    (budget : Nat) (cost : P.size≤budget) (out : P.output<n+P.size) :
    ∃hs : List Gate, ∃w : Nat, hs.length=budget ∧ listed bin hs=budget ∧
      (∀g∈hs,g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) ∧
      w<n+(gs++hs).length ∧ ∀x : Fin n→Bool,(run (gs++hs) (List.ofFn x)).getD w false=P.eval (List.ofFn x) := by
  let ρ:=appendShift n gs.length
  let translatedP:=P.gates.map (translated n gs.length)
  let padding:=List.replicate (budget-P.size) filler
  let hs:=translatedP++padding
  have hlen : hs.length=budget:=by simp [hs,translatedP,padding,Circuit.size] at cost ⊢;omega
  have mono' (g) (hg : g∈hs) : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
    rcases List.mem_append.mp hg with h|h
    · obtain ⟨q,mem,rfl⟩:=List.mem_map.mp h
      obtain ⟨op,l⟩:=mono q mem
      exact ⟨by simpa [translated] using op,by simpa [translated] using l⟩
    · have e : g=filler:=(List.mem_replicate.mp h).2
      subst g;exact ⟨Or.inr rfl,by decide⟩
  have bound : ρ P.output<n+gs.length+translatedP.length := by
    simp only [translatedP,List.length_map];unfold ρ appendShift;split <;> change P.output<n+P.gates.length at out <;> omega
  refine ⟨hs,ρ P.output,hlen,(listMono _ (fun g h=>(mono' g h).1)).trans hlen,?_,?_,?_⟩
  · intro g h;obtain ⟨op,l⟩:=mono' g h;exact ⟨by rcases op with eq|eq <;> simp [eq],l⟩
  · change ρ P.output<n+(gs++(translatedP++padding)).length
    rw [List.length_append,List.length_append];omega
  · intro x
    let X:=List.ofFn x
    let W:=run gs X
    have lx : X.length=n:=List.length_ofFn
    have lw : W.length=n+gs.length:=by rw [show W.length=X.length+gs.length from run_length gs X,lx]
    have z:=map_gates_sim n (W.length+P.gates.length) ρ P.gates X W lx le_rfl
      (fun i hi=>Or.inl ⟨by simp [ρ,appendShift,hi,lw];omega,by simp [ρ,appendShift,hi,W];exact run_input _ _ _ (by rwa [lx])⟩)
      (fun i hi=>by simp [ρ,appendShift,show ¬i<n by omega,lw];omega) P.output
    change (run (gs++(translatedP++padding)) X).getD (ρ P.output) false=_
    rw [←List.append_assoc,run_init _ _ _ _ (by simp [lx];omega)]
    exact (show (run (gs++translatedP) X).getD (ρ P.output) false=(run translatedP W).getD (ρ P.output) false from by
      simp [run,W,List.foldl_append]).trans z

def xorList (m a b : Nat) : List Gate:=[⟨.or,[a,b]⟩,⟨.and,[a,b]⟩,⟨.not,[m+1]⟩,⟨.and,[m,m+2]⟩]
theorem xorCost (m a b : Nat) : (xorList m a b).length=4 ∧ listed bin (xorList m a b)=3 ∧
    ∀g∈xorList m a b,g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2 := by
  refine ⟨rfl,by simp [xorList,listed,bin],?_⟩
  intro g hg;simp only [xorList,List.mem_cons,List.mem_nil_iff,or_false] at hg
  rcases hg with e|e|e|e <;> subst g <;> simp

theorem xorAt {n : Nat} (gs : List Gate) (a b : Nat) (ha : a<n+gs.length) (hb : b<n+gs.length)
    (x : Fin n→Bool) : (run (gs++xorList (n+gs.length) a b) (List.ofFn x)).getD (n+gs.length+3) false=
      xor ((run gs (List.ofFn x)).getD a false) ((run gs (List.ofFn x)).getD b false) := by
  let W:=run gs (List.ofFn x)
  have len : W.length=n+gs.length:=by simp [W,run_length]
  have h:=xorStepAlt W a b (by omega) (by omega)
  rw [len] at h
  change (run (xorList (n+gs.length) a b) W).getD (n+gs.length+3) false=_ at h
  exact (show run (gs++xorList (n+gs.length) a b) (List.ofFn x)=run (xorList (n+gs.length) a b) W from by
    simp [run,W,List.foldl_append]) ▸ h
end PEqualNP.Outside.L_meta_25689_aux.Lit

namespace PEqualNP.Outside.L_meta_25689_aux.Lit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Normalize
open scoped Classical

def oddCount {m : Nat} (S : Finset (Fin m)) (x : Fin m→Bool) := decide ((S.filter (fun j=>x j)).card % 2=1)

theorem oddInsert {m : Nat} (S : Finset (Fin m)) (j : Fin m) (off : j∉S) (x : Fin m→Bool) :
    oddCount (insert j S) x=xor (oddCount S x) (x j) := by
  have notin : j∉S.filter (fun j=>x j):=fun h=>off (Finset.mem_filter.mp h).1
  cases v : x j <;> unfold oddCount <;> simp [Finset.filter_insert,v,notin,Nat.add_mod]
  have h:=Nat.mod_two_eq_zero_or_one (S.filter (fun i=>x i)).card
  rcases h with e|e <;> simp [e]

def allowed (g : Gate) := g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

theorem buildParts {n m : Nat} (block : Fin m→(Fin n→Bool)→Bool) (cap : Fin m→Nat)
    (supply : ∀j,∃P : Circuit,Monotone2 P ∧ P.size≤cap j ∧ P.output<n+P.size ∧ ∀x,P.eval (List.ofFn x)=block j x)
    (S : Finset (Fin m)) (non : S.Nonempty) :
    ∃ (gs : List Gate) (w : Nat), (∀g∈gs,allowed g) ∧
      gs.length=(∑j∈S,cap j)+4*(S.card-1) ∧ listed bin gs=(∑j∈S,cap j)+3*(S.card-1) ∧
      w<n+gs.length ∧ ∀x : Fin n→Bool,(run gs (List.ofFn x)).getD w false=oddCount S (fun j=>block j x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at non
  | @insert j S off ih =>
    obtain ⟨P,mono,cost,out,value⟩:=supply j
    by_cases empty : S=∅
    · subst S
      obtain ⟨hs,w,len,charge,fan,bound,eval⟩:=appendBlock [] P mono (cap j) cost out
      refine ⟨hs,w,fan,by simpa using len,by simpa using charge,by simpa using bound,fun x=>?_⟩
      have e : (run hs (List.ofFn x)).getD w false=block j x:=by simpa using (eval x).trans (value x)
      rw [e,oddInsert _ _ (by simp)]
      simp [oddCount]
    · obtain ⟨gs,a,ok,len,charge,low,eval⟩:=ih (Finset.nonempty_iff_ne_empty.mpr empty)
      obtain ⟨hs,b,hLen,hCost,hFan,hBound,hEval⟩:=appendBlock gs P mono (cap j) cost out
      let t:=n+(gs++hs).length
      let gates:=xorList t a b
      obtain ⟨xLen,xCost,xFan⟩:=xorCost t a b
      have positive:=Finset.card_pos.mp (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty))
      have card : 0<S.card:=Finset.card_pos.mpr positive
      refine ⟨(gs++hs)++gates,t+3,?_,?_,?_,?_,fun x=>?_⟩
      · intro g h
        rcases List.mem_append.mp h with earlier|last
        · rcases List.mem_append.mp earlier with h|h
          · exact ok g h
          · exact hFan g h
        · exact xFan g last
      · simp only [List.length_append,Finset.sum_insert off,Finset.card_insert_of_notMem off]
        change gs.length+hs.length+(xorList t a b).length=_
        rw [xLen,hLen,len];omega
      · have append (l r : List Gate) : listed bin (l++r)=listed bin l+listed bin r:=by simp [listed]
        rw [append,append,charge,hCost,show listed bin gates=3 from xCost,Finset.sum_insert off,Finset.card_insert_of_notMem off];omega
      · simp [gates,xorList,t] <;> omega
      · have al : a<n+(gs++hs).length:=by simp;omega
        have e:=xorAt (gs++hs) a b al hBound x
        have orig : (run (gs++hs) (List.ofFn x)).getD a false=oddCount S (fun j=>block j x) :=
          (run_init gs hs _ a (by simpa using low)).trans (eval x)
        change (run ((gs++hs)++xorList t a b) (List.ofFn x)).getD (t+3) false = _
        rw [e,orig,hEval,value,oddInsert S j off]

theorem allUpper {n m : Nat} (mp : 0 < m) (owner : Fin n→Fin m) (block : Fin m→(Fin n→Bool)→Bool)
    (surj : Function.Surjective owner)
    (pos : ∀i,∃x,block (owner i) (Function.update x i false)=false ∧ block (owner i) (Function.update x i true)=true)
    (small : ∀ j,∃P : Circuit,Monotone2 P ∧ P.size+1≤((Finset.univ : Finset (Fin n)).filter (fun i=>owner i=j)).card ∧
      ∀x,P.eval (List.ofFn x)=block j x) :
    ∃C : Circuit,FanInTwo C ∧ (∀x,C.eval (List.ofFn x)=par m (fun j=>block j x)) ∧
      listed bin C.gates=n-m+3*(m-1) ∧ C.size=n-m+4*(m-1) := by
  classical
  let fib:=fun j=>(Finset.univ : Finset (Fin n)).filter (fun i=>owner i=j)
  let cap:=fun j=>(fib j).card-1
  have one (j : Fin m) : 1≤(fib j).card:=by
    obtain ⟨i,eq⟩:=surj j
    exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩⟩
  have total : (∑j : Fin m,(fib j).card)=n := by
    simp only [fib,Finset.card_filter];rw [Finset.sum_comm]
    simp
  have exactCost : (∑j : Fin m,cap j)=n-m := by
    have sums : (∑j : Fin m,(cap j+1))=n:=by
      rw [←total];apply Finset.sum_congr rfl;intro j _
      dsimp [cap];have :=one j;omega
    rw [Finset.sum_add_distrib] at sums;simp at sums;omega
  have supply (j : Fin m) : ∃P : Circuit,Monotone2 P ∧ P.size≤cap j ∧ P.output<n+P.size ∧ ∀x,P.eval (List.ofFn x)=block j x := by
    obtain ⟨P,mon,size,sim⟩:=small j
    change P.size+1≤(fib j).card at size
    obtain ⟨i,e⟩:=surj j
    obtain ⟨x,l,r⟩:=pos i;rw [e] at l r
    have nc : ¬∃v,∀x : Fin n→Bool,P.eval (List.ofFn x)=v := by
      rintro ⟨v,z⟩
      have left:=(sim (Function.update x i false)).symm.trans (z _)
      have right:=(sim (Function.update x i true)).symm.trans (z _)
      rw [l] at left;rw [r] at right;cases v <;> contradiction
    exact ⟨P,mon,by dsimp [cap];omega,outputBound P nc,sim⟩
  have non : (Finset.univ : Finset (Fin m)).Nonempty:=⟨⟨0,mp⟩,Finset.mem_univ _⟩
  obtain ⟨gs,w,fan,len,charge,_,eval⟩:=buildParts block cap supply Finset.univ non
  exact ⟨⟨gs,w⟩,fan,eval,by simpa [exactCost] using charge,by simpa [Circuit.size,exactCost] using len⟩
end PEqualNP.Outside.L_meta_25689_aux.Lit

open PEqualNP.Outside.L_meta_25689_aux in
theorem PEqualNP.Outside.L_meta_25689 : ∀ (n m : Nat), 0 < m →
  let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
  ∀ (owner : Fin n → Fin m) (block : Fin m → (Fin n → Bool) → Bool),
    Function.Surjective owner →
    (∀ j x y, (∀ i, owner i = j → x i = y i) → block j x = block j y) →
    (∀ i, ∃ x : Fin n → Bool, block (owner i) (Function.update x i false) = false ∧
        block (owner i) (Function.update x i true) = true) →
    (∀ j, ∃ P : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 P ∧
      P.size + 1 ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => owner i = j)).card ∧
      ∀ x, P.eval (List.ofFn x) = block j x) →
    let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ x : Fin n → Bool,
        C.eval (List.ofFn x) = (((Finset.univ : Finset (Fin m)).filter (fun j => block j x)).card).testBit 0
    let B := (n-m)+3*(m-1)
    let G := (n-m)+4*(m-1)
    (∃ C, fits C ∧ binary C = B ∧ C.size = G) ∧ (∀ C, fits C → B ≤ binary C ∧ G ≤ C.size) := by
  intro n m mp
  dsimp only
  intro owner block surj localRead pos small
  obtain ⟨C,fan,eval,bin,len⟩:=Lit.allUpper mp owner block surj pos small
  constructor
  · refine ⟨C,⟨fan,fun x=>(eval x).trans (Lit.parBit _ _).symm⟩,?_,len⟩
    rwa [(costs C).2] at bin
  · intro E h
    obtain ⟨binary,total⟩:=Lit.allLower mp owner block surj localRead pos E h.1 (fun x=>(h.2 x).trans (Lit.parBit _ _))
    rw [(costs E).2] at binary
    exact ⟨binary,total⟩

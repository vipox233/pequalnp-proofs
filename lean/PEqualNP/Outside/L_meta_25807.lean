import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25807_aux.Normalize
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

end PEqualNP.Outside.L_meta_25807_aux.Normalize

namespace PEqualNP.Outside.L_meta_25807_aux.Normalize
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

end PEqualNP.Outside.L_meta_25807_aux.Normalize

namespace PEqualNP.Outside.L_meta_25807_aux.Normalize
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

end PEqualNP.Outside.L_meta_25807_aux.Normalize

namespace PEqualNP.Outside.L_meta_25807_aux.Normalize
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

end PEqualNP.Outside.L_meta_25807_aux.Normalize

namespace PEqualNP.Outside.L_meta_25807_aux.Normalize

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

end PEqualNP.Outside.L_meta_25807_aux.Normalize

namespace PEqualNP.Outside.L_meta_25807_aux.Pins
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

end PEqualNP.Outside.L_meta_25807_aux.Pins

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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

end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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

end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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

end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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

end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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
end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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
end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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
end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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
end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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
end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux.Partition
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
end PEqualNP.Outside.L_meta_25807_aux.Partition

namespace PEqualNP.Outside.L_meta_25807_aux
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

theorem normalized {n m : ℕ} {G : Fin n → Fin m → Bool} (C : Circuit) (fan : FanInTwo C)
    (rep : Represents G C) (horizontal : ∃ a c d, G a c ≠ G a d) (vertical : ∃ a b c, G a c ≠ G b c) :
    ∃ D : Circuit, D.size≤C.size ∧ Represents G D ∧ ReadsBack (n+m) D ∧
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
  obtain ⟨E,shape,back,sz,values⟩ := Normalize.engine False N N C y y len len ∅ fan False.elim
    (fun w hw => Or.inr ⟨w,hw,fun _ => rfl⟩)
    (fun ⟨z,h⟩ => nc ⟨z,fun p => (rep p.1 p.2).symm.trans (h p)⟩) (by simp)
  have esize : E.size≤C.size := by simpa only [Finset.card_empty,Nat.add_zero] using sz
  obtain ⟨D,dshape,db,ds,dv,live⟩ := Normalize.finish_live False N y len f nc E shape back
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
  refine ⟨D,ds.trans esize,dr,db,?_,pos,lastEq,?_⟩
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

theorem few_missing {n m : ℕ} (G : Fin n → Fin m → Bool) (D : Circuit) (back : ReadsBack (n+m) D)
    (rep : Represents G D) (out : n+m≤D.output) (rows : DifferentRows G) (cols : DifferentCols G) :
    n+m≤((Finset.range (n+m)).filter (fun i => 1≤Active D i)).card+2 := by
  classical
  let v := Active D
  have equal {a b : Fin n} {c d : Fin m}
      (same : ∀ i<n+m, 0<v i → ((i=a.val ∨ i=n+c.val) ↔ (i=b.val ∨ i=n+d.val))) : G a c=G b d := by
    rw [←rep a c,←rep b d]
    apply observed_agree back _ _ (Normalize.oneEach_length _ _) (Normalize.oneEach_length _ _) _ _ out
    intro i hi hit
    rw [Normalize.oneEach_getD,Normalize.oneEach_getD]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using same i hi hit
  have rsmall : ((Finset.range n).filter (fun i => v i=0)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,za⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,zb⟩ := Finset.mem_filter.mp hb
    let A : Fin n := ⟨a,Finset.mem_range.mp ha⟩
    let B : Fin n := ⟨b,Finset.mem_range.mp hb⟩
    by_contra ne
    obtain ⟨c,diff⟩ := rows A B (fun h => ne (congrArg Fin.val h))
    apply diff; apply equal
    intro i hi hit
    have ia : i≠a := fun e => by rw [e,za] at hit; omega
    have ib : i≠b := fun e => by rw [e,zb] at hit; omega
    simp [A,B,ia,ib]
  have csmall : ((Finset.range m).filter (fun i => v (n+i)=0)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro c hc d hd
    obtain ⟨hc,zc⟩ := Finset.mem_filter.mp hc
    obtain ⟨hd,zd⟩ := Finset.mem_filter.mp hd
    let X : Fin m := ⟨c,Finset.mem_range.mp hc⟩
    let Y : Fin m := ⟨d,Finset.mem_range.mp hd⟩
    by_contra ne
    obtain ⟨a,diff⟩ := cols X Y (fun h => ne (congrArg Fin.val h))
    apply diff; apply equal
    intro i hi hit
    have ix : i≠n+c := fun e => by rw [e,zc] at hit; omega
    have iy : i≠n+d := fun e => by rw [e,zd] at hit; omega
    simp [X,Y,ix,iy]
  let A := Finset.range (n+m)
  have split : (A.filter (fun i => v i=0)).card+(A.filter (fun i => 1≤v i)).card=A.card := by
    rw [Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib]
    calc
      _ = ∑ _i∈A, 1 := by
        apply Finset.sum_congr rfl
        intro i _; split_ifs <;> omega
      _ = _ := by simp
  have zeros : (A.filter (fun i => v i=0)).card≤2 := by
    rw [Finset.card_filter] at rsmall csmall ⊢
    dsimp only [A]
    rw [Finset.sum_range_add]
    omega
  change n+m≤(A.filter (fun i => 1≤v i)).card+2
  have total : A.card=n+m := by simp [A]
  omega

end PEqualNP.Outside.L_meta_25807_aux

namespace PEqualNP.Outside.L_meta_25807_aux
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


end PEqualNP.Outside.L_meta_25807_aux

namespace PEqualNP.Outside.L_meta_25807_aux
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

end PEqualNP.Outside.L_meta_25807_aux

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves.Profile.Wire


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def pt (n m a b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n m : ℕ) (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n m u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castAdd, Fin.coe_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.coe_natAdd]
    omega

end PEqualNP.Outside.L_meta_25807_aux.Leaves.Profile.Wire

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves.Profile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def inner51 (N : Nat) (D : Finset Nat) (w : Nat) : Prop :=
  N≤w ∧ w-N∈D

structure Region51 (N : Nat) (C : Circuit) (S D E : Finset Nat) (top : Nat) : Prop where
  back : ReadsBack N C
  small : ∀ w∈S, w<N
  kept : D ⊆ Finset.range C.size
  topMem : top∈D
  one : E.card≤1
  entries : ∀ w∈E,w<N+top ∧ w∉S ∧ ¬inner51 N D w
  gates : ∀ j∈D, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    ∀ w∈(gateAt C j).inputs,w∈S ∨ inner51 N D w ∨ w∈E
  sealedInputs : ∀ j<C.size,j∉D → ∀ w∈(gateAt C j).inputs,w∉S ∧ (inner51 N D w → w=N+top)
  outS : C.output∉S
  outD : inner51 N D C.output → C.output=N+top

def cutVal51 (C : Circuit) (N : Nat) (E : Finset Nat) (lit : Nat) (e : Bool) (w : Nat) : Bool :=
  if w∈E then e else if w<N then decide (w=lit) else
    (gateAt C (w-N)).op.eval ((gateAt C (w-N)).inputs.map fun v =>
      if hv : v<w then cutVal51 C N E lit e v else false)
termination_by w

private lemma gateMono51 {l : List Nat} {f g : Nat → Bool} {op : GateOp}
    (h : op=.and ∨ op=.or) (le : ∀ v∈l,f v=true → g v=true)
    (x : op.eval (l.map f)=true) : op.eval (l.map g)=true := by
  rcases h with rfl|rfl
  · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at x ⊢
    exact fun v hv => le v hv (x v hv)
  · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at x ⊢
    obtain ⟨v,hv,hf⟩ := x
    exact ⟨v,hv,le v hv hf⟩

theorem cutMono51 {C : Circuit} {N lit top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) {a b : Bool} (le : ∀ v∈E,a=true → b=true) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E →
      cutVal51 C N E lit a w=true → cutVal51 C N E lit b w=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    rw [cutVal51,cutVal51]
    by_cases he : w∈E
    · simpa only [if_pos he] using le w he
    simp only [if_neg he]
    by_cases raw : w<N
    · simp only [if_pos raw,imp_self]
    simp only [if_neg raw]
    have ins : inner51 N D w := (h.resolve_left (fun z => raw (H.small w z))).resolve_right he
    have jmem := ins.2
    refine gateMono51 (H.gates _ jmem).1 ?_
    intro v hv
    have lt := H.back (w-N) (Finset.mem_range.mp (H.kept jmem)) v hv
    have bound : v<w := by have := ins.1;omega
    simpa only [dif_pos bound] using ih v bound ((H.gates _ jmem).2 v hv)

theorem cutMatches51 {C : Circuit} {N lit top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (values : Nat → Bool) (e : Bool)
    (base : ∀ w∈S,values w=decide (w=lit)) (boundary : ∀ w∈E,values w=e)
    (step : ∀ j<C.size,values (N+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map values)) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E → values w=cutVal51 C N E lit e w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    rw [cutVal51]
    by_cases he : w∈E
    · simpa only [if_pos he] using boundary w he
    simp only [if_neg he]
    by_cases raw : w<N
    · rw [if_pos raw]
      exact base w (h.resolve_right (fun z => z.elim (fun si => (Nat.not_le_of_gt raw) si.1) he))
    rw [if_neg raw]
    have ins : inner51 N D w := (h.resolve_left (fun z => raw (H.small w z))).resolve_right he
    have jmem := ins.2
    have jlt := Finset.mem_range.mp (H.kept jmem)
    have eq := step (w-N) jlt
    rw [show N+(w-N)=w by omega] at eq
    rw [eq]
    congr 1
    apply List.map_congr_left
    intro v hv
    have lt := H.back (w-N) jlt v hv
    have bound : v<w := by have := ins.1;omega
    rw [dif_pos bound]
    exact ih v bound ((H.gates _ jmem).2 v hv)

theorem outside51 {C : Circuit} {N top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (x y : Nat → Bool)
    (raw : ∀ w<N,w∉S → x w=y w)
    (gate : ∀ j<C.size,(∀ v∈(gateAt C j).inputs,x v=y v) → x (N+j)=y (N+j))
    (large : ∀ w,N+C.size≤w → x w=y w) :
    ∀ w,w∉S → (inner51 N D w → w=N+top) → (N+top≤w → x (N+top)=y (N+top)) → x w=y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro ns ex term
    by_cases inp : w<N
    · exact raw w inp ns
    by_cases high : N+C.size≤w
    · exact large w high
    by_cases localWire : inner51 N D w
    · have eq := ex localWire
      exact eq ▸ term (by omega)
    have jlt : w-N<C.size := by omega
    have nreg : w-N∉D := fun hit => localWire ⟨by omega,hit⟩
    have add : N+(w-N)=w := by omega
    have agree (v : Nat) (hv : v∈(gateAt C (w-N)).inputs) : x v=y v := by
      have b := H.back (w-N) jlt v hv
      have bv : v<w := by omega
      have e := H.sealedInputs _ jlt nreg v hv
      exact ih v bv e.1 e.2 (fun z => term (by omega))
    exact add ▸ gate _ jlt agree

end PEqualNP.Outside.L_meta_25807_aux.Leaves.Profile

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves.Profile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sideCap51 {n m d N top : Nat} {C : Circuit} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (A : Finset (Fin n)) (B : Finset (Fin m))
    (G : Fin n → Fin m → Bool) (pin : Fin n → Nat) (other : Fin m → Nat)
    (V : Fin n → Fin m → Nat → Bool)
    (distance : ∀ a b : Fin n,a≠b → d≤(Finset.univ.filter (fun v=>G a v≠G b v)).card)
    (privatePin : ∀ a∈A,pin a∈S) (unmarked : ∀ v∉B,other v∉S)
    (inputs : ∀ a v w,w<N → V a v w=(decide (w=pin a) || decide (w=other v)))
    (step : ∀ a v j,j<C.size → V a v (N+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map (V a v)))
    (large : ∀ a v w,N+C.size≤w → V a v w=false)
    (result : ∀ a v,V a v C.output=G a v) (short : B.card<d) :
    A.card≤2+E.card := by
  classical
  let sig (a : Fin n) (e : Bool) := cutVal51 C N E (pin a) e (N+top)
  have itop : inner51 N D (N+top) := ⟨by omega,by simpa using H.topMem⟩
  have mon (a : Fin n) : sig a false=true → sig a true=true :=
    cutMono51 H (fun _ _ _ => rfl) _ (Or.inr (Or.inl itop))
  let code (a : Fin n) : Nat := if sig a false then 0 else if sig a true then 2 else 1
  have cap (a : Fin n) : code a<2+E.card := by
    by_cases nonempty : E.Nonempty
    · have h := Finset.card_pos.mpr nonempty
      dsimp [code]; split <;> (try split) <;> omega
    · have rev : sig a true=true → sig a false=true :=
        cutMono51 H (fun w hw => (nonempty ⟨w,hw⟩).elim) _ (Or.inr (Or.inl itop))
      dsimp [code]; split <;> (try split) <;> first | omega | solve_by_elim
  have same {a b : Fin n} (h : code a=code b) (t : Bool) : sig a t=sig b t := by
    have ma := mon a
    have mb := mon b
    dsimp only [code] at h
    cases t <;> cases fa : sig a false <;> cases fb : sig b false <;>
      cases ta : sig a true <;> cases tb : sig b true <;> simp_all
  have inj : Set.InjOn code (↑A : Set (Fin n)) := by
    intro a ha b hb eqcode
    by_contra ne
    have subset : Finset.univ.filter (fun v=>G a v≠G b v) ⊆ B := by
      intro v hv
      by_contra nv
      have agreeRaw : ∀ w<N,w∉S → V a v w=V b v w := by
        intro w hw ns
        have na : w≠pin a := fun z=>ns (z ▸ privatePin a ha)
        have nb : w≠pin b := fun z=>ns (z ▸ privatePin b hb)
        simp [inputs a v w hw,inputs b v w hw,na,nb]
      have outside := outside51 H (V a v) (V b v) agreeRaw (fun j hj h => by
        rw [step a v j hj,step b v j hj,List.map_congr_left h])
        (fun w hw => (large a v w hw).trans (large b v w hw).symm)
      have entrySame {w : Nat} (hw : w∈E) : V a v w=V b v w := by
        obtain ⟨less,ns,nd⟩ := H.entries w hw
        exact outside w ns (fun i=> (nd i).elim) (fun le=> (Nat.not_le_of_gt less le).elim)
      obtain ⟨state,ab,bb⟩ : ∃ t : Bool,(∀ w∈E,V a v w=t) ∧ ∀ w∈E,V b v w=t := by
        by_cases ex : E.Nonempty
        · obtain ⟨w,hw⟩ := ex
          refine ⟨V a v w,?_,?_⟩
          · intro t ht
            rw [Finset.card_le_one.mp H.one t ht w hw]
          · intro t ht
            rw [Finset.card_le_one.mp H.one t ht w hw,entrySame hw]
        · exact ⟨false,fun w hw=>(ex ⟨w,hw⟩).elim,fun w hw=>(ex ⟨w,hw⟩).elim⟩
      have base (q : Fin n) (w : Nat) (hw : w∈S) : V q v w=decide (w=pin q) := by
        have otherNe : w≠other v := fun en => unmarked v nv (en ▸ hw)
        simp [inputs q v w (H.small w hw),otherNe]
      have topA := cutMatches51 H (V a v) state (base a) ab (step a v) (N+top) (Or.inr (Or.inl itop))
      have topB := cutMatches51 H (V b v) state (base b) bb (step b v) (N+top) (Or.inr (Or.inl itop))
      have topAgree := topA.trans ((same eqcode state).trans topB.symm)
      apply (Finset.mem_filter.mp hv).2
      exact (result a v).symm.trans ((outside _ H.outS H.outD (fun _=>topAgree)).trans (result b v))
    have low := distance a b ne
    have up := Finset.card_le_card subset
    omega
  have small : A.image code ⊆ Finset.range (2+E.card) := by
    intro j hj
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (cap a)
  have cnt := Finset.card_le_card small
  simpa [Finset.card_image_of_injOn inj] using cnt

end PEqualNP.Outside.L_meta_25807_aux.Leaves.Profile

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves
open PEqualNP.Outside.L_meta_25807_aux.Leaves.Profile in
theorem cap51 :
∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
  entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
  (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
    w ∉ sources ∧ (inside w → w = raw + top)) →
  C.output ∉ sources → (inside C.output → C.output = raw + top) →
  (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card) := by
  intro n m d G C R B region entry top raw sources inside gate farR farB back rep kept topMem one ext gates privateReads outputRaw outputGate
  classical
  let row := fun u : Fin n => u.val
  let col := fun v : Fin m => n+v.val
  have containsRow (u : Fin n) : row u∈sources ↔ u∈R := by
    constructor
    · intro hu
      rcases Finset.mem_union.mp hu with h|h
      · obtain ⟨q,hq,eqn⟩ := Finset.mem_image.mp h
        exact (Fin.ext eqn : q=u) ▸ hq
      · obtain ⟨q,_,eqn⟩ := Finset.mem_image.mp h
        change n+q.val=u.val at eqn
        omega
    · exact fun hu=>Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
  have containsCol (v : Fin m) : col v∈sources ↔ v∈B := by
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with h|h
      · obtain ⟨q,_,eqn⟩ := Finset.mem_image.mp h
        change q.val=n+v.val at eqn
        omega
      · obtain ⟨q,hq,eqn⟩ := Finset.mem_image.mp h
        change n+q.val=n+v.val at eqn
        exact (Fin.ext (Nat.add_left_cancel eqn) : q=v) ▸ hq
    · exact fun hv=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  have small : ∀ w∈sources,w<raw := by
    intro w h
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
      change q.val<n+m; omega
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
      change n+q.val<n+m; omega
  have H : Region51 raw C sources region entry top :=
    ⟨back,small,kept,topMem,one,ext,gates,privateReads,outputRaw,outputGate⟩
  let V := fun (u : Fin n) (v : Fin m) => Wire.val C (List.ofFn (Wire.pt n m (row u) (col v)))
  have inp (a : Fin n) (v : Fin m) (w : Nat) (hw : w<raw) :
      V a v w=(decide (w=row a) || decide (w=col v)) :=
    Wire.val_ofFn_lt C (Wire.pt n m (row a) (col v)) w hw
  have next (a : Fin n) (v : Fin m) (j : Nat) (hj : j<C.size) :
      V a v (raw+j)=(gate j).op.eval ((gate j).inputs.map (V a v)) :=
    Wire.val_gate_rb (by simp [raw]) hj (back j hj)
  have high (a : Fin n) (v : Fin m) (w : Nat) (hw : raw+C.size≤w) : V a v w=false :=
    Wire.val_ge (by simp [raw]) hw
  have out (a : Fin n) (v : Fin m) : V a v C.output=G a v := by
    have h := rep a v
    rw [Wire.oneEach_pt] at h
    exact h
  refine ⟨sideCap51 H R B G row col V farR (fun a=> (containsRow a).2)
      (fun v hv h=>hv ((containsCol v).1 h)) inp next high out,?_⟩
  apply sideCap51 H B R (fun v a=>G a v) col row (fun v a=>V a v) farB
      (fun v=>(containsCol v).2) (fun a ha h=>ha ((containsRow a).1 h))
  · intro v a w l
    rw [inp a v w l,Bool.or_comm]
  · exact fun v a => next a v
  · exact fun v a => high a v
  · exact fun v a => out a v

end PEqualNP.Outside.L_meta_25807_aux.Leaves

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def nodes (N:Nat) (region S:Finset Nat) := S ∪ region.image (fun j=>N+j)
def edge (N:Nat) (C:Circuit) (region:Finset Nat) (w z:Nat) : Prop :=
  ∃ j∈region,z=N+j ∧ w∈(gateAt C j).inputs
abbrev reach (N:Nat) (C:Circuit) (region:Finset Nat) := Relation.ReflTransGen (edge N C region)
noncomputable def subsetAt (N:Nat) (C:Circuit) (region S:Finset Nat) (top:Nat) : Finset Nat := by
  classical exact S.filter (fun w=>reach N C region w top)
structure Frame (N:Nat) (C:Circuit) (region S entries:Finset Nat) (root:Nat) : Prop where
  low : ∀w∈S,w<N
  back : ReadsBack N C
  reg : region ⊆ Finset.range C.size
  rootIn : root∈nodes N region S
  entryOut : ∀e∈entries,e∉nodes N region S
  entryRead : ∀e∈entries,readsIn C region e=1
  shape : ∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧
    ∀ w∈(gateAt C j).inputs,w∈nodes N region S ∨ w∈entries
  rootZero : readsIn C region root=0
  priv : ∀w∈nodes N region S,w≠root →
    readsIn C region w=1 ∧ readsIn C (Finset.range C.size) w=1 ∧ C.output≠w

end PEqualNP.Outside.L_meta_25807_aux.Leaves

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {reg S X : Finset Nat} {root : Nat}
variable (F : Frame N C reg S X root)
include F
lemma edge_lt {u v:Nat} (e:edge N C reg u v) : u<v := by
  obtain ⟨j,hj,rfl,hit⟩:=e
  exact F.back j (Finset.mem_range.mp (F.reg hj)) u hit
lemma reach_le {u v:Nat} (h:reach N C reg u v) : u≤v := by
  induction h with
  | refl => rfl
  | tail _ e ih => exact ih.trans (Nat.le_of_lt (edge_lt F e))
lemma reader_le_one {j w:Nat} (hj:j∈reg) (hw:w∈(gateAt C j).inputs) : readsIn C reg w≤1 := by
  rcases (F.shape j hj).2.2 w hw with inside|ent
  · by_cases eq:w=root
    · simp [eq,F.rootZero]
    · exact Nat.le_of_eq (F.priv w inside eq).1
  · exact Nat.le_of_eq (F.entryRead w ent)
lemma succUnique {u v w:Nat} (h:edge N C reg u v) (h':edge N C reg u w) : v=w := by
  obtain ⟨i,hi,rfl,iu⟩:=h;obtain ⟨j,hj,rfl,ju⟩:=h'
  by_contra neq
  have ij : i≠j:=by omega
  have le:=Finset.add_le_sum (f:=fun k=>(gateAt C k).inputs.count u) (fun _ _=>Nat.zero_le _) hi hj ij
  have h1:=List.count_pos_iff.mpr iu
  have h2:=List.count_pos_iff.mpr ju
  have h3:=reader_le_one F hi iu
  change _≤readsIn C reg u at le
  omega
lemma enters {u v : Nat} (e:edge N C reg u v) : ∃ j∈reg,v=N+j := by
  obtain ⟨j,h,rfl,_⟩:=e;exact ⟨j,h,rfl⟩
lemma reachesRoot {w:Nat} (hw:w∈nodes N reg S) : reach N C reg w root := by
  let M:=N+C.size
  have bl {i:Nat} (h:i∈nodes N reg S) : i<M := by
    rcases Finset.mem_union.mp h with hs|hi
    · have:=F.low _ hs;dsimp [M];omega
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi
      have:=Finset.mem_range.mp (F.reg hj);dsimp [M];omega
  suffices work : ∀ d,∀ i∈nodes N reg S, M-i=d → reach N C reg i root by exact work _ w hw rfl
  intro d;induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro i hi eq
    by_cases ir:i=root
    · subst i;exact .refl
    have one:readsIn C reg i=1 := (F.priv _ hi ir).1
    have hit:∃j∈reg,i∈(gateAt C j).inputs := by
      by_contra! nh
      have z:readsIn C reg i=0:=Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (nh j hj))
      omega
    obtain ⟨j,hj,m⟩:=hit
    have ed : edge N C reg i (N+j) := ⟨j,hj,rfl,m⟩
    have next:N+j∈nodes N reg S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    exact (ih (M-(N+j)) (by have:=edge_lt F ed;have:=bl next;omega) (N+j) next rfl).head ed

lemma siblingsApart {x y top u:Nat} (ex:edge N C reg x top) (ey:edge N C reg y top)
    (ne:x≠y) (px:reach N C reg u x) (py:reach N C reg u y) : False := by
  have impossible {a b:Nat} (aa:edge N C reg a top) (bb:edge N C reg b top)
      (nn:a≠b) (path:reach N C reg a b) : False := by
    rcases path.cases_head with eq|⟨c,ac,cb⟩
    · exact nn eq
    · have same:=succUnique F aa ac
      have :=reach_le F cb;have:=edge_lt F bb;omega
  have unique : Relator.RightUnique (edge N C reg) := by
    intro a b c x y;exact succUnique F x y
  rcases Relation.ReflTransGen.total_of_right_unique unique px py with xy|yx
  · exact impossible ex ey ne xy
  · exact impossible ey ex ne.symm yx
lemma rootLeaves : subsetAt N C reg S root=S := by
  classical
  ext w;constructor
  · exact fun h=>(Finset.mem_filter.mp h).1
  · intro h;exact Finset.mem_filter.mpr ⟨h,reachesRoot F (Finset.mem_union_left _ h)⟩
end PEqualNP.Outside.L_meta_25807_aux.Leaves

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {reg S X : Finset Nat} {root : Nat}
variable (F : Frame N C reg S X root)
include F
private lemma splitNode (top:Nat) :
    (subsetAt N C reg S top).card≤1 ∨
    ∃ x y : Nat, x≠y ∧ top∈nodes N reg S ∧ edge N C reg x top ∧ edge N C reg y top ∧
      (subsetAt N C reg S top).card≤(subsetAt N C reg S x).card+(subsetAt N C reg S y).card := by
  classical
  by_cases gate : ∃ j∈reg,top=N+j
  · right
    obtain ⟨j,hj,rfl⟩:=gate
    obtain ⟨x,y,eq⟩:=List.length_eq_two.mp (F.shape j hj).2.1
    have hitx : x∈(gateAt C j).inputs := by simp [eq]
    have hity : y∈(gateAt C j).inputs := by simp [eq]
    have ne:x≠y := by
      intro e;subst y
      have le:=Finset.single_le_sum (f:=fun k=>(gateAt C k).inputs.count x) (fun _ _=>Nat.zero_le _) hj
      change (gateAt C j).inputs.count x≤readsIn C reg x at le
      have lim:=reader_le_one F hj hitx
      simp [eq] at le;omega
    refine ⟨x,y,ne,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩),⟨j,hj,rfl,hitx⟩,⟨j,hj,rfl,hity⟩,?_⟩
    apply le_trans (b:=((subsetAt N C reg S x) ∪ (subsetAt N C reg S y)).card) _ (Finset.card_union_le _ _)
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hs,p⟩:=Finset.mem_filter.mp hw
    rcases p.cases_tail with same|⟨v,pv,i,hi,ii,m⟩
    · have:=F.low w hs;omega
    · have ij:i=j:=by omega
      subst i
      rw [eq] at m
      rcases (by simpa using m : v=x ∨ v=y) with rfl|rfl
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs,pv⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs,pv⟩)
  · left;apply Finset.card_le_one.mpr
    intro a ha b hb
    have eqtop (w:Nat) (h:w∈subsetAt N C reg S top) : w=top := by
      have p:reach N C reg w top := (Finset.mem_filter.mp h).2
      rcases p.cases_tail with eq|⟨v,_,e⟩
      · exact eq.symm
      · exact (gate (enters F e)).elim
    exact (eqtop _ ha).trans (eqtop _ hb).symm
omit F in
private lemma below {a b : Nat} {T:Finset Nat} (e:edge N C reg a b) :
    subsetAt N C reg T a ⊆ subsetAt N C reg T b := by
  classical
  intro w hw;obtain ⟨h,p⟩:=Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨h,p.tail e⟩

lemma pureBounds (cap:∀top∈nodes N reg S,(subsetAt N C reg X top)=∅ →
    5≤(subsetAt N C reg S top).card → (subsetAt N C reg S top).card≤8 → False) :
    ∀top,(subsetAt N C reg X top)=∅ → (subsetAt N C reg S top).card≤4 := by
  intro t;induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro empty
    rcases splitNode F t with leaf|⟨x,y,ne,ht,ex,ey,le⟩
    · omega
    · have bx:=ih x (edge_lt F ex) (Finset.subset_empty.mp (empty ▸ below (T:=X) ex))
      have by':=ih y (edge_lt F ey) (Finset.subset_empty.mp (empty ▸ below (T:=X) ey))
      by_contra! hlarge
      exact cap t ht empty (by omega) (by omega)
lemma boundPure (cap:∀top∈nodes N reg S,(subsetAt N C reg X top)=∅ →
    5≤(subsetAt N C reg S top).card → (subsetAt N C reg S top).card≤8 → False)
    (empty:X=∅) : S.card≤4 := by
  have hx : subsetAt N C reg X root=∅ := by simp [subsetAt,empty]
  simpa [rootLeaves F] using pureBounds F cap root hx
lemma boundMixed (cardX:X.card≤1)
    (pureCap:∀top∈nodes N reg S,(subsetAt N C reg X top)=∅ →
      5≤(subsetAt N C reg S top).card → (subsetAt N C reg S top).card≤8 → False)
    (mixCap:∀top∈nodes N reg S,7≤(subsetAt N C reg S top).card →
      (subsetAt N C reg S top).card≤10 → False) : S.card≤6 := by
  classical
  suffices all : ∀t,(subsetAt N C reg S t).card≤6 by simpa [rootLeaves F] using all root
  intro t;induction t using Nat.strong_induction_on with
  | ind t ih =>
    rcases splitNode F t with leaf|⟨x,y,ne,ht,ex,ey,le⟩
    · omega
    · have bx:=ih x (edge_lt F ex);have by':=ih y (edge_lt F ey)
      have either : subsetAt N C reg X x=∅ ∨ subsetAt N C reg X y=∅ := by
        by_contra! h
        obtain ⟨a,ha⟩:=h.1
        obtain ⟨b,hb⟩:=h.2
        obtain ⟨ax,ap⟩:=Finset.mem_filter.mp ha
        obtain ⟨bx,bp⟩:=Finset.mem_filter.mp hb
        have ab:=Finset.card_le_one.mp cardX a ax b bx;subst b
        exact siblingsApart F ex ey ne ap bp
      by_contra! large
      apply mixCap t ht (by omega)
      rcases either with h|h
      · have:=pureBounds F pureCap x h;omega
      · have:=pureBounds F pureCap y h;omega
end PEqualNP.Outside.L_meta_25807_aux.Leaves

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
abbrev srcSet {n m:Nat} (R:Finset (Fin n)) (B:Finset (Fin m)) :=
  R.image (fun u=>u.val) ∪ B.image (fun v=>n+v.val)
lemma srcCard {n m:Nat} (R:Finset (Fin n)) (B:Finset (Fin m)) :
    (srcSet R B).card=R.card+B.card := by
  classical
  unfold srcSet
  rw [Finset.card_union_of_disjoint,Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (show Function.Injective (fun v:Fin m=>n+v.val) from fun _ _ e=>Fin.ext (Nat.add_left_cancel e))]
  apply Finset.disjoint_left.mpr
  intro w hu hv
  obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp hu
  obtain ⟨v,_,e⟩:=Finset.mem_image.mp hv
  have:=u.isLt;omega
lemma srcLow {n m:Nat} (R:Finset (Fin n)) (B:Finset (Fin m)) (w:Nat) (hw:w∈srcSet R B) : w<n+m := by
  rcases Finset.mem_union.mp hw with a|b
  · obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp a;have:=u.isLt;omega
  · obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp b;have:=v.isLt;omega

def WindowCap {N:Nat} (C:Circuit) (reg S X:Finset Nat) (d:Nat) : Prop :=
  ∀top∈nodes N reg S,
    let l:=(subsetAt N C reg S top).card
    let e:=(subsetAt N C reg X top).card
    e≤1 → 2+e<d → l<2*d → l≤2*(2+e)

lemma pure59 {N root : Nat} {C:Circuit} {reg S:Finset Nat} (F:Frame N C reg S ∅ root)
    (cap:WindowCap (N:=N) C reg S ∅ 5) : S.card≤4 := by
  apply boundPure F _ rfl
  intro t ht empty low hi
  have val:=cap t ht
  dsimp only at val;rw [empty,Finset.card_empty] at val;omega
lemma mixed62 {N root e : Nat} {C:Circuit} {reg S:Finset Nat} (F:Frame N C reg S {e} root)
    (cap:WindowCap (N:=N) C reg S {e} 6) : S.card≤6 := by
  apply boundMixed F (by simp)
  · intro t ht empty low hi
    have val:=cap t ht
    dsimp only at val;rw [empty,Finset.card_empty] at val;omega
  · intro t ht low hi
    classical
    have le : (subsetAt N C reg {e} t).card≤1 := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_singleton e).le
    have val:=cap t ht
    dsimp only at val;omega

end PEqualNP.Outside.L_meta_25807_aux.Leaves


namespace PEqualNP.Outside.L_meta_25807_aux.Leaves
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def gateSubset (N : Nat) (C : Circuit) (region : Finset Nat) (top : Nat) : Finset Nat := by
  classical exact region.filter (fun j => reach N C region (N+j) top)

private theorem walk_le {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {x y : Nat} (h : reach N C P x y) : x≤y := by
  induction h with
  | refl => exact le_rfl
  | tail _ e ih =>
    obtain ⟨j,hj,rfl,inp⟩:=e
    exact ih.trans (Nat.le_of_lt (F.back j (Finset.mem_range.mp (F.reg hj)) _ inp))

private theorem first_observer {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {w top : Nat} (inW : w∈nodes N P S)
    (path : reach N C P w top) (notTop : w≠top) :
    C.output≠w ∧ ∀j<C.size,w∈(gateAt C j).inputs → j∈gateSubset N C P top := by
  classical
  obtain ⟨v,edge,rest⟩ := path.cases_head.resolve_left notTop
  obtain ⟨i,hi,rfl,hit⟩ := edge
  have count := List.count_pos_iff.mpr hit
  have sub : (gateAt C i).inputs.count w ≤ readsIn C P w :=
    Finset.single_le_sum (fun l _ => Nat.zero_le ((gateAt C l).inputs.count w)) hi
  have nr : w≠root := by
    intro eq
    subst w
    rw [F.rootZero] at sub
    omega
  obtain ⟨_,one,out⟩ := F.priv w inW nr
  refine ⟨out,?_⟩
  intro j hj readJ
  have ji : j=i := by
    by_contra ne
    have cnt2 := List.count_pos_iff.mpr readJ
    have both := Finset.add_le_sum (f:=fun l => (gateAt C l).inputs.count w) (fun _ _=>Nat.zero_le _)
      (Finset.mem_range.mpr hj) (F.reg hi) ne
    change _ ≤ readsIn C (Finset.range C.size) w at both
    omega
  subst j
  exact Finset.mem_filter.mpr ⟨hi,rest⟩

theorem subtree_boundary {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {top : Nat} (member : top∈nodes N P S) (large : N≤top) :
    let P' := gateSubset N C P top
    let S' := subsetAt N C P S top
    let E' := subsetAt N C P E top
    let inside := fun w => N≤w ∧ w-N∈P'
    P' ⊆ Finset.range C.size ∧ top-N∈P' ∧
    (∀ e∈E', e<top ∧ e∉S' ∧ ¬inside e) ∧
    (∀ k∈P', ((gateAt C k).op=.and ∨ (gateAt C k).op=.or) ∧
      ∀w∈(gateAt C k).inputs,w∈S' ∨ inside w ∨ w∈E') ∧
    (∀ k<C.size, k∉P' → ∀w∈(gateAt C k).inputs, w∉S' ∧ (inside w → w=top)) ∧
    C.output∉S' ∧ (inside C.output → C.output=top) := by
  classical
  dsimp only
  have in_orig {w : Nat} (h : N≤w ∧ w-N∈gateSubset N C P top) :
      w∈nodes N P S ∧ reach N C P w top := by
    obtain ⟨lo,hw⟩:=h
    obtain ⟨hp,way⟩:=Finset.mem_filter.mp hw
    have eq : N+(w-N)=w:=by omega
    exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,hp,eq⟩),eq ▸ way⟩
  have raw_prop {w : Nat} (h : w∈subsetAt N C P S top) :
      w∈nodes N P S ∧ reach N C P w top ∧ w≠top := by
    obtain ⟨hs,path⟩:=Finset.mem_filter.mp h
    exact ⟨Finset.mem_union_left _ hs,path,ne_of_lt ((F.low _ hs).trans_le large)⟩
  have idx : top-N∈P := by
    rcases Finset.mem_union.mp member with hs | hg
    · have := F.low top hs;omega
    · obtain ⟨j,hj,eq⟩:=Finset.mem_image.mp hg
      exact (show top-N=j by omega) ▸ hj
  refine ⟨fun _ h=>F.reg (Finset.mem_filter.mp h).1,
    Finset.mem_filter.mpr ⟨idx,by rw [Nat.add_sub_of_le large]⟩,?_,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨inE,path⟩:=Finset.mem_filter.mp he
    have no := F.entryOut e inE
    exact ⟨lt_of_le_of_ne (walk_le F path) (fun eq=>no (eq ▸ member)),
      fun hs=>no (raw_prop hs).1,fun hi=>no (in_orig hi).1⟩
  · intro j hj
    obtain ⟨occurs,path⟩:=Finset.mem_filter.mp hj
    obtain ⟨op,_,inputs⟩:=F.shape j occurs
    refine ⟨op,?_⟩
    intro w hit
    have way : reach N C P w top := path.head ⟨j,occurs,rfl,hit⟩
    rcases inputs w hit with orig | ent
    · rcases Finset.mem_union.mp orig with src | g
      · exact Or.inl (Finset.mem_filter.mpr ⟨src,way⟩)
      · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp g
        refine Or.inr (Or.inl ⟨by omega,?_⟩)
        rw [Nat.add_sub_cancel_left]
        exact Finset.mem_filter.mpr ⟨hk,way⟩
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨ent,way⟩))
  · intro j hj outside w read
    constructor
    · intro hs
      obtain ⟨inW,way,ne⟩:=raw_prop hs
      exact outside ((first_observer F inW way ne).2 j hj read)
    · intro hi
      by_contra ne
      obtain ⟨inW,way⟩:=in_orig hi
      exact outside ((first_observer F inW way ne).2 j hj read)
  · intro hs
    obtain ⟨inW,way,ne⟩:=raw_prop hs
    exact (first_observer F inW way ne).1 rfl
  · intro hi
    by_contra ne
    obtain ⟨inW,way⟩:=in_orig hi
    exact (first_observer F inW way ne).1 rfl

theorem leaves_one_of_low {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {top : Nat} (small : top<N) : (subsetAt N C P S top).card≤1 := by
  classical
  have sub : subsetAt N C P S top ⊆ {top} := by
    intro w hw;obtain ⟨_,path⟩:=Finset.mem_filter.mp hw
    rcases path.cases_tail with eq | ⟨v,_,j,hj,eq,_⟩
    · simpa using eq.symm
    · omega
  exact (Finset.card_le_card sub).trans (by simp)

end PEqualNP.Outside.L_meta_25807_aux.Leaves

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves
def Gap51 : Prop :=
∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
  entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
  (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
    w ∉ sources ∧ (inside w → w = raw + top)) →
  C.output ∉ sources → (inside C.output → C.output = raw + top) →
  (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card)
end PEqualNP.Outside.L_meta_25807_aux.Leaves

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def sourceIds {n m : Nat} (R : Finset (Fin n)) (B : Finset (Fin m)) : Finset Nat :=
  R.image Fin.val ∪ B.image (fun v=>n+v.val)

theorem sourceCard {n m : Nat} (R : Finset (Fin n)) (B : Finset (Fin m)) :
    (sourceIds R B).card = R.card+B.card := by
  classical
  have dis : Disjoint (R.image Fin.val) (B.image (fun v=>n+v.val)) := by
    apply Finset.disjoint_left.mpr
    intro w hw hb
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨v,hv,e⟩:=Finset.mem_image.mp hb
    have:=u.isLt;omega
  unfold sourceIds
  rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (fun _ _ e=>Fin.ext (Nat.add_left_cancel e))]

theorem forbiddenWindow {n m d root : Nat} {G : Fin n → Fin m → Bool} {C : Circuit}
    {R : Finset (Fin n)} {B : Finset (Fin m)} {region entries : Finset Nat}
    (cap : Gap51)
    (dr : ∀ a b : Fin n, a≠b → d≤(Finset.univ.filter (fun col=>G a col≠G b col)).card)
    (dc : ∀ a b : Fin m, a≠b → d≤(Finset.univ.filter (fun row=>G row a≠G row b)).card)
    (rep : Represents G C) (F : Frame (n+m) C region (sourceIds R B) entries root)
    {top : Nat} (ht : top∈nodes (n+m) region (sourceIds R B))
    (one : (subsetAt (n+m) C region entries top).card≤1)
    (narrow : 2+(subsetAt (n+m) C region entries top).card<d)
    (window : (subsetAt (n+m) C region (sourceIds R B) top).card<2*d) :
    (subsetAt (n+m) C region (sourceIds R B) top).card ≤
      2*(2+(subsetAt (n+m) C region entries top).card) := by
  classical
  let N:=n+m
  let S:=sourceIds R B
  let P' := gateSubset N C region top
  let E' := subsetAt N C region entries top
  let A := R.filter (fun u => reach N C region u.val top)
  let H := B.filter (fun v => reach N C region (n+v.val) top)
  have ids : sourceIds A H = subsetAt N C region S top := by
    ext w
    simp only [sourceIds, A, H, S,subsetAt,Finset.mem_filter,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro (⟨u,⟨hu,way⟩,rfl⟩ | ⟨v,⟨hv,way⟩,rfl⟩)
      · exact ⟨Or.inl ⟨u,hu,rfl⟩,way⟩
      · exact ⟨Or.inr ⟨v,hv,rfl⟩,way⟩
    · rintro ⟨(⟨u,hu,rfl⟩ | ⟨v,hv,rfl⟩),way⟩
      · exact Or.inl ⟨u,⟨hu,way⟩,rfl⟩
      · exact Or.inr ⟨v,⟨hv,way⟩,rfl⟩
  have card : (subsetAt N C region S top).card = A.card+H.card := by rw [←ids,sourceCard]
  by_cases inside : N≤top
  · obtain ⟨sub,topIn,ent,op,out,privateR,privateG⟩:=subtree_boundary F ht inside
    have eq : N+(top-N)=top := Nat.add_sub_of_le inside
    have rule := cap n m d G C A H P' E' (top-N) dr dc F.back rep sub topIn one
    change (∀w∈E', w<N+(top-N) ∧ w∉sourceIds A H ∧ ¬(N≤w ∧ w-N∈P')) → _ at rule
    have answer := rule (by simpa only [eq,ids] using ent)
      (by
        change ∀k∈P', _ ∧ ∀w∈(gateAt C k).inputs,w∈sourceIds A H ∨ (N≤w ∧ w-N∈P') ∨ w∈E'
        rw [ids];exact op)
      (by
        change ∀k<C.size,k∉P' → ∀w∈(gateAt C k).inputs,w∉sourceIds A H ∧ ((N≤w ∧ w-N∈P') → w=N+(top-N))
        rw [ids,eq];exact out)
      (by change C.output∉sourceIds A H;rw [ids];exact privateR)
      (by change (N≤C.output ∧ C.output-N∈P') → C.output=N+(top-N);rw [eq];exact privateG)
    obtain ⟨bsmall,asmall⟩ := answer
    change H.card<d → A.card≤2+E'.card at bsmall
    change A.card<d → H.card≤2+E'.card at asmall
    change 2+E'.card<d at narrow
    change (subsetAt N C region S top).card<2*d at window
    change (subsetAt N C region S top).card≤2*(2+E'.card)
    omega
  · have small:=leaves_one_of_low F (top:=top) (by omega)
    omega
end PEqualNP.Outside.L_meta_25807_aux.Leaves

namespace PEqualNP.Outside.L_meta_25807_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def sharedRaw (N : ℕ) (C : Circuit) := (Finset.range N).filter (fun i => 2 ≤ Active C i)

theorem combined (N : ℕ) (C : Circuit) (shape : Partition.shapes69 C) :
    (sharedRaw N C).card + 2 * Partition.exits69 N C + 4 * Partition.entries69 N C ≤ 12 * budget N C := by
  classical
  let X := Finset.range C.size \ Partition.ordinary N C
  let J := X.image (fun j => N + j)
  let R := sharedRaw N C
  let S := Partition.special N C
  have lower : R ∪ J ⊆ S := by
    intro w hw
    rcases Finset.mem_union.mp hw with raw | gate
    · obtain ⟨small, reads⟩ := Finset.mem_filter.mp raw
      have le := Finset.mem_range.mp small
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), reads⟩)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp gate
      obtain ⟨mem, absent⟩ := Finset.mem_sdiff.mp hj
      by_contra no
      exact absent (Finset.mem_filter.mpr ⟨mem, no⟩)
  have dis : Disjoint R J := by
    apply Finset.disjoint_left.mpr
    intro w raw gate
    have low : w < N := Finset.mem_range.mp (Finset.mem_filter.mp raw).1
    obtain ⟨j, _, eq⟩ := Finset.mem_image.mp gate
    change N + j = w at eq; omega
  have together := (Finset.card_le_card lower).trans (special_count N C)
  have inj : Function.Injective (fun j : ℕ => N + j) := fun _ _ eq => Nat.add_left_cancel eq
  rw [Finset.card_union_of_disjoint dis, show J.card = X.card from Finset.card_image_of_injective _ inj] at together
  have exits : Partition.exits69 N C ≤ 2 * X.card := by
    change (∑ j ∈ X, (gateAt C j).inputs.countP (fun w => decide (w ∉ S))) ≤ _
    calc
      _ ≤ ∑ _j ∈ X, 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have len : j < C.gates.length := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
        have gm : gateAt C j ∈ C.gates := by rw [gateAt, List.getD_eq_getElem _ _ len]; exact List.getElem_mem len
        have cap : (gateAt C j).inputs.length ≤ 2 := by rcases shape _ gm with h | h <;> omega
        exact (List.countP_le_length ..).trans cap
      _ = _ := by simp [Nat.mul_comm]
  have entries := (slot_limits N C shape).2
  change R.card + _ + _ ≤ _
  omega

theorem marked_union_one (L : List (Finset ℕ)) (H : Finset ℕ)
    (separate : L.Pairwise Disjoint) (small : ∀ S ∈ L, S.card ≤ 2 + (S ∩ H).card) :
    (L.toFinset.biUnion id).card ≤ 2 * L.length + ((L.toFinset.biUnion id) ∩ H).card := by
  classical
  induction L with
  | nil => simp
  | cons S l ih =>
    obtain ⟨bySet, rest⟩ := List.pairwise_cons.mp separate
    have bound := small S (by simp)
    have tail := ih rest (fun t ht => small t (by simp [ht]))
    let A := l.toFinset.biUnion id
    have dis : Disjoint S A := by
      apply Finset.disjoint_left.mpr
      intro w ws wa
      obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp wa
      exact Finset.disjoint_left.mp (bySet t (List.mem_toFinset.mp ht)) ws hit
    have di : Disjoint (S ∩ H) (A ∩ H) := by
      apply Finset.disjoint_left.mpr
      intro w hs ha
      exact Finset.disjoint_left.mp dis (Finset.mem_inter.mp hs).1 (Finset.mem_inter.mp ha).1
    rw [List.toFinset_cons, Finset.biUnion_insert, List.length_cons]
    change (S ∪ A).card ≤ 2 * (l.length + 1) + ((S ∪ A) ∩ H).card
    rw [Finset.card_union_of_disjoint dis, Finset.union_inter_distrib_right, Finset.card_union_of_disjoint di]
    change A.card ≤ 2 * l.length + (A ∩ H).card at tail
    omega

theorem counted_one (N : ℕ) (C : Circuit) (H : Finset ℕ) (shape : Partition.shapes69 C)
    (back : ReadsBack N C) (pos : 0 < C.size) (last : C.output + 1 = N + C.size)
    (live : ∀ j < C.size, j + 1 < C.size → 0 < Active C (N + j))
    (small : ∀ S E, S ⊆ Partition.once69 N C → E.card ≤ 1 → Partition.tree69 N C S E → S.card ≤ 2 + (S ∩ H).card) :
    used N C ≤ 12 * budget N C + 2 + H.card := by
  classical
  obtain ⟨P, Q, ex, en, dis, all, pureT, entryT⟩ := Partition.finish69 N C shape back pos last live
  have bounds : ∀ S ∈ P ++ Q, S.card ≤ 2 + (S ∩ H).card := by
    intro S mem
    have sub : S ⊆ Partition.once69 N C := by
      intro w hw
      have incl : w ∈ (P ++ Q).toFinset.biUnion id := Finset.mem_biUnion.mpr ⟨S, List.mem_toFinset.mpr mem, hw⟩
      rw [show (P ++ Q).toFinset.biUnion id = Partition.once69 N C from all] at incl
      exact incl
    rcases List.mem_append.mp mem with p | q
    · exact small S ∅ sub (by simp) (pureT S p).2
    · obtain ⟨_, b, h⟩ := entryT S q
      exact small S {b} sub (by simp) h
  have count := marked_union_one (P ++ Q) H dis bounds
  rw [show (P ++ Q).toFinset.biUnion id = Partition.once69 N C from all, List.length_append] at count
  have excess := combined N C shape
  have marked := Finset.card_le_card (Finset.inter_subset_right (s₁ := Partition.once69 N C) (s₂ := H))
  have split : used N C = (Partition.once69 N C).card + (sharedRaw N C).card := by
    unfold used Partition.once69 sharedRaw
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (if 1 ≤ Active C i then 1 else 0) = (if Active C i = 1 then 1 else 0) + (if 2 ≤ Active C i then 1 else 0)
    split_ifs <;> omega
  omega

end PEqualNP.Outside.L_meta_25807_aux

namespace PEqualNP.Outside.L_meta_25807_aux.Leaves.Profile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

private lemma gateMono51' {l : List Nat} {f g : Nat → Bool} {op : GateOp}
    (h : op = .and ∨ op = .or) (le : ∀ v ∈ l, f v = true → g v = true)
    (x : op.eval (l.map f) = true) : op.eval (l.map g) = true := by
  rcases h with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at x ⊢
    exact fun v hv => le v hv (x v hv)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at x ⊢
    obtain ⟨v, hv, hf⟩ := x
    exact ⟨v, hv, le v hv hf⟩

theorem cutOffLe51 {C : Circuit} {N lit top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (e : Bool) :
    ∀ w, w ∈ S ∨ inner51 N D w ∨ w ∈ E →
      cutVal51 C N E N e w = true → cutVal51 C N E lit e w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    rw [cutVal51, cutVal51]
    by_cases he : w ∈ E
    · simp only [if_pos he, imp_self]
    simp only [if_neg he]
    by_cases raw : w < N
    · simp only [if_pos raw]
      have hne : w ≠ N := Nat.ne_of_lt raw
      simp [hne]
    simp only [if_neg raw]
    have ins : inner51 N D w := (h.resolve_left (fun z => raw (H.small w z))).resolve_right he
    have jmem := ins.2
    refine gateMono51' (H.gates _ jmem).1 ?_
    intro v hv
    have lt := H.back (w - N) (Finset.mem_range.mp (H.kept jmem)) v hv
    have bound : v < w := by have := ins.1; omega
    simpa only [dif_pos bound] using ih v bound ((H.gates _ jmem).2 v hv)

theorem mono_order (l0 h0 l1 h1 l2 h2 : Bool)
    (m0 : l0 = true → h0 = true) (m1 : l1 = true → h1 = true) (m2 : l2 = true → h2 = true)
    (le1l : l0 = true → l1 = true) (le1h : h0 = true → h1 = true)
    (le2l : l0 = true → l2 = true) (le2h : h0 = true → h2 = true) :
    ((l1 ≠ l2 → l1 = l0) ∧ (h1 ≠ h2 → h1 = h0)) ∨
    ((l2 ≠ l1 → l2 = l0) ∧ (h2 ≠ h1 → h2 = h0)) := by
  cases l0 <;> cases h0 <;> cases l1 <;> cases h1 <;> cases l2 <;> cases h2 <;> simp_all

theorem sideAffordable51 {n m N top : Nat} {C : Circuit} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (A : Finset (Fin n)) (B : Finset (Fin m))
    (G : Fin n → Fin m → Bool) (off : Fin m → Bool)
    (pin : Fin n → Nat) (other : Fin m → Nat)
    (V : Fin n → Fin m → Nat → Bool) (V0 : Fin m → Nat → Bool)
    (privatePin : ∀ a ∈ A, pin a ∈ S) (unmarked : ∀ v ∉ B, other v ∉ S)
    (inputs : ∀ a v w, w < N → V a v w = (decide (w = pin a) || decide (w = other v)))
    (inputs0 : ∀ v w, w < N → V0 v w = decide (w = other v))
    (step : ∀ a v j, j < C.size → V a v (N + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V a v)))
    (step0 : ∀ v j, j < C.size → V0 v (N + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V0 v)))
    (large : ∀ a v w, N + C.size ≤ w → V a v w = false)
    (large0 : ∀ v w, N + C.size ≤ w → V0 v w = false)
    (result : ∀ a v, V a v C.output = G a v)
    (result0 : ∀ v, V0 v C.output = off v)
    (hB : B.card ≤ 3)
    {a₁ a₂ : Fin n} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) :
    (Finset.univ.filter (fun v => G a₁ v ≠ G a₂ v ∧ G a₁ v ≠ off v)).card ≤ 3 ∨
    (Finset.univ.filter (fun v => G a₂ v ≠ G a₁ v ∧ G a₂ v ≠ off v)).card ≤ 3 := by
  classical
  let sig (lit : Nat) (e : Bool) := cutVal51 C N E lit e (N + top)
  have itop : inner51 N D (N + top) := ⟨by omega, by simpa using H.topMem⟩
  have mon (lit : Nat) : sig lit false = true → sig lit true = true :=
    cutMono51 H (fun _ _ _ => rfl) _ (Or.inr (Or.inl itop))
  have offLe (lit : Nat) (e : Bool) : sig N e = true → sig lit e = true :=
    cutOffLe51 H e _ (Or.inr (Or.inl itop))
  have pair_sub (x y : Fin n) (hx : x ∈ A) (hy : y ∈ A)
      (hord : (sig (pin x) false ≠ sig (pin y) false → sig (pin x) false = sig N false) ∧
              (sig (pin x) true ≠ sig (pin y) true → sig (pin x) true = sig N true)) :
      (Finset.univ.filter (fun v => G x v ≠ G y v ∧ G x v ≠ off v)).card ≤ 3 := by
    have subset : Finset.univ.filter (fun v => G x v ≠ G y v ∧ G x v ≠ off v) ⊆ B := by
      intro v hv
      by_contra nv
      have agreeXY : ∀ w < N, w ∉ S → V x v w = V y v w := by
        intro w hw ns
        have nx : w ≠ pin x := fun z => ns (z ▸ privatePin x hx)
        have ny : w ≠ pin y := fun z => ns (z ▸ privatePin y hy)
        simp [inputs x v w hw, inputs y v w hw, nx, ny]
      have agreeX0 : ∀ w < N, w ∉ S → V x v w = V0 v w := by
        intro w hw ns
        have nx : w ≠ pin x := fun z => ns (z ▸ privatePin x hx)
        simp [inputs x v w hw, inputs0 v w hw, nx]
      have outXY := outside51 H (V x v) (V y v) agreeXY (fun j hj h => by
        rw [step x v j hj, step y v j hj, List.map_congr_left h])
        (fun w hw => (large x v w hw).trans (large y v w hw).symm)
      have outX0 := outside51 H (V x v) (V0 v) agreeX0 (fun j hj h => by
        rw [step x v j hj, step0 v j hj, List.map_congr_left h])
        (fun w hw => (large x v w hw).trans (large0 v w hw).symm)
      have entryXY {w : Nat} (hw : w ∈ E) : V x v w = V y v w := by
        obtain ⟨less, ns, nd⟩ := H.entries w hw
        exact outXY w ns (fun i => (nd i).elim) (fun le => (Nat.not_le_of_gt less le).elim)
      have entryX0 {w : Nat} (hw : w ∈ E) : V x v w = V0 v w := by
        obtain ⟨less, ns, nd⟩ := H.entries w hw
        exact outX0 w ns (fun i => (nd i).elim) (fun le => (Nat.not_le_of_gt less le).elim)
      obtain ⟨state, bx, by', b0⟩ :
          ∃ t : Bool, (∀ w ∈ E, V x v w = t) ∧ (∀ w ∈ E, V y v w = t) ∧ (∀ w ∈ E, V0 v w = t) := by
        by_cases ex : E.Nonempty
        · obtain ⟨w, hw⟩ := ex
          refine ⟨V x v w, ?_, ?_, ?_⟩
          · intro t ht; rw [Finset.card_le_one.mp H.one t ht w hw]
          · intro t ht; rw [Finset.card_le_one.mp H.one t ht w hw, entryXY hw]
          · intro t ht; rw [Finset.card_le_one.mp H.one t ht w hw, entryX0 hw]
        · exact ⟨false, fun w hw => (ex ⟨w, hw⟩).elim,
            fun w hw => (ex ⟨w, hw⟩).elim, fun w hw => (ex ⟨w, hw⟩).elim⟩
      have base (q : Fin n) (w : Nat) (hw : w ∈ S) : V q v w = decide (w = pin q) := by
        have otherNe : w ≠ other v := fun en => unmarked v nv (en ▸ hw)
        simp [inputs q v w (H.small w hw), otherNe]
      have base0 (w : Nat) (hw : w ∈ S) : V0 v w = decide (w = N) := by
        have otherNe : w ≠ other v := fun en => unmarked v nv (en ▸ hw)
        have ltN : w ≠ N := Nat.ne_of_lt (H.small w hw)
        simp [inputs0 v w (H.small w hw), otherNe, ltN]
      have topX := cutMatches51 H (V x v) state (base x) bx (step x v) (N + top) (Or.inr (Or.inl itop))
      have topY := cutMatches51 H (V y v) state (base y) by' (step y v) (N + top) (Or.inr (Or.inl itop))
      have top0 := cutMatches51 H (V0 v) state base0 b0 (step0 v) (N + top) (Or.inr (Or.inl itop))
      by_cases hxy : sig (pin x) state = sig (pin y) state
      · have topAgree : V x v (N + top) = V y v (N + top) := topX.trans (hxy.trans topY.symm)
        exact (Finset.mem_filter.mp hv).2.1
          ((result x v).symm.trans ((outXY _ H.outS H.outD (fun _ => topAgree)).trans (result y v)))
      · have hx0 : sig (pin x) state = sig N state := by
          cases state
          · exact hord.1 hxy
          · exact hord.2 hxy
        have topAgree0 : V x v (N + top) = V0 v (N + top) := topX.trans (hx0.trans top0.symm)
        exact (Finset.mem_filter.mp hv).2.2
          ((result x v).symm.trans ((outX0 _ H.outS H.outD (fun _ => topAgree0)).trans (result0 v)))
    exact (Finset.card_le_card subset).trans hB
  rcases mono_order (sig N false) (sig N true) (sig (pin a₁) false) (sig (pin a₁) true)
      (sig (pin a₂) false) (sig (pin a₂) true)
      (mon N) (mon (pin a₁)) (mon (pin a₂))
      (offLe (pin a₁) false) (offLe (pin a₁) true)
      (offLe (pin a₂) false) (offLe (pin a₂) true) with h1 | h2
  · exact Or.inl (pair_sub a₁ a₂ ha₁ ha₂ h1)
  · exact Or.inr (pair_sub a₂ a₁ ha₂ ha₁ h2)

end PEqualNP.Outside.L_meta_25807_aux.Leaves.Profile

namespace PEqualNP.Outside.L_meta_25807_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical

def onlyCol (n m : ℕ) (v : Fin m) : List Bool :=
  List.ofFn (Leaves.Profile.Wire.pt n m (n + m) (n + v.val))

def onlyRow (n m : ℕ) (u : Fin n) : List Bool :=
  List.ofFn (Leaves.Profile.Wire.pt n m u.val (n + m))

theorem onlyCol_length (n m : ℕ) (v : Fin m) : (onlyCol n m v).length = n + m := by
  simp [onlyCol]

theorem onlyRow_length (n m : ℕ) (u : Fin n) : (onlyRow n m u).length = n + m := by
  simp [onlyRow]

theorem onlyCol_getD (n m : ℕ) (v : Fin m) {i : ℕ} (hi : i < n + m) :
    (onlyCol n m v).getD i false = decide (i = n + v.val) := by
  rw [onlyCol, Leaves.Profile.Wire.ofFn_getD _ _ hi]
  simp [Leaves.Profile.Wire.pt, Nat.ne_of_lt hi]

theorem onlyRow_getD (n m : ℕ) (u : Fin n) {i : ℕ} (hi : i < n + m) :
    (onlyRow n m u).getD i false = decide (i = u.val) := by
  rw [onlyRow, Leaves.Profile.Wire.ofFn_getD _ _ hi]
  simp [Leaves.Profile.Wire.pt, Nat.ne_of_lt hi]

theorem unread_eq_offR {n m : ℕ} {G : Fin n → Fin m → Bool} {D : Circuit}
    (back : ReadsBack (n + m) D) (rep : Represents G D) (out : n + m ≤ D.output)
    {u : Fin n} (hu : Active D u.val = 0) (v : Fin m) :
    G u v = D.eval (onlyCol n m v) := by
  rw [← rep u v]
  apply observed_agree back _ _ (Normalize.oneEach_length u v) (onlyCol_length n m v) _ D.output out
  intro i hi hit
  have hne : i ≠ u.val := by intro h; subst h; omega
  rw [Normalize.oneEach_getD, onlyCol_getD n m v hi]
  simp [hne]

theorem unread_eq_offC {n m : ℕ} {G : Fin n → Fin m → Bool} {D : Circuit}
    (back : ReadsBack (n + m) D) (rep : Represents G D) (out : n + m ≤ D.output)
    {v : Fin m} (hv : Active D (n + v.val) = 0) (u : Fin n) :
    G u v = D.eval (onlyRow n m u) := by
  rw [← rep u v]
  apply observed_agree back _ _ (Normalize.oneEach_length u v) (onlyRow_length n m u) _ D.output out
  intro i hi hit
  have hne : i ≠ n + v.val := by intro h; subst h; omega
  rw [Normalize.oneEach_getD, onlyRow_getD n m u hi]
  simp [hne]

theorem used_add_unread (n m : ℕ) (D : Circuit) :
    used (n + m) D +
      (Finset.univ.filter (fun u : Fin n => Active D u.val = 0)).card +
      (Finset.univ.filter (fun v : Fin m => Active D (n + v.val) = 0)).card = n + m := by
  rw [used, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i => if Active D i = 0 then 1 else 0)]
  rw [Fin.sum_univ_eq_sum_range (fun j => if Active D (n + j) = 0 then 1 else 0)]
  rw [add_assoc, ← Finset.sum_range_add (fun i => if Active D i = 0 then 1 else 0) n m]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i ∈ Finset.range (n + m),
        ((if 1 ≤ Active D i then 1 else 0) + (if Active D i = 0 then 1 else 0)))
      = ∑ _i ∈ Finset.range (n + m), 1 := by
        apply Finset.sum_congr rfl
        intro i _; split_ifs <;> omega
    _ = n + m := by simp

def IsAffPair {i j : ℕ} (T : Fin i → Fin j → Bool) (off : Fin j → Bool) (a b : Fin i) : Prop :=
  a ≠ b ∧ (Finset.univ.filter (fun col => T a col ≠ T b col ∧ T a col ≠ off col)).card ≤ 3

def IsDisjPairs {i : ℕ} (F : Finset (Fin i × Fin i)) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, e ≠ f → e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2

theorem exists_marked_bank {i j h : ℕ} (T : Fin i → Fin j → Bool) (off : Fin j → Bool)
    (hdim : 2 * h + 2 ≤ i)
    (hbound : ∀ F : Finset (Fin i × Fin i),
      ((∀ e ∈ F, IsAffPair T off e.1 e.2) ∧ IsDisjPairs F) → F.card ≤ h)
    (U : Finset (Fin i)) (hUcard : U.card ≤ 1)
    (hUoff : ∀ u ∈ U, ∀ col : Fin j, T u col = off col) :
    ∃ H : Finset (Fin i), H.card + 2 * U.card ≤ 2 * h ∧
      ∀ a b : Fin i, a ≠ b → a ∉ U → b ∉ U → a ∉ H → b ∉ H → ¬ IsAffPair T off a b := by
  classical
  let Good (F : Finset (Fin i × Fin i)) : Prop :=
    (∀ e ∈ F, IsAffPair T off e.1 e.2 ∧ e.1 ∉ U ∧ e.2 ∉ U) ∧ IsDisjPairs F
  let P (k : ℕ) : Prop := ∃ F : Finset (Fin i × Fin i), Good F ∧ F.card = k
  have hP0 : P 0 := ⟨∅, ⟨by simp, by simp [IsDisjPairs]⟩, by simp⟩
  have hPle : ∀ F, Good F → F.card ≤ h := fun F hF => hbound F ⟨fun e he => (hF.1 e he).1, hF.2⟩
  let k := Nat.findGreatest P h
  have hkP : P k := Nat.findGreatest_spec (m := 0) (Nat.zero_le h) hP0
  obtain ⟨F, hF, hFcard⟩ := hkP
  have hFmax : ∀ F', Good F' → F'.card ≤ k := by
    intro F' hF'
    by_contra! hgt
    exact Nat.findGreatest_is_greatest hgt (hPle F' hF') ⟨F', hF', rfl⟩
  let H : Finset (Fin i) := F.image Prod.fst ∪ F.image Prod.snd
  have hHcard : H.card ≤ 2 * F.card := by
    have h1 := (Finset.card_union_le (F.image Prod.fst) (F.image Prod.snd)).trans
      (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    change H.card ≤ F.card + F.card at h1
    omega
  have hnotH : ∀ x : Fin i, x ∉ H → ∀ g ∈ F, x ≠ g.1 ∧ x ≠ g.2 := by
    intro x hx g hg
    exact ⟨fun eq => hx (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g, hg, eq.symm⟩)),
      fun eq => hx (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, hg, eq.symm⟩))⟩
  have hmax : ∀ a b : Fin i, a ≠ b → a ∉ U → b ∉ U → a ∉ H → b ∉ H → ¬ IsAffPair T off a b := by
    intro a b hab haU hbU haH hbH haff
    have hnotin : (a, b) ∉ F := fun h => (hnotH a haH (a, b) h).1 rfl
    have hgood' : Good (insert (a, b) F) := by
      refine ⟨?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | heF
        · exact ⟨haff, haU, hbU⟩
        · exact hF.1 e heF
      · intro e he f hf hef
        rcases Finset.mem_insert.mp he with rfl | heF <;>
        rcases Finset.mem_insert.mp hf with rfl | hfF
        · exact (hef rfl).elim
        · have ha := hnotH a haH f hfF
          have hb := hnotH b hbH f hfF
          exact ⟨ha.1, ha.2, hb.1, hb.2⟩
        · have ha := hnotH a haH e heF
          have hb := hnotH b hbH e heF
          exact ⟨ha.1.symm, hb.1.symm, ha.2.symm, hb.2.symm⟩
        · exact hF.2 e heF f hfF hef
    have hle := hFmax (insert (a, b) F) hgood'
    rw [Finset.card_insert_of_notMem hnotin] at hle
    omega
  refine ⟨H, ?_, hmax⟩
  by_cases hU0 : U = ∅
  · subst hU0
    have := hPle F hF
    simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero]
    omega
  · obtain ⟨u0, hu0⟩ := Finset.nonempty_iff_ne_empty.mpr hU0
    have hFlt : F.card + 1 ≤ h := by
      by_contra! hge
      have hFeq : F.card = h := by have := hPle F hF; omega
      have hcardIns : (insert u0 H).card < i := by
        have := Finset.card_insert_le u0 H
        omega
      have hexW : ∃ w : Fin i, w ∉ insert u0 H := by
        by_contra! hall
        have hsub : (Finset.univ : Finset (Fin i)) ⊆ insert u0 H := fun w _ => hall w
        have hle := Finset.card_le_card hsub
        simp only [Finset.card_univ, Fintype.card_fin] at hle
        omega
      obtain ⟨w, hw⟩ := hexW
      have hwu : u0 ≠ w := fun eq => hw (eq ▸ Finset.mem_insert_self u0 H)
      have hwH : w ∉ H := fun h => hw (Finset.mem_insert_of_mem h)
      have hnotin : (u0, w) ∉ F := fun h => (hnotH w hwH (u0, w) h).2 rfl
      have haff0 : IsAffPair T off u0 w := by
        refine ⟨hwu, ?_⟩
        have hempty : Finset.univ.filter (fun col => T u0 col ≠ T w col ∧ T u0 col ≠ off col) = ∅ := by
          ext col
          simp [hUoff u0 hu0 col]
        simp [hempty]
      have hle := hbound (insert (u0, w) F) ⟨?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hnotin] at hle
        omega
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | heF
        · exact haff0
        · exact (hF.1 e heF).1
      · intro e he f hf hef
        rcases Finset.mem_insert.mp he with rfl | heF <;>
        rcases Finset.mem_insert.mp hf with rfl | hfF
        · exact (hef rfl).elim
        · have hfU := hF.1 f hfF
          have hwf := hnotH w hwH f hfF
          exact ⟨fun eq => hfU.2.1 (eq ▸ hu0), fun eq => hfU.2.2 (eq ▸ hu0), hwf.1, hwf.2⟩
        · have heU := hF.1 e heF
          have hwe := hnotH w hwH e heF
          exact ⟨fun eq => heU.2.1 (eq.symm ▸ hu0), hwe.1.symm, fun eq => heU.2.2 (eq.symm ▸ hu0), hwe.2.symm⟩
        · exact hF.2 e heF f hfF hef
    omega

theorem piece_bound {n m : ℕ} (G : Fin n → Fin m → Bool) (D : Circuit)
    (hrowSep : ∀ a b : Fin n, a ≠ b → 6 ≤ (Finset.univ.filter (fun j => G a j ≠ G b j)).card)
    (hcolSep : ∀ a b : Fin m, a ≠ b → 6 ≤ (Finset.univ.filter (fun i => G i a ≠ G i b)).card)
    (back : ReadsBack (n + m) D) (rep : Represents G D)
    (H_R : Finset (Fin n)) (H_C : Finset (Fin m))
    (hmaxR : ∀ a b : Fin n, a ≠ b → Active D a.val ≠ 0 → Active D b.val ≠ 0 →
      a ∉ H_R → b ∉ H_R → ¬ IsAffPair G (fun v => D.eval (onlyCol n m v)) a b)
    (hmaxC : ∀ a b : Fin m, a ≠ b → Active D (n + a.val) ≠ 0 → Active D (n + b.val) ≠ 0 →
      a ∉ H_C → b ∉ H_C → ¬ IsAffPair (fun j i => G i j) (fun u => D.eval (onlyRow n m u)) a b)
    (S E : Finset ℕ) (hS_once : S ⊆ Partition.once69 (n + m) D) (hE : E.card ≤ 1)
    (htree : Partition.tree69 (n + m) D S E) :
    S.card ≤ 2 + (S ∩ (H_R.image Fin.val ∪ H_C.image (fun v => n + v.val))).card := by
  classical
  let H := H_R.image Fin.val ∪ H_C.image (fun v => n + v.val)
  by_cases hsmall : S.card ≤ 1
  · omega
  have hS_sub : S ⊆ Finset.range (n + m) := fun w hw => (Finset.mem_filter.mp (hS_once hw)).1
  obtain ⟨R, B, hRB_eq, hRB_card⟩ := raw_parts S hS_sub
  have hS_src : Leaves.srcSet R B = S := hRB_eq
  have hR_act : ∀ a ∈ R, Active D a.val ≠ 0 := by
    intro a ha
    have hw : a.val ∈ S := hRB_eq ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
    have h1 := (Finset.mem_filter.mp (hS_once hw)).2
    change Active D a.val = 1 at h1
    omega
  have hB_act : ∀ c ∈ B, Active D (n + c.val) ≠ 0 := by
    intro c hc
    have hw : n + c.val ∈ S := hRB_eq ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)
    have h1 := (Finset.mem_filter.mp (hS_once hw)).2
    change Active D (n + c.val) = 1 at h1
    omega
  have hmark_sub : (R ∩ H_R).card + (B ∩ H_C).card ≤ (S ∩ H).card := by
    let A := (R ∩ H_R).image Fin.val
    let K := (B ∩ H_C).image (fun c => n + c.val)
    have hsub : A ∪ K ⊆ S ∩ H := by
      intro w hw
      rw [← hRB_eq]
      rcases Finset.mem_union.mp hw with hl | hr
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
        obtain ⟨haR, haH⟩ := Finset.mem_inter.mp ha
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ haR),
           Finset.mem_union_left _ (Finset.mem_image_of_mem _ haH)⟩
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨hcB, hcH⟩ := Finset.mem_inter.mp hc
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hcB),
           Finset.mem_union_right _ (Finset.mem_image_of_mem _ hcH)⟩
    have hdisj : Disjoint A K := by
      apply Finset.disjoint_left.mpr
      intro w hl hr
      obtain ⟨a, _, eq1⟩ := Finset.mem_image.mp hl
      obtain ⟨c, _, eq2⟩ := Finset.mem_image.mp hr
      have := a.isLt; omega
    have hle := Finset.card_le_card hsub
    have hinjC : Function.Injective (fun c : Fin m => n + c.val) :=
      fun _ _ eq => Fin.ext (Nat.add_left_cancel eq)
    simpa only [Finset.card_union_of_disjoint hdisj, A, K,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ hinjC] using hle
  obtain ⟨region, root, hreg_ord, hroot_mem, hroot_zero, hE_prop, hgates, hpriv⟩ := htree
  have F : Leaves.Frame (n + m) D region (Leaves.srcSet R B) E root := by
    refine ⟨Leaves.srcLow R B, back,
      fun k hk => Finset.mem_range.mpr (Partition.ordinary_index69 (hreg_ord hk)),
      hS_src.symm ▸ hroot_mem,
      fun e he => hS_src.symm ▸ (hE_prop e he).1,
      fun e he => (hE_prop e he).2.2,
      fun j hj => ?_, hroot_zero,
      fun w hw hne => hpriv w (hS_src ▸ hw) hne⟩
    obtain ⟨hop, hlen, hin⟩ := hgates j hj
    exact ⟨hop, hlen, fun w hw => (hin w hw).imp_left (fun h => hS_src.symm ▸ h)⟩
  have hroot_ge : n + m ≤ root := by
    by_contra! hlt
    have h1 := Leaves.leaves_one_of_low F hlt
    rw [Leaves.rootLeaves F, hS_src] at h1
    omega
  have hRB_le6 : R.card + B.card ≤ 6 := by
    by_cases hE0 : E = ∅
    · subst hE0
      have hcap5 : Leaves.WindowCap (N := n + m) D region (Leaves.srcSet R B) ∅ 5 := fun t ht =>
        Leaves.forbiddenWindow Leaves.cap51
          (fun a b hab => le_trans (by omega) (hrowSep a b hab))
          (fun a b hab => le_trans (by omega) (hcolSep a b hab)) rep F ht
      have h4 := Leaves.pure59 F hcap5
      rw [Leaves.srcCard] at h4
      omega
    · have hE1 : E.card = 1 := by
        have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hE0)
        omega
      obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hE1
      have hcap6 : Leaves.WindowCap (N := n + m) D region (Leaves.srcSet R B) {e} 6 := fun t ht =>
        Leaves.forbiddenWindow Leaves.cap51 hrowSep hcolSep rep F ht
      have h6 := Leaves.mixed62 F hcap6
      rw [Leaves.srcCard] at h6
      exact h6
  let P' := Leaves.gateSubset (n + m) D region root
  let E' := Leaves.subsetAt (n + m) D region E root
  let top := root - (n + m)
  have htop_eq : n + m + top = root := Nat.add_sub_of_le hroot_ge
  have hE'_card : E'.card ≤ 1 := (Finset.card_le_card (Finset.filter_subset _ _)).trans hE
  obtain ⟨hP'_sub, htop_mem, hE'_props, hP'_gates, hP'_out, hout_src, hout_in⟩ :=
    Leaves.subtree_boundary F F.rootIn hroot_ge
  rw [Leaves.rootLeaves F] at hE'_props hP'_gates hP'_out hout_src
  have hcap := Leaves.cap51 n m 6 G D R B P' E' top hrowSep hcolSep back rep
    hP'_sub htop_mem hE'_card
    (by simpa only [htop_eq] using hE'_props)
    hP'_gates
    (by simpa only [htop_eq] using hP'_out)
    hout_src
    (by simpa only [htop_eq] using hout_in)
  have hR_le3 : R.card ≤ 3 := by omega
  have hB_le3 : B.card ≤ 3 := by omega
  have Hreg : Leaves.Profile.Region51 (n + m) D (Leaves.srcSet R B) P' E' top :=
    ⟨back, Leaves.srcLow R B, hP'_sub, htop_mem, hE'_card,
     by simpa only [htop_eq, Leaves.Profile.inner51] using hE'_props,
     hP'_gates,
     by simpa only [htop_eq, Leaves.Profile.inner51] using hP'_out,
     hout_src,
     by simpa only [htop_eq, Leaves.Profile.inner51] using hout_in⟩
  let row := fun u : Fin n => u.val
  let col := fun v : Fin m => n + v.val
  have containsRow (u : Fin n) : row u ∈ Leaves.srcSet R B ↔ u ∈ R := by
    constructor
    · intro hu
      rcases Finset.mem_union.mp hu with h | h
      · obtain ⟨q, hq, eqn⟩ := Finset.mem_image.mp h
        exact (Fin.ext eqn : q = u) ▸ hq
      · obtain ⟨q, _, eqn⟩ := Finset.mem_image.mp h
        change n + q.val = u.val at eqn; omega
    · exact fun hu => Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  have containsCol (v : Fin m) : col v ∈ Leaves.srcSet R B ↔ v ∈ B := by
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with h | h
      · obtain ⟨q, _, eqn⟩ := Finset.mem_image.mp h
        change q.val = n + v.val at eqn; omega
      · obtain ⟨q, hq, eqn⟩ := Finset.mem_image.mp h
        change n + q.val = n + v.val at eqn
        exact (Fin.ext (Nat.add_left_cancel eqn) : q = v) ▸ hq
    · exact fun hv => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  let V := fun (u : Fin n) (v : Fin m) =>
    Leaves.Profile.Wire.val D (List.ofFn (Leaves.Profile.Wire.pt n m (row u) (col v)))
  let V0R := fun (v : Fin m) => Leaves.Profile.Wire.val D (onlyCol n m v)
  let V0C := fun (u : Fin n) => Leaves.Profile.Wire.val D (onlyRow n m u)
  have inp (a : Fin n) (v : Fin m) (w : Nat) (hw : w < n + m) :
      V a v w = (decide (w = row a) || decide (w = col v)) :=
    Leaves.Profile.Wire.val_ofFn_lt D (Leaves.Profile.Wire.pt n m (row a) (col v)) w hw
  have inp0R (v : Fin m) (w : Nat) (hw : w < n + m) : V0R v w = decide (w = col v) := by
    dsimp only [V0R, onlyCol]
    rw [Leaves.Profile.Wire.val_ofFn_lt D (Leaves.Profile.Wire.pt n m (n + m) (n + v.val)) w hw]
    simp [Leaves.Profile.Wire.pt, col, Nat.ne_of_lt hw]
  have inp0C (u : Fin n) (w : Nat) (hw : w < n + m) : V0C u w = decide (w = row u) := by
    dsimp only [V0C, onlyRow]
    rw [Leaves.Profile.Wire.val_ofFn_lt D (Leaves.Profile.Wire.pt n m u.val (n + m)) w hw]
    simp [Leaves.Profile.Wire.pt, row, Nat.ne_of_lt hw]
  have nextV (a : Fin n) (v : Fin m) (j : Nat) (hj : j < D.size) :
      V a v (n + m + j) = (gateAt D j).op.eval ((gateAt D j).inputs.map (V a v)) :=
    Leaves.Profile.Wire.val_gate_rb (by simp) hj (back j hj)
  have next0R (v : Fin m) (j : Nat) (hj : j < D.size) :
      V0R v (n + m + j) = (gateAt D j).op.eval ((gateAt D j).inputs.map (V0R v)) :=
    Leaves.Profile.Wire.val_gate_rb (onlyCol_length n m v) hj (back j hj)
  have next0C (u : Fin n) (j : Nat) (hj : j < D.size) :
      V0C u (n + m + j) = (gateAt D j).op.eval ((gateAt D j).inputs.map (V0C u)) :=
    Leaves.Profile.Wire.val_gate_rb (onlyRow_length n m u) hj (back j hj)
  have highV (a : Fin n) (v : Fin m) (w : Nat) (hw : n + m + D.size ≤ w) : V a v w = false :=
    Leaves.Profile.Wire.val_ge (by simp) hw
  have high0R (v : Fin m) (w : Nat) (hw : n + m + D.size ≤ w) : V0R v w = false :=
    Leaves.Profile.Wire.val_ge (onlyCol_length n m v) hw
  have high0C (u : Fin n) (w : Nat) (hw : n + m + D.size ≤ w) : V0C u w = false :=
    Leaves.Profile.Wire.val_ge (onlyRow_length n m u) hw
  have outV (a : Fin n) (v : Fin m) : V a v D.output = G a v := by
    have h := rep a v
    rw [Leaves.Profile.Wire.oneEach_pt] at h
    exact h
  have hR_unmarked : (R \ H_R).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a₁ ha₁ a₂ ha₂
    by_contra hne
    obtain ⟨ha₁R, ha₁H⟩ := Finset.mem_sdiff.mp ha₁
    obtain ⟨ha₂R, ha₂H⟩ := Finset.mem_sdiff.mp ha₂
    rcases Leaves.Profile.sideAffordable51 Hreg R B G (fun v => D.eval (onlyCol n m v))
        row col V V0R (fun a => (containsRow a).2) (fun v hv h => hv ((containsCol v).1 h))
        inp inp0R nextV next0R highV high0R outV (fun _ => rfl) hB_le3 ha₁R ha₂R with h1 | h2
    · exact hmaxR a₁ a₂ hne (hR_act a₁ ha₁R) (hR_act a₂ ha₂R) ha₁H ha₂H ⟨hne, h1⟩
    · exact hmaxR a₂ a₁ (Ne.symm hne) (hR_act a₂ ha₂R) (hR_act a₁ ha₁R) ha₂H ha₁H ⟨Ne.symm hne, h2⟩
  have hB_unmarked : (B \ H_C).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro c₁ hc₁ c₂ hc₂
    by_contra hne
    obtain ⟨hc₁B, hc₁H⟩ := Finset.mem_sdiff.mp hc₁
    obtain ⟨hc₂B, hc₂H⟩ := Finset.mem_sdiff.mp hc₂
    rcases Leaves.Profile.sideAffordable51 Hreg B R (fun v u => G u v) (fun u => D.eval (onlyRow n m u))
        col row (fun v u => V u v) V0C (fun v => (containsCol v).2) (fun a ha h => ha ((containsRow a).1 h))
        (fun v a w hw => by rw [inp a v w hw, Bool.or_comm]) inp0C
        (fun v a => nextV a v) next0C (fun v a => highV a v) high0C
        (fun v a => outV a v) (fun _ => rfl) hR_le3 hc₁B hc₂B with h1 | h2
    · exact hmaxC c₁ c₂ hne (hB_act c₁ hc₁B) (hB_act c₂ hc₂B) hc₁H hc₂H ⟨hne, h1⟩
    · exact hmaxC c₂ c₁ (Ne.symm hne) (hB_act c₂ hc₂B) (hB_act c₁ hc₁B) hc₂H hc₁H ⟨Ne.symm hne, h2⟩
  have hR_split : R.card = (R \ H_R).card + (R ∩ H_R).card := (Finset.card_sdiff_add_card_inter R H_R).symm
  have hB_split : B.card = (B \ H_C).card + (B ∩ H_C).card := (Finset.card_sdiff_add_card_inter B H_C).symm
  change S.card ≤ 2 + (S ∩ H).card
  omega

end PEqualNP.Outside.L_meta_25807_aux

open PEqualNP.Outside.L_meta_25807_aux in
theorem PEqualNP.Outside.L_meta_25807 :
    ∀ (n m hr hc : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
  let bounded := fun (i j : ℕ) (T : Fin i → Fin j → Bool) (h : ℕ) =>
    ∀ (off : Fin j → Bool) (F : Finset (Fin i × Fin i)),
      ((∀ e ∈ F, e.1 ≠ e.2 ∧
        (Finset.univ.filter (fun col => T e.1 col ≠ T e.2 col ∧ T e.1 col ≠ off col)).card ≤ 3) ∧
      (∀ e ∈ F, ∀ f ∈ F, e ≠ f →
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)) → F.card ≤ h
  2*hr+2 ≤ n → 2*hc+2 ≤ m →
  (∀ a b : Fin n, a ≠ b → 6 ≤ (Finset.univ.filter (fun j => G a j ≠ G b j)).card) →
  (∀ a b : Fin m, a ≠ b → 6 ≤ (Finset.univ.filter (fun i => G i a ≠ G i b)).card) →
  bounded n m G hr → bounded m n (fun j i => G i j) hc →
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents G C →
    13 * (n+m) ≤ 12*C.size + 36 + 2*(hr+hc) := by
  classical
  intro n m hr hc G C
  dsimp only
  intro hhr hhc hrowSep hcolSep hboundR hboundC fan rep
  have hdiffR : DifferentRows G := by
    intro a b hab
    have hpos : 0 < (Finset.univ.filter (fun j => G a j ≠ G b j)).card := by
      have := hrowSep a b hab; omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    exact ⟨c, (Finset.mem_filter.mp hc).2⟩
  have hdiffC : DifferentCols G := by
    intro a b hab
    have hpos : 0 < (Finset.univ.filter (fun i => G i a ≠ G i b)).card := by
      have := hcolSep a b hab; omega
    obtain ⟨r, hr'⟩ := Finset.card_pos.mp hpos
    exact ⟨r, (Finset.mem_filter.mp hr').2⟩
  have horiz : ∃ a c d, G a c ≠ G a d := by
    have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by intro h; simp [Fin.ext_iff] at h
    obtain ⟨a, ha⟩ := hdiffC _ _ h01
    exact ⟨a, ⟨0, by omega⟩, ⟨1, by omega⟩, ha⟩
  have vert : ∃ a b c, G a c ≠ G b c := by
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by intro h; simp [Fin.ext_iff] at h
    obtain ⟨c, hc⟩ := hdiffR _ _ h01
    exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, c, hc⟩
  obtain ⟨D, hDsize, hDrep, hDback, hDshape, hDpos, hDlast, hDlive⟩ := normalized C fan rep horiz vert
  have hDout : n + m ≤ D.output := by omega
  have hbal := budget_eq D hDshape hDback hDpos hDlive
  let offR : Fin m → Bool := fun v => D.eval (onlyCol n m v)
  let offC : Fin n → Bool := fun u => D.eval (onlyRow n m u)
  let U_R : Finset (Fin n) := Finset.univ.filter (fun u => Active D u.val = 0)
  let U_C : Finset (Fin m) := Finset.univ.filter (fun v => Active D (n + v.val) = 0)
  have hUR_off : ∀ u ∈ U_R, ∀ v : Fin m, G u v = offR v := fun u hu v =>
    unread_eq_offR hDback hDrep hDout (Finset.mem_filter.mp hu).2 v
  have hUC_off : ∀ v ∈ U_C, ∀ u : Fin n, G u v = offC u := fun v hv u =>
    unread_eq_offC hDback hDrep hDout (Finset.mem_filter.mp hv).2 u
  have hUR_le1 : U_R.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hne
    obtain ⟨c, hc⟩ := hdiffR a b hne
    exact hc ((hUR_off a ha c).trans (hUR_off b hb c).symm)
  have hUC_le1 : U_C.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hne
    obtain ⟨r, hr'⟩ := hdiffC a b hne
    exact hr' ((hUC_off a ha r).trans (hUC_off b hb r).symm)
  obtain ⟨H_R, hHR_card, hHR_max⟩ := exists_marked_bank G offR hhr (hboundR offR) U_R hUR_le1 hUR_off
  obtain ⟨H_C, hHC_card, hHC_max⟩ := exists_marked_bank (fun j i => G i j) offC hhc (hboundC offC) U_C hUC_le1 hUC_off
  let H : Finset ℕ := H_R.image Fin.val ∪ H_C.image (fun v => n + v.val)
  have hH_card : H.card ≤ H_R.card + H_C.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  have hcnt := counted_one (n + m) D H hDshape hDback hDpos hDlast hDlive (fun S E hS_once hE htree =>
    piece_bound G D hrowSep hcolSep hDback hDrep H_R H_C
      (fun a b hab ha hb => hHR_max a b hab (by simp [U_R, ha]) (by simp [U_R, hb]))
      (fun a b hab ha hb => hHC_max a b hab (by simp [U_C, ha]) (by simp [U_C, hb]))
      S E hS_once hE htree)
  have hsplit := used_add_unread n m D
  change used (n + m) D + U_R.card + U_C.card = n + m at hsplit
  omega

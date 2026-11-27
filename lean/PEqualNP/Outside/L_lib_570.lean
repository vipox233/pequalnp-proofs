import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_570_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge_false (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma foldl_stepWire_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_stepWire_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · simp only [hi, ↓reduceIte]
        rw [foldl_stepWire_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp only [hi, ↓reduceIte]
        exact getD_ge_false w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

private def wireVal (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

private lemma eval_eq_wireVal (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = wireVal n C x C.output := rfl

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) {u : ℕ} (hu : u < n) :
    wireVal n C x u = x ⟨u, hu⟩ := by
  unfold wireVal
  rw [wires_eq_foldl]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  rw [foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by omega)]
  simp [List.getD_eq_getElem?_getD, hu]

private lemma wireVal_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : wireVal n C x u = false := by
  unfold wireVal
  rw [wires_eq_foldl]
  apply getD_ge_false
  rw [foldl_stepWire_length, List.length_ofFn]
  exact hu

private lemma wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (k : Fin C.gates.length) :
    wireVal n C x (n + k.val) =
      (C.gates[k.val]).op.eval ((C.gates[k.val]).inputs.map fun a =>
        if a < n + k.val then wireVal n C x a else false) := by
  unfold wireVal
  rw [wires_eq_foldl]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h := foldl_stepWire_getD_gate C.gates (List.ofFn x) k.val k.isLt
  rwa [hlen] at h

private def deps (n : ℕ) (C : Circuit) (k : Fin C.gates.length) : Finset ℕ :=
  match (C.gates[k.val]).op, (C.gates[k.val]).inputs with
  | GateOp.not, a :: _ => if a < n + k.val then {a} else ∅
  | GateOp.not, [] => ∅
  | _, ins => (ins.filter (fun a => a < n + k.val)).toFinset

private lemma deps_lt {n : ℕ} {C : Circuit} {k : Fin C.gates.length} {a : ℕ}
    (ha : a ∈ deps n C k) : a < n + k.val := by
  unfold deps at ha
  cases hop : (C.gates[k.val]).op <;> simp only [hop] at ha
  · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ha; exact ha.2
  · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ha; exact ha.2
  · cases hins : (C.gates[k.val]).inputs with
    | nil => simp [hins] at ha
    | cons a₀ rest =>
      simp only [hins] at ha
      split at ha
      · simp only [Finset.mem_singleton] at ha; subst ha; assumption
      · simp at ha
  · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ha; exact ha.2
  · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ha; exact ha.2

private lemma deps_card_not {n : ℕ} {C : Circuit} {k : Fin C.gates.length}
    (hnot : (C.gates[k.val]).op = GateOp.not) : (deps n C k).card ≤ 1 := by
  unfold deps
  rw [hnot]
  cases (C.gates[k.val]).inputs with
  | nil => simp
  | cons a rest =>
    dsimp only
    by_cases h : a < n + k.val <;> simp [h]

private lemma deps_card_le_two {n : ℕ} {C : Circuit} (hfit : FanInTwo C)
    (k : Fin C.gates.length) : (deps n C k).card ≤ 2 := by
  have hlen : (C.gates[k.val]).inputs.length ≤ 2 := (hfit _ (List.getElem_mem k.isLt)).2
  unfold deps
  cases hop : (C.gates[k.val]).op
  · dsimp only; exact le_trans (List.toFinset_card_le _) (le_trans (List.length_filter_le _ _) hlen)
  · dsimp only; exact le_trans (List.toFinset_card_le _) (le_trans (List.length_filter_le _ _) hlen)
  · cases (C.gates[k.val]).inputs with
    | nil => simp
    | cons a rest => dsimp only; by_cases h : a < n + k.val <;> simp [h]
  · dsimp only; exact le_trans (List.toFinset_card_le _) (le_trans (List.length_filter_le _ _) hlen)
  · dsimp only; exact le_trans (List.toFinset_card_le _) (le_trans (List.length_filter_le _ _) hlen)

private lemma mem_deps_of_bin {n : ℕ} {C : Circuit} {k : Fin C.gates.length}
    (hbin : (C.gates[k.val]).op ≠ GateOp.not) {a : ℕ}
    (ha : a ∈ (C.gates[k.val]).inputs) (hlt : a < n + k.val) : a ∈ deps n C k := by
  unfold deps
  cases hop : (C.gates[k.val]).op
  · simp [List.mem_toFinset, ha, hlt]
  · simp [List.mem_toFinset, ha, hlt]
  · exact absurd hop hbin
  · simp [List.mem_toFinset, ha, hlt]
  · simp [List.mem_toFinset, ha, hlt]

private lemma list_forall_of_filter_length {α : Type} (p : α → Bool) (l : List α)
    (h : (l.filter p).length = l.length) : ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte, List.length_cons] at h
      have := List.length_filter_le p xs
      omega
    · simp only [List.filter_cons, hpx, ↓reduceIte, List.length_cons, Nat.add_right_cancel_iff] at h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hpx
      · exact ih h a ha'

private lemma inputs_lt_of_deps_card_two {n : ℕ} {C : Circuit} (hfit : FanInTwo C)
    (k : Fin C.gates.length) (hbin : (C.gates[k.val]).op ≠ GateOp.not)
    (hcard : (deps n C k).card = 2) :
    ∀ a ∈ (C.gates[k.val]).inputs, a < n + k.val ∧ a ∈ deps n C k := by
  have hlen : (C.gates[k.val]).inputs.length ≤ 2 := (hfit _ (List.getElem_mem k.isLt)).2
  have hfilt_eq : ((C.gates[k.val]).inputs.filter (fun a => decide (a < n + k.val))).length =
      (C.gates[k.val]).inputs.length := by
    have h1 : 2 ≤ ((C.gates[k.val]).inputs.filter (fun a => decide (a < n + k.val))).length := by
      have hdeps : (deps n C k).card =
          ((C.gates[k.val]).inputs.filter (fun a => decide (a < n + k.val))).toFinset.card := by
        unfold deps
        cases hop : (C.gates[k.val]).op
        · rfl
        · rfl
        · exact absurd hop hbin
        · rfl
        · rfl
      rw [hdeps] at hcard
      have := List.toFinset_card_le
        ((C.gates[k.val]).inputs.filter (fun a => decide (a < n + k.val)))
      omega
    have h2 := List.length_filter_le (fun a => decide (a < n + k.val)) (C.gates[k.val]).inputs
    omega
  have hall := list_forall_of_filter_length (fun a => decide (a < n + k.val)) _ hfilt_eq
  intro a ha
  have hlt : a < n + k.val := of_decide_eq_true (hall a ha)
  exact ⟨hlt, mem_deps_of_bin hbin ha hlt⟩

private def gateEval (g : Gate) (bound : ℕ) (V : ℕ → Bool) : Bool :=
  g.op.eval (g.inputs.map fun a => if a < bound then V a else false)

private lemma gateEval_congr {n : ℕ} {C : Circuit} {k : Fin C.gates.length} {V₁ V₂ : ℕ → Bool}
    (h : ∀ a ∈ deps n C k, V₁ a = V₂ a) :
    gateEval (C.gates[k.val]) (n + k.val) V₁ = gateEval (C.gates[k.val]) (n + k.val) V₂ := by
  unfold gateEval
  cases hop : (C.gates[k.val]).op
  · congr 1
    apply List.map_congr_left
    intro a ha
    by_cases hlt : a < n + k.val
    · simp only [hlt, ↓reduceIte]
      exact h a (mem_deps_of_bin (by simp [hop]) ha hlt)
    · simp only [hlt, ↓reduceIte]
  · congr 1
    apply List.map_congr_left
    intro a ha
    by_cases hlt : a < n + k.val
    · simp only [hlt, ↓reduceIte]
      exact h a (mem_deps_of_bin (by simp [hop]) ha hlt)
    · simp only [hlt, ↓reduceIte]
  · cases hins : (C.gates[k.val]).inputs with
    | nil => simp [GateOp.eval]
    | cons a rest =>
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      by_cases hlt : a < n + k.val
      · simp only [hlt, ↓reduceIte]
        have hmem : a ∈ deps n C k := by simp [deps, hop, hins, hlt]
        rw [h a hmem]
      · simp only [hlt, ↓reduceIte]
  · congr 1
    apply List.map_congr_left
    intro a ha
    by_cases hlt : a < n + k.val
    · simp only [hlt, ↓reduceIte]
      exact h a (mem_deps_of_bin (by simp [hop]) ha hlt)
    · simp only [hlt, ↓reduceIte]
  · congr 1
    apply List.map_congr_left
    intro a ha
    by_cases hlt : a < n + k.val
    · simp only [hlt, ↓reduceIte]
      exact h a (mem_deps_of_bin (by simp [hop]) ha hlt)
    · simp only [hlt, ↓reduceIte]

private lemma gateEval_mono_and_or {n : ℕ} {C : Circuit} (hfit : FanInTwo C)
    {k : Fin C.gates.length} (hbin : (C.gates[k.val]).op ≠ GateOp.not)
    {V₁ V₂ : ℕ → Bool} (h : ∀ a ∈ deps n C k, V₁ a = true → V₂ a = true) :
    gateEval (C.gates[k.val]) (n + k.val) V₁ = true →
    gateEval (C.gates[k.val]) (n + k.val) V₂ = true := by
  have hop_mem := (hfit _ (List.getElem_mem k.isLt)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop_mem
  unfold gateEval
  rcases hop_mem with hop | hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro h1 a ha
    by_cases hlt : a < n + k.val
    · simp only [hlt, ↓reduceIte]
      have h2 := h1 a ha
      simp only [hlt, ↓reduceIte] at h2
      exact h a (mem_deps_of_bin hbin ha hlt) h2
    · have h2 := h1 a ha
      simp only [hlt, ↓reduceIte] at h2
      simp at h2
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨a, ha, rfl⟩, hb⟩
    by_cases hlt : a < n + k.val
    · simp only [hlt, ↓reduceIte] at hb
      exact ⟨V₂ a, ⟨a, ha, by simp [hlt]⟩, h a (mem_deps_of_bin hbin ha hlt) hb⟩
    · simp only [hlt, ↓reduceIte] at hb
      simp at hb
  · exact absurd hop hbin

private lemma gateEval_anti_not {n : ℕ} {C : Circuit} {k : Fin C.gates.length}
    (hnot : (C.gates[k.val]).op = GateOp.not)
    {V₁ V₂ : ℕ → Bool} (h : ∀ a ∈ deps n C k, V₂ a = true → V₁ a = true) :
    gateEval (C.gates[k.val]) (n + k.val) V₁ = true →
    gateEval (C.gates[k.val]) (n + k.val) V₂ = true := by
  unfold gateEval
  rw [hnot]
  cases hins : (C.gates[k.val]).inputs with
  | nil => simp [GateOp.eval]
  | cons a rest =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
    by_cases hlt : a < n + k.val
    · simp only [hlt, ↓reduceIte]
      have hmem : a ∈ deps n C k := by simp [deps, hnot, hins, hlt]
      intro h1
      cases hv2 : V₂ a
      · rfl
      · have hv1 := h a hmem hv2
        rw [hv1] at h1
        simp at h1
    · simp only [hlt, ↓reduceIte, imp_self]

private def Edge (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k : Fin C.gates.length, v = n + k.val ∧ u ∈ deps n C k

private lemma edge_lt {n : ℕ} {C : Circuit} {u v : ℕ} (h : Edge n C u v) : u < v := by
  rcases h with ⟨k, rfl, ha⟩
  exact deps_lt ha

private def Reach (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  Relation.ReflTransGen (Edge n C) u v

private lemma reach_le {n : ℕ} {C : Circuit} {u v : ℕ} (h : Reach n C u v) : u ≤ v := by
  induction h with
  | refl => exact le_refl _
  | tail _ he ih => exact le_trans ih (le_of_lt (edge_lt he))

private lemma reach_trans {n : ℕ} {C : Circuit} {u v w : ℕ}
    (h1 : Reach n C u v) (h2 : Reach n C v w) : Reach n C u w :=
  Relation.ReflTransGen.trans h1 h2

private lemma wireVal_congr_of_reach {n : ℕ} (C : Circuit) {x x' : Fin n → Bool} :
    ∀ v : ℕ, v < n + C.gates.length →
    (∀ i : Fin n, Reach n C i.val v → x i = x' i) →
    wireVal n C x v = wireVal n C x' v := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv hagree
    by_cases hlt : v < n
    · rw [wireVal_input C x hlt, wireVal_input C x' hlt]
      exact hagree ⟨v, hlt⟩ Relation.ReflTransGen.refl
    · let k : Fin C.gates.length := ⟨v - n, by omega⟩
      have hvk : v = n + k.val := by dsimp [k]; omega
      rw [hvk, wireVal_gate C x k, wireVal_gate C x' k]
      refine gateEval_congr fun a ha => ?_
      have halt : a < v := by rw [hvk]; exact deps_lt ha
      exact ih a halt (by omega) fun i hir =>
        hagree i (Relation.ReflTransGen.tail hir ⟨k, hvk, ha⟩)

private noncomputable def activeWires (n : ℕ) (C : Circuit) : Finset ℕ :=
  letI : DecidablePred (fun u => Reach n C u C.output) := Classical.decPred _
  (Finset.range (n + C.gates.length)).filter (fun u => Reach n C u C.output)

private noncomputable def subInputs (n : ℕ) (Sub : Finset ℕ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => i.val ∈ Sub)

private noncomputable def subGates (n : ℕ) (C : Circuit) (Sub : Finset ℕ) :
    Finset (Fin C.gates.length) :=
  (Finset.univ : Finset (Fin C.gates.length)).filter (fun k => n + k.val ∈ Sub)

private noncomputable def outDeg (n : ℕ) (C : Circuit) (Sub : Finset ℕ) (u : ℕ) : ℕ :=
  ((subGates n C Sub).filter (fun k => u ∈ deps n C k)).card

private lemma card_sub_eq_in_add_gate {n : ℕ} (C : Circuit) (Sub : Finset ℕ)
    (hSub : Sub ⊆ Finset.range (n + C.gates.length)) :
    Sub.card = (subInputs n Sub).card + (subGates n C Sub).card := by
  let S₁ := (subInputs n Sub).image (fun i : Fin n => i.val)
  let S₂ := (subGates n C Sub).image (fun k : Fin C.gates.length => n + k.val)
  have hunion : Sub = S₁ ∪ S₂ := by
    ext u
    simp only [S₁, S₂, subInputs, subGates, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hu
      have hlt : u < n + C.gates.length := Finset.mem_range.mp (hSub hu)
      by_cases h : u < n
      · exact Or.inl ⟨⟨u, h⟩, hu, rfl⟩
      · exact Or.inr ⟨⟨u - n, by omega⟩, by simpa [Nat.add_sub_of_le (by omega : n ≤ u)] using hu,
          by dsimp; omega⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩) <;> assumption
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    rcases Finset.mem_image.mp hu1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hu2 with ⟨k, _, heq⟩
    omega
  conv_lhs => rw [hunion]
  rw [Finset.card_union_of_disjoint hdisj]
  have hc1 : S₁.card = (subInputs n Sub).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have hc2 : S₂.card = (subGates n C Sub).card :=
    Finset.card_image_of_injective _ fun a b hab => Fin.ext (by omega)
  rw [hc1, hc2]

open Classical in
private lemma handshaking_sub {n : ℕ} (C : Circuit) (hfit : FanInTwo C) (Sub : Finset ℕ)
    (target : ℕ)
    (hSub : Sub ⊆ Finset.range (n + C.gates.length))
    (ht_mem : target ∈ Sub)
    (ht_max : ∀ u ∈ Sub, u ≤ target)
    (hdown : ∀ k : Fin C.gates.length, n + k.val ∈ Sub → ∀ a ∈ deps n C k, a ∈ Sub)
    (hup : ∀ u ∈ Sub, u ≠ target → ∃ k : Fin C.gates.length, n + k.val ∈ Sub ∧ u ∈ deps n C k) :
    let B := (subGates n C Sub).filter (fun k => (C.gates[k.val]).op ≠ GateOp.not)
    let N := (subGates n C Sub).filter (fun k => (C.gates[k.val]).op = GateOp.not)
    (∑ u ∈ Sub.erase target, (outDeg n C Sub u - 1)) +
      ((∑ k ∈ B, (2 - (deps n C k).card)) + (∑ k ∈ N, (1 - (deps n C k).card))) +
      (subInputs n Sub).card = B.card + 1 := by
  intro B N

  have hdouble : (∑ u ∈ Sub, outDeg n C Sub u) = ∑ k ∈ subGates n C Sub, (deps n C k).card := by
    unfold outDeg
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hsub_deps : deps n C k ⊆ Sub := fun a ha =>
      hdown k (Finset.mem_filter.mp hk).2 a ha
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub_deps]

  have hout_t : outDeg n C Sub target = 0 := by
    unfold outDeg
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk hmem
    have h1 : target < n + k.val := deps_lt hmem
    have h2 : n + k.val ≤ target := ht_max _ (Finset.mem_filter.mp hk).2
    omega

  have hout_ge1 : ∀ u ∈ Sub.erase target, 1 ≤ outDeg n C Sub u := by
    intro u hu
    rcases Finset.mem_erase.mp hu with ⟨hne, huSub⟩
    rcases hup u huSub hne with ⟨k, hkSub, hdep⟩
    exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkSub⟩, hdep⟩⟩
  have hlhs : (∑ u ∈ Sub, outDeg n C Sub u) =
      (∑ u ∈ Sub.erase target, (outDeg n C Sub u - 1)) + (Sub.card - 1) := by
    rw [← Finset.add_sum_erase _ _ ht_mem, hout_t, zero_add]
    have hcard1 : (Sub.erase target).card = ∑ _u ∈ Sub.erase target, 1 := by simp
    have hadd : (∑ u ∈ Sub.erase target, (outDeg n C Sub u - 1)) + (Sub.erase target).card =
        ∑ u ∈ Sub.erase target, outDeg n C Sub u := by
      rw [hcard1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u hu => ?_
      have := hout_ge1 u hu
      omega
    rw [Finset.card_erase_of_mem ht_mem] at hadd
    omega

  have hBN_union : subGates n C Sub = B ∪ N := by
    ext k
    simp only [B, N, Finset.mem_union, Finset.mem_filter]
    tauto
  have hBN_disj : Disjoint B N := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    exact (Finset.mem_filter.mp hk1).2 (Finset.mem_filter.mp hk2).2
  have hgate_card : (subGates n C Sub).card = B.card + N.card := by
    rw [hBN_union, Finset.card_union_of_disjoint hBN_disj]
  have hsum_BN : (∑ k ∈ subGates n C Sub, (deps n C k).card) =
      (∑ k ∈ B, (deps n C k).card) + (∑ k ∈ N, (deps n C k).card) := by
    rw [hBN_union, Finset.sum_union hBN_disj]
  have hB_def : (∑ k ∈ B, (deps n C k).card) + (∑ k ∈ B, (2 - (deps n C k).card)) = 2 * B.card := by
    rw [← Finset.sum_add_distrib]
    calc (∑ k ∈ B, ((deps n C k).card + (2 - (deps n C k).card)))
        = ∑ _k ∈ B, 2 := Finset.sum_congr rfl fun k _ => by
            have := deps_card_le_two (n := n) hfit k; omega
      _ = 2 * B.card := by simp [mul_comm]
  have hN_def : (∑ k ∈ N, (deps n C k).card) + (∑ k ∈ N, (1 - (deps n C k).card)) = N.card := by
    rw [← Finset.sum_add_distrib]
    calc (∑ k ∈ N, ((deps n C k).card + (1 - (deps n C k).card)))
        = ∑ _k ∈ N, 1 := Finset.sum_congr rfl fun k hk => by
            have := deps_card_not (n := n) (Finset.mem_filter.mp hk).2; omega
      _ = N.card := by simp
  have hsub_pos : 1 ≤ Sub.card := Finset.card_pos.mpr ⟨target, ht_mem⟩
  have hsub_card := card_sub_eq_in_add_gate C Sub hSub
  omega

private def evalOv (n : ℕ) (C : Circuit) (w : ℕ) (b : Bool) (x : Fin n → Bool) (u : ℕ) : Bool :=
  if u = w then b
  else if h : u < n then x ⟨u, h⟩
  else if hk : u - n < C.gates.length then
    let g := C.gates[u - n]
    g.op.eval (g.inputs.map fun a => if _ : a < u then evalOv n C w b x a else false)
  else false
termination_by u

private lemma evalOv_eq_w {n : ℕ} (C : Circuit) (w : ℕ) (b : Bool) (x : Fin n → Bool) :
    evalOv n C w b x w = b := by
  rw [evalOv]; simp

private lemma evalOv_input {n : ℕ} (C : Circuit) (w : ℕ) (b : Bool) (x : Fin n → Bool)
    {u : ℕ} (hu : u < n) (hne : u ≠ w) :
    evalOv n C w b x u = x ⟨u, hu⟩ := by
  rw [evalOv]
  simp [hne, hu]

private lemma evalOv_gate {n : ℕ} (C : Circuit) (w : ℕ) (b : Bool) (x : Fin n → Bool)
    (k : Fin C.gates.length) (hne : n + k.val ≠ w) :
    evalOv n C w b x (n + k.val) = gateEval (C.gates[k.val]) (n + k.val) (evalOv n C w b x) := by
  rw [evalOv]
  have hnotlt : ¬ n + k.val < n := by omega
  have hsub : n + k.val - n = k.val := by omega
  simp only [hne, ↓reduceIte, hnotlt, ↓reduceDIte, hsub, k.isLt]
  rfl

private lemma evalOv_eq_wireVal_of_ge {n : ℕ} (C : Circuit) (b : Bool) (x : Fin n → Bool) :
    ∀ u : ℕ, u < n + C.gates.length →
    evalOv n C (n + C.gates.length) b x u = wireVal n C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    have hne : u ≠ n + C.gates.length := by omega
    by_cases hlt : u < n
    · rw [evalOv_input C _ b x hlt hne, wireVal_input C x hlt]
    · let k : Fin C.gates.length := ⟨u - n, by omega⟩
      have hvk : u = n + k.val := by dsimp [k]; omega
      rw [hvk, evalOv_gate C _ b x k (by omega), wireVal_gate C x k]
      refine gateEval_congr fun a ha => ?_
      have halt : a < u := by rw [hvk]; exact deps_lt ha
      exact ih a halt (by omega)

private lemma evalOv_diag {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    ∀ u : ℕ, u < n + C.gates.length →
    evalOv n C w (wireVal n C x w) x u = wireVal n C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    by_cases heq : u = w
    · subst heq; exact evalOv_eq_w C u (wireVal n C x u) x
    · by_cases hlt : u < n
      · rw [evalOv_input C w _ x hlt heq, wireVal_input C x hlt]
      · let k : Fin C.gates.length := ⟨u - n, by omega⟩
        have hvk : u = n + k.val := by dsimp [k]; omega
        rw [hvk, evalOv_gate C w _ x k (by omega), wireVal_gate C x k]
        refine gateEval_congr fun a ha => ?_
        have halt : a < u := by rw [hvk]; exact deps_lt ha
        exact ih a halt (by omega)

private lemma evalOv_mono_of_no_not {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (R : Finset ℕ) (w : ℕ) (x : Fin n → Bool)
    (hdown : ∀ k : Fin C.gates.length, n + k.val ∈ R → ∀ a ∈ deps n C k, a ∈ R)
    (hno_not : ∀ k : Fin C.gates.length, n + k.val ∈ R → ¬ Reach n C (n + k.val) w →
      (C.gates[k.val]).op ≠ GateOp.not)
    (hcone : ∀ k : Fin C.gates.length, n + k.val ∈ R → ¬ Reach n C (n + k.val) w →
      ∀ a ∈ deps n C k, a = w ∨ ¬ Reach n C a w) :
    ∀ u : ℕ, u ∈ R → (u = w ∨ ¬ Reach n C u w) →
    evalOv n C w false x u = true → evalOv n C w true x u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro huR hcase hval
    by_cases heq : u = w
    · subst heq; rw [evalOv_eq_w] at hval; simp at hval
    · have hnotR : ¬ Reach n C u w := hcase.resolve_left heq
      by_cases hlt : u < n
      · rw [evalOv_input C w false x hlt heq] at hval
        rw [evalOv_input C w true x hlt heq]
        exact hval
      · by_cases hk : u - n < C.gates.length
        · let k : Fin C.gates.length := ⟨u - n, hk⟩
          have hvk : u = n + k.val := by dsimp [k]; omega
          rw [hvk] at huR hnotR heq hval ⊢
          rw [evalOv_gate C w false x k heq] at hval
          rw [evalOv_gate C w true x k heq]
          refine gateEval_mono_and_or hfit (hno_not k huR hnotR) (fun a ha => ?_) hval
          have halt : a < n + k.val := deps_lt ha
          exact ih a (by omega) (hdown k huR a ha) (hcone k huR hnotR a ha)
        · rw [evalOv] at hval
          simp [heq, hlt, hk] at hval

private lemma chain_linear {n : ℕ} (C : Circuit) (R : Finset ℕ) (i : Fin n) (target : ℕ)
    (hR_up : ∀ u v : ℕ, Reach n C u v → v ∈ R → u ∈ R)
    (hdeg1 : ∀ u ∈ R, Reach n C i.val u → u < target →
      ∀ k₁ k₂ : Fin C.gates.length, n + k₁.val ∈ R → n + k₂.val ∈ R →
        u ∈ deps n C k₁ → u ∈ deps n C k₂ → k₁ = k₂) :
    ∀ u : ℕ, u ∈ R → Reach n C i.val u → u ≤ target →
    ∀ v : ℕ, v ∈ R → Reach n C i.val v → v ≤ target →
    u ≤ v → Reach n C u v := by
  intro u huR hiu hut v hvR hiv hvt huv
  induction hiu with
  | refl => exact hiv
  | tail hiu₀ he ih =>
    rename_i u₀ u₁
    have hu₀lt : u₀ < u₁ := edge_lt he
    have hu₀R : u₀ ∈ R := hR_up u₀ u₁ (Relation.ReflTransGen.single he) huR
    have hreach0 : Reach n C u₀ v := ih hu₀R (by omega) (by omega)
    rcases Relation.ReflTransGen.cases_head hreach0 with rfl | ⟨u', he', hreach'⟩
    · omega
    · rcases he with ⟨k₁, rfl, hdep₁⟩
      rcases he' with ⟨k₂, rfl, hdep₂⟩
      have hu'R : n + k₂.val ∈ R := hR_up _ v hreach' hvR
      have hkeq : k₁ = k₂ := hdeg1 u₀ hu₀R hiu₀ (by omega) k₁ k₂ huR hu'R hdep₁ hdep₂
      subst hkeq
      exact hreach'

private lemma chain_at_most_one_dep {n : ℕ} (C : Circuit) (R : Finset ℕ) (i : Fin n) (target : ℕ)
    (hR_up : ∀ u v : ℕ, Reach n C u v → v ∈ R → u ∈ R)
    (hdeg1 : ∀ u ∈ R, Reach n C i.val u → u < target →
      ∀ k₁ k₂ : Fin C.gates.length, n + k₁.val ∈ R → n + k₂.val ∈ R →
        u ∈ deps n C k₁ → u ∈ deps n C k₂ → k₁ = k₂)
    (k : Fin C.gates.length) (hkR : n + k.val ∈ R) (hkt : n + k.val ≤ target)
    {a₁ a₂ : ℕ} (ha₁ : a₁ ∈ deps n C k) (ha₂ : a₂ ∈ deps n C k)
    (hi₁ : Reach n C i.val a₁) (hi₂ : Reach n C i.val a₂) : a₁ = a₂ := by
  have ha₁R : a₁ ∈ R := hR_up a₁ (n + k.val) (Relation.ReflTransGen.single ⟨k, rfl, ha₁⟩) hkR
  have ha₂R : a₂ ∈ R := hR_up a₂ (n + k.val) (Relation.ReflTransGen.single ⟨k, rfl, ha₂⟩) hkR
  have hlt₁ : a₁ < n + k.val := deps_lt ha₁
  have hlt₂ : a₂ < n + k.val := deps_lt ha₂
  rcases lt_trichotomy a₁ a₂ with hlt | heq | hgt
  · exfalso
    have hr := chain_linear C R i target hR_up hdeg1 a₁ ha₁R hi₁ (by omega) a₂ ha₂R hi₂ (by omega) (le_of_lt hlt)
    rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨u', ⟨k', rfl, hdep'⟩, hr'⟩
    · omega
    · have hu'R : n + k'.val ∈ R := hR_up _ a₂ hr' ha₂R
      have hkeq : k = k' := hdeg1 a₁ ha₁R hi₁ (by omega) k k' hkR hu'R ha₁ hdep'
      subst hkeq
      have := reach_le hr'
      omega
  · exact heq
  · exfalso
    have hr := chain_linear C R i target hR_up hdeg1 a₂ ha₂R hi₂ (by omega) a₁ ha₁R hi₁ (by omega) (le_of_lt hgt)
    rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨u', ⟨k', rfl, hdep'⟩, hr'⟩
    · omega
    · have hu'R : n + k'.val ∈ R := hR_up _ a₁ hr' ha₁R
      have hkeq : k = k' := hdeg1 a₂ ha₂R hi₂ (by omega) k k' hkR hu'R ha₂ hdep'
      subst hkeq
      have := reach_le hr'
      omega

private lemma chain_unate {n : ℕ} (C : Circuit) (hfit : FanInTwo C) (R : Finset ℕ)
    (w : ℕ) (i : Fin n) (target : ℕ)
    (hR_sub : R ⊆ Finset.range (n + C.gates.length))
    (hR_up : ∀ u v : ℕ, Reach n C u v → v ∈ R → u ∈ R)
    (hno_w : ∀ u ∈ R, Reach n C i.val u → u ≤ target → u ≠ w)
    (hdeg1 : ∀ u ∈ R, Reach n C i.val u → u < target →
      ∀ k₁ k₂ : Fin C.gates.length, n + k₁.val ∈ R → n + k₂.val ∈ R →
        u ∈ deps n C k₁ → u ∈ deps n C k₂ → k₁ = k₂) :
    ∀ u : ℕ, u ∈ R → u ≤ target →
    ∃ s : Bool, ∀ (b : Bool) (x : Fin n → Bool),
      (¬ Reach n C i.val u →
        evalOv n C w b (Function.update x i false) u =
        evalOv n C w b (Function.update x i true) u) ∧
      (Reach n C i.val u →
        (s = false → evalOv n C w b (Function.update x i false) u = true →
          evalOv n C w b (Function.update x i true) u = true) ∧
        (s = true → evalOv n C w b (Function.update x i true) u = true →
          evalOv n C w b (Function.update x i false) u = true)) := by
  classical
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro huR hut
    have hult : u < n + C.gates.length := Finset.mem_range.mp (hR_sub huR)
    by_cases heqw : u = w
    · refine ⟨false, fun b x => ⟨fun _ => ?_, fun hr => absurd heqw (hno_w u huR hr hut)⟩⟩
      rw [heqw, evalOv_eq_w, evalOv_eq_w]
    · by_cases hlt : u < n
      · refine ⟨false, fun b x => ⟨fun hnr => ?_, fun hr => ?_⟩⟩
        · rw [evalOv_input C w b _ hlt heqw, evalOv_input C w b _ hlt heqw]
          have hne : (⟨u, hlt⟩ : Fin n) ≠ i := by
            intro heq; apply hnr; rw [← heq]; exact Relation.ReflTransGen.refl
          simp [Function.update, hne]
        · constructor
          · intro _ h1
            rw [evalOv_input C w b _ hlt heqw] at h1 ⊢
            by_cases heq : (⟨u, hlt⟩ : Fin n) = i
            · simp [heq]
            · simpa [Function.update, heq] using h1
          · intro h; simp at h
      · let k : Fin C.gates.length := ⟨u - n, by omega⟩
        have hvk : u = n + k.val := by dsimp [k]; omega
        by_cases hreach : Reach n C i.val u
        ·
          have hex_dep : ∃ a ∈ deps n C k, Reach n C i.val a := by
            rcases Relation.ReflTransGen.cases_tail hreach with heqi | ⟨a, hia, he⟩
            · omega
            · rcases he with ⟨k', hkk', ha⟩
              have hk'eq : k' = k := Fin.ext (by omega)
              subst hk'eq
              exact ⟨a, ha, hia⟩
          rcases hex_dep with ⟨a₀, ha₀_dep, ha₀_reach⟩
          have ha₀_lt : a₀ < u := by rw [hvk]; exact deps_lt ha₀_dep
          have ha₀_R : a₀ ∈ R :=
            hR_up a₀ u (Relation.ReflTransGen.single ⟨k, hvk, ha₀_dep⟩) huR
          rcases ih a₀ ha₀_lt ha₀_R (by omega) with ⟨s₀, hs₀⟩
          have hother : ∀ a ∈ deps n C k, a ≠ a₀ → ¬ Reach n C i.val a := by
            intro a ha hne hra
            exact hne (chain_at_most_one_dep C R i target hR_up hdeg1 k
              (by rwa [← hvk]) (by omega) ha ha₀_dep hra ha₀_reach)
          have hother_eq : ∀ (b : Bool) (x : Fin n → Bool) (a : ℕ), a ∈ deps n C k → a ≠ a₀ →
              evalOv n C w b (Function.update x i false) a =
              evalOv n C w b (Function.update x i true) a := by
            intro b x a ha hne
            have halt : a < u := by rw [hvk]; exact deps_lt ha
            have haR : a ∈ R := hR_up a u (Relation.ReflTransGen.single ⟨k, hvk, ha⟩) huR
            rcases ih a halt haR (by omega) with ⟨_, hsa⟩
            exact (hsa b x).1 (hother a ha hne)
          by_cases hnot : (C.gates[k.val]).op = GateOp.not
          · refine ⟨!s₀, fun b x => ⟨fun hnr => absurd hreach hnr, fun _ => ?_⟩⟩
            have h0 := (hs₀ b x).2 ha₀_reach
            constructor
            · intro hs
              have hs0t : s₀ = true := by cases s₀ <;> simp at hs ⊢
              rw [hvk, evalOv_gate C w b _ k (by omega), evalOv_gate C w b _ k (by omega)]
              refine gateEval_anti_not hnot fun a ha hv => ?_
              by_cases haa : a = a₀
              · subst haa; exact h0.2 hs0t hv
              · rw [hother_eq b x a ha haa]; exact hv
            · intro hs
              have hs0f : s₀ = false := by cases s₀ <;> simp at hs ⊢
              rw [hvk, evalOv_gate C w b _ k (by omega), evalOv_gate C w b _ k (by omega)]
              refine gateEval_anti_not hnot fun a ha hv => ?_
              by_cases haa : a = a₀
              · subst haa; exact h0.1 hs0f hv
              · rw [← hother_eq b x a ha haa]; exact hv
          · refine ⟨s₀, fun b x => ⟨fun hnr => absurd hreach hnr, fun _ => ?_⟩⟩
            have h0 := (hs₀ b x).2 ha₀_reach
            constructor
            · intro hs
              rw [hvk, evalOv_gate C w b _ k (by omega), evalOv_gate C w b _ k (by omega)]
              refine gateEval_mono_and_or hfit hnot fun a ha hv => ?_
              by_cases haa : a = a₀
              · subst haa; exact h0.1 hs hv
              · rw [← hother_eq b x a ha haa]; exact hv
            · intro hs
              rw [hvk, evalOv_gate C w b _ k (by omega), evalOv_gate C w b _ k (by omega)]
              refine gateEval_mono_and_or hfit hnot fun a ha hv => ?_
              by_cases haa : a = a₀
              · subst haa; exact h0.2 hs hv
              · rw [hother_eq b x a ha haa]; exact hv
        · refine ⟨false, fun b x => ⟨fun _ => ?_, fun hr => absurd hr hreach⟩⟩
          rw [hvk, evalOv_gate C w b _ k (by omega), evalOv_gate C w b _ k (by omega)]
          refine gateEval_congr fun a ha => ?_
          have halt : a < u := by rw [hvk]; exact deps_lt ha
          have haR : a ∈ R := hR_up a u (Relation.ReflTransGen.single ⟨k, hvk, ha⟩) huR
          have hna : ¬ Reach n C i.val a := fun hra =>
            hreach (Relation.ReflTransGen.tail hra ⟨k, hvk, ha⟩)
          rcases ih a halt haR (by omega) with ⟨_, hsa⟩
          exact (hsa b x).1 hna

private lemma circuit_mono_all_false {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (R : Finset ℕ)
    (hR_sub : R ⊆ Finset.range (n + C.gates.length))
    (hdown : ∀ k : Fin C.gates.length, n + k.val ∈ R → ∀ a ∈ deps n C k, a ∈ R)
    (hfull : ∀ k : Fin C.gates.length, n + k.val ∈ R → (deps n C k).card = 2)
    (hno_not : ∀ k : Fin C.gates.length, n + k.val ∈ R → (C.gates[k.val]).op ≠ GateOp.not) :
    ∀ u ∈ R, wireVal n C (fun _ => false) u = false ∧ wireVal n C (fun _ => true) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro huR
    have hult : u < n + C.gates.length := Finset.mem_range.mp (hR_sub huR)
    by_cases hlt : u < n
    · rw [wireVal_input C _ hlt, wireVal_input C _ hlt]
      exact ⟨rfl, rfl⟩
    · let k : Fin C.gates.length := ⟨u - n, by omega⟩
      have hvk : u = n + k.val := by dsimp [k]; omega
      rw [hvk] at huR ⊢
      have hnot := hno_not k huR
      have hcard := hfull k huR
      have hins := inputs_lt_of_deps_card_two hfit k hnot hcard
      have hlen_ne : (C.gates[k.val]).inputs ≠ [] := by
        intro hemp
        have hc : (deps n C k).card = 0 := by
          unfold deps
          cases hop : (C.gates[k.val]).op
          · simp [hemp]
          · simp [hemp]
          · exact absurd hop hnot
          · simp [hemp]
          · simp [hemp]
        omega
      rcases List.exists_cons_of_ne_nil hlen_ne with ⟨a₀, rest, heq_ins⟩
      have ha₀_mem : a₀ ∈ (C.gates[k.val]).inputs := by rw [heq_ins]; simp
      have hop_mem := (hfit _ (List.getElem_mem k.isLt)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop_mem
      have hval_f : ∀ a ∈ (C.gates[k.val]).inputs,
          (if a < n + k.val then wireVal n C (fun _ => false) a else false) = false := by
        intro a ha
        rcases hins a ha with ⟨halt, hadep⟩
        simp only [halt, ↓reduceIte]
        exact (ih a (by omega) (hdown k huR a hadep)).1
      have hval_t : ∀ a ∈ (C.gates[k.val]).inputs,
          (if a < n + k.val then wireVal n C (fun _ => true) a else false) = true := by
        intro a ha
        rcases hins a ha with ⟨halt, hadep⟩
        simp only [halt, ↓reduceIte]
        exact (ih a (by omega) (hdown k huR a hadep)).2
      rw [wireVal_gate C _ k, wireVal_gate C _ k]
      rcases hop_mem with hop | hop | hop
      · rw [hop]
        constructor
        · by_contra h
          simp only [Bool.not_eq_false, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at h
          have h0 := h false ⟨a₀, ha₀_mem, hval_f a₀ ha₀_mem⟩
          simp at h0
        · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂]
          exact hval_t
      · rw [hop]
        constructor
        · simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂]
          intro a ha; rw [hval_f a ha]; simp
        · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨a₀, ha₀_mem, hval_t a₀ ha₀_mem⟩, rfl⟩
      · exact absurd hop hnot

private lemma monotone_circuit_of_sub {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (U : Finset ℕ) (w : ℕ)
    (hU_sub : U ⊆ Finset.range (n + C.gates.length))
    (hw_mem : w ∈ U)
    (hdown : ∀ k : Fin C.gates.length, n + k.val ∈ U → ∀ a ∈ deps n C k, a ∈ U)
    (hfull : ∀ k : Fin C.gates.length, n + k.val ∈ U → (deps n C k).card = 2)
    (hno_not : ∀ k : Fin C.gates.length, n + k.val ∈ U → (C.gates[k.val]).op ≠ GateOp.not) :
    ∃ P : Circuit, Monotone2 P ∧ P.size = (subGates n C U).card ∧
      ∀ x : Fin n → Bool, P.eval (List.ofFn x) = wireVal n C x w := by
  classical
  let gs : List (Fin C.gates.length) := (List.finRange C.gates.length).filter (fun k => decide (n + k.val ∈ U))
  have hgs_mem : ∀ k : Fin C.gates.length, k ∈ gs ↔ n + k.val ∈ U := by
    intro k; simp [gs, List.mem_finRange]
  have hgs_nodup : gs.Nodup := (List.nodup_finRange _).filter _
  have hgs_len : gs.length = (subGates n C U).card := by
    have hto : gs.toFinset = subGates n C U := by
      ext k; simp [subGates, hgs_mem]
    rw [← hto, List.toFinset_card_of_nodup hgs_nodup]
  have hgs_mono : ∀ i j : ℕ, (hi : i < gs.length) → (hj : j < gs.length) → i < j →
      (gs[i]).val < (gs[j]).val := by
    have hsorted : gs.Pairwise (fun a b : Fin C.gates.length => a.val < b.val) := by
      apply List.Pairwise.filter
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp [List.getElem_finRange, hij]
    rw [List.pairwise_iff_getElem] at hsorted
    exact hsorted
  let idxOf (u : ℕ) : ℕ :=
    if u < n then u else n + gs.findIdx (fun k => decide (n + k.val = u))
  have hidxOf_lt : ∀ u : ℕ, u < n → idxOf u = u := fun u hu => by simp [idxOf, hu]
  have hidxOf_gate : ∀ j : ℕ, (hj : j < gs.length) → idxOf (n + (gs[j]).val) = n + j := by
    intro j hj
    simp only [idxOf, show ¬ n + (gs[j]).val < n by omega, ↓reduceIte]
    congr 1
    rw [List.findIdx_eq (by omega)]
    refine ⟨by simp, fun i hi => ?_⟩
    have hlt := hgs_mono i j (by omega) hj hi
    simp only [decide_eq_false_iff_not]
    omega
  let Pg : List Gate := gs.map fun k =>
    { op := (C.gates[k.val]).op, inputs := (C.gates[k.val]).inputs.map idxOf }
  let P : Circuit := { gates := Pg, output := idxOf w }
  have hP_mono : Monotone2 P := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
    have hkU : n + k.val ∈ U := (hgs_mem k).mp hk
    have hnot := hno_not k hkU
    have hfitk := hfit _ (List.getElem_mem k.isLt)
    constructor
    · rcases hfitk.1 with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · exact absurd hop hnot
    · simp [hfitk.2]
  have hP_size : P.size = (subGates n C U).card := by
    simp [Circuit.size, P, Pg, hgs_len]
  have hP_wire : ∀ j : ℕ, (hj : j < gs.length) → ∀ x : Fin n → Bool,
      wireVal n P x (n + j) = wireVal n C x (n + (gs[j]).val) := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj x
      let k := gs[j]
      have hkU : n + k.val ∈ U := (hgs_mem k).mp (List.getElem_mem hj)
      have hnot := hno_not k hkU
      have hcard := hfull k hkU
      have hins := inputs_lt_of_deps_card_two hfit k hnot hcard
      have hjP : j < P.gates.length := by simp [P, Pg, hj]
      rw [wireVal_gate P x ⟨j, hjP⟩, wireVal_gate C x k]
      have hgateP : P.gates[j] =
          { op := (C.gates[k.val]).op, inputs := (C.gates[k.val]).inputs.map idxOf } := by
        simp [P, Pg, k]
      rw [hgateP]
      dsimp only
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      rcases hins a ha with ⟨halt, hadep⟩
      have haU : a ∈ U := hdown k hkU a hadep
      simp only [halt, ↓reduceIte, Function.comp_apply]
      by_cases han : a < n
      · rw [hidxOf_lt a han]
        have hltj : a < n + j := by omega
        simp only [hltj, ↓reduceIte]
        rw [wireVal_input P x han, wireVal_input C x han]
      · have hault : a < n + C.gates.length := Finset.mem_range.mp (hU_sub haU)
        let k' : Fin C.gates.length := ⟨a - n, by omega⟩
        have hak' : a = n + k'.val := by dsimp [k']; omega
        have hk'gs : k' ∈ gs := (hgs_mem k').mpr (by rwa [← hak'])
        rcases List.getElem_of_mem hk'gs with ⟨j', hj', hgsj'⟩
        have hlt_val : (gs[j']).val < (gs[j]).val := by rw [hgsj']; dsimp [k']; omega
        have hj'lt : j' < j := by
          by_contra hge
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
          · omega
          · have := hgs_mono j j' hj hj' hgt; omega
        rw [hak', ← hgsj', hidxOf_gate j' hj']
        have hnj' : n + j' < n + j := by omega
        simp only [hnj', ↓reduceIte]
        exact ih j' hj'lt hj' x
  refine ⟨P, hP_mono, hP_size, fun x => ?_⟩
  rw [eval_eq_wireVal]
  change wireVal n P x (idxOf w) = wireVal n C x w
  by_cases hwn : w < n
  · rw [hidxOf_lt w hwn, wireVal_input P x hwn, wireVal_input C x hwn]
  · have hwlt : w < n + C.gates.length := Finset.mem_range.mp (hU_sub hw_mem)
    let kw : Fin C.gates.length := ⟨w - n, by omega⟩
    have hwkw : w = n + kw.val := by dsimp [kw]; omega
    have hkw_gs : kw ∈ gs := (hgs_mem kw).mpr (by rwa [← hwkw])
    rcases List.getElem_of_mem hkw_gs with ⟨jw, hjw, hgsjw⟩
    rw [hwkw, ← hgsjw, hidxOf_gate jw hjw]
    exact hP_wire jw hjw x

private lemma card_ge_two_of_four_pairs {α : Type} [DecidableEq α] (T : Finset α)
    (F : (α → Bool) → Bool × Bool)
    (hsurj : ∀ p : Bool × Bool, ∃ y : α → Bool, F y = p)
    (hdep : ∀ y₁ y₂ : α → Bool, (∀ a ∈ T, y₁ a = y₂ a) → F y₁ = F y₂) :
    2 ≤ T.card := by
  by_contra hlt
  have hle1 : T.card ≤ 1 := by omega
  let G : (T → Bool) → Bool × Bool := fun r =>
    F (fun a => if h : a ∈ T then r ⟨a, h⟩ else false)
  have hGsurj : Function.Surjective G := by
    intro p
    rcases hsurj p with ⟨y, rfl⟩
    refine ⟨fun a => y a.val, ?_⟩
    apply hdep
    intro a ha
    simp [ha]
  have hcard_le : Fintype.card (Bool × Bool) ≤ Fintype.card (T → Bool) :=
    Fintype.card_le_of_surjective G hGsurj
  have hc1 : Fintype.card (Bool × Bool) = 4 := by decide
  have hc2 : Fintype.card (T → Bool) = 2 ^ T.card := by
    simp [Fintype.card_pi]
  rw [hc1, hc2] at hcard_le
  have hpow : 2 ^ T.card ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hle1
  omega

open Classical in
private lemma binary_eq_card_allBin (C : Circuit) :
    (C.gates.filter (fun g => @decide (g.op ≠ GateOp.not) (Classical.propDecidable _))).length =
    ((Finset.univ : Finset (Fin C.gates.length)).filter
      (fun k => (C.gates[k.val]).op ≠ GateOp.not)).card := by
  have hmap : C.gates = (List.finRange C.gates.length).map (fun k => C.gates[k.val]) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp
  conv_lhs => rw [hmap]
  rw [List.filter_map, List.length_map]
  have hto : ((List.finRange C.gates.length).filter
      ((fun g => @decide (g.op ≠ GateOp.not) (Classical.propDecidable _)) ∘
        fun k => C.gates[k.val])).toFinset =
      (Finset.univ : Finset (Fin C.gates.length)).filter
        (fun k => (C.gates[k.val]).op ≠ GateOp.not) := by
    ext k; simp
  rw [← hto, List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]

open Classical in
private lemma single_not_case {n : ℕ} (C : Circuit) (hfit : FanInTwo C)
    (R U : Finset ℕ) (E S : Finset (Fin n)) (w : ℕ)
    (code : (Fin n → Bool) → Bool)
    (hR_sub : R ⊆ Finset.range (n + C.gates.length))
    (hout_R : C.output ∈ R)
    (hR_down : ∀ k : Fin C.gates.length, n + k.val ∈ R → ∀ a ∈ deps n C k, a ∈ R)
    (hU_sub_R : U ⊆ R)
    (hw_U : w ∈ U)
    (hw_lt_out : w < C.output)
    (hU_max : ∀ u ∈ U, u ≤ w)
    (hU_down : ∀ k : Fin C.gates.length, n + k.val ∈ U → ∀ a ∈ deps n C k, a ∈ U)
    (hU_up : ∀ u ∈ U, u ≠ w → ∃ k : Fin C.gates.length, n + k.val ∈ U ∧ u ∈ deps n C k)
    (hU_mem : ∀ u, u ∈ U ↔ u ∈ R ∧ Reach n C u w)
    (hcone_sep : ∀ k : Fin C.gates.length, n + k.val ∈ R → ¬ Reach n C (n + k.val) w →
      ∀ a ∈ deps n C k, a = w ∨ ¬ Reach n C a w)
    (hother_deg1 : ∀ u ∈ R.erase C.output, u ≠ w → outDeg n C R u ≤ 1)
    (hB_full : ∀ k : Fin C.gates.length, n + k.val ∈ R → (C.gates[k.val]).op ≠ GateOp.not →
      (deps n C k).card = 2)
    (hS_eq_Uin : S = subInputs n U)
    (hbin_eq : (C.gates.filter (fun g => @decide (g.op ≠ GateOp.not) (Classical.propDecidable _))).length = E.card)
    (hpair_10 : ∃ y : Fin n → Bool,
      evalOv n C w false y C.output = true ∧ evalOv n C w true y C.output = false)
    (hcode_eq : ∀ x : Fin n → Bool, code x = (wireVal n C x w != wireVal n C (fun _ => false) w))
    (hsize_le : C.size ≤ E.card + 1) :
    C.size = E.card + 1 ∧ code (fun _ => true) = true ∧
    ∃ P : Circuit, Monotone2 P ∧ P.size + 1 = S.card ∧
      (∀ x : Fin n → Bool, P.eval (List.ofFn x) = code x) := by
  let allNot := (Finset.univ : Finset (Fin C.gates.length)).filter
    (fun k => (C.gates[k.val]).op = GateOp.not)
  let allBin := (Finset.univ : Finset (Fin C.gates.length)).filter
    (fun k => (C.gates[k.val]).op ≠ GateOp.not)
  have hall_split : C.size = allBin.card + allNot.card := by
    have hunion : (Finset.univ : Finset (Fin C.gates.length)) = allBin ∪ allNot := by
      ext k; simp [allBin, allNot]; tauto
    have hdisj : Disjoint allBin allNot := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      exact (Finset.mem_filter.mp hk1).2 (Finset.mem_filter.mp hk2).2
    have hc := Finset.card_union_of_disjoint hdisj
    rw [← hunion, Finset.card_univ, Fintype.card_fin] at hc
    exact hc
  have hallBin_eq : allBin.card = E.card := (binary_eq_card_allBin C).symm.trans hbin_eq
  have hex_not_out : ∃ k : Fin C.gates.length,
      n + k.val ∈ R ∧ ¬ Reach n C (n + k.val) w ∧ (C.gates[k.val]).op = GateOp.not := by
    by_contra hnone
    push Not at hnone
    rcases hpair_10 with ⟨y, hy0, hy1⟩
    have hmono := evalOv_mono_of_no_not C hfit R w y hR_down hnone hcone_sep
      C.output hout_R (Or.inr fun h => by have := reach_le h; omega) hy0
    rw [hy1] at hmono
    simp at hmono
  rcases hex_not_out with ⟨k_not, _, hk_not_nU, hk_not_op⟩
  have hk_not_mem : k_not ∈ allNot := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_not_op⟩
  have hnot_ge1 : 1 ≤ allNot.card := Finset.card_pos.mpr ⟨k_not, hk_not_mem⟩
  have hsize_eq : C.size = E.card + 1 := by omega
  have hnot_eq1 : allNot.card = 1 := by omega
  have hU_no_not : ∀ k : Fin C.gates.length, n + k.val ∈ U → (C.gates[k.val]).op ≠ GateOp.not := by
    intro k hkU hop
    have hk_mem : k ∈ allNot := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hop⟩
    have heq : k = k_not := Finset.card_le_one_iff.mp (by omega) hk_mem hk_not_mem
    subst heq
    exact hk_not_nU ((hU_mem _).mp hkU).2
  have hU_sub : U ⊆ Finset.range (n + C.gates.length) := Finset.Subset.trans hU_sub_R hR_sub
  have hU_full : ∀ k : Fin C.gates.length, n + k.val ∈ U → (deps n C k).card = 2 := fun k hkU =>
    hB_full k (hU_sub_R hkU) (hU_no_not k hkU)
  have hgz_go := circuit_mono_all_false C hfit U hU_sub hU_down hU_full hU_no_not w hw_U
  have hcode_eq_g : ∀ x : Fin n → Bool, code x = wireVal n C x w := fun x => by
    rw [hcode_eq x, hgz_go.1, Bool.bne_false]
  have hcode_o : code (fun _ => true) = true := by
    rw [hcode_eq_g]; exact hgz_go.2
  have hshakeU := handshaking_sub C hfit U w hU_sub hw_U hU_max hU_down hU_up
  dsimp only at hshakeU
  have hδout_U : (∑ u ∈ U.erase w, (outDeg n C U u - 1)) = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    rcases Finset.mem_erase.mp hu with ⟨huw, huU⟩
    have huR : u ∈ R := hU_sub_R huU
    have hne_out : u ≠ C.output := by
      have := hU_max u huU; omega
    have hleR : outDeg n C U u ≤ outDeg n C R u := by
      unfold outDeg
      apply Finset.card_le_card
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkU, hdep⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU_sub_R (Finset.mem_filter.mp hkU).2⟩, hdep⟩
    have hR1 := hother_deg1 u (Finset.mem_erase.mpr ⟨hne_out, huR⟩) huw
    omega
  have hBU_eq : (subGates n C U).filter (fun k => (C.gates[k.val]).op ≠ GateOp.not) =
      subGates n C U := by
    ext k
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hk
    exact hU_no_not k (Finset.mem_filter.mp hk).2
  have hNU_eq : (subGates n C U).filter (fun k => (C.gates[k.val]).op = GateOp.not) = ∅ := by
    ext k
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hk
    exact hU_no_not k (Finset.mem_filter.mp hk).2
  have hδin_BU : (∑ k ∈ subGates n C U, (2 - (deps n C k).card)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have := hU_full k (Finset.mem_filter.mp hk).2
    omega
  rw [hδout_U, hBU_eq, hNU_eq, hδin_BU, Finset.sum_empty] at hshakeU
  have hUgate_card : (subGates n C U).card + 1 = S.card := by
    rw [hS_eq_Uin]; omega
  rcases monotone_circuit_of_sub C hfit U w hU_sub hw_U hU_down hU_full hU_no_not with
    ⟨P, hP_mono, hP_size, hP_eval⟩
  refine ⟨hsize_eq, hcode_o, P, hP_mono, by omega, fun x => ?_⟩
  rw [hP_eval x, hcode_eq_g x]

private lemma prove_570 (n : Nat) (C : Circuit) (hfit : FanInTwo C) :
    let W := Fin n → Bool
    let f := fun (x : W) => C.eval (List.ofFn x)
    let change := fun (j : Fin n) (v : Bool) =>
      ∃ x : W, f (Function.update x j false) = v ∧ f (Function.update x j true) = !v
    let E := (Finset.univ : Finset (Fin n)).filter (fun j => change j false ∨ change j true)
    let S := E.filter (fun j => change j false ∧ change j true)
    let merge := fun (x y : W) (j : Fin n) => if j ∈ S then x j else y j
    let z : W := fun _ => false
    let o : W := fun _ => true
    let code := fun (x : W) => decide (∃ y : W, f (merge x y) ≠ f (merge z y))
    let binary := (C.gates.filter (fun g => @decide (g.op ≠ GateOp.not) (Classical.propDecidable _))).length
    S.Nonempty → binary ≤ E.card →
      binary = E.card ∧ S.card + 2 ≤ E.card ∧
      (∀ i : Fin n, ∃ sign : Bool, ∀ input : W,
        code (Function.update input i false) = sign →
        code (Function.update input i true) = sign) ∧
      (∃ hi : W,
        (∀ x y : W, f (merge x y) =
          if code x then f (merge hi y) else f (merge z y)) ∧
        (∀ p q : Bool, ∃ y : W, f (merge z y) = p ∧ f (merge hi y) = q)) ∧
      (C.size ≤ E.card + 1 →
        C.size = E.card + 1 ∧ code o = true ∧
        ∃ P : Circuit,
          Monotone2 P ∧ P.size + 1 = S.card ∧
          (∀ x : W, P.eval (List.ofFn x) = code x)) := by
  classical
  intro W f change E S merge z o code binary hS_ne hbin_le

  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    rcases hS_ne with ⟨s, hs⟩
    have hsE : s ∈ E := (Finset.mem_filter.mp hs).1
    have hch : change s false ∨ change s true := (Finset.mem_filter.mp hsE).2
    have hconst : ∀ x : W, f x = false := fun x => wireVal_ge C x (by omega)
    rcases hch with ⟨x, h1, h2⟩ | ⟨x, h1, h2⟩ <;> simp [hconst] at h1 h2

  let R := activeWires n C
  have hR_sub : R ⊆ Finset.range (n + C.gates.length) := Finset.filter_subset _ _
  have hR_mem : ∀ u, u ∈ R ↔ u < n + C.gates.length ∧ Reach n C u C.output := by
    intro u; simp [R, activeWires, Finset.mem_range]
  have hout_R : C.output ∈ R := (hR_mem _).mpr ⟨hout_lt, Relation.ReflTransGen.refl⟩
  have hR_max : ∀ u ∈ R, u ≤ C.output := fun u hu => reach_le ((hR_mem u).mp hu).2
  have hR_up : ∀ u v : ℕ, Reach n C u v → v ∈ R → u ∈ R := by
    intro u v huv hv
    rcases (hR_mem v).mp hv with ⟨hvlt, hvo⟩
    exact (hR_mem u).mpr ⟨lt_of_le_of_lt (reach_le huv) hvlt, reach_trans huv hvo⟩
  have hR_down : ∀ k : Fin C.gates.length, n + k.val ∈ R → ∀ a ∈ deps n C k, a ∈ R := by
    intro k hk a ha
    exact hR_up a (n + k.val) (Relation.ReflTransGen.single ⟨k, rfl, ha⟩) hk
  have hR_upstep : ∀ u ∈ R, u ≠ C.output →
      ∃ k : Fin C.gates.length, n + k.val ∈ R ∧ u ∈ deps n C k := by
    intro u hu hne
    rcases (hR_mem u).mp hu with ⟨_, hr⟩
    rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨v, ⟨k, rfl, hdep⟩, hr'⟩
    · exact absurd rfl hne
    · exact ⟨k, hR_up _ C.output hr' hout_R, hdep⟩

  have hE_sub : E ⊆ subInputs n R := by
    intro i hi
    simp only [subInputs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine (hR_mem i.val).mpr ⟨by omega, ?_⟩
    by_contra hnr
    have hch : change i false ∨ change i true := (Finset.mem_filter.mp hi).2
    have hEq : ∀ x : W, f (Function.update x i false) = f (Function.update x i true) := by
      intro x
      refine wireVal_congr_of_reach C C.output hout_lt fun j hjr => ?_
      have hne : j ≠ i := fun heq => hnr (heq ▸ hjr)
      simp [Function.update, hne]
    rcases hch with ⟨x, h1, h2⟩ | ⟨x, h1, h2⟩
    · rw [hEq x, h2] at h1; simp at h1
    · rw [hEq x, h2] at h1; simp at h1
  have hE_le_Rin : E.card ≤ (subInputs n R).card := Finset.card_le_card hE_sub

  let B_act := (subGates n C R).filter (fun k => (C.gates[k.val]).op ≠ GateOp.not)
  let N_act := (subGates n C R).filter (fun k => (C.gates[k.val]).op = GateOp.not)
  have hB_le_bin : B_act.card ≤ binary := by
    let allB := (Finset.univ : Finset (Fin C.gates.length)).filter
      (fun k => (C.gates[k.val]).op ≠ GateOp.not)
    have hsub : B_act ⊆ allB := by
      intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2⟩
    dsimp only [binary]
    rw [binary_eq_card_allBin C]
    exact Finset.card_le_card hsub

  have hshake := handshaking_sub C hfit R C.output hR_sub hout_R hR_max hR_down hR_upstep
  change (∑ u ∈ R.erase C.output, (outDeg n C R u - 1)) +
      ((∑ k ∈ B_act, (2 - (deps n C k).card)) + (∑ k ∈ N_act, (1 - (deps n C k).card))) +
      (subInputs n R).card = B_act.card + 1 at hshake

  have hδout_pos : 1 ≤ ∑ u ∈ R.erase C.output, (outDeg n C R u - 1) := by
    by_contra hlt
    have hδ0 : (∑ u ∈ R.erase C.output, (outDeg n C R u - 1)) = 0 := by omega
    have hdeg1_all : ∀ u ∈ R, u < C.output →
        ∀ k₁ k₂ : Fin C.gates.length, n + k₁.val ∈ R → n + k₂.val ∈ R →
          u ∈ deps n C k₁ → u ∈ deps n C k₂ → k₁ = k₂ := by
      intro u huR hult k₁ k₂ hk₁ hk₂ hd₁ hd₂
      have huE : u ∈ R.erase C.output := Finset.mem_erase.mpr ⟨by omega, huR⟩
      have h0 : outDeg n C R u - 1 = 0 :=
        Finset.sum_eq_zero_iff.mp hδ0 u huE
      have hle1 : outDeg n C R u ≤ 1 := by omega
      have h1 : k₁ ∈ (subGates n C R).filter (fun k => u ∈ deps n C k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₁⟩, hd₁⟩
      have h2 : k₂ ∈ (subGates n C R).filter (fun k => u ∈ deps n C k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₂⟩, hd₂⟩
      exact Finset.card_le_one_iff.mp hle1 h1 h2
    rcases hS_ne with ⟨s, hs⟩
    have hs_mem := Finset.mem_filter.mp hs
    have hcu := chain_unate C hfit R (n + C.gates.length) s C.output hR_sub hR_up
      (fun u huR _ _ => by have := Finset.mem_range.mp (hR_sub huR); omega)
      (fun u huR _ hult => hdeg1_all u huR hult)
      C.output hout_R (le_refl _)
    rcases hcu with ⟨sign, hsign⟩
    have hs_reach : Reach n C s.val C.output :=
      ((hR_mem s.val).mp (Finset.mem_filter.mp (hE_sub hs_mem.1)).2).2
    have hspec := fun x => (hsign false x).2 hs_reach
    cases sign
    · rcases hs_mem.2.2 with ⟨x, h1, h2⟩
      have hm := (hspec x).1 rfl
      rw [evalOv_eq_wireVal_of_ge C false _ C.output hout_lt,
          evalOv_eq_wireVal_of_ge C false _ C.output hout_lt] at hm
      change f (Function.update x s false) = true → f (Function.update x s true) = true at hm
      have hres := hm h1
      rw [h2] at hres; simp at hres
    · rcases hs_mem.2.1 with ⟨x, h1, h2⟩
      have hm := (hspec x).2 rfl
      rw [evalOv_eq_wireVal_of_ge C false _ C.output hout_lt,
          evalOv_eq_wireVal_of_ge C false _ C.output hout_lt] at hm
      change f (Function.update x s true) = true → f (Function.update x s false) = true at hm
      have hres := hm (by simpa using h2)
      rw [h1] at hres; simp at hres

  have hδout_eq : (∑ u ∈ R.erase C.output, (outDeg n C R u - 1)) = 1 := by omega
  have hδin_B : (∑ k ∈ B_act, (2 - (deps n C k).card)) = 0 := by omega
  have hδin_N : (∑ k ∈ N_act, (1 - (deps n C k).card)) = 0 := by omega
  have hRin_card : (subInputs n R).card = E.card := by omega
  have hbin_eq : binary = E.card := by omega
  have hBact_eq : B_act.card = binary := by omega
  have hRin_eq_E : subInputs n R = E :=
    (Finset.eq_of_subset_of_card_le hE_sub (by omega)).symm
  have hB_full : ∀ k : Fin C.gates.length, n + k.val ∈ R → (C.gates[k.val]).op ≠ GateOp.not →
      (deps n C k).card = 2 := by
    intro k hk hnot
    have hkB : k ∈ B_act :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, hnot⟩
    have h0 := Finset.sum_eq_zero_iff.mp hδin_B k hkB
    have hle := deps_card_le_two (n := n) hfit k
    omega

  have hex_w : ∃ w ∈ R.erase C.output, outDeg n C R w = 2 ∧
      ∀ u ∈ R.erase C.output, u ≠ w → outDeg n C R u ≤ 1 := by
    have hne : ∃ w ∈ R.erase C.output, 0 < outDeg n C R w - 1 := by
      by_contra hall
      push Not at hall
      have h0 : (∑ u ∈ R.erase C.output, (outDeg n C R u - 1)) = 0 :=
        Finset.sum_eq_zero fun u hu => by have := hall u hu; omega
      omega
    rcases hne with ⟨w, hw, hwpos⟩
    have hrest : (∑ u ∈ (R.erase C.output).erase w, (outDeg n C R u - 1)) +
        (outDeg n C R w - 1) = 1 := by
      have := Finset.add_sum_erase (R.erase C.output) (fun u => outDeg n C R u - 1) hw
      omega
    have hw2 : outDeg n C R w = 2 := by omega
    have hrest0 : (∑ u ∈ (R.erase C.output).erase w, (outDeg n C R u - 1)) = 0 := by omega
    refine ⟨w, hw, hw2, fun u hu hne => ?_⟩
    have h0 := Finset.sum_eq_zero_iff.mp hrest0 u (Finset.mem_erase.mpr ⟨hne, hu⟩)
    omega
  rcases hex_w with ⟨w, hw_erase, hw_deg2, hother_deg1⟩
  have hw_ne_out : w ≠ C.output := (Finset.mem_erase.mp hw_erase).1
  have hw_R : w ∈ R := (Finset.mem_erase.mp hw_erase).2
  have hw_lt : w < n + C.gates.length := Finset.mem_range.mp (hR_sub hw_R)
  have hw_lt_out : w < C.output := lt_of_le_of_ne (hR_max w hw_R) hw_ne_out
  have hdeg1_ne_w : ∀ u ∈ R, u ≠ w → u < C.output →
      ∀ k₁ k₂ : Fin C.gates.length, n + k₁.val ∈ R → n + k₂.val ∈ R →
        u ∈ deps n C k₁ → u ∈ deps n C k₂ → k₁ = k₂ := by
    intro u huR huw hult k₁ k₂ hk₁ hk₂ hd₁ hd₂
    have hle1 := hother_deg1 u (Finset.mem_erase.mpr ⟨by omega, huR⟩) huw
    have h1 : k₁ ∈ (subGates n C R).filter (fun k => u ∈ deps n C k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₁⟩, hd₁⟩
    have h2 : k₂ ∈ (subGates n C R).filter (fun k => u ∈ deps n C k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₂⟩, hd₂⟩
    exact Finset.card_le_one_iff.mp hle1 h1 h2

  let U : Finset ℕ := R.filter (fun u => Reach n C u w)
  let U_in : Finset (Fin n) := subInputs n U
  have hU_sub_R : U ⊆ R := Finset.filter_subset _ _
  have hU_sub : U ⊆ Finset.range (n + C.gates.length) := Finset.Subset.trans hU_sub_R hR_sub
  have hw_U : w ∈ U := Finset.mem_filter.mpr ⟨hw_R, Relation.ReflTransGen.refl⟩
  have hU_max : ∀ u ∈ U, u ≤ w := fun u hu => reach_le (Finset.mem_filter.mp hu).2
  have hU_down : ∀ k : Fin C.gates.length, n + k.val ∈ U → ∀ a ∈ deps n C k, a ∈ U := by
    intro k hk a ha
    rcases Finset.mem_filter.mp hk with ⟨hkR, hkw⟩
    exact Finset.mem_filter.mpr ⟨hR_down k hkR a ha,
      Relation.ReflTransGen.head ⟨k, rfl, ha⟩ hkw⟩
  have hU_up : ∀ u ∈ U, u ≠ w → ∃ k : Fin C.gates.length, n + k.val ∈ U ∧ u ∈ deps n C k := by
    intro u hu hne
    rcases Finset.mem_filter.mp hu with ⟨_, huw⟩
    rcases Relation.ReflTransGen.cases_head huw with rfl | ⟨v, ⟨k, rfl, hdep⟩, hr'⟩
    · exact absurd rfl hne
    · exact ⟨k, Finset.mem_filter.mpr ⟨hR_up _ w hr' hw_R, hr'⟩, hdep⟩
  have hU_in_sub_E : U_in ⊆ E := by
    rw [← hRin_eq_E]
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU_sub_R (Finset.mem_filter.mp hi).2⟩

  have hcone_sep : ∀ k : Fin C.gates.length, n + k.val ∈ R → ¬ Reach n C (n + k.val) w →
      ∀ a ∈ deps n C k, a = w ∨ ¬ Reach n C a w := by
    intro k hkR hknw a ha
    by_cases haw : a = w
    · exact Or.inl haw
    · right
      intro haw_reach
      have haR : a ∈ R := hR_down k hkR a ha
      have haU : a ∈ U := Finset.mem_filter.mpr ⟨haR, haw_reach⟩
      rcases hU_up a haU haw with ⟨k', hk'U, ha_dep'⟩
      have hk'R : n + k'.val ∈ R := hU_sub_R hk'U
      have halt : a < C.output := lt_of_le_of_lt (reach_le haw_reach) hw_lt_out
      have hkeq := hdeg1_ne_w a haR haw halt k k' hkR hk'R ha ha_dep'
      subst hkeq
      exact hknw (Finset.mem_filter.mp hk'U).2

  let g : W → Bool := fun x => wireVal n C x w
  let F : W → Bool → Bool := fun y b => evalOv n C w b y C.output
  have hf_eq_F : ∀ x : W, f x = F x (g x) := fun x =>
    (evalOv_diag C w x C.output hout_lt).symm
  have hg_dep_U : ∀ x₁ x₂ : W, (∀ i ∈ U_in, x₁ i = x₂ i) → g x₁ = g x₂ := by
    intro x₁ x₂ hagree
    refine wireVal_congr_of_reach C w hw_lt fun i hir => ?_
    apply hagree
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hR_up i.val w hir hw_R, hir⟩⟩
  have hF_dep_out : ∀ (b : Bool) (y₁ y₂ : W), (∀ i ∈ E \ U_in, y₁ i = y₂ i) → F y₁ b = F y₂ b := by
    intro b y₁ y₂ hagree
    have hgen : ∀ u : ℕ, u ∈ R → (u = w ∨ ¬ Reach n C u w) →
        evalOv n C w b y₁ u = evalOv n C w b y₂ u := by
      intro u
      induction u using Nat.strong_induction_on with
      | ind u ih =>
        intro huR hcase
        by_cases heqw : u = w
        · subst heqw; rw [evalOv_eq_w, evalOv_eq_w]
        · have hnotR : ¬ Reach n C u w := hcase.resolve_left heqw
          have hult : u < n + C.gates.length := Finset.mem_range.mp (hR_sub huR)
          by_cases hlt : u < n
          · rw [evalOv_input C w b y₁ hlt heqw, evalOv_input C w b y₂ hlt heqw]
            apply hagree
            refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · rw [← hRin_eq_E]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huR⟩
            · intro hiU
              exact hnotR (Finset.mem_filter.mp (Finset.mem_filter.mp hiU).2).2
          · let k : Fin C.gates.length := ⟨u - n, by omega⟩
            have hvk : u = n + k.val := by dsimp [k]; omega
            rw [hvk] at huR hnotR heqw ⊢
            rw [evalOv_gate C w b y₁ k heqw, evalOv_gate C w b y₂ k heqw]
            refine gateEval_congr fun a ha => ?_
            have halt : a < n + k.val := deps_lt ha
            exact ih a (by omega) (hR_down k huR a ha) (hcone_sep k huR hnotR a ha)
    exact hgen C.output hout_R (Or.inr fun h => by have := reach_le h; omega)

  have hg_unate : ∀ i : Fin n, ∃ sg : Bool, ∀ x : W,
      (sg = false → g (Function.update x i false) = true → g (Function.update x i true) = true) ∧
      (sg = true → g (Function.update x i true) = true → g (Function.update x i false) = true) := by
    intro i
    rcases chain_unate C hfit R (n + C.gates.length) i w hR_sub hR_up
      (fun u huR _ _ => by have := Finset.mem_range.mp (hR_sub huR); omega)
      (fun u huR _ hult => hdeg1_ne_w u huR (by omega) (by omega))
      w hw_R (le_refl _) with ⟨sg, hsg⟩
    refine ⟨sg, fun x => ?_⟩
    by_cases hr : Reach n C i.val w
    · have h := (hsg false x).2 hr
      rw [evalOv_eq_wireVal_of_ge C false _ w hw_lt,
          evalOv_eq_wireVal_of_ge C false _ w hw_lt] at h
      exact h
    · have h := (hsg false x).1 hr
      rw [evalOv_eq_wireVal_of_ge C false _ w hw_lt,
          evalOv_eq_wireVal_of_ge C false _ w hw_lt] at h
      change g (Function.update x i false) = g (Function.update x i true) at h
      exact ⟨fun _ h1 => h ▸ h1, fun _ h1 => h.symm ▸ h1⟩

  have hF_unate_ex : ∀ i : Fin n, i ∉ U_in →
      ∃ τ : Bool, ∀ (b : Bool) (y : W),
        (τ = false → F (Function.update y i false) b = true → F (Function.update y i true) b = true) ∧
        (τ = true → F (Function.update y i true) b = true → F (Function.update y i false) b = true) := by
    intro i hi_notU
    have hi_nw : ¬ Reach n C i.val w := by
      intro hr
      apply hi_notU
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨hR_up i.val w hr hw_R, hr⟩⟩
    have hno_w : ∀ u ∈ R, Reach n C i.val u → u ≤ C.output → u ≠ w := by
      intro u _ hiu _ heq; subst heq; exact hi_nw hiu
    rcases chain_unate C hfit R w i C.output hR_sub hR_up hno_w
      (fun u huR hiu hult => hdeg1_ne_w u huR (hno_w u huR hiu (le_of_lt hult)) hult)
      C.output hout_R (le_refl _) with ⟨τ, hτ⟩
    refine ⟨τ, fun b y => ?_⟩
    by_cases hr : Reach n C i.val C.output
    · exact (hτ b y).2 hr
    · have h := (hτ b y).1 hr
      change F (Function.update y i false) b = F (Function.update y i true) b at h
      exact ⟨fun _ h1 => h ▸ h1, fun _ h1 => h.symm ▸ h1⟩

  have hS_sub_Uin : S ⊆ U_in := by
    intro i hiS
    by_contra hi_notU
    rcases hF_unate_ex i hi_notU with ⟨τ, hτ⟩
    have hg_eq : ∀ x : W, g (Function.update x i false) = g (Function.update x i true) := by
      intro x
      refine hg_dep_U _ _ fun j hj => ?_
      have hne : j ≠ i := fun heq => hi_notU (heq ▸ hj)
      simp [Function.update, hne]
    have hch := (Finset.mem_filter.mp hiS).2
    cases hτv : τ
    · rcases hch.2 with ⟨x, h1, h2⟩
      have hm := (hτ (g (Function.update x i false)) x).1 hτv
      rw [← hf_eq_F] at hm
      rw [hg_eq x, ← hf_eq_F] at hm
      have hres := hm h1
      rw [h2] at hres; simp at hres
    · rcases hch.1 with ⟨x, h1, h2⟩
      have hm := (hτ (g (Function.update x i false)) x).2 hτv
      rw [← hf_eq_F] at hm
      rw [hg_eq x, ← hf_eq_F] at hm
      have hres := hm (by simpa using h2)
      rw [h1] at hres; simp at hres

  have hpair_01_10 : (∃ y : W, F y false = false ∧ F y true = true) ∧
      (∃ y : W, F y false = true ∧ F y true = false) := by
    rcases hS_ne with ⟨s, hsS⟩
    have hsU : s ∈ U_in := hS_sub_Uin hsS
    have hch := (Finset.mem_filter.mp hsS).2
    rcases hg_unate s with ⟨sg, hsg⟩
    have hF_same : ∀ (x : W) (b : Bool),
        F (Function.update x s false) b = F (Function.update x s true) b := by
      intro x b
      refine hF_dep_out b _ _ fun j hj => ?_
      have hne : j ≠ s := fun heq => (Finset.mem_sdiff.mp hj).2 (heq ▸ hsU)
      simp [Function.update, hne]
    rcases hch.1 with ⟨x₁, hx₁0, hx₁1⟩
    rcases hch.2 with ⟨x₂, hx₂0, hx₂1⟩
    rw [hf_eq_F] at hx₁0 hx₁1 hx₂0 hx₂1
    rw [hF_same x₁ _] at hx₁0
    rw [hF_same x₂ _] at hx₂0
    have hne1 : g (Function.update x₁ s false) ≠ g (Function.update x₁ s true) := by
      intro heq; rw [heq, hx₁1] at hx₁0; simp at hx₁0
    have hne2 : g (Function.update x₂ s false) ≠ g (Function.update x₂ s true) := by
      intro heq; rw [heq, hx₂1] at hx₂0; simp at hx₂0
    cases hsgv : sg
    · have h1f : g (Function.update x₁ s false) = false := by
        cases h0 : g (Function.update x₁ s false)
        · rfl
        · have h1 := (hsg x₁).1 hsgv h0; exact absurd (h0.trans h1.symm) hne1
      have h1t : g (Function.update x₁ s true) = true := by
        cases h1 : g (Function.update x₁ s true)
        · exact absurd (h1f.trans h1.symm) hne1
        · rfl
      have h2f : g (Function.update x₂ s false) = false := by
        cases h0 : g (Function.update x₂ s false)
        · rfl
        · have h1 := (hsg x₂).1 hsgv h0; exact absurd (h0.trans h1.symm) hne2
      have h2t : g (Function.update x₂ s true) = true := by
        cases h1 : g (Function.update x₂ s true)
        · exact absurd (h2f.trans h1.symm) hne2
        · rfl
      rw [h1f] at hx₁0; rw [h1t] at hx₁1
      rw [h2f] at hx₂0; rw [h2t] at hx₂1
      exact ⟨⟨Function.update x₁ s true, hx₁0, by simpa using hx₁1⟩,
             ⟨Function.update x₂ s true, hx₂0, by simpa using hx₂1⟩⟩
    · have h1f : g (Function.update x₁ s false) = true := by
        cases h0 : g (Function.update x₁ s false)
        · cases h1 : g (Function.update x₁ s true)
          · exact absurd (h0.trans h1.symm) hne1
          · have := (hsg x₁).2 hsgv h1; rw [h0] at this; simp at this
        · rfl
      have h1t : g (Function.update x₁ s true) = false := by
        cases h1 : g (Function.update x₁ s true)
        · rfl
        · exact absurd (h1f.trans h1.symm) hne1
      have h2f : g (Function.update x₂ s false) = true := by
        cases h0 : g (Function.update x₂ s false)
        · cases h1 : g (Function.update x₂ s true)
          · exact absurd (h0.trans h1.symm) hne2
          · have := (hsg x₂).2 hsgv h1; rw [h0] at this; simp at this
        · rfl
      have h2t : g (Function.update x₂ s true) = false := by
        cases h1 : g (Function.update x₂ s true)
        · rfl
        · exact absurd (h2f.trans h1.symm) hne2
      rw [h1f] at hx₁0; rw [h1t] at hx₁1
      rw [h2f] at hx₂0; rw [h2t] at hx₂1
      exact ⟨⟨Function.update x₂ s true, by simpa using hx₂1, hx₂0⟩,
             ⟨Function.update x₁ s true, by simpa using hx₁1, hx₁0⟩⟩

  let τ : Fin n → Bool := fun i =>
    if h : i ∉ U_in then Classical.choose (hF_unate_ex i h) else false
  have hτ_spec : ∀ (i : Fin n) (h : i ∉ U_in) (b : Bool) (y : W),
      (τ i = false → F (Function.update y i false) b = true → F (Function.update y i true) b = true) ∧
      (τ i = true → F (Function.update y i true) b = true → F (Function.update y i false) b = true) := by
    intro i h b y
    have hspec := Classical.choose_spec (hF_unate_ex i h) b y
    simpa [τ, h] using hspec
  have hF_mono_order : ∀ (b : Bool) (y₁ y₂ : W),
      (∀ i : Fin n, i ∉ U_in → (y₁ i != τ i) = true → (y₂ i != τ i) = true) →
      F y₁ b = true → F y₂ b = true := by
    intro b y₁ y₂ hle h1
    have hstep : ∀ (T : Finset (Fin n)) (u : W),
        (∀ i : Fin n, i ∉ U_in → (u i != τ i) = true → (y₂ i != τ i) = true) →
        (∀ i ∈ E \ U_in, i ∉ T → u i = y₂ i) →
        F u b = true → F y₂ b = true := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro u _ hsame hu
        have heq := hF_dep_out b u y₂ (fun i hi => hsame i hi (by simp))
        rwa [← heq]
      | insert a T ha ih =>
        intro u hule hsame hu
        by_cases haU : a ∈ U_in
        · refine ih u hule (fun i hi hniT => hsame i hi fun hmem => ?_) hu
          rcases Finset.mem_insert.mp hmem with rfl | hT
          · exact (Finset.mem_sdiff.mp hi).2 haU
          · exact hniT hT
        · let u' := Function.update u a (y₂ a)
          have hu' : F u' b = true := by
            by_cases heq : u a = y₂ a
            · have : u' = u := by
                funext j; dsimp [u', Function.update]; split <;> simp_all
              rwa [this]
            · have hspec := hτ_spec a haU b u
              have htau : u a = τ a ∧ y₂ a = !τ a := by
                have hl := hule a haU
                cases hta : τ a <;> cases hua : u a <;> cases hy2a : y₂ a <;>
                  simp [hta, hua, hy2a] at hl heq ⊢
              rcases htau with ⟨hua, hy2a⟩
              have hu_eq : Function.update u a (u a) = u := Function.update_eq_self a u
              cases hta : τ a
              · rw [hta] at hua hy2a
                have h0 : F (Function.update u a false) b = true := by
                  have hupd : Function.update u a false = u := by rw [← hua, hu_eq]
                  rwa [hupd]
                have h2 := hspec.1 hta h0
                simpa [u', hy2a] using h2
              · rw [hta] at hua hy2a
                have h0 : F (Function.update u a true) b = true := by
                  have hupd : Function.update u a true = u := by rw [← hua, hu_eq]
                  rwa [hupd]
                have h2 := hspec.2 hta h0
                simpa [u', hy2a] using h2
          refine ih u' ?_ ?_ hu'
          · intro i hiU hbi
            dsimp [u', Function.update] at hbi
            by_cases hia : i = a
            · subst hia; simpa using hbi
            · simp only [hia, ↓reduceDIte] at hbi
              exact hule i hiU hbi
          · intro i hi hniT
            dsimp [u', Function.update]
            by_cases hia : i = a
            · simp [hia]
            · simp only [hia, ↓reduceDIte]
              exact hsame i hi (by simp [hia, hniT])
    exact hstep (E \ U_in) y₁ hle (fun i hi hni => absurd hi hni) h1

  have hall_pairs : ∀ p q : Bool, ∃ y : W, F y false = p ∧ F y true = q := by
    rcases hpair_01_10 with ⟨⟨y01, h01_0, h01_1⟩, ⟨y10, h10_0, h10_1⟩⟩
    let ymin : W := fun i => τ i
    let ymax : W := fun i => !τ i
    have hmin_0 : F ymin false = false := by
      cases h : F ymin false
      · rfl
      · have h1 := hF_mono_order false ymin y01 (fun i _ hbi => by simp [ymin] at hbi) h
        rw [h01_0] at h1; simp at h1
    have hmin_1 : F ymin true = false := by
      cases h : F ymin true
      · rfl
      · have h1 := hF_mono_order true ymin y10 (fun i _ hbi => by simp [ymin] at hbi) h
        rw [h10_1] at h1; simp at h1
    have hmax_0 : F ymax false = true :=
      hF_mono_order false y10 ymax (fun i _ _ => by simp [ymax]) h10_0
    have hmax_1 : F ymax true = true :=
      hF_mono_order true y01 ymax (fun i _ _ => by simp [ymax]) h01_1
    intro p q
    cases p <;> cases q
    · exact ⟨ymin, hmin_0, hmin_1⟩
    · exact ⟨y01, h01_0, h01_1⟩
    · exact ⟨y10, h10_0, h10_1⟩
    · exact ⟨ymax, hmax_0, hmax_1⟩

  have hS_eq_Uin : S = U_in := by
    apply Finset.Subset.antisymm hS_sub_Uin
    intro i hiU
    have hiE : i ∈ E := hU_in_sub_E hiU
    refine Finset.mem_filter.mpr ⟨hiE, ?_⟩

    have hex_g : ∃ x : W, g (Function.update x i false) ≠ g (Function.update x i true) := by
      have hch : change i false ∨ change i true := (Finset.mem_filter.mp hiE).2
      have hfrom : ∀ v, change i v → ∃ x : W, g (Function.update x i false) ≠ g (Function.update x i true) := by
        rintro v ⟨x, h1, h2⟩
        refine ⟨x, fun heq => ?_⟩
        rw [hf_eq_F] at h1 h2
        have hFs : F (Function.update x i false) (g (Function.update x i false)) =
            F (Function.update x i true) (g (Function.update x i true)) := by
          rw [heq]
          refine hF_dep_out _ _ _ fun j hj => ?_
          have hne : j ≠ i := fun h => (Finset.mem_sdiff.mp hj).2 (h ▸ hiU)
          simp [Function.update, hne]
        rw [h1, h2] at hFs
        cases v <;> simp at hFs
      rcases hch with h | h <;> exact hfrom _ h
    rcases hex_g with ⟨x, hgx⟩
    let b0 := g (Function.update x i false)
    let b1 := g (Function.update x i true)
    have hbne : b0 ≠ b1 := hgx
    have hmerge_g : ∀ (y : W) (c : Bool),
        g (Function.update (fun j => if j ∈ U_in then x j else y j) i c) =
        g (Function.update x i c) := by
      intro y c
      refine hg_dep_U _ _ fun j hj => ?_
      by_cases hji : j = i
      · simp [hji]
      · simp [Function.update, hji, hj]
    have hmerge_F : ∀ (y : W) (c : Bool) (b : Bool),
        F (Function.update (fun j => if j ∈ U_in then x j else y j) i c) b = F y b := by
      intro y c b
      refine hF_dep_out b _ _ fun j hj => ?_
      rcases Finset.mem_sdiff.mp hj with ⟨_, hjU⟩
      have hne : j ≠ i := fun h => hjU (h ▸ hiU)
      simp [Function.update, hne, hjU]
    constructor
    ·
      rcases hall_pairs (if b0 then true else false) (if b0 then false else true) with ⟨y, hy0, hy1⟩
      refine ⟨fun j => if j ∈ U_in then x j else y j, ?_, ?_⟩
      · rw [hf_eq_F, hmerge_g, hmerge_F]
        change F y b0 = false
        cases hb0 : b0
        · simpa [hb0] using hy0
        · simpa [hb0] using hy1
      · rw [hf_eq_F, hmerge_g, hmerge_F]
        change F y b1 = !false
        cases hb0 : b0 <;> cases hb1 : b1
        · exact absurd (hb0.trans hb1.symm) hbne
        · simpa [hb0] using hy1
        · simpa [hb0] using hy0
        · exact absurd (hb0.trans hb1.symm) hbne
    ·
      rcases hall_pairs (if b0 then false else true) (if b0 then true else false) with ⟨y, hy0, hy1⟩
      refine ⟨fun j => if j ∈ U_in then x j else y j, ?_, ?_⟩
      · rw [hf_eq_F, hmerge_g, hmerge_F]
        change F y b0 = true
        cases hb0 : b0
        · simpa [hb0] using hy0
        · simpa [hb0] using hy1
      · rw [hf_eq_F, hmerge_g, hmerge_F]
        change F y b1 = !true
        cases hb0 : b0 <;> cases hb1 : b1
        · exact absurd (hb0.trans hb1.symm) hbne
        · simpa [hb0] using hy1
        · simpa [hb0] using hy0
        · exact absurd (hb0.trans hb1.symm) hbne
  have hdiff_ge2 : 2 ≤ (E \ U_in).card :=
    card_ge_two_of_four_pairs (E \ U_in) (fun y => (F y false, F y true))
      (fun ⟨p, q⟩ => by rcases hall_pairs p q with ⟨y, h1, h2⟩; exact ⟨y, Prod.ext h1 h2⟩)
      (fun y₁ y₂ h => Prod.ext (hF_dep_out false y₁ y₂ h) (hF_dep_out true y₁ y₂ h))
  have hS_add2 : S.card + 2 ≤ E.card := by
    rw [hS_eq_Uin]
    have hcard_sdiff : (E \ U_in).card = E.card - U_in.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hU_in_sub_E]
    have hle : U_in.card ≤ E.card := Finset.card_le_card hU_in_sub_E
    omega

  have hf_merge : ∀ x y : W, f (merge x y) = F y (g x) := by
    intro x y
    rw [hf_eq_F]
    have hg_m : g (merge x y) = g x := by
      refine hg_dep_U _ _ fun j hj => ?_
      have hjS : j ∈ S := by rwa [hS_eq_Uin]
      simp [merge, hjS]
    have hF_m : F (merge x y) (g x) = F y (g x) := by
      refine hF_dep_out (g x) _ _ fun j hj => ?_
      have hjS : j ∉ S := by rw [hS_eq_Uin]; exact (Finset.mem_sdiff.mp hj).2
      simp [merge, hjS]
    rw [hg_m, hF_m]
  have hcode_eq : ∀ x : W, code x = (g x != g z) := by
    intro x
    dsimp only [code]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, bne_iff_ne]
    constructor
    · rintro ⟨y, hne⟩ heq
      rw [hf_merge, hf_merge, heq] at hne
      exact hne rfl
    · intro hne
      rcases hall_pairs false true with ⟨y, hy0, hy1⟩
      refine ⟨y, ?_⟩
      rw [hf_merge, hf_merge]
      cases hgx : g x <;> cases hgz : g z
      · exact absurd (hgx.trans hgz.symm) hne
      · rw [hy0, hy1]; decide
      · rw [hy1, hy0]; decide
      · exact absurd (hgx.trans hgz.symm) hne

  have hcode_unate : ∀ i : Fin n, ∃ sign : Bool, ∀ input : W,
      code (Function.update input i false) = sign →
      code (Function.update input i true) = sign := by
    intro i
    rcases hg_unate i with ⟨sg, hsg⟩
    cases hgz : g z
    ·
      cases hsgv : sg
      · refine ⟨true, fun input h => ?_⟩
        rw [hcode_eq, hgz, Bool.bne_false] at h ⊢
        exact (hsg input).1 hsgv h
      · refine ⟨false, fun input h => ?_⟩
        rw [hcode_eq, hgz, Bool.bne_false] at h ⊢
        cases ht : g (Function.update input i true)
        · rfl
        · have hf := (hsg input).2 hsgv ht; rw [h] at hf; simp at hf
    ·
      cases hsgv : sg
      · refine ⟨false, fun input h => ?_⟩
        rw [hcode_eq, hgz, Bool.bne_true] at h ⊢
        have ht : g (Function.update input i false) = true := by
          cases hf : g (Function.update input i false) <;> simp [hf] at h ⊢
        have h1 := (hsg input).1 hsgv ht
        simp [h1]
      · refine ⟨true, fun input h => ?_⟩
        rw [hcode_eq, hgz, Bool.bne_true] at h ⊢
        have hf : g (Function.update input i false) = false := by
          cases hf' : g (Function.update input i false) <;> simp [hf'] at h ⊢
        cases ht : g (Function.update input i true)
        · rfl
        · have h1 := (hsg input).2 hsgv ht; rw [hf] at h1; simp at h1

  have hex_hi : ∃ hi : W,
      (∀ x y : W, f (merge x y) = if code x then f (merge hi y) else f (merge z y)) ∧
      (∀ p q : Bool, ∃ y : W, f (merge z y) = p ∧ f (merge hi y) = q) := by
    have hhi_ex : ∃ hi : W, g hi = !g z := by
      rcases hS_ne with ⟨s, hsS⟩
      have hsE : s ∈ E := (Finset.mem_filter.mp hsS).1
      have hch := (Finset.mem_filter.mp hsS).2
      rcases hch.1 with ⟨x, h1, h2⟩
      have hne : g (Function.update x s false) ≠ g (Function.update x s true) := by
        intro heq
        rw [hf_eq_F] at h1 h2
        have hsU : s ∈ U_in := hS_sub_Uin hsS
        have hFs : F (Function.update x s false) (g (Function.update x s false)) =
            F (Function.update x s true) (g (Function.update x s true)) := by
          rw [heq]
          refine hF_dep_out _ _ _ fun j hj => ?_
          have hnej : j ≠ s := fun h => (Finset.mem_sdiff.mp hj).2 (h ▸ hsU)
          simp [Function.update, hnej]
        rw [h1, h2] at hFs; simp at hFs
      by_cases h0 : g (Function.update x s false) = g z
      · refine ⟨Function.update x s true, ?_⟩
        cases ht : g (Function.update x s true) <;> cases hgz : g z <;>
          simp [h0, ht, hgz] at hne ⊢
      · refine ⟨Function.update x s false, ?_⟩
        cases hf : g (Function.update x s false) <;> cases hgz : g z <;>
          simp [hf, hgz] at h0 ⊢
    rcases hhi_ex with ⟨hi, hghi⟩
    refine ⟨hi, fun x y => ?_, fun p q => ?_⟩
    · rw [hf_merge, hf_merge, hf_merge, hcode_eq]
      cases g x <;> cases hgz : g z <;> simp [hghi, hgz]
    · cases hgz : g z
      · rcases hall_pairs p q with ⟨y, hy0, hy1⟩
        refine ⟨y, ?_, ?_⟩
        · rw [hf_merge, hgz]; exact hy0
        · rw [hf_merge, hghi, hgz]; simpa using hy1
      · rcases hall_pairs q p with ⟨y, hy0, hy1⟩
        refine ⟨y, ?_, ?_⟩
        · rw [hf_merge, hgz]; exact hy1
        · rw [hf_merge, hghi, hgz]; simpa using hy0

  have hsingle_not : C.size ≤ E.card + 1 →
      C.size = E.card + 1 ∧ code o = true ∧
      ∃ P : Circuit, Monotone2 P ∧ P.size + 1 = S.card ∧
        (∀ x : W, P.eval (List.ofFn x) = code x) :=
    single_not_case C hfit R U E S w code hR_sub hout_R hR_down hU_sub_R hw_U hw_lt_out
      hU_max hU_down hU_up (fun u => Finset.mem_filter) hcone_sep hother_deg1 hB_full
      hS_eq_Uin hbin_eq hpair_01_10.2 hcode_eq
  exact ⟨hbin_eq, hS_add2, hcode_unate, hex_hi, hsingle_not⟩

end PEqualNP.Outside.L_lib_570_aux

theorem PEqualNP.Outside.L_lib_570 : (∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C →
  let W := Fin n → Bool
  let f := fun (x : W) => C.eval (List.ofFn x)
  let change := fun (j : Fin n) (v : Bool) =>
    ∃ x : W, f (Function.update x j false) = v ∧ f (Function.update x j true) = !v
  let E := (Finset.univ : Finset (Fin n)).filter (fun j => change j false ∨ change j true)
  let S := E.filter (fun j => change j false ∧ change j true)
  let merge := fun (x y : W) (j : Fin n) => if j ∈ S then x j else y j
  let z : W := fun _ => false
  let o : W := fun _ => true
  let code := fun (x : W) => decide (∃ y : W, f (merge x y) ≠ f (merge z y))
  let binary := (C.gates.filter (fun g => @decide (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  S.Nonempty → binary ≤ E.card →
    binary = E.card ∧ S.card + 2 ≤ E.card ∧
    (∀ i : Fin n, ∃ sign : Bool, ∀ input : W,
      code (Function.update input i false) = sign →
      code (Function.update input i true) = sign) ∧
    (∃ hi : W,
      (∀ x y : W, f (merge x y) =
        if code x then f (merge hi y) else f (merge z y)) ∧
      (∀ p q : Bool, ∃ y : W, f (merge z y) = p ∧ f (merge hi y) = q)) ∧
    (C.size ≤ E.card + 1 →
      C.size = E.card + 1 ∧ code o = true ∧
      ∃ P : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 P ∧ P.size + 1 = S.card ∧
        (∀ x : W, P.eval (List.ofFn x) = code x))) := by
  exact PEqualNP.Outside.L_lib_570_aux.prove_570

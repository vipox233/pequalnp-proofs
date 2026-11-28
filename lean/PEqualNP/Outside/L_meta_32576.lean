import PEqualNP.Defs
import Mathlib.Analysis.Complex.Polynomial.GaussLucas

namespace PEqualNP.Outside.L_meta_32576_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Polynomial

private def IsMatching {α : Type*} [DecidableEq α] (V : Finset α) (M : Finset (Finset α)) : Prop :=
  (∀ e ∈ M, e.card = 2 ∧ e ⊆ V) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂)

private instance {α : Type*} [DecidableEq α] (V : Finset α) (M : Finset (Finset α)) :
    Decidable (IsMatching V M) := by
  unfold IsMatching; infer_instance

private def matchFn {n : ℕ} (M : Finset (Finset (Fin n))) (x y : Fin n → Bool) : Bool :=
  decide ((∃ i : Fin n, x i = true ∧ y i = true) ∨
    (∃ e ∈ M, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)))

private def matchFnOn {n : ℕ} (S : Finset (Fin n)) (M : Finset (Finset (Fin n)))
    (x y : Fin n → Bool) : Bool :=
  decide ((∃ i ∈ S, x i = true ∧ y i = true) ∨
    (∃ e ∈ M, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)))

private lemma wires_append (g₁ g₂ : List Gate) (inp : List Bool) (o : ℕ) :
    (Circuit.mk (g₁ ++ g₂) o).wires inp = (Circuit.mk g₂ o).wires ((Circuit.mk g₁ o).wires inp) := by
  simp [Circuit.wires, List.foldl_append]

private lemma wires_length (gs : List Gate) (inp : List Bool) (o : ℕ) :
    ((Circuit.mk gs o).wires inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

private lemma wires_getD_prefix (gs : List Gate) (inp : List Bool) (o k : ℕ) (hk : k < inp.length) :
    ((Circuit.mk gs o).wires inp).getD k false = inp.getD k false := by
  induction gs generalizing inp with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih (inp ++ [g.op.eval (g.inputs.map fun i => inp.getD i false)]) (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private lemma wires_getD_step (gs : List Gate) (g : Gate) (inp : List Bool) (o : ℕ) :
    ((Circuit.mk (gs ++ [g]) o).wires inp).getD (inp.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => ((Circuit.mk gs o).wires inp).getD i false) := by
  rw [wires_append]
  set w := (Circuit.mk gs o).wires inp
  have hw : w.length = inp.length + gs.length := wires_length gs inp o
  simp only [Circuit.wires, List.foldl_cons, List.foldl_nil]
  rw [← hw]
  simp [List.getD_eq_getElem?_getD]

private lemma wires_getD_gate (C : Circuit) (inp : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires inp).getD (inp.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < inp.length + j then (C.wires inp).getD i false else false) := by
  have hsplit : C.gates = (C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [List.append_assoc, List.singleton_append, ← h2, h1]
  have hlen : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hstep : ((Circuit.mk (C.gates.take j ++ [C.gates[j]]) 0).wires inp).getD (inp.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        ((Circuit.mk (C.gates.take j) 0).wires inp).getD i false) := by
    have hs := wires_getD_step (C.gates.take j) C.gates[j] inp 0
    rw [hlen] at hs; exact hs
  have hpref1 : (C.wires inp).getD (inp.length + j) false =
      ((Circuit.mk (C.gates.take j ++ [C.gates[j]]) 0).wires inp).getD (inp.length + j) false := by
    have heq : C.wires inp = (Circuit.mk ((C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1)) 0).wires inp := by
      simp only [Circuit.wires, ← hsplit]
    rw [heq, wires_append]
    exact wires_getD_prefix _ _ 0 _ (by rw [wires_length]; simp; omega)
  rw [hpref1, hstep]
  congr 1
  refine List.map_congr_left (fun i _ => ?_)
  by_cases hi : i < inp.length + j
  · simp only [hi, ↓reduceIte]
    have hpref2 : (C.wires inp).getD i false =
        ((Circuit.mk (C.gates.take j) 0).wires inp).getD i false := by
      have heq : C.wires inp = (Circuit.mk (C.gates.take j ++ C.gates.drop j) 0).wires inp := by
        simp only [Circuit.wires, List.take_append_drop]
      rw [heq, wires_append]
      exact wires_getD_prefix _ _ 0 _ (by rw [wires_length, hlen]; exact hi)
    exact hpref2.symm
  · simp only [hi, ↓reduceIte]
    have hlen2 : ((Circuit.mk (C.gates.take j) 0).wires inp).length = inp.length + j := by
      rw [wires_length, hlen]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

private lemma wires_getD_oob (C : Circuit) (inp : List Bool) (w : ℕ)
    (hw : inp.length + C.gates.length ≤ w) :
    (C.wires inp).getD w false = false := by
  have hlen : (C.wires inp).length = inp.length + C.gates.length := wires_length C.gates inp C.output
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

private lemma gateOp_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {l₁ l₂ : List Bool} (hlen : l₁.length = l₂.length)
    (hle : ∀ i (h1 : i < l₁.length) (h2 : i < l₂.length), l₁[i] ≤ l₂[i]) :
    op.eval l₁ ≤ op.eval l₂ := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval]
    cases h1 : l₁.all id
    · exact Bool.false_le _
    · have h2 : l₂.all id = true := by
        rw [List.all_eq_true] at h1 ⊢
        intro b hb
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
        have h1i : l₁[i]'(by omega) = true := h1 _ (List.getElem_mem _)
        have hle_i := hle i (by omega) hi
        rw [h1i] at hle_i
        exact Bool.eq_true_of_true_le hle_i
      rw [h2]
  · simp only [GateOp.eval]
    cases h1 : l₁.any id
    · exact Bool.false_le _
    · have h2 : l₂.any id = true := by
        rw [List.any_eq_true] at h1 ⊢
        rcases h1 with ⟨a, ha, ha_t⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
        refine ⟨l₂[i]'(by omega), List.getElem_mem _, ?_⟩
        have hle_i := hle i hi (by omega)
        simp only [id_eq] at ha_t ⊢
        rw [ha_t] at hle_i
        exact Bool.eq_true_of_true_le hle_i
      rw [h2]

private lemma monotone2_wires_mono (C : Circuit) (hM : Monotone2 C)
    {inp₁ inp₂ : List Bool} (hlen : inp₁.length = inp₂.length)
    (hle : ∀ i, inp₁.getD i false ≤ inp₂.getD i false) :
    ∀ w, (C.wires inp₁).getD w false ≤ (C.wires inp₂).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < inp₁.length
    · have hp1 := wires_getD_prefix C.gates inp₁ C.output w h1
      have hp2 := wires_getD_prefix C.gates inp₂ C.output w (by omega)
      rw [hp1, hp2]
      exact hle w
    · by_cases h2 : w < inp₁.length + C.gates.length
      · set j := w - inp₁.length
        have hj : j < C.gates.length := by omega
        have hw1 : w = inp₁.length + j := by omega
        have hw2 : w = inp₂.length + j := by omega
        rw [hw1, wires_getD_gate C inp₁ j hj]
        rw [← hw1, hw2, wires_getD_gate C inp₂ j hj]
        refine gateOp_mono (C.gates[j]).op (hM _ (List.getElem_mem hj)).1 (by simp) ?_
        intro idx hidx1 hidx2
        have hidx : idx < (C.gates[j]).inputs.length := by simpa using hidx1
        simp only [List.getElem_map]
        by_cases hlt : (C.gates[j]).inputs[idx]'hidx < inp₁.length + j
        · have hlt2 : (C.gates[j]).inputs[idx]'hidx < inp₂.length + j := by omega
          simp only [hlt, hlt2, ↓reduceIte]
          exact ih _ (by omega)
        · have hlt2 : ¬ (C.gates[j]).inputs[idx]'hidx < inp₂.length + j := by omega
          simp only [hlt, hlt2, ↓reduceIte]
          exact le_refl false
      · rw [wires_getD_oob C inp₁ w (by omega), wires_getD_oob C inp₂ w (by omega)]

private def gateParents (C : Circuit) (m w : ℕ) : Finset ℕ :=
  if h : m ≤ w ∧ w - m < C.gates.length then
    ((C.gates[w - m]'(h.2)).inputs.filter (fun u => decide (u < w))).toFinset
  else ∅

private lemma mem_gateParents_lt (C : Circuit) (m w u : ℕ) (hu : u ∈ gateParents C m w) : u < w := by
  unfold gateParents at hu
  split_ifs at hu with h
  · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2
  · simp at hu

private lemma gateParents_card_le (C : Circuit) (hM : Monotone2 C) (m w : ℕ) :
    (gateParents C m w).card ≤ 2 := by
  unfold gateParents
  split_ifs with h
  · have hlen := (hM _ (List.getElem_mem h.2)).2
    calc
      ((C.gates[w - m]'(h.2)).inputs.filter (fun u => decide (u < w))).toFinset.card
        ≤ ((C.gates[w - m]'(h.2)).inputs.filter (fun u => decide (u < w))).length := List.toFinset_card_le _
      _ ≤ (C.gates[w - m]'(h.2)).inputs.length := List.length_filter_le _ _
      _ ≤ 2 := hlen
  · simp

private def reach (C : Circuit) (m : ℕ) (w : ℕ) : Finset ℕ :=
  insert w ((gateParents C m w).attach.biUnion (fun u => reach C m u.1))
termination_by w
decreasing_by exact mem_gateParents_lt C m w u.1 u.2

private lemma reach_eq (C : Circuit) (m w : ℕ) :
    reach C m w = insert w ((gateParents C m w).biUnion (reach C m)) := by
  conv_lhs => rw [reach]
  ext x
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, exists_prop]

private lemma self_mem_reach (C : Circuit) (m w : ℕ) : w ∈ reach C m w := by
  rw [reach_eq]; exact Finset.mem_insert_self _ _

private lemma reach_subset_of_mem_gateParents (C : Circuit) (m w u : ℕ)
    (hu : u ∈ gateParents C m w) : reach C m u ⊆ reach C m w := by
  intro x hx
  rw [reach_eq]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hx⟩)

private lemma mem_reach_le (C : Circuit) (m w x : ℕ) (hx : x ∈ reach C m w) : x ≤ w := by
  induction w using Nat.strong_induction_on generalizing x with
  | ind w ih =>
    rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hx
    rcases hx with rfl | ⟨u, hu, hxu⟩
    · exact le_refl _
    · exact le_trans (ih u (mem_gateParents_lt C m w u hu) x hxu) (Nat.le_of_lt (mem_gateParents_lt C m w u hu))

private lemma reach_eq_on_wires (C : Circuit) (m : ℕ) {inp₁ inp₂ : List Bool}
    (h1 : inp₁.length = m) (h2 : inp₂.length = m) (w : ℕ)
    (hagree : ∀ i < m, i ∈ reach C m w → inp₁.getD i false = inp₂.getD i false) :
    (C.wires inp₁).getD w false = (C.wires inp₂).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < m
    · rw [wires_getD_prefix C.gates inp₁ C.output w (by omega),
          wires_getD_prefix C.gates inp₂ C.output w (by omega)]
      exact hagree w hw (self_mem_reach C m w)
    · by_cases hw2 : w < m + C.gates.length
      · set j := w - m
        have hj : j < C.gates.length := by omega
        have hwm1 : w = inp₁.length + j := by omega
        have hwm2 : w = inp₂.length + j := by omega
        rw [hwm1, wires_getD_gate C inp₁ j hj]
        rw [← hwm1, hwm2, wires_getD_gate C inp₂ j hj]
        congr 1
        refine List.map_congr_left (fun u hu => ?_)
        by_cases hlt : u < w
        · have hlt1 : u < inp₁.length + j := by omega
          have hlt2 : u < inp₂.length + j := by omega
          simp only [hlt1, hlt2, ↓reduceIte]
          have hup : u ∈ gateParents C m w := by
            unfold gateParents
            have hcond : m ≤ w ∧ w - m < C.gates.length := ⟨by omega, hj⟩
            rw [dif_pos hcond]
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
            exact ⟨hu, hlt⟩
          exact ih u hlt (fun i him hi => hagree i him (reach_subset_of_mem_gateParents C m w u hup hi))
        · have hlt1 : ¬ u < inp₁.length + j := by omega
          have hlt2 : ¬ u < inp₂.length + j := by omega
          simp only [hlt1, hlt2, ↓reduceIte]
      · rw [wires_getD_oob C inp₁ w (by omega), wires_getD_oob C inp₂ w (by omega)]

private lemma biUnion_card_eq_sum_iff_disjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card = ∑ a ∈ s, (f a).card →
    ∀ a₁ ∈ s, ∀ a₂ ∈ s, a₁ ≠ a₂ → Disjoint (f a₁) (f a₂) := by
  intro heq a₁ ha₁ a₂ ha₂ hne
  by_contra hnd
  rw [Finset.not_disjoint_iff] at hnd
  rcases hnd with ⟨b, hb1, hb2⟩
  have hsub : s.biUnion f = (f a₁ ∪ f a₂) ∪ ((s.erase a₁).erase a₂).biUnion f := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro ⟨a, ha, hxa⟩
      by_cases h1 : a = a₁
      · left; left; rwa [← h1]
      · by_cases h2 : a = a₂
        · left; right; rwa [← h2]
        · right; exact ⟨a, ⟨h2, h1, ha⟩, hxa⟩
    · rintro ((hx | hx) | ⟨a, ⟨_, _, ha⟩, hxa⟩)
      · exact ⟨a₁, ha₁, hx⟩
      · exact ⟨a₂, ha₂, hx⟩
      · exact ⟨a, ha, hxa⟩
  have hlt : (f a₁ ∪ f a₂).card < (f a₁).card + (f a₂).card := by
    have hpos : 0 < (f a₁ ∩ f a₂).card := Finset.card_pos.mpr ⟨b, Finset.mem_inter.mpr ⟨hb1, hb2⟩⟩
    have hu := Finset.card_union_add_card_inter (f a₁) (f a₂)
    omega
  have hsum : ∑ a ∈ s, (f a).card =
      (f a₁).card + (f a₂).card + ∑ a ∈ (s.erase a₁).erase a₂, (f a).card := by
    have h1 := Finset.add_sum_erase s (fun a => (f a).card) ha₁
    have ha₂' : a₂ ∈ s.erase a₁ := Finset.mem_erase.mpr ⟨hne.symm, ha₂⟩
    have h2 := Finset.add_sum_erase (s.erase a₁) (fun a => (f a).card) ha₂'
    omega
  have hle : (s.biUnion f).card ≤ (f a₁ ∪ f a₂).card + ∑ a ∈ (s.erase a₁).erase a₂, (f a).card := by
    rw [hsub]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (Finset.card_biUnion_le) _)
  omega

private inductive MTree (n : ℕ) where
  | leafL (i : Fin n)
  | leafR (i : Fin n)
  | and (t₁ t₂ : MTree n)
  | or (t₁ t₂ : MTree n)

private def MTree.eval {n : ℕ} : MTree n → (Fin n → Bool) → (Fin n → Bool) → Bool
  | .leafL i, x, _ => x i
  | .leafR i, _, y => y i
  | .and t₁ t₂, x, y => t₁.eval x y && t₂.eval x y
  | .or t₁ t₂, x, y => t₁.eval x y || t₂.eval x y

private def MTree.vars {n : ℕ} : MTree n → Finset (Fin n ⊕ Fin n)
  | .leafL i => {Sum.inl i}
  | .leafR i => {Sum.inr i}
  | .and t₁ t₂ => t₁.vars ∪ t₂.vars
  | .or t₁ t₂ => t₁.vars ∪ t₂.vars

private def MTree.ReadOnce {n : ℕ} : MTree n → Prop
  | .leafL _ => True
  | .leafR _ => True
  | .and t₁ t₂ => t₁.ReadOnce ∧ t₂.ReadOnce ∧ Disjoint t₁.vars t₂.vars
  | .or t₁ t₂ => t₁.ReadOnce ∧ t₂.ReadOnce ∧ Disjoint t₁.vars t₂.vars

private lemma MTree.vars_nonempty {n : ℕ} (t : MTree n) : t.vars.Nonempty := by
  induction t with
  | leafL i => exact ⟨Sum.inl i, Finset.mem_singleton_self _⟩
  | leafR i => exact ⟨Sum.inr i, Finset.mem_singleton_self _⟩
  | and _ _ ih₁ _ => exact ih₁.mono Finset.subset_union_left
  | or _ _ ih₁ _ => exact ih₁.mono Finset.subset_union_left

private lemma MTree.eval_zero {n : ℕ} (t : MTree n) :
    t.eval (fun _ => false) (fun _ => false) = false := by
  induction t with
  | leafL _ => rfl
  | leafR _ => rfl
  | and _ _ ih₁ ih₂ => simp [MTree.eval, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [MTree.eval, ih₁, ih₂]

private lemma MTree.eval_eq_of_eq_on_vars {n : ℕ} (t : MTree n) {x₁ x₂ y₁ y₂ : Fin n → Bool}
    (hx : ∀ i, Sum.inl i ∈ t.vars → x₁ i = x₂ i)
    (hy : ∀ i, Sum.inr i ∈ t.vars → y₁ i = y₂ i) :
    t.eval x₁ y₁ = t.eval x₂ y₂ := by
  induction t with
  | leafL i => exact hx i (Finset.mem_singleton_self _)
  | leafR i => exact hy i (Finset.mem_singleton_self _)
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [MTree.eval]
    rw [ih₁ (fun i hi => hx i (Finset.mem_union_left _ hi))
            (fun i hi => hy i (Finset.mem_union_left _ hi)),
        ih₂ (fun i hi => hx i (Finset.mem_union_right _ hi))
            (fun i hi => hy i (Finset.mem_union_right _ hi))]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [MTree.eval]
    rw [ih₁ (fun i hi => hx i (Finset.mem_union_left _ hi))
            (fun i hi => hy i (Finset.mem_union_left _ hi)),
        ih₂ (fun i hi => hx i (Finset.mem_union_right _ hi))
            (fun i hi => hy i (Finset.mem_union_right _ hi))]

private lemma MTree.eval_mono {n : ℕ} (t : MTree n) {x₁ x₂ y₁ y₂ : Fin n → Bool}
    (hx : ∀ i, x₁ i ≤ x₂ i) (hy : ∀ i, y₁ i ≤ y₂ i) :
    t.eval x₁ y₁ ≤ t.eval x₂ y₂ := by
  induction t with
  | leafL i => exact hx i
  | leafR i => exact hy i
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [MTree.eval]
    cases h1 : t₁.eval x₁ y₁ <;> cases h2 : t₂.eval x₁ y₁
    · simp
    · simp
    · simp
    · rw [h1] at ih₁; rw [h2] at ih₂
      rw [Bool.eq_true_of_true_le ih₁, Bool.eq_true_of_true_le ih₂]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [MTree.eval]
    cases h1 : t₁.eval x₁ y₁ <;> cases h2 : t₂.eval x₁ y₁
    · simp
    · rw [h2] at ih₂; rw [Bool.eq_true_of_true_le ih₂]; simp
    · rw [h1] at ih₁; rw [Bool.eq_true_of_true_le ih₁]; simp
    · rw [h1] at ih₁; rw [Bool.eq_true_of_true_le ih₁]; simp

private def unitVec {n : ℕ} (i : Fin n) : Fin n → Bool := fun k => decide (k = i)

private lemma MTree.all_unit_true_is_or {n : ℕ} (t : MTree n) (hro : t.ReadOnce)
    (hL : ∀ i, Sum.inl i ∈ t.vars → t.eval (unitVec i) (fun _ => false) = true)
    (hR : ∀ i, Sum.inr i ∈ t.vars → t.eval (fun _ => false) (unitVec i) = true) :
    ∀ x y, t.eval x y =
      decide ((∃ i, Sum.inl i ∈ t.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t.vars ∧ y i = true)) := by
  induction t with
  | leafL i =>
    intro x y
    simp only [MTree.eval, MTree.vars, Finset.mem_singleton, Sum.inl.injEq,
      exists_eq_left, reduceCtorEq, false_and, exists_false, or_false, decide_eq_true_iff]
    cases x i <;> decide
  | leafR i =>
    intro x y
    simp only [MTree.eval, MTree.vars, Finset.mem_singleton, reduceCtorEq, false_and,
      exists_false, Sum.inr.injEq, exists_eq_left, false_or, decide_eq_true_iff]
    cases y i <;> decide
  | and t₁ t₂ _ _ =>
    exfalso
    rcases t₁.vars_nonempty with ⟨v, hv⟩
    have hv2 : v ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 hv
    cases v with
    | inl i =>
      have ht := hL i (Finset.mem_union_left _ hv)
      simp only [MTree.eval, Bool.and_eq_true] at ht
      have h0 : t₂.eval (unitVec i) (fun _ => false) = t₂.eval (fun _ => false) (fun _ => false) := by
        refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
        have hji : j ≠ i := fun h => hv2 (h ▸ hj)
        simp [unitVec, hji]
      rw [h0, t₂.eval_zero] at ht
      exact Bool.false_ne_true ht.2
    | inr i =>
      have ht := hR i (Finset.mem_union_left _ hv)
      simp only [MTree.eval, Bool.and_eq_true] at ht
      have h0 : t₂.eval (fun _ => false) (unitVec i) = t₂.eval (fun _ => false) (fun _ => false) := by
        refine t₂.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
        have hji : j ≠ i := fun h => hv2 (h ▸ hj)
        simp [unitVec, hji]
      rw [h0, t₂.eval_zero] at ht
      exact Bool.false_ne_true ht.2
  | or t₁ t₂ ih₁ ih₂ =>
    have hL₁ : ∀ i, Sum.inl i ∈ t₁.vars → t₁.eval (unitVec i) (fun _ => false) = true := by
      intro i hi
      have ht := hL i (Finset.mem_union_left _ hi)
      have hi2 : Sum.inl i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 hi
      have h0 : t₂.eval (unitVec i) (fun _ => false) = false := by
        refine (t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)).trans t₂.eval_zero
        have hji : j ≠ i := fun h => hi2 (h ▸ hj)
        simp [unitVec, hji]
      simp [MTree.eval, h0] at ht
      exact ht
    have hR₁ : ∀ i, Sum.inr i ∈ t₁.vars → t₁.eval (fun _ => false) (unitVec i) = true := by
      intro i hi
      have ht := hR i (Finset.mem_union_left _ hi)
      have hi2 : Sum.inr i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 hi
      have h0 : t₂.eval (fun _ => false) (unitVec i) = false := by
        refine (t₂.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)).trans t₂.eval_zero
        have hji : j ≠ i := fun h => hi2 (h ▸ hj)
        simp [unitVec, hji]
      simp [MTree.eval, h0] at ht
      exact ht
    have hL₂ : ∀ i, Sum.inl i ∈ t₂.vars → t₂.eval (unitVec i) (fun _ => false) = true := by
      intro i hi
      have ht := hL i (Finset.mem_union_right _ hi)
      have hi1 : Sum.inl i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hi
      have h0 : t₁.eval (unitVec i) (fun _ => false) = false := by
        refine (t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)).trans t₁.eval_zero
        have hji : j ≠ i := fun h => hi1 (h ▸ hj)
        simp [unitVec, hji]
      simp [MTree.eval, h0] at ht
      exact ht
    have hR₂ : ∀ i, Sum.inr i ∈ t₂.vars → t₂.eval (fun _ => false) (unitVec i) = true := by
      intro i hi
      have ht := hR i (Finset.mem_union_right _ hi)
      have hi1 : Sum.inr i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hi
      have h0 : t₁.eval (fun _ => false) (unitVec i) = false := by
        refine (t₁.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)).trans t₁.eval_zero
        have hji : j ≠ i := fun h => hi1 (h ▸ hj)
        simp [unitVec, hji]
      simp [MTree.eval, h0] at ht
      exact ht
    intro x y
    simp only [MTree.eval, ih₁ hro.1 hL₁ hR₁ x y, ih₂ hro.2.1 hL₂ hR₂ x y, MTree.vars,
      Finset.mem_union]
    by_cases h : (∃ i, (Sum.inl i ∈ t₁.vars ∨ Sum.inl i ∈ t₂.vars) ∧ x i = true) ∨
        (∃ i, (Sum.inr i ∈ t₁.vars ∨ Sum.inr i ∈ t₂.vars) ∧ y i = true)
    · rw [decide_eq_true h]
      rcases h with ⟨i, hi | hi, hxi⟩ | ⟨i, hi | hi, hyi⟩
      · have : decide ((∃ i, Sum.inl i ∈ t₁.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₁.vars ∧ y i = true)) = true :=
          decide_eq_true (Or.inl ⟨i, hi, hxi⟩)
        simp [this]
      · have : decide ((∃ i, Sum.inl i ∈ t₂.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₂.vars ∧ y i = true)) = true :=
          decide_eq_true (Or.inl ⟨i, hi, hxi⟩)
        simp [this]
      · have : decide ((∃ i, Sum.inl i ∈ t₁.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₁.vars ∧ y i = true)) = true :=
          decide_eq_true (Or.inr ⟨i, hi, hyi⟩)
        simp [this]
      · have : decide ((∃ i, Sum.inl i ∈ t₂.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₂.vars ∧ y i = true)) = true :=
          decide_eq_true (Or.inr ⟨i, hi, hyi⟩)
        simp [this]
    · rw [decide_eq_false h]
      have h1 : ¬ ((∃ i, Sum.inl i ∈ t₁.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₁.vars ∧ y i = true)) := by
        rintro (⟨i, hi, hxi⟩ | ⟨i, hi, hyi⟩)
        · exact h (Or.inl ⟨i, Or.inl hi, hxi⟩)
        · exact h (Or.inr ⟨i, Or.inl hi, hyi⟩)
      have h2 : ¬ ((∃ i, Sum.inl i ∈ t₂.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₂.vars ∧ y i = true)) := by
        rintro (⟨i, hi, hxi⟩ | ⟨i, hi, hyi⟩)
        · exact h (Or.inl ⟨i, Or.inr hi, hxi⟩)
        · exact h (Or.inr ⟨i, Or.inr hi, hyi⟩)
      simp [decide_eq_false h1, decide_eq_false h2]

private lemma classify_mtree {n : ℕ} :
    ∀ (t : MTree n) (S : Finset (Fin n)),
      S.Nonempty →
      t.ReadOnce →
      (∀ i, Sum.inl i ∈ t.vars ↔ i ∈ S) →
      (∀ i, Sum.inr i ∈ t.vars ↔ i ∈ S) →
      (∀ i ∈ S, t.eval (unitVec i) (unitVec i) = true) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → t.eval (unitVec i) (unitVec j) = false) →
      (∀ i ∈ S, t.eval (unitVec i) (fun _ => false) = false ∧
                t.eval (fun _ => false) (unitVec i) = false) →
      ∃ M : Finset (Finset (Fin n)), IsMatching S M ∧
        ∀ x y, t.eval x y = matchFnOn S M x y := by
  intro t
  induction t with
  | leafL i =>
    intro S hS _ hL hR _ _ hzero
    have hi : i ∈ S := (hL i).mp (Finset.mem_singleton_self _)
    have h0 := (hzero i hi).1
    simp [MTree.eval, unitVec] at h0
  | leafR i =>
    intro S hS _ hL hR _ _ hzero
    have hi : i ∈ S := (hR i).mp (Finset.mem_singleton_self _)
    have h0 := (hzero i hi).2
    simp [MTree.eval, unitVec] at h0
  | or t₁ t₂ ih₁ ih₂ =>
    intro S hS hro hL hR hdiag hoff hzero
    have hsame : ∀ i ∈ S, Sum.inl i ∈ t₁.vars ↔ Sum.inr i ∈ t₁.vars := by
      intro i hi
      have hL_in : Sum.inl i ∈ t₁.vars ∨ Sum.inl i ∈ t₂.vars := Finset.mem_union.mp ((hL i).mpr hi)
      have hR_in : Sum.inr i ∈ t₁.vars ∨ Sum.inr i ∈ t₂.vars := Finset.mem_union.mp ((hR i).mpr hi)
      have h10 : t₁.eval (unitVec i) (fun _ => false) = false := by
        have h := (hzero i hi).1; simp [MTree.eval] at h; exact h.1
      have h01 : t₁.eval (fun _ => false) (unitVec i) = false := by
        have h := (hzero i hi).2; simp [MTree.eval] at h; exact h.1
      have h20 : t₂.eval (unitVec i) (fun _ => false) = false := by
        have h := (hzero i hi).1; simp [MTree.eval] at h; exact h.2
      have h02 : t₂.eval (fun _ => false) (unitVec i) = false := by
        have h := (hzero i hi).2; simp [MTree.eval] at h; exact h.2
      constructor
      · intro h1L
        by_contra h1R
        have h2L : Sum.inl i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 h1L
        have he1 : t₁.eval (unitVec i) (unitVec i) = false := by
          rw [← h10]
          refine t₁.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
          have hji : j ≠ i := fun h => h1R (h ▸ hj)
          simp [unitVec, hji]
        have he2 : t₂.eval (unitVec i) (unitVec i) = false := by
          rw [← h02]
          refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
          have hji : j ≠ i := fun h => h2L (h ▸ hj)
          simp [unitVec, hji]
        have hd := hdiag i hi
        simp [MTree.eval, he1, he2] at hd
      · intro h1R
        by_contra h1L
        have h2R : Sum.inr i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 h1R
        have he1 : t₁.eval (unitVec i) (unitVec i) = false := by
          rw [← h01]
          refine t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
          have hji : j ≠ i := fun h => h1L (h ▸ hj)
          simp [unitVec, hji]
        have he2 : t₂.eval (unitVec i) (unitVec i) = false := by
          rw [← h20]
          refine t₂.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
          have hji : j ≠ i := fun h => h2R (h ▸ hj)
          simp [unitVec, hji]
        have hd := hdiag i hi
        simp [MTree.eval, he1, he2] at hd
    let S₁ := S.filter (fun i => decide (Sum.inl i ∈ t₁.vars))
    let S₂ := S.filter (fun i => decide (Sum.inl i ∈ t₂.vars))
    have hL₁ : ∀ i, Sum.inl i ∈ t₁.vars ↔ i ∈ S₁ := by
      intro i
      simp only [S₁, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨fun hi => ⟨(hL i).mp (Finset.mem_union_left _ hi), hi⟩, And.right⟩
    have hR₁ : ∀ i, Sum.inr i ∈ t₁.vars ↔ i ∈ S₁ := by
      intro i
      constructor
      · intro hi
        have hiS : i ∈ S := (hR i).mp (Finset.mem_union_left _ hi)
        exact (hL₁ i).mp ((hsame i hiS).mpr hi)
      · intro hi
        have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
        exact (hsame i hiS).mp ((hL₁ i).mpr hi)
    have hL₂ : ∀ i, Sum.inl i ∈ t₂.vars ↔ i ∈ S₂ := by
      intro i
      simp only [S₂, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨fun hi => ⟨(hL i).mp (Finset.mem_union_right _ hi), hi⟩, And.right⟩
    have hR₂ : ∀ i, Sum.inr i ∈ t₂.vars ↔ i ∈ S₂ := by
      intro i
      constructor
      · intro hi
        have hiS : i ∈ S := (hR i).mp (Finset.mem_union_right _ hi)
        have h1R : Sum.inr i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hi
        have h1L : Sum.inl i ∉ t₁.vars := fun h => h1R ((hsame i hiS).mp h)
        have h2L : Sum.inl i ∈ t₂.vars := (Finset.mem_union.mp ((hL i).mpr hiS)).resolve_left h1L
        exact (hL₂ i).mp h2L
      · intro hi
        have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
        have h2L : Sum.inl i ∈ t₂.vars := (hL₂ i).mpr hi
        have h1L : Sum.inl i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 h2L
        have h1R : Sum.inr i ∉ t₁.vars := fun h => h1L ((hsame i hiS).mpr h)
        exact (Finset.mem_union.mp ((hR i).mpr hiS)).resolve_left h1R
    have hS₁_ne : S₁.Nonempty := by
      rcases t₁.vars_nonempty with ⟨v, hv⟩
      cases v with
      | inl i => exact ⟨i, (hL₁ i).mp hv⟩
      | inr i => exact ⟨i, (hR₁ i).mp hv⟩
    have hS₂_ne : S₂.Nonempty := by
      rcases t₂.vars_nonempty with ⟨v, hv⟩
      cases v with
      | inl i => exact ⟨i, (hL₂ i).mp hv⟩
      | inr i => exact ⟨i, (hR₂ i).mp hv⟩
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      exact Finset.disjoint_left.mp hro.2.2 ((hL₁ i).mpr h1) ((hL₂ i).mpr h2)
    have hunion : S₁ ∪ S₂ = S := by
      ext i
      rw [Finset.mem_union, ← hL₁, ← hL₂, ← Finset.mem_union, ← hL]
      rfl
    have hd₁ : ∀ i ∈ S₁, t₁.eval (unitVec i) (unitVec i) = true := by
      intro i hi
      have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
      have h2L : Sum.inl i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 ((hL₁ i).mpr hi)
      have h2R : Sum.inr i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 ((hR₁ i).mpr hi)
      have he2 : t₂.eval (unitVec i) (unitVec i) = false := by
        rw [← t₂.eval_zero]
        refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun j hj => ?_)
        · have hji : j ≠ i := fun h => h2L (h ▸ hj)
          simp [unitVec, hji]
        · have hji : j ≠ i := fun h => h2R (h ▸ hj)
          simp [unitVec, hji]
      have hd := hdiag i hiS
      simp [MTree.eval, he2] at hd
      exact hd
    have hd₂ : ∀ i ∈ S₂, t₂.eval (unitVec i) (unitVec i) = true := by
      intro i hi
      have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
      have h1L : Sum.inl i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 ((hL₂ i).mpr hi)
      have h1R : Sum.inr i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 ((hR₂ i).mpr hi)
      have he1 : t₁.eval (unitVec i) (unitVec i) = false := by
        rw [← t₁.eval_zero]
        refine t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun j hj => ?_)
        · have hji : j ≠ i := fun h => h1L (h ▸ hj)
          simp [unitVec, hji]
        · have hji : j ≠ i := fun h => h1R (h ▸ hj)
          simp [unitVec, hji]
      have hd := hdiag i hiS
      simp [MTree.eval, he1] at hd
      exact hd
    have ho₁ : ∀ i ∈ S₁, ∀ j ∈ S₁, i ≠ j → t₁.eval (unitVec i) (unitVec j) = false := by
      intro i hi j hj hne
      have h := hoff i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne
      simp [MTree.eval] at h; exact h.1
    have ho₂ : ∀ i ∈ S₂, ∀ j ∈ S₂, i ≠ j → t₂.eval (unitVec i) (unitVec j) = false := by
      intro i hi j hj hne
      have h := hoff i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne
      simp [MTree.eval] at h; exact h.2
    have hz₁ : ∀ i ∈ S₁, t₁.eval (unitVec i) (fun _ => false) = false ∧
        t₁.eval (fun _ => false) (unitVec i) = false := by
      intro i hi
      have h := hzero i (Finset.mem_filter.mp hi).1
      simp [MTree.eval] at h
      exact ⟨h.1.1, h.2.1⟩
    have hz₂ : ∀ i ∈ S₂, t₂.eval (unitVec i) (fun _ => false) = false ∧
        t₂.eval (fun _ => false) (unitVec i) = false := by
      intro i hi
      have h := hzero i (Finset.mem_filter.mp hi).1
      simp [MTree.eval] at h
      exact ⟨h.1.2, h.2.2⟩
    obtain ⟨M₁, hM₁, hev₁⟩ := ih₁ S₁ hS₁_ne hro.1 hL₁ hR₁ hd₁ ho₁ hz₁
    obtain ⟨M₂, hM₂, hev₂⟩ := ih₂ S₂ hS₂_ne hro.2.1 hL₂ hR₂ hd₂ ho₂ hz₂
    refine ⟨M₁ ∪ M₂, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro e he
        rcases Finset.mem_union.mp he with he1 | he2
        · exact ⟨(hM₁.1 e he1).1, (hM₁.1 e he1).2.trans (hunion ▸ Finset.subset_union_left)⟩
        · exact ⟨(hM₂.1 e he2).1, (hM₂.1 e he2).2.trans (hunion ▸ Finset.subset_union_right)⟩
      · intro e₁ he₁ e₂ he₂ hne
        rcases Finset.mem_union.mp he₁ with h1 | h1 <;> rcases Finset.mem_union.mp he₂ with h2 | h2
        · exact hM₁.2 e₁ h1 e₂ h2 hne
        · exact Disjoint.mono (hM₁.1 e₁ h1).2 (hM₂.1 e₂ h2).2 hdisj
        · exact Disjoint.mono (hM₂.1 e₁ h1).2 (hM₁.1 e₂ h2).2 hdisj.symm
        · exact hM₂.2 e₁ h1 e₂ h2 hne
    · intro x y
      simp only [MTree.eval, hev₁ x y, hev₂ x y, matchFnOn]
      rw [← hunion]
      by_cases h : (∃ i ∈ S₁ ∪ S₂, x i = true ∧ y i = true) ∨
          (∃ e ∈ M₁ ∪ M₂, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))
      · rw [decide_eq_true h]
        rcases h with ⟨i, hi, hxi, hyi⟩ | ⟨e, he, hex⟩
        · rcases Finset.mem_union.mp hi with hi1 | hi2
          · have : decide ((∃ i ∈ S₁, x i = true ∧ y i = true) ∨
                (∃ e ∈ M₁, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) = true :=
              decide_eq_true (Or.inl ⟨i, hi1, hxi, hyi⟩)
            simp [this]
          · have : decide ((∃ i ∈ S₂, x i = true ∧ y i = true) ∨
                (∃ e ∈ M₂, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) = true :=
              decide_eq_true (Or.inl ⟨i, hi2, hxi, hyi⟩)
            simp [this]
        · rcases Finset.mem_union.mp he with he1 | he2
          · have : decide ((∃ i ∈ S₁, x i = true ∧ y i = true) ∨
                (∃ e ∈ M₁, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) = true :=
              decide_eq_true (Or.inr ⟨e, he1, hex⟩)
            simp [this]
          · have : decide ((∃ i ∈ S₂, x i = true ∧ y i = true) ∨
                (∃ e ∈ M₂, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) = true :=
              decide_eq_true (Or.inr ⟨e, he2, hex⟩)
            simp [this]
      · rw [decide_eq_false h]
        have h1 : ¬ ((∃ i ∈ S₁, x i = true ∧ y i = true) ∨
            (∃ e ∈ M₁, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) := by
          rintro (⟨i, hi, hxy⟩ | ⟨e, he, hex⟩)
          · exact h (Or.inl ⟨i, Finset.mem_union_left _ hi, hxy⟩)
          · exact h (Or.inr ⟨e, Finset.mem_union_left _ he, hex⟩)
        have h2 : ¬ ((∃ i ∈ S₂, x i = true ∧ y i = true) ∨
            (∃ e ∈ M₂, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) := by
          rintro (⟨i, hi, hxy⟩ | ⟨e, he, hex⟩)
          · exact h (Or.inl ⟨i, Finset.mem_union_right _ hi, hxy⟩)
          · exact h (Or.inr ⟨e, Finset.mem_union_right _ he, hex⟩)
        simp [decide_eq_false h1, decide_eq_false h2]
  | and t₁ t₂ _ _ =>
    intro S hS hro hL hR hdiag hoff _
    have hboth : ∀ i ∈ S, (Sum.inl i ∈ t₁.vars ∨ Sum.inr i ∈ t₁.vars) ∧
        (Sum.inl i ∈ t₂.vars ∨ Sum.inr i ∈ t₂.vars) := by
      intro i hi
      have hd := hdiag i hi
      simp only [MTree.eval, Bool.and_eq_true] at hd
      constructor
      · by_contra hno
        push_neg at hno
        have h0 : t₁.eval (unitVec i) (unitVec i) = false := by
          rw [← t₁.eval_zero]
          refine t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun j hj => ?_)
          · have hji : j ≠ i := fun h => hno.1 (h ▸ hj); simp [unitVec, hji]
          · have hji : j ≠ i := fun h => hno.2 (h ▸ hj); simp [unitVec, hji]
        exact Bool.false_ne_true (h0.symm.trans hd.1)
      · by_contra hno
        push_neg at hno
        have h0 : t₂.eval (unitVec i) (unitVec i) = false := by
          rw [← t₂.eval_zero]
          refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun j hj => ?_)
          · have hji : j ≠ i := fun h => hno.1 (h ▸ hj); simp [unitVec, hji]
          · have hji : j ≠ i := fun h => hno.2 (h ▸ hj); simp [unitVec, hji]
        exact Bool.false_ne_true (h0.symm.trans hd.2)
    have hexact : ∀ i ∈ S,
        (Sum.inl i ∈ t₁.vars ∧ Sum.inr i ∉ t₁.vars ∧ Sum.inl i ∉ t₂.vars ∧ Sum.inr i ∈ t₂.vars) ∨
        (Sum.inl i ∉ t₁.vars ∧ Sum.inr i ∈ t₁.vars ∧ Sum.inl i ∈ t₂.vars ∧ Sum.inr i ∉ t₂.vars) := by
      intro i hi
      rcases hboth i hi with ⟨h1L | h1R, h2L | h2R⟩
      · exact absurd h2L (Finset.disjoint_left.mp hro.2.2 h1L)
      · left
        exact ⟨h1L, Finset.disjoint_right.mp hro.2.2 h2R, Finset.disjoint_left.mp hro.2.2 h1L, h2R⟩
      · right
        exact ⟨Finset.disjoint_right.mp hro.2.2 h2L, h1R, h2L, Finset.disjoint_left.mp hro.2.2 h1R⟩
      · exact absurd h2R (Finset.disjoint_left.mp hro.2.2 h1R)
    have ht₁_or : ∀ x y, t₁.eval x y =
        decide ((∃ i, Sum.inl i ∈ t₁.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₁.vars ∧ y i = true)) := by
      refine t₁.all_unit_true_is_or hro.1 ?_ ?_
      · intro i hi
        have hiS : i ∈ S := (hL i).mp (Finset.mem_union_left _ hi)
        have h1R : Sum.inr i ∉ t₁.vars := by
          rcases hexact i hiS with ⟨_, h1R, _, _⟩ | ⟨h1L, _, _, _⟩
          · exact h1R
          · exact absurd hi h1L
        have hd := (Bool.and_eq_true _ _).mp (hdiag i hiS)
        rw [← hd.1]
        refine t₁.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
        have hji : j ≠ i := fun h => h1R (h ▸ hj)
        simp [unitVec, hji]
      · intro i hi
        have hiS : i ∈ S := (hR i).mp (Finset.mem_union_left _ hi)
        have h1L : Sum.inl i ∉ t₁.vars := by
          rcases hexact i hiS with ⟨_, h1R, _, _⟩ | ⟨h1L, _, _, _⟩
          · exact absurd hi h1R
          · exact h1L
        have hd := (Bool.and_eq_true _ _).mp (hdiag i hiS)
        rw [← hd.1]
        refine t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
        have hji : j ≠ i := fun h => h1L (h ▸ hj)
        simp [unitVec, hji]
    have ht₂_or : ∀ x y, t₂.eval x y =
        decide ((∃ i, Sum.inl i ∈ t₂.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₂.vars ∧ y i = true)) := by
      refine t₂.all_unit_true_is_or hro.2.1 ?_ ?_
      · intro i hi
        have hiS : i ∈ S := (hL i).mp (Finset.mem_union_right _ hi)
        have h2R : Sum.inr i ∉ t₂.vars := by
          rcases hexact i hiS with ⟨_, _, h2L, _⟩ | ⟨_, _, _, h2R⟩
          · exact absurd hi h2L
          · exact h2R
        have hd := (Bool.and_eq_true _ _).mp (hdiag i hiS)
        rw [← hd.2]
        refine t₂.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
        have hji : j ≠ i := fun h => h2R (h ▸ hj)
        simp [unitVec, hji]
      · intro i hi
        have hiS : i ∈ S := (hR i).mp (Finset.mem_union_right _ hi)
        have h2L : Sum.inl i ∉ t₂.vars := by
          rcases hexact i hiS with ⟨_, _, h2L, _⟩ | ⟨_, _, _, h2R⟩
          · exact h2L
          · exact absurd hi h2R
        have hd := (Bool.and_eq_true _ _).mp (hdiag i hiS)
        rw [← hd.2]
        refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
        have hji : j ≠ i := fun h => h2L (h ▸ hj)
        simp [unitVec, hji]
    have huniqL : ∀ i ∈ S, ∀ j ∈ S, Sum.inl i ∈ t₁.vars → Sum.inl j ∈ t₁.vars → i = j := by
      intro i hi j hj hi1 hj1
      by_contra hne
      have hj2R : Sum.inr j ∈ t₂.vars := by
        rcases hexact j hj with ⟨_, _, _, h2R⟩ | ⟨h1L, _, _, _⟩
        · exact h2R
        · exact absurd hj1 h1L
      have h := hoff i hi j hj hne
      simp only [MTree.eval, ht₁_or, ht₂_or] at h
      have h1t : decide ((∃ k, Sum.inl k ∈ t₁.vars ∧ unitVec i k = true) ∨
          (∃ k, Sum.inr k ∈ t₁.vars ∧ unitVec j k = true)) = true :=
        decide_eq_true (Or.inl ⟨i, hi1, by simp [unitVec]⟩)
      have h2t : decide ((∃ k, Sum.inl k ∈ t₂.vars ∧ unitVec i k = true) ∨
          (∃ k, Sum.inr k ∈ t₂.vars ∧ unitVec j k = true)) = true :=
        decide_eq_true (Or.inr ⟨j, hj2R, by simp [unitVec]⟩)
      rw [h1t, h2t] at h
      exact Bool.false_ne_true.symm h
    have huniqR : ∀ i ∈ S, ∀ j ∈ S, Sum.inr i ∈ t₁.vars → Sum.inr j ∈ t₁.vars → i = j := by
      intro i hi j hj hi1 hj1
      by_contra hne
      have hj2L : Sum.inl j ∈ t₂.vars := by
        rcases hexact j hj with ⟨_, h1R, _, _⟩ | ⟨_, _, h2L, _⟩
        · exact absurd hj1 h1R
        · exact h2L
      have h := hoff j hj i hi (Ne.symm hne)
      simp only [MTree.eval, ht₁_or, ht₂_or] at h
      have h1t : decide ((∃ k, Sum.inl k ∈ t₁.vars ∧ unitVec j k = true) ∨
          (∃ k, Sum.inr k ∈ t₁.vars ∧ unitVec i k = true)) = true :=
        decide_eq_true (Or.inr ⟨i, hi1, by simp [unitVec]⟩)
      have h2t : decide ((∃ k, Sum.inl k ∈ t₂.vars ∧ unitVec j k = true) ∨
          (∃ k, Sum.inr k ∈ t₂.vars ∧ unitVec i k = true)) = true :=
        decide_eq_true (Or.inl ⟨j, hj2L, by simp [unitVec]⟩)
      rw [h1t, h2t] at h
      exact Bool.false_ne_true.symm h
    by_cases hcard : S.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
      refine ⟨∅, ⟨by simp, by simp⟩, ?_⟩
      intro x y
      simp only [MTree.eval, ht₁_or, ht₂_or, matchFnOn, Finset.mem_singleton, Finset.notMem_empty,
        false_and, exists_false, or_false]
      have ha_vars : ∀ k, Sum.inl k ∈ t₁.vars ∨ Sum.inr k ∈ t₁.vars → k = a := by
        intro k hk
        rcases hk with h1 | h1
        · exact Finset.mem_singleton.mp ((hL k).mp (Finset.mem_union_left _ h1))
        · exact Finset.mem_singleton.mp ((hR k).mp (Finset.mem_union_left _ h1))
      have ha_vars2 : ∀ k, Sum.inl k ∈ t₂.vars ∨ Sum.inr k ∈ t₂.vars → k = a := by
        intro k hk
        rcases hk with h1 | h1
        · exact Finset.mem_singleton.mp ((hL k).mp (Finset.mem_union_right _ h1))
        · exact Finset.mem_singleton.mp ((hR k).mp (Finset.mem_union_right _ h1))
      rcases hexact a (Finset.mem_singleton_self a) with ⟨h1L, h1R, h2L, h2R⟩ | ⟨h1L, h1R, h2L, h2R⟩
      · have he1 : ((∃ k, Sum.inl k ∈ t₁.vars ∧ x k = true) ∨ (∃ k, Sum.inr k ∈ t₁.vars ∧ y k = true)) ↔
            x a = true := by
          constructor
          · rintro (⟨k, hk, hxk⟩ | ⟨k, hk, _⟩)
            · rwa [← ha_vars k (Or.inl hk)]
            · exact absurd (ha_vars k (Or.inr hk) ▸ hk) h1R
          · intro hx; exact Or.inl ⟨a, h1L, hx⟩
        have he2 : ((∃ k, Sum.inl k ∈ t₂.vars ∧ x k = true) ∨ (∃ k, Sum.inr k ∈ t₂.vars ∧ y k = true)) ↔
            y a = true := by
          constructor
          · rintro (⟨k, hk, _⟩ | ⟨k, hk, hyk⟩)
            · exact absurd (ha_vars2 k (Or.inl hk) ▸ hk) h2L
            · rwa [← ha_vars2 k (Or.inr hk)]
          · intro hy; exact Or.inr ⟨a, h2R, hy⟩
        simp only [he1, he2, exists_eq_left]
        cases x a <;> cases y a <;> decide
      · have he1 : ((∃ k, Sum.inl k ∈ t₁.vars ∧ x k = true) ∨ (∃ k, Sum.inr k ∈ t₁.vars ∧ y k = true)) ↔
            y a = true := by
          constructor
          · rintro (⟨k, hk, _⟩ | ⟨k, hk, hyk⟩)
            · exact absurd (ha_vars k (Or.inl hk) ▸ hk) h1L
            · rwa [← ha_vars k (Or.inr hk)]
          · intro hy; exact Or.inr ⟨a, h1R, hy⟩
        have he2 : ((∃ k, Sum.inl k ∈ t₂.vars ∧ x k = true) ∨ (∃ k, Sum.inr k ∈ t₂.vars ∧ y k = true)) ↔
            x a = true := by
          constructor
          · rintro (⟨k, hk, hxk⟩ | ⟨k, hk, _⟩)
            · rwa [← ha_vars2 k (Or.inl hk)]
            · exact absurd (ha_vars2 k (Or.inr hk) ▸ hk) h2R
          · intro hx; exact Or.inl ⟨a, h2L, hx⟩
        simp only [he1, he2, exists_eq_left]
        cases x a <;> cases y a <;> decide
    · have hge2 : 2 ≤ S.card := by
        have hpos : 0 < S.card := hS.card_pos
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
      have hpair : ∃ u v, u ∈ S ∧ v ∈ S ∧ u ≠ v ∧
          Sum.inl u ∈ t₁.vars ∧ Sum.inr v ∈ t₁.vars ∧
          Sum.inr u ∈ t₂.vars ∧ Sum.inl v ∈ t₂.vars := by
        rcases hexact a ha with ⟨ha1L, _, _, ha2R⟩ | ⟨_, ha1R, ha2L, _⟩
        · rcases hexact b hb with ⟨hb1L, _, _, _⟩ | ⟨_, hb1R, hb2L, _⟩
          · exact absurd (huniqL a ha b hb ha1L hb1L) hab
          · exact ⟨a, b, ha, hb, hab, ha1L, hb1R, ha2R, hb2L⟩
        · rcases hexact b hb with ⟨hb1L, _, _, hb2R⟩ | ⟨_, hb1R, _, _⟩
          · exact ⟨b, a, hb, ha, hab.symm, hb1L, ha1R, hb2R, ha2L⟩
          · exact absurd (huniqR a ha b hb ha1R hb1R) hab
      rcases hpair with ⟨u, v, huS, hvS, huv, hu1L, hv1R, hu2R, hv2L⟩
      have hSeq : S = {u, v} := by
        ext k
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hk
          rcases hexact k hk with ⟨hk1L, _, _, _⟩ | ⟨_, hk1R, _, _⟩
          · left; exact huniqL k hk u huS hk1L hu1L
          · right; exact huniqR k hk v hvS hk1R hv1R
        · rintro (rfl | rfl)
          · exact huS
          · exact hvS
      refine ⟨{{u, v}}, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro e he
          rw [Finset.mem_singleton.mp he]
          exact ⟨Finset.card_pair huv, by rw [hSeq]⟩
        · intro e₁ he₁ e₂ he₂ hne
          exact absurd ((Finset.mem_singleton.mp he₁).trans (Finset.mem_singleton.mp he₂).symm) hne
      · intro x y
        simp only [MTree.eval, ht₁_or, ht₂_or, matchFnOn, hSeq, Finset.mem_singleton]
        have h1L_iff : ∀ k, Sum.inl k ∈ t₁.vars ↔ k = u := by
          intro k
          constructor
          · intro hk
            have hkS : k ∈ S := (hL k).mp (Finset.mem_union_left _ hk)
            exact huniqL k hkS u huS hk hu1L
          · rintro rfl; exact hu1L
        have h1R_iff : ∀ k, Sum.inr k ∈ t₁.vars ↔ k = v := by
          intro k
          constructor
          · intro hk
            have hkS : k ∈ S := (hR k).mp (Finset.mem_union_left _ hk)
            exact huniqR k hkS v hvS hk hv1R
          · rintro rfl; exact hv1R
        have h2L_iff : ∀ k, Sum.inl k ∈ t₂.vars ↔ k = v := by
          intro k
          constructor
          · intro hk
            have hkS : k ∈ S := (hL k).mp (Finset.mem_union_right _ hk)
            have hk1L : Sum.inl k ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hk
            rcases hexact k hkS with ⟨h, _, _, _⟩ | ⟨_, hk1R, _, _⟩
            · exact absurd h hk1L
            · exact huniqR k hkS v hvS hk1R hv1R
          · rintro rfl; exact hv2L
        have h2R_iff : ∀ k, Sum.inr k ∈ t₂.vars ↔ k = u := by
          intro k
          constructor
          · intro hk
            have hkS : k ∈ S := (hR k).mp (Finset.mem_union_right _ hk)
            have hk1R : Sum.inr k ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hk
            rcases hexact k hkS with ⟨hk1L, _, _, _⟩ | ⟨_, h, _, _⟩
            · exact huniqL k hkS u huS hk1L hu1L
            · exact absurd h hk1R
          · rintro rfl; exact hu2R
        simp only [h1L_iff, h1R_iff, h2L_iff, h2R_iff, exists_eq_left, exists_eq_or_imp,
          Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
        cases x u <;> cases x v <;> cases y u <;> cases y v <;> decide

private lemma optimal_circuit_is_matchFn {n : ℕ} (hn : 2 ≤ n) (C : Circuit)
    (hM : Monotone2 C) (hsz : C.size + 1 ≤ 2 * n)
    (hrep : Represents (fun i j : Fin n => decide (i = j)) C) :
    ∃ M : Finset (Finset (Fin n)), IsMatching Finset.univ M ∧
      ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = matchFn M x y := by
  have heval_zeroL : ∀ i : Fin n, C.eval (List.ofFn (fun _ : Fin n => false) ++ List.ofFn (unitVec i)) = false := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_cases h0 : i = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by intro h; rw [h0] at h; exact (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val h)⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
    have hle : C.eval (List.ofFn (fun _ : Fin n => false) ++ List.ofFn (unitVec i)) ≤
        C.eval (oneEach j i) := by
      unfold Circuit.eval
      refine monotone2_wires_mono C hM (by simp [oneEach]) (fun k => ?_) C.output
      by_cases hk : k < n
      · simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, hk]
      · by_cases hk2 : k < n + n
        · simp only [oneEach, unitVec, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp [show k - n < n by omega]
          exact le_refl _
        · simp only [oneEach, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    have hf : C.eval (oneEach j i) = false := by rw [hrep j i]; simp [hj]
    rw [hf] at hle
    exact Bool.eq_false_of_le_false hle
  have heval_zeroR : ∀ i : Fin n, C.eval (List.ofFn (unitVec i) ++ List.ofFn (fun _ : Fin n => false)) = false := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_cases h0 : i = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by intro h; rw [h0] at h; exact (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val h)⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
    have hle : C.eval (List.ofFn (unitVec i) ++ List.ofFn (fun _ : Fin n => false)) ≤
        C.eval (oneEach i j) := by
      unfold Circuit.eval
      refine monotone2_wires_mono C hM (by simp [oneEach]) (fun k => ?_) C.output
      by_cases hk : k < n
      · simp [oneEach, unitVec, List.getD_eq_getElem?_getD, List.getElem?_append_left, hk]
      · by_cases hk2 : k < n + n
        · simp only [oneEach, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp [show k - n < n by omega]
        · simp only [oneEach, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    have hf : C.eval (oneEach i j) = false := by rw [hrep i j]; simp [hj.symm]
    rw [hf] at hle
    exact Bool.eq_false_of_le_false hle
  have hall_inp : ∀ k < 2 * n, k ∈ reach C (2 * n) C.output := by
    intro k hk
    by_contra hnot
    by_cases hkn : k < n
    · let i : Fin n := ⟨k, hkn⟩
      have heq := reach_eq_on_wires C (2 * n)
        (inp₁ := List.ofFn (unitVec i) ++ List.ofFn (unitVec i))
        (inp₂ := List.ofFn (fun _ : Fin n => false) ++ List.ofFn (unitVec i))
        (by simp; omega) (by simp; omega) C.output (fun m hm hmr => ?_)
      · have h1 : C.eval (List.ofFn (unitVec i) ++ List.ofFn (unitVec i)) = true := by
          change C.eval (oneEach i i) = true; rw [hrep i i]; simp
        have h2 := heval_zeroL i
        unfold Circuit.eval at h1 h2
        rw [heq] at h1
        exact Bool.false_ne_true.symm (h1.symm.trans h2)
      · have hmk : m ≠ k := fun h => hnot (h ▸ hmr)
        by_cases hmn : m < n
        · simp [unitVec, List.getD_eq_getElem?_getD, List.getElem?_append_left, hmn,
            Fin.ext_iff, i, hmk]
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp
    · let i : Fin n := ⟨k - n, by omega⟩
      have heq := reach_eq_on_wires C (2 * n)
        (inp₁ := List.ofFn (unitVec i) ++ List.ofFn (unitVec i))
        (inp₂ := List.ofFn (unitVec i) ++ List.ofFn (fun _ : Fin n => false))
        (by simp; omega) (by simp; omega) C.output (fun m hm hmr => ?_)
      · have h1 : C.eval (List.ofFn (unitVec i) ++ List.ofFn (unitVec i)) = true := by
          change C.eval (oneEach i i) = true; rw [hrep i i]; simp
        have h2 := heval_zeroR i
        unfold Circuit.eval at h1 h2
        rw [heq] at h1
        exact Bool.false_ne_true.symm (h1.symm.trans h2)
      · have hmk : m ≠ k := fun h => hnot (h ▸ hmr)
        by_cases hmn : m < n
        · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hmn]
        · have hsub : m - n ≠ k - n := by omega
          have hmn2 : m - n < n := by omega
          have hne_fin : (⟨m - n, hmn2⟩ : Fin n) ≠ i := fun h => hsub (congrArg Fin.val h)
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp only [List.length_ofFn, List.getElem?_ofFn, hmn2, ↓reduceDIte, Option.getD_some]
          simp [unitVec, hne_fin, hne_fin.symm]
  have hout_lt : C.output < 2 * n + C.gates.length := by
    by_contra hge
    push_neg at hge
    have h0 := hrep ⟨0, by omega⟩ ⟨0, by omega⟩
    unfold Circuit.eval at h0
    rw [wires_getD_oob C (oneEach ⟨0, by omega⟩ ⟨0, by omega⟩) C.output (by simp [oneEach]; omega)] at h0
    simp at h0
  let R := reach C (2 * n) C.output
  let G := R.filter (fun w => decide (2 * n ≤ w))
  have hG_sub : G ⊆ (Finset.range C.gates.length).image (fun j => 2 * n + j) := by
    intro w hw
    simp only [G, Finset.mem_filter, decide_eq_true_eq] at hw
    have hw_le := mem_reach_le C (2 * n) C.output w hw.1
    rw [Finset.mem_image]
    exact ⟨w - 2 * n, Finset.mem_range.mpr (by omega), by omega⟩
  have hG_card_le : G.card ≤ 2 * n - 1 := by
    have h1 := Finset.card_le_card hG_sub
    have h2 := Finset.card_image_le (s := Finset.range C.gates.length) (f := fun j => 2 * n + j)
    rw [Finset.card_range] at h2
    have h3 : C.gates.length ≤ 2 * n - 1 := by unfold Circuit.size at hsz; omega
    omega
  have hR_card : R.card = 2 * n + G.card := by
    have hpart : R = Finset.range (2 * n) ∪ G := by
      ext w
      simp only [Finset.mem_union, Finset.mem_range, G, Finset.mem_filter, decide_eq_true_eq]
      constructor
      · intro hw
        by_cases hlt : w < 2 * n
        · left; exact hlt
        · right; exact ⟨hw, by omega⟩
      · rintro (hlt | ⟨hw, _⟩)
        · exact hall_inp w hlt
        · exact hw
    have hdisj : Disjoint (Finset.range (2 * n)) G := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [Finset.mem_range] at hw1
      simp only [G, Finset.mem_filter, decide_eq_true_eq] at hw2
      omega
    rw [hpart, Finset.card_union_of_disjoint hdisj, Finset.card_range]
  have herase_sub : R.erase C.output ⊆ G.biUnion (gateParents C (2 * n)) := by
    have hrec : ∀ w ∈ R, ∀ x ∈ reach C (2 * n) w, x ≠ w →
        x ∈ (G.filter (· ≤ w)).biUnion (gateParents C (2 * n)) := by
      intro w hw
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro x hx hne
        rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hx
        rcases hx with rfl | ⟨u, hu, hxu⟩
        · exact absurd rfl hne
        · have hwG : w ∈ G := by
            simp only [G, Finset.mem_filter, decide_eq_true_eq]
            refine ⟨hw, ?_⟩
            by_contra hlt
            unfold gateParents at hu
            have hcond : ¬ (2 * n ≤ w ∧ w - 2 * n < C.gates.length) := by omega
            rw [dif_neg hcond] at hu
            simp at hu
          by_cases hxu_eq : x = u
          · rw [hxu_eq]
            exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hwG, le_refl w⟩, hu⟩
          · have huR : u ∈ R := by
              have hsub : reach C (2 * n) u ⊆ reach C (2 * n) w :=
                reach_subset_of_mem_gateParents C (2 * n) w u hu
              have hwsub : ∀ y ∈ reach C (2 * n) w, y ∈ R := by
                intro y hy
                clear ih
                have htrans : ∀ a b c, b ∈ reach C (2 * n) a → c ∈ reach C (2 * n) b → c ∈ reach C (2 * n) a := by
                  intro a
                  induction a using Nat.strong_induction_on with
                  | ind a iha =>
                    intro b c hba hcb
                    rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hba
                    rcases hba with rfl | ⟨v, hv, hbv⟩
                    · exact hcb
                    · exact reach_subset_of_mem_gateParents C (2 * n) a v hv
                        (iha v (mem_gateParents_lt C (2 * n) a v hv) b c hbv hcb)
                exact htrans C.output w y hw hy
              exact hwsub u (reach_subset_of_mem_gateParents C (2 * n) w u hu (self_mem_reach _ _ _))
            have hih := ih u (mem_gateParents_lt C (2 * n) w u hu) huR x hxu hxu_eq
            rcases Finset.mem_biUnion.mp hih with ⟨v, hv, hxv⟩
            rw [Finset.mem_filter] at hv
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨hv.1, le_trans hv.2 (Nat.le_of_lt (mem_gateParents_lt _ _ _ _ hu))⟩, hxv⟩
    intro x hx
    rw [Finset.mem_erase] at hx
    have h := hrec C.output (self_mem_reach C (2 * n) C.output) x hx.2 hx.1
    rcases Finset.mem_biUnion.mp h with ⟨v, hv, hxv⟩
    exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_filter.mp hv).1, hxv⟩
  have hsum_le : ∑ w ∈ G, (gateParents C (2 * n) w).card ≤ 2 * G.card := by
    calc
      ∑ w ∈ G, (gateParents C (2 * n) w).card ≤ ∑ _w ∈ G, 2 :=
        Finset.sum_le_sum (fun w _ => gateParents_card_le C hM (2 * n) w)
      _ = 2 * G.card := by simp [mul_comm]
  have herase_card : (R.erase C.output).card = 2 * n + G.card - 1 := by
    rw [Finset.card_erase_of_mem (self_mem_reach C (2 * n) C.output), hR_card]
  have hbi_ge : 2 * n + G.card - 1 ≤ (G.biUnion (gateParents C (2 * n))).card := by
    rw [← herase_card]; exact Finset.card_le_card herase_sub
  have hbi_le : (G.biUnion (gateParents C (2 * n))).card ≤ ∑ w ∈ G, (gateParents C (2 * n) w).card :=
    Finset.card_biUnion_le
  have hG_card : G.card = 2 * n - 1 := by omega
  have hbi_eq : (G.biUnion (gateParents C (2 * n))).card = ∑ w ∈ G, (gateParents C (2 * n) w).card := by omega
  have hsum_eq : ∑ w ∈ G, (gateParents C (2 * n) w).card = 2 * G.card := by omega
  have hdeg2 : ∀ w ∈ G, (gateParents C (2 * n) w).card = 2 := by
    intro w hw
    by_contra hne
    have hlt : (gateParents C (2 * n) w).card < 2 :=
      Nat.lt_of_le_of_ne (gateParents_card_le C hM (2 * n) w) hne
    have h1 := Finset.add_sum_erase G (fun x => (gateParents C (2 * n) x).card) hw
    have h2 : ∑ x ∈ G.erase w, (gateParents C (2 * n) x).card ≤ 2 * (G.erase w).card := by
      calc
        ∑ x ∈ G.erase w, (gateParents C (2 * n) x).card ≤ ∑ _x ∈ G.erase w, 2 :=
          Finset.sum_le_sum (fun x _ => gateParents_card_le C hM (2 * n) x)
        _ = 2 * (G.erase w).card := by simp [mul_comm]
    have h3 : (G.erase w).card + 1 = G.card := Finset.card_erase_add_one hw
    omega
  have hpar_disj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint (gateParents C (2 * n) w₁) (gateParents C (2 * n) w₂) :=
    biUnion_card_eq_sum_iff_disjoint G (gateParents C (2 * n)) hbi_eq
  have hreach_trans : ∀ a b c, b ∈ reach C (2 * n) a → c ∈ reach C (2 * n) b → c ∈ reach C (2 * n) a := by
    intro a
    induction a using Nat.strong_induction_on with
    | ind a iha =>
      intro b c hba hcb
      rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hba
      rcases hba with rfl | ⟨v, hv, hbv⟩
      · exact hcb
      · exact reach_subset_of_mem_gateParents C (2 * n) a v hv
          (iha v (mem_gateParents_lt C (2 * n) a v hv) b c hbv hcb)
  have hstep_parent : ∀ a b, b ∈ reach C (2 * n) a → b ≠ a →
      ∃ p ∈ reach C (2 * n) a, b ∈ gateParents C (2 * n) p := by
    intro a
    induction a using Nat.strong_induction_on with
    | ind a iha =>
      intro b hba hne
      rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hba
      rcases hba with rfl | ⟨v, hv, hbv⟩
      · exact absurd rfl hne
      · by_cases hbv_eq : b = v
        · exact ⟨a, self_mem_reach _ _ _, hbv_eq ▸ hv⟩
        · obtain ⟨p, hp, hbp⟩ := iha v (mem_gateParents_lt C (2 * n) a v hv) b hbv hbv_eq
          exact ⟨p, reach_subset_of_mem_gateParents C (2 * n) a v hv hp, hbp⟩
  have hchildren_disj : ∀ w ∈ G, ∀ u ∈ gateParents C (2 * n) w, ∀ v ∈ gateParents C (2 * n) w,
      u ≠ v → Disjoint (reach C (2 * n) u) (reach C (2 * n) v) := by
    intro w hw u hu v hv huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    let common := reach C (2 * n) u ∩ reach C (2 * n) v
    have hne_c : common.Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hxu, hxv⟩⟩
    let y := common.max' hne_c
    have hy_mem : y ∈ common := Finset.max'_mem common hne_c
    have hyu : y ∈ reach C (2 * n) u := (Finset.mem_inter.mp hy_mem).1
    have hyv : y ∈ reach C (2 * n) v := (Finset.mem_inter.mp hy_mem).2
    have hpu : ∃ p ∈ G, p ≤ w ∧ y ∈ gateParents C (2 * n) p ∧ (p = w ∨ p ∈ reach C (2 * n) u) := by
      by_cases hyu_eq : y = u
      · exact ⟨w, hw, le_refl w, hyu_eq ▸ hu, Or.inl rfl⟩
      · obtain ⟨p, hpu, hyp⟩ := hstep_parent u y hyu hyu_eq
        have hpR : p ∈ R := hreach_trans C.output w p (Finset.mem_filter.mp hw).1
          (reach_subset_of_mem_gateParents C (2 * n) w u hu hpu)
        have hpG : p ∈ G := by
          simp only [G, Finset.mem_filter, decide_eq_true_eq]
          refine ⟨hpR, ?_⟩
          by_contra hlt
          unfold gateParents at hyp
          have hcond : ¬ (2 * n ≤ p ∧ p - 2 * n < C.gates.length) := by omega
          rw [dif_neg hcond] at hyp; simp at hyp
        exact ⟨p, hpG, le_trans (mem_reach_le _ _ _ _ hpu) (Nat.le_of_lt (mem_gateParents_lt _ _ _ _ hu)),
          hyp, Or.inr hpu⟩
    have hpv : ∃ q ∈ G, q ≤ w ∧ y ∈ gateParents C (2 * n) q ∧ (q = w ∨ q ∈ reach C (2 * n) v) := by
      by_cases hyv_eq : y = v
      · exact ⟨w, hw, le_refl w, hyv_eq ▸ hv, Or.inl rfl⟩
      · obtain ⟨q, hqv, hyq⟩ := hstep_parent v y hyv hyv_eq
        have hqR : q ∈ R := hreach_trans C.output w q (Finset.mem_filter.mp hw).1
          (reach_subset_of_mem_gateParents C (2 * n) w v hv hqv)
        have hqG : q ∈ G := by
          simp only [G, Finset.mem_filter, decide_eq_true_eq]
          refine ⟨hqR, ?_⟩
          by_contra hlt
          unfold gateParents at hyq
          have hcond : ¬ (2 * n ≤ q ∧ q - 2 * n < C.gates.length) := by omega
          rw [dif_neg hcond] at hyq; simp at hyq
        exact ⟨q, hqG, le_trans (mem_reach_le _ _ _ _ hqv) (Nat.le_of_lt (mem_gateParents_lt _ _ _ _ hv)),
          hyq, Or.inr hqv⟩
    rcases hpu with ⟨p, hpG, _, hyp, hpw | hpu'⟩ <;> rcases hpv with ⟨q, hqG, _, hyq, hqw | hqv'⟩
    · have hyu_eq : y = u := by
        by_contra hne
        obtain ⟨p', hp', hyp'⟩ := hstep_parent u y hyu hne
        have hp'lt : p' < w := lt_of_le_of_lt (mem_reach_le _ _ _ _ hp') (mem_gateParents_lt _ _ _ _ hu)
        have hp'R : p' ∈ R := hreach_trans C.output w p' (Finset.mem_filter.mp hw).1
          (reach_subset_of_mem_gateParents C (2 * n) w u hu hp')
        have hp'G : p' ∈ G := by
          simp only [G, Finset.mem_filter, decide_eq_true_eq]
          refine ⟨hp'R, ?_⟩
          by_contra hlt
          unfold gateParents at hyp'
          have hcond : ¬ (2 * n ≤ p' ∧ p' - 2 * n < C.gates.length) := by omega
          rw [dif_neg hcond] at hyp'; simp at hyp'
        exact Finset.disjoint_left.mp (hpar_disj w hw p' hp'G (Nat.ne_of_gt hp'lt)) (hpw ▸ hyp) hyp'
      have hyv_eq : y = v := by
        by_contra hne
        obtain ⟨q', hq', hyq'⟩ := hstep_parent v y hyv hne
        have hq'lt : q' < w := lt_of_le_of_lt (mem_reach_le _ _ _ _ hq') (mem_gateParents_lt _ _ _ _ hv)
        have hq'R : q' ∈ R := hreach_trans C.output w q' (Finset.mem_filter.mp hw).1
          (reach_subset_of_mem_gateParents C (2 * n) w v hv hq')
        have hq'G : q' ∈ G := by
          simp only [G, Finset.mem_filter, decide_eq_true_eq]
          refine ⟨hq'R, ?_⟩
          by_contra hlt
          unfold gateParents at hyq'
          have hcond : ¬ (2 * n ≤ q' ∧ q' - 2 * n < C.gates.length) := by omega
          rw [dif_neg hcond] at hyq'; simp at hyq'
        exact Finset.disjoint_left.mp (hpar_disj w hw q' hq'G (Nat.ne_of_gt hq'lt)) (hqw ▸ hyq) hyq'
      exact huv (hyu_eq.symm.trans hyv_eq)
    · have hqlt : q < w := lt_of_le_of_lt (mem_reach_le _ _ _ _ hqv') (mem_gateParents_lt _ _ _ _ hv)
      exact Finset.disjoint_left.mp (hpar_disj w hw q hqG (Nat.ne_of_gt hqlt)) (hpw ▸ hyp) hyq
    · have hplt : p < w := lt_of_le_of_lt (mem_reach_le _ _ _ _ hpu') (mem_gateParents_lt _ _ _ _ hu)
      exact Finset.disjoint_left.mp (hpar_disj w hw p hpG (Nat.ne_of_gt hplt)) (hqw ▸ hyq) hyp
    · have hpq : p = q := by
        by_contra hne
        exact Finset.disjoint_left.mp (hpar_disj p hpG q hqG hne) hyp hyq
      have hp_mem : p ∈ common := Finset.mem_inter.mpr ⟨hpu', hpq ▸ hqv'⟩
      have hle_y : p ≤ y := Finset.le_max' common p hp_mem
      have hlt_p : y < p := mem_gateParents_lt C (2 * n) p y hyp
      omega
  have hbuild : ∀ w ∈ R, ∃ t : MTree n, t.ReadOnce ∧
      (∀ i : Fin n, Sum.inl i ∈ t.vars ↔ i.val ∈ reach C (2 * n) w) ∧
      (∀ i : Fin n, Sum.inr i ∈ t.vars ↔ n + i.val ∈ reach C (2 * n) w) ∧
      (∀ x y, t.eval x y = (C.wires (List.ofFn x ++ List.ofFn y)).getD w false) := by
    intro w hw
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hlt : w < 2 * n
      · by_cases hwn : w < n
        · refine ⟨MTree.leafL ⟨w, hwn⟩, trivial, ?_, ?_, ?_⟩
          · intro i
            simp only [MTree.vars, Finset.mem_singleton, Sum.inl.injEq, Fin.ext_iff]
            have hrg : reach C (2 * n) w = {w} := by
              rw [reach_eq]
              have hp : gateParents C (2 * n) w = ∅ := by
                unfold gateParents
                rw [dif_neg (by omega)]
              simp [hp]
            rw [hrg, Finset.mem_singleton]
          · intro i
            simp only [MTree.vars, Finset.mem_singleton, reduceCtorEq, false_iff]
            intro hmem
            have hle := mem_reach_le C (2 * n) w (n + i.val) hmem
            omega
          · intro x y
            rw [wires_getD_prefix C.gates (List.ofFn x ++ List.ofFn y) C.output w (by simp; omega)]
            simp [MTree.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left, hwn]
        · refine ⟨MTree.leafR ⟨w - n, by omega⟩, trivial, ?_, ?_, ?_⟩
          · intro i
            simp only [MTree.vars, Finset.mem_singleton, reduceCtorEq, false_iff]
            have hrg : reach C (2 * n) w = {w} := by
              rw [reach_eq]
              have hp : gateParents C (2 * n) w = ∅ := by
                unfold gateParents
                rw [dif_neg (by omega)]
              simp [hp]
            rw [hrg, Finset.mem_singleton]; omega
          · intro i
            simp only [MTree.vars, Finset.mem_singleton, Sum.inr.injEq, Fin.ext_iff]
            have hrg : reach C (2 * n) w = {w} := by
              rw [reach_eq]
              have hp : gateParents C (2 * n) w = ∅ := by
                unfold gateParents
                rw [dif_neg (by omega)]
              simp [hp]
            rw [hrg, Finset.mem_singleton]; omega
          · intro x y
            rw [wires_getD_prefix C.gates (List.ofFn x ++ List.ofFn y) C.output w (by simp; omega)]
            simp only [MTree.eval, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by simp; omega)]
            simp [show w - n < n by omega]
      · have hwG : w ∈ G := Finset.mem_filter.mpr ⟨hw, decide_eq_true (by omega)⟩
        have hw_le : w ≤ C.output := mem_reach_le C (2 * n) C.output w hw
        have hj : w - 2 * n < C.gates.length := by omega
        have hpc : (gateParents C (2 * n) w).card = 2 := hdeg2 w hwG
        obtain ⟨u, v, huv, hp_eq⟩ := Finset.card_eq_two.mp hpc
        have hu_mem : u ∈ gateParents C (2 * n) w := hp_eq ▸ Finset.mem_insert_self u {v}
        have hv_mem : v ∈ gateParents C (2 * n) w := hp_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
        have huR : u ∈ R := hreach_trans C.output w u hw (reach_subset_of_mem_gateParents _ _ _ _ hu_mem (self_mem_reach _ _ _))
        have hvR : v ∈ R := hreach_trans C.output w v hw (reach_subset_of_mem_gateParents _ _ _ _ hv_mem (self_mem_reach _ _ _))
        obtain ⟨t₁, hro₁, hL₁, hR₁, hev₁⟩ := ih u (mem_gateParents_lt C (2 * n) w u hu_mem) huR
        obtain ⟨t₂, hro₂, hL₂, hR₂, hev₂⟩ := ih v (mem_gateParents_lt C (2 * n) w v hv_mem) hvR
        have hdisj_r : Disjoint (reach C (2 * n) u) (reach C (2 * n) v) :=
          hchildren_disj w hwG u hu_mem v hv_mem huv
        have hdisj_t : Disjoint t₁.vars t₂.vars := by
          rw [Finset.disjoint_left]
          intro z hz1 hz2
          cases z with
          | inl i => exact Finset.disjoint_left.mp hdisj_r ((hL₁ i).mp hz1) ((hL₂ i).mp hz2)
          | inr i => exact Finset.disjoint_left.mp hdisj_r ((hR₁ i).mp hz1) ((hR₂ i).mp hz2)
        have hg_inp : ∀ z, z ∈ (C.gates[w - 2 * n]).inputs ↔ z = u ∨ z = v := by
          have hsub_len : (C.gates[w - 2 * n]).inputs.length ≤ 2 := (hM _ (List.getElem_mem hj)).2
          have hu_in : u ∈ (C.gates[w - 2 * n]).inputs := by
            unfold gateParents at hu_mem
            rw [dif_pos ⟨by omega, hj⟩] at hu_mem
            exact (List.mem_filter.mp (List.mem_toFinset.mp hu_mem)).1
          have hv_in : v ∈ (C.gates[w - 2 * n]).inputs := by
            unfold gateParents at hv_mem
            rw [dif_pos ⟨by omega, hj⟩] at hv_mem
            exact (List.mem_filter.mp (List.mem_toFinset.mp hv_mem)).1
          cases hlist : (C.gates[w - 2 * n]).inputs with
          | nil => rw [hlist] at hu_in; simp at hu_in
          | cons a l =>
            cases l with
            | nil =>
              rw [hlist] at hu_in hv_in
              simp only [List.mem_singleton] at hu_in hv_in
              exact absurd (hu_in.trans hv_in.symm) huv
            | cons b l' =>
              cases l' with
              | nil =>
                rw [hlist] at hu_in hv_in
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_in hv_in
                intro z
                simp only [List.mem_cons, List.not_mem_nil, or_false]
                rcases hu_in with rfl | rfl <;> rcases hv_in with rfl | rfl
                · exact absurd rfl huv
                · rfl
                · exact or_comm
                · exact absurd rfl huv
              | cons c l'' =>
                rw [hlist] at hsub_len; simp at hsub_len
        have hlist_pair : (C.gates[w - 2 * n]).inputs = [u, v] ∨ (C.gates[w - 2 * n]).inputs = [v, u] := by
          have hsub_len : (C.gates[w - 2 * n]).inputs.length ≤ 2 := (hM _ (List.getElem_mem hj)).2
          cases hlist : (C.gates[w - 2 * n]).inputs with
          | nil =>
            have := (hg_inp u).mpr (Or.inl rfl); rw [hlist] at this; simp at this
          | cons a l =>
            cases l with
            | nil =>
              have hu1 := (hg_inp u).mpr (Or.inl rfl)
              have hv1 := (hg_inp v).mpr (Or.inr rfl)
              rw [hlist] at hu1 hv1; simp at hu1 hv1; exact absurd (hu1.trans hv1.symm) huv
            | cons b l' =>
              cases l' with
              | nil =>
                have ha := (hg_inp a).mp (by rw [hlist]; simp)
                have hb := (hg_inp b).mp (by rw [hlist]; simp)
                have hu1 := (hg_inp u).mpr (Or.inl rfl)
                have hv1 := (hg_inp v).mpr (Or.inr rfl)
                rw [hlist] at hu1 hv1; simp at hu1 hv1
                rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
                · rcases hv1 with h | h <;> exact absurd h.symm huv
                · left; rfl
                · right; rfl
                · rcases hu1 with h | h <;> exact absurd h huv
              | cons c l'' => rw [hlist] at hsub_len; simp at hsub_len
        have hvarsL : ∀ i : Fin n, Sum.inl i ∈ t₁.vars ∪ t₂.vars ↔ i.val ∈ reach C (2 * n) w := by
          intro i
          rw [Finset.mem_union, hL₁, hL₂]
          conv_rhs => rw [reach_eq, hp_eq]
          simp only [Finset.mem_insert, Finset.biUnion_insert, Finset.biUnion_singleton, Finset.mem_union]
          have hne_w : i.val ≠ w := by omega
          simp [hne_w]
        have hvarsR : ∀ i : Fin n, Sum.inr i ∈ t₁.vars ∪ t₂.vars ↔ n + i.val ∈ reach C (2 * n) w := by
          intro i
          rw [Finset.mem_union, hR₁, hR₂]
          conv_rhs => rw [reach_eq, hp_eq]
          simp only [Finset.mem_insert, Finset.biUnion_insert, Finset.biUnion_singleton, Finset.mem_union]
          have hne_w : n + i.val ≠ w := by omega
          simp [hne_w]
        have hu_lt : u < w := mem_gateParents_lt C (2 * n) w u hu_mem
        have hv_lt : v < w := mem_gateParents_lt C (2 * n) w v hv_mem
        have hop := (hM _ (List.getElem_mem hj)).1
        rcases hop with hop_and | hop_or
        · refine ⟨MTree.and t₁ t₂, ⟨hro₁, hro₂, hdisj_t⟩, hvarsL, hvarsR, ?_⟩
          intro x y
          have hwm : w = (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          conv_rhs => rw [hwm]
          rw [wires_getD_gate C (List.ofFn x ++ List.ofFn y) (w - 2 * n) hj]
          simp only [MTree.eval, hev₁, hev₂, hop_and]
          have hul : u < (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          have hvl : v < (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          rcases hlist_pair with hlp | hlp
          · rw [hlp]
            simp only [GateOp.eval, List.map_cons, List.map_nil, hul, hvl, ↓reduceIte,
              List.all_cons, List.all_nil, id_eq, Bool.and_true]
          · rw [hlp]
            simp only [GateOp.eval, List.map_cons, List.map_nil, hul, hvl, ↓reduceIte,
              List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact Bool.and_comm _ _
        · refine ⟨MTree.or t₁ t₂, ⟨hro₁, hro₂, hdisj_t⟩, hvarsL, hvarsR, ?_⟩
          intro x y
          have hwm : w = (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          conv_rhs => rw [hwm]
          rw [wires_getD_gate C (List.ofFn x ++ List.ofFn y) (w - 2 * n) hj]
          simp at hop_or
          simp only [MTree.eval, hev₁, hev₂, hop_or]
          have hul : u < (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          have hvl : v < (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          rcases hlist_pair with hlp | hlp
          · rw [hlp]
            simp only [GateOp.eval, List.map_cons, List.map_nil, hul, hvl, ↓reduceIte,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · rw [hlp]
            simp only [GateOp.eval, List.map_cons, List.map_nil, hul, hvl, ↓reduceIte,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact Bool.or_comm _ _
  obtain ⟨t, hro, hL, hR, hev⟩ := hbuild C.output (self_mem_reach C (2 * n) C.output)
  have hL' : ∀ i : Fin n, Sum.inl i ∈ t.vars ↔ i ∈ (Finset.univ : Finset (Fin n)) := by
    intro i; simp [hL, hall_inp i.val (by omega)]
  have hR' : ∀ i : Fin n, Sum.inr i ∈ t.vars ↔ i ∈ (Finset.univ : Finset (Fin n)) := by
    intro i; simp [hR, hall_inp (n + i.val) (by omega)]
  have hS_ne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hdiag : ∀ i ∈ (Finset.univ : Finset (Fin n)), t.eval (unitVec i) (unitVec i) = true := by
    intro i _; rw [hev]; change C.eval (oneEach i i) = true; rw [hrep i i]; simp
  have hoff : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ (Finset.univ : Finset (Fin n)),
      i ≠ j → t.eval (unitVec i) (unitVec j) = false := by
    intro i _ j _ hij; rw [hev]; change C.eval (oneEach i j) = false; rw [hrep i j]; simp [hij]
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      t.eval (unitVec i) (fun _ => false) = false ∧ t.eval (fun _ => false) (unitVec i) = false := by
    intro i _; rw [hev, hev]; exact ⟨heval_zeroR i, heval_zeroL i⟩
  obtain ⟨M, hM_match, hM_eq⟩ := classify_mtree t Finset.univ hS_ne hro hL' hR' hdiag hoff hzero
  refine ⟨M, hM_match, ?_⟩
  intro x y
  unfold Circuit.eval
  rw [← hev x y, hM_eq x y]
  simp [matchFn, matchFnOn]

private lemma exists_circuit_of_matching {n : ℕ} (hn : 2 ≤ n) (M : Finset (Finset (Fin n)))
    (hM : IsMatching Finset.univ M) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ 2 * n ∧
      Represents (fun i j : Fin n => decide (i = j)) C ∧
      ∀ x y, matchFn M x y = C.eval (List.ofFn x ++ List.ofFn y) := by
  let covered : Finset (Fin n) := M.biUnion id
  let free : List (Fin n) := (Finset.univ \ covered).toList
  let pairs : List (Finset (Fin n)) := M.toList
  have hcov_card : covered.card = 2 * M.card := by
    rw [Finset.card_biUnion]
    · simp only [id_eq]
      calc
        ∑ e ∈ M, e.card = ∑ _e ∈ M, 2 := Finset.sum_congr rfl (fun e he => (hM.1 e he).1)
        _ = 2 * M.card := by simp [mul_comm]
    · intro e₁ he₁ e₂ he₂ hne; exact hM.2 e₁ he₁ e₂ he₂ hne
  have hfree_len : free.length = n - 2 * M.card := by
    simp only [free, Finset.length_toList]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcov_card]
  have hpairs_len : pairs.length = M.card := Finset.length_toList M
  have h2M_le : 2 * M.card ≤ n := by
    rw [← hcov_card]
    exact le_trans (Finset.card_le_univ covered) (by simp)
  let gFree : List Gate := free.map (fun i => Gate.mk .and [i.val, n + i.val])
  let pairGateFn : Finset (Fin n) → ℕ → List Gate := fun e base =>
    if h : e.Nonempty then
      let a := e.min' h
      let b := e.max' h
      [Gate.mk .or [a.val, n + b.val],
       Gate.mk .or [b.val, n + a.val],
       Gate.mk .and [base, base + 1]]
    else []
  let buildPairs : List (Finset (Fin n)) → ℕ → List Gate × List ℕ :=
    fun ps base => ps.foldl (fun (acc : List Gate × List ℕ) e =>
      let b := base + acc.1.length
      (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) ([], [])
  let bp := buildPairs pairs (2 * n + gFree.length)
  let freeWires : List ℕ := (List.range free.length).map (fun k => 2 * n + k)
  let allWires : List ℕ := freeWires ++ bp.2
  have hbp_len : bp.1.length = 3 * M.card ∧ bp.2.length = M.card ∧
      (∀ g ∈ bp.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) := by
    have hgen : ∀ (ps : List (Finset (Fin n))) (base : ℕ),
        (∀ e ∈ ps, e.card = 2) →
        (buildPairs ps base).1.length = 3 * ps.length ∧
        (buildPairs ps base).2.length = ps.length ∧
        (∀ g ∈ (buildPairs ps base).1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) := by
      intro ps base hps
      have hfold : ∀ (qs : List (Finset (Fin n))) (accG : List Gate) (accW : List ℕ),
          (∀ e ∈ qs, e.card = 2) →
          (∀ g ∈ accG, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
          let res := qs.foldl (fun (acc : List Gate × List ℕ) e =>
            let b := base + acc.1.length
            (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (accG, accW)
          res.1.length = accG.length + 3 * qs.length ∧
          res.2.length = accW.length + qs.length ∧
          (∀ g ∈ res.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) := by
        intro qs
        induction qs with
        | nil =>
          intro accG accW _ hacc
          exact ⟨by simp, by simp, hacc⟩
        | cons e qs ih =>
          intro accG accW hqs hacc
          have he2 : e.card = 2 := hqs e (List.mem_cons_self)
          have hne : e.Nonempty := Finset.card_pos.mp (by omega)
          have hpg_len : (pairGateFn e (base + accG.length)).length = 3 := by
            simp [pairGateFn, hne]
          have hpg_ok : ∀ g ∈ pairGateFn e (base + accG.length),
              g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
            intro g hg
            simp only [pairGateFn, hne, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with rfl | rfl | rfl <;> simp
          simp only [List.foldl_cons]
          have hrec := ih (accG ++ pairGateFn e (base + accG.length)) (accW ++ [base + accG.length + 2])
            (fun e' he' => hqs e' (List.mem_cons_of_mem _ he'))
            (fun g hg => by
              rcases List.mem_append.mp hg with h1 | h2
              · exact hacc g h1
              · exact hpg_ok g h2)
          refine ⟨?_, ?_, hrec.2.2⟩
          · rw [hrec.1, List.length_append, hpg_len]; simp; omega
          · rw [hrec.2.1, List.length_append]; simp; omega
      have h := hfold ps [] [] hps (by simp)
      simpa [buildPairs] using h
    have h := hgen pairs (2 * n + gFree.length) (fun e he => (hM.1 e (Finset.mem_toList.mp he)).1)
    simpa [bp, hpairs_len] using h
  have hallW_len : allWires.length = n - M.card := by
    simp only [allWires, freeWires, List.length_append, List.length_map, List.length_range,
      hfree_len, hbp_len.2.1]
    omega
  have hallW_pos : 0 < allWires.length := by omega
  let orFold : ℕ → List ℕ → ℕ → List Gate × ℕ := fun cur ws base =>
    ws.foldl (fun (acc : List Gate × ℕ) w =>
      (acc.1 ++ [Gate.mk .or [acc.2, w]], base + acc.1.length)) ([], cur)
  have horFold_props : ∀ (cur : ℕ) (ws : List ℕ) (base : ℕ),
      (orFold cur ws base).1.length = ws.length ∧
      (∀ g ∈ (orFold cur ws base).1, g.op = .or ∧ g.inputs.length = 2) ∧
      ∀ (pre : List Gate) (inp : List Bool), inp.length + pre.length = base →
        cur < base → (∀ w ∈ ws, w < base) →
        ((Circuit.mk (pre ++ (orFold cur ws base).1) 0).wires inp).getD (orFold cur ws base).2 false =
          (((Circuit.mk pre 0).wires inp).getD cur false ||
            ws.any (fun w => ((Circuit.mk pre 0).wires inp).getD w false)) := by
    intro cur ws base
    have hgen : ∀ (qs : List ℕ) (accG : List Gate) (accW : ℕ),
        (∀ g ∈ accG, g.op = .or ∧ g.inputs.length = 2) →
        let res := qs.foldl (fun (acc : List Gate × ℕ) w =>
          (acc.1 ++ [Gate.mk .or [acc.2, w]], base + acc.1.length)) (accG, accW)
        res.1.length = accG.length + qs.length ∧
        (∀ g ∈ res.1, g.op = .or ∧ g.inputs.length = 2) ∧
        ∀ (pre : List Gate) (inp : List Bool), inp.length + pre.length = base →
          accW < base + accG.length → (∀ w ∈ qs, w < base) →
          ((Circuit.mk (pre ++ res.1) 0).wires inp).getD res.2 false =
            (((Circuit.mk (pre ++ accG) 0).wires inp).getD accW false ||
              qs.any (fun w => ((Circuit.mk pre 0).wires inp).getD w false)) := by
      intro qs
      induction qs with
      | nil =>
        intro accG accW hacc
        refine ⟨by simp, hacc, ?_⟩
        intro pre inp _ _ _
        simp
      | cons w qs ih =>
        intro accG accW hacc
        simp only [List.foldl_cons]
        have hacc' : ∀ g ∈ accG ++ [Gate.mk .or [accW, w]], g.op = .or ∧ g.inputs.length = 2 := by
          intro g hg
          rcases List.mem_append.mp hg with h1 | h2
          · exact hacc g h1
          · rw [List.mem_singleton.mp h2]; exact ⟨rfl, rfl⟩
        have hrec := ih (accG ++ [Gate.mk .or [accW, w]]) (base + accG.length) hacc'
        refine ⟨?_, hrec.2.1, ?_⟩
        · rw [hrec.1, List.length_append]; simp; omega
        · intro pre inp hbase haccW hqs
          have hw_lt : w < base := hqs w (List.mem_cons_self)
          have hstep := hrec.2.2 pre inp hbase (by rw [List.length_append]; simp)
            (fun w' hw' => hqs w' (List.mem_cons_of_mem _ hw'))
          rw [hstep]
          have hgate : ((Circuit.mk (pre ++ (accG ++ [Gate.mk .or [accW, w]])) 0).wires inp).getD
              (base + accG.length) false =
              (((Circuit.mk (pre ++ accG) 0).wires inp).getD accW false ||
                ((Circuit.mk pre 0).wires inp).getD w false) := by
            rw [← List.append_assoc]
            have hidx : base + accG.length = inp.length + (pre ++ accG).length := by
              rw [List.length_append]; omega
            rw [hidx, wires_getD_step (pre ++ accG) (Gate.mk .or [accW, w]) inp 0]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false]
            congr 1
            rw [wires_append]
            exact wires_getD_prefix accG _ 0 w (by rw [wires_length]; omega)
          rw [hgate]
          simp [Bool.or_assoc]
    have h := hgen ws [] cur (by simp)
    simpa [orFold] using h
  cases hallW_eq : allWires with
  | nil => rw [hallW_eq] at hallW_pos; simp at hallW_pos
  | cons w0 ws =>
    let baseOr := 2 * n + gFree.length + bp.1.length
    let of := orFold w0 ws baseOr
    let C : Circuit := ⟨gFree ++ bp.1 ++ of.1, of.2⟩
    have hC_mono : Monotone2 C := by
      intro g hg
      simp only [C, List.mem_append] at hg
      rcases hg with (hg1 | hg2) | hg3
      · simp only [gFree, List.mem_map] at hg1
        rcases hg1 with ⟨i, _, rfl⟩
        simp
      · exact hbp_len.2.2 g hg2
      · have h := (horFold_props w0 ws baseOr).2.1 g hg3
        exact ⟨Or.inr h.1, by omega⟩
    have hC_sz : C.size + 1 ≤ 2 * n := by
      simp only [C, Circuit.size, List.length_append]
      have hws : ws.length + 1 = n - M.card := by
        have := hallW_len; rw [hallW_eq] at this; simp at this; exact this
      have hgf : gFree.length = n - 2 * M.card := by simp [gFree, hfree_len]
      have hof : of.1.length = ws.length := (horFold_props w0 ws baseOr).1
      omega
    have hC_eval : ∀ x y, matchFn M x y = C.eval (List.ofFn x ++ List.ofFn y) := by
      intro x y
      let inp := List.ofFn x ++ List.ofFn y
      have hinp_len : inp.length = 2 * n := by simp [inp]; omega
      have hinp_L : ∀ i : Fin n, inp.getD i.val false = x i := by
        intro i; simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_left, i.isLt]
      have hinp_R : ∀ i : Fin n, inp.getD (n + i.val) false = y i := by
        intro i; simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right]
      have hpre_free : ∀ k (hk : k < free.length),
          ((Circuit.mk (gFree ++ bp.1) 0).wires inp).getD (2 * n + k) false =
            (x (free[k]) && y (free[k])) := by
        intro k hk
        rw [wires_append]
        have hlen_f : ((Circuit.mk gFree 0).wires inp).length = 2 * n + gFree.length := by
          rw [wires_length, hinp_len]
        have hk_g : k < gFree.length := by simp [gFree, hk]
        rw [wires_getD_prefix bp.1 _ 0 (2 * n + k) (by rw [hlen_f]; omega)]
        rw [← hinp_len, wires_getD_gate (Circuit.mk gFree 0) inp k hk_g]
        have hgk : gFree[k] = Gate.mk .and [(free[k]).val, n + (free[k]).val] := by
          simp [gFree]
        rw [hgk]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true]
        have hlt1 : (free[k]).val < inp.length + k := by omega
        have hlt2 : n + (free[k]).val < inp.length + k := by omega
        simp only [hlt1, hlt2, ↓reduceIte]
        rw [wires_getD_prefix gFree inp 0 _ (by omega),
            wires_getD_prefix gFree inp 0 _ (by omega),
            hinp_L, hinp_R]
      have hpre_pairs : ∀ w ∈ bp.2, w < baseOr ∧
          ∃ e ∈ M, ((Circuit.mk (gFree ++ bp.1) 0).wires inp).getD w false =
            decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
        have hgen_ev : ∀ (ps : List (Finset (Fin n))) (pre : List Gate),
            (∀ e ∈ ps, e ∈ M) →
            let base := inp.length + pre.length
            let res := buildPairs ps base
            (∀ w ∈ res.2, w < base + res.1.length) ∧
            (∀ w ∈ res.2, ∃ e ∈ ps,
              ((Circuit.mk (pre ++ res.1) 0).wires inp).getD w false =
                decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) ∧
            (∀ e ∈ ps, ∃ w ∈ res.2,
              ((Circuit.mk (pre ++ res.1) 0).wires inp).getD w false =
                decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) := by
          intro ps pre hps
          let base := inp.length + pre.length
          have hfold_ev : ∀ (qs : List (Finset (Fin n))) (accG : List Gate) (accW : List ℕ),
              (∀ e ∈ qs, e ∈ M) →
              (∀ w ∈ accW, w < base + accG.length) →
              (∀ w ∈ accW, ∃ e ∈ ps,
                ((Circuit.mk (pre ++ accG) 0).wires inp).getD w false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) →
              (∀ e ∈ qs, e ∈ ps) →
              let res := qs.foldl (fun (acc : List Gate × List ℕ) e =>
                let b := base + acc.1.length
                (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (accG, accW)
              (∀ w ∈ res.2, w < base + res.1.length) ∧
              (∀ w ∈ res.2, ∃ e ∈ ps,
                ((Circuit.mk (pre ++ res.1) 0).wires inp).getD w false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) ∧
              (∀ e ∈ qs, ∃ w ∈ res.2,
                ((Circuit.mk (pre ++ res.1) 0).wires inp).getD w false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) := by
            intro qs
            induction qs with
            | nil =>
              intro accG accW _ hlt hev _
              exact ⟨hlt, hev, by simp⟩
            | cons e qs ih =>
              intro accG accW hqs hlt hev hsub
              have heM : e ∈ M := hqs e (List.mem_cons_self)
              have he2 : e.card = 2 := (hM.1 e heM).1
              have hne : e.Nonempty := Finset.card_pos.mp (by omega)
              let a := e.min' hne
              let b := e.max' hne
              have hab : a ≠ b := by
                intro h
                have : ∀ z ∈ e, z = a := fun z hz =>
                  le_antisymm (h ▸ Finset.le_max' e z hz) (Finset.min'_le e z hz)
                have hsub1 : e ⊆ {a} := fun z hz => Finset.mem_singleton.mpr (this z hz)
                have hle1 := Finset.card_le_card hsub1
                simp at hle1; omega
              have he_eq : e = {a, b} := by
                have hsub2 : ({a, b} : Finset (Fin n)) ⊆ e := by
                  intro z hz
                  rcases Finset.mem_insert.mp hz with rfl | hz
                  · exact Finset.min'_mem e hne
                  · rw [Finset.mem_singleton.mp hz]; exact Finset.max'_mem e hne
                exact (Finset.eq_of_subset_of_card_le hsub2 (by rw [Finset.card_pair hab, he2])).symm
              let base0 := base + accG.length
              have hpg_eq : pairGateFn e base0 =
                  [Gate.mk .or [a.val, n + b.val],
                   Gate.mk .or [b.val, n + a.val],
                   Gate.mk .and [base0, base0 + 1]] := by
                simp [pairGateFn, hne, a, b]
              let accG' := accG ++ pairGateFn e base0
              have hlen_accG' : accG'.length = accG.length + 3 := by simp [accG', hpg_eq]
              have hval_e : ((Circuit.mk (pre ++ accG') 0).wires inp).getD (base0 + 2) false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
                have h0 : ((Circuit.mk (pre ++ accG') 0).wires inp).getD base0 false = (x a || y b) := by
                  have hsplit : pre ++ accG' = ((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]) ++
                      [Gate.mk .or [b.val, n + a.val], Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit, wires_append, wires_getD_prefix]
                  · have hidx : base0 = inp.length + (pre ++ accG).length := by
                      simp [base0, base, List.length_append]; omega
                    rw [hidx, wires_getD_step]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false]
                    rw [wires_getD_prefix _ inp 0 a.val (by omega),
                        wires_getD_prefix _ inp 0 (n + b.val) (by omega),
                        hinp_L, hinp_R]
                  · rw [wires_length]; simp [base0, base, List.length_append]; omega
                have h1 : ((Circuit.mk (pre ++ accG') 0).wires inp).getD (base0 + 1) false = (x b || y a) := by
                  have hsplit : pre ++ accG' = (((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]) ++
                      [Gate.mk .or [b.val, n + a.val]]) ++ [Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit, wires_append, wires_getD_prefix]
                  · have hidx : base0 + 1 = inp.length + ((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]).length := by
                      simp [base0, base, List.length_append]; omega
                    rw [hidx, wires_getD_step]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false]
                    rw [wires_getD_prefix _ inp 0 b.val (by omega),
                        wires_getD_prefix _ inp 0 (n + a.val) (by omega),
                        hinp_L, hinp_R]
                  · rw [wires_length]; simp [base0, base, List.length_append]; omega
                have h2 : ((Circuit.mk (pre ++ accG') 0).wires inp).getD (base0 + 2) false =
                    (((Circuit.mk (pre ++ accG') 0).wires inp).getD base0 false &&
                      ((Circuit.mk (pre ++ accG') 0).wires inp).getD (base0 + 1) false) := by
                  have hsplit : pre ++ accG' = (((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val],
                      Gate.mk .or [b.val, n + a.val]])) ++ [Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit]
                  have hidx : base0 + 2 = inp.length + ((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val],
                      Gate.mk .or [b.val, n + a.val]]).length := by
                    simp [base0, base, List.length_append]; omega
                  rw [hidx, wires_getD_step]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                    id_eq, Bool.and_true]
                  congr 1
                  · conv_rhs => rw [wires_append]
                    refine (wires_getD_prefix _ _ 0 _ ?_).symm
                    simp only [wires_length, List.length_append, List.length_cons, List.length_nil, base0, base]; omega
                  · conv_rhs => rw [wires_append]
                    refine (wires_getD_prefix _ _ 0 _ ?_).symm
                    simp only [wires_length, List.length_append, List.length_cons, List.length_nil, base0, base]; omega
                rw [h2, h0, h1, he_eq]
                simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
                  forall_eq_or_imp, forall_eq]
                cases x a <;> cases x b <;> cases y a <;> cases y b <;> decide
              simp only [List.foldl_cons]
              have hrec := ih accG' (accW ++ [base0 + 2])
                (fun e' he' => hqs e' (List.mem_cons_of_mem _ he'))
                (fun w hw => by
                  rcases List.mem_append.mp hw with h1 | h2
                  · have := hlt w h1; omega
                  · rw [List.mem_singleton.mp h2]; omega)
                (fun w hw => by
                  rcases List.mem_append.mp hw with h1 | h2
                  · obtain ⟨e', he', hev'⟩ := hev w h1
                    refine ⟨e', he', ?_⟩
                    have hpref : ((Circuit.mk (pre ++ accG') 0).wires inp).getD w false =
                        ((Circuit.mk (pre ++ accG) 0).wires inp).getD w false := by
                      have : pre ++ accG' = (pre ++ accG) ++ pairGateFn e base0 := by simp [accG', List.append_assoc]
                      rw [this, wires_append]
                      refine wires_getD_prefix _ _ 0 w ?_
                      have hlw : ((Circuit.mk (pre ++ accG) 0).wires inp).length = inp.length + pre.length + accG.length := by
                        simp only [wires_length, List.length_append, Nat.add_assoc]
                      rw [hlw]; exact hlt w h1
                    rw [hpref, hev']
                  · rw [List.mem_singleton.mp h2]
                    exact ⟨e, hsub e (List.mem_cons_self), hval_e⟩)
                (fun e' he' => hsub e' (List.mem_cons_of_mem _ he'))
              refine ⟨hrec.1, hrec.2.1, ?_⟩
              intro e' he'
              rcases List.mem_cons.mp he' with rfl | he_qs
              · have hmem_res : base0 + 2 ∈ (qs.foldl (fun (acc : List Gate × List ℕ) e =>
                    let b := base + acc.1.length
                    (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (accG', accW ++ [base0 + 2])).2 := by
                  have hmono : ∀ (rs : List (Finset (Fin n))) (ag : List Gate) (aw : List ℕ) (z : ℕ),
                      z ∈ aw → z ∈ (rs.foldl (fun (acc : List Gate × List ℕ) e =>
                        let b := base + acc.1.length
                        (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (ag, aw)).2 := by
                    intro rs
                    induction rs with
                    | nil => intro _ _ _ hz; exact hz
                    | cons r rs ihr =>
                      intro ag aw z hz; simp only [List.foldl_cons]
                      exact ihr _ _ z (List.mem_append_left _ hz)
                  exact hmono qs accG' (accW ++ [base0 + 2]) (base0 + 2) (by simp)
                have hpref_res : ∀ (rs : List (Finset (Fin n))) (ag : List Gate) (aw : List ℕ) (z : ℕ),
                    z < base + ag.length →
                    ((Circuit.mk (pre ++ (rs.foldl (fun (acc : List Gate × List ℕ) e =>
                      let b := base + acc.1.length
                      (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (ag, aw)).1) 0).wires inp).getD z false =
                    ((Circuit.mk (pre ++ ag) 0).wires inp).getD z false := by
                  intro rs
                  induction rs with
                  | nil => intro _ _ _ _; rfl
                  | cons r rs ihr =>
                    intro ag aw z hz
                    simp only [List.foldl_cons]
                    rw [ihr (ag ++ pairGateFn r (base + ag.length)) (aw ++ [base + ag.length + 2]) z
                      (by rw [List.length_append]; omega)]
                    have : pre ++ (ag ++ pairGateFn r (base + ag.length)) =
                        (pre ++ ag) ++ pairGateFn r (base + ag.length) := by simp [List.append_assoc]
                    rw [this, wires_append]
                    refine wires_getD_prefix _ _ 0 z ?_
                    have hlw : ((Circuit.mk (pre ++ ag) 0).wires inp).length = inp.length + pre.length + ag.length := by
                      simp only [wires_length, List.length_append, Nat.add_assoc]
                    rw [hlw]; exact hz
                refine ⟨base0 + 2, hmem_res, ?_⟩
                rw [hpref_res qs accG' (accW ++ [base0 + 2]) (base0 + 2) (by omega), hval_e]
              · exact hrec.2.2 e' he_qs
          have h := hfold_ev ps [] [] hps (by simp) (by simp) (fun _ h => h)
          simpa [buildPairs, base] using h
        have h := hgen_ev pairs gFree (fun e he => Finset.mem_toList.mp he)
        have hbp_eq : bp = buildPairs pairs (inp.length + gFree.length) := by simp [bp, hinp_len]
        intro w hw
        rw [hbp_eq] at hw
        refine ⟨?_, ?_⟩
        · have h1 := h.1 w hw
          simpa [bp, baseOr, hinp_len, Nat.add_assoc] using h1
        · obtain ⟨e, he, hev⟩ := h.2.1 w hw
          exact ⟨e, Finset.mem_toList.mp he, by simpa [bp, hinp_len] using hev⟩
      have hpair_hit : ∀ e ∈ M, ∃ w ∈ bp.2,
          ((Circuit.mk (gFree ++ bp.1) 0).wires inp).getD w false =
            decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
        have hgen_hit : ∀ (qs : List (Finset (Fin n))) (accG : List Gate) (accW : List ℕ),
            (∀ e ∈ qs, e ∈ M) →
            let base := 2 * n + gFree.length
            let res := qs.foldl (fun (acc : List Gate × List ℕ) e =>
              let b := base + acc.1.length
              (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (accG, accW)
            ∀ e ∈ qs, ∃ w ∈ res.2,
              ((Circuit.mk (gFree ++ res.1) 0).wires inp).getD w false =
                decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
          intro qs
          induction qs with
          | nil => intro _ _ _ _ _ _ h; cases h
          | cons e qs ih =>
            intro accG accW hqs
            dsimp only
            have heM : e ∈ M := hqs e (List.mem_cons_self)
            have he2 : e.card = 2 := (hM.1 e heM).1
            have hne : e.Nonempty := Finset.card_pos.mp (by omega)
            let a := e.min' hne
            let b := e.max' hne
            have hab : a ≠ b := by
              intro h
              have : ∀ z ∈ e, z = a := fun z hz =>
                le_antisymm (h ▸ Finset.le_max' e z hz) (Finset.min'_le e z hz)
              have hle1 := Finset.card_le_card (fun z hz => Finset.mem_singleton.mpr (this z hz))
              simp at hle1; omega
            have he_eq : e = {a, b} := by
              have hsub2 : ({a, b} : Finset (Fin n)) ⊆ e := by
                intro z hz
                rcases Finset.mem_insert.mp hz with rfl | hz
                · exact Finset.min'_mem e hne
                · rw [Finset.mem_singleton.mp hz]; exact Finset.max'_mem e hne
              exact (Finset.eq_of_subset_of_card_le hsub2 (by rw [Finset.card_pair hab, he2])).symm
            let base := 2 * n + gFree.length
            let base0 := base + accG.length
            have hpg_eq : pairGateFn e base0 =
                [Gate.mk .or [a.val, n + b.val],
                 Gate.mk .or [b.val, n + a.val],
                 Gate.mk .and [base0, base0 + 1]] := by simp [pairGateFn, hne, a, b]
            let accG' := accG ++ pairGateFn e base0
            have hlen_accG' : accG'.length = accG.length + 3 := by simp [accG', hpg_eq]
            intro e' he'
            rw [List.foldl_cons]
            rcases List.mem_cons.mp he' with he'eq | he_qs
            · rw [he'eq]
              have hval_e : ((Circuit.mk (gFree ++ accG') 0).wires inp).getD (base0 + 2) false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
                have h0 : ((Circuit.mk (gFree ++ accG') 0).wires inp).getD base0 false = (x a || y b) := by
                  have hsplit : gFree ++ accG' = ((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]) ++
                      [Gate.mk .or [b.val, n + a.val], Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit, wires_append, wires_getD_prefix]
                  · have hidx : base0 = inp.length + (gFree ++ accG).length := by
                      simp [base0, base, hinp_len, List.length_append]; omega
                    rw [hidx, wires_getD_step]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false]
                    rw [wires_getD_prefix _ inp 0 a.val (by omega),
                        wires_getD_prefix _ inp 0 (n + b.val) (by omega),
                        hinp_L, hinp_R]
                  · rw [wires_length]; simp [base0, base, hinp_len, List.length_append]; omega
                have h1 : ((Circuit.mk (gFree ++ accG') 0).wires inp).getD (base0 + 1) false = (x b || y a) := by
                  have hsplit : gFree ++ accG' = (((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]) ++
                      [Gate.mk .or [b.val, n + a.val]]) ++ [Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit, wires_append, wires_getD_prefix]
                  · have hidx : base0 + 1 = inp.length + ((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]).length := by
                      simp [base0, base, hinp_len, List.length_append]; omega
                    rw [hidx, wires_getD_step]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false]
                    rw [wires_getD_prefix _ inp 0 b.val (by omega),
                        wires_getD_prefix _ inp 0 (n + a.val) (by omega),
                        hinp_L, hinp_R]
                  · rw [wires_length]; simp [base0, base, hinp_len, List.length_append]; omega
                have h2 : ((Circuit.mk (gFree ++ accG') 0).wires inp).getD (base0 + 2) false =
                    (((Circuit.mk (gFree ++ accG') 0).wires inp).getD base0 false &&
                      ((Circuit.mk (gFree ++ accG') 0).wires inp).getD (base0 + 1) false) := by
                  have hsplit : gFree ++ accG' = (((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val],
                      Gate.mk .or [b.val, n + a.val]])) ++ [Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit]
                  have hidx : base0 + 2 = inp.length + ((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val],
                      Gate.mk .or [b.val, n + a.val]]).length := by
                    simp [base0, base, hinp_len, List.length_append]; omega
                  rw [hidx, wires_getD_step]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                    id_eq, Bool.and_true]
                  congr 1
                  · conv_rhs => rw [wires_append]
                    refine (wires_getD_prefix _ _ 0 _ ?_).symm
                    simp only [wires_length, List.length_append, List.length_cons, List.length_nil,
                      base0, base, inp, List.length_ofFn]; omega
                  · conv_rhs => rw [wires_append]
                    refine (wires_getD_prefix _ _ 0 _ ?_).symm
                    simp only [wires_length, List.length_append, List.length_cons, List.length_nil,
                      base0, base, inp, List.length_ofFn]; omega
                rw [h2, h0, h1, he_eq]
                simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
                  forall_eq_or_imp, forall_eq]
                cases x a <;> cases x b <;> cases y a <;> cases y b <;> decide
              have hmono : ∀ (rs : List (Finset (Fin n))) (ag : List Gate) (aw : List ℕ) (z : ℕ),
                  z ∈ aw → z ∈ (rs.foldl (fun (acc : List Gate × List ℕ) e =>
                    let b := base + acc.1.length
                    (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (ag, aw)).2 := by
                intro rs
                induction rs with
                | nil => intro _ _ _ hz; exact hz
                | cons r rs ihr =>
                  intro ag aw z hz; simp only [List.foldl_cons]
                  exact ihr _ _ z (List.mem_append_left _ hz)
              have hpref_res : ∀ (rs : List (Finset (Fin n))) (ag : List Gate) (aw : List ℕ) (z : ℕ),
                  z < base + ag.length →
                  ((Circuit.mk (gFree ++ (rs.foldl (fun (acc : List Gate × List ℕ) e =>
                    let b := base + acc.1.length
                    (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (ag, aw)).1) 0).wires inp).getD z false =
                  ((Circuit.mk (gFree ++ ag) 0).wires inp).getD z false := by
                intro rs
                induction rs with
                | nil => intro _ _ _ _; rfl
                | cons r rs ihr =>
                  intro ag aw z hz
                  simp only [List.foldl_cons]
                  rw [ihr (ag ++ pairGateFn r (base + ag.length)) (aw ++ [base + ag.length + 2]) z
                    (by rw [List.length_append]; omega)]
                  have : gFree ++ (ag ++ pairGateFn r (base + ag.length)) =
                      (gFree ++ ag) ++ pairGateFn r (base + ag.length) := by simp [List.append_assoc]
                  rw [this, wires_append]
                  refine wires_getD_prefix _ _ 0 z ?_
                  have hlw : ((Circuit.mk (gFree ++ ag) 0).wires inp).length = 2 * n + gFree.length + ag.length := by
                    rw [wires_length, hinp_len, List.length_append, Nat.add_assoc]
                  rw [hlw]; exact hz
              refine ⟨base0 + 2, hmono qs accG' (accW ++ [base0 + 2]) (base0 + 2) (by simp), ?_⟩
              rw [hpref_res qs accG' (accW ++ [base0 + 2]) (base0 + 2) (by omega), hval_e]
            · exact ih accG' (accW ++ [base0 + 2]) (fun e'' he'' => hqs e'' (List.mem_cons_of_mem _ he'')) e' he_qs
        intro e he
        exact hgen_hit pairs [] [] (fun e' he' => Finset.mem_toList.mp he') e (Finset.mem_toList.mpr he)
      have hall_lt : ∀ w ∈ allWires, w < baseOr := by
        intro w hw
        rcases List.mem_append.mp hw with h1 | h2
        · simp only [freeWires, List.mem_map, List.mem_range] at h1
          rcases h1 with ⟨k, hk, rfl⟩
          have : gFree.length = free.length := by simp [gFree]
          omega
        · exact (hpre_pairs w h2).1
      have hC_any : C.eval inp =
          allWires.any (fun w => ((Circuit.mk (gFree ++ bp.1) 0).wires inp).getD w false) := by
        unfold Circuit.eval
        change ((Circuit.mk ((gFree ++ bp.1) ++ of.1) of.2).wires inp).getD of.2 false = _
        have h := (horFold_props w0 ws baseOr).2.2 (gFree ++ bp.1) inp
          (by rw [hinp_len, List.length_append]; omega)
          (hall_lt w0 (by rw [hallW_eq]; simp))
          (fun w hw => hall_lt w (by rw [hallW_eq]; exact List.mem_cons_of_mem _ hw))
        rw [hallW_eq, List.any_cons]
        exact h
      rw [hC_any]
      apply Bool.eq_iff_iff.mpr
      simp only [matchFn, decide_eq_true_eq, List.any_eq_true]
      constructor
      · rintro (⟨i, hxi, hyi⟩ | ⟨e, he, hex⟩)
        · by_cases hi : i ∈ covered
          · rcases Finset.mem_biUnion.mp hi with ⟨e, heM, hie⟩
            obtain ⟨w, hw, hwev⟩ := hpair_hit e heM
            refine ⟨w, List.mem_append_right _ hw, ?_⟩
            rw [hwev]
            exact decide_eq_true (Or.inl ⟨i, hie, hxi, hyi⟩)
          · have hi_free : i ∈ free := Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
            obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi_free
            refine ⟨2 * n + k, List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), ?_⟩
            rw [hpre_free k hk, hxi, hyi]; rfl
        · obtain ⟨w, hw, hwev⟩ := hpair_hit e he
          refine ⟨w, List.mem_append_right _ hw, ?_⟩
          rw [hwev]
          exact decide_eq_true (Or.inr hex)
      · rintro ⟨w, hw, hwt⟩
        rcases List.mem_append.mp hw with h1 | h2
        · simp only [freeWires, List.mem_map, List.mem_range] at h1
          rcases h1 with ⟨k, hk, rfl⟩
          rw [hpre_free k hk, Bool.and_eq_true] at hwt
          exact Or.inl ⟨free[k], hwt.1, hwt.2⟩
        · obtain ⟨e, heM, hwev⟩ := (hpre_pairs w h2).2
          rw [hwev, decide_eq_true_eq] at hwt
          rcases hwt with ⟨i, _, hxi, hyi⟩ | hex
          · exact Or.inl ⟨i, hxi, hyi⟩
          · exact Or.inr ⟨e, heM, hex⟩
    refine ⟨C, hC_mono, hC_sz, ?_, hC_eval⟩
    intro u v
    have h1 := (hC_eval (unitVec u) (unitVec v)).symm
    change C.eval (List.ofFn (unitVec u) ++ List.ofFn (unitVec v)) = decide (u = v)
    rw [h1]
    simp only [matchFn, unitVec]
    by_cases huv : u = v
    · rw [decide_eq_true huv]
      exact decide_eq_true (Or.inl ⟨u, by simp, by simp [huv]⟩)
    · rw [decide_eq_false huv]
      apply decide_eq_false
      rintro (⟨i, hiu, hiv⟩ | ⟨e, he, hL | hR⟩)
      · simp only [decide_eq_true_eq] at hiu hiv
        exact huv (hiu.symm.trans hiv)
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hM.1 e he).1
        have ha : a = u := decide_eq_true_eq.mp (hL a (Finset.mem_insert_self _ _))
        have hb : b = u := decide_eq_true_eq.mp (hL b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        exact hab (ha.trans hb.symm)
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hM.1 e he).1
        have ha : a = v := decide_eq_true_eq.mp (hR a (Finset.mem_insert_self _ _))
        have hb : b = v := decide_eq_true_eq.mp (hR b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        exact hab (ha.trans hb.symm)

private lemma matchFn_obs_empty {n : ℕ} (M : Finset (Finset (Fin n))) (hM : IsMatching Finset.univ M)
    (R : Finset (Fin n)) :
    matchFn M (fun i => decide (i ∈ R)) (fun _ => decide (False)) = true ↔
      ∃ e ∈ M, e ⊆ R := by
  simp only [matchFn, decide_eq_true_eq, decide_false, reduceCtorEq, and_false, exists_false,
    false_or]
  constructor
  · rintro ⟨e, he, hL | hR⟩
    · exact ⟨e, he, fun i hi => hL i hi⟩
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [(hM.1 e he).1]; decide)
      exact False.elim (hR a ha)
  · rintro ⟨e, he, hsub⟩
    exact ⟨e, he, Or.inl (fun i hi => hsub hi)⟩

private lemma matchFn_obs_pair {n : ℕ} (M : Finset (Finset (Fin n))) (hM : IsMatching Finset.univ M)
    (R S : Finset (Fin n)) :
    matchFn M (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S)) = false ↔
      Disjoint R S ∧ ∀ e ∈ M, ¬ (e ⊆ R) ∧ ¬ (e ⊆ S) := by
  simp only [matchFn, decide_eq_false_iff_not, not_or, not_exists, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Finset.disjoint_left.mpr (fun i hiR hiS => h1 i (decide_eq_true hiR) (decide_eq_true hiS)), ?_⟩
    intro e he
    have h := h2 e he
    push_neg at h
    exact ⟨fun hsub => by rcases h.1 with ⟨i, hi, hni⟩; exact hni (decide_eq_true (hsub hi)),
           fun hsub => by rcases h.2 with ⟨i, hi, hni⟩; exact hni (decide_eq_true (hsub hi))⟩
  · rintro ⟨hd, h2⟩
    refine ⟨fun i hiR hiS => Finset.disjoint_left.mp hd (decide_eq_true_eq.mp hiR) (decide_eq_true_eq.mp hiS), ?_⟩
    intro e he
    exact ⟨fun hL => (h2 e he).1 (fun i hi => decide_eq_true_eq.mp (hL i hi)),
           fun hR => (h2 e he).2 (fun i hi => decide_eq_true_eq.mp (hR i hi))⟩

private lemma matchFn_inj {n : ℕ} {M₁ M₂ : Finset (Finset (Fin n))}
    (h1 : IsMatching Finset.univ M₁) (h2 : IsMatching Finset.univ M₂)
    (heq : matchFn M₁ = matchFn M₂) : M₁ = M₂ := by
  ext e
  constructor
  · intro he1
    have hobs : matchFn M₁ (fun i => decide (i ∈ e)) (fun _ => decide False) = true :=
      (matchFn_obs_empty M₁ h1 e).mpr ⟨e, he1, subset_refl e⟩
    rw [heq, matchFn_obs_empty M₂ h2 e] at hobs
    rcases hobs with ⟨e', he2, hsub⟩
    have hcard_eq : e'.card = e.card := by rw [(h2.1 e' he2).1, (h1.1 e he1).1]
    rwa [← Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)]
  · intro he2
    have hobs : matchFn M₂ (fun i => decide (i ∈ e)) (fun _ => decide False) = true :=
      (matchFn_obs_empty M₂ h2 e).mpr ⟨e, he2, subset_refl e⟩
    rw [← heq, matchFn_obs_empty M₁ h1 e] at hobs
    rcases hobs with ⟨e', he1, hsub⟩
    have hcard_eq : e'.card = e.card := by rw [(h1.1 e' he1).1, (h2.1 e he2).1]
    rwa [← Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)]

private lemma matchFn_size {n : ℕ} (M : Finset (Finset (Fin n))) (hM : IsMatching Finset.univ M) :
    (Finset.univ.filter (fun z : Fin n × Fin n =>
      z.1 < z.2 ∧ matchFn M (fun i => decide (i ∈ ({z.1, z.2} : Finset (Fin n))))
        (fun j => decide (j ∈ (∅ : Finset (Fin n)))) = true)).card = M.card := by
  have heq_pred : ∀ z : Fin n × Fin n,
      (z.1 < z.2 ∧ matchFn M (fun i => decide (i ∈ ({z.1, z.2} : Finset (Fin n))))
        (fun j => decide (j ∈ (∅ : Finset (Fin n)))) = true) ↔
      (z.1 < z.2 ∧ ({z.1, z.2} : Finset (Fin n)) ∈ M) := by
    intro z
    constructor
    · rintro ⟨hlt, hobs⟩
      have hobs' : matchFn M (fun i => decide (i ∈ ({z.1, z.2} : Finset (Fin n))))
          (fun _ => decide False) = true := by simpa using hobs
      rcases (matchFn_obs_empty M hM {z.1, z.2}).mp hobs' with ⟨e, heM, hsub⟩
      have hcard : ({z.1, z.2} : Finset (Fin n)).card = 2 := Finset.card_pair (ne_of_lt hlt)
      have heq : e = {z.1, z.2} := Finset.eq_of_subset_of_card_le hsub (by rw [(hM.1 e heM).1, hcard])
      exact ⟨hlt, heq ▸ heM⟩
    · rintro ⟨hlt, hmem⟩
      refine ⟨hlt, ?_⟩
      have hobs' := (matchFn_obs_empty M hM {z.1, z.2}).mpr ⟨{z.1, z.2}, hmem, subset_refl _⟩
      simpa using hobs'
  refine Finset.card_bij (fun z _ => ({z.1, z.2} : Finset (Fin n))) ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_filter] at hz
    exact ((heq_pred z).mp hz.2).2
  · intro z₁ hz₁ z₂ hz₂ heq
    rw [Finset.mem_filter] at hz₁ hz₂
    have h1 := ((heq_pred z₁).mp hz₁.2).1
    have h2 := ((heq_pred z₂).mp hz₂.2).1
    have hmin1 : ({z₁.1, z₁.2} : Finset (Fin n)).min' (by simp) = z₁.1 := by
      apply le_antisymm (Finset.min'_le _ _ (by simp))
      refine Finset.le_min' _ _ _ (fun y hy => ?_)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact le_refl _
      · rw [Finset.mem_singleton.mp hy]; exact le_of_lt h1
    have hmin2 : ({z₂.1, z₂.2} : Finset (Fin n)).min' (by simp) = z₂.1 := by
      apply le_antisymm (Finset.min'_le _ _ (by simp))
      refine Finset.le_min' _ _ _ (fun y hy => ?_)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact le_refl _
      · rw [Finset.mem_singleton.mp hy]; exact le_of_lt h2
    have hmax1 : ({z₁.1, z₁.2} : Finset (Fin n)).max' (by simp) = z₁.2 := by
      apply le_antisymm _ (Finset.le_max' _ _ (by simp))
      refine Finset.max'_le _ _ _ (fun y hy => ?_)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact le_of_lt h1
      · rw [Finset.mem_singleton.mp hy]
    have hmax2 : ({z₂.1, z₂.2} : Finset (Fin n)).max' (by simp) = z₂.2 := by
      apply le_antisymm _ (Finset.le_max' _ _ (by simp))
      refine Finset.max'_le _ _ _ (fun y hy => ?_)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact le_of_lt h2
      · rw [Finset.mem_singleton.mp hy]
    apply Prod.ext
    · rw [← hmin1, ← hmin2]; simp [heq]
    · rw [← hmax1, ← hmax2]; simp [heq]
  · intro e he
    have hne : e.Nonempty := Finset.card_pos.mp (by rw [(hM.1 e he).1]; decide)
    let a := e.min' hne
    let b := e.max' hne
    have hlt : a < b := by
      have hle : a ≤ b := Finset.min'_le e b (Finset.max'_mem e hne)
      refine lt_of_le_of_ne hle (fun h => ?_)
      have hsub : e ⊆ {a} := fun y hy => Finset.mem_singleton.mpr
        (le_antisymm (h ▸ Finset.le_max' e y hy) (Finset.min'_le e y hy))
      have hc := Finset.card_le_card hsub
      rw [(hM.1 e he).1] at hc; simp at hc
    have heq : ({a, b} : Finset (Fin n)) = e := by
      refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_pair (ne_of_lt hlt), (hM.1 e he).1])
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.min'_mem e hne
      · rw [Finset.mem_singleton.mp hy]; exact Finset.max'_mem e hne
    refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (heq_pred (a, b)).mpr ⟨hlt, heq.symm ▸ he⟩⟩, heq⟩

private def ZPoly {α : Type*} [DecidableEq α]
    (V : Finset α) (F₂ H : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ) (z : ℂ) : ℂ :=
  ∑ M ∈ (V.powerset.filter (fun e => e.card = 2)).powerset.filter
      (fun M => IsMatching V M ∧ F₂ ⊆ M ∧ ∀ R ∈ H, ∃ e ∈ M, e ⊆ R),
    ((∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card

private def MPoly {α : Type*} [DecidableEq α]
    (V : Finset α) (w : Finset α → ℝ) (z : ℂ) : ℂ :=
  ∑ M ∈ (V.powerset.filter (fun e => e.card = 2)).powerset.filter (fun M => IsMatching V M),
    (∏ e ∈ M, (w e : ℂ)) * z ^ M.card

private def matchingsOn {α : Type*} [DecidableEq α] (V : Finset α) : Finset (Finset (Finset α)) :=
  (V.powerset.filter (fun e => e.card = 2)).powerset.filter (fun M => IsMatching V M)

private lemma mem_matchingsOn {α : Type*} [DecidableEq α] {V : Finset α} {M : Finset (Finset α)} :
    M ∈ matchingsOn V ↔ IsMatching V M := by
  simp only [matchingsOn, Finset.mem_filter, Finset.mem_powerset, and_iff_right_iff_imp]
  intro hM e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hM.1 e he).2, (hM.1 e he).1⟩

private def muPoly {α : Type*} [DecidableEq α]
    (V : Finset α) (w : Finset α → ℝ) (z : ℂ) : ℂ :=
  ∑ M ∈ matchingsOn V, (-1 : ℂ) ^ M.card * (∏ e ∈ M, (w e : ℂ)) * z ^ (V.card - 2 * M.card)

private lemma card_biUnion_matching {α : Type*} [DecidableEq α] {V : Finset α} {M : Finset (Finset α)}
    (hM : IsMatching V M) : (M.biUnion id).card = 2 * M.card := by
  rw [Finset.card_biUnion (s := M) (t := id) (fun e₁ he₁ e₂ he₂ hne => hM.2 e₁ he₁ e₂ he₂ hne)]
  simp only [id_eq]
  calc
    ∑ e ∈ M, e.card = ∑ _e ∈ M, 2 := Finset.sum_congr rfl (fun e he => (hM.1 e he).1)
    _ = 2 * M.card := by simp [mul_comm]

private lemma two_mul_card_le_of_matching {α : Type*} [DecidableEq α] {V : Finset α}
    {M : Finset (Finset α)} (hM : IsMatching V M) : 2 * M.card ≤ V.card := by
  rw [← card_biUnion_matching hM]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun e he => (hM.1 e he).2))

private lemma muPoly_eq_MPoly {α : Type*} [DecidableEq α]
    (V : Finset α) (w : Finset α → ℝ) {z : ℂ} (hz : z ≠ 0) :
    muPoly V w z = z ^ V.card * MPoly V w (-z⁻¹ ^ 2) := by
  unfold muPoly MPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  have hMm : IsMatching V M := mem_matchingsOn.mp hM
  have hle : 2 * M.card ≤ V.card := two_mul_card_le_of_matching hMm
  have hpow : z ^ V.card * (-z⁻¹ ^ 2) ^ M.card = (-1 : ℂ) ^ M.card * z ^ (V.card - 2 * M.card) := by
    have hsplit : V.card = (V.card - 2 * M.card) + 2 * M.card := by omega
    conv_lhs => rw [hsplit, pow_add]
    have hneg : (-z⁻¹ ^ 2) ^ M.card = (-1 : ℂ) ^ M.card * (z ^ (2 * M.card))⁻¹ := by
      rw [neg_eq_neg_one_mul, mul_pow, ← inv_pow, ← pow_mul, inv_pow]
    rw [hneg]
    have hne : z ^ (2 * M.card) ≠ 0 := pow_ne_zero _ hz
    calc
      z ^ (V.card - 2 * M.card) * z ^ (2 * M.card) * ((-1 : ℂ) ^ M.card * (z ^ (2 * M.card))⁻¹)
        = (-1 : ℂ) ^ M.card * z ^ (V.card - 2 * M.card) * (z ^ (2 * M.card) * (z ^ (2 * M.card))⁻¹) := by ring
      _ = (-1 : ℂ) ^ M.card * z ^ (V.card - 2 * M.card) * 1 := by rw [mul_inv_cancel₀ hne]
      _ = (-1 : ℂ) ^ M.card * z ^ (V.card - 2 * M.card) := mul_one _
  calc
    (-1 : ℂ) ^ M.card * (∏ e ∈ M, (w e : ℂ)) * z ^ (V.card - 2 * M.card)
      = (∏ e ∈ M, (w e : ℂ)) * ((-1 : ℂ) ^ M.card * z ^ (V.card - 2 * M.card)) := by ring
    _ = (∏ e ∈ M, (w e : ℂ)) * (z ^ V.card * (-z⁻¹ ^ 2) ^ M.card) := by rw [hpow]
    _ = z ^ V.card * ((∏ e ∈ M, (w e : ℂ)) * (-z⁻¹ ^ 2) ^ M.card) := by ring

private lemma muPoly_expand {α : Type*} [DecidableEq α]
    (V : Finset α) (w : Finset α → ℝ) (z : ℂ) (v : α) (hv : v ∈ V) :
    muPoly V w z = z * muPoly (V.erase v) w z -
      ∑ u ∈ V.erase v, (w {v, u} : ℂ) * muPoly ((V.erase v).erase u) w z := by
  unfold muPoly
  let S0 := (matchingsOn V).filter (fun M => v ∉ M.biUnion id)
  let Su := fun u : α => (matchingsOn V).filter (fun M => ({v, u} : Finset α) ∈ M)
  have hpart : matchingsOn V = S0 ∪ (V.erase v).biUnion Su := by
    ext M
    simp only [Finset.mem_union, S0, Su, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_erase]
    constructor
    · intro hM
      by_cases hvin : v ∈ M.biUnion id
      · right
        rcases Finset.mem_biUnion.mp hvin with ⟨e, heM, hve⟩
        have hMm := mem_matchingsOn.mp hM
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hMm.1 e heM).1
        rcases Finset.mem_insert.mp hve with rfl | hvb
        · exact ⟨b, ⟨hab.symm, (hMm.1 _ heM).2 (by simp)⟩, hM, heM⟩
        · obtain rfl : v = b := Finset.mem_singleton.mp hvb
          have hpair : ({a, v} : Finset α) = {v, a} := Finset.pair_comm a v
          exact ⟨a, ⟨hab, (hMm.1 _ heM).2 (by simp)⟩, hM, hpair ▸ heM⟩
      · left; exact ⟨hM, by simpa using hvin⟩
    · rintro (⟨hM, _⟩ | ⟨_, _, hM, _⟩) <;> exact hM
  have hdisj0 : Disjoint S0 ((V.erase v).biUnion Su) := by
    rw [Finset.disjoint_left]
    intro M h1 h2
    simp only [S0, Finset.mem_filter] at h1
    simp only [Su, Finset.mem_biUnion, Finset.mem_filter] at h2
    rcases h2 with ⟨u, _, _, huv⟩
    exact h1.2 (Finset.mem_biUnion.mpr ⟨{v, u}, huv, by simp⟩)
  have hdisju : ∀ u₁ ∈ V.erase v, ∀ u₂ ∈ V.erase v, u₁ ≠ u₂ → Disjoint (Su u₁) (Su u₂) := by
    intro u₁ _ u₂ _ hne
    rw [Finset.disjoint_left]
    intro M h1 h2
    simp only [Su, Finset.mem_filter] at h1 h2
    have hMm := mem_matchingsOn.mp h1.1
    have hne_e : ({v, u₁} : Finset α) ≠ {v, u₂} := by
      intro h
      have hu1 : u₁ ∈ ({v, u₂} : Finset α) := h ▸ by simp
      rcases Finset.mem_insert.mp hu1 with h1v | h12
      · have hne1 : u₁ ≠ v := (Finset.mem_erase.mp ‹_›).1
        exact hne1 h1v
      · exact hne (Finset.mem_singleton.mp h12)
    have hv1 : v ∈ ({v, u₁} : Finset α) := by simp
    have hv2 : v ∈ ({v, u₂} : Finset α) := by simp
    exact Finset.disjoint_left.mp (hMm.2 _ h1.2 _ h2.2 hne_e) hv1 hv2
  rw [hpart, Finset.sum_union hdisj0, Finset.sum_biUnion hdisju, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_bij (fun M _ => M) ?_ ?_ ?_ ?_
    · intro M hM
      simp only [S0, Finset.mem_filter, mem_matchingsOn] at hM ⊢
      refine ⟨fun e he => ⟨(hM.1.1 e he).1, fun x hx => Finset.mem_erase.mpr
        ⟨fun hxv => hM.2 (Finset.mem_biUnion.mpr ⟨e, he, hxv ▸ hx⟩), (hM.1.1 e he).2 hx⟩⟩, hM.1.2⟩
    · intro _ _ _ _ h; exact h
    · intro M hM
      have hMm := mem_matchingsOn.mp hM
      refine ⟨M, Finset.mem_filter.mpr ⟨mem_matchingsOn.mpr ⟨fun e he =>
        ⟨(hMm.1 e he).1, (hMm.1 e he).2.trans (Finset.erase_subset _ _)⟩, hMm.2⟩,
        fun hv_in => by
          rcases Finset.mem_biUnion.mp hv_in with ⟨e, he, hve⟩
          exact (Finset.mem_erase.mp ((hMm.1 e he).2 hve)).1 rfl⟩, rfl⟩
    · intro M hM
      have hMm := mem_matchingsOn.mp (Finset.mem_filter.mp hM).1
      have hle : 2 * M.card ≤ (V.erase v).card := by
        have hM' : IsMatching (V.erase v) M := ⟨fun e he => ⟨(hMm.1 e he).1, fun x hx =>
          Finset.mem_erase.mpr ⟨fun hxv => (Finset.mem_filter.mp hM).2
            (Finset.mem_biUnion.mpr ⟨e, he, hxv ▸ hx⟩), (hMm.1 e he).2 hx⟩⟩, hMm.2⟩
        exact two_mul_card_le_of_matching hM'
      have hcard : V.card = (V.erase v).card + 1 := (Finset.card_erase_add_one hv).symm
      have hexp : V.card - 2 * M.card = ((V.erase v).card - 2 * M.card) + 1 := by omega
      rw [hexp, pow_succ]
      ring
  · refine Finset.sum_congr rfl (fun u hu => ?_)
    have huv : u ≠ v := (Finset.mem_erase.mp hu).1
    rw [← neg_mul, Finset.mul_sum]
    refine Finset.sum_bij (fun M _ => M.erase {v, u}) ?_ ?_ ?_ ?_
    · intro M hM
      simp only [Su, Finset.mem_filter, mem_matchingsOn] at hM ⊢
      refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ hne =>
        hM.1.2 e₁ (Finset.mem_of_mem_erase he₁) e₂ (Finset.mem_of_mem_erase he₂) hne⟩
      have heM := Finset.mem_of_mem_erase he
      have hdisj := hM.1.2 e heM {v, u} hM.2 (Finset.ne_of_mem_erase he)
      refine ⟨(hM.1.1 e heM).1, fun x hx => ?_⟩
      refine Finset.mem_erase.mpr ⟨fun hxu => Finset.disjoint_left.mp hdisj hx (by simp [hxu]),
        Finset.mem_erase.mpr ⟨fun hxv => Finset.disjoint_left.mp hdisj hx (by simp [hxv]),
          (hM.1.1 e heM).2 hx⟩⟩
    · intro M₁ hM₁ M₂ hM₂ heq
      have h1 := (Finset.mem_filter.mp hM₁).2
      have h2 := (Finset.mem_filter.mp hM₂).2
      rw [← Finset.insert_erase h1, ← Finset.insert_erase h2, heq]
    · intro M' hM'
      have hM'm := mem_matchingsOn.mp hM'
      have hnot : ({v, u} : Finset α) ∉ M' := fun h =>
        (Finset.mem_erase.mp ((hM'm.1 _ h).2 (by simp))).1 rfl
      have hM_ins : IsMatching V (insert {v, u} M') := by
        refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ hne => ?_⟩
        · rcases Finset.mem_insert.mp he with rfl | he'
          · exact ⟨Finset.card_pair huv.symm, fun x hx => by
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact hv
              · rw [Finset.mem_singleton.mp hx]; exact (Finset.mem_erase.mp hu).2⟩
          · exact ⟨(hM'm.1 e he').1, (hM'm.1 e he').2.trans
              ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))⟩
        · rcases Finset.mem_insert.mp he₁ with rfl | h1 <;> rcases Finset.mem_insert.mp he₂ with rfl | h2
          · exact absurd rfl hne
          · rw [Finset.disjoint_left]
            intro x hx1 hx2
            have hx2' := (hM'm.1 e₂ h2).2 hx2
            rcases Finset.mem_insert.mp hx1 with rfl | hx1
            · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx2').2).1 rfl
            · rw [Finset.mem_singleton.mp hx1] at hx2'
              exact (Finset.mem_erase.mp hx2').1 rfl
          · rw [Finset.disjoint_right]
            intro x hx2 hx1
            have hx1' := (hM'm.1 e₁ h1).2 hx1
            rcases Finset.mem_insert.mp hx2 with rfl | hx2
            · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx1').2).1 rfl
            · rw [Finset.mem_singleton.mp hx2] at hx1'
              exact (Finset.mem_erase.mp hx1').1 rfl
          · exact hM'm.2 e₁ h1 e₂ h2 hne
      exact ⟨insert {v, u} M', Finset.mem_filter.mpr ⟨mem_matchingsOn.mpr hM_ins, Finset.mem_insert_self _ _⟩,
        Finset.erase_insert hnot⟩
    · intro M hM
      have hvu : ({v, u} : Finset α) ∈ M := (Finset.mem_filter.mp hM).2
      have hcardM : M.card = (M.erase {v, u}).card + 1 := (Finset.card_erase_add_one hvu).symm
      have hcardV : V.card = ((V.erase v).erase u).card + 2 := by
        have h1 := Finset.card_erase_add_one hv
        have h2 := Finset.card_erase_add_one hu
        omega
      have hexp : V.card - 2 * M.card = ((V.erase v).erase u).card - 2 * (M.erase {v, u}).card := by omega
      have hprod : ∏ e ∈ M, (w e : ℂ) = (w {v, u} : ℂ) * ∏ e ∈ M.erase {v, u}, (w e : ℂ) :=
        (Finset.mul_prod_erase M (fun e => (w e : ℂ)) hvu).symm
      rw [hexp, hcardM, hprod, pow_succ]
      ring

private lemma im_neg_inv_pos {ζ : ℂ} (h : 0 < ζ.im) : 0 < (-ζ⁻¹).im := by
  have hne : ζ ≠ 0 := fun h0 => by rw [h0] at h; simp at h
  have hns : 0 < Complex.normSq ζ := Complex.normSq_pos.mpr hne
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos h hns

private lemma heilmann_lieb_upper {α : Type*} [DecidableEq α]
    (w : Finset α → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∀ (k : ℕ) (V : Finset α), V.card = k → ∀ z : ℂ, 0 < z.im →
      muPoly V w z ≠ 0 ∧ ∀ v ∈ V, 0 < (muPoly V w z / muPoly (V.erase v) w z).im := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro V hcard z hz
    have hratio : ∀ v ∈ V, 0 < (muPoly V w z / muPoly (V.erase v) w z).im := by
      intro v hv
      have h1 : (V.erase v).card = k - 1 := by
        have := Finset.card_erase_add_one hv; omega
      have hlt1 : k - 1 < k := by
        have := Finset.card_pos.mpr ⟨v, hv⟩; omega
      have hih1 := ih (k - 1) hlt1 (V.erase v) h1 z hz
      have hne1 : muPoly (V.erase v) w z ≠ 0 := hih1.1
      rw [muPoly_expand V w z v hv, sub_div, mul_div_cancel_right₀ _ hne1, Finset.sum_div]
      simp only [Complex.sub_im, Complex.im_sum]
      have hsum_le : ∑ u ∈ V.erase v, ((w {v, u} : ℂ) * muPoly ((V.erase v).erase u) w z /
          muPoly (V.erase v) w z).im ≤ 0 := by
        refine Finset.sum_nonpos (fun u hu => ?_)
        have hpos_u : 0 < (muPoly (V.erase v) w z / muPoly ((V.erase v).erase u) w z).im := hih1.2 u hu
        have h2 : ((V.erase v).erase u).card = k - 2 := by
          have := Finset.card_erase_add_one hu; omega
        have hne2 : muPoly ((V.erase v).erase u) w z ≠ 0 :=
          (ih (k - 2) (by omega) ((V.erase v).erase u) h2 z hz).1
        have hinv_eq : (w {v, u} : ℂ) * muPoly ((V.erase v).erase u) w z / muPoly (V.erase v) w z =
            -((w {v, u} : ℂ) * (-(muPoly (V.erase v) w z / muPoly ((V.erase v).erase u) w z)⁻¹)) := by
          rw [inv_div, mul_neg, neg_neg, mul_div_assoc]
        rw [hinv_eq, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero]
        have h_im_pos : 0 < (-(muPoly (V.erase v) w z / muPoly ((V.erase v).erase u) w z)⁻¹).im :=
          im_neg_inv_pos hpos_u
        have hnonneg : 0 ≤ w {v, u} * (-(muPoly (V.erase v) w z / muPoly ((V.erase v).erase u) w z)⁻¹).im :=
          mul_nonneg (hw _) (le_of_lt h_im_pos)
        linarith
      linarith
    refine ⟨?_, hratio⟩
    by_cases hV : V.Nonempty
    · obtain ⟨v, hv⟩ := hV
      intro h0
      have hr := hratio v hv
      rw [h0, zero_div] at hr
      simp at hr
    · rw [Finset.not_nonempty_iff_eq_empty] at hV
      subst hV
      have h1 : muPoly (∅ : Finset α) w z = 1 := by
        unfold muPoly
        have hm : matchingsOn (∅ : Finset α) = {∅} := by
          ext M
          simp only [mem_matchingsOn, Finset.mem_singleton]
          constructor
          · intro hM
            ext e
            simp only [Finset.notMem_empty, iff_false]
            intro he
            have hc := (hM.1 e he).1
            have hs := Finset.subset_empty.mp (hM.1 e he).2
            rw [hs] at hc; simp at hc
          · rintro rfl; exact ⟨by simp, by simp⟩
        rw [hm]; simp
      rw [h1]; exact one_ne_zero

private lemma muPoly_conj {α : Type*} [DecidableEq α]
    (V : Finset α) (w : Finset α → ℝ) (z : ℂ) :
    muPoly V w (starRingEnd ℂ z) = starRingEnd ℂ (muPoly V w z) := by
  unfold muPoly
  rw [map_sum]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  simp [map_mul, map_pow, map_prod]

private lemma exists_complex_sq (c : ℂ) : ∃ z : ℂ, z ^ 2 = c := by
  let r := Real.sqrt (c.re ^ 2 + c.im ^ 2)
  have hr_ge : |c.re| ≤ r := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg c.im])
  have h1 : 0 ≤ (r + c.re) / 2 := by linarith [neg_abs_le c.re]
  have h2 : 0 ≤ (r - c.re) / 2 := by linarith [le_abs_self c.re]
  let a := Real.sqrt ((r + c.re) / 2)
  let b := Real.sqrt ((r - c.re) / 2)
  have ha2 : a ^ 2 = (r + c.re) / 2 := Real.sq_sqrt h1
  have hb2 : b ^ 2 = (r - c.re) / 2 := Real.sq_sqrt h2
  have hab2 : (2 * a * b) ^ 2 = c.im ^ 2 := by
    have hr2 : r ^ 2 = c.re ^ 2 + c.im ^ 2 := Real.sq_sqrt (by positivity)
    calc
      (2 * a * b) ^ 2 = 4 * a ^ 2 * b ^ 2 := by ring
      _ = 4 * ((r + c.re) / 2) * ((r - c.re) / 2) := by rw [ha2, hb2]
      _ = r ^ 2 - c.re ^ 2 := by ring
      _ = c.im ^ 2 := by linarith
  have hab_nn : 0 ≤ 2 * a * b := by positivity
  by_cases him : 0 ≤ c.im
  · refine ⟨⟨a, b⟩, ?_⟩
    have hab : 2 * a * b = c.im := by nlinarith
    apply Complex.ext
    · simp only [sq, Complex.mul_re]; linarith
    · simp only [sq, Complex.mul_im]; linarith
  · refine ⟨⟨a, -b⟩, ?_⟩
    have hab : 2 * a * b = -c.im := by nlinarith
    apply Complex.ext
    · simp only [sq, Complex.mul_re]; linarith
    · simp only [sq, Complex.mul_im]; linarith

private lemma MPoly_roots_real_neg {α : Type*} [DecidableEq α]
    (V : Finset α) (w : Finset α → ℝ) (hw : ∀ e, 0 ≤ w e) (ζ : ℂ) (h0 : MPoly V w ζ = 0) :
    ζ.im = 0 ∧ ζ.re < 0 := by
  have hne0 : ζ ≠ 0 := by
    intro hζ0
    rw [hζ0] at h0
    have h1 : MPoly V w 0 = 1 := by
      unfold MPoly
      rw [Finset.sum_eq_single ∅]
      · simp
      · intro M _ hMne
        have hpos : 0 < M.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hMne)
        rw [zero_pow (Nat.ne_of_gt hpos), mul_zero]
      · intro hnot
        exact absurd (mem_matchingsOn.mpr ⟨by simp, by simp⟩) hnot
    rw [h1] at h0
    exact one_ne_zero h0
  obtain ⟨z, hz2⟩ := exists_complex_sq (-ζ⁻¹)
  have hz_ne : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz2
    simp at hz2
    exact hne0 hz2
  have hneg : -z⁻¹ ^ 2 = ζ := by
    have h1 : z ^ 2 = -ζ⁻¹ := hz2
    have h2 : z⁻¹ ^ 2 = (-ζ⁻¹)⁻¹ := by rw [inv_pow, h1]
    rw [h2, inv_neg, inv_inv, neg_neg]
  have hmu0 : muPoly V w z = 0 := by
    rw [muPoly_eq_MPoly V w hz_ne, hneg, h0, mul_zero]
  have hzim : z.im = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpos : 0 < (starRingEnd ℂ z).im := by simp [hlt]
      have hconj := (heilmann_lieb_upper w hw V.card V rfl (starRingEnd ℂ z) hpos).1
      rw [muPoly_conj, hmu0, map_zero] at hconj
      exact hconj rfl
    · exact (heilmann_lieb_upper w hw V.card V rfl z hgt).1 hmu0
  have hz_eq : z = (z.re : ℂ) := Complex.ext rfl (by simp [hzim])
  have hzre_ne : z.re ≠ 0 := fun h => hz_ne (by rw [hz_eq, h]; simp)
  have hζ_eq : ζ = (-(1 / z.re ^ 2) : ℝ) := by
    rw [← hneg, hz_eq]
    apply Complex.ext <;> simp [div_eq_mul_inv, inv_pow]
  rw [hζ_eq]
  refine ⟨Complex.ofReal_im _, ?_⟩
  simp only [Complex.ofReal_re]
  have hsq : 0 < z.re ^ 2 := sq_pos_of_ne_zero hzre_ne
  linarith [div_pos one_pos hsq]

private lemma ZPoly_nonneg_at_one {α : Type*} [DecidableEq α]
    (V : Finset α) (F₂ H : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ)
    (hvw : ∀ v ∈ V, 0 < vw v) (hew : ∀ e, 0 ≤ ew e) :
    0 ≤ (ZPoly V F₂ H vw ew 1).re := by
  unfold ZPoly
  rw [Complex.re_sum]
  refine Finset.sum_nonneg (fun M _ => ?_)
  have hre : (((∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * (1 : ℂ) ^ M.card).re =
      (∏ v ∈ V \ M.biUnion id, vw v) * (∏ e ∈ M, ew e) := by
    rw [one_pow, mul_one, ← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hre]
  exact mul_nonneg (Finset.prod_nonneg (fun v hv => le_of_lt (hvw v (Finset.mem_sdiff.mp hv).1)))
    (Finset.prod_nonneg (fun e _ => hew e))

private lemma exists_pos_matching_of_ZPoly_pos {α : Type*} [DecidableEq α]
    (V : Finset α) (F₂ H : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ)
    (hvw : ∀ v ∈ V, 0 < vw v) (hew : ∀ e, 0 ≤ ew e) (hpos : 0 < (ZPoly V F₂ H vw ew 1).re) :
    ∃ M, IsMatching V M ∧ F₂ ⊆ M ∧ (∀ R ∈ H, ∃ e ∈ M, e ⊆ R) ∧
      0 < (∏ v ∈ V \ M.biUnion id, vw v) * (∏ e ∈ M, ew e) := by
  unfold ZPoly at hpos
  rw [Complex.re_sum] at hpos
  have hpos_sum : ∑ _M ∈ (V.powerset.filter (fun e => e.card = 2)).powerset.filter
      (fun M => IsMatching V M ∧ F₂ ⊆ M ∧ ∀ R ∈ H, ∃ e ∈ M, e ⊆ R), (0 : ℝ) <
      ∑ M ∈ (V.powerset.filter (fun e => e.card = 2)).powerset.filter
      (fun M => IsMatching V M ∧ F₂ ⊆ M ∧ ∀ R ∈ H, ∃ e ∈ M, e ⊆ R),
        (((∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * (1 : ℂ) ^ M.card).re := by
    simpa only [Finset.sum_const_zero] using hpos
  obtain ⟨M, hM, hMp⟩ := Finset.exists_lt_of_sum_lt hpos_sum
  have hre : (((∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * (1 : ℂ) ^ M.card).re =
      (∏ v ∈ V \ M.biUnion id, vw v) * (∏ e ∈ M, ew e) := by
    rw [one_pow, mul_one, ← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hre] at hMp
  rw [Finset.mem_filter] at hM
  exact ⟨M, hM.2.1, hM.2.2.1, hM.2.2.2, hMp⟩

private lemma exists_comp_of_linear_hypergraph {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ v : α, (H.filter (fun R => v ∈ R)).card ≤ 2)
    (hlin : ∀ R₁ ∈ H, ∀ R₂ ∈ H, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1)
    (hne : H.Nonempty) :
    ∃ C ⊆ H, C.Nonempty ∧
      (∀ R₁ ∈ C, ∀ R₂ ∈ H \ C, Disjoint R₁ R₂) ∧
      (C.biUnion id).card ≤ 2 * C.card + 1 := by
  obtain ⟨R₀, hR₀⟩ := hne
  let step : Finset (Finset α) → Finset (Finset α) := fun S =>
    S ∪ H.filter (fun R => ∃ T ∈ S, ¬ Disjoint R T)
  let C := step^[H.card] {R₀}
  have hstep_sub : ∀ S ⊆ H, S ⊆ step S ∧ step S ⊆ H := by
    intro S hS
    refine ⟨Finset.subset_union_left, Finset.union_subset hS (Finset.filter_subset _ _)⟩
  have hiter_sub : ∀ k, {R₀} ⊆ step^[k] {R₀} ∧ step^[k] {R₀} ⊆ H := by
    intro k
    induction k with
    | zero => exact ⟨subset_refl _, Finset.singleton_subset_iff.mpr hR₀⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1.trans (hstep_sub _ ih.2).1, (hstep_sub _ ih.2).2⟩
  have hfixed : step C = C := by
    by_contra hne_step
    have hlt_all : ∀ k ≤ H.card, step^[k] {R₀} ⊂ step^[k + 1] {R₀} := by
      intro k hk
      by_contra hnot
      have heq : step (step^[k] {R₀}) = step^[k] {R₀} := by
        rw [Function.iterate_succ_apply'] at hnot
        have hsub := (hstep_sub _ (hiter_sub k).2).1
        exact (Finset.eq_of_subset_of_card_le hsub (Nat.le_of_not_lt (fun hlt =>
          hnot (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => by rw [← h] at hlt; exact lt_irrefl _ hlt⟩)))).symm
      have hconst : ∀ m, step^[k + m] {R₀} = step^[k] {R₀} := by
        intro m
        induction m with
        | zero => simp
        | succ m ihm =>
          rw [← Nat.add_assoc, Function.iterate_succ_apply', ihm, heq]
      have hC_eq : C = step^[k] {R₀} := by
        have := hconst (H.card - k)
        rwa [Nat.add_sub_cancel' hk] at this
      exact hne_step (by rw [hC_eq, heq])
    have hcard_ge : ∀ k ≤ H.card + 1, k + 1 ≤ (step^[k] {R₀}).card := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := Finset.card_lt_card (hlt_all k (by omega))
        omega
    have hbig := hcard_ge (H.card + 1) (le_refl _)
    have hle := Finset.card_le_card (hiter_sub (H.card + 1)).2
    omega
  have hC_sub : C ⊆ H := (hiter_sub H.card).2
  have hC_ne : C.Nonempty := ⟨R₀, (hiter_sub H.card).1 (Finset.mem_singleton_self _)⟩
  have hC_closed : ∀ R₁ ∈ C, ∀ R₂ ∈ H \ C, Disjoint R₁ R₂ := by
    intro R₁ hR₁ R₂ hR₂
    by_contra hnd
    have hR₂_mem : R₂ ∈ step C := Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hR₂).1, R₁, hR₁, fun hd => hnd hd.symm⟩)
    rw [hfixed] at hR₂_mem
    exact (Finset.mem_sdiff.mp hR₂).2 hR₂_mem
  have hbound : ∀ k, (step^[k] {R₀} |>.biUnion id).card ≤ 2 * (step^[k] {R₀}).card + 1 := by
    intro k
    induction k with
    | zero =>
      simp only [Function.iterate_zero_apply, Finset.card_singleton]
      rw [Finset.singleton_biUnion, id_eq, hH3 R₀ hR₀]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      set S := step^[k] {R₀}
      set D := (H.filter (fun R => ∃ T ∈ S, ¬ Disjoint R T)) \ S
      have hstep_eq : step S = S ∪ D := by
        ext R; simp only [step, D, Finset.mem_union, Finset.mem_sdiff]; tauto
      have hdisj_SD : Disjoint S D := Finset.disjoint_sdiff
      have hgen : ∀ (A : Finset (Finset α)), A ⊆ D →
          ((S ∪ A).biUnion id).card ≤ 2 * (S ∪ A).card + 1 := by
        intro A
        induction A using Finset.induction_on with
        | empty => intro _; simpa using ih
        | insert R A hRA ihA =>
          intro hsub
          have hAsub : A ⊆ D := (Finset.subset_insert R A).trans hsub
          have hRD : R ∈ D := hsub (Finset.mem_insert_self R A)
          have hRH : R ∈ H := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hRD).1).1
          have hRnotS : R ∉ S := (Finset.mem_sdiff.mp hRD).2
          have hRnotSA : R ∉ S ∪ A := fun h => by
            rcases Finset.mem_union.mp h with h1 | h2
            · exact hRnotS h1
            · exact hRA h2
          obtain ⟨T, hTS, hnd⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hRD).1).2
          rw [Finset.not_disjoint_iff] at hnd
          rcases hnd with ⟨x, hxR, hxT⟩
          have hx_in : x ∈ (S ∪ A).biUnion id :=
            Finset.mem_biUnion.mpr ⟨T, Finset.mem_union_left _ hTS, hxT⟩
          have hcard_u : ((S ∪ insert R A).biUnion id).card ≤ ((S ∪ A).biUnion id).card + 2 := by
            have heq : (S ∪ insert R A).biUnion id = (S ∪ A).biUnion id ∪ R := by
              ext y
              simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_insert, id_eq]
              constructor
              · rintro ⟨T, hT | rfl | hT, hyT⟩
                · left; exact ⟨T, Or.inl hT, hyT⟩
                · right; exact hyT
                · left; exact ⟨T, Or.inr hT, hyT⟩
              · rintro (⟨T, hT | hT, hyT⟩ | hyR)
                · exact ⟨T, Or.inl hT, hyT⟩
                · exact ⟨T, Or.inr (Or.inr hT), hyT⟩
                · exact ⟨R, Or.inr (Or.inl rfl), hyR⟩
            rw [heq]
            have h1 := Finset.card_union_add_card_inter ((S ∪ A).biUnion id) R
            have h2 : 1 ≤ (((S ∪ A).biUnion id) ∩ R).card :=
              Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hx_in, hxR⟩⟩
            have h3 : R.card = 3 := hH3 R hRH
            omega
          have hcard_SA : (S ∪ insert R A).card = (S ∪ A).card + 1 := by
            rw [Finset.union_insert, Finset.card_insert_of_notMem hRnotSA]
          have hihA := ihA hAsub
          omega
      rw [hstep_eq]
      exact hgen D (subset_refl D)
  exact ⟨C, hC_sub, hC_ne, hC_closed, hbound H.card⟩

private def ZPolyStepGoal {α : Type*} [DecidableEq α]
    (V : Finset α) (F₂ H : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ) : Prop :=
  ∃ (dk : ℕ) (c₀ : ℝ) (V' : Finset α) (F₂' H' : Finset (Finset α)) (vw' : α → ℝ) (ew' : Finset α → ℝ),
    0 < c₀ ∧ V'.card < V.card ∧
    (∀ e ∈ F₂', e.card = 2 ∧ e ⊆ V') ∧
    (∀ R ∈ H', R.card = 3 ∧ R ⊆ V') ∧
    (∀ v ∈ V', (H'.filter (fun R => v ∈ R)).card ≤ 2) ∧
    (∀ v ∈ V', 0 < vw' v) ∧
    (∀ e, 0 ≤ ew' e) ∧
    0 < (ZPoly V' F₂' H' vw' ew' 1).re ∧
    ∀ z : ℂ, ZPoly V F₂ H vw ew z = (c₀ : ℂ) * z ^ dk * ZPoly V' F₂' H' vw' ew' z

private lemma reduce_ZPoly_step_F2 {α : Type*} [DecidableEq α]
    (V : Finset α) (F₂ H : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ)
    (hF₂ : ∀ e ∈ F₂, e.card = 2 ∧ e ⊆ V)
    (hH : ∀ R ∈ H, R.card = 3 ∧ R ⊆ V)
    (hdeg : ∀ v ∈ V, (H.filter (fun R => v ∈ R)).card ≤ 2)
    (hvw : ∀ v ∈ V, 0 < vw v) (hew : ∀ e, 0 ≤ ew e)
    (hpos : 0 < (ZPoly V F₂ H vw ew 1).re) (hF₂_ne : F₂.Nonempty) :
    ZPolyStepGoal V F₂ H vw ew := by
  obtain ⟨e₀, he₀⟩ := hF₂_ne
  obtain ⟨Mpos, hMp_m, hMp_F₂, _, hMp_pos⟩ := exists_pos_matching_of_ZPoly_pos V F₂ H vw ew hvw hew hpos
  have he₀_pos : 0 < ew e₀ := by
    by_contra hle
    have heq0 : ew e₀ = 0 := le_antisymm (not_lt.mp hle) (hew e₀)
    have hprod0 : ∏ e ∈ Mpos, ew e = 0 := Finset.prod_eq_zero (hMp_F₂ he₀) heq0
    rw [hprod0, mul_zero] at hMp_pos
    exact lt_irrefl 0 hMp_pos
  let V' := V \ e₀
  let F₂' := (F₂.erase e₀) ∪ (H.filter (fun R => (R ∩ e₀).card = 1)).image (fun R => R \ e₀)
  let H' := H.filter (fun R => Disjoint R e₀)
  have hV'_lt : V'.card < V.card := by
    have h1 : V'.card + e₀.card = V.card := Finset.card_sdiff_add_card_eq_card (hF₂ e₀ he₀).2
    have h2 : e₀.card = 2 := (hF₂ e₀ he₀).1
    omega
  have hF₂'_ok : ∀ e ∈ F₂', e.card = 2 ∧ e ⊆ V' := by
    intro e he
    rcases Finset.mem_union.mp he with h1 | h2
    · have heF := Finset.mem_of_mem_erase h1
      have hdisj : Disjoint e e₀ := hMp_m.2 e (hMp_F₂ heF) e₀ (hMp_F₂ he₀) (Finset.ne_of_mem_erase h1)
      exact ⟨(hF₂ e heF).1, Finset.subset_sdiff.mpr ⟨(hF₂ e heF).2, hdisj⟩⟩
    · rcases Finset.mem_image.mp h2 with ⟨R, hR, rfl⟩
      rw [Finset.mem_filter] at hR
      have hc1 : (R \ e₀).card + (R ∩ e₀).card = R.card := Finset.card_sdiff_add_card_inter R e₀
      have hc3 : R.card = 3 := (hH R hR.1).1
      exact ⟨by omega, Finset.sdiff_subset_sdiff (hH R hR.1).2 (subset_refl _)⟩
  have hH'_ok : ∀ R ∈ H', R.card = 3 ∧ R ⊆ V' := by
    intro R hR
    rw [Finset.mem_filter] at hR
    exact ⟨(hH R hR.1).1, Finset.subset_sdiff.mpr ⟨(hH R hR.1).2, hR.2⟩⟩
  have hdeg' : ∀ v ∈ V', (H'.filter (fun R => v ∈ R)).card ≤ 2 := by
    intro v hv
    exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))
      (hdeg v (Finset.mem_sdiff.mp hv).1)
  have hZ_eq : ∀ z : ℂ, ZPoly V F₂ H vw ew z = (ew e₀ : ℂ) * z * ZPoly V' F₂' H' vw ew z := by
    intro z
    unfold ZPoly
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun M _ => M.erase e₀) ?_ ?_ ?_ ?_
    · intro M hM
      rw [Finset.mem_filter] at hM ⊢
      have hMm := hM.2.1
      have he₀M : e₀ ∈ M := hM.2.2.1 he₀
      have hM' : IsMatching V' (M.erase e₀) := ⟨fun e he =>
        ⟨(hMm.1 e (Finset.mem_of_mem_erase he)).1,
          Finset.subset_sdiff.mpr ⟨(hMm.1 e (Finset.mem_of_mem_erase he)).2,
            hMm.2 e (Finset.mem_of_mem_erase he) e₀ he₀M (Finset.ne_of_mem_erase he)⟩⟩,
        fun e₁ h1 e₂ h2 hne => hMm.2 e₁ (Finset.mem_of_mem_erase h1) e₂ (Finset.mem_of_mem_erase h2) hne⟩
      refine ⟨Finset.mem_powerset.mpr (fun e he => Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (hM'.1 e he).2, (hM'.1 e he).1⟩), hM', ?_, ?_⟩
      · intro e he
        rcases Finset.mem_union.mp he with h1 | h2
        · exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase h1, hM.2.2.1 (Finset.mem_of_mem_erase h1)⟩
        · rcases Finset.mem_image.mp h2 with ⟨R, hR, rfl⟩
          rw [Finset.mem_filter] at hR
          obtain ⟨e', he'M, he'R⟩ := hM.2.2.2 R hR.1
          have hne : e' ≠ e₀ := by
            intro h
            rw [h] at he'R
            have : (R ∩ e₀).card = 2 := by
              rw [Finset.inter_eq_right.mpr he'R]; exact (hF₂ e₀ he₀).1
            omega
          have hdisj : Disjoint e' e₀ := hMm.2 e' he'M e₀ he₀M hne
          have hsub : e' ⊆ R \ e₀ := Finset.subset_sdiff.mpr ⟨he'R, hdisj⟩
          have hc : (R \ e₀).card = 2 := by
            have := Finset.card_sdiff_add_card_inter R e₀
            have := (hH R hR.1).1; omega
          have heq : e' = R \ e₀ := Finset.eq_of_subset_of_card_le hsub (by rw [(hMm.1 e' he'M).1, hc])
          exact Finset.mem_erase.mpr ⟨heq ▸ hne, heq ▸ he'M⟩
      · intro R hR
        rw [Finset.mem_filter] at hR
        obtain ⟨e, heM, heR⟩ := hM.2.2.2 R hR.1
        have hne : e ≠ e₀ := by
          intro h
          rw [h] at heR
          obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(hF₂ e₀ he₀).1]; decide)
          exact Finset.disjoint_left.mp hR.2 (heR hx) hx
        exact ⟨e, Finset.mem_erase.mpr ⟨hne, heM⟩, heR⟩
    · intro M₁ hM₁ M₂ hM₂ heq
      have h1 : e₀ ∈ M₁ := (Finset.mem_filter.mp hM₁).2.2.1 he₀
      have h2 : e₀ ∈ M₂ := (Finset.mem_filter.mp hM₂).2.2.1 he₀
      rw [← Finset.insert_erase h1, ← Finset.insert_erase h2, heq]
    · intro M' hM'
      rw [Finset.mem_filter] at hM'
      have hM'm := hM'.2.1
      have hnot : e₀ ∉ M' := fun h => by
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(hF₂ e₀ he₀).1]; decide)
        exact (Finset.mem_sdiff.mp ((hM'm.1 e₀ h).2 hx)).2 hx
      have hM_ins : IsMatching V (insert e₀ M') := by
        refine ⟨fun e he => ?_, fun e₁ h1 e₂ h2 hne => ?_⟩
        · rcases Finset.mem_insert.mp he with rfl | h
          · exact hF₂ e he₀
          · exact ⟨(hM'm.1 e h).1, (hM'm.1 e h).2.trans Finset.sdiff_subset⟩
        · rcases Finset.mem_insert.mp h1 with rfl | h1' <;> rcases Finset.mem_insert.mp h2 with rfl | h2'
          · exact absurd rfl hne
          · exact (Finset.subset_sdiff.mp (hM'm.1 e₂ h2').2).2.symm
          · exact (Finset.subset_sdiff.mp (hM'm.1 e₁ h1').2).2
          · exact hM'm.2 e₁ h1' e₂ h2' hne
      refine ⟨insert e₀ M', Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun e he =>
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hM_ins.1 e he).2, (hM_ins.1 e he).1⟩),
        hM_ins, ?_, ?_⟩, Finset.erase_insert hnot⟩
      · intro e he
        by_cases h : e = e₀
        · exact h ▸ Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hM'.2.2.1 (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, he⟩)))
      · intro R hR
        have hle : (R ∩ e₀).card ≤ 2 := le_trans (Finset.card_le_card Finset.inter_subset_right) (le_of_eq (hF₂ e₀ he₀).1)
        by_cases hc0 : (R ∩ e₀).card = 0
        · have hd : Disjoint R e₀ := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hc0)
          obtain ⟨e, heM', heR⟩ := hM'.2.2.2 R (Finset.mem_filter.mpr ⟨hR, hd⟩)
          exact ⟨e, Finset.mem_insert_of_mem heM', heR⟩
        · by_cases hc1 : (R ∩ e₀).card = 1
          · refine ⟨R \ e₀, Finset.mem_insert_of_mem (hM'.2.2.1 (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨R, Finset.mem_filter.mpr ⟨hR, hc1⟩, rfl⟩))), Finset.sdiff_subset⟩
          · have hc2 : (R ∩ e₀).card = 2 := by omega
            have hsub : e₀ ⊆ R := by
              have heq : R ∩ e₀ = e₀ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [(hF₂ e₀ he₀).1, hc2])
              exact heq ▸ Finset.inter_subset_left
            exact ⟨e₀, Finset.mem_insert_self _ _, hsub⟩
    · intro M hM
      have he₀M : e₀ ∈ M := (Finset.mem_filter.mp hM).2.2.1 he₀
      have hsdiff : V \ M.biUnion id = V' \ (M.erase e₀).biUnion id := by
        ext x
        simp only [V', Finset.mem_sdiff, Finset.mem_biUnion, id_eq, Finset.mem_erase]
        constructor
        · rintro ⟨hxV, hno⟩
          exact ⟨⟨hxV, fun hxe => hno ⟨e₀, he₀M, hxe⟩⟩, fun ⟨e, ⟨_, heM⟩, hxe⟩ => hno ⟨e, heM, hxe⟩⟩
        · rintro ⟨⟨hxV, hxne⟩, hno⟩
          refine ⟨hxV, fun ⟨e, heM, hxe⟩ => ?_⟩
          by_cases h : e = e₀
          · exact hxne (h ▸ hxe)
          · exact hno ⟨e, ⟨h, heM⟩, hxe⟩
      have hprod : ∏ e ∈ M, (ew e : ℂ) = (ew e₀ : ℂ) * ∏ e ∈ M.erase e₀, (ew e : ℂ) :=
        (Finset.mul_prod_erase M (fun e => (ew e : ℂ)) he₀M).symm
      have hcard : M.card = (M.erase e₀).card + 1 := (Finset.card_erase_add_one he₀M).symm
      rw [hsdiff, hprod, hcard, pow_succ]
      ring
  have hpos' : 0 < (ZPoly V' F₂' H' vw ew 1).re := by
    have h1 : (ZPoly V F₂ H vw ew 1).re = ew e₀ * (ZPoly V' F₂' H' vw ew 1).re := by
      rw [hZ_eq 1, mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [h1] at hpos
    exact pos_of_mul_pos_right hpos (le_of_lt he₀_pos)
  exact ⟨1, ew e₀, V', F₂', H', vw, ew, he₀_pos, hV'_lt, hF₂'_ok, hH'_ok, hdeg',
    (fun v hv => hvw v (Finset.mem_sdiff.mp hv).1), hew, hpos', fun z => by simpa [pow_one] using hZ_eq z⟩

private lemma core2_sum_pair {α : Type*} [DecidableEq α]
    (V : Finset α) (H : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ)
    (R₁ R₂ c : Finset α) (a b u v : α)
    (hc_eq : c = {a, b}) (hc_sub : c ⊆ V)
    (hR₁_eq : R₁ = {a, b, u}) (hR₂_eq : R₂ = {a, b, v})
    (hab : a ≠ b) (huv : u ≠ v)
    (ha_ne_u : a ≠ u) (hb_ne_u : b ≠ u) (ha_ne_v : a ≠ v) (hb_ne_v : b ≠ v)
    (ha_c : a ∈ c) (hb_c : b ∈ c)
    (hu_mem_V' : u ∈ V \ c) (hv_mem_V' : v ∈ V \ c)
    (hno_ab : ∀ R ∈ (H.erase R₁).erase R₂, Disjoint R c)
    (z : ℂ) (p₁ p₂ : Finset α)
    (hp : p₁ = {a, u} ∧ p₂ = {b, v} ∨ p₁ = {a, v} ∧ p₂ = {b, u}) :
    ∑ M ∈ ((V.powerset.filter (fun e => e.card = 2)).powerset.filter
      (fun M => IsMatching V M ∧ ∅ ⊆ M ∧ ∀ R ∈ H, ∃ e ∈ M, e ⊆ R)).filter
      (fun M => p₁ ∈ M ∧ p₂ ∈ M),
      ((∏ x ∈ V \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card =
    (ew p₁ : ℂ) * (ew p₂ : ℂ) * z ^ 2 *
      ∑ M' ∈ (matchingsOn ((V \ c) \ {u, v})).filter (fun M' => ∀ R ∈ (H.erase R₁).erase R₂, ∃ e ∈ M', e ⊆ R),
        ((∏ x ∈ ((V \ c) \ {u, v}) \ M'.biUnion id, (vw x : ℂ)) * (∏ e ∈ M', (ew e : ℂ))) * z ^ M'.card := by
  let V' := V \ c
  let H' := (H.erase R₁).erase R₂
  have hp_union : p₁ ∪ p₂ = c ∪ {u, v} := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [hc_eq]; ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hp_disj : Disjoint p₁ p₂ := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      rcases hx1 with rfl | rfl <;> rcases hx2 with h1 | h2
      · exact hab h1
      · exact ha_ne_v h2
      · exact hb_ne_u h1.symm
      · exact huv h2
    · rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      rcases hx1 with rfl | rfl <;> rcases hx2 with h1 | h2
      · exact hab h1
      · exact ha_ne_u h2
      · exact hb_ne_v h1.symm
      · exact huv.symm h2
  have hp_ne : p₁ ≠ p₂ := fun h => by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have ha1 : a ∈ ({a, u} : Finset α) := by simp
      exact Finset.disjoint_left.mp hp_disj ha1 (h ▸ ha1)
    · have ha1 : a ∈ ({a, v} : Finset α) := by simp
      exact Finset.disjoint_left.mp hp_disj ha1 (h ▸ ha1)
  have hp_card : p₁.card = 2 ∧ p₂.card = 2 := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Finset.card_pair ha_ne_u, Finset.card_pair hb_ne_v⟩
    · exact ⟨Finset.card_pair ha_ne_v, Finset.card_pair hb_ne_u⟩
  have hp_subV : p₁ ⊆ V ∧ p₂ ⊆ V := by
    have hcu : c ∪ {u, v} ⊆ V := Finset.union_subset hc_sub (by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (Finset.mem_sdiff.mp hu_mem_V').1
      · rw [Finset.mem_singleton.mp hx]; exact (Finset.mem_sdiff.mp hv_mem_V').1)
    rw [← hp_union] at hcu
    exact ⟨Finset.subset_union_left.trans hcu, Finset.subset_union_right.trans hcu⟩
  have hp_hit : (p₁ ⊆ R₁ ∧ p₂ ⊆ R₂) ∨ (p₁ ⊆ R₂ ∧ p₂ ⊆ R₁) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; rw [hR₁_eq, hR₂_eq]
      exact ⟨by simp [Finset.insert_subset_iff], by simp [Finset.insert_subset_iff]⟩
    · right; rw [hR₁_eq, hR₂_eq]
      exact ⟨by simp [Finset.insert_subset_iff], by simp [Finset.insert_subset_iff]⟩
  have ha1 : a ∈ p₁ := by rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hb2 : b ∈ p₂ := by rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun M _ => (M.erase p₁).erase p₂) ?_ ?_ ?_ ?_
  · intro M hM
    have hM_all := (Finset.mem_filter.mp hM).1
    have hp1M := (Finset.mem_filter.mp hM).2.1
    have hp2M := (Finset.mem_filter.mp hM).2.2
    have hMm := (Finset.mem_filter.mp hM_all).2.1
    have hM' : IsMatching (V' \ {u, v}) ((M.erase p₁).erase p₂) := ⟨fun e he => by
      have heM := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he)
      have hne2 := Finset.ne_of_mem_erase he
      have hne1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he)
      have hd1 := hMm.2 e heM p₁ hp1M hne1
      have hd2 := hMm.2 e heM p₂ hp2M hne2
      refine ⟨(hMm.1 e heM).1, fun x hx => ?_⟩
      have hnotu : x ∉ p₁ ∪ p₂ := fun h => by
        rcases Finset.mem_union.mp h with h1 | h2
        · exact Finset.disjoint_left.mp hd1 hx h1
        · exact Finset.disjoint_left.mp hd2 hx h2
      rw [hp_union, Finset.mem_union] at hnotu
      push_neg at hnotu
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨(hMm.1 e heM).2 hx, hnotu.1⟩, hnotu.2⟩,
      fun e₁ h1 e₂ h2 hne => hMm.2 e₁ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h1))
        e₂ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h2)) hne⟩
    refine Finset.mem_filter.mpr ⟨mem_matchingsOn.mpr hM', ?_⟩
    intro R hR
    obtain ⟨e, heM, heR⟩ := (Finset.mem_filter.mp hM_all).2.2.2 R
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hR))
    have hne1 : e ≠ p₁ := fun h => by
      have : a ∈ R := heR (h ▸ ha1)
      exact Finset.disjoint_left.mp (hno_ab R hR) this ha_c
    have hne2 : e ≠ p₂ := fun h => by
      have : b ∈ R := heR (h ▸ hb2)
      exact Finset.disjoint_left.mp (hno_ab R hR) this hb_c
    exact ⟨e, Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, heM⟩⟩, heR⟩
  · intro M₁ h1 M₂ h2 heq
    have h11 := (Finset.mem_filter.mp h1).2.1
    have h12 := (Finset.mem_filter.mp h1).2.2
    have h21 := (Finset.mem_filter.mp h2).2.1
    have h22 := (Finset.mem_filter.mp h2).2.2
    have h12' : p₂ ∈ M₁.erase p₁ := Finset.mem_erase.mpr ⟨hp_ne.symm, h12⟩
    have h22' : p₂ ∈ M₂.erase p₁ := Finset.mem_erase.mpr ⟨hp_ne.symm, h22⟩
    have heq' : M₁.erase p₁ = M₂.erase p₁ := by
      rw [← Finset.insert_erase h12', ← Finset.insert_erase h22', heq]
    rw [← Finset.insert_erase h11, ← Finset.insert_erase h21, heq']
  · intro M' hM'
    have hM'm := mem_matchingsOn.mp (Finset.mem_filter.mp hM').1
    have hdisj_e : ∀ e ∈ M', Disjoint e p₁ ∧ Disjoint e p₂ := by
      intro e he
      have hsub : e ⊆ V' \ {u, v} := (hM'm.1 e he).2
      have hd : Disjoint e (c ∪ {u, v}) := by
        rw [Finset.disjoint_left]
        intro x hxe hxcu
        have hx := hsub hxe
        rw [Finset.mem_sdiff, Finset.mem_sdiff] at hx
        rcases Finset.mem_union.mp hxcu with hxc | hxuv
        · exact hx.1.2 hxc
        · exact hx.2 hxuv
      rw [← hp_union, Finset.disjoint_union_right] at hd
      exact hd
    have hnot1 : p₁ ∉ M' := fun h => by
      have hd := (hdisj_e p₁ h).1
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < p₁.card)
      exact Finset.disjoint_left.mp hd hx hx
    have hnot2 : p₂ ∉ M' := fun h => by
      have hd := (hdisj_e p₂ h).2
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < p₂.card)
      exact Finset.disjoint_left.mp hd hx hx
    have hM_ins : IsMatching V (insert p₁ (insert p₂ M')) := ⟨fun e he => by
      rcases Finset.mem_insert.mp he with rfl | he
      · exact ⟨hp_card.1, hp_subV.1⟩
      · rcases Finset.mem_insert.mp he with rfl | he
        · exact ⟨hp_card.2, hp_subV.2⟩
        · exact ⟨(hM'm.1 e he).1, (hM'm.1 e he).2.trans (Finset.sdiff_subset.trans Finset.sdiff_subset)⟩,
      fun e₁ h1 e₂ h2 hne => by
        rcases Finset.mem_insert.mp h1 with rfl | h1a <;> rcases Finset.mem_insert.mp h2 with rfl | h2a
        · exact absurd rfl hne
        · rcases Finset.mem_insert.mp h2a with rfl | h2'
          · exact hp_disj
          · exact (hdisj_e e₂ h2').1.symm
        · rcases Finset.mem_insert.mp h1a with rfl | h1'
          · exact hp_disj.symm
          · exact (hdisj_e e₁ h1').1
        · rcases Finset.mem_insert.mp h1a with rfl | h1' <;> rcases Finset.mem_insert.mp h2a with rfl | h2'
          · exact absurd rfl hne
          · exact (hdisj_e e₂ h2').2.symm
          · exact (hdisj_e e₁ h1').2
          · exact hM'm.2 e₁ h1' e₂ h2' hne⟩
    refine ⟨insert p₁ (insert p₂ M'), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hM_ins.1 e he).2, (hM_ins.1 e he).1⟩),
      hM_ins, Finset.empty_subset _, ?_⟩, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩, ?_⟩
    · intro R hR
      by_cases h1 : R = R₁
      · rcases hp_hit with ⟨h11, _⟩ | ⟨_, h21⟩
        · exact ⟨p₁, Finset.mem_insert_self _ _, h1 ▸ h11⟩
        · exact ⟨p₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h1 ▸ h21⟩
      · by_cases h2 : R = R₂
        · rcases hp_hit with ⟨_, h22⟩ | ⟨h12, _⟩
          · exact ⟨p₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h2 ▸ h22⟩
          · exact ⟨p₁, Finset.mem_insert_self _ _, h2 ▸ h12⟩
        · obtain ⟨e, heM', heR⟩ := (Finset.mem_filter.mp hM').2 R
            (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hR⟩⟩)
          exact ⟨e, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem heM'), heR⟩
    · have hnot1' : p₁ ∉ insert p₂ M' := fun h => by
        rcases Finset.mem_insert.mp h with h1 | h2
        · exact hp_ne h1
        · exact hnot1 h2
      rw [Finset.erase_insert hnot1', Finset.erase_insert hnot2]
  · intro M hM
    have hp1M := (Finset.mem_filter.mp hM).2.1
    have hp2M := (Finset.mem_filter.mp hM).2.2
    have hp2M' : p₂ ∈ M.erase p₁ := Finset.mem_erase.mpr ⟨hp_ne.symm, hp2M⟩
    have hsdiff : V \ M.biUnion id = (V' \ {u, v}) \ ((M.erase p₁).erase p₂).biUnion id := by
      ext x
      simp only [V', Finset.mem_sdiff, Finset.mem_biUnion, id_eq, Finset.mem_erase]
      have hmem_p : (x ∈ c ∨ x ∈ ({u, v} : Finset α)) ↔ (x ∈ p₁ ∨ x ∈ p₂) := by
        rw [← Finset.mem_union, ← hp_union, Finset.mem_union]
      constructor
      · rintro ⟨hxV, hno⟩
        have hnp : ¬ (x ∈ p₁ ∨ x ∈ p₂) := fun h => by
          rcases h with h1 | h2
          · exact hno ⟨p₁, hp1M, h1⟩
          · exact hno ⟨p₂, hp2M, h2⟩
        rw [← hmem_p] at hnp; push_neg at hnp
        exact ⟨⟨⟨hxV, hnp.1⟩, hnp.2⟩, fun ⟨e, ⟨_, _, heM⟩, hxe⟩ => hno ⟨e, heM, hxe⟩⟩
      · rintro ⟨⟨⟨hxV, hxnc⟩, hxnuv⟩, hno⟩
        refine ⟨hxV, fun ⟨e, heM, hxe⟩ => ?_⟩
        by_cases h1 : e = p₁
        · have hcv : x ∈ c ∨ x ∈ ({u, v} : Finset α) := hmem_p.mpr (Or.inl (h1 ▸ hxe))
          rcases hcv with h | h
          · exact hxnc h
          · exact hxnuv h
        · by_cases h2 : e = p₂
          · have hcv : x ∈ c ∨ x ∈ ({u, v} : Finset α) := hmem_p.mpr (Or.inr (h2 ▸ hxe))
            rcases hcv with h | h
            · exact hxnc h
            · exact hxnuv h
          · exact hno ⟨e, ⟨h2, h1, heM⟩, hxe⟩
    have hprod : ∏ e ∈ M, (ew e : ℂ) =
        (ew p₁ : ℂ) * (ew p₂ : ℂ) * ∏ e ∈ (M.erase p₁).erase p₂, (ew e : ℂ) := by
      rw [← Finset.mul_prod_erase M (fun e => (ew e : ℂ)) hp1M,
          ← Finset.mul_prod_erase (M.erase p₁) (fun e => (ew e : ℂ)) hp2M', mul_assoc]
    have hcard : M.card = ((M.erase p₁).erase p₂).card + 2 := by
      have h1 := Finset.card_erase_add_one hp1M
      have h2 := Finset.card_erase_add_one hp2M'
      omega
    rw [hsdiff, hprod, hcard, pow_add]
    ring

private lemma core2_split_ZPoly {α : Type*} [DecidableEq α]
    (V : Finset α) (H : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ)
    (R₁ R₂ c : Finset α) (a b u v : α)
    (hR₁ : R₁ ∈ H) (hR₂ : R₂ ∈ H)
    (hc_def : c = R₁ ∩ R₂) (hcap2 : c.card = 2)
    (hc_eq : c = {a, b}) (hc_sub : c ⊆ V)
    (huR₁ : u ∈ R₁ ∧ u ∉ c) (hvR₂ : v ∈ R₂ ∧ v ∉ c)
    (hR₁_eq : R₁ = {a, b, u}) (hR₂_eq : R₂ = {a, b, v})
    (hab : a ≠ b) (huv : u ≠ v)
    (ha_ne_u : a ≠ u) (hb_ne_u : b ≠ u) (ha_ne_v : a ≠ v) (hb_ne_v : b ≠ v)
    (ha_c : a ∈ c) (hb_c : b ∈ c)
    (hu_mem_V' : u ∈ V \ c) (hv_mem_V' : v ∈ V \ c)
    (hno_ab : ∀ R ∈ (H.erase R₁).erase R₂, Disjoint R c) (z : ℂ) :
    ZPoly V ∅ H vw ew z =
      (ew c : ℂ) * z * ZPoly (V \ c) ∅ ((H.erase R₁).erase R₂) vw ew z +
      ((ew {a, u} * ew {b, v} + ew {a, v} * ew {b, u} : ℝ) : ℂ) * z ^ 2 *
        ∑ M' ∈ (matchingsOn ((V \ c) \ {u, v})).filter (fun M' => ∀ R ∈ (H.erase R₁).erase R₂, ∃ e ∈ M', e ⊆ R),
          ((∏ x ∈ ((V \ c) \ {u, v}) \ M'.biUnion id, (vw x : ℂ)) * (∏ e ∈ M', (ew e : ℂ))) * z ^ M'.card := by
  let V' := V \ c
  let H' := (H.erase R₁).erase R₂
  unfold ZPoly
  let All := (V.powerset.filter (fun e => e.card = 2)).powerset.filter
    (fun M => IsMatching V M ∧ ∅ ⊆ M ∧ ∀ R ∈ H, ∃ e ∈ M, e ⊆ R)
  let A0 := All.filter (fun M => c ∈ M)
  let A1 := All.filter (fun M => ({a, u} : Finset α) ∈ M ∧ ({b, v} : Finset α) ∈ M)
  let A2 := All.filter (fun M => ({a, v} : Finset α) ∈ M ∧ ({b, u} : Finset α) ∈ M)
  have hAll_eq : All = A0 ∪ (A1 ∪ A2) := by
    ext M
    simp only [Finset.mem_union, A0, A1, A2, Finset.mem_filter]
    constructor
    · intro hM
      have hMm : IsMatching V M := (Finset.mem_filter.mp hM).2.1
      obtain ⟨e₁, he₁M, he₁R₁⟩ := (Finset.mem_filter.mp hM).2.2.2 R₁ hR₁
      obtain ⟨e₂, he₂M, he₂R₂⟩ := (Finset.mem_filter.mp hM).2.2.2 R₂ hR₂
      have hsub1 : e₁ = c ∨ e₁ = {a, u} ∨ e₁ = {b, u} := by
        rw [hR₁_eq] at he₁R₁
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (hMm.1 e₁ he₁M).1
        have hx := he₁R₁ (Finset.mem_insert_self x {y})
        have hy := he₁R₁ (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact absurd rfl hxy
        · left; exact hc_eq.symm
        · right; left; rfl
        · left; rw [Finset.pair_comm, hc_eq]
        · exact absurd rfl hxy
        · right; right; rfl
        · right; left; exact Finset.pair_comm _ _
        · right; right; exact Finset.pair_comm _ _
        · exact absurd rfl hxy
      have hsub2 : e₂ = c ∨ e₂ = {a, v} ∨ e₂ = {b, v} := by
        rw [hR₂_eq] at he₂R₂
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (hMm.1 e₂ he₂M).1
        have hx := he₂R₂ (Finset.mem_insert_self x {y})
        have hy := he₂R₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact absurd rfl hxy
        · left; exact hc_eq.symm
        · right; left; rfl
        · left; rw [Finset.pair_comm, hc_eq]
        · exact absurd rfl hxy
        · right; right; rfl
        · right; left; exact Finset.pair_comm _ _
        · right; right; exact Finset.pair_comm _ _
        · exact absurd rfl hxy
      rcases hsub1 with rfl | rfl | rfl
      · left; exact ⟨hM, he₁M⟩
      · rcases hsub2 with rfl | rfl | rfl
        · left; exact ⟨hM, he₂M⟩
        · exfalso
          have hne_e : ({a, u} : Finset α) ≠ {a, v} := fun h => by
            have : u ∈ ({a, v} : Finset α) := h ▸ by simp
            rcases Finset.mem_insert.mp this with h1 | h2
            · exact ha_ne_u h1.symm
            · exact huv (Finset.mem_singleton.mp h2)
          have h1 : a ∈ ({a, u} : Finset α) := by simp
          have h2 : a ∈ ({a, v} : Finset α) := by simp
          exact Finset.disjoint_left.mp (hMm.2 _ he₁M _ he₂M hne_e) h1 h2
        · right; left; exact ⟨hM, he₁M, he₂M⟩
      · rcases hsub2 with rfl | rfl | rfl
        · left; exact ⟨hM, he₂M⟩
        · right; right; exact ⟨hM, he₂M, he₁M⟩
        · exfalso
          have hne_e : ({b, u} : Finset α) ≠ {b, v} := fun h => by
            have : u ∈ ({b, v} : Finset α) := h ▸ by simp
            rcases Finset.mem_insert.mp this with h1 | h2
            · exact hb_ne_u h1.symm
            · exact huv (Finset.mem_singleton.mp h2)
          have h1 : b ∈ ({b, u} : Finset α) := by simp
          have h2 : b ∈ ({b, v} : Finset α) := by simp
          exact Finset.disjoint_left.mp (hMm.2 _ he₁M _ he₂M hne_e) h1 h2
    · rintro (⟨hM, _⟩ | ⟨hM, _⟩ | ⟨hM, _⟩) <;> exact hM
  have hd0 : Disjoint A0 (A1 ∪ A2) := by
    rw [Finset.disjoint_left]
    intro M h0 h12
    have hMm : IsMatching V M := (Finset.mem_filter.mp (Finset.mem_filter.mp h0).1).2.1
    have hcM : c ∈ M := (Finset.mem_filter.mp h0).2
    rcases Finset.mem_union.mp h12 with h1 | h2
    · have hau : ({a, u} : Finset α) ∈ M := (Finset.mem_filter.mp h1).2.1
      have hne : c ≠ {a, u} := fun h => by
        have : u ∈ c := h ▸ by simp
        exact huR₁.2 this
      exact Finset.disjoint_left.mp (hMm.2 c hcM {a, u} hau hne) ha_c (by simp)
    · have hav : ({a, v} : Finset α) ∈ M := (Finset.mem_filter.mp h2).2.1
      have hne : c ≠ {a, v} := fun h => by
        have : v ∈ c := h ▸ by simp
        exact hvR₂.2 this
      exact Finset.disjoint_left.mp (hMm.2 c hcM {a, v} hav hne) ha_c (by simp)
  have hd12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]
    intro M h1 h2
    have hMm : IsMatching V M := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2.1
    have hau : ({a, u} : Finset α) ∈ M := (Finset.mem_filter.mp h1).2.1
    have hav : ({a, v} : Finset α) ∈ M := (Finset.mem_filter.mp h2).2.1
    have hne : ({a, u} : Finset α) ≠ {a, v} := fun h => by
      have : u ∈ ({a, v} : Finset α) := h ▸ by simp
      rcases Finset.mem_insert.mp this with h1 | h2
      · exact ha_ne_u h1.symm
      · exact huv (Finset.mem_singleton.mp h2)
    have h1 : a ∈ ({a, u} : Finset α) := by simp
    have h2 : a ∈ ({a, v} : Finset α) := by simp
    exact Finset.disjoint_left.mp (hMm.2 _ hau _ hav hne) h1 h2
  change ∑ M ∈ All, _ = _
  rw [hAll_eq, Finset.sum_union hd0, Finset.sum_union hd12]
  have hsum0 : ∑ M ∈ A0, ((∏ x ∈ V \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card =
      (ew c : ℂ) * z * ∑ M' ∈ (V'.powerset.filter (fun e => e.card = 2)).powerset.filter
        (fun M' => IsMatching V' M' ∧ ∅ ⊆ M' ∧ ∀ R ∈ H', ∃ e ∈ M', e ⊆ R),
        ((∏ x ∈ V' \ M'.biUnion id, (vw x : ℂ)) * (∏ e ∈ M', (ew e : ℂ))) * z ^ M'.card := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun M _ => M.erase c) ?_ ?_ ?_ ?_
    · intro M hM
      have hM_all := (Finset.mem_filter.mp hM).1
      have hcM := (Finset.mem_filter.mp hM).2
      have hMm := (Finset.mem_filter.mp hM_all).2.1
      have hM' : IsMatching V' (M.erase c) := ⟨fun e he =>
        ⟨(hMm.1 e (Finset.mem_of_mem_erase he)).1,
          Finset.subset_sdiff.mpr ⟨(hMm.1 e (Finset.mem_of_mem_erase he)).2,
            hMm.2 e (Finset.mem_of_mem_erase he) c hcM (Finset.ne_of_mem_erase he)⟩⟩,
        fun e₁ h1 e₂ h2 hne => hMm.2 e₁ (Finset.mem_of_mem_erase h1) e₂ (Finset.mem_of_mem_erase h2) hne⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun e he => Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (hM'.1 e he).2, (hM'.1 e he).1⟩), hM', Finset.empty_subset _, ?_⟩
      intro R hR
      obtain ⟨e, heM, heR⟩ := (Finset.mem_filter.mp hM_all).2.2.2 R
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hR))
      have hne : e ≠ c := fun h => by
        have haR : a ∈ R := heR (h ▸ ha_c)
        exact Finset.disjoint_left.mp (hno_ab R hR) haR ha_c
      exact ⟨e, Finset.mem_erase.mpr ⟨hne, heM⟩, heR⟩
    · intro M₁ h1 M₂ h2 heq
      rw [← Finset.insert_erase (Finset.mem_filter.mp h1).2,
          ← Finset.insert_erase (Finset.mem_filter.mp h2).2, heq]
    · intro M' hM'
      have hM'm := (Finset.mem_filter.mp hM').2.1
      have hnot : c ∉ M' := fun h =>
        (Finset.mem_sdiff.mp ((hM'm.1 c h).2 ha_c)).2 ha_c
      have hM_ins : IsMatching V (insert c M') := ⟨fun e he => by
        rcases Finset.mem_insert.mp he with rfl | h
        · exact ⟨hcap2, hc_sub⟩
        · exact ⟨(hM'm.1 e h).1, (hM'm.1 e h).2.trans Finset.sdiff_subset⟩,
        fun e₁ h1 e₂ h2 hne => by
          rcases Finset.mem_insert.mp h1 with rfl | h1' <;> rcases Finset.mem_insert.mp h2 with rfl | h2'
          · exact absurd rfl hne
          · exact (Finset.subset_sdiff.mp (hM'm.1 e₂ h2').2).2.symm
          · exact (Finset.subset_sdiff.mp (hM'm.1 e₁ h1').2).2
          · exact hM'm.2 e₁ h1' e₂ h2' hne⟩
      refine ⟨insert c M', Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hM_ins.1 e he).2, (hM_ins.1 e he).1⟩),
        hM_ins, Finset.empty_subset _, ?_⟩, Finset.mem_insert_self _ _⟩, Finset.erase_insert hnot⟩
      intro R hR
      by_cases h1 : R = R₁
      · exact ⟨c, Finset.mem_insert_self _ _, h1 ▸ hc_def ▸ Finset.inter_subset_left⟩
      · by_cases h2 : R = R₂
        · exact ⟨c, Finset.mem_insert_self _ _, h2 ▸ hc_def ▸ Finset.inter_subset_right⟩
        · obtain ⟨e, heM', heR⟩ := (Finset.mem_filter.mp hM').2.2.2 R
            (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hR⟩⟩)
          exact ⟨e, Finset.mem_insert_of_mem heM', heR⟩
    · intro M hM
      have hcM := (Finset.mem_filter.mp hM).2
      have hsdiff : V \ M.biUnion id = V' \ (M.erase c).biUnion id := by
        ext x; simp only [V', Finset.mem_sdiff, Finset.mem_biUnion, id_eq, Finset.mem_erase]
        constructor
        · rintro ⟨hxV, hno⟩
          exact ⟨⟨hxV, fun hxc => hno ⟨c, hcM, hxc⟩⟩, fun ⟨e, ⟨_, heM⟩, hxe⟩ => hno ⟨e, heM, hxe⟩⟩
        · rintro ⟨⟨hxV, hxnc⟩, hno⟩
          refine ⟨hxV, fun ⟨e, heM, hxe⟩ => ?_⟩
          by_cases h : e = c
          · exact hxnc (h ▸ hxe)
          · exact hno ⟨e, ⟨h, heM⟩, hxe⟩
      have hprod : ∏ e ∈ M, (ew e : ℂ) = (ew c : ℂ) * ∏ e ∈ M.erase c, (ew e : ℂ) :=
        (Finset.mul_prod_erase M (fun e => (ew e : ℂ)) hcM).symm
      have hcard : M.card = (M.erase c).card + 1 := (Finset.card_erase_add_one hcM).symm
      rw [hsdiff, hprod, hcard, pow_succ]; ring
  have hs1 := core2_sum_pair V H vw ew R₁ R₂ c a b u v hc_eq hc_sub hR₁_eq hR₂_eq
    hab huv ha_ne_u hb_ne_u ha_ne_v hb_ne_v ha_c hb_c hu_mem_V' hv_mem_V' hno_ab z
    {a, u} {b, v} (Or.inl ⟨rfl, rfl⟩)
  have hs2 := core2_sum_pair V H vw ew R₁ R₂ c a b u v hc_eq hc_sub hR₁_eq hR₂_eq
    hab huv ha_ne_u hb_ne_u ha_ne_v hb_ne_v ha_c hb_c hu_mem_V' hv_mem_V' hno_ab z
    {a, v} {b, u} (Or.inr ⟨rfl, rfl⟩)
  rw [hsum0, hs1, hs2]
  push_cast
  ring

private lemma core2_ew_shift {α : Type*} [DecidableEq α]
    (V' : Finset α) (H' : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ)
    (u v : α) (huv : u ≠ v) (hu_mem_V' : u ∈ V') (hv_mem_V' : v ∈ V')
    (hboth : ∀ R ∈ H', ¬ ({u, v} : Finset α) ⊆ R) (δ : ℝ) (z : ℂ) :
    ZPoly V' ∅ H' vw (fun e => if e = {u, v} then ew {u, v} + δ else ew e) z =
      ZPoly V' ∅ H' vw ew z +
      (δ : ℂ) * z *
        ∑ M' ∈ (matchingsOn (V' \ {u, v})).filter (fun M' => ∀ R ∈ H', ∃ e ∈ M', e ⊆ R),
          ((∏ x ∈ (V' \ {u, v}) \ M'.biUnion id, (vw x : ℂ)) * (∏ e ∈ M', (ew e : ℂ))) * z ^ M'.card := by
  let ew' : Finset α → ℝ := fun e => if e = {u, v} then ew {u, v} + δ else ew e
  change ZPoly V' ∅ H' vw ew' z = _
  unfold ZPoly
  let S' := (V'.powerset.filter (fun e => e.card = 2)).powerset.filter
    (fun M => IsMatching V' M ∧ ∅ ⊆ M ∧ ∀ R ∈ H', ∃ e ∈ M, e ⊆ R)
  have hdiff : ∑ M ∈ S', ((∏ x ∈ V' \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew' e : ℂ))) * z ^ M.card -
      ∑ M ∈ S', ((∏ x ∈ V' \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card =
      (δ : ℂ) * z *
        ∑ M' ∈ (matchingsOn (V' \ {u, v})).filter (fun M' => ∀ R ∈ H', ∃ e ∈ M', e ⊆ R),
          ((∏ x ∈ (V' \ {u, v}) \ M'.biUnion id, (vw x : ℂ)) * (∏ e ∈ M', (ew e : ℂ))) * z ^ M'.card := by
    rw [← Finset.sum_sub_distrib]
    have hfilt : ∑ M ∈ S', (((∏ x ∈ V' \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew' e : ℂ))) * z ^ M.card -
        ((∏ x ∈ V' \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card) =
        ∑ M ∈ S'.filter (fun M => ({u, v} : Finset α) ∈ M),
          (((∏ x ∈ V' \ M.biUnion id, (vw x : ℂ)) *
            (δ : ℂ) * (∏ e ∈ M.erase {u, v}, (ew e : ℂ))) * z ^ M.card) := by
      rw [← Finset.sum_filter_add_sum_filter_not S' (fun M => ({u, v} : Finset α) ∈ M)]
      have hzero : ∑ M ∈ S'.filter (fun M => ({u, v} : Finset α) ∉ M),
          (((∏ x ∈ V' \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew' e : ℂ))) * z ^ M.card -
          ((∏ x ∈ V' \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card) = 0 := by
        refine Finset.sum_eq_zero (fun M hM => ?_)
        have hnot := (Finset.mem_filter.mp hM).2
        have hp : ∏ e ∈ M, (ew' e : ℂ) = ∏ e ∈ M, (ew e : ℂ) :=
          Finset.prod_congr rfl (fun e he => by
            have hne : e ≠ {u, v} := fun h => hnot (h ▸ he)
            simp [ew', hne])
        rw [hp, sub_self]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl (fun M hM => ?_)
      have huvM : ({u, v} : Finset α) ∈ M := (Finset.mem_filter.mp hM).2
      have hp1 : ∏ e ∈ M, (ew' e : ℂ) =
          ((ew {u, v} : ℂ) + (δ : ℂ)) * ∏ e ∈ M.erase {u, v}, (ew e : ℂ) := by
        rw [← Finset.mul_prod_erase M (fun e => (ew' e : ℂ)) huvM]
        have hrest : ∏ e ∈ M.erase {u, v}, (ew' e : ℂ) = ∏ e ∈ M.erase {u, v}, (ew e : ℂ) :=
          Finset.prod_congr rfl (fun e he => by simp [ew', Finset.ne_of_mem_erase he])
        rw [hrest]
        simp [ew']
      have hp2 : ∏ e ∈ M, (ew e : ℂ) = (ew {u, v} : ℂ) * ∏ e ∈ M.erase {u, v}, (ew e : ℂ) :=
        (Finset.mul_prod_erase M (fun e => (ew e : ℂ)) huvM).symm
      rw [hp1, hp2]; ring
    rw [hfilt, Finset.mul_sum]
    refine Finset.sum_bij (fun M _ => M.erase {u, v}) ?_ ?_ ?_ ?_
    · intro M hM
      have hMS := (Finset.mem_filter.mp hM).1
      have huvM := (Finset.mem_filter.mp hM).2
      have hMm := (Finset.mem_filter.mp hMS).2.1
      have hM' : IsMatching (V' \ {u, v}) (M.erase {u, v}) := ⟨fun e he =>
        ⟨(hMm.1 e (Finset.mem_of_mem_erase he)).1,
          Finset.subset_sdiff.mpr ⟨(hMm.1 e (Finset.mem_of_mem_erase he)).2,
            hMm.2 e (Finset.mem_of_mem_erase he) {u, v} huvM (Finset.ne_of_mem_erase he)⟩⟩,
        fun e₁ h1 e₂ h2 hne => hMm.2 e₁ (Finset.mem_of_mem_erase h1) e₂ (Finset.mem_of_mem_erase h2) hne⟩
      refine Finset.mem_filter.mpr ⟨mem_matchingsOn.mpr hM', ?_⟩
      intro R hR
      obtain ⟨e, heM, heR⟩ := (Finset.mem_filter.mp hMS).2.2.2 R hR
      have hne : e ≠ {u, v} := fun h => hboth R hR (h ▸ heR)
      exact ⟨e, Finset.mem_erase.mpr ⟨hne, heM⟩, heR⟩
    · intro M₁ h1 M₂ h2 heq
      rw [← Finset.insert_erase (Finset.mem_filter.mp h1).2,
          ← Finset.insert_erase (Finset.mem_filter.mp h2).2, heq]
    · intro M' hM'
      have hM'm := mem_matchingsOn.mp (Finset.mem_filter.mp hM').1
      have hnot : ({u, v} : Finset α) ∉ M' := fun h =>
        (Finset.mem_sdiff.mp ((hM'm.1 _ h).2 (by simp : u ∈ ({u, v} : Finset α)))).2 (by simp)
      have hM_ins : IsMatching V' (insert {u, v} M') := ⟨fun e he => by
        rcases Finset.mem_insert.mp he with rfl | h
        · exact ⟨Finset.card_pair huv, fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hu_mem_V'
            · rw [Finset.mem_singleton.mp hx]; exact hv_mem_V'⟩
        · exact ⟨(hM'm.1 e h).1, (hM'm.1 e h).2.trans Finset.sdiff_subset⟩,
        fun e₁ h1 e₂ h2 hne => by
          rcases Finset.mem_insert.mp h1 with rfl | h1' <;> rcases Finset.mem_insert.mp h2 with rfl | h2'
          · exact absurd rfl hne
          · exact (Finset.subset_sdiff.mp (hM'm.1 e₂ h2').2).2.symm
          · exact (Finset.subset_sdiff.mp (hM'm.1 e₁ h1').2).2
          · exact hM'm.2 e₁ h1' e₂ h2' hne⟩
      refine ⟨insert {u, v} M', Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hM_ins.1 e he).2, (hM_ins.1 e he).1⟩),
        hM_ins, Finset.empty_subset _, fun R hR => ?_⟩, Finset.mem_insert_self _ _⟩, Finset.erase_insert hnot⟩
      obtain ⟨e, heM', heR⟩ := (Finset.mem_filter.mp hM').2 R hR
      exact ⟨e, Finset.mem_insert_of_mem heM', heR⟩
    · intro M hM
      have huvM := (Finset.mem_filter.mp hM).2
      have hsdiff : V' \ M.biUnion id = (V' \ {u, v}) \ (M.erase {u, v}).biUnion id := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_biUnion, id_eq, Finset.mem_erase]
        constructor
        · rintro ⟨hxV, hno⟩
          exact ⟨⟨hxV, fun hxuv => hno ⟨{u, v}, huvM, hxuv⟩⟩, fun ⟨e, ⟨_, heM⟩, hxe⟩ => hno ⟨e, heM, hxe⟩⟩
        · rintro ⟨⟨hxV, hxnuv⟩, hno⟩
          refine ⟨hxV, fun ⟨e, heM, hxe⟩ => ?_⟩
          by_cases h : e = {u, v}
          · exact hxnuv (h ▸ hxe)
          · exact hno ⟨e, ⟨h, heM⟩, hxe⟩
      have hcard : M.card = (M.erase {u, v}).card + 1 := (Finset.card_erase_add_one huvM).symm
      rw [hsdiff, hcard, pow_succ]; ring
  rw [add_comm]
  exact eq_add_of_sub_eq hdiff

private lemma reduce_ZPoly_step_core2 {α : Type*} [DecidableEq α]
    (V : Finset α) (H : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ)
    (hH : ∀ R ∈ H, R.card = 3 ∧ R ⊆ V)
    (hdeg : ∀ v ∈ V, (H.filter (fun R => v ∈ R)).card ≤ 2)
    (hvw : ∀ v ∈ V, 0 < vw v) (hew : ∀ e, 0 ≤ ew e)
    (hpos : 0 < (ZPoly V ∅ H vw ew 1).re)
    (hpair2 : ∃ R₁ ∈ H, ∃ R₂ ∈ H, R₁ ≠ R₂ ∧ (R₁ ∩ R₂).card = 2) :
    ZPolyStepGoal V ∅ H vw ew := by
  rcases hpair2 with ⟨R₁, hR₁, R₂, hR₂, hRne, hcap2⟩
  set c := R₁ ∩ R₂
  have hc_card : c.card = 2 := hcap2
  have hc_sub : c ⊆ V := Finset.inter_subset_left.trans (hH R₁ hR₁).2
  have hu1_card : (R₁ \ c).card = 1 := by
    have h1 : (R₁ \ c).card + c.card = R₁.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : c ⊆ R₁)
    rw [hc_card, (hH R₁ hR₁).1] at h1
    exact Nat.add_right_cancel h1
  have hu2_card : (R₂ \ c).card = 1 := by
    have h1 : (R₂ \ c).card + c.card = R₂.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_right : c ⊆ R₂)
    rw [hc_card, (hH R₂ hR₂).1] at h1
    exact Nat.add_right_cancel h1
  obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hu1_card
  obtain ⟨v, hv_eq⟩ := Finset.card_eq_one.mp hu2_card
  obtain ⟨a, b, hab, hc_eq⟩ := Finset.card_eq_two.mp hc_card
  have huR₁ : u ∈ R₁ ∧ u ∉ c := by
    have : u ∈ R₁ \ c := hu_eq ▸ Finset.mem_singleton_self u
    exact Finset.mem_sdiff.mp this
  have hvR₂ : v ∈ R₂ ∧ v ∉ c := by
    have : v ∈ R₂ \ c := hv_eq ▸ Finset.mem_singleton_self v
    exact Finset.mem_sdiff.mp this
  have huv : u ≠ v := by
    intro h
    have : u ∈ R₁ ∩ R₂ := Finset.mem_inter.mpr ⟨huR₁.1, h ▸ hvR₂.1⟩
    exact huR₁.2 this
  have hR₁_eq : R₁ = {a, b, u} := by
    ext x
    have hx : x ∈ R₁ ↔ x ∈ c ∨ x ∈ R₁ \ c := by
      simp only [Finset.mem_sdiff]; by_cases h : x ∈ c
      · exact ⟨fun _ => Or.inl h, fun _ => Finset.inter_subset_left h⟩
      · simp [h]
    rw [hx, hu_eq, hc_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hR₂_eq : R₂ = {a, b, v} := by
    ext x
    have hx : x ∈ R₂ ↔ x ∈ c ∨ x ∈ R₂ \ c := by
      simp only [Finset.mem_sdiff]; by_cases h : x ∈ c
      · exact ⟨fun _ => Or.inl h, fun _ => Finset.inter_subset_right h⟩
      · simp [h]
    rw [hx, hv_eq, hc_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  let V' := V \ c
  let H' := (H.erase R₁).erase R₂
  have hno_ab : ∀ R ∈ H', Disjoint R c := by
    intro R hR
    have hRH : R ∈ H := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hR)
    have hne2 : R ≠ R₂ := Finset.ne_of_mem_erase hR
    have hne1 : R ≠ R₁ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hR)
    rw [Finset.disjoint_left]
    intro x hxR hxc
    have h3 : ({R₁, R₂, R} : Finset (Finset α)) ⊆ H.filter (fun T => x ∈ T) := by
      intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact Finset.mem_filter.mpr ⟨hR₁, Finset.inter_subset_left hxc⟩
      · rcases Finset.mem_insert.mp hT with rfl | hT
        · exact Finset.mem_filter.mpr ⟨hR₂, Finset.inter_subset_right hxc⟩
        · rw [Finset.mem_singleton.mp hT]; exact Finset.mem_filter.mpr ⟨hRH, hxR⟩
    have hcard3 : ({R₁, R₂, R} : Finset (Finset α)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hne2.symm]
      simp [hRne, hne1.symm]
    have hle2 := hdeg x (hc_sub hxc)
    have hle3 := Finset.card_le_card h3
    omega
  have hV'_lt : V'.card < V.card := by
    have h1 : V'.card + c.card = V.card := Finset.card_sdiff_add_card_eq_card hc_sub
    omega
  have hH'_ok : ∀ R ∈ H', R.card = 3 ∧ R ⊆ V' := fun R hR =>
    ⟨(hH R (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hR))).1,
      Finset.subset_sdiff.mpr ⟨(hH R (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hR))).2, hno_ab R hR⟩⟩
  have hdeg' : ∀ x ∈ V', (H'.filter (fun R => x ∈ R)).card ≤ 2 := fun x hx =>
    le_trans (Finset.card_le_card (Finset.filter_subset_filter _
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))))
      (hdeg x (Finset.mem_sdiff.mp hx).1)
  let wcross : ℝ := ew {a, u} * ew {b, v} + ew {a, v} * ew {b, u}
  have hwcross_nn : 0 ≤ wcross := add_nonneg (mul_nonneg (hew _) (hew _)) (mul_nonneg (hew _) (hew _))
  have hu_mem_V' : u ∈ V' := Finset.mem_sdiff.mpr ⟨(hH R₁ hR₁).2 huR₁.1, huR₁.2⟩
  have hv_mem_V' : v ∈ V' := Finset.mem_sdiff.mpr ⟨(hH R₂ hR₂).2 hvR₂.1, hvR₂.2⟩
  have ha_c : a ∈ c := by rw [hc_eq]; simp
  have hb_c : b ∈ c := by rw [hc_eq]; simp
  have ha_ne_u : a ≠ u := fun h => huR₁.2 (h ▸ ha_c)
  have hb_ne_u : b ≠ u := fun h => huR₁.2 (h ▸ hb_c)
  have ha_ne_v : a ≠ v := fun h => hvR₂.2 (h ▸ ha_c)
  have hb_ne_v : b ≠ v := fun h => hvR₂.2 (h ▸ hb_c)
  have hsplit_Z : ∀ z : ℂ, ZPoly V ∅ H vw ew z =
      (ew c : ℂ) * z * ZPoly V' ∅ H' vw ew z +
      (wcross : ℂ) * z ^ 2 *
        ∑ M' ∈ (matchingsOn (V' \ {u, v})).filter (fun M' => ∀ R ∈ H', ∃ e ∈ M', e ⊆ R),
          ((∏ x ∈ (V' \ {u, v}) \ M'.biUnion id, (vw x : ℂ)) * (∏ e ∈ M', (ew e : ℂ))) * z ^ M'.card :=
    fun z => core2_split_ZPoly V H vw ew R₁ R₂ c a b u v hR₁ hR₂ rfl hcap2 hc_eq hc_sub
      huR₁ hvR₂ hR₁_eq hR₂_eq hab huv ha_ne_u hb_ne_u ha_ne_v hb_ne_v ha_c hb_c
      hu_mem_V' hv_mem_V' hno_ab z
  by_cases hewc : ew c = 0
  · have hwcross_pos : 0 < wcross := by
      have h1 := hsplit_Z 1
      rw [hewc] at h1
      simp only [Complex.ofReal_zero, zero_mul, zero_add, one_pow, mul_one] at h1
      by_contra hle
      have h0 : wcross = 0 := le_antisymm (not_lt.mp hle) hwcross_nn
      rw [h0] at h1
      simp at h1
      rw [h1] at hpos; simp at hpos
    let V'' := V' \ {u, v}
    let F₂'' := (H'.filter (fun R => (R ∩ {u, v}).card = 1)).image (fun R => R \ {u, v})
    let H'' := H'.filter (fun R => Disjoint R {u, v})
    have hno_both : ∀ R ∈ H', ¬ ({u, v} ⊆ R) := by
      intro R hR hsub
      have h1 := hsplit_Z 1
      rw [hewc] at h1
      simp only [Complex.ofReal_zero, zero_mul, zero_add, one_pow, mul_one] at h1
      have hempty : ((matchingsOn V'').filter (fun M' => ∀ R ∈ H', ∃ e ∈ M', e ⊆ R)) = ∅ := by
        ext M'
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hM' hhit
        obtain ⟨e, heM', heR⟩ := hhit R hR
        have hM'm := mem_matchingsOn.mp hM'
        have hdisj : Disjoint e {u, v} := (Finset.subset_sdiff.mp (hM'm.1 e heM').2).2
        have he_sub : e ⊆ R \ {u, v} := Finset.subset_sdiff.mpr ⟨heR, hdisj⟩
        have hc : (R \ {u, v}).card = 1 := by
          have h1 := Finset.card_sdiff_add_card_eq_card hsub
          have h2 := Finset.card_pair huv
          have h3 := (hH'_ok R hR).1
          omega
        have hle := Finset.card_le_card he_sub
        rw [(hM'm.1 e heM').1, hc] at hle; omega
      rw [hempty] at h1; simp at h1
      rw [h1] at hpos; simp at hpos
    have hZ_eq : ∀ z : ℂ, ZPoly V ∅ H vw ew z = (wcross : ℂ) * z ^ 2 * ZPoly V'' F₂'' H'' vw ew z := by
      intro z
      rw [hsplit_Z z, hewc]
      simp only [Complex.ofReal_zero, zero_mul, zero_add]
      apply congrArg ((wcross : ℂ) * z ^ 2 * ·)
      unfold ZPoly
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext M'
      simp only [Finset.mem_filter, mem_matchingsOn, Finset.mem_powerset]
      constructor
      · rintro ⟨hM'm, hhit⟩
        refine ⟨fun e he => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hM'm.1 e he).2, (hM'm.1 e he).1⟩,
          hM'm, ?_, ?_⟩
        · intro e he
          rcases Finset.mem_image.mp he with ⟨R, hR, rfl⟩
          rw [Finset.mem_filter] at hR
          obtain ⟨e', he'M', he'R⟩ := hhit R hR.1
          have hdisj : Disjoint e' {u, v} := (Finset.subset_sdiff.mp (hM'm.1 e' he'M').2).2
          have hsub : e' ⊆ R \ {u, v} := Finset.subset_sdiff.mpr ⟨he'R, hdisj⟩
          have hc : (R \ {u, v}).card = 2 := by
            have h1 := Finset.card_sdiff_add_card_inter R {u, v}
            have h2 := (hH'_ok R hR.1).1
            have h3 := hR.2
            omega
          have heq : e' = R \ {u, v} := Finset.eq_of_subset_of_card_le hsub (by rw [(hM'm.1 e' he'M').1, hc])
          exact heq ▸ he'M'
        · intro R hR
          exact hhit R (Finset.mem_filter.mp hR).1
      · rintro ⟨_, hM'm, hF, hH''⟩
        refine ⟨hM'm, fun R hR => ?_⟩
        have hle : (R ∩ {u, v}).card ≤ 2 := le_trans (Finset.card_le_card Finset.inter_subset_right)
          (by rw [Finset.card_pair huv])
        by_cases hc0 : (R ∩ {u, v}).card = 0
        · exact hH'' R (Finset.mem_filter.mpr ⟨hR, Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hc0)⟩)
        · by_cases hc1 : (R ∩ {u, v}).card = 1
          · exact ⟨R \ {u, v}, hF (Finset.mem_image.mpr ⟨R, Finset.mem_filter.mpr ⟨hR, hc1⟩, rfl⟩), Finset.sdiff_subset⟩
          · exfalso
            have hc2 : (R ∩ {u, v}).card = 2 := by omega
            have heq : R ∩ {u, v} = {u, v} := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
              (by rw [Finset.card_pair huv, hc2])
            exact hno_both R hR (heq ▸ Finset.inter_subset_left)
    have hpos'' : 0 < (ZPoly V'' F₂'' H'' vw ew 1).re := by
      have h1 : (ZPoly V ∅ H vw ew 1).re = wcross * (ZPoly V'' F₂'' H'' vw ew 1).re := by
        rw [hZ_eq 1, one_pow, mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [h1] at hpos
      exact pos_of_mul_pos_right hpos (le_of_lt hwcross_pos)
    have hV''_lt : V''.card < V.card := lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset) hV'_lt
    have hF₂''_ok : ∀ e ∈ F₂'', e.card = 2 ∧ e ⊆ V'' := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨R, hR, rfl⟩
      rw [Finset.mem_filter] at hR
      have h1 := Finset.card_sdiff_add_card_inter R {u, v}
      have h2 := (hH'_ok R hR.1).1
      have h3 := hR.2
      exact ⟨by omega, Finset.sdiff_subset_sdiff (hH'_ok R hR.1).2 (subset_refl _)⟩
    have hH''_ok : ∀ R ∈ H'', R.card = 3 ∧ R ⊆ V'' := fun R hR =>
      ⟨(hH'_ok R (Finset.mem_filter.mp hR).1).1,
        Finset.subset_sdiff.mpr ⟨(hH'_ok R (Finset.mem_filter.mp hR).1).2, (Finset.mem_filter.mp hR).2⟩⟩
    have hdeg'' : ∀ x ∈ V'', (H''.filter (fun R => x ∈ R)).card ≤ 2 := fun x hx =>
      le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))
        (hdeg' x (Finset.mem_sdiff.mp hx).1)
    exact ⟨2, wcross, V'', F₂'', H'', vw, ew, hwcross_pos, hV''_lt, hF₂''_ok, hH''_ok, hdeg'',
      (fun x hx => hvw x (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1), hew, hpos'', hZ_eq⟩
  · have hewc_pos : 0 < ew c := lt_of_le_of_ne (hew c) (Ne.symm hewc)
    by_cases hboth : ∃ R ∈ H', ({u, v} : Finset α) ⊆ R
    · rcases hboth with ⟨R₃, hR₃, hsub3⟩
      have hempty : ((matchingsOn (V' \ {u, v})).filter (fun M' => ∀ R ∈ H', ∃ e ∈ M', e ⊆ R)) = ∅ := by
        ext M'
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hM' hhit
        obtain ⟨e, heM', heR⟩ := hhit R₃ hR₃
        have hM'm := mem_matchingsOn.mp hM'
        have hdisj : Disjoint e {u, v} := (Finset.subset_sdiff.mp (hM'm.1 e heM').2).2
        have he_sub : e ⊆ R₃ \ {u, v} := Finset.subset_sdiff.mpr ⟨heR, hdisj⟩
        have hc : (R₃ \ {u, v}).card = 1 := by
          have h1 := Finset.card_sdiff_add_card_eq_card hsub3
          have h2 := Finset.card_pair huv
          have h3 := (hH'_ok R₃ hR₃).1
          omega
        have hle := Finset.card_le_card he_sub
        rw [(hM'm.1 e heM').1, hc] at hle; omega
      have hZ_eq : ∀ z : ℂ, ZPoly V ∅ H vw ew z = (ew c : ℂ) * z * ZPoly V' ∅ H' vw ew z := by
        intro z
        rw [hsplit_Z z, hempty]
        simp
      have hpos' : 0 < (ZPoly V' ∅ H' vw ew 1).re := by
        have h1 : (ZPoly V ∅ H vw ew 1).re = ew c * (ZPoly V' ∅ H' vw ew 1).re := by
          rw [hZ_eq 1, mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rw [h1] at hpos
        exact pos_of_mul_pos_right hpos (le_of_lt hewc_pos)
      exact ⟨1, ew c, V', ∅, H', vw, ew, hewc_pos, hV'_lt, (by simp), hH'_ok, hdeg',
        (fun x hx => hvw x (Finset.mem_sdiff.mp hx).1), hew, hpos', fun z => by simpa [pow_one] using hZ_eq z⟩
    · push_neg at hboth
      let ew' : Finset α → ℝ := fun e => if e = {u, v} then ew {u, v} + wcross / ew c else ew e
      have hew' : ∀ e, 0 ≤ ew' e := fun e => by
        simp only [ew']
        split_ifs
        · exact add_nonneg (hew _) (div_nonneg hwcross_nn (le_of_lt hewc_pos))
        · exact hew e
      have hZ_eq : ∀ z : ℂ, ZPoly V ∅ H vw ew z = (ew c : ℂ) * z * ZPoly V' ∅ H' vw ew' z := by
        intro z
        rw [hsplit_Z z]
        have hdecomp := core2_ew_shift V' H' vw ew u v huv hu_mem_V' hv_mem_V' hboth (wcross / ew c) z
        rw [hdecomp, mul_add]
        apply congrArg ((ew c : ℂ) * z * ZPoly V' ∅ H' vw ew z + ·)
        have hcancel : (ew c : ℂ) * ((wcross / ew c : ℝ) : ℂ) = (wcross : ℂ) := by
          push_cast
          have hne : (ew c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hewc_pos)
          exact mul_div_cancel₀ _ hne
        have hl : (ew c : ℂ) * z * (((wcross / ew c : ℝ) : ℂ) * z) = (wcross : ℂ) * z ^ 2 := by
          calc
            (ew c : ℂ) * z * (((wcross / ew c : ℝ) : ℂ) * z)
              = (ew c : ℂ) * ((wcross / ew c : ℝ) : ℂ) * z ^ 2 := by ring
            _ = (wcross : ℂ) * z ^ 2 := by rw [hcancel]
        symm
        rw [← mul_assoc, hl]
      have hpos' : 0 < (ZPoly V' ∅ H' vw ew' 1).re := by
        have h1 : (ZPoly V ∅ H vw ew 1).re = ew c * (ZPoly V' ∅ H' vw ew' 1).re := by
          rw [hZ_eq 1, mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rw [h1] at hpos
        exact pos_of_mul_pos_right hpos (le_of_lt hewc_pos)
      exact ⟨1, ew c, V', ∅, H', vw, ew', hewc_pos, hV'_lt, (by simp), hH'_ok, hdeg',
        (fun x hx => hvw x (Finset.mem_sdiff.mp hx).1), hew', hpos', fun z => by simpa [pow_one] using hZ_eq z⟩

private lemma reduce_ZPoly_step_unicyclic {α : Type*} [DecidableEq α]
    (V : Finset α) (H C : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ)
    (hH : ∀ R ∈ H, R.card = 3 ∧ R ⊆ V)
    (hdeg : ∀ v ∈ V, (H.filter (fun R => v ∈ R)).card ≤ 2)
    (hvw : ∀ v ∈ V, 0 < vw v) (hew : ∀ e, 0 ≤ ew e)
    (hpos : 0 < (ZPoly V ∅ H vw ew 1).re)
    (hC_sub : C ⊆ H) (hC_ne : C.Nonempty)
    (hC_closed : ∀ R₁ ∈ C, ∀ R₂ ∈ H \ C, Disjoint R₁ R₂)
    (hVC_sub : C.biUnion id ⊆ V)
    (hhit_C_card : ∀ M, IsMatching V M → (∀ R ∈ C, ∃ e ∈ M, e ⊆ R) →
      let MC := M.filter (fun e => ∃ R ∈ C, e ⊆ R)
      MC.card = C.card ∧ (MC.biUnion id) ⊆ C.biUnion id ∧ (MC.biUnion id).card = 2 * C.card)
    (hVC_even : (C.biUnion id).card = 2 * C.card) :
    ZPolyStepGoal V ∅ H vw ew := by
  let VC := C.biUnion id
  let MCs := (matchingsOn VC).filter (fun MC => (∀ e ∈ MC, ∃ R ∈ C, e ⊆ R) ∧ ∀ R ∈ C, ∃ e ∈ MC, e ⊆ R)
  let cC : ℝ := ∑ MC ∈ MCs, ∏ e ∈ MC, ew e
  have hcC_nn : 0 ≤ cC := Finset.sum_nonneg (fun MC _ => Finset.prod_nonneg (fun e _ => hew e))
  let V' := V \ VC
  let H' := H \ C
  have hZ_eq : ∀ z : ℂ, ZPoly V ∅ H vw ew z = (cC : ℂ) * z ^ C.card * ZPoly V' ∅ H' vw ew z := by
    intro z
    unfold ZPoly
    have hprod_sum : (cC : ℂ) * z ^ C.card *
        ∑ M' ∈ (V'.powerset.filter (fun e => e.card = 2)).powerset.filter
          (fun M' => IsMatching V' M' ∧ ∅ ⊆ M' ∧ ∀ R ∈ H', ∃ e ∈ M', e ⊆ R),
          ((∏ x ∈ V' \ M'.biUnion id, (vw x : ℂ)) * (∏ e ∈ M', (ew e : ℂ))) * z ^ M'.card =
        ∑ p ∈ MCs ×ˢ ((V'.powerset.filter (fun e => e.card = 2)).powerset.filter
          (fun M' => IsMatching V' M' ∧ ∅ ⊆ M' ∧ ∀ R ∈ H', ∃ e ∈ M', e ⊆ R)),
          ((∏ e ∈ p.1, (ew e : ℂ)) * z ^ C.card) *
          (((∏ x ∈ V' \ p.2.biUnion id, (vw x : ℂ)) * (∏ e ∈ p.2, (ew e : ℂ))) * z ^ p.2.card) := by
      rw [Finset.sum_product]
      simp only [cC, Complex.ofReal_sum, Complex.ofReal_prod, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hprod_sum]
    refine Finset.sum_bij (fun M _ => (M.filter (fun e => ∃ R ∈ C, e ⊆ R),
        M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R))) ?_ ?_ ?_ ?_
    · intro M hM
      have hMm := (Finset.mem_filter.mp hM).2.1
      have hhit := (Finset.mem_filter.mp hM).2.2.2
      have hC := hhit_C_card M hMm (fun R hR => hhit R (hC_sub hR))
      set MC := M.filter (fun e => ∃ R ∈ C, e ⊆ R)
      set M' := M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R)
      have hMC_full : MC.biUnion id = VC :=
        Finset.eq_of_subset_of_card_le hC.2.1 (by rw [hC.2.2, hVC_even])
      have hMC_in : MC ∈ MCs := by
        refine Finset.mem_filter.mpr ⟨mem_matchingsOn.mpr ⟨fun e he =>
          ⟨(hMm.1 e (Finset.mem_filter.mp he).1).1,
            (Finset.subset_biUnion_of_mem id he).trans hC.2.1⟩,
          fun e₁ h1 e₂ h2 hne => hMm.2 e₁ (Finset.mem_filter.mp h1).1 e₂ (Finset.mem_filter.mp h2).1 hne⟩,
          fun e he => (Finset.mem_filter.mp he).2,
          fun R hR => by
            obtain ⟨e, heM, heR⟩ := hhit R (hC_sub hR)
            exact ⟨e, Finset.mem_filter.mpr ⟨heM, R, hR, heR⟩, heR⟩⟩
      have hM'_m : IsMatching V' M' := ⟨fun e he => by
        have heM := (Finset.mem_filter.mp he).1
        have hnot := (Finset.mem_filter.mp he).2
        refine ⟨(hMm.1 e heM).1, Finset.subset_sdiff.mpr ⟨(hMm.1 e heM).2, ?_⟩⟩
        rw [← hMC_full, Finset.disjoint_biUnion_right]
        intro e' he'
        have hne : e ≠ e' := fun h => hnot (h ▸ (Finset.mem_filter.mp he').2)
        exact hMm.2 e heM e' (Finset.mem_filter.mp he').1 hne,
        fun e₁ h1 e₂ h2 hne => hMm.2 e₁ (Finset.mem_filter.mp h1).1 e₂ (Finset.mem_filter.mp h2).1 hne⟩
      refine Finset.mem_product.mpr ⟨hMC_in, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hM'_m.1 e he).2, (hM'_m.1 e he).1⟩),
        hM'_m, Finset.empty_subset _, ?_⟩⟩
      intro R hR
      obtain ⟨e, heM, heR⟩ := hhit R (Finset.mem_sdiff.mp hR).1
      have hnot : ¬ ∃ R' ∈ C, e ⊆ R' := fun ⟨R', hR', heR'⟩ => by
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(hMm.1 e heM).1]; decide)
        exact Finset.disjoint_left.mp (hC_closed R' hR' R hR) (heR' hx) (heR hx)
      exact ⟨e, Finset.mem_filter.mpr ⟨heM, hnot⟩, heR⟩
    · intro M₁ _ M₂ _ heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      ext e
      by_cases h : ∃ R ∈ C, e ⊆ R
      · have := Finset.ext_iff.mp h1 e; simp [h] at this; exact this
      · have := Finset.ext_iff.mp h2 e
        simp only [Finset.mem_filter] at this
        exact ⟨fun ha => (this.mp ⟨ha, h⟩).1, fun hb => (this.mpr ⟨hb, h⟩).1⟩
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      have h1m := mem_matchingsOn.mp (Finset.mem_filter.mp hp1).1
      have h1in := (Finset.mem_filter.mp hp1).2.1
      have h1hit := (Finset.mem_filter.mp hp1).2.2
      have h2m := (Finset.mem_filter.mp hp2).2.1
      have h2hit := (Finset.mem_filter.mp hp2).2.2.2
      have hdisj : Disjoint p.1 p.2 := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(h1m.1 e he1).1]; decide)
        exact (Finset.mem_sdiff.mp ((h2m.1 e he2).2 hx)).2 ((h1m.1 e he1).2 hx)
      have hMu : IsMatching V (p.1 ∪ p.2) := ⟨fun e he => by
        rcases Finset.mem_union.mp he with h1 | h2
        · exact ⟨(h1m.1 e h1).1, (h1m.1 e h1).2.trans hVC_sub⟩
        · exact ⟨(h2m.1 e h2).1, (h2m.1 e h2).2.trans Finset.sdiff_subset⟩,
        fun e₁ h1 e₂ h2 hne => by
          rcases Finset.mem_union.mp h1 with h1' | h1' <;> rcases Finset.mem_union.mp h2 with h2' | h2'
          · exact h1m.2 e₁ h1' e₂ h2' hne
          · exact (Finset.subset_sdiff.mp (h2m.1 e₂ h2').2).2.symm.mono_left (h1m.1 e₁ h1').2
          · exact (Finset.subset_sdiff.mp (h2m.1 e₁ h1').2).2.mono_right (h1m.1 e₂ h2').2
          · exact h2m.2 e₁ h1' e₂ h2' hne⟩
      refine ⟨p.1 ∪ p.2, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hMu.1 e he).2, (hMu.1 e he).1⟩),
        hMu, Finset.empty_subset _, ?_⟩, ?_⟩
      · intro R hR
        by_cases hRC : R ∈ C
        · obtain ⟨e, he1, heR⟩ := h1hit R hRC
          exact ⟨e, Finset.mem_union_left _ he1, heR⟩
        · obtain ⟨e, he2, heR⟩ := h2hit R (Finset.mem_sdiff.mpr ⟨hR, hRC⟩)
          exact ⟨e, Finset.mem_union_right _ he2, heR⟩
      · apply Prod.ext
        · ext e; simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨h1 | h2, hex⟩
            · exact h1
            · exfalso
              rcases hex with ⟨R, hR, heR⟩
              obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(h2m.1 e h2).1]; decide)
              exact (Finset.mem_sdiff.mp ((h2m.1 e h2).2 hx)).2 (Finset.mem_biUnion.mpr ⟨R, hR, heR hx⟩)
          · intro h1; exact ⟨Or.inl h1, h1in e h1⟩
        · ext e; simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨h1 | h2, hnot⟩
            · exact absurd (h1in e h1) hnot
            · exact h2
          · intro h2
            refine ⟨Or.inr h2, fun ⟨R, hR, heR⟩ => ?_⟩
            obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(h2m.1 e h2).1]; decide)
            exact (Finset.mem_sdiff.mp ((h2m.1 e h2).2 hx)).2 (Finset.mem_biUnion.mpr ⟨R, hR, heR hx⟩)
    · intro M hM
      have hMm := (Finset.mem_filter.mp hM).2.1
      have hhit := (Finset.mem_filter.mp hM).2.2.2
      have hC := hhit_C_card M hMm (fun R hR => hhit R (hC_sub hR))
      set MC := M.filter (fun e => ∃ R ∈ C, e ⊆ R)
      set M' := M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R)
      have hMC_full : MC.biUnion id = VC :=
        Finset.eq_of_subset_of_card_le hC.2.1 (by rw [hC.2.2, hVC_even])
      have hpart : M = MC ∪ M' := (Finset.filter_union_filter_not_eq _ M).symm
      have hdisj : Disjoint MC M' := Finset.disjoint_filter_filter_not M M _
      have hsdiff : V \ M.biUnion id = V' \ M'.biUnion id := by
        rw [hpart, Finset.union_biUnion, hMC_full]
        ext x; simp only [V', Finset.mem_sdiff, Finset.mem_union]; tauto
      have hprod : ∏ e ∈ M, (ew e : ℂ) = (∏ e ∈ MC, (ew e : ℂ)) * (∏ e ∈ M', (ew e : ℂ)) := by
        rw [hpart, Finset.prod_union hdisj]
      have hcard : M.card = C.card + M'.card := by
        rw [hpart, Finset.card_union_of_disjoint hdisj, hC.1]
      rw [hsdiff, hprod, hcard, pow_add]; ring
  have hcC_pos : 0 < cC := by
    by_contra hle
    have h0 : cC = 0 := le_antisymm (not_lt.mp hle) hcC_nn
    have h1 := hZ_eq 1
    rw [h0] at h1; simp at h1; rw [h1] at hpos; simp at hpos
  have hpos' : 0 < (ZPoly V' ∅ H' vw ew 1).re := by
    have h1 : (ZPoly V ∅ H vw ew 1).re = cC * (ZPoly V' ∅ H' vw ew 1).re := by
      rw [hZ_eq 1, one_pow, mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [h1] at hpos
    exact pos_of_mul_pos_right hpos (le_of_lt hcC_pos)
  have hV'_lt : V'.card < V.card := by
    have h1 : V'.card + VC.card = V.card := Finset.card_sdiff_add_card_eq_card hVC_sub
    have h2 : 0 < C.card := hC_ne.card_pos
    have h3 : VC.card = 2 * C.card := hVC_even
    omega
  have hH'_ok : ∀ R ∈ H', R.card = 3 ∧ R ⊆ V' := fun R hR =>
    ⟨(hH R (Finset.mem_sdiff.mp hR).1).1,
      Finset.subset_sdiff.mpr ⟨(hH R (Finset.mem_sdiff.mp hR).1).2,
        Finset.disjoint_left.mpr (fun x hxR hxVC => by
          rcases Finset.mem_biUnion.mp hxVC with ⟨R₁, hR₁, hxR₁⟩
          exact Finset.disjoint_left.mp (hC_closed R₁ hR₁ R hR) hxR₁ hxR)⟩⟩
  have hdeg' : ∀ x ∈ V', (H'.filter (fun R => x ∈ R)).card ≤ 2 := fun x hx =>
    le_trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
      (hdeg x (Finset.mem_sdiff.mp hx).1)
  exact ⟨C.card, cC, V', ∅, H', vw, ew, hcC_pos, hV'_lt, (by simp), hH'_ok, hdeg',
    (fun x hx => hvw x (Finset.mem_sdiff.mp hx).1), hew, hpos', hZ_eq⟩

private lemma reduce_ZPoly_step_tree {α : Type*} [DecidableEq α]
    (V : Finset α) (H C : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ)
    (hH : ∀ R ∈ H, R.card = 3 ∧ R ⊆ V)
    (hdeg : ∀ v ∈ V, (H.filter (fun R => v ∈ R)).card ≤ 2)
    (hvw : ∀ v ∈ V, 0 < vw v) (hew : ∀ e, 0 ≤ ew e)
    (hpos : 0 < (ZPoly V ∅ H vw ew 1).re)
    (hC_sub : C ⊆ H) (hC_ne : C.Nonempty)
    (hC_closed : ∀ R₁ ∈ C, ∀ R₂ ∈ H \ C, Disjoint R₁ R₂)
    (hVC_sub : C.biUnion id ⊆ V)
    (hhit_C_card : ∀ M, IsMatching V M → (∀ R ∈ C, ∃ e ∈ M, e ⊆ R) →
      let MC := M.filter (fun e => ∃ R ∈ C, e ⊆ R)
      MC.card = C.card ∧ (MC.biUnion id) ⊆ C.biUnion id ∧ (MC.biUnion id).card = 2 * C.card)
    (hVC_odd : (C.biUnion id).card = 2 * C.card + 1) :
    ZPolyStepGoal V ∅ H vw ew := by
  let VC := C.biUnion id
  have hVC_card : VC.card = 2 * C.card + 1 := hVC_odd
  have hVC_ne : VC.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v₀, hv₀⟩ := hVC_ne
  let MCs := fun u : α => (matchingsOn VC).filter (fun MC =>
    (∀ e ∈ MC, ∃ R ∈ C, e ⊆ R) ∧ (∀ R ∈ C, ∃ e ∈ MC, e ⊆ R) ∧ VC \ MC.biUnion id = {u})
  let cu : α → ℝ := fun u => ∑ MC ∈ MCs u, ∏ e ∈ MC, ew e
  have hcu_nn : ∀ u, 0 ≤ cu u := fun u => Finset.sum_nonneg (fun MC _ => Finset.prod_nonneg (fun e _ => hew e))
  let V' := insert v₀ (V \ VC)
  let H' := H \ C
  let vw' : α → ℝ := fun x => if x = v₀ then ∑ u ∈ VC, cu u * vw u else vw x
  let ew' : Finset α → ℝ := fun e =>
    if v₀ ∈ e then
      if h : (e.erase v₀).card = 1 then
        let w := Classical.choose (Finset.card_eq_one.mp h)
        ∑ u ∈ VC, cu u * ew {u, w}
      else ew e
    else ew e
  have hew'_pair : ∀ w ∈ V \ VC, ew' {v₀, w} = ∑ u ∈ VC, cu u * ew {u, w} := by
    intro w hw
    have hne : w ≠ v₀ := fun h => (Finset.mem_sdiff.mp hw).2 (h ▸ hv₀)
    have her : ({v₀, w} : Finset α).erase v₀ = {w} := by
      ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx0, rfl | rfl⟩
        · exact absurd rfl hx0
        · rfl
      · rintro rfl; exact ⟨hne, Or.inr rfl⟩
    have hc1 : (({v₀, w} : Finset α).erase v₀).card = 1 := by rw [her, Finset.card_singleton]
    have hch : Classical.choose (Finset.card_eq_one.mp hc1) = w := by
      have hspec := Classical.choose_spec (Finset.card_eq_one.mp hc1)
      exact (Finset.singleton_injective (her.symm.trans hspec)).symm
    simp only [ew', Finset.mem_insert_self, ↓reduceIte, hc1, ↓reduceDIte, hch]
  have hew'_other : ∀ e, v₀ ∉ e → ew' e = ew e := fun e h => by simp [ew', h]
  have hew'_nn : ∀ e, 0 ≤ ew' e := fun e => by
    simp only [ew']
    split_ifs
    · exact Finset.sum_nonneg (fun u _ => mul_nonneg (hcu_nn u) (hew _))
    · exact hew e
    · exact hew e
  have hV'_lt : V'.card < V.card := by
    have hnot : v₀ ∉ V \ VC := fun h => (Finset.mem_sdiff.mp h).2 hv₀
    have h1 : V'.card = (V \ VC).card + 1 := Finset.card_insert_of_notMem hnot
    have h2 : (V \ VC).card + VC.card = V.card := Finset.card_sdiff_add_card_eq_card hVC_sub
    have h3 : 0 < C.card := hC_ne.card_pos
    omega
  have hZ_eq : ∀ z : ℂ, ZPoly V ∅ H vw ew z = z ^ C.card * ZPoly V' ∅ H' vw' ew' z := by
    intro z
    unfold ZPoly
    let All := (V.powerset.filter (fun e => e.card = 2)).powerset.filter
      (fun M => IsMatching V M ∧ ∅ ⊆ M ∧ ∀ R ∈ H, ∃ e ∈ M, e ⊆ R)
    let All' := (V'.powerset.filter (fun e => e.card = 2)).powerset.filter
      (fun M' => IsMatching V' M' ∧ ∅ ⊆ M' ∧ ∀ R ∈ H', ∃ e ∈ M', e ⊆ R)
    let proj : Finset (Finset α) → Finset (Finset α) := fun M =>
      (M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R)).image (fun e =>
        if Disjoint e VC then e else insert v₀ (e \ VC))
    have hproj_mem : ∀ M ∈ All, proj M ∈ All' ∧
        ∃ u ∈ VC, (M.filter (fun e => ∃ R ∈ C, e ⊆ R)) ∈ MCs u := by
      intro M hM
      have hMm := (Finset.mem_filter.mp hM).2.1
      have hhit := (Finset.mem_filter.mp hM).2.2.2
      have hC := hhit_C_card M hMm (fun R hR => hhit R (hC_sub hR))
      set MC := M.filter (fun e => ∃ R ∈ C, e ⊆ R)
      set Mrest := M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R)
      have hrem_card : (VC \ MC.biUnion id).card = 1 := by
        have h1 : (VC \ MC.biUnion id).card + (MC.biUnion id).card = VC.card :=
          Finset.card_sdiff_add_card_eq_card hC.2.1
        have h2 : (MC.biUnion id).card = 2 * C.card := hC.2.2
        omega
      obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hrem_card
      have hu_VC : u ∈ VC := (Finset.mem_sdiff.mp (hu_eq ▸ Finset.mem_singleton_self u)).1
      have hMC_in : MC ∈ MCs u := Finset.mem_filter.mpr ⟨mem_matchingsOn.mpr ⟨fun e he =>
        ⟨(hMm.1 e (Finset.mem_filter.mp he).1).1, (Finset.subset_biUnion_of_mem id he).trans hC.2.1⟩,
        fun e₁ h1 e₂ h2 hne => hMm.2 e₁ (Finset.mem_filter.mp h1).1 e₂ (Finset.mem_filter.mp h2).1 hne⟩,
        fun e he => (Finset.mem_filter.mp he).2,
        fun R hR => by
          obtain ⟨e, heM, heR⟩ := hhit R (hC_sub hR)
          exact ⟨e, Finset.mem_filter.mpr ⟨heM, R, hR, heR⟩, heR⟩, hu_eq⟩
      have hrest_inter : ∀ e ∈ Mrest, e ∩ VC ⊆ {u} := by
        intro e he x hx
        rw [← hu_eq, Finset.mem_sdiff]
        refine ⟨(Finset.mem_inter.mp hx).2, fun hx_in => ?_⟩
        rcases Finset.mem_biUnion.mp hx_in with ⟨e', he'MC, hxe'⟩
        have hne : e ≠ e' := fun h => (Finset.mem_filter.mp he).2 (h ▸ (Finset.mem_filter.mp he'MC).2)
        exact Finset.disjoint_left.mp (hMm.2 e (Finset.mem_filter.mp he).1 e'
          (Finset.mem_filter.mp he'MC).1 hne) (Finset.mem_inter.mp hx).1 hxe'
      have hproj_edge : ∀ e ∈ Mrest,
          (Disjoint e VC ∧ (if Disjoint e VC then e else insert v₀ (e \ VC)) = e) ∨
          (∃ w ∈ V \ VC, e = {u, w} ∧ (if Disjoint e VC then e else insert v₀ (e \ VC)) = {v₀, w}) := by
        intro e he
        by_cases hd : Disjoint e VC
        · left; exact ⟨hd, if_pos hd⟩
        · right
          have hne_inter : (e ∩ VC).Nonempty := Finset.not_disjoint_iff.mp hd |>
            fun ⟨x, h1, h2⟩ => ⟨x, Finset.mem_inter.mpr ⟨h1, h2⟩⟩
          have hinter_eq : e ∩ VC = {u} := Finset.eq_of_subset_of_card_le (hrest_inter e he)
            (by rw [Finset.card_singleton]; exact hne_inter.card_pos)
          have hsdiff_card : (e \ VC).card = 1 := by
            have h1 := Finset.card_sdiff_add_card_inter e VC
            have h2 := (hMm.1 e (Finset.mem_filter.mp he).1).1
            rw [hinter_eq, Finset.card_singleton] at h1; omega
          obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp hsdiff_card
          have hw_mem : w ∈ e \ VC := hw_eq ▸ Finset.mem_singleton_self w
          have hw_V : w ∈ V \ VC := Finset.mem_sdiff.mpr
            ⟨(hMm.1 e (Finset.mem_filter.mp he).1).2 (Finset.mem_sdiff.mp hw_mem).1,
              (Finset.mem_sdiff.mp hw_mem).2⟩
          have he_eq : e = {u, w} := by
            ext x
            have h1 : x ∈ e ↔ x ∈ e ∩ VC ∨ x ∈ e \ VC := by
              simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
            rw [h1, hinter_eq, hw_eq]
            simp only [Finset.mem_insert, Finset.mem_singleton]
          refine ⟨w, hw_V, he_eq, ?_⟩
          rw [if_neg hd, hw_eq]
      have hproj_m : IsMatching V' (proj M) := by
        refine ⟨fun e' he' => ?_, fun e₁' h1 e₂' h2 hne => ?_⟩
        · rcases Finset.mem_image.mp he' with ⟨e, he, rfl⟩
          rcases hproj_edge e he with ⟨hd, heq⟩ | ⟨w, hw, _, heq⟩
          · rw [heq]
            exact ⟨(hMm.1 e (Finset.mem_filter.mp he).1).1,
              (Finset.subset_sdiff.mpr ⟨(hMm.1 e (Finset.mem_filter.mp he).1).2, hd⟩).trans
                (Finset.subset_insert _ _)⟩
          · rw [heq]
            have hwne : v₀ ≠ w := fun h => (Finset.mem_sdiff.mp hw).2 (h ▸ hv₀)
            exact ⟨Finset.card_pair hwne, fun x hx => by
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact Finset.mem_insert_self _ _
              · rw [Finset.mem_singleton.mp hx]; exact Finset.mem_insert_of_mem hw⟩
        · rcases Finset.mem_image.mp h1 with ⟨e₁, he₁, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨e₂, he₂, rfl⟩
          have hene : e₁ ≠ e₂ := fun h => hne (by rw [h])
          have hd12 := hMm.2 e₁ (Finset.mem_filter.mp he₁).1 e₂ (Finset.mem_filter.mp he₂).1 hene
          rcases hproj_edge e₁ he₁ with ⟨hd1, heq1⟩ | ⟨w₁, hw₁, he₁_eq, heq1⟩ <;>
            rcases hproj_edge e₂ he₂ with ⟨hd2, heq2⟩ | ⟨w₂, hw₂, he₂_eq, heq2⟩
          · rw [heq1, heq2]; exact hd12
          · rw [heq1, heq2, Finset.disjoint_left]
            intro x hx1 hx2
            rcases Finset.mem_insert.mp hx2 with rfl | hx2
            · exact Finset.disjoint_left.mp hd1 hx1 hv₀
            · rw [Finset.mem_singleton.mp hx2] at hx1
              exact Finset.disjoint_left.mp hd12 hx1 (he₂_eq ▸ by simp)
          · rw [heq1, heq2, Finset.disjoint_right]
            intro x hx2 hx1
            rcases Finset.mem_insert.mp hx1 with rfl | hx1
            · exact Finset.disjoint_left.mp hd2 hx2 hv₀
            · rw [Finset.mem_singleton.mp hx1] at hx2
              exact Finset.disjoint_left.mp hd12 (he₁_eq ▸ by simp) hx2
          · exfalso
            have hu1 : u ∈ e₁ := by rw [he₁_eq]; simp
            have hu2 : u ∈ e₂ := by rw [he₂_eq]; simp
            exact Finset.disjoint_left.mp hd12 hu1 hu2
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun e' he' =>
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hproj_m.1 e' he').2, (hproj_m.1 e' he').1⟩),
        hproj_m, Finset.empty_subset _, ?_⟩, u, hu_VC, hMC_in⟩
      intro R hR
      obtain ⟨e, heM, heR⟩ := hhit R (Finset.mem_sdiff.mp hR).1
      have hdisjR : Disjoint R VC := Finset.disjoint_left.mpr (fun x hxR hxVC => by
        rcases Finset.mem_biUnion.mp hxVC with ⟨R₁, hR₁, hxR₁⟩
        exact Finset.disjoint_left.mp (hC_closed R₁ hR₁ R hR) hxR₁ hxR)
      have hdisje : Disjoint e VC := hdisjR.mono_left heR
      have hnotC : ¬ ∃ R₁ ∈ C, e ⊆ R₁ := fun ⟨R₁, hR₁, heR₁⟩ => by
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(hMm.1 e heM).1]; decide)
        exact Finset.disjoint_left.mp hdisje hx (Finset.mem_biUnion.mpr ⟨R₁, hR₁, heR₁ hx⟩)
      have he_in : e ∈ proj M := by
        refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heM, hnotC⟩, if_pos hdisje⟩
      exact ⟨e, he_in, heR⟩
    rw [← Finset.sum_fiberwise_of_maps_to (fun M hM => (hproj_mem M hM).1), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun M' hM' => ?_)
    have hM'm := (Finset.mem_filter.mp hM').2.1
    have hM'hit := (Finset.mem_filter.mp hM').2.2.2
    by_cases hv0_in : v₀ ∈ M'.biUnion id
    · rcases Finset.mem_biUnion.mp hv0_in with ⟨e₀, he₀M', hv0e₀⟩
      obtain ⟨a, b, hab, he₀_eq⟩ := Finset.card_eq_two.mp (hM'm.1 e₀ he₀M').1
      have hex_w : ∃ w ∈ V \ VC, e₀ = {v₀, w} := by
        rcases Finset.mem_insert.mp (he₀_eq ▸ hv0e₀) with rfl | hb
        · have hbV' : b ∈ V' := (hM'm.1 e₀ he₀M').2 (he₀_eq ▸ by simp)
          rcases Finset.mem_insert.mp hbV' with rfl | hb'
          · exact absurd rfl hab
          · exact ⟨b, hb', he₀_eq⟩
        · obtain rfl : v₀ = b := Finset.mem_singleton.mp hb
          have haV' : a ∈ V' := (hM'm.1 e₀ he₀M').2 (he₀_eq ▸ by simp)
          rcases Finset.mem_insert.mp haV' with rfl | ha'
          · exact absurd rfl hab
          · exact ⟨a, ha', he₀_eq.trans (Finset.pair_comm _ _)⟩
      rcases hex_w with ⟨w, hw, he₀_vw⟩
      let S_fib := VC.sigma (fun u => MCs u)
      have hfib : ∑ M ∈ All.filter (fun M => proj M = M'),
            ((∏ x ∈ V \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card =
          ∑ p ∈ S_fib,
            ((∏ x ∈ V' \ M'.biUnion id, (vw x : ℂ)) *
              ((∏ e ∈ M'.erase e₀, (ew e : ℂ)) * (ew {p.1, w} : ℂ) * (∏ e ∈ p.2, (ew e : ℂ)))) *
            z ^ (C.card + M'.card) := by
        refine Finset.sum_bij (fun M hM =>
          let hu := (hproj_mem M (Finset.mem_filter.mp hM).1).2
          ⟨Classical.choose hu, M.filter (fun e => ∃ R ∈ C, e ⊆ R)⟩) ?_ ?_ ?_ ?_
        · intro M hM
          have hspec := Classical.choose_spec (hproj_mem M (Finset.mem_filter.mp hM).1).2
          exact Finset.mem_sigma.mpr ⟨hspec.1, hspec.2⟩
        · intro M₁ h1 M₂ h2 heq
          have h1a := (Finset.mem_filter.mp h1).1
          have h2a := (Finset.mem_filter.mp h2).1
          have hp1 := (Finset.mem_filter.mp h1).2
          have hp2 := (Finset.mem_filter.mp h2).2
          have hMCeq : M₁.filter (fun e => ∃ R ∈ C, e ⊆ R) = M₂.filter (fun e => ∃ R ∈ C, e ⊆ R) := by
            have := congrArg Sigma.snd heq; simpa using this
          have hueq : Classical.choose (hproj_mem M₁ h1a).2 = Classical.choose (hproj_mem M₂ h2a).2 :=
            congrArg Sigma.fst heq
          set u := Classical.choose (hproj_mem M₁ h1a).2
          have hu1 := (Finset.mem_filter.mp (Classical.choose_spec (hproj_mem M₁ h1a).2).2).2.2.2
          have hu2 := (Finset.mem_filter.mp (Classical.choose_spec (hproj_mem M₂ h2a).2).2).2.2.2
          rw [← hueq] at hu2
          have hrest_eq : ∀ M (hMa : M ∈ All) (hpr : proj M = M')
              (huM : VC \ (M.filter (fun e => ∃ R ∈ C, e ⊆ R)).biUnion id = {u}),
              M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R) = insert {u, w} (M'.erase e₀) := by
            intro M hMa hpr huM
            have hMm := (Finset.mem_filter.mp hMa).2.1
            have hrest_disj : ∀ e ∈ M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R),
                (Disjoint e VC ∧ e ∈ M'.erase e₀) ∨ e = {u, w} := by
              intro e he
              have him : (if Disjoint e VC then e else insert v₀ (e \ VC)) ∈ M' :=
                hpr ▸ Finset.mem_image.mpr ⟨e, he, rfl⟩
              by_cases hd : Disjoint e VC
              · rw [if_pos hd] at him
                left
                refine ⟨hd, Finset.mem_erase.mpr ⟨fun h => ?_, him⟩⟩
                exact Finset.disjoint_left.mp hd (h ▸ he₀_vw ▸ by simp) hv₀
              · right
                rw [if_neg hd] at him
                have heq_e0 : insert v₀ (e \ VC) = e₀ := by
                  by_contra hne
                  exact Finset.disjoint_left.mp (hM'm.2 _ him e₀ he₀M' hne)
                    (Finset.mem_insert_self _ _) (he₀_vw ▸ by simp)
                have hsdiff_w : e \ VC = {w} := by
                  have h1 : (insert v₀ (e \ VC)).erase v₀ = e₀.erase v₀ := congrArg (·.erase v₀) heq_e0
                  have hnv0 : v₀ ∉ e \ VC := fun h => (Finset.mem_sdiff.mp h).2 hv₀
                  rw [Finset.erase_insert hnv0, he₀_vw] at h1
                  have hne : w ≠ v₀ := fun h => (Finset.mem_sdiff.mp hw).2 (h ▸ hv₀)
                  rw [h1]; ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
                  constructor
                  · rintro ⟨hx0, rfl | rfl⟩
                    · exact absurd rfl hx0
                    · rfl
                  · rintro rfl; exact ⟨hne, Or.inr rfl⟩
                have hinter_u : e ∩ VC = {u} := by
                  have hsub : e ∩ VC ⊆ {u} := fun x hx => by
                    rw [← huM, Finset.mem_sdiff]
                    refine ⟨(Finset.mem_inter.mp hx).2, fun hxin => ?_⟩
                    rcases Finset.mem_biUnion.mp hxin with ⟨e', he', hxe'⟩
                    have hne : e ≠ e' := fun h => (Finset.mem_filter.mp he).2 (h ▸ (Finset.mem_filter.mp he').2)
                    exact Finset.disjoint_left.mp (hMm.2 e (Finset.mem_filter.mp he).1 e'
                      (Finset.mem_filter.mp he').1 hne) (Finset.mem_inter.mp hx).1 hxe'
                  have hne_i : (e ∩ VC).Nonempty := Finset.not_disjoint_iff.mp hd |>
                    fun ⟨x, h1, h2⟩ => ⟨x, Finset.mem_inter.mpr ⟨h1, h2⟩⟩
                  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; exact hne_i.card_pos)
                ext x
                have hx : x ∈ e ↔ x ∈ e ∩ VC ∨ x ∈ e \ VC := by simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
                rw [hx, hinter_u, hsdiff_w]; simp only [Finset.mem_insert, Finset.mem_singleton]
            ext e
            simp only [Finset.mem_insert]
            constructor
            · intro he
              rcases hrest_disj e he with ⟨_, hmem⟩ | rfl
              · right; exact hmem
              · left; rfl
            · rintro (rfl | he)
              · have he₀_in : e₀ ∈ proj M := hpr.symm ▸ he₀M'
                rcases Finset.mem_image.mp he₀_in with ⟨e', he', heq'⟩
                rcases hrest_disj e' he' with ⟨hd, hmem⟩ | rfl
                · rw [if_pos hd] at heq'
                  exact absurd heq' (Finset.ne_of_mem_erase hmem)
                · exact he'
              · have he_in : e ∈ proj M := hpr.symm ▸ Finset.mem_of_mem_erase he
                rcases Finset.mem_image.mp he_in with ⟨e', he', heq'⟩
                rcases hrest_disj e' he' with ⟨hd, _⟩ | rfl
                · rw [if_pos hd] at heq'; exact heq' ▸ he'
                · exfalso
                  have hnd : ¬ Disjoint ({u, w} : Finset α) VC := fun hd =>
                    Finset.disjoint_left.mp hd (by simp)
                      (Finset.mem_sdiff.mp (huM ▸ Finset.mem_singleton_self u)).1
                  rw [if_neg hnd] at heq'
                  have hv0_e : v₀ ∈ e := heq' ▸ Finset.mem_insert_self _ _
                  exact Finset.disjoint_left.mp (hM'm.2 e (Finset.mem_of_mem_erase he) e₀ he₀M'
                    (Finset.ne_of_mem_erase he)) hv0_e (he₀_vw ▸ by simp)
          have hr1 := hrest_eq M₁ h1a hp1 hu1
          have hr2 := hrest_eq M₂ h2a hp2 hu2
          rw [← Finset.filter_union_filter_not_eq (fun e => ∃ R ∈ C, e ⊆ R) M₁,
              ← Finset.filter_union_filter_not_eq (fun e => ∃ R ∈ C, e ⊆ R) M₂,
              hMCeq, hr1, hr2]
        · intro p hp
          rcases Finset.mem_sigma.mp hp with ⟨huVC, hMC⟩
          have hMCm := mem_matchingsOn.mp (Finset.mem_filter.mp hMC).1
          have hMCin := (Finset.mem_filter.mp hMC).2.1
          have hMChit := (Finset.mem_filter.mp hMC).2.2.1
          have hMCrem := (Finset.mem_filter.mp hMC).2.2.2
          let M := p.2 ∪ insert {p.1, w} (M'.erase e₀)
          have hu_not_MC : p.1 ∉ p.2.biUnion id :=
            (Finset.mem_sdiff.mp (hMCrem ▸ Finset.mem_singleton_self p.1)).2
          have hw_ne_u : p.1 ≠ w := fun h => (Finset.mem_sdiff.mp hw).2 (h ▸ huVC)
          have hM'_er_sub : ∀ e ∈ M'.erase e₀, e ⊆ V \ VC := fun e he x hx => by
            have hxV' := (hM'm.1 e (Finset.mem_of_mem_erase he)).2 hx
            rcases Finset.mem_insert.mp hxV' with rfl | hx'
            · exact absurd (Finset.disjoint_left.mp (hM'm.2 e (Finset.mem_of_mem_erase he) e₀ he₀M'
                (Finset.ne_of_mem_erase he)) hx (he₀_vw ▸ by simp)) id
            · exact hx'
          have hM_m : IsMatching V M := ⟨fun e he => by
            rcases Finset.mem_union.mp he with h1 | h2
            · exact ⟨(hMCm.1 e h1).1, (hMCm.1 e h1).2.trans hVC_sub⟩
            · rcases Finset.mem_insert.mp h2 with rfl | h2'
              · exact ⟨Finset.card_pair hw_ne_u, fun x hx => by
                  rcases Finset.mem_insert.mp hx with rfl | hx
                  · exact hVC_sub huVC
                  · rw [Finset.mem_singleton.mp hx]; exact (Finset.mem_sdiff.mp hw).1⟩
              · exact ⟨(hM'm.1 e (Finset.mem_of_mem_erase h2')).1,
                  (hM'_er_sub e h2').trans Finset.sdiff_subset⟩,
            fun e₁ h1 e₂ h2 hne => by
              have hdisj_er_VC : ∀ e ∈ M'.erase e₀, Disjoint e VC := fun e he =>
                (Finset.subset_sdiff.mp (hM'_er_sub e he)).2
              have hdisj_er_w : ∀ e ∈ M'.erase e₀, w ∉ e := fun e he hwe =>
                Finset.disjoint_left.mp (hM'm.2 e (Finset.mem_of_mem_erase he) e₀ he₀M'
                  (Finset.ne_of_mem_erase he)) hwe (he₀_vw ▸ by simp)
              have hdisj_MC_uw : ∀ e ∈ p.2, Disjoint e {p.1, w} := fun e he => by
                rw [Finset.disjoint_left]; intro x hxe hxuw
                rcases Finset.mem_insert.mp hxuw with rfl | hxuw
                · exact hu_not_MC (Finset.mem_biUnion.mpr ⟨e, he, hxe⟩)
                · rw [Finset.mem_singleton.mp hxuw] at hxe
                  exact (Finset.mem_sdiff.mp hw).2 ((hMCm.1 e he).2 hxe)
              rcases Finset.mem_union.mp h1 with h1 | h1 <;> rcases Finset.mem_union.mp h2 with h2 | h2
              · exact hMCm.2 e₁ h1 e₂ h2 hne
              · rcases Finset.mem_insert.mp h2 with rfl | h2'
                · exact hdisj_MC_uw e₁ h1
                · exact (hdisj_er_VC e₂ h2').symm.mono_left (hMCm.1 e₁ h1).2
              · rcases Finset.mem_insert.mp h1 with rfl | h1'
                · exact (hdisj_MC_uw e₂ h2).symm
                · exact (hdisj_er_VC e₁ h1').mono_right (hMCm.1 e₂ h2).2
              · rcases Finset.mem_insert.mp h1 with rfl | h1' <;> rcases Finset.mem_insert.mp h2 with rfl | h2'
                · exact absurd rfl hne
                · rw [Finset.disjoint_left]; intro x hx1 hx2
                  rcases Finset.mem_insert.mp hx1 with rfl | hx1
                  · exact Finset.disjoint_left.mp (hdisj_er_VC e₂ h2') hx2 huVC
                  · rw [Finset.mem_singleton.mp hx1] at hx2; exact hdisj_er_w e₂ h2' hx2
                · rw [Finset.disjoint_right]; intro x hx2 hx1
                  rcases Finset.mem_insert.mp hx2 with rfl | hx2
                  · exact Finset.disjoint_left.mp (hdisj_er_VC e₁ h1') hx1 huVC
                  · rw [Finset.mem_singleton.mp hx2] at hx1; exact hdisj_er_w e₁ h1' hx1
                · exact hM'm.2 e₁ (Finset.mem_of_mem_erase h1') e₂ (Finset.mem_of_mem_erase h2') hne⟩
          have hM_in_All : M ∈ All := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
            (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hM_m.1 e he).2, (hM_m.1 e he).1⟩),
            hM_m, Finset.empty_subset _, fun R hR => by
              by_cases hRC : R ∈ C
              · obtain ⟨e, he, heR⟩ := hMChit R hRC; exact ⟨e, Finset.mem_union_left _ he, heR⟩
              · obtain ⟨e, he, heR⟩ := hM'hit R (Finset.mem_sdiff.mpr ⟨hR, hRC⟩)
                have hne : e ≠ e₀ := fun h => by
                  have hv0R : v₀ ∈ R := heR (h ▸ he₀_vw ▸ by simp)
                  rcases Finset.mem_biUnion.mp hv₀ with ⟨R₁, hR₁, hv0R₁⟩
                  exact Finset.disjoint_left.mp (hC_closed R₁ hR₁ R (Finset.mem_sdiff.mpr ⟨hR, hRC⟩)) hv0R₁ hv0R
                exact ⟨e, Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, he⟩)), heR⟩⟩
          have hfilt_MC : M.filter (fun e => ∃ R ∈ C, e ⊆ R) = p.2 := by
            ext e; simp only [M, Finset.mem_filter, Finset.mem_union, Finset.mem_insert]
            constructor
            · rintro ⟨h1 | rfl | h2, hex⟩
              · exact h1
              · exfalso; rcases hex with ⟨R, hR, heR⟩
                exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_biUnion.mpr ⟨R, hR, heR (by simp)⟩)
              · exfalso; rcases hex with ⟨R, hR, heR⟩
                obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(hM'm.1 e (Finset.mem_of_mem_erase h2)).1]; decide)
                exact (Finset.mem_sdiff.mp (hM'_er_sub e h2 hx)).2 (Finset.mem_biUnion.mpr ⟨R, hR, heR hx⟩)
            · intro h1; exact ⟨Or.inl h1, hMCin e h1⟩
          have hfilt_rest : M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R) = insert {p.1, w} (M'.erase e₀) := by
            ext e; simp only [M, Finset.mem_filter, Finset.mem_union, Finset.mem_insert]
            constructor
            · rintro ⟨h1 | h2, hnot⟩
              · exact absurd (hMCin e h1) hnot
              · exact h2
            · rintro (rfl | h2)
              · exact ⟨Or.inr (Or.inl rfl), fun ⟨R, hR, heR⟩ =>
                  (Finset.mem_sdiff.mp hw).2 (Finset.mem_biUnion.mpr ⟨R, hR, heR (by simp)⟩)⟩
              · refine ⟨Or.inr (Or.inr h2), fun ⟨R, hR, heR⟩ => ?_⟩
                obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(hM'm.1 e (Finset.mem_of_mem_erase h2)).1]; decide)
                exact (Finset.mem_sdiff.mp (hM'_er_sub e h2 hx)).2 (Finset.mem_biUnion.mpr ⟨R, hR, heR hx⟩)
          have hproj_eq : proj M = M' := by
            unfold proj; rw [hfilt_rest, Finset.image_insert]
            have hnd : ¬ Disjoint ({p.1, w} : Finset α) VC := fun hd =>
              Finset.disjoint_left.mp hd (by simp) huVC
            have hsdiff : ({p.1, w} : Finset α) \ VC = {w} := by
              ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, hx⟩
                · exact absurd huVC hx
                · rfl
              · rintro rfl; exact ⟨Or.inr rfl, (Finset.mem_sdiff.mp hw).2⟩
            have him : (M'.erase e₀).image (fun e => if Disjoint e VC then e else insert v₀ (e \ VC)) = M'.erase e₀ := by
              conv_rhs => rw [← Finset.image_id (s := M'.erase e₀)]
              refine Finset.image_congr (fun e he => ?_)
              exact if_pos (Finset.subset_sdiff.mp (hM'_er_sub e he)).2
            rw [if_neg hnd, hsdiff, him, ← he₀_vw, Finset.insert_erase he₀M']
          refine ⟨M, Finset.mem_filter.mpr ⟨hM_in_All, hproj_eq⟩, ?_⟩
          have hch_eq : Classical.choose (hproj_mem M hM_in_All).2 = p.1 := by
            have hspec := Classical.choose_spec (hproj_mem M hM_in_All).2
            have hrem := (Finset.mem_filter.mp hspec.2).2.2.2
            have hrem' : ({p.1} : Finset α) = {Classical.choose (hproj_mem M hM_in_All).2} := by
              calc ({p.1} : Finset α) = VC \ p.2.biUnion id := hMCrem.symm
                _ = VC \ (M.filter (fun e => ∃ R ∈ C, e ⊆ R)).biUnion id := by rw [hfilt_MC]
                _ = {Classical.choose (hproj_mem M hM_in_All).2} := hrem
            exact Finset.singleton_injective hrem'.symm
          apply Sigma.ext hch_eq
          simp [hfilt_MC]
        · intro M hM
          have hMa := (Finset.mem_filter.mp hM).1
          have hpr := (Finset.mem_filter.mp hM).2
          have hMm := (Finset.mem_filter.mp hMa).2.1
          have hhit := (Finset.mem_filter.mp hMa).2.2.2
          have hC := hhit_C_card M hMm (fun R hR => hhit R (hC_sub hR))
          set u := Classical.choose (hproj_mem M hMa).2
          have hu_spec := Classical.choose_spec (hproj_mem M hMa).2
          have hu_rem := (Finset.mem_filter.mp hu_spec.2).2.2.2
          set MC := M.filter (fun e => ∃ R ∈ C, e ⊆ R)
          set Mrest := M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R)
          have hrest_eq : Mrest = insert {u, w} (M'.erase e₀) := by
            have hrest_disj : ∀ e ∈ Mrest, (Disjoint e VC ∧ e ∈ M'.erase e₀) ∨ e = {u, w} := by
              intro e he
              have him : (if Disjoint e VC then e else insert v₀ (e \ VC)) ∈ M' :=
                hpr ▸ Finset.mem_image.mpr ⟨e, he, rfl⟩
              by_cases hd : Disjoint e VC
              · rw [if_pos hd] at him
                exact Or.inl ⟨hd, Finset.mem_erase.mpr ⟨fun h =>
                  Finset.disjoint_left.mp hd (h ▸ he₀_vw ▸ by simp) hv₀, him⟩⟩
              · right; rw [if_neg hd] at him
                have heq_e0 : insert v₀ (e \ VC) = e₀ := by
                  by_contra hne
                  exact Finset.disjoint_left.mp (hM'm.2 _ him e₀ he₀M' hne)
                    (Finset.mem_insert_self _ _) (he₀_vw ▸ by simp)
                have hsdiff_w : e \ VC = {w} := by
                  have h1 := congrArg (·.erase v₀) heq_e0
                  rw [Finset.erase_insert (fun h => (Finset.mem_sdiff.mp h).2 hv₀), he₀_vw] at h1
                  have hne : w ≠ v₀ := fun h => (Finset.mem_sdiff.mp hw).2 (h ▸ hv₀)
                  rw [h1]; ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
                  constructor
                  · rintro ⟨hx0, rfl | rfl⟩
                    · exact absurd rfl hx0
                    · rfl
                  · rintro rfl; exact ⟨hne, Or.inr rfl⟩
                have hinter_u : e ∩ VC = {u} := by
                  have hsub : e ∩ VC ⊆ {u} := fun x hx => by
                    rw [← hu_rem, Finset.mem_sdiff]
                    refine ⟨(Finset.mem_inter.mp hx).2, fun hxin => ?_⟩
                    rcases Finset.mem_biUnion.mp hxin with ⟨e', he', hxe'⟩
                    have hne : e ≠ e' := fun h => (Finset.mem_filter.mp he).2 (h ▸ (Finset.mem_filter.mp he').2)
                    exact Finset.disjoint_left.mp (hMm.2 e (Finset.mem_filter.mp he).1 e'
                      (Finset.mem_filter.mp he').1 hne) (Finset.mem_inter.mp hx).1 hxe'
                  have hne_i : (e ∩ VC).Nonempty := Finset.not_disjoint_iff.mp hd |>
                    fun ⟨x, h1, h2⟩ => ⟨x, Finset.mem_inter.mpr ⟨h1, h2⟩⟩
                  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; exact hne_i.card_pos)
                ext x
                have hx : x ∈ e ↔ x ∈ e ∩ VC ∨ x ∈ e \ VC := by simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
                rw [hx, hinter_u, hsdiff_w]; simp only [Finset.mem_insert, Finset.mem_singleton]
            ext e; simp only [Finset.mem_insert]
            constructor
            · intro he
              rcases hrest_disj e he with ⟨_, hmem⟩ | rfl
              · right; exact hmem
              · left; rfl
            · rintro (rfl | he)
              · rcases Finset.mem_image.mp (hpr.symm ▸ he₀M') with ⟨e', he', heq'⟩
                rcases hrest_disj e' he' with ⟨hd, hmem⟩ | rfl
                · rw [if_pos hd] at heq'; exact absurd heq' (Finset.ne_of_mem_erase hmem)
                · exact he'
              · rcases Finset.mem_image.mp (hpr.symm ▸ Finset.mem_of_mem_erase he) with ⟨e', he', heq'⟩
                rcases hrest_disj e' he' with ⟨hd, _⟩ | rfl
                · rw [if_pos hd] at heq'; exact heq' ▸ he'
                · exfalso
                  have hnd : ¬ Disjoint ({u, w} : Finset α) VC := fun hd =>
                    Finset.disjoint_left.mp hd (by simp : u ∈ ({u, w} : Finset α)) hu_spec.1
                  rw [if_neg hnd] at heq'
                  exact Finset.disjoint_left.mp (hM'm.2 e (Finset.mem_of_mem_erase he) e₀ he₀M'
                    (Finset.ne_of_mem_erase he)) (heq' ▸ Finset.mem_insert_self _ _) (he₀_vw ▸ by simp)
          have hpart : M = MC ∪ Mrest := (Finset.filter_union_filter_not_eq _ M).symm
          have hdisj : Disjoint MC Mrest := Finset.disjoint_filter_filter_not M M _
          have huw_not : ({u, w} : Finset α) ∉ M'.erase e₀ := fun h => by
            have hw1 : w ∈ ({u, w} : Finset α) := by simp
            have hw2 : w ∈ e₀ := by rw [he₀_vw]; simp
            exact Finset.disjoint_left.mp (hM'm.2 {u, w} (Finset.mem_of_mem_erase h) e₀ he₀M'
              (Finset.ne_of_mem_erase h)) hw1 hw2
          have hsdiff : V \ M.biUnion id = V' \ M'.biUnion id := by
            have hbi_M' : M'.biUnion id = ({v₀, w} : Finset α) ∪ (M'.erase e₀).biUnion id := by
              conv_lhs => rw [← Finset.insert_erase he₀M', Finset.biUnion_insert]
              simp only [id_eq, he₀_vw]
            rw [hpart, hrest_eq, Finset.union_biUnion, Finset.biUnion_insert, hbi_M']
            ext x
            simp only [V', Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, id_eq]
            have hVC_cov : ∀ y ∈ VC, y ∈ MC.biUnion id ∨ y = u := fun y hy => by
              by_cases h : y ∈ MC.biUnion id
              · left; exact h
              · right; exact Finset.mem_singleton.mp (hu_rem ▸ Finset.mem_sdiff.mpr ⟨hy, h⟩)
            constructor
            · rintro ⟨hxV, hno⟩
              push_neg at hno
              have hnotVC : x ∉ VC := fun hxVC => by
                rcases hVC_cov x hxVC with h1 | rfl
                · exact hno.1 h1
                · exact hno.2.1.1 rfl
              refine ⟨Or.inr ⟨hxV, hnotVC⟩, ?_⟩
              rintro ((rfl | rfl) | h3)
              · exact hnotVC hv₀
              · exact hno.2.1.2 rfl
              · exact hno.2.2 h3
            · rintro ⟨rfl | ⟨hxV, hnotVC⟩, hno⟩
              · exact absurd (Or.inl (Or.inl rfl)) hno
              · refine ⟨hxV, ?_⟩
                rintro (h1 | (rfl | rfl) | h3)
                · exact hnotVC (hC.2.1 h1)
                · exact hnotVC hu_spec.1
                · exact hno (Or.inl (Or.inr rfl))
                · exact hno (Or.inr h3)
          have hprod : ∏ e ∈ M, (ew e : ℂ) =
              (∏ e ∈ M'.erase e₀, (ew e : ℂ)) * (ew {u, w} : ℂ) * (∏ e ∈ MC, (ew e : ℂ)) := by
            rw [hpart, Finset.prod_union hdisj, hrest_eq, Finset.prod_insert huw_not]; ring
          have hcard : M.card = C.card + M'.card := by
            rw [hpart, Finset.card_union_of_disjoint hdisj, hC.1, hrest_eq,
                Finset.card_insert_of_notMem huw_not, Finset.card_erase_add_one he₀M']
          rw [hsdiff, hprod, hcard]
      rw [hfib, Finset.sum_sigma]
      have hvw_eq : ∏ x ∈ V' \ M'.biUnion id, (vw' x : ℂ) = ∏ x ∈ V' \ M'.biUnion id, (vw x : ℂ) :=
        Finset.prod_congr rfl (fun x hx => by
          have hne : x ≠ v₀ := fun h => (Finset.mem_sdiff.mp hx).2 (h ▸ hv0_in)
          simp [vw', hne])
      have hew_eq : ∏ e ∈ M', (ew' e : ℂ) =
          (∏ e ∈ M'.erase e₀, (ew e : ℂ)) * (∑ u ∈ VC, (cu u : ℂ) * (ew {u, w} : ℂ)) := by
        rw [← Finset.mul_prod_erase M' (fun e => (ew' e : ℂ)) he₀M']
        have h1 : (ew' e₀ : ℂ) = ∑ u ∈ VC, (cu u : ℂ) * (ew {u, w} : ℂ) := by
          rw [he₀_vw, hew'_pair w hw]; push_cast; rfl
        have h2 : ∏ e ∈ M'.erase e₀, (ew' e : ℂ) = ∏ e ∈ M'.erase e₀, (ew e : ℂ) :=
          Finset.prod_congr rfl (fun e he => by
            have hnv0 : v₀ ∉ e := fun hv0e =>
              Finset.disjoint_left.mp (hM'm.2 e (Finset.mem_of_mem_erase he) e₀ he₀M'
                (Finset.ne_of_mem_erase he)) hv0e (he₀_vw ▸ by simp)
            rw [hew'_other e hnv0])
        rw [h1, h2, mul_comm]
      rw [hvw_eq, hew_eq]
      simp only [cu, Complex.ofReal_sum, Complex.ofReal_prod, Finset.sum_mul, Finset.mul_sum, pow_add]
      refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun MC _ => by ring))
    · let S_fib := VC.sigma (fun u => MCs u)
      have hfib : ∑ M ∈ All.filter (fun M => proj M = M'),
            ((∏ x ∈ V \ M.biUnion id, (vw x : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card =
          ∑ p ∈ S_fib,
            ((∏ x ∈ (V' \ M'.biUnion id).erase v₀, (vw x : ℂ)) * (vw p.1 : ℂ) *
              ((∏ e ∈ M', (ew e : ℂ)) * (∏ e ∈ p.2, (ew e : ℂ)))) *
            z ^ (C.card + M'.card) := by
        refine Finset.sum_bij (fun M hM =>
          let hu := (hproj_mem M (Finset.mem_filter.mp hM).1).2
          ⟨Classical.choose hu, M.filter (fun e => ∃ R ∈ C, e ⊆ R)⟩) ?_ ?_ ?_ ?_
        · intro M hM
          have hspec := Classical.choose_spec (hproj_mem M (Finset.mem_filter.mp hM).1).2
          exact Finset.mem_sigma.mpr ⟨hspec.1, hspec.2⟩
        · intro M₁ h1 M₂ h2 heq
          have h1a := (Finset.mem_filter.mp h1).1
          have h2a := (Finset.mem_filter.mp h2).1
          have hp1 := (Finset.mem_filter.mp h1).2
          have hp2 := (Finset.mem_filter.mp h2).2
          have hMCeq : M₁.filter (fun e => ∃ R ∈ C, e ⊆ R) = M₂.filter (fun e => ∃ R ∈ C, e ⊆ R) := by
            have := congrArg Sigma.snd heq; simpa using this
          have hrest_eq : ∀ M (hpr : proj M = M'),
              M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R) = M' := by
            intro M hpr
            have hall_disj : ∀ e ∈ M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R), Disjoint e VC := by
              intro e he
              by_contra hnd
              have hv0_im : insert v₀ (e \ VC) ∈ M' := hpr ▸ Finset.mem_image.mpr ⟨e, he, if_neg hnd⟩
              exact hv0_in (Finset.mem_biUnion.mpr ⟨_, hv0_im, Finset.mem_insert_self _ _⟩)
            rw [← hpr]; unfold proj
            conv_lhs => rw [← Finset.image_id (s := M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R))]
            exact (Finset.image_congr (fun e he => if_pos (hall_disj e he))).symm
          rw [← Finset.filter_union_filter_not_eq (fun e => ∃ R ∈ C, e ⊆ R) M₁,
              ← Finset.filter_union_filter_not_eq (fun e => ∃ R ∈ C, e ⊆ R) M₂,
              hMCeq, hrest_eq M₁ hp1, hrest_eq M₂ hp2]
        · intro p hp
          rcases Finset.mem_sigma.mp hp with ⟨huVC, hMC⟩
          have hMCm := mem_matchingsOn.mp (Finset.mem_filter.mp hMC).1
          have hMCin := (Finset.mem_filter.mp hMC).2.1
          have hMChit := (Finset.mem_filter.mp hMC).2.2.1
          have hMCrem := (Finset.mem_filter.mp hMC).2.2.2
          have hM'_sub : ∀ e ∈ M', e ⊆ V \ VC := fun e he x hx => by
            have hxV' := (hM'm.1 e he).2 hx
            rcases Finset.mem_insert.mp hxV' with rfl | hx'
            · exact absurd (Finset.mem_biUnion.mpr ⟨e, he, hx⟩) hv0_in
            · exact hx'
          let M := p.2 ∪ M'
          have hM_m : IsMatching V M := ⟨fun e he => by
            rcases Finset.mem_union.mp he with h1 | h2
            · exact ⟨(hMCm.1 e h1).1, (hMCm.1 e h1).2.trans hVC_sub⟩
            · exact ⟨(hM'm.1 e h2).1, (hM'_sub e h2).trans Finset.sdiff_subset⟩,
            fun e₁ h1 e₂ h2 hne => by
              rcases Finset.mem_union.mp h1 with h1' | h1' <;> rcases Finset.mem_union.mp h2 with h2' | h2'
              · exact hMCm.2 e₁ h1' e₂ h2' hne
              · exact (Finset.subset_sdiff.mp (hM'_sub e₂ h2')).2.symm.mono_left (hMCm.1 e₁ h1').2
              · exact (Finset.subset_sdiff.mp (hM'_sub e₁ h1')).2.mono_right (hMCm.1 e₂ h2').2
              · exact hM'm.2 e₁ h1' e₂ h2' hne⟩
          have hM_in_All : M ∈ All := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
            (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hM_m.1 e he).2, (hM_m.1 e he).1⟩),
            hM_m, Finset.empty_subset _, fun R hR => by
              by_cases hRC : R ∈ C
              · obtain ⟨e, he, heR⟩ := hMChit R hRC; exact ⟨e, Finset.mem_union_left _ he, heR⟩
              · obtain ⟨e, he, heR⟩ := hM'hit R (Finset.mem_sdiff.mpr ⟨hR, hRC⟩)
                exact ⟨e, Finset.mem_union_right _ he, heR⟩⟩
          have hfilt_MC : M.filter (fun e => ∃ R ∈ C, e ⊆ R) = p.2 := by
            ext e; simp only [M, Finset.mem_filter, Finset.mem_union]
            constructor
            · rintro ⟨h1 | h2, hex⟩
              · exact h1
              · exfalso; rcases hex with ⟨R, hR, heR⟩
                obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(hM'm.1 e h2).1]; decide)
                exact (Finset.mem_sdiff.mp (hM'_sub e h2 hx)).2 (Finset.mem_biUnion.mpr ⟨R, hR, heR hx⟩)
            · intro h1; exact ⟨Or.inl h1, hMCin e h1⟩
          have hfilt_rest : M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R) = M' := by
            ext e; simp only [M, Finset.mem_filter, Finset.mem_union]
            constructor
            · rintro ⟨h1 | h2, hnot⟩
              · exact absurd (hMCin e h1) hnot
              · exact h2
            · intro h2; refine ⟨Or.inr h2, fun ⟨R, hR, heR⟩ => ?_⟩
              obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [(hM'm.1 e h2).1]; decide)
              exact (Finset.mem_sdiff.mp (hM'_sub e h2 hx)).2 (Finset.mem_biUnion.mpr ⟨R, hR, heR hx⟩)
          have hproj_eq : proj M = M' := by
            unfold proj; rw [hfilt_rest]
            conv_rhs => rw [← Finset.image_id (s := M')]
            exact Finset.image_congr (fun e he => if_pos (Finset.subset_sdiff.mp (hM'_sub e he)).2)
          refine ⟨M, Finset.mem_filter.mpr ⟨hM_in_All, hproj_eq⟩, ?_⟩
          have hch_eq : Classical.choose (hproj_mem M hM_in_All).2 = p.1 := by
            have hspec := Classical.choose_spec (hproj_mem M hM_in_All).2
            have hrem := (Finset.mem_filter.mp hspec.2).2.2.2
            have hrem' : ({p.1} : Finset α) = {Classical.choose (hproj_mem M hM_in_All).2} := by
              calc ({p.1} : Finset α) = VC \ p.2.biUnion id := hMCrem.symm
                _ = VC \ (M.filter (fun e => ∃ R ∈ C, e ⊆ R)).biUnion id := by rw [hfilt_MC]
                _ = {Classical.choose (hproj_mem M hM_in_All).2} := hrem
            exact Finset.singleton_injective hrem'.symm
          apply Sigma.ext hch_eq
          simp [hfilt_MC]
        · intro M hM
          have hMa := (Finset.mem_filter.mp hM).1
          have hpr := (Finset.mem_filter.mp hM).2
          have hMm := (Finset.mem_filter.mp hMa).2.1
          have hhit := (Finset.mem_filter.mp hMa).2.2.2
          have hC := hhit_C_card M hMm (fun R hR => hhit R (hC_sub hR))
          set u := Classical.choose (hproj_mem M hMa).2
          have hu_spec := Classical.choose_spec (hproj_mem M hMa).2
          have hu_rem := (Finset.mem_filter.mp hu_spec.2).2.2.2
          set MC := M.filter (fun e => ∃ R ∈ C, e ⊆ R)
          set Mrest := M.filter (fun e => ¬ ∃ R ∈ C, e ⊆ R)
          have hrest_eq : Mrest = M' := by
            have hall_disj : ∀ e ∈ Mrest, Disjoint e VC := fun e he => by
              by_contra hnd
              have hv0_im : insert v₀ (e \ VC) ∈ M' := hpr ▸ Finset.mem_image.mpr ⟨e, he, if_neg hnd⟩
              exact hv0_in (Finset.mem_biUnion.mpr ⟨_, hv0_im, Finset.mem_insert_self _ _⟩)
            rw [← hpr]; unfold proj
            conv_lhs => rw [← Finset.image_id (s := Mrest)]
            exact (Finset.image_congr (fun e he => if_pos (hall_disj e he))).symm
          have hpart : M = MC ∪ Mrest := (Finset.filter_union_filter_not_eq _ M).symm
          have hdisj : Disjoint MC Mrest := Finset.disjoint_filter_filter_not M M _
          have hsdiff : V \ M.biUnion id = insert u ((V' \ M'.biUnion id).erase v₀) := by
            rw [hpart, hrest_eq, Finset.union_biUnion]
            ext x
            simp only [V', Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
            have hVC_cov : ∀ y ∈ VC, y ∈ MC.biUnion id ∨ y = u := fun y hy => by
              by_cases h : y ∈ MC.biUnion id
              · left; exact h
              · right; exact Finset.mem_singleton.mp (hu_rem ▸ Finset.mem_sdiff.mpr ⟨hy, h⟩)
            constructor
            · rintro ⟨hxV, hno⟩
              push_neg at hno
              by_cases hxVC : x ∈ VC
              · left; exact (hVC_cov x hxVC).resolve_left hno.1
              · right; exact ⟨fun h => hxVC (h ▸ hv₀), Or.inr ⟨hxV, hxVC⟩, hno.2⟩
            · rintro (rfl | ⟨hne0, rfl | ⟨hxV, hxnotVC⟩, hnotM'⟩)
              · refine ⟨hVC_sub hu_spec.1, fun h => ?_⟩
                rcases h with h1 | h2
                · exact (Finset.mem_sdiff.mp (hu_rem ▸ Finset.mem_singleton_self u)).2 h1
                · rcases Finset.mem_biUnion.mp h2 with ⟨e, he, hue⟩
                  have hdisj_e : Disjoint e VC := by
                    by_contra hnd
                    have hv0_im : insert v₀ (e \ VC) ∈ M' := by
                      have he_rest : e ∈ Mrest := by rw [hrest_eq]; exact he
                      rw [← hpr]
                      exact Finset.mem_image.mpr ⟨e, he_rest, if_neg hnd⟩
                    exact hv0_in (Finset.mem_biUnion.mpr ⟨_, hv0_im, Finset.mem_insert_self _ _⟩)
                  exact Finset.disjoint_left.mp hdisj_e hue hu_spec.1
              · exact absurd rfl hne0
              · refine ⟨hxV, fun h => ?_⟩
                rcases h with h1 | h2
                · exact hxnotVC (hC.2.1 h1)
                · exact hnotM' h2
          have hu_not_er : u ∉ (V' \ M'.biUnion id).erase v₀ := fun h => by
            have hmem := (Finset.mem_erase.mp h).2
            rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hmem).1 with h1 | h2
            · exact (Finset.mem_erase.mp h).1 h1
            · exact (Finset.mem_sdiff.mp h2).2 hu_spec.1
          have hvw_prod : ∏ x ∈ V \ M.biUnion id, (vw x : ℂ) =
              (∏ x ∈ (V' \ M'.biUnion id).erase v₀, (vw x : ℂ)) * (vw u : ℂ) := by
            rw [hsdiff, Finset.prod_insert hu_not_er, mul_comm]
          have hew_prod : ∏ e ∈ M, (ew e : ℂ) =
              (∏ e ∈ M', (ew e : ℂ)) * (∏ e ∈ MC, (ew e : ℂ)) := by
            rw [hpart, Finset.prod_union hdisj, hrest_eq, mul_comm]
          have hcard : M.card = C.card + M'.card := by
            rw [hpart, Finset.card_union_of_disjoint hdisj, hC.1, hrest_eq]
          rw [hvw_prod, hew_prod, hcard]
      rw [hfib, Finset.sum_sigma]
      have hv0_mem : v₀ ∈ V' \ M'.biUnion id :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, hv0_in⟩
      have hvw_eq : ∏ x ∈ V' \ M'.biUnion id, (vw' x : ℂ) =
          (∑ u ∈ VC, (cu u : ℂ) * (vw u : ℂ)) * ∏ x ∈ (V' \ M'.biUnion id).erase v₀, (vw x : ℂ) := by
        rw [← Finset.mul_prod_erase (V' \ M'.biUnion id) (fun x => (vw' x : ℂ)) hv0_mem]
        have h1 : (vw' v₀ : ℂ) = ∑ u ∈ VC, (cu u : ℂ) * (vw u : ℂ) := by
          simp only [vw', ↓reduceIte]; push_cast; rfl
        have h2 : ∏ x ∈ (V' \ M'.biUnion id).erase v₀, (vw' x : ℂ) =
            ∏ x ∈ (V' \ M'.biUnion id).erase v₀, (vw x : ℂ) :=
          Finset.prod_congr rfl (fun x hx => by simp [vw', Finset.ne_of_mem_erase hx])
        rw [h1, h2]
      have hew_eq : ∏ e ∈ M', (ew' e : ℂ) = ∏ e ∈ M', (ew e : ℂ) :=
        Finset.prod_congr rfl (fun e he => by
          have hnv0 : v₀ ∉ e := fun h => hv0_in (Finset.mem_biUnion.mpr ⟨e, he, h⟩)
          rw [hew'_other e hnv0])
      rw [hvw_eq, hew_eq]
      simp only [cu, Complex.ofReal_sum, Complex.ofReal_prod, Finset.sum_mul, Finset.mul_sum, pow_add]
      refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun MC _ => by ring))
  have hvw'_pos : ∀ x ∈ V', 0 < vw' x := by
    intro x hx
    by_cases hx0 : x = v₀
    · subst hx0
      simp only [vw', ↓reduceIte]
      obtain ⟨Mpos, hMp_m, _, hMp_hit, hMp_pos⟩ := exists_pos_matching_of_ZPoly_pos V ∅ H vw ew hvw hew hpos
      have hC := hhit_C_card Mpos hMp_m (fun R hR => hMp_hit R (hC_sub hR))
      set MC := Mpos.filter (fun e => ∃ R ∈ C, e ⊆ R)
      have hrem : (VC \ MC.biUnion id).card = 1 := by
        have h1 : (VC \ MC.biUnion id).card + (MC.biUnion id).card = VC.card :=
          Finset.card_sdiff_add_card_eq_card hC.2.1
        have h2 : (MC.biUnion id).card = 2 * C.card := hC.2.2
        omega
      obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hrem
      have huVC : u ∈ VC := (Finset.mem_sdiff.mp (hu_eq ▸ Finset.mem_singleton_self u)).1
      have hMC_in : MC ∈ MCs u := Finset.mem_filter.mpr ⟨mem_matchingsOn.mpr ⟨fun e he =>
        ⟨(hMp_m.1 e (Finset.mem_filter.mp he).1).1, (Finset.subset_biUnion_of_mem id he).trans hC.2.1⟩,
        fun e₁ h1 e₂ h2 hne => hMp_m.2 e₁ (Finset.mem_filter.mp h1).1 e₂ (Finset.mem_filter.mp h2).1 hne⟩,
        fun e he => (Finset.mem_filter.mp he).2,
        fun R hR => by
          obtain ⟨e, heM, heR⟩ := hMp_hit R (hC_sub hR)
          exact ⟨e, Finset.mem_filter.mpr ⟨heM, R, hR, heR⟩, heR⟩, hu_eq⟩
      have hprod_pos : 0 < ∏ e ∈ MC, ew e := by
        have hMp_prod : 0 < ∏ e ∈ Mpos, ew e :=
          pos_of_mul_pos_right hMp_pos (Finset.prod_nonneg (fun v hv => le_of_lt (hvw v (Finset.mem_sdiff.mp hv).1)))
        have hall_pos : ∀ e ∈ Mpos, 0 < ew e := fun e he => by
          by_contra hle
          have h0 : ew e = 0 := le_antisymm (not_lt.mp hle) (hew e)
          rw [Finset.prod_eq_zero he h0] at hMp_prod; exact lt_irrefl 0 hMp_prod
        exact Finset.prod_pos (fun e he => hall_pos e (Finset.mem_filter.mp he).1)
      have hcu_pos : 0 < cu u := lt_of_lt_of_le hprod_pos
        (Finset.single_le_sum (fun MC' _ => Finset.prod_nonneg (fun e _ => hew e)) hMC_in)
      exact lt_of_lt_of_le (mul_pos hcu_pos (hvw u (hVC_sub huVC)))
        (Finset.single_le_sum (fun u' hu' => mul_nonneg (hcu_nn u') (le_of_lt (hvw u' (hVC_sub hu')))) huVC)
    · simp only [vw', hx0, ↓reduceIte]
      have hx_sdiff : x ∈ V \ VC := (Finset.mem_insert.mp hx).resolve_left hx0
      exact hvw x (Finset.mem_sdiff.mp hx_sdiff).1
  have hpos' : 0 < (ZPoly V' ∅ H' vw' ew' 1).re := by
    have h1 := hZ_eq 1
    rw [one_pow, one_mul] at h1
    rwa [← h1]
  have hH'_ok : ∀ R ∈ H', R.card = 3 ∧ R ⊆ V' := fun R hR =>
    ⟨(hH R (Finset.mem_sdiff.mp hR).1).1,
      (Finset.subset_sdiff.mpr ⟨(hH R (Finset.mem_sdiff.mp hR).1).2,
        Finset.disjoint_left.mpr (fun x hxR hxVC => by
          rcases Finset.mem_biUnion.mp hxVC with ⟨R₁, hR₁, hxR₁⟩
          exact Finset.disjoint_left.mp (hC_closed R₁ hR₁ R hR) hxR₁ hxR)⟩).trans
        (Finset.subset_insert _ _)⟩
  have hdeg' : ∀ x ∈ V', (H'.filter (fun R => x ∈ R)).card ≤ 2 := fun x hx => by
    by_cases hx0 : x = v₀
    · rw [hx0]
      have hemp : H'.filter (fun R => v₀ ∈ R) = ∅ := by
        ext R; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hR hv0R
        rcases Finset.mem_biUnion.mp hv₀ with ⟨R₁, hR₁, hv0R₁⟩
        exact Finset.disjoint_left.mp (hC_closed R₁ hR₁ R hR) hv0R₁ hv0R
      rw [hemp]; simp
    · exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
        (hdeg x (Finset.mem_sdiff.mp ((Finset.mem_insert.mp hx).resolve_left hx0)).1)
  exact ⟨C.card, 1, V', ∅, H', vw', ew', zero_lt_one, hV'_lt, (by simp), hH'_ok, hdeg',
    hvw'_pos, hew'_nn, hpos', fun z => by simpa using hZ_eq z⟩

private lemma reduce_ZPoly_base {α : Type*} [DecidableEq α]
    (V : Finset α) (vw : α → ℝ) (ew : Finset α → ℝ)
    (hvw : ∀ v ∈ V, 0 < vw v) (hew : ∀ e, 0 ≤ ew e) :
    ∃ (k : ℕ) (C₀ : ℝ) (W : Finset α) (w : Finset α → ℝ),
      0 < C₀ ∧ (∀ e, 0 ≤ w e) ∧
      ∀ z : ℂ, ZPoly V ∅ ∅ vw ew z = (C₀ : ℂ) * z ^ k * MPoly W w z := by
  let C₀ : ℝ := ∏ v ∈ V, vw v
  have hC₀ : 0 < C₀ := Finset.prod_pos hvw
  let w' : Finset α → ℝ := fun e => if e ⊆ V then ew e / (∏ v ∈ e, vw v) else 0
  have hw' : ∀ e, 0 ≤ w' e := fun e => by
    simp only [w']
    split_ifs with hsub
    · exact div_nonneg (hew e) (le_of_lt (Finset.prod_pos (fun v hv => hvw v (hsub hv))))
    · exact le_refl 0
  refine ⟨0, C₀, V, w', hC₀, hw', fun z => ?_⟩
  rw [pow_zero, mul_one]
  unfold ZPoly MPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr ?_ (fun M hM => ?_)
  · ext M; simp
  · have hMm : IsMatching V M := (Finset.mem_filter.mp hM).2
    have hbi_sub : M.biUnion id ⊆ V := Finset.biUnion_subset.mpr (fun e he => (hMm.1 e he).2)
    have hprod_V : (C₀ : ℂ) = (∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) * (∏ v ∈ M.biUnion id, (vw v : ℂ)) := by
      simp only [C₀, Complex.ofReal_prod]
      rw [← Finset.prod_sdiff hbi_sub, mul_comm]
    have hprod_bi : ∏ v ∈ M.biUnion id, (vw v : ℂ) = ∏ e ∈ M, ∏ v ∈ e, (vw v : ℂ) := by
      rw [Finset.prod_biUnion (s := M) (t := id) (fun e₁ h1 e₂ h2 hne => hMm.2 e₁ h1 e₂ h2 hne)]
      rfl
    have hprod_w : (∏ e ∈ M, ∏ v ∈ e, (vw v : ℂ)) * (∏ e ∈ M, (w' e : ℂ)) = ∏ e ∈ M, (ew e : ℂ) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun e he => ?_)
      have hsub : e ⊆ V := (hMm.1 e he).2
      simp only [w', hsub, ↓reduceIte, Complex.ofReal_div, Complex.ofReal_prod]
      have hne : (∏ v ∈ e, (vw v : ℂ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun v hv => Complex.ofReal_ne_zero.mpr (ne_of_gt (hvw v (hsub hv))))
      exact mul_div_cancel₀ _ hne
    calc
      ((∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card
        = ((∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) *
            ((∏ e ∈ M, ∏ v ∈ e, (vw v : ℂ)) * (∏ e ∈ M, (w' e : ℂ)))) * z ^ M.card := by rw [hprod_w]
      _ = ((∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) * (∏ v ∈ M.biUnion id, (vw v : ℂ))) *
            ((∏ e ∈ M, (w' e : ℂ)) * z ^ M.card) := by rw [hprod_bi]; ring
      _ = (C₀ : ℂ) * ((∏ e ∈ M, (w' e : ℂ)) * z ^ M.card) := by rw [← hprod_V]


private lemma reduce_ZPoly {α : Type*} [DecidableEq α] :
    ∀ (m : ℕ) (V : Finset α) (F₂ H : Finset (Finset α)) (vw : α → ℝ) (ew : Finset α → ℝ),
      V.card ≤ m →
      (∀ e ∈ F₂, e.card = 2 ∧ e ⊆ V) →
      (∀ R ∈ H, R.card = 3 ∧ R ⊆ V) →
      (∀ v ∈ V, (H.filter (fun R => v ∈ R)).card ≤ 2) →
      (∀ v ∈ V, 0 < vw v) →
      (∀ e, 0 ≤ ew e) →
      0 < (ZPoly V F₂ H vw ew 1).re →
      ∃ (k : ℕ) (C₀ : ℝ) (W : Finset α) (w : Finset α → ℝ),
        0 < C₀ ∧ (∀ e, 0 ≤ w e) ∧
        ∀ z : ℂ, ZPoly V F₂ H vw ew z = (C₀ : ℂ) * z ^ k * MPoly W w z := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro V F₂ H vw ew hVm hF₂ hH hdeg hvw hew hpos
    have hstep_use : ZPolyStepGoal V F₂ H vw ew →
        ∃ (k : ℕ) (C₀ : ℝ) (W : Finset α) (w : Finset α → ℝ),
          0 < C₀ ∧ (∀ e, 0 ≤ w e) ∧
          ∀ z : ℂ, ZPoly V F₂ H vw ew z = (C₀ : ℂ) * z ^ k * MPoly W w z := by
      rintro ⟨dk, c₀, V', F₂', H', vw', ew', hc₀, hlt, hF₂', hH', hdeg', hvw', hew', hpos', hZeq⟩
      obtain ⟨k, C₀, W, w, hC₀, hw, hrec⟩ := ih V'.card (lt_of_lt_of_le hlt hVm) V' F₂' H' vw' ew'
        (le_refl _) hF₂' hH' hdeg' hvw' hew' hpos'
      refine ⟨k + dk, c₀ * C₀, W, w, mul_pos hc₀ hC₀, hw, fun z => ?_⟩
      rw [hZeq z, hrec z]
      push_cast; rw [pow_add]; ring
    by_cases hF₂_ne : F₂.Nonempty
    · exact hstep_use (reduce_ZPoly_step_F2 V F₂ H vw ew hF₂ hH hdeg hvw hew hpos hF₂_ne)
    · rw [Finset.not_nonempty_iff_eq_empty] at hF₂_ne
      subst hF₂_ne
      by_cases hpair2 : ∃ R₁ ∈ H, ∃ R₂ ∈ H, R₁ ≠ R₂ ∧ (R₁ ∩ R₂).card = 2
      · exact hstep_use (reduce_ZPoly_step_core2 V H vw ew hH hdeg hvw hew hpos hpair2)
      · push_neg at hpair2
        by_cases hH_ne : H.Nonempty
        · refine hstep_use ?_
          have hlin_step : ZPolyStepGoal V ∅ H vw ew := by
            have hlin : ∀ R₁ ∈ H, ∀ R₂ ∈ H, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1 := by
              intro R₁ hR₁ R₂ hR₂ hne
              have hle3 : (R₁ ∩ R₂).card ≤ 3 := le_trans (Finset.card_le_card Finset.inter_subset_left) (le_of_eq (hH R₁ hR₁).1)
              have hne3 : (R₁ ∩ R₂).card ≠ 3 := fun h3 => by
                have h1 : R₁ ∩ R₂ = R₁ := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [(hH R₁ hR₁).1, h3])
                have h2 : R₁ ∩ R₂ = R₂ := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [(hH R₂ hR₂).1, h3])
                exact hne (h1.symm.trans h2)
              have hne2 := hpair2 R₁ hR₁ R₂ hR₂ hne
              omega
            have hdeg_all : ∀ x : α, (H.filter (fun R => x ∈ R)).card ≤ 2 := by
              intro x
              by_cases hx : x ∈ V
              · exact hdeg x hx
              · have : H.filter (fun R => x ∈ R) = ∅ := by
                  ext R; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
                  intro hR hxR; exact hx ((hH R hR).2 hxR)
                rw [this]; simp
            obtain ⟨C, hC_sub, hC_ne, hC_closed, hVC_le⟩ :=
              exists_comp_of_linear_hypergraph H (fun R hR => (hH R hR).1) hdeg_all hlin hH_ne
            let VC := C.biUnion id
            have hVC_sub : VC ⊆ V := Finset.biUnion_subset.mpr (fun R hR => (hH R (hC_sub hR)).2)
            have hVC_ge : 2 * C.card ≤ VC.card := by
              obtain ⟨Mpos, hMp_m, _, hMp_hit, _⟩ := exists_pos_matching_of_ZPoly_pos V ∅ H vw ew hvw hew hpos
              have hex : ∀ R ∈ C, ∃ e ∈ Mpos, e ⊆ R := fun R hR => hMp_hit R (hC_sub hR)
              let f : Finset α → Finset α := fun R =>
                if h : R ∈ C then Classical.choose (hex R h) else ∅
              have hf_in : ∀ R ∈ C, f R ∈ Mpos ∧ f R ⊆ R := fun R hR => by
                simp only [f, hR, ↓reduceDIte]
                exact Classical.choose_spec (hex R hR)
              have hf_inj : Set.InjOn f C := by
                intro R₁ hR₁ R₂ hR₂ heq
                by_contra hne
                have hsub : f R₁ ⊆ R₁ ∩ R₂ := Finset.subset_inter (hf_in R₁ hR₁).2 (heq ▸ (hf_in R₂ hR₂).2)
                have hc := Finset.card_le_card hsub
                rw [(hMp_m.1 _ (hf_in R₁ hR₁).1).1] at hc
                have hl := hlin R₁ (hC_sub hR₁) R₂ (hC_sub hR₂) hne
                omega
              let MC := C.image f
              have hMC_m : IsMatching VC MC := ⟨fun e he => by
                rcases Finset.mem_image.mp he with ⟨R, hR, rfl⟩
                exact ⟨(hMp_m.1 _ (hf_in R hR).1).1, (hf_in R hR).2.trans
                  (fun x hx => Finset.mem_biUnion.mpr ⟨R, hR, hx⟩)⟩,
                fun e₁ h1 e₂ h2 hne => by
                  rcases Finset.mem_image.mp h1 with ⟨R₁, hR₁, rfl⟩
                  rcases Finset.mem_image.mp h2 with ⟨R₂, hR₂, rfl⟩
                  exact hMp_m.2 _ (hf_in R₁ hR₁).1 _ (hf_in R₂ hR₂).1 hne⟩
              have hMC_card : MC.card = C.card := Finset.card_image_of_injOn hf_inj
              rw [← hMC_card]
              exact two_mul_card_le_of_matching hMC_m
            have hVC_le' : VC.card ≤ 2 * C.card + 1 := hVC_le
            have hVC_cases : VC.card = 2 * C.card ∨ VC.card = 2 * C.card + 1 := by omega
            have hhit_C_card : ∀ M, IsMatching V M → (∀ R ∈ C, ∃ e ∈ M, e ⊆ R) →
                let MC := M.filter (fun e => ∃ R ∈ C, e ⊆ R)
                MC.card = C.card ∧ (MC.biUnion id) ⊆ VC ∧ (MC.biUnion id).card = 2 * C.card := by
              intro M hMm hhit
              let MC := M.filter (fun e => ∃ R ∈ C, e ⊆ R)
              have hMC_card : MC.card = C.card := by
                refine Finset.card_bij (fun e he => Classical.choose (Finset.mem_filter.mp he).2) ?_ ?_ ?_
                · intro e he; exact (Classical.choose_spec (Finset.mem_filter.mp he).2).1
                · intro e₁ h1 e₂ h2 heq
                  have hR₁ := (Classical.choose_spec (Finset.mem_filter.mp h1).2).1
                  have hs₁ := (Classical.choose_spec (Finset.mem_filter.mp h1).2).2
                  have hs₂ := (Classical.choose_spec (Finset.mem_filter.mp h2).2).2
                  rw [← heq] at hs₂
                  by_contra hne
                  have hd := hMm.2 e₁ (Finset.mem_filter.mp h1).1 e₂ (Finset.mem_filter.mp h2).1 hne
                  have hc := Finset.card_le_card (Finset.union_subset hs₁ hs₂)
                  rw [Finset.card_union_of_disjoint hd, (hMm.1 e₁ (Finset.mem_filter.mp h1).1).1,
                      (hMm.1 e₂ (Finset.mem_filter.mp h2).1).1, (hH _ (hC_sub hR₁)).1] at hc
                  omega
                · intro R hR
                  obtain ⟨e, heM, heR⟩ := hhit R hR
                  have heMC : e ∈ MC := Finset.mem_filter.mpr ⟨heM, R, hR, heR⟩
                  refine ⟨e, heMC, ?_⟩
                  set R' := Classical.choose (Finset.mem_filter.mp heMC).2
                  have hR' := (Classical.choose_spec (Finset.mem_filter.mp heMC).2).1
                  have hs' := (Classical.choose_spec (Finset.mem_filter.mp heMC).2).2
                  by_contra hne
                  have hsub : e ⊆ R' ∩ R := Finset.subset_inter hs' heR
                  have hc := Finset.card_le_card hsub
                  rw [(hMm.1 e heM).1] at hc
                  have hl := hlin R' (hC_sub hR') R (hC_sub hR) hne
                  omega
              have hMC_sub : MC.biUnion id ⊆ VC := Finset.biUnion_subset.mpr (fun e he => by
                rcases (Finset.mem_filter.mp he).2 with ⟨R, hR, heR⟩
                exact heR.trans (fun x hx => Finset.mem_biUnion.mpr ⟨R, hR, hx⟩))
              have hMC_m : IsMatching VC MC := ⟨fun e he => ⟨(hMm.1 e (Finset.mem_filter.mp he).1).1,
                (Finset.subset_biUnion_of_mem id he).trans hMC_sub⟩,
                fun e₁ h1 e₂ h2 hne => hMm.2 e₁ (Finset.mem_filter.mp h1).1 e₂ (Finset.mem_filter.mp h2).1 hne⟩
              exact ⟨hMC_card, hMC_sub, by rw [card_biUnion_matching hMC_m, hMC_card]⟩
            rcases hVC_cases with hVC_even | hVC_odd
            · exact reduce_ZPoly_step_unicyclic V H C vw ew hH hdeg hvw hew hpos hC_sub hC_ne hC_closed hVC_sub hhit_C_card hVC_even
            · exact reduce_ZPoly_step_tree V H C vw ew hH hdeg hvw hew hpos hC_sub hC_ne hC_closed hVC_sub hhit_C_card hVC_odd
          exact hlin_step
        · rw [Finset.not_nonempty_iff_eq_empty] at hH_ne
          subst hH_ne
          exact reduce_ZPoly_base V vw ew hvw hew

private lemma factor_real_nonpos_roots :
    ∀ (k : ℕ) (P : Polynomial ℝ), P ≠ 0 → P.natDegree = k →
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ≤ 0) →
      ∃ (c : ℝ) (r : Fin k → ℝ), (∀ j, 0 ≤ r j) ∧
        P = Polynomial.C c * ∏ j : Fin k, (Polynomial.X + Polynomial.C (r j)) := by
  intro k
  induction k with
  | zero =>
    intro P _ hdeg _
    refine ⟨P.coeff 0, Fin.elim0, fun j => Fin.elim0 j, ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact Polynomial.eq_C_of_natDegree_eq_zero hdeg
  | succ k ih =>
    intro P hP hdeg hroots
    have hdeg_C : 0 < (P.map (algebraMap ℝ ℂ)).degree := by
      rw [Polynomial.degree_map_eq_of_injective Complex.ofReal_injective,
          Polynomial.degree_eq_natDegree hP, hdeg]
      exact WithBot.coe_lt_coe.mpr (Nat.zero_lt_succ k)
    obtain ⟨z₀, hz₀⟩ := Complex.exists_root hdeg_C
    have hrz := hroots z₀ hz₀
    have hz_eq : z₀ = (z₀.re : ℂ) := Complex.ext rfl (by simp [hrz.1])
    have hev0 : P.eval z₀.re = 0 := by
      have h1 : ((P.eval z₀.re : ℝ) : ℂ) = (P.map (algebraMap ℝ ℂ)).eval z₀ := by
        rw [hz_eq]; exact (Polynomial.eval_map_apply (f := algebraMap ℝ ℂ) (x := z₀.re) (p := P)).symm
      rw [hz₀] at h1
      exact Complex.ofReal_eq_zero.mp h1
    have hdvd : (Polynomial.X - Polynomial.C z₀.re) ∣ P := Polynomial.dvd_iff_isRoot.mpr hev0
    obtain ⟨Q, hPQ⟩ := hdvd
    have hQne : Q ≠ 0 := fun h0 => hP (by rw [hPQ, h0, mul_zero])
    have hXne : (Polynomial.X - Polynomial.C z₀.re : Polynomial ℝ) ≠ 0 := Polynomial.X_sub_C_ne_zero _
    have hQdeg : Q.natDegree = k := by
      have h1 : P.natDegree = (Polynomial.X - Polynomial.C z₀.re).natDegree + Q.natDegree := by
        rw [hPQ, Polynomial.natDegree_mul hXne hQne]
      rw [Polynomial.natDegree_X_sub_C, hdeg] at h1
      omega
    have hQroots : ∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ≤ 0 := by
      intro z hz
      apply hroots z
      rw [hPQ, Polynomial.map_mul, Polynomial.eval_mul, hz, mul_zero]
    obtain ⟨c, r', hr', hQeq⟩ := ih Q hQne hQdeg hQroots
    let r : Fin (k + 1) → ℝ := Fin.cons (-z₀.re) r'
    refine ⟨c, r, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun i => hr' i) j
      simp only [r, Fin.cons_zero]
      linarith [hrz.2]
    · rw [hPQ, hQeq, Fin.prod_univ_succ]
      simp only [r, Fin.cons_zero, Fin.cons_succ, map_neg, sub_eq_add_neg]
      ring

private lemma all_roots_real_deriv' (P : Polynomial ℂ) (hP : 0 < P.degree)
    (h : ∀ z : ℂ, P.eval z = 0 → z.im = 0) :
    ∀ z : ℂ, P.derivative.eval z = 0 → z.im = 0 := by
  intro z hz
  rw [Polynomial.eq_centerMass_of_eval_derivative_eq_zero hP hz]
  unfold Finset.centerMass
  rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.im_sum]
  have hsum0 : ∑ w ∈ P.roots.toFinset, (P.derivRootWeight z w • id w).im = 0 := by
    refine Finset.sum_eq_zero (fun w hw => ?_)
    have hPne : P ≠ 0 := by rintro rfl; simp at hP
    have hw0 : P.eval w = 0 := (Polynomial.mem_roots hPne).mp (Multiset.mem_toFinset.mp hw)
    simp only [id_eq]
    rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        h w hw0, mul_zero]
  rw [hsum0, mul_zero]

private lemma all_roots_real_iter_deriv (P : Polynomial ℂ) :
    ∀ k : ℕ, k ≤ P.natDegree → P ≠ 0 →
      (∀ z : ℂ, P.eval z = 0 → z.im = 0) →
      (Polynomial.derivative^[k] P) ≠ 0 ∧
      (Polynomial.derivative^[k] P).natDegree = P.natDegree - k ∧
      (∀ z : ℂ, (Polynomial.derivative^[k] P).eval z = 0 → z.im = 0) := by
  intro k
  induction k with
  | zero =>
    intro _ hne h; exact ⟨hne, by simp, h⟩
  | succ k ih =>
    intro hk hne h
    obtain ⟨hne_k, hdeg_k, hr_k⟩ := ih (by omega) hne h
    have hpos_k : 0 < (Polynomial.derivative^[k] P).natDegree := by omega
    have hdeg_pos : 0 < (Polynomial.derivative^[k] P).degree := by
      rw [Polynomial.degree_eq_natDegree hne_k]; exact WithBot.coe_lt_coe.mpr hpos_k
    have htop_ne : (Polynomial.derivative (Polynomial.derivative^[k] P)).coeff
        ((Polynomial.derivative^[k] P).natDegree - 1) ≠ 0 := by
      rw [Polynomial.coeff_derivative]
      have hsub : (Polynomial.derivative^[k] P).natDegree - 1 + 1 = (Polynomial.derivative^[k] P).natDegree := by omega
      rw [hsub]
      have hlc : (Polynomial.derivative^[k] P).coeff (Polynomial.derivative^[k] P).natDegree ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr hne_k
      have hnat : ((↑((Polynomial.derivative^[k] P).natDegree - 1) + 1 : ℂ)) ≠ 0 := by
        have hcast : ((↑((Polynomial.derivative^[k] P).natDegree - 1) + 1 : ℂ)) =
            (((Polynomial.derivative^[k] P).natDegree : ℕ) : ℂ) := by
          rw [← hsub]; push_cast; rfl
        rw [hcast]
        exact Nat.cast_ne_zero.mpr (by omega)
      exact mul_ne_zero hlc hnat
    have hdeg_succ : (Polynomial.derivative^[k + 1] P).natDegree = (Polynomial.derivative^[k] P).natDegree - 1 := by
      rw [Function.iterate_succ_apply']
      exact le_antisymm (Polynomial.natDegree_derivative_le _) (Polynomial.le_natDegree_of_ne_zero htop_ne)
    have hne_succ : Polynomial.derivative^[k + 1] P ≠ 0 := by
      rw [Function.iterate_succ_apply']
      intro h0
      exact htop_ne (by rw [h0]; simp)
    refine ⟨hne_succ, by rw [hdeg_succ, hdeg_k]; omega, ?_⟩
    rw [Function.iterate_succ_apply']
    exact all_roots_real_deriv' _ hdeg_pos hr_k

private lemma coeff_iter_deriv (P : Polynomial ℂ) :
    ∀ k j : ℕ, (Polynomial.derivative^[k] P).coeff j =
      (Nat.descFactorial (j + k) k : ℂ) * P.coeff (j + k) := by
  intro k
  induction k with
  | zero => intro j; simp
  | succ k ih =>
    intro j
    rw [Function.iterate_succ_apply', Polynomial.coeff_derivative, ih (j + 1)]
    have h1 : j + 1 + k = j + (k + 1) := by omega
    have h2 : Nat.descFactorial (j + (k + 1)) (k + 1) =
        (j + 1) * Nat.descFactorial (j + 1 + k) k := by
      rw [← h1]
      have h3 : (j + 1 + k) - k = j + 1 := by omega
      rw [Nat.descFactorial_succ, h3]
    rw [h2, ← h1]
    push_cast
    ring

private noncomputable def revPoly (m : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (m + 1), Polynomial.C (P.coeff (m - j)) * Polynomial.X ^ j

private lemma coeff_revPoly (m : ℕ) (P : Polynomial ℂ) (j : ℕ) :
    (revPoly m P).coeff j = if j ≤ m then P.coeff (m - j) else 0 := by
  unfold revPoly
  rw [← Polynomial.lcoeff_apply, map_sum]; simp only [Polynomial.lcoeff_apply]
  by_cases hj : j ≤ m
  · rw [if_pos hj, Finset.sum_eq_single j]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    · intro b _ hbj; simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hbj.symm]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hj]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    have hbj : b ≠ j := by rw [Finset.mem_range] at hb; omega
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hbj.symm]

private lemma eval_revPoly (m : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ m) {z : ℂ} (hz : z ≠ 0) :
    (revPoly m P).eval z = z ^ m * P.eval z⁻¹ := by
  unfold revPoly
  rw [← Polynomial.coe_evalRingHom, map_sum]; simp only [Polynomial.coe_evalRingHom]
  have hP : P = ∑ i ∈ Finset.range (m + 1), Polynomial.C (P.coeff i) * Polynomial.X ^ i := by
    ext i
    conv_rhs => rw [← Polynomial.lcoeff_apply, map_sum]; simp only [Polynomial.lcoeff_apply]
    by_cases hi : i ≤ m
    · rw [Finset.sum_eq_single i]
      · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · intro b _ hbi; simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hbi.symm]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      symm; refine Finset.sum_eq_zero (fun b hb => ?_)
      have hbi : b ≠ i := by rw [Finset.mem_range] at hb; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hbi.symm]
  conv_rhs => rw [hP, ← Polynomial.coe_evalRingHom, map_sum, Finset.mul_sum]
  simp only [Polynomial.coe_evalRingHom]
  refine Finset.sum_bij (fun j _ => m - j) ?_ ?_ ?_ ?_
  · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
  · intro j₁ h1 j₂ h2 heq; rw [Finset.mem_range] at h1 h2; omega
  · intro i hi; rw [Finset.mem_range] at hi; exact ⟨m - i, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    rw [Finset.mem_range] at hj
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have hpow : z ^ m * (z⁻¹) ^ (m - j) = z ^ j := by
      have hm : z ^ m = z ^ j * z ^ (m - j) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
      rw [hm, inv_pow]
      have hne : z ^ (m - j) ≠ 0 := pow_ne_zero _ hz
      calc
        z ^ j * z ^ (m - j) * (z ^ (m - j))⁻¹ = z ^ j * (z ^ (m - j) * (z ^ (m - j))⁻¹) := by ring
        _ = z ^ j * 1 := by rw [mul_inv_cancel₀ hne]
        _ = z ^ j := mul_one _
    calc
      P.coeff (m - j) * z ^ j = P.coeff (m - j) * (z ^ m * (z⁻¹) ^ (m - j)) := by rw [hpow]
      _ = z ^ m * (P.coeff (m - j) * (z⁻¹) ^ (m - j)) := by ring

private lemma quadratic_real_roots_disc (a b c : ℝ)
    (h : ∀ z : ℂ, (a : ℂ) * z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 → z.im = 0) :
    4 * a * c ≤ b ^ 2 := by
  by_cases ha : a = 0
  · rw [ha]; nlinarith [sq_nonneg b]
  · by_contra hlt
    push_neg at hlt
    let δ := Real.sqrt (4 * a * c - b ^ 2)
    have hδ_pos : 0 < δ := Real.sqrt_pos.mpr (by linarith)
    have hδ2 : δ ^ 2 = 4 * a * c - b ^ 2 := Real.sq_sqrt (by linarith)
    let z : ℂ := ⟨-b / (2 * a), δ / (2 * a)⟩
    have hz0 : (a : ℂ) * z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 := by
      apply Complex.ext
      · simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, Complex.zero_re, z]
        field_simp [ha]
        nlinarith [hδ2]
      · simp only [sq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, Complex.zero_im, z]
        field_simp [ha]
        ring
    have him0 := h z hz0
    simp only [z] at him0
    have hne0 : δ / (2 * a) ≠ 0 := div_ne_zero (ne_of_gt hδ_pos) (mul_ne_zero two_ne_zero ha)
    exact hne0 him0

private lemma newton_ineq_of_real_roots (d : ℕ) (h : ℕ → ℕ)
    (hreal : ∀ z : ℂ, (∑ s ∈ Finset.range (d + 1), (h s : ℂ) * z ^ s) = 0 → z.im = 0)
    (hpos_sum : 0 < ∑ s ∈ Finset.range (d + 1), h s) :
    ∀ s : ℕ, 0 < s → s < d →
      h (s - 1) * h (s + 1) * (d.choose s) ^ 2 ≤
        (h s) ^ 2 * d.choose (s - 1) * d.choose (s + 1) := by
  intro s hs_pos hs_lt
  by_cases h0 : h (s - 1) = 0 ∨ h (s + 1) = 0
  · rcases h0 with h1 | h1 <;> simp [h1]
  push_neg at h0
  let P : Polynomial ℂ := ∑ j ∈ Finset.range (d + 1), Polynomial.C (h j : ℂ) * Polynomial.X ^ j
  have hP_coeff : ∀ j, P.coeff j = if j ≤ d then (h j : ℂ) else 0 := by
    intro j
    dsimp only [P]
    rw [← Polynomial.lcoeff_apply, map_sum]; simp only [Polynomial.lcoeff_apply]
    by_cases hj : j ≤ d
    · rw [if_pos hj, Finset.sum_eq_single j]
      · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · intro b _ hbj; simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hbj.symm]
      · intro hm; exact absurd (Finset.mem_range.mpr (by omega)) hm
    · rw [if_neg hj]
      refine Finset.sum_eq_zero (fun b hb => ?_)
      have hbj : b ≠ j := by rw [Finset.mem_range] at hb; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hbj.symm]
  have hP_eval : ∀ z : ℂ, P.eval z = ∑ j ∈ Finset.range (d + 1), (h j : ℂ) * z ^ j := by
    intro z
    simp only [P, ← Polynomial.coe_evalRingHom, map_sum]; simp [Polynomial.coe_evalRingHom]
  have hP_ne : P ≠ 0 := by
    intro hP0
    have hs1 : P.coeff (s + 1) = 0 := by rw [hP0]; simp
    rw [hP_coeff, if_pos (by omega)] at hs1
    exact h0.2 (Nat.cast_eq_zero.mp hs1)
  have hP_deg_ge : s + 1 ≤ P.natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    rw [hP_coeff, if_pos (by omega)]
    exact Nat.cast_ne_zero.mpr h0.2
  have hP_deg_le : P.natDegree ≤ d := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [hP_coeff, if_neg (by omega)]
  have hP_real : ∀ z : ℂ, P.eval z = 0 → z.im = 0 := fun z hz => hreal z (by rw [← hP_eval]; exact hz)
  obtain ⟨hP1_ne, hP1_deg, hP1_real⟩ := all_roots_real_iter_deriv P (s - 1) (by omega) hP_ne hP_real
  set P₁ := Polynomial.derivative^[s - 1] P
  let m := d - s + 1
  have hP1_deg_le : P₁.natDegree ≤ m := by omega
  let Q := revPoly m P₁
  have hQ_coeff_top : Q.coeff m = (Nat.descFactorial (s - 1) (s - 1) : ℂ) * (h (s - 1) : ℂ) := by
    rw [coeff_revPoly, if_pos (le_refl m), Nat.sub_self, coeff_iter_deriv, zero_add, hP_coeff, if_pos (by omega)]
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have hc : Q.coeff m = 0 := by rw [hQ0]; simp
    rw [hQ_coeff_top] at hc
    have h1 : (Nat.descFactorial (s - 1) (s - 1) : ℂ) ≠ 0 := by
      rw [Nat.descFactorial_self]; exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (h (s - 1) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h0.1
    exact mul_ne_zero h1 h2 hc
  have hQ_deg : Q.natDegree = m := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro j hj; rw [coeff_revPoly, if_neg (by omega)]
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [hQ_coeff_top]
      have h1 : (Nat.descFactorial (s - 1) (s - 1) : ℂ) ≠ 0 := by
        rw [Nat.descFactorial_self]; exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      exact mul_ne_zero h1 (Nat.cast_ne_zero.mpr h0.1)
  have hQ_real : ∀ z : ℂ, Q.eval z = 0 → z.im = 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · rw [eval_revPoly m P₁ hP1_deg_le hz0] at hz
      rcases mul_eq_zero.mp hz with hpow | hinv
      · exact absurd (eq_zero_of_pow_eq_zero hpow) hz0
      · have him := hP1_real z⁻¹ hinv
        have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
        rw [Complex.inv_im] at him
        have hneg : -z.im = 0 := (div_eq_zero_iff.mp him).resolve_right (ne_of_gt hns)
        linarith
  obtain ⟨_, hR_deg, hR_real⟩ := all_roots_real_iter_deriv Q (d - s - 1) (by omega) hQ_ne hQ_real
  set R := Polynomial.derivative^[d - s - 1] Q
  have hR_deg2 : R.natDegree = 2 := by rw [hR_deg, hQ_deg]; omega
  let a : ℝ := (Nat.descFactorial (d - s + 1) (d - s - 1) * Nat.descFactorial (s - 1) (s - 1) * h (s - 1) : ℕ)
  let b : ℝ := (Nat.descFactorial (d - s) (d - s - 1) * Nat.descFactorial s (s - 1) * h s : ℕ)
  let c : ℝ := (Nat.descFactorial (d - s - 1) (d - s - 1) * Nat.descFactorial (s + 1) (s - 1) * h (s + 1) : ℕ)
  have hR_c2 : R.coeff 2 = (a : ℂ) := by
    rw [coeff_iter_deriv, coeff_revPoly]
    have hidx : 2 + (d - s - 1) = m := by omega
    rw [hidx, if_pos (le_refl m), Nat.sub_self, coeff_iter_deriv, zero_add, hP_coeff, if_pos (by omega)]
    simp only [a, m]; push_cast; ring
  have hR_c1 : R.coeff 1 = (b : ℂ) := by
    rw [coeff_iter_deriv, coeff_revPoly]
    have hidx : 1 + (d - s - 1) = d - s := by omega
    have hsub : m - (d - s) = 1 := by omega
    have hs1 : 1 + (s - 1) = s := by omega
    rw [hidx, if_pos (by omega), hsub, coeff_iter_deriv, hs1, hP_coeff, if_pos (by omega)]
    simp only [b]; push_cast; ring
  have hR_c0 : R.coeff 0 = (c : ℂ) := by
    rw [coeff_iter_deriv, coeff_revPoly]
    have hidx : 0 + (d - s - 1) = d - s - 1 := by omega
    have hsub : m - (d - s - 1) = 2 := by omega
    have hs2 : 2 + (s - 1) = s + 1 := by omega
    rw [hidx, if_pos (by omega), hsub, coeff_iter_deriv, hs2, hP_coeff, if_pos (by omega)]
    simp only [c]; push_cast; ring
  have hR_eval : ∀ z : ℂ, R.eval z = (a : ℂ) * z ^ 2 + (b : ℂ) * z + (c : ℂ) := by
    intro z
    have hR_sum : R = Polynomial.C (R.coeff 2) * Polynomial.X ^ 2 +
        Polynomial.C (R.coeff 1) * Polynomial.X + Polynomial.C (R.coeff 0) := by
      ext j
      match j with
      | 0 => simp [Polynomial.coeff_X_pow]
      | 1 => simp [Polynomial.coeff_X_pow]
      | 2 => simp [Polynomial.coeff_X_pow]
      | j + 3 =>
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [Polynomial.coeff_X_pow]
    conv_lhs => rw [hR_sum]
    simp [hR_c2, hR_c1, hR_c0]
  have hdisc : 4 * a * c ≤ b ^ 2 := quadratic_real_roots_disc a b c (fun z hz => hR_real z (by rw [hR_eval]; exact hz))
  have hdf_a1 : Nat.descFactorial (d - s + 1) (d - s - 1) * 2 = (d - s + 1) * (d - s) * (d - s - 1).factorial := by
    have h1 := Nat.factorial_mul_descFactorial (by omega : d - s - 1 ≤ d - s + 1)
    have hsub : (d - s + 1) - (d - s - 1) = 2 := by omega
    rw [hsub] at h1
    have h2 : (d - s + 1).factorial = (d - s + 1) * (d - s) * (d - s - 1).factorial := by
      have ha2 : d - s = (d - s - 1) + 1 := by omega
      rw [Nat.factorial_succ]
      conv_lhs => rw [ha2, Nat.factorial_succ]
      rw [← ha2]; ring
    rw [h2] at h1
    have h2f : (2 : ℕ).factorial = 2 := rfl
    rw [h2f, mul_comm] at h1
    exact h1
  have hdf_a2 : Nat.descFactorial (s - 1) (s - 1) = (s - 1).factorial := Nat.descFactorial_self _
  have hdf_b1 : Nat.descFactorial (d - s) (d - s - 1) = (d - s) * (d - s - 1).factorial := by
    have h1 := Nat.factorial_mul_descFactorial (by omega : d - s - 1 ≤ d - s)
    have hsub : (d - s) - (d - s - 1) = 1 := by omega
    rw [hsub, Nat.factorial_one, one_mul] at h1
    have h2 : (d - s).factorial = (d - s) * (d - s - 1).factorial := by
      have ha2 : d - s = (d - s - 1) + 1 := by omega
      conv_lhs => rw [ha2, Nat.factorial_succ]
      rw [← ha2]
    rw [h1, h2]
  have hdf_b2 : Nat.descFactorial s (s - 1) = s * (s - 1).factorial := by
    have h1 := Nat.factorial_mul_descFactorial (by omega : s - 1 ≤ s)
    have hsub : s - (s - 1) = 1 := by omega
    rw [hsub, Nat.factorial_one, one_mul] at h1
    have h2 : s.factorial = s * (s - 1).factorial := by
      have ha : s = (s - 1) + 1 := by omega
      conv_lhs => rw [ha, Nat.factorial_succ]
      rw [← ha]
    rw [h1, h2]
  have hdf_c1 : Nat.descFactorial (d - s - 1) (d - s - 1) = (d - s - 1).factorial := Nat.descFactorial_self _
  have hdf_c2 : Nat.descFactorial (s + 1) (s - 1) * 2 = (s + 1) * s * (s - 1).factorial := by
    have h1 := Nat.factorial_mul_descFactorial (by omega : s - 1 ≤ s + 1)
    have hsub : (s + 1) - (s - 1) = 2 := by omega
    rw [hsub] at h1
    have h2 : (s + 1).factorial = (s + 1) * s * (s - 1).factorial := by
      have ha : s = (s - 1) + 1 := by omega
      rw [Nat.factorial_succ]
      conv_lhs => rw [ha, Nat.factorial_succ]
      rw [← ha]; ring
    rw [h2] at h1
    have h2f : (2 : ℕ).factorial = 2 := rfl
    rw [h2f, mul_comm] at h1
    exact h1
  have hnat_disc : 4 * (Nat.descFactorial (d - s + 1) (d - s - 1) * Nat.descFactorial (s - 1) (s - 1) * h (s - 1)) *
      (Nat.descFactorial (d - s - 1) (d - s - 1) * Nat.descFactorial (s + 1) (s - 1) * h (s + 1)) ≤
      (Nat.descFactorial (d - s) (d - s - 1) * Nat.descFactorial s (s - 1) * h s) ^ 2 := by
    have hreal_disc : ((4 * (Nat.descFactorial (d - s + 1) (d - s - 1) * Nat.descFactorial (s - 1) (s - 1) * h (s - 1)) *
        (Nat.descFactorial (d - s - 1) (d - s - 1) * Nat.descFactorial (s + 1) (s - 1) * h (s + 1)) : ℕ) : ℝ) ≤
        (((Nat.descFactorial (d - s) (d - s - 1) * Nat.descFactorial s (s - 1) * h s) ^ 2 : ℕ) : ℝ) := by
      simp only [a, b, c] at hdisc
      push_cast at hdisc ⊢
      exact hdisc
    exact Nat.cast_le.mp hreal_disc
  have hfac_lhs : 4 * (Nat.descFactorial (d - s + 1) (d - s - 1) * Nat.descFactorial (s - 1) (s - 1) * h (s - 1)) *
      (Nat.descFactorial (d - s - 1) (d - s - 1) * Nat.descFactorial (s + 1) (s - 1) * h (s + 1)) =
      ((d - s - 1).factorial * (s - 1).factorial) ^ 2 * ((d - s) * s) *
      ((d - s + 1) * (s + 1) * h (s - 1) * h (s + 1)) := by
    have hmul : (Nat.descFactorial (d - s + 1) (d - s - 1) * 2) * (Nat.descFactorial (s + 1) (s - 1) * 2) =
        ((d - s + 1) * (d - s) * (d - s - 1).factorial) * ((s + 1) * s * (s - 1).factorial) := by
      rw [hdf_a1, hdf_c2]
    rw [hdf_a2, hdf_c1]
    calc
      4 * (Nat.descFactorial (d - s + 1) (d - s - 1) * (s - 1).factorial * h (s - 1)) *
          ((d - s - 1).factorial * Nat.descFactorial (s + 1) (s - 1) * h (s + 1))
        = (Nat.descFactorial (d - s + 1) (d - s - 1) * 2) * (Nat.descFactorial (s + 1) (s - 1) * 2) *
          ((s - 1).factorial * (d - s - 1).factorial * h (s - 1) * h (s + 1)) := by ring
      _ = ((d - s + 1) * (d - s) * (d - s - 1).factorial) * ((s + 1) * s * (s - 1).factorial) *
          ((s - 1).factorial * (d - s - 1).factorial * h (s - 1) * h (s + 1)) := by rw [hmul]
      _ = ((d - s - 1).factorial * (s - 1).factorial) ^ 2 * ((d - s) * s) *
          ((d - s + 1) * (s + 1) * h (s - 1) * h (s + 1)) := by ring
  have hfac_rhs : (Nat.descFactorial (d - s) (d - s - 1) * Nat.descFactorial s (s - 1) * h s) ^ 2 =
      ((d - s - 1).factorial * (s - 1).factorial) ^ 2 * ((d - s) * s) *
      ((d - s) * s * (h s) ^ 2) := by
    rw [hdf_b1, hdf_b2]; ring
  rw [hfac_lhs, hfac_rhs] at hnat_disc
  have hpos_fac : 0 < ((d - s - 1).factorial * (s - 1).factorial) ^ 2 * ((d - s) * s) :=
    Nat.mul_pos (pow_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) 2)
      (Nat.mul_pos (by omega) hs_pos)
  have hcore : (d - s + 1) * (s + 1) * h (s - 1) * h (s + 1) ≤ (d - s) * s * (h s) ^ 2 :=
    Nat.le_of_mul_le_mul_left hnat_disc hpos_fac
  have hch1 : d.choose (s - 1) * (d - s + 1) = d.choose s * s := by
    have h1 := Nat.choose_succ_right_eq d (s - 1)
    have hsub1 : s - 1 + 1 = s := by omega
    have hsub2 : d - (s - 1) = d - s + 1 := by omega
    rw [hsub1, hsub2] at h1
    linarith
  have hch2 : d.choose (s + 1) * (s + 1) = d.choose s * (d - s) := by
    have h1 := Nat.choose_succ_right_eq d s
    linarith
  have hch_prod : d.choose (s - 1) * d.choose (s + 1) * ((d - s + 1) * (s + 1)) =
      (d.choose s) ^ 2 * ((d - s) * s) := by
    calc
      d.choose (s - 1) * d.choose (s + 1) * ((d - s + 1) * (s + 1))
        = (d.choose (s - 1) * (d - s + 1)) * (d.choose (s + 1) * (s + 1)) := by ring
      _ = (d.choose s * s) * (d.choose s * (d - s)) := by rw [hch1, hch2]
      _ = (d.choose s) ^ 2 * ((d - s) * s) := by ring
  have hmul_ch : ((d - s) * s) * (h (s - 1) * h (s + 1) * (d.choose s) ^ 2) ≤
      ((d - s) * s) * ((h s) ^ 2 * d.choose (s - 1) * d.choose (s + 1)) := by
    calc
      ((d - s) * s) * (h (s - 1) * h (s + 1) * (d.choose s) ^ 2)
        = (h (s - 1) * h (s + 1)) * ((d.choose s) ^ 2 * ((d - s) * s)) := by ring
      _ = (h (s - 1) * h (s + 1)) * (d.choose (s - 1) * d.choose (s + 1) * ((d - s + 1) * (s + 1))) := by
        rw [← hch_prod]
      _ = ((d - s + 1) * (s + 1) * h (s - 1) * h (s + 1)) * (d.choose (s - 1) * d.choose (s + 1)) := by ring
      _ ≤ ((d - s) * s * (h s) ^ 2) * (d.choose (s - 1) * d.choose (s + 1)) :=
        Nat.mul_le_mul_right _ hcore
      _ = ((d - s) * s) * ((h s) ^ 2 * d.choose (s - 1) * d.choose (s + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left hmul_ch (Nat.mul_pos (by omega) hs_pos)

private lemma main_proof :
    ∀ (n : Nat), 2 ≤ n →
      ∀ (pos : List (Finset (Fin n))) (neg : List (Finset (Fin n) × Finset (Fin n))),
      (∀ R ∈ pos, R.card ≤ 3) →
      (∀ i : Fin n, (pos.toFinset.filter (fun R => R.card = 3 ∧ i ∈ R)).card ≤ 2) →
      let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
      let obs := fun (f : Fn) (R S : Finset (Fin n)) =>
        f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S))
      let fits := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
        PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
        ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
        (∀ R ∈ pos, obs f R ∅ = true) ∧ (∀ z ∈ neg, obs f z.1 z.2 = false)

      let size := fun f : Fn => (Finset.univ.filter (fun z : Fin n × Fin n =>
        z.1 < z.2 ∧ obs f {z.1,z.2} ∅ = true)).card
      let hist := fun s : Nat => Nat.card {f : Fn // fits f ∧ size f = s}

      let total := Nat.card {f : Fn // fits f}
      let d := n/2
      0 < total →
        (∃ p : Fin d → ℝ, (∀ j, 0 ≤ p j ∧ p j ≤ 1) ∧ ∀ x : ℝ,
          (Finset.range (d+1)).sum (fun s => (hist s : ℝ)*x^s) =
            (total : ℝ)* ∏ j : Fin d, (1-p j+p j*x)) ∧
        (∀ z : ℂ, (Finset.range (d+1)).sum (fun s => (hist s : ℂ)*z^s) = 0 →
          z.im = 0 ∧ z.re ≤ 0) ∧
        ∀ s : Nat, 0 < s → s < d →
          hist (s-1)*hist (s+1)*(d.choose s)^2 ≤
            (hist s)^2 * d.choose (s-1) * d.choose (s+1) := by
  intro n hn pos neg hpos3 hdeg3
  dsimp only
  intro htot_pos
  let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
  let obs := fun (f : Fn) (R S : Finset (Fin n)) =>
    f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S))
  let fits := fun f : Fn => (∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ 2 * n ∧
    Represents (fun i j : Fin n => decide (i = j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
    (∀ R ∈ pos, obs f R ∅ = true) ∧ (∀ z ∈ neg, obs f z.1 z.2 = false)
  let size := fun f : Fn => (Finset.univ.filter (fun z : Fin n × Fin n =>
    z.1 < z.2 ∧ obs f {z.1, z.2} ∅ = true)).card
  let hist := fun s : Nat => Nat.card {f : Fn // fits f ∧ size f = s}
  let total := Nat.card {f : Fn // fits f}
  let d := n / 2
  have hfit_ex : ∃ f : Fn, fits f := by
    by_contra h
    push_neg at h
    haveI : IsEmpty {f : Fn // fits f} := ⟨fun ⟨f, hf⟩ => h f hf⟩
    have h0 : total = 0 := by
      classical
      rw [show total = Fintype.card {f : Fn // fits f} from Nat.card_eq_fintype_card]
      exact Fintype.card_eq_zero
    have hpos_tot : 0 < total := htot_pos
    omega
  rcases hfit_ex with ⟨f₀, ⟨C₀, hC₀m, hC₀sz, hC₀rep, hC₀ev⟩, hpos₀, hneg₀⟩
  obtain ⟨M₀, hM₀, hM₀ev⟩ := optimal_circuit_is_matchFn hn C₀ hC₀m hC₀sz hC₀rep
  have hf₀_eq : f₀ = matchFn M₀ := by ext x y; rw [hC₀ev, hM₀ev]
  have hneg_disj : ∀ z ∈ neg, Disjoint z.1 z.2 := fun z hz => by
    have h := hneg₀ z hz
    rw [show obs f₀ z.1 z.2 = matchFn M₀ (fun i => decide (i ∈ z.1)) (fun j => decide (j ∈ z.2)) by
      simp [obs, hf₀_eq]] at h
    exact ((matchFn_obs_pair M₀ hM₀ z.1 z.2).mp h).1
  have hpos_ge2 : ∀ R ∈ pos, 2 ≤ R.card := fun R hR => by
    have h := hpos₀ R hR
    have h' : matchFn M₀ (fun i => decide (i ∈ R)) (fun _ => decide False) = true := by
      simpa [obs, hf₀_eq] using h
    obtain ⟨e, heM₀, heR⟩ := (matchFn_obs_empty M₀ hM₀ R).mp h'
    rw [← (hM₀.1 e heM₀).1]
    exact Finset.card_le_card heR
  let V : Finset (Fin n) := Finset.univ
  let F₂ : Finset (Finset (Fin n)) := pos.toFinset.filter (fun R => R.card = 2)
  let H : Finset (Finset (Fin n)) := pos.toFinset.filter (fun R => R.card = 3)
  let ew : Finset (Fin n) → ℝ := fun e =>
    if ∀ z ∈ neg, ¬ (e ⊆ z.1) ∧ ¬ (e ⊆ z.2) then 1 else 0
  let vw : Fin n → ℝ := fun _ => 1
  have hfits_iff : ∀ M, IsMatching V M →
      (fits (matchFn M) ↔ F₂ ⊆ M ∧ (∀ R ∈ H, ∃ e ∈ M, e ⊆ R) ∧
        ∀ e ∈ M, ∀ z ∈ neg, ¬ (e ⊆ z.1) ∧ ¬ (e ⊆ z.2)) := by
    intro M hM
    constructor
    · rintro ⟨_, hposM, hnegM⟩
      refine ⟨?_, ?_, ?_⟩
      · intro R hR
        rw [Finset.mem_filter, List.mem_toFinset] at hR
        have h' : matchFn M (fun i => decide (i ∈ R)) (fun _ => decide False) = true := by
          simpa [obs] using hposM R hR.1
        obtain ⟨e, heM, heR⟩ := (matchFn_obs_empty M hM R).mp h'
        have heq : e = R := Finset.eq_of_subset_of_card_le heR (by rw [(hM.1 e heM).1, hR.2])
        exact heq ▸ heM
      · intro R hR
        rw [Finset.mem_filter, List.mem_toFinset] at hR
        have h' : matchFn M (fun i => decide (i ∈ R)) (fun _ => decide False) = true := by
          simpa [obs] using hposM R hR.1
        exact (matchFn_obs_empty M hM R).mp h'
      · intro e heM z hz
        have h' : matchFn M (fun i => decide (i ∈ z.1)) (fun j => decide (j ∈ z.2)) = false := hnegM z hz
        exact ((matchFn_obs_pair M hM z.1 z.2).mp h').2 e heM
    · rintro ⟨hF₂M, hHM, hnegM⟩
      refine ⟨exists_circuit_of_matching hn M hM, ?_, ?_⟩
      · intro R hR
        have hle3 := hpos3 R hR
        have hge2 := hpos_ge2 R hR
        have h23 : R.card = 2 ∨ R.card = 3 := by omega
        have hex : ∃ e ∈ M, e ⊆ R := by
          rcases h23 with hc2 | hc3
          · exact ⟨R, hF₂M (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hR, hc2⟩), subset_refl R⟩
          · exact hHM R (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hR, hc3⟩)
        have h' := (matchFn_obs_empty M hM R).mpr hex
        simpa [obs] using h'
      · intro z hz
        exact (matchFn_obs_pair M hM z.1 z.2).mpr ⟨hneg_disj z hz, fun e heM => hnegM e heM z hz⟩
  let validM := (V.powerset.filter (fun e => e.card = 2)).powerset.filter
    (fun M => IsMatching V M ∧ F₂ ⊆ M ∧ (∀ R ∈ H, ∃ e ∈ M, e ⊆ R) ∧
      ∀ e ∈ M, ∀ z ∈ neg, ¬ (e ⊆ z.1) ∧ ¬ (e ⊆ z.2))
  have hbij_tot : total = validM.card := by
    classical
    rw [show total = Fintype.card {f : Fn // fits f} from Nat.card_eq_fintype_card]
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun ⟨f, hf⟩ =>
          let M := Classical.choose (optimal_circuit_is_matchFn hn (Classical.choose hf.1)
            (Classical.choose_spec hf.1).1 (Classical.choose_spec hf.1).2.1 (Classical.choose_spec hf.1).2.2.1)
          have hMspec := Classical.choose_spec (optimal_circuit_is_matchFn hn (Classical.choose hf.1)
            (Classical.choose_spec hf.1).1 (Classical.choose_spec hf.1).2.1 (Classical.choose_spec hf.1).2.2.1)
          have hf_eq : f = matchFn M := by
            ext x y; rw [(Classical.choose_spec hf.1).2.2.2 x y, hMspec.2 x y]
          have hcond := (hfits_iff M hMspec.1).mp (hf_eq ▸ hf)
          ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun e he =>
            Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hMspec.1.1 e he).2, (hMspec.1.1 e he).1⟩),
            hMspec.1, hcond.1, hcond.2.1, hcond.2.2⟩⟩
        invFun := fun ⟨M, hM⟩ =>
          have hMm := (Finset.mem_filter.mp hM).2.1
          have hc := (Finset.mem_filter.mp hM).2.2
          ⟨matchFn M, (hfits_iff M hMm).mpr ⟨hc.1, hc.2.1, hc.2.2⟩⟩
        left_inv := fun ⟨f, hf⟩ => by
          apply Subtype.ext
          dsimp only
          have hMspec := Classical.choose_spec (optimal_circuit_is_matchFn hn (Classical.choose hf.1)
            (Classical.choose_spec hf.1).1 (Classical.choose_spec hf.1).2.1 (Classical.choose_spec hf.1).2.2.1)
          ext x y; rw [(Classical.choose_spec hf.1).2.2.2 x y, hMspec.2 x y]
        right_inv := fun ⟨M, hM⟩ => by
          apply Subtype.ext
          have hMm := (Finset.mem_filter.mp hM).2.1
          have hc := (Finset.mem_filter.mp hM).2.2
          have hfit : fits (matchFn M) := (hfits_iff M hMm).mpr ⟨hc.1, hc.2.1, hc.2.2⟩
          have hMspec := Classical.choose_spec (optimal_circuit_is_matchFn hn (Classical.choose hfit.1)
            (Classical.choose_spec hfit.1).1 (Classical.choose_spec hfit.1).2.1 (Classical.choose_spec hfit.1).2.2.1)
          have heq : matchFn M = matchFn (Classical.choose (optimal_circuit_is_matchFn hn (Classical.choose hfit.1)
            (Classical.choose_spec hfit.1).1 (Classical.choose_spec hfit.1).2.1 (Classical.choose_spec hfit.1).2.2.1)) := by
            ext x y; rw [(Classical.choose_spec hfit.1).2.2.2 x y, hMspec.2 x y]
          exact (matchFn_inj hMm hMspec.1 heq).symm }
  have hbij_hist : ∀ s, hist s = (validM.filter (fun M => M.card = s)).card := by
    intro s
    classical
    rw [show hist s = Fintype.card {f : Fn // fits f ∧ size f = s} from Nat.card_eq_fintype_card]
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun ⟨f, hf, hsz⟩ =>
          let M := Classical.choose (optimal_circuit_is_matchFn hn (Classical.choose hf.1)
            (Classical.choose_spec hf.1).1 (Classical.choose_spec hf.1).2.1 (Classical.choose_spec hf.1).2.2.1)
          have hMspec := Classical.choose_spec (optimal_circuit_is_matchFn hn (Classical.choose hf.1)
            (Classical.choose_spec hf.1).1 (Classical.choose_spec hf.1).2.1 (Classical.choose_spec hf.1).2.2.1)
          have hf_eq : f = matchFn M := by
            ext x y; rw [(Classical.choose_spec hf.1).2.2.2 x y, hMspec.2 x y]
          have hcond := (hfits_iff M hMspec.1).mp (hf_eq ▸ hf)
          have hMsz : M.card = s := by
            rw [← matchFn_size M hMspec.1, ← hf_eq]; exact hsz
          ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun e he =>
            Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hMspec.1.1 e he).2, (hMspec.1.1 e he).1⟩),
            hMspec.1, hcond.1, hcond.2.1, hcond.2.2⟩, hMsz⟩⟩
        invFun := fun ⟨M, hM⟩ =>
          have hMv := (Finset.mem_filter.mp hM).1
          have hMsz := (Finset.mem_filter.mp hM).2
          have hMm := (Finset.mem_filter.mp hMv).2.1
          have hc := (Finset.mem_filter.mp hMv).2.2
          ⟨matchFn M, (hfits_iff M hMm).mpr ⟨hc.1, hc.2.1, hc.2.2⟩, by rw [← hMsz]; exact matchFn_size M hMm⟩
        left_inv := fun ⟨f, hf, _⟩ => by
          apply Subtype.ext
          dsimp only
          have hMspec := Classical.choose_spec (optimal_circuit_is_matchFn hn (Classical.choose hf.1)
            (Classical.choose_spec hf.1).1 (Classical.choose_spec hf.1).2.1 (Classical.choose_spec hf.1).2.2.1)
          ext x y; rw [(Classical.choose_spec hf.1).2.2.2 x y, hMspec.2 x y]
        right_inv := fun ⟨M, hM⟩ => by
          apply Subtype.ext
          have hMv := (Finset.mem_filter.mp hM).1
          have hMm := (Finset.mem_filter.mp hMv).2.1
          have hc := (Finset.mem_filter.mp hMv).2.2
          have hfit : fits (matchFn M) := (hfits_iff M hMm).mpr ⟨hc.1, hc.2.1, hc.2.2⟩
          have hMspec := Classical.choose_spec (optimal_circuit_is_matchFn hn (Classical.choose hfit.1)
            (Classical.choose_spec hfit.1).1 (Classical.choose_spec hfit.1).2.1 (Classical.choose_spec hfit.1).2.2.1)
          have heq : matchFn M = matchFn (Classical.choose (optimal_circuit_is_matchFn hn (Classical.choose hfit.1)
            (Classical.choose_spec hfit.1).1 (Classical.choose_spec hfit.1).2.1 (Classical.choose_spec hfit.1).2.2.1)) := by
            ext x y; rw [(Classical.choose_spec hfit.1).2.2.2 x y, hMspec.2 x y]
          exact (matchFn_inj hMm hMspec.1 heq).symm }
  have hsum_eq_Z : ∀ z : ℂ, (Finset.range (d + 1)).sum (fun s => (hist s : ℂ) * z ^ s) =
      ZPoly V F₂ H vw ew z := by
    intro z
    unfold ZPoly
    set AllM := (V.powerset.filter (fun e => e.card = 2)).powerset.filter
      (fun M => IsMatching V M ∧ F₂ ⊆ M ∧ ∀ R ∈ H, ∃ e ∈ M, e ⊆ R)
    have hprod_ew : ∀ M ∈ AllM,
        ((∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card =
        if M ∈ validM then z ^ M.card else 0 := by
      intro M hM
      simp only [vw, Complex.ofReal_one, Finset.prod_const_one, one_mul]
      by_cases hMv : M ∈ validM
      · rw [if_pos hMv]
        have hall : ∀ e ∈ M, (ew e : ℂ) = 1 := fun e he => by
          have hnegM := (Finset.mem_filter.mp hMv).2.2.2.2 e he
          simp only [ew, if_pos hnegM, Complex.ofReal_one]
        rw [Finset.prod_eq_one hall, one_mul]
      · rw [if_neg hMv]
        have hnot : ¬ ∀ e ∈ M, ∀ z ∈ neg, ¬ (e ⊆ z.1) ∧ ¬ (e ⊆ z.2) := by
          intro hall
          have h1 := Finset.mem_filter.mp hM
          exact hMv (Finset.mem_filter.mpr ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, hall⟩)
        push_neg at hnot
        rcases hnot with ⟨e, heM, z₀, hz₀, hbad⟩
        have hew0 : (ew e : ℂ) = 0 := by
          have hneg : ¬ ∀ z ∈ neg, ¬ (e ⊆ z.1) ∧ ¬ (e ⊆ z.2) := fun h => by
            have := h z₀ hz₀; tauto
          simp only [ew, if_neg hneg, Complex.ofReal_zero]
        rw [Finset.prod_eq_zero heM hew0, zero_mul]
    have hAllM_eq : ZPoly V F₂ H vw ew z =
        ∑ M ∈ AllM, ((∏ v ∈ V \ M.biUnion id, (vw v : ℂ)) * (∏ e ∈ M, (ew e : ℂ))) * z ^ M.card := by
      unfold ZPoly
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext M; simp only [AllM, Finset.mem_filter]
    symm
    change ZPoly V F₂ H vw ew z = _
    rw [hAllM_eq, Finset.sum_congr rfl hprod_ew, ← Finset.sum_filter]
    have hfilt_eq : AllM.filter (fun M => M ∈ validM) = validM := by
      ext M; simp only [Finset.mem_filter, AllM, validM]; tauto
    rw [hfilt_eq]
    have hcard_le_d : ∀ M ∈ validM, M.card ∈ Finset.range (d + 1) := by
      intro M hM
      have hMm := (Finset.mem_filter.mp hM).2.1
      have h2 := two_mul_card_le_of_matching hMm
      simp only [V, Finset.card_univ, Fintype.card_fin] at h2
      rw [Finset.mem_range]; omega
    rw [← Finset.sum_fiberwise_of_maps_to hcard_le_d]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hbij_hist s]
    have hconst : ∑ M ∈ validM.filter (fun M => M.card = s), z ^ M.card =
        ∑ _M ∈ validM.filter (fun M => M.card = s), z ^ s :=
      Finset.sum_congr rfl (fun M hM => by rw [(Finset.mem_filter.mp hM).2])
    rw [hconst, Finset.sum_const, nsmul_eq_mul]
  have hsum_hist_tot : ∑ s ∈ Finset.range (d + 1), hist s = total := by
    have h1 := hsum_eq_Z 1
    have hcard_le_d : ∀ M ∈ validM, M.card ∈ Finset.range (d + 1) := by
      intro M hM
      have hMm := (Finset.mem_filter.mp hM).2.1
      have h2 := two_mul_card_le_of_matching hMm
      simp only [V, Finset.card_univ, Fintype.card_fin] at h2
      rw [Finset.mem_range]; omega
    rw [hbij_tot]
    have h2 : ∑ s ∈ Finset.range (d + 1), (validM.filter (fun M => M.card = s)).card = validM.card :=
      Finset.sum_card_fiberwise_eq_card_filter validM (Finset.range (d + 1)) Finset.card |> fun h => by
        rw [h]; congr 1; ext M; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hcard_le_d M
    simpa [hbij_hist] using h2
  have hZ1_pos : 0 < (ZPoly V F₂ H vw ew 1).re := by
    rw [← hsum_eq_Z 1]
    simp only [one_pow, mul_one, Complex.re_sum, Complex.natCast_re]
    have : ∑ s ∈ Finset.range (d + 1), (hist s : ℝ) = (total : ℝ) := by
      exact_mod_cast hsum_hist_tot
    rw [this]
    exact Nat.cast_pos.mpr htot_pos
  have hF₂_ok : ∀ e ∈ F₂, e.card = 2 ∧ e ⊆ V := fun e he => ⟨(Finset.mem_filter.mp he).2, Finset.subset_univ e⟩
  have hH_ok : ∀ R ∈ H, R.card = 3 ∧ R ⊆ V := fun R hR => ⟨(Finset.mem_filter.mp hR).2, Finset.subset_univ R⟩
  have hdeg_ok : ∀ v ∈ V, (H.filter (fun R => v ∈ R)).card ≤ 2 := fun v _ => by
    have heq : H.filter (fun R => v ∈ R) = pos.toFinset.filter (fun R => R.card = 3 ∧ v ∈ R) := by
      ext R; simp only [H, Finset.mem_filter]; tauto
    rw [heq]; exact hdeg3 v
  have hew_nn : ∀ e, 0 ≤ ew e := fun e => by simp only [ew]; split_ifs <;> norm_num
  obtain ⟨k, C₀, W, w, hC₀, hw, hZ_red⟩ := reduce_ZPoly V.card V F₂ H vw ew (le_refl _)
    hF₂_ok hH_ok hdeg_ok (fun _ _ => zero_lt_one) hew_nn hZ1_pos
  have hpart2 : ∀ z : ℂ, (Finset.range (d + 1)).sum (fun s => (hist s : ℂ) * z ^ s) = 0 →
      z.im = 0 ∧ z.re ≤ 0 := by
    intro z hz
    rw [hsum_eq_Z z, hZ_red z] at hz
    rcases mul_eq_zero.mp hz with h1 | hM0
    · rcases mul_eq_zero.mp h1 with hC | hzk
      · exact absurd hC (Complex.ofReal_ne_zero.mpr (ne_of_gt hC₀))
      · have hz0 : z = 0 := eq_zero_of_pow_eq_zero hzk
        simp [hz0]
    · have hneg := MPoly_roots_real_neg W w hw z hM0
      exact ⟨hneg.1, le_of_lt hneg.2⟩
  have hpart1 : ∃ p : Fin d → ℝ, (∀ j, 0 ≤ p j ∧ p j ≤ 1) ∧ ∀ x : ℝ,
      (Finset.range (d + 1)).sum (fun s => (hist s : ℝ) * x ^ s) =
        (total : ℝ) * ∏ j : Fin d, (1 - p j + p j * x) := by
    let P_R : Polynomial ℝ := ∑ s ∈ Finset.range (d + 1), Polynomial.C (hist s : ℝ) * Polynomial.X ^ s
    have hPR_eval : ∀ x : ℝ, P_R.eval x = ∑ s ∈ Finset.range (d + 1), (hist s : ℝ) * x ^ s := by
      intro x; simp only [P_R, ← Polynomial.coe_evalRingHom, map_sum]; simp [Polynomial.coe_evalRingHom]
    have hPR_map_eval : ∀ z : ℂ, (P_R.map (algebraMap ℝ ℂ)).eval z =
        ∑ s ∈ Finset.range (d + 1), (hist s : ℂ) * z ^ s := by
      intro z
      simp only [P_R, Polynomial.map_sum, ← Polynomial.coe_evalRingHom, map_sum]; simp [Polynomial.coe_evalRingHom]
    have hPR_ne : P_R ≠ 0 := by
      intro h0
      have h1 : P_R.eval 1 = 0 := by rw [h0]; simp
      rw [hPR_eval 1] at h1
      simp only [one_pow, mul_one] at h1
      have htot_eq : ∑ s ∈ Finset.range (d + 1), (hist s : ℝ) = (total : ℝ) := by exact_mod_cast hsum_hist_tot
      rw [htot_eq] at h1
      exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt htot_pos)) h1
    have hPR_deg : P_R.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro j hj
      dsimp only [P_R]
      rw [← Polynomial.lcoeff_apply, map_sum]; simp only [Polynomial.lcoeff_apply]
      refine Finset.sum_eq_zero (fun s hs => ?_)
      have hsj : s ≠ j := by rw [Finset.mem_range] at hs; omega
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hsj.symm]
    obtain ⟨c, r, hr, hP_fac⟩ := factor_real_nonpos_roots P_R.natDegree P_R hPR_ne rfl
      (fun z hz => hpart2 z (by rw [← hPR_map_eval]; exact hz))
    let m := P_R.natDegree
    let p : Fin d → ℝ := fun j => if h : j.val < m then 1 / (1 + r ⟨j.val, h⟩) else 0
    refine ⟨p, ?_, ?_⟩
    · intro j
      simp only [p]
      split_ifs with hj
      · have hrj : 0 ≤ r ⟨j.val, hj⟩ := hr ⟨j.val, hj⟩
        refine ⟨div_nonneg zero_le_one (by linarith), ?_⟩
        rw [div_le_one (by linarith)]; linarith
      · exact ⟨le_refl 0, zero_le_one⟩
    · intro x
      have htot_fac : (total : ℝ) = c * ∏ i : Fin m, (1 + r i) := by
        have h1 : P_R.eval 1 = (total : ℝ) := by
          rw [hPR_eval 1]
          simp only [one_pow, mul_one]
          exact_mod_cast hsum_hist_tot
        rw [← h1, hP_fac]
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_add,
          Polynomial.eval_X]
        rfl
      have hprod_split : (∏ j : Fin d, (1 - p j + p j * x)) =
          ∏ i : Fin m, (x + r i) / (1 + r i) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j : Fin d => j.val < m)]
        have hhi : ∏ j ∈ Finset.univ.filter (fun j : Fin d => ¬ j.val < m), (1 - p j + p j * x) = 1 := by
          refine Finset.prod_eq_one (fun j hj => ?_)
          have hnot : ¬ j.val < m := (Finset.mem_filter.mp hj).2
          simp [p, hnot]
        rw [hhi, mul_one]
        refine Finset.prod_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin m)) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro j₁ _ j₂ _ heq; exact Fin.ext (congrArg (fun k : Fin m => k.val) heq)
        · intro i _; exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hPR_deg⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩
        · intro j hj
          have hlt : j.val < m := (Finset.mem_filter.mp hj).2
          have hpos1 : 0 < 1 + r ⟨j.val, hlt⟩ := by linarith [hr ⟨j.val, hlt⟩]
          simp only [p, hlt, ↓reduceDIte]
          field_simp [ne_of_gt hpos1]
          ring
      rw [← hPR_eval x, hP_fac, htot_fac, hprod_split]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_add,
        Polynomial.eval_X]
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hpos1 : 0 < 1 + r i := by linarith [hr i]
      field_simp [ne_of_gt hpos1]
  have hpart3 : ∀ s : Nat, 0 < s → s < d →
      hist (s - 1) * hist (s + 1) * (d.choose s) ^ 2 ≤
        (hist s) ^ 2 * d.choose (s - 1) * d.choose (s + 1) :=
    newton_ineq_of_real_roots d hist (fun z hz => (hpart2 z hz).1) (by rw [hsum_hist_tot]; exact htot_pos)
  exact ⟨hpart1, hpart2, hpart3⟩

end PEqualNP.Outside.L_meta_32576_aux

theorem PEqualNP.Outside.L_meta_32576 : (∀ (n : Nat), 2 ≤ n →
  ∀ (pos : List (Finset (Fin n))) (neg : List (Finset (Fin n) × Finset (Fin n))),
  (∀ R ∈ pos, R.card ≤ 3) →
  (∀ i : Fin n, (pos.toFinset.filter (fun R => R.card = 3 ∧ i ∈ R)).card ≤ 2) →
  let Fn := (Fin n → Bool) → (Fin n → Bool) → Bool
  let obs := fun (f : Fn) (R S : Finset (Fin n)) =>
    f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S))
  let fits := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*n ∧
    PEqualNP.Represents.Represents (fun i j : Fin n => decide (i=j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
    (∀ R ∈ pos, obs f R ∅ = true) ∧ (∀ z ∈ neg, obs f z.1 z.2 = false)

  let size := fun f : Fn => (Finset.univ.filter (fun z : Fin n × Fin n =>
    z.1 < z.2 ∧ obs f {z.1,z.2} ∅ = true)).card
  let hist := fun s : Nat => Nat.card {f : Fn // fits f ∧ size f = s}

  let total := Nat.card {f : Fn // fits f}
  let d := n/2
  0 < total →
    (∃ p : Fin d → ℝ, (∀ j, 0 ≤ p j ∧ p j ≤ 1) ∧ ∀ x : ℝ,
      (Finset.range (d+1)).sum (fun s => (hist s : ℝ)*x^s) =
        (total : ℝ)* ∏ j : Fin d, (1-p j+p j*x)) ∧
    (∀ z : ℂ, (Finset.range (d+1)).sum (fun s => (hist s : ℂ)*z^s) = 0 →
      z.im = 0 ∧ z.re ≤ 0) ∧
    ∀ s : Nat, 0 < s → s < d →
      hist (s-1)*hist (s+1)*(d.choose s)^2 ≤
        (hist s)^2 * d.choose (s-1) * d.choose (s+1)) := by
  exact PEqualNP.Outside.L_meta_32576_aux.main_proof

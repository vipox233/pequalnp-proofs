import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20612

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i ∈ ins, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i hi (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hi hv⟩

theorem sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
    (∀ g ∈ gs, g.op = .and ∨ g.op = .or) → W1.length = D.length → W2.length = D.length →
    (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = true → W2.getD w false = true) →
    ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
      (gs.foldl wstep W1).getD w false = true → (gs.foldl wstep W2).getD w false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 D _ _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 D hop h1 h2 h
    simp only [List.foldl_cons]
    apply ih
    · exact fun a ha => hop a (List.mem_cons_of_mem _ ha)
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro w hw
      simp only [wstep, dstep] at hw ⊢
      rw [getD_snoc, getD_snoc]
      rw [getD_snoc] at hw
      rw [h1, h2]
      split_ifs with c1 c2
      · rw [if_pos c1] at hw; exact h w hw
      · rw [if_neg c1, if_pos c2] at hw
        apply eval_mono _ (hop g List.mem_cons_self)
        intro j hj
        apply h j
        intro i hi
        apply hw
        rw [Finset.mem_biUnion]
        exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
      · exact id

theorem cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
    ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
      T.card + k + gs.length := by
  intro gs
  induction gs with
  | nil => intro D k _ h T; simpa using h T
  | cons g gs ih =>
    intro D k hg h T
    simp only [List.foldl_cons, List.length_cons]
    have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
    · omega
    intro T
    have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
        ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨w, hw, hi⟩ := hi
      simp only [dstep] at hi
      rw [getD_snoc] at hi
      rw [Finset.mem_biUnion]
      split_ifs at hi with c1 c2
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
      · rw [Finset.mem_biUnion] at hi
        obtain ⟨j, hj, hi⟩ := hi
        exact ⟨j, Finset.mem_union_right _ hj, hi⟩
      · simp at hi
    have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
    have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
    have h4 := List.toFinset_card_le g.inputs
    have h5 := hg g List.mem_cons_self
    have h6 := Finset.card_le_card hsub
    by_cases hm : D.length ∈ T
    · have h7 := Finset.card_erase_of_mem hm
      have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
          T.biUnion fun w => D.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        simp only [dstep]
        rw [getD_snoc]
        have : w ≠ D.length := fun e => hm (e ▸ hw)
        split_ifs with c1
        · rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h9]; have := h T; omega

theorem base_card (n : ℕ) (T : Finset ℕ) :
    (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
      T.card + 0 := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [Nat.add_zero]
  calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
      ≤ ∑ w ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro w _
        rw [List.getD_eq_getElem?_getD]
        by_cases hw : w < n
        · simp [hw]
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
    _ = T.card := by simp

def relation (u v : Fin 5) : Bool := (12978208 : ℕ).testBit (5 * u.val + v.val)

def required : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8}

theorem comparison : ∀ i : Fin 10, i.val ∈ required →
    ∃ a b c d : Fin 5, relation a b = true ∧ relation c d = false ∧
      ∀ j : Fin 10, j.val ≠ i.val →
        (oneEach a b).getD j.val false = true → (oneEach c d).getD j.val false = true := by
  decide +kernel

theorem lower : ¬ RepSizeAtMost relation 6 := by
  rintro ⟨C, hm, hs, hr⟩
  let D0 : List (Finset ℕ) := (List.range 10).map fun i => ({i} : Finset ℕ)
  let S := (C.gates.foldl dstep D0).getD C.output ∅
  have sub : required ⊆ S := by
    intro i hi
    have ib : i < 10 := by
      have h : ∀ i ∈ required, i < 10 := by decide
      exact h _ hi
    by_contra absent
    obtain ⟨a,b,c,d,yes,no,cmp⟩ := comparison ⟨i,ib⟩ hi
    let x := oneEach a b
    let y := oneEach c d
    have lx : x.length = 10 := by simp [x, oneEach]
    have ly : y.length = 10 := by simp [y, oneEach]
    have step := sem (fun j => x.getD j false = true → y.getD j false = true)
      C.gates x y D0 (fun g hg => by simpa using (hm g hg).1)
      (by simpa [D0] using lx) (by simpa [D0] using ly) ?_ C.output ?_
    · have hv : C.eval x = true := (hr a b).trans yes
      have hn : C.eval y = false := (hr c d).trans no
      change C.eval x = true → C.eval y = true at step
      exact Bool.noConfusion (hn.symm.trans (step hv))
    · intro w h
      by_cases hw : w < 10
      · apply h w
        simp [D0, List.getD_eq_getElem?_getD, hw]
      · rw [List.getD_eq_default _ _ (by omega : x.length ≤ w)]
        simp
    · intro j hj
      by_cases jw : j < 10
      · exact cmp ⟨j,jw⟩ (by intro e; change j = i at e; exact absent (e ▸ hj))
      · rw [List.getD_eq_default _ _ (by omega : x.length ≤ j)]
        simp
  have hc := cardb C.gates D0 0 (fun g hg => (hm g hg).2) (base_card 10) {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  have h := Finset.card_le_card sub
  have hn : required.card = 8 := by decide
  change C.gates.length ≤ 6 at hs
  change S.card ≤ 1 + 0 + C.gates.length at hc
  omega

def witness : Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [15, 14]⟩],16⟩

theorem upper : RepSizeAtMost relation 7 := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_20612

theorem PEqualNP.Outside.L_meta_20612 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12978208 : ℕ).testBit (5 * u.val + v.val)) 7 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12978208 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  exact ⟨PEqualNP.Outside.L_meta_20612.upper, PEqualNP.Outside.L_meta_20612.lower⟩

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20629

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def gateStep (xs : List Bool) (g : Gate) :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

def Agree (T : Finset ℕ) (x y : List Bool) : Prop :=
  ∀ i ∈ T, x.getD i false = true → y.getD i false = true

theorem unchanged (xs : List Bool) (b : Bool) (i : ℕ) (h : i ≠ xs.length) :
    (xs ++ [b]).getD i false = xs.getD i false := by
  by_cases hi : i < xs.length
  · exact List.getD_append _ _ _ _ hi
  · have ha : (xs ++ [b]).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none ha,
      List.getElem?_eq_none (show xs.length ≤ i by omega)]

theorem atNew (xs : List Bool) (g : Gate) :
    (gateStep xs g).getD xs.length false = g.op.eval (g.inputs.map fun i => xs.getD i false) := by
  simp [gateStep, List.getD_eq_getElem?_getD]

theorem gateImpl (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (h : Agree g.inputs.toFinset x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
    g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases hg with ha | ho
  · simp only [ha, GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id_eq]
    intro hx i hi
    exact h i (List.mem_toFinset.mpr hi) (hx i hi)
  · simp only [ho, GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, h i (List.mem_toFinset.mpr hi) hx⟩

theorem support (gs : List Gate)
    (mono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (N : ℕ) (goal : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ goal.card + gs.length ∧
      ∀ x y : List Bool, x.length = N → y.length = N → Agree S x y →
        Agree goal (gs.foldl gateStep x) (gs.foldl gateStep y) := by
  induction gs generalizing N with
  | nil => exact ⟨goal, by simp, fun _ _ _ _ h => h⟩
  | cons g gs ih =>
    have hg := mono g (by simp)
    obtain ⟨T, ct, ht⟩ := ih (fun z hz => mono z (List.mem_cons_of_mem _ hz)) (N + 1)
    let S := if N ∈ T then T.erase N ∪ g.inputs.toFinset else T
    refine ⟨S, ?_, ?_⟩
    · by_cases hn : N ∈ T
      · have a := Finset.card_union_le (T.erase N) g.inputs.toFinset
        have b := Finset.card_erase_add_one hn
        have d := List.toFinset_card_le g.inputs
        simp only [S, ite_eq_left hn, List.length_cons]
        omega
      · simp only [S, ite_eq_right hn, List.length_cons]; omega
    · intro x y hx hy h
      apply ht _ _ (by simp [gateStep, hx]) (by simp [gateStep, hy])
      intro i hi
      by_cases e : i = N
      · subst i
        have hinputs : Agree g.inputs.toFinset x y := by
          intro j hj
          exact h j (by simp only [S, ite_eq_left hi, Finset.mem_union]; exact Or.inr hj)
        rw [← hx, atNew, hx, ← hy, atNew]
        exact gateImpl g hg.1 x y hinputs
      · have hs : i ∈ S := by
          by_cases hn : N ∈ T
          · simp only [S, ite_eq_left hn, Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨e, hi⟩
          · simpa [S, hn] using hi
        unfold gateStep
        rw [unchanged _ _ _ (by rwa [hx]), unchanged _ _ _ (by rwa [hy])]
        exact h i hs

def graph (u : Fin 5) (v : Fin 5) : Bool := (29426720 : ℕ).testBit (5 * u.val + v.val)
def must : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9}

def wit : ℕ → Fin 5 × Fin 5 × Fin 5 × Fin 5
  | 1 => (1, 0, 0, 0)
  | 2 => (2, 0, 0, 0)
  | 3 => (3, 1, 0, 1)
  | 4 => (4, 2, 0, 2)
  | 5 => (1, 0, 1, 1)
  | 6 => (3, 1, 3, 0)
  | 7 => (4, 2, 4, 0)
  | 8 => (4, 3, 4, 0)
  | 9 => (4, 4, 4, 0)
  | _ => (0, 0, 0, 0)

theorem witnesses : ∀ i : Fin 10, i.val ∈ must →
    let p := wit i.val
    graph p.1 p.2.1 = true ∧ graph p.2.2.1 p.2.2.2 = false ∧
    ∀ j : Fin 10, j.val ≠ i.val →
      (oneEach p.1 p.2.1).getD j.val false = true →
      (oneEach p.2.2.1 p.2.2.2).getD j.val false = true := by
  decide +kernel

theorem lower : ¬ RepSizeAtMost graph 7 := by
  rintro ⟨C, mono, sz, rep⟩
  obtain ⟨S, card, hs⟩ := support C.gates (fun g hg => by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using mono g hg) 10 {C.output}
  have subset : must ⊆ S := by
    intro i hi
    by_contra missing
    have ilt : i < 10 := by simp [must] at hi; omega
    have hw := witnesses ⟨i, ilt⟩ hi
    dsimp only at hw
    obtain ⟨hpos, hneg, horder⟩ := hw
    let p := wit i
    have ord : Agree S (oneEach p.1 p.2.1) (oneEach p.2.2.1 p.2.2.2) := by
      intro j hj
      by_cases jlt : j < 10
      · apply horder ⟨j, jlt⟩
        intro e
        change j = i at e
        exact missing (e ▸ hj)
      · have hle : (oneEach p.1 p.2.1).length ≤ j := by simp [oneEach]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
    have ev := hs _ _ (by simp [oneEach]) (by simp [oneEach]) ord C.output (by simp)
    change C.eval (oneEach p.1 p.2.1) = true → C.eval (oneEach p.2.2.1 p.2.2.2) = true at ev
    rw [rep, rep, hpos, hneg] at ev
    simp at ev
  have ct := Finset.card_le_card subset
  have cm : must.card = 9 := by decide +kernel
  simp only [Finset.card_singleton] at card
  change C.gates.length ≤ 7 at sz
  omega

def witness : Circuit :=
  ⟨[⟨.or, [3, 7]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [5, 14]⟩, ⟨.or, [15, 16]⟩], 17⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

theorem upper : RepSizeAtMost graph 8 :=
  ⟨witness, witnessFit, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20629

open PEqualNP.Outside.L_meta_20629 in
theorem PEqualNP.Outside.L_meta_20629 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (29426720 : ℕ).testBit (5 * u.val + v.val)) 8 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (29426720 : ℕ).testBit (5 * u.val + v.val)) 7) :=
  ⟨upper, lower⟩

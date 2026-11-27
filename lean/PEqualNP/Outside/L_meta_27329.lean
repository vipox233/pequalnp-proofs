import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27329_aux
open PEqualNP.CircuitLowerBounds

private def A : Gate := ⟨.and, [0,4]⟩
private def B : Gate := ⟨.or, [2,6]⟩
private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private def seed (x : Fin 9 → Bool) := step (step (List.ofFn x) A) B
private theorem seed_len (x) : (seed x).length = 11 := by simp [seed, step]
private def pm (x : Fin 9 → Bool) :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
private def mask (i : Fin 9) : Nat := [160,96,80,132,68,66,20,12,10][i.val]!
private def low (i j : Fin 9) := (mask i).testBit j.val
private def high (i j : Fin 9) := decide (j = i) || low i j
private theorem cert : ∀ i : Fin 9, pm (low i) ≠ pm (high i) ∧
    ∀ j : Fin 11, j.val ≠ i.val → (seed (low i)).getD j false = (seed (high i)).getD j false := by decide

private theorem runAgree (gs : List Gate) (i : Nat) (u v : List Bool)
    (hl : u.length = v.length) (ha : ∀ j, j ≠ i → u.getD j false = v.getD j false)
    (hn : i ∉ gs.flatMap Gate.inputs) : ∀ j, j ≠ i →
    (gs.foldl step u).getD j false = (gs.foldl step v).getD j false := by
  induction gs generalizing u v with
  | nil => exact ha
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hn
    have e : g.inputs.map (fun j => u.getD j false) = g.inputs.map (fun j => v.getD j false) :=
      List.map_congr_left fun j hj => ha j (fun eq => hn.1 (eq ▸ hj))
    apply ih (step u g) (step v g) (by simp [step,hl]) _ hn.2
    intro j hj
    by_cases h : j < u.length
    · simpa only [step, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hl ▸ h)] using ha j hj
    · simp only [step, List.getD_append_right _ _ _ _ (by omega : u.length ≤ j),
        List.getD_append_right _ _ _ _ (by omega : v.length ≤ j), hl, e]

private theorem pinBound (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have := hf g (by simp)
    have := ih (fun k hk => hf k (by simp [hk]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

end PEqualNP.Outside.L_meta_27329_aux

open PEqualNP.Outside.L_meta_27329_aux PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_27329 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩)) := by
  rintro ⟨⟨gates,out⟩, hf, hs, hc, ho, _, _, live, hA, hB⟩
  cases gates with
  | nil => contradiction
  | cons a rest =>
    cases rest with
    | nil => contradiction
    | cons b gs =>
      change some a = some A at hA
      change some b = some B at hB
      cases Option.some.inj hA; cases Option.some.inj hB
      change (A :: B :: gs).length ≤ 11 at hs
      change out + 1 = 9 + (A :: B :: gs).length at ho
      simp only [List.length_cons] at hs ho
      change ∀ x, (gs.foldl step (seed x)).getD out false = pm x at hc
      let pins := out :: gs.flatMap Gate.inputs
      have raw (i : Fin 9) : i.val ∈ pins := by
        by_contra hn
        change i.val ∉ out :: gs.flatMap Gate.inputs at hn
        simp only [List.mem_cons, not_or] at hn
        apply (cert i).1
        rw [← hc, ← hc]
        apply runAgree _ i.val _ _ (by simp [seed_len]) _ hn.2 _ (Ne.symm hn.1)
        intro j hj
        by_cases h : j < 11
        · exact (cert i).2 ⟨j,h⟩ hj
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [seed_len]; omega : (seed (low i)).length ≤ j), List.getElem?_eq_none (by simp [seed_len]; omega : (seed (high i)).length ≤ j)]
      have sub : Finset.range (11 + gs.length) ⊆ pins.toFinset := by
        intro n hn
        apply List.mem_toFinset.mpr
        have hn := Finset.mem_range.mp hn
        by_cases h : n < 9
        · exact raw ⟨n,h⟩
        by_cases last : n = out
        · simp [pins,last]
        let j : Fin (A :: B :: gs).length := ⟨n-9, by simp; omega⟩
        obtain ⟨k, _, hk⟩ := live j (by change n-9+1 < (A :: B :: gs).length; simp; omega)
        have en : 9 + j.val = n := by dsimp [j]; omega
        rw [en] at hk
        have mem := (A :: B :: gs).get_mem k
        simp only [List.mem_cons] at mem
        rcases mem with eq | eq | mem
        · rw [eq] at hk; simp [A] at hk; omega
        · rw [eq] at hk; simp [B] at hk; omega
        · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,mem,hk⟩)
      have hcard := Finset.card_le_card sub
      rw [Finset.card_range] at hcard
      have plen := List.toFinset_card_le pins
      change pins.toFinset.card ≤ (gs.flatMap Gate.inputs).length + 1 at plen
      have bound := pinBound gs (fun g hg => (hf g (by simp [hg])).2)
      omega

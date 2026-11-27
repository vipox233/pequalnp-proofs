import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_27711_aux

def match3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def g0 : Gate := ⟨.or, [0, 4]⟩
def g1 : Gate := ⟨.or, [1, 2]⟩

def bits (m : ℕ) (j : Fin 9) : Bool := m.testBit j.val

theorem essential_after_prefix (i : Fin 9) :
    ∃ x y : Fin 9 → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
      (x 0 || x 4) = (y 0 || y 4) ∧
      (x 1 || x 2) = (y 1 || y 2) ∧ match3 x ≠ match3 y := by
  fin_cases i
  · exact ⟨bits 176, bits 177, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 100, bits 102, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 82, bits 86, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 132, bits 140, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 69, bits 85, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 66, bits 98, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 20, bits 84, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 12, bits 140, by decide, by decide, by decide, by decide⟩
  · exact ⟨bits 10, bits 266, by decide, by decide, by decide, by decide⟩

def EqExcept (i : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ j ≠ i, a.getD j false = b.getD j false

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

theorem append_bit {i : ℕ} {a b : List Bool} (h : EqExcept i a b) (v : Bool) :
    EqExcept i (a ++ [v]) (b ++ [v]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  by_cases hj' : j < a.length
  · rw [List.getD_append _ _ _ _ hj', List.getD_append _ _ _ _ (h.1 ▸ hj')]
    exact h.2 _ hj
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hj')]
    rw [List.getD_append_right _ _ _ _ (h.1 ▸ Nat.le_of_not_gt hj')]
    rw [h.1]

theorem step_preserve {i : ℕ} {a b : List Bool} (g : Gate)
    (h : EqExcept i a b) (hg : i ∉ g.inputs) : EqExcept i (step a g) (step b g) := by
  have hm : g.inputs.map (fun j => a.getD j false) = g.inputs.map (fun j => b.getD j false) :=
    List.map_congr_left (fun j hj => h.2 j (fun eq => hg (eq ▸ hj)))
  unfold step
  rw [hm]
  exact append_bit h _

theorem fold_preserve {i : ℕ} (gs : List Gate) :
    ∀ {a b : List Bool}, EqExcept i a b → i ∉ gs.flatMap Gate.inputs →
      EqExcept i (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b h _; exact h
  | cons g gs ih =>
    intro a b h hg
    have h' : i ∉ g.inputs ∧ i ∉ gs.flatMap Gate.inputs := by simpa using hg
    exact ih (step_preserve g h h'.1) h'.2

theorem initial_agree {i : Fin 9} {x y : Fin 9 → Bool}
    (h : ∀ j, j ≠ i → x j = y j) : EqExcept i.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  by_cases hlt : j < 9
  · have he : (⟨j,hlt⟩ : Fin 9) ≠ i := fun e => hj (congrArg Fin.val e)
    rw [List.getD, List.getD, List.getElem?_ofFn, List.getElem?_ofFn, dif_pos hlt, dif_pos hlt]
    exact h ⟨j,hlt⟩ he
  · rw [List.getD_eq_default, List.getD_eq_default] <;> simp [Nat.le_of_not_gt hlt]

theorem step_input (x : Fin 9 → Bool) (g : Gate) (j : Fin 9) :
    (step (List.ofFn x) g).getD j.val false = x j := by
  rw [step, List.getD_append _ _ _ _ (by simpa using j.isLt)]
  rw [List.getD, List.getElem?_ofFn, dif_pos j.isLt]
  rfl

theorem prefix_eval (x : Fin 9 → Bool) :
    step (step (List.ofFn x) g0) g1 =
      (List.ofFn x) ++ [x 0 || x 4] ++ [x 1 || x 2] := by
  have hx0 : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD, List.getElem?_ofFn]
  have hx4 : (List.ofFn x).getD 4 false = x 4 := by simp [List.getD, List.getElem?_ofFn]
  have hx1 : (step (List.ofFn x) g0).getD 1 false = x 1 := step_input x g0 1
  have hx2 : (step (List.ofFn x) g0).getD 2 false = x 2 := step_input x g0 2
  unfold step at ⊢
  change (step (List.ofFn x) g0 ++
      [GateOp.or.eval [(step (List.ofFn x) g0).getD 1 false, (step (List.ofFn x) g0).getD 2 false]]) = _
  rw [hx1,hx2]
  unfold step
  change (List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false]] ++ _) = _
  rw [hx0,hx4]
  simp [GateOp.eval]

theorem primary_in_tail (gs : List Gate) (out : ℕ) (hout : 9 ≤ out)
    (hf : ∀ x : Fin 9 → Bool, (Circuit.mk (g0 :: g1 :: gs) out).eval (List.ofFn x) = match3 x)
    (i : Fin 9) : i.val ∈ gs.flatMap Gate.inputs := by
  by_contra hn
  obtain ⟨x,y,hxy,h0,h1,hd⟩ := essential_after_prefix i
  have hp : EqExcept i.val (step (step (List.ofFn x) g0) g1) (step (step (List.ofFn y) g0) g1) := by
    rw [prefix_eval, prefix_eval, ← h0, ← h1]
    exact append_bit (append_bit (initial_agree hxy) _) _
  have h := (fold_preserve gs hp hn).2 out (by have := i.isLt; omega)
  exact hd ((hf x).symm.trans (h.trans (hf y)))

theorem tail_entries (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2*gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem fixed_prefix_lower (C : Circuit) (hfan : FanInTwo C)
    (hf : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = match3 x)
    (hout : C.output+1=9+C.size)
    (hused : ∀ j : Fin C.gates.length, j.val+1<C.gates.length →
      ∃ k : Fin C.gates.length, j.val<k.val ∧ 9+j.val∈(C.gates.get k).inputs)
    (h0 : C.gates.head?=some g0) (h1 : C.gates.tail.head?=some g1) :
    12 ≤ C.size := by
  rcases C with ⟨gs,out⟩
  cases gs with
  | nil => simp at h0
  | cons a gs =>
    cases gs with
    | nil => simp at h1
    | cons b gs =>
      have ha : a = g0 := Option.some.inj h0
      have hb : b = g1 := Option.some.inj h1
      subst a
      subst b
      change out+1 = 9+(g0 :: g1 :: gs).length at hout
      simp only [List.length_cons] at hout
      have hreq : Finset.range (10 + gs.length) ⊆ (gs.flatMap Gate.inputs).toFinset := by
        intro z hz
        rw [Finset.mem_range] at hz
        rw [List.mem_toFinset]
        by_cases hz9 : z < 9
        · exact primary_in_tail gs out (by omega) hf ⟨z,hz9⟩
        · let j : Fin (g0 :: g1 :: gs).length := ⟨z-9, by simp; omega⟩
          obtain ⟨k, _, hk⟩ := hused j (by simp [j]; omega)
          let g := (g0 :: g1 :: gs).get k
          have hg : z ∈ g.inputs := by
            have eq : 9+j.val=z := by dsimp [j]; omega
            rwa [eq] at hk
          have hmem : g ∈ g0 :: g1 :: gs := List.get_mem _ _
          have htail : g ∈ gs := by
            rcases List.mem_cons.mp hmem with e | hrest
            · have hh : z ∈ g0.inputs := e ▸ hg
              simp [g0] at hh
              omega
            · rcases List.mem_cons.mp hrest with e | htail
              · have hh : z ∈ g1.inputs := e ▸ hg
                simp [g1] at hh
                omega
              · exact htail
          exact List.mem_flatMap.mpr ⟨g,htail,hg⟩
      have hc := Finset.card_le_card hreq
      rw [Finset.card_range] at hc
      have hlen := (List.toFinset_card_le (gs.flatMap Gate.inputs)).trans
        (tail_entries gs fun g hg => (hfan g (by simp [hg])).2)
      change 12 ≤ (g0 :: g1 :: gs).length
      simp only [List.length_cons]
      omega

end PEqualNP.Outside.L_meta_27711_aux

open PEqualNP.Outside.L_meta_27711_aux

theorem PEqualNP.Outside.L_meta_27711 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩) := by
  rintro ⟨C, hfan, hsize, hf, hout, _, _, hused, h0, h1⟩
  have h := fixed_prefix_lower C hfan hf hout hused h0 h1
  omega

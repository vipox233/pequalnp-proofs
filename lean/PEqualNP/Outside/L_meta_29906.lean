import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29906

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (u : ℕ) (hu : u < w.length) :
    (gs.foldl stepWire w).getD u false = w.getD u false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : u < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hu]

lemma foldl_agree (gs : List Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length)
    (h3_1 : w1.getD 3 false = true) (h3_2 : w2.getD 3 false = true)
    (h3lt : 3 < w1.length)
    (hagree : ∀ u, u ≠ 0 → w1.getD u false = w2.getD u false)
    (hgates : ∀ g ∈ gs, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ 3 ∈ g.inputs)) :
    ∀ u, u ≠ 0 → (gs.foldl stepWire w1).getD u false = (gs.foldl stepWire w2).getD u false := by
  induction gs generalizing w1 w2 with
  | nil => exact hagree
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have hval : g.op.eval (g.inputs.map fun a => w1.getD a false) =
        g.op.eval (g.inputs.map fun a => w2.getD a false) := by
      rcases hgates g (List.mem_cons_self) with hno0 | ⟨hor, h3in⟩
      · congr 1
        apply List.map_congr_left
        intro a ha
        exact hagree a (fun h0 => hno0 (h0 ▸ ha))
      · rw [hor]
        simp only [GateOp.eval, List.any_map]
        have b1 : (g.inputs.any (id ∘ fun a => w1.getD a false)) = true :=
          List.any_eq_true.mpr ⟨3, h3in, h3_1⟩
        have b2 : (g.inputs.any (id ∘ fun a => w2.getD a false)) = true :=
          List.any_eq_true.mpr ⟨3, h3in, h3_2⟩
        rw [b1, b2]
    apply ih (stepWire w1 g) (stepWire w2 g)
    · simp [stepWire, hlen]
    · rw [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left h3lt,
        ← List.getD_eq_getElem?_getD]
      exact h3_1
    · have h3lt2 : 3 < w2.length := by omega
      rw [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left h3lt2,
        ← List.getD_eq_getElem?_getD]
      exact h3_2
    · simp [stepWire]; omega
    · intro u hu
      by_cases hlt : u < w1.length
      · have hlt2 : u < w2.length := by omega
        rw [stepWire, stepWire, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hlt, List.getElem?_append_left hlt2,
          ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
        exact hagree u hu
      · by_cases heq : u = w1.length
        · subst heq
          have h1 : (stepWire w1 g).getD w1.length false =
              g.op.eval (g.inputs.map fun a => w1.getD a false) := by
            simp [stepWire, List.getD_eq_getElem?_getD]
          have h2 : (stepWire w2 g).getD w1.length false =
              g.op.eval (g.inputs.map fun a => w2.getD a false) := by
            rw [hlen]
            simp [stepWire, List.getD_eq_getElem?_getD]
          rw [h1, h2, hval]
        · have hge1 : (stepWire w1 g).length ≤ u := by simp [stepWire]; omega
          have hge2 : (stepWire w2 g).length ≤ u := by simp [stepWire]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
    · intro g' hg'
      exact hgates g' (List.mem_cons_of_mem g hg')

def xA : Fin 7 → Bool := fun t => decide (t.val = 1 ∨ t.val = 3)
def xB : Fin 7 → Bool := fun t => decide (t.val = 0 ∨ t.val = 1 ∨ t.val = 3)
def x0 : Fin 7 → Bool := fun t => decide (t.val = 0)

end PEqualNP.Outside.L_meta_29906

theorem PEqualNP.Outside.L_meta_29906 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 3 ∈ (C.gates.get i).inputs ∧ 3 ≠ 0 ∧ 3 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 3 false = true)) := by
  rintro ⟨C, i, k, _, _, _, heval, _, h0only, hopi, _, _, _, h3i, _, _, _⟩
  by_cases hout0 : C.output = 0
  · have h0 := heval PEqualNP.Outside.L_meta_29906.x0
    have hlhs : C.eval (List.ofFn PEqualNP.Outside.L_meta_29906.x0) = true := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [hout0]
      change (C.gates.foldl PEqualNP.Outside.L_meta_29906.stepWire
        (List.ofFn PEqualNP.Outside.L_meta_29906.x0)).getD 0 false = true
      rw [PEqualNP.Outside.L_meta_29906.foldl_getD_lt _ _ 0 (by simp)]
      decide
    rw [hlhs] at h0
    have hrhs : ((PEqualNP.Outside.L_meta_29906.x0 0 && PEqualNP.Outside.L_meta_29906.x0 1) ||
        (PEqualNP.Outside.L_meta_29906.x0 1 && PEqualNP.Outside.L_meta_29906.x0 2) ||
        (PEqualNP.Outside.L_meta_29906.x0 2 && PEqualNP.Outside.L_meta_29906.x0 3) ||
        (PEqualNP.Outside.L_meta_29906.x0 3 && PEqualNP.Outside.L_meta_29906.x0 4) ||
        (PEqualNP.Outside.L_meta_29906.x0 4 && PEqualNP.Outside.L_meta_29906.x0 5) ||
        (PEqualNP.Outside.L_meta_29906.x0 5 && PEqualNP.Outside.L_meta_29906.x0 6) ||
        (PEqualNP.Outside.L_meta_29906.x0 6 && PEqualNP.Outside.L_meta_29906.x0 0)) = false := by
      decide
    rw [hrhs] at h0
    cases h0
  · have hgates : ∀ g ∈ C.gates, 0 ∉ g.inputs ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 3 ∈ g.inputs) := by
      intro g hg
      obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
      by_cases h0 : 0 ∈ (C.gates.get j).inputs
      · right
        have hj : j = i := h0only j h0
        subst hj
        exact ⟨hopi, h3i⟩
      · exact Or.inl h0
    have hEq := PEqualNP.Outside.L_meta_29906.foldl_agree C.gates
      (List.ofFn PEqualNP.Outside.L_meta_29906.xA)
      (List.ofFn PEqualNP.Outside.L_meta_29906.xB)
      (by simp) (by decide) (by decide) (by simp)
      (by
        intro u hu
        by_cases hlt : u < 7
        · have hcases : u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 ∨ u = 6 := by omega
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      hgates C.output hout0
    have hA := heval PEqualNP.Outside.L_meta_29906.xA
    have hB := heval PEqualNP.Outside.L_meta_29906.xB
    change C.eval (List.ofFn PEqualNP.Outside.L_meta_29906.xA) =
      C.eval (List.ofFn PEqualNP.Outside.L_meta_29906.xB) at hEq
    rw [hA, hB] at hEq
    have hfalse : ((PEqualNP.Outside.L_meta_29906.xA 0 && PEqualNP.Outside.L_meta_29906.xA 1) ||
        (PEqualNP.Outside.L_meta_29906.xA 1 && PEqualNP.Outside.L_meta_29906.xA 2) ||
        (PEqualNP.Outside.L_meta_29906.xA 2 && PEqualNP.Outside.L_meta_29906.xA 3) ||
        (PEqualNP.Outside.L_meta_29906.xA 3 && PEqualNP.Outside.L_meta_29906.xA 4) ||
        (PEqualNP.Outside.L_meta_29906.xA 4 && PEqualNP.Outside.L_meta_29906.xA 5) ||
        (PEqualNP.Outside.L_meta_29906.xA 5 && PEqualNP.Outside.L_meta_29906.xA 6) ||
        (PEqualNP.Outside.L_meta_29906.xA 6 && PEqualNP.Outside.L_meta_29906.xA 0)) = false := by
      decide
    have htrue : ((PEqualNP.Outside.L_meta_29906.xB 0 && PEqualNP.Outside.L_meta_29906.xB 1) ||
        (PEqualNP.Outside.L_meta_29906.xB 1 && PEqualNP.Outside.L_meta_29906.xB 2) ||
        (PEqualNP.Outside.L_meta_29906.xB 2 && PEqualNP.Outside.L_meta_29906.xB 3) ||
        (PEqualNP.Outside.L_meta_29906.xB 3 && PEqualNP.Outside.L_meta_29906.xB 4) ||
        (PEqualNP.Outside.L_meta_29906.xB 4 && PEqualNP.Outside.L_meta_29906.xB 5) ||
        (PEqualNP.Outside.L_meta_29906.xB 5 && PEqualNP.Outside.L_meta_29906.xB 6) ||
        (PEqualNP.Outside.L_meta_29906.xB 6 && PEqualNP.Outside.L_meta_29906.xB 0)) = true := by
      decide
    rw [hfalse, htrue] at hEq
    cases hEq

import PEqualNP.Defs
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_29850

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma run_prefix (gs : List Gate) (w : List Bool) (k : Nat) (hk : k < w.length) :
    (run gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD k false = w.getD k false
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hk

lemma append_agree (w v : List Bool) (b : Bool) (hlen : w.length = v.length)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false) :
    ∀ k, k ≠ 0 → (w ++ [b]).getD k false = (v ++ [b]).getD k false := by
  intro k hk
  by_cases hkw : k < w.length
  · rw [List.getD_append _ _ _ _ hkw,
      List.getD_append _ _ _ _ (by omega)]
    exact heq k hk
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

lemma or_true (w : List Bool) (g : Gate) (j : Nat)
    (hop : g.op = GateOp.or) (hmem : j ∈ g.inputs) (hj : w.getD j false = true) :
    g.op.eval (g.inputs.map fun k => w.getD k false) = true := by
  rw [hop]
  change (g.inputs.map fun k => w.getD k false).any id = true
  apply List.any_eq_true.mpr
  exact ⟨true, List.mem_map.mpr ⟨j, hmem, hj⟩, rfl⟩

lemma run_agree (gs : List Gate) (j : Nat)
    (hgood : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = GateOp.or ∧ j ∈ g.inputs)
    (w v : List Bool) (hlen : w.length = v.length) (hjl : j < w.length)
    (hjw : w.getD j false = true) (hjv : v.getD j false = true)
    (heq : ∀ k, k ≠ 0 → w.getD k false = v.getD k false) :
    ∀ k, k ≠ 0 → (run gs w).getD k false = (run gs v).getD k false := by
  induction gs generalizing w v with
  | nil => exact heq
  | cons g gs ih =>
    have hval : g.op.eval (g.inputs.map fun k => w.getD k false) =
        g.op.eval (g.inputs.map fun k => v.getD k false) := by
      by_cases h0 : 0 ∈ g.inputs
      · obtain ⟨hop, hmem⟩ := hgood g (by simp) h0
        rw [or_true w g j hop hmem hjw, or_true v g j hop hmem hjv]
      · congr 1
        apply List.map_congr_left
        intro k hk
        apply heq k
        intro hz
        subst k
        exact h0 hk
    have hext : ∀ k, k ≠ 0 → (step w g).getD k false = (step v g).getD k false := by
      unfold step
      rw [hval]
      exact append_agree w v _ hlen heq
    change ∀ k, k ≠ 0 → (run gs (step w g)).getD k false =
      (run gs (step v g)).getD k false
    apply ih (fun g hg => hgood g (by simp [hg])) (step w g) (step v g)
    · simp [step, hlen]
    · simp [step]; omega
    · unfold step
      rw [List.getD_append _ _ _ _ hjl]
      exact hjw
    · unfold step
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hjv
    · exact hext

def cycle7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def pair (j : Nat) (b : Bool) : Fin 7 → Bool :=
  fun k => if k = 0 then b else decide (k.val = j ∨ k.val = (if j = 5 then 1 else 6))

lemma output_nonzero (C : Circuit)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x) : C.output ≠ 0 := by
  intro hz
  let z : Fin 7 → Bool := fun k => decide (k = 1 ∨ k = 2)
  have h := hc z
  change (run C.gates (List.ofFn z)).getD C.output false = cycle7 z at h
  rw [hz, run_prefix C.gates (List.ofFn z) 0 (by simp)] at h
  have hl : (List.ofFn z).getD 0 false = false := by decide
  have hr : cycle7 z = true := by decide
  rw [hl, hr] at h
  cases h

theorem obstruction (C : Circuit) (i : Fin C.gates.length) (j : Nat)
    (hj : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5)
    (hc : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cycle7 x)
    (hunique : ∀ q : Fin C.gates.length, 0 ∈ (C.gates.get q).inputs → q = i)
    (hop : (C.gates.get i).op = GateOp.or) (hmem : j ∈ (C.gates.get i).inputs) : False := by
  have hgood : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = GateOp.or ∧ j ∈ g.inputs := by
    intro g hg h0
    obtain ⟨q, hq⟩ := List.mem_iff_get.mp hg
    have h0q : 0 ∈ (C.gates.get q).inputs := by rw [hq]; exact h0
    have he := hunique q h0q
    subst q
    rw [← hq]
    exact ⟨hop, hmem⟩
  have hjl : j < (List.ofFn (pair j false)).length := by
    simp only [List.length_ofFn]
    omega
  have hjf : (List.ofFn (pair j false)).getD j false = true := by
    rcases hj with rfl | rfl | rfl | rfl <;> decide
  have hjt : (List.ofFn (pair j true)).getD j false = true := by
    rcases hj with rfl | rfl | rfl | rfl <;> decide
  have hinit : ∀ k, k ≠ 0 → (List.ofFn (pair j false)).getD k false =
      (List.ofFn (pair j true)).getD k false := by
    intro k hk
    cases k with
    | zero => exact (hk rfl).elim
    | succ k => rfl
  have he := run_agree C.gates j hgood (List.ofFn (pair j false))
    (List.ofFn (pair j true)) (by simp) hjl hjf hjt hinit C.output (output_nonzero C hc)
  change C.eval (List.ofFn (pair j false)) = C.eval (List.ofFn (pair j true)) at he
  rw [hc, hc] at he
  have hf : cycle7 (pair j false) = false := by
    rcases hj with rfl | rfl | rfl | rfl <;> decide
  have ht : cycle7 (pair j true) = true := by
    rcases hj with rfl | rfl | rfl | rfl <;> decide
  rw [hf, ht] at he
  cases he

end PEqualNP.Outside.L_meta_29850


theorem PEqualNP.Outside.L_meta_29850 :
¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 5 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 5 ∈ (C.gates.get i).inputs ∧ 5 ≠ 0 ∧ 5 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 5 false = true) := by
  rintro ⟨C, i, k, hi, hfan, hsize, heval, hread, hunique, hop, hkop, hik, hreadik, hpartner, hjne, hjl, hx⟩
  exact PEqualNP.Outside.L_meta_29850.obstruction C i 5 (by decide) heval hunique hop hpartner

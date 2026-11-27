import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29832

open PEqualNP.CircuitLowerBounds

def advance (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

theorem raw_read (gs : List Gate) (w : List Bool) (j : ℕ) (h : j < w.length) :
    (gs.foldl advance w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl advance (advance w g)).getD j false = w.getD j false
    rw [ih (advance w g) (by simp [advance]; omega)]
    exact List.getD_append _ _ _ _ h

theorem masked (b : ℕ) (gs : List Gate) (w v : List Bool)
    (rule : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ b ∈ g.inputs)
    (hlen : w.length = v.length) (hb : b < w.length)
    (hw : w.getD b false = true) (hv : v.getD b false = true)
    (agree : ∀ j, j ≠ 0 → w.getD j false = v.getD j false) :
    ∀ j, j ≠ 0 → (gs.foldl advance w).getD j false = (gs.foldl advance v).getD j false := by
  induction gs generalizing w v with
  | nil => exact agree
  | cons g gs ih =>
    have same : g.op.eval (g.inputs.map fun j => w.getD j false) =
        g.op.eval (g.inputs.map fun j => v.getD j false) := by
      by_cases reads : 0 ∈ g.inputs
      · obtain ⟨op, mem⟩ := rule g (by simp) reads
        have lit (u : List Bool) (h : u.getD b false = true) :
            g.op.eval (g.inputs.map fun j => u.getD j false) = true := by
          rw [op]
          change (g.inputs.map fun j => u.getD j false).any id = true
          apply List.any_eq_true.mpr
          exact ⟨u.getD b false, List.mem_map.mpr ⟨b, mem, rfl⟩, h⟩
        exact (lit w hw).trans (lit v hv).symm
      · congr 1
        apply List.map_congr_left
        intro j hj
        exact agree j (fun e => reads (e ▸ hj))
    apply ih (advance w g) (advance v g) (fun a ha => rule a (by simp [ha]))
        (by simp [advance, hlen]) (by simp [advance]; omega)
        ((List.getD_append _ _ _ _ hb).trans hw)
        ((List.getD_append _ _ _ _ (hlen ▸ hb)).trans hv)
    intro j hj
    unfold advance
    rw [same]
    by_cases h : j < w.length
    · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hlen ▸ h)]
      exact agree j hj
    · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), hlen]

def off (i : Fin 7) := decide (i.val = 1 ∨ i.val = 4)
def on (i : Fin 7) := decide (i.val = 0 ∨ i.val = 1 ∨ i.val = 4)
def singletonZero (i : Fin 7) := decide (i.val = 0)

end PEqualNP.Outside.L_meta_29832

theorem PEqualNP.Outside.L_meta_29832 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 4 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 4 ∈ (C.gates.get i).inputs ∧ 4 ≠ 0 ∧ 4 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 4 false = true)) := by
  rintro ⟨C, i, k, _, _, _, correct, _, unique, hor, _, _, _, mem, _⟩
  have rule (g) (hg : g ∈ C.gates) (h : 0 ∈ g.inputs) :
      g.op = .or ∧ 4 ∈ g.inputs := by
    obtain ⟨j, rfl⟩ := List.get_of_mem hg
    rw [unique j h]
    exact ⟨hor, mem⟩
  have nonzero : C.output ≠ 0 := by
    intro h
    have bad := correct PEqualNP.Outside.L_meta_29832.singletonZero
    change (C.gates.foldl PEqualNP.Outside.L_meta_29832.advance _).getD C.output false = false at bad
    rw [h, PEqualNP.Outside.L_meta_29832.raw_read _ _ _ (by simp)] at bad
    exact Bool.noConfusion bad
  have init : ∀ j : Fin 7, j.val ≠ 0 →
      (List.ofFn PEqualNP.Outside.L_meta_29832.on).getD j.val false =
      (List.ofFn PEqualNP.Outside.L_meta_29832.off).getD j.val false := by decide +kernel
  have agree := PEqualNP.Outside.L_meta_29832.masked 4 C.gates
    (List.ofFn PEqualNP.Outside.L_meta_29832.on) (List.ofFn PEqualNP.Outside.L_meta_29832.off)
    rule (by simp) (by decide) (by decide) (by decide) (by
      intro j hj
      by_cases h : j < 7
      · exact init ⟨j, h⟩ hj
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
    C.output nonzero
  change C.eval (List.ofFn PEqualNP.Outside.L_meta_29832.on) =
    C.eval (List.ofFn PEqualNP.Outside.L_meta_29832.off) at agree
  rw [correct, correct] at agree
  exact Bool.noConfusion agree

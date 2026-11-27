import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_29912
private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private theorem foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

private theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
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
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key


private def value (C : Circuit) (x : Fin 7 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private theorem value_in (C : Circuit) (x : Fin 7 → Bool) {w : ℕ} (hw : w < 7) :
    value C x w = x ⟨w, hw⟩ := by
  unfold value
  rw [wires_eq_foldl, foldl_getD_lt _ _ _ (by simpa using hw)]
  interval_cases w <;> rfl

private def readAt (C : Circuit) (x : Fin 7 → Bool) (j w : ℕ) : Bool :=
  if w < 7+j then value C x w else false

private theorem value_at (C : Circuit) (x : Fin 7 → Bool) (j : Fin C.gates.length) :
    value C x (7+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (readAt C x j.val)) := by
  unfold readAt value
  simp only [wires_eq_foldl]
  simpa only [List.length_ofFn, List.get_eq_getElem] using
    foldl_getD_gate C.gates (List.ofFn x) j.val j.isLt

private theorem value_far (C : Circuit) (x : Fin 7 → Bool) {w : ℕ} (h : 7+C.gates.length ≤ w) :
    value C x w = false := by
  apply getD_ge
  rw [wires_eq_foldl, foldl_length, List.length_ofFn]
  exact h

private def sample (b : Bool) (m : ℕ) (j : Fin 7) : Bool :=
  if j.val = 0 then b else m.testBit j.val

private def edge (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

private def pivot (k : Fin 2) : ℕ := if k = 0 then 2 else 64
private def pairMask (k : Fin 3) : ℕ := if k = 0 then 6 else if k = 1 then 24 else 96
private def probe (m : ℕ) (i : Fin 8) : Bool :=
  if i.val = 0 ∨ i.val = 7 then false else m.testBit i.val
private def clip (w : ℕ) : Fin 8 := ⟨min w 7, by omega⟩

private theorem collision : ∀ a b : Fin 8, ∃ p : Fin 2, ∃ q : Fin 3,
    probe (pivot p) a = probe (pairMask q) a ∧ probe (pivot p) b = probe (pairMask q) b := by decide

private theorem bit_at (C : Circuit) (m w : ℕ) :
    readAt C (sample false m) 0 w = probe m (clip w) := by
  by_cases hw : w < 7
  · simp [readAt, hw, value_in _ _ hw, probe, clip, Nat.min_eq_left (Nat.le_of_lt hw),
      Nat.ne_of_lt hw, sample]
  · simp [readAt, hw, probe, clip, Nat.min_eq_right (Nat.le_of_not_gt hw)]

private theorem first_collision (C : Circuit) (j : Fin C.gates.length) (hj : j.val = 0)
    (hlen : (C.gates.get j).inputs.length ≤ 2) :
    ∃ p : Fin 2, ∃ q : Fin 3, value C (sample false (pivot p)) 7 =
        value C (sample false (pairMask q)) 7 := by
  let ins := (C.gates.get j).inputs
  obtain ⟨p,q,ha,hb⟩ := collision (clip (ins.getD 0 7)) (clip (ins.getD 1 7))
  refine ⟨p,q,?_⟩
  have hv (m : ℕ) := value_at C (sample false m) j
  simp only [hj, Nat.add_zero] at hv
  rw [hv, hv]
  congr 1
  apply List.map_congr_left
  intro w hw
  change w ∈ ins at hw
  change ins.length ≤ 2 at hlen
  rw [bit_at, bit_at]
  have covered (l : List ℕ) (hl : l.length ≤ 2) (hm : w ∈ l) :
      w = l.getD 0 7 ∨ w = l.getD 1 7 := by
    cases l with
    | nil => simp at hm
    | cons a l =>
      cases l with
      | nil => simpa using Or.inl (List.mem_singleton.mp hm) (b := w = 7)
      | cons b l =>
        have lnil : l = [] := List.length_eq_zero_iff.mp (by simpa using hl)
        subst l
        simpa using hm
  rcases covered ins hlen hw with h | h
  · exact h ▸ ha
  · exact h ▸ hb

private theorem agreement (C : Circuit) (i : Fin C.gates.length) (hi : i.val = 8)
    (uniq : ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i)
    (hop : (C.gates.get i).op = .or) (hseven : 7 ∈ (C.gates.get i).inputs)
    (m : ℕ) (w : ℕ) (hn : w ≠ 0)
    (cond : w < 15 ∨ value C (sample false m) 7 = true) :
    value C (sample false m) w = value C (sample true m) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < 7
    · rw [value_in _ _ input, value_in _ _ input]
      simp [sample, hn]
    by_cases far : 7 + C.gates.length ≤ w
    · rw [value_far _ _ far, value_far _ _ far]
    let j : Fin C.gates.length := ⟨w-7, by omega⟩
    have index : 7+j.val = w := by dsimp [j]; omega
    have gate (b : Bool) := value_at C (sample b m) j
    rw [index] at gate
    rw [gate, gate]
    by_cases special : j = i
    · have hw : w = 15 := by rw [← index, special, hi]
      have seven : value C (sample false m) 7 = true := cond.resolve_left (by omega)
      have seven' : value C (sample true m) 7 = true := (ih 7 (by omega) (by decide) (Or.inl (by decide))).symm.trans seven
      have lit (b : Bool) (hval : value C (sample b m) 7 = true) :
          ((C.gates.get i).inputs.map (readAt C (sample b m) i.val)).any id = true := by
        apply List.any_eq_true.mpr
        exact ⟨true, List.mem_map.mpr ⟨7,hseven,by simpa [readAt, hi] using hval⟩,rfl⟩
      rw [special, hop]
      exact (lit false seven).trans (lit true seven').symm
    · congr 1
      apply List.map_congr_left
      intro v hv
      have hne : v ≠ 0 := by rintro rfl; exact special (uniq j hv)
      unfold readAt
      split_ifs with back
      · have vw : v < w := by omega
        exact ih v vw hne (cond.imp_left (fun h => by omega))
      · rfl

end PEqualNP.Outside.L_meta_29912
open PEqualNP.Outside.L_meta_29912

theorem PEqualNP.Outside.L_meta_29912 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 7 ∈ (C.gates.get i).inputs ∧ 7 ≠ 0 ∧ 7 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 7 false = true)) := by
  rintro ⟨C, i, k, hi, fan, size, correct, hz, onlyReader, hop, hand, later, uses, hseven, _⟩
  change C.gates.length = 10 at size
  have hk : k.val = 9 := by have := k.isLt; omega
  have computed (b : Bool) (m : ℕ) : value C (sample b m) C.output = edge (sample b m) :=
    correct _
  have nonzero : C.output ≠ 0 := by
    intro zero
    have h := computed true 0
    rw [zero, value_in _ _ (by decide)] at h
    exact Bool.noConfusion h
  let first : Fin C.gates.length := ⟨0,by omega⟩
  obtain ⟨p,q,shared⟩ := first_collision C first rfl (fan _ (List.get_mem ..)).2
  have piv : ∀ p : Fin 2, edge (sample false (pivot p)) = false ∧
      edge (sample true (pivot p)) = true := by decide
  have pos : ∀ q : Fin 3, edge (sample false (pairMask q)) = true := by decide
  have diff : value C (sample false (pivot p)) C.output ≠ value C (sample true (pivot p)) C.output := by
    rw [computed, computed, (piv p).1, (piv p).2]; decide
  have impossible := fun cond => diff (agreement C i hi onlyReader hop hseven (pivot p) C.output nonzero cond)
  have outputBound : 15 ≤ C.output := by
    by_contra! bad
    exact impossible (Or.inl bad)
  have firstOff : value C (sample false (pairMask q)) 7 = false := by
    rw [← shared]
    cases h : value C (sample false (pivot p)) 7 with
    | false => rfl
    | true => exact (impossible (Or.inr h)).elim
  let x := sample false (pairMask q)
  have zeroOff : value C x 0 = false := (value_in _ _ (by decide)).trans rfl
  have inputList (l : List ℕ) (h : l.length ≤ 2) (ha : 0 ∈ l) (hb : 7 ∈ l) :
      l = [0,7] ∨ l = [7,0] := by
    cases l with
    | nil => simp at ha
    | cons a l =>
      cases l with
      | nil => simp only [List.mem_singleton] at ha hb; omega
      | cons b rest =>
        have er : rest = [] := List.length_eq_zero_iff.mp (by simpa using h)
        subst rest
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with he | he <;> simp_all
  have orOff : value C x 15 = false := by
    have e := value_at C x i
    rw [hi,hop] at e
    rcases inputList _ (fan _ (List.get_mem ..)).2 hz hseven with inp | inp <;>
      rw [inp] at e <;> simpa [GateOp.eval, readAt, zeroOff, firstOff, x] using e
  have andOff : value C x 16 = false := by
    have e := value_at C x k
    rw [hk,hand] at e
    refine e.trans (List.all_eq_false.mpr ⟨false, ?_, by decide⟩)
    rw [hi] at uses
    exact List.mem_map.mpr ⟨15, uses, by simpa [readAt] using orOff⟩
  have outOff : value C x C.output = false := by
    rcases Nat.eq_or_lt_of_le outputBound with e | more
    · rw [← e]; exact orOff
    · by_cases e : C.output = 16
      · rw [e]; exact andOff
      · exact value_far _ _ (by omega)
  exact Bool.noConfusion (outOff.symm.trans ((computed false _).trans (pos q)))

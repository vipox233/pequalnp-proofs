import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowMergeWires
import PEqualNP.Outside.L_meta_30581
import PEqualNP.Outside.L_meta_17187

-- Uses the merged L-meta-30581 (exact monotone size n + m + 1 of the table) and
-- L-meta-17187 (the crown bound 2 N for fan-in-two circuits, via Transfer.bound_all).
-- Credit: tab_spec is adapted from edge_spec in L-meta-30581 (Lior Dagan Mantinband, PR 42624),
-- and the oneEach list identity in fanA_lower from the final theorem of L-meta-17187
-- (ChrisMythos, PR 22238).

namespace PEqualNP.Outside.L_meta_33675

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Represents (oneEach Represents RepSizeAtMost)

theorem tab_spec (a b : Nat) :
    (64478 : Nat).testBit (4 * min a 3 + min b 3) = !decide (a = b ∧ a < 3) := by
  have small : ∀ x y : Fin 4, (64478 : Nat).testBit (4 * x.val + y.val) =
      !decide (x.val = y.val ∧ x.val < 3) := by decide
  rw [small ⟨min a 3, by omega⟩ ⟨min b 3, by omega⟩]
  have h : (min a 3 = min b 3 ∧ min a 3 < 3) ↔ (a = b ∧ a < 3) := by omega
  simp only [h]

theorem oe_len {n m : Nat} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oe_left {n m : Nat} (u : Fin n) (v : Fin m) (i : Nat) (h : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, h, Fin.ext_iff]

theorem oe_right {n m : Nat} (u : Fin n) (v : Fin m) (j : Nat) (h : j < m) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, h, Fin.ext_iff]

theorem wires_snoc (gs : List Gate) (g : Gate) (o o' : Nat) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) o).wires x = (Circuit.mk gs o').wires x ++
      [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs o').wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.size :=
  PEqualNP.Outside.L_meta_17187.Transfer.length_wiresFrom C.gates x

/-- The five gate circuit of the three diagonal cells. -/
def gs5 (n m : Nat) : List Gate :=
  [⟨GateOp.and, [0, n]⟩, ⟨GateOp.and, [1, n + 1]⟩, ⟨GateOp.or, [n + m, n + m + 1]⟩,
    ⟨GateOp.and, [2, n + 2]⟩, ⟨GateOp.or, [n + m + 2, n + m + 3]⟩]

theorem gd (x t : List Bool) (i : Nat) :
    (x ++ t).getD i false = if i < x.length then x.getD i false else t.getD (i - x.length) false := by
  split
  · exact List.getD_append _ _ _ _ (by assumption)
  · exact List.getD_append_right _ _ _ _ (by omega)

def CB (n m : Nat) : Circuit := ⟨gs5 n m, n + m + 4⟩

theorem diag3 (a b : Nat) :
    ((decide (0 = a) && decide (0 = b)) || (decide (1 = a) && decide (1 = b)) ||
      (decide (2 = a) && decide (2 = b))) = decide (a = b ∧ a < 3) := by
  by_cases h0 : a = 0
  · subst h0; by_cases hb : b = 0 <;> simp [hb, eq_comm]
  by_cases h1 : a = 1
  · subst h1; by_cases hb : b = 1 <;> simp [hb, eq_comm]
  by_cases h2 : a = 2
  · subst h2; by_cases hb : b = 2 <;> simp [hb, eq_comm]
  have e0 : decide (0 = a) = false := by simp; omega
  have e1 : decide (1 = a) = false := by simp; omega
  have e2 : decide (2 = a) = false := by simp; omega
  have e3 : decide (a = b ∧ a < 3) = false := by simp; omega
  rw [e0, e1, e2, e3]; rfl

theorem CB_eval (n m : Nat) (hn : 3 ≤ n) (hm : 3 ≤ m) (u : Fin n) (v : Fin m) :
    (CB n m).eval (oneEach u v) = decide (u.val = v.val ∧ u.val < 3) := by
  have hx := oe_len u v
  have l0 := oe_left u v 0 (by omega)
  have l1 := oe_left u v 1 (by omega)
  have l2 := oe_left u v 2 (by omega)
  have r0 := oe_right u v 0 (by omega)
  have r1 := oe_right u v 1 (by omega)
  have r2 := oe_right u v 2 (by omega)
  rw [Nat.add_zero] at r0
  set x := oneEach u v
  unfold CB Circuit.eval Circuit.wires gs5
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
  have f1 : 1 < n + m := by omega
  have f2 : 2 < n + m := by omega
  have f4 : n + 1 < n + m := by omega
  have f5 : n + 2 < n + m := by omega
  have g0 : ¬ (n + m < n + m) := by omega
  have g1 : ¬ (n + m + 1 < n + m) := by omega
  have g2 : ¬ (n + m + 2 < n + m) := by omega
  have g3 : ¬ (n + m + 3 < n + m) := by omega
  have g4 : ¬ (n + m + 4 < n + m) := by omega
  simp only [List.append_assoc, List.cons_append, List.nil_append, gd, hx, f1, f2, f4, f5,
    g0, g1, g2, g3, g4, ite_true, ite_false, Nat.sub_self, Nat.add_sub_cancel_left,
    List.getD_cons_zero, List.getD_cons_succ, l0, l1, l2, r0, r1, r2, GateOp.eval, List.all_cons,
    List.any_cons, List.all_nil, List.any_nil, Bool.and_true, Bool.or_false]
  simp only [id]
  exact diag3 _ _

theorem CB_mono (n m : Nat) : Monotone2 (CB n m) := by
  intro g hg
  simp only [CB, gs5, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem fan_of_mono (C : Circuit) (h : Monotone2 C) : FanInTwo C := by
  intro g hg
  have ops : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (h g hg).1
  refine ⟨?_, (h g hg).2⟩
  rcases ops with e | e <;> simp [e]

theorem CB_size (n m : Nat) : (CB n m).size = 5 := by
  simp [CB, gs5, Circuit.size]

def addNot (C : Circuit) (N : Nat) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.not, [C.output]⟩], N + C.size⟩

theorem addNot_eval (C : Circuit) (N : Nat) (x : List Bool) (h : x.length = N) :
    (addNot C N).eval x = !(C.eval x) := by
  unfold addNot Circuit.eval
  dsimp only
  rw [wires_snoc C.gates _ _ C.output x]
  have hl := wires_len C x
  rw [PEqualNP.Outside.L_meta_17187.Transfer.getD_snoc_len _ _ _ _ (by
    change (C.wires x).length = _; omega)]
  simp [GateOp.eval]

theorem addNot_fan (C : Circuit) (N : Nat) (h : FanInTwo C) : FanInTwo (addNot C N) := by
  intro g hg
  simp only [addNot, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with hg | rfl
  · exact h g hg
  · simp

theorem addNot_size (C : Circuit) (N : Nat) : (addNot C N).size = C.size + 1 := by
  simp [addNot, Circuit.size]

theorem addNot_notCount (n m N : Nat) : PEqualNP.NotBracket.notCount (addNot (CB n m) N) ≤ 1 := by
  simp [addNot, CB, gs5, PEqualNP.NotBracket.notCount]

theorem repMono {n m : Nat} (A : Fin n → Fin m → Bool) (s t : Nat) (h : RepSizeAtMost A s)
    (hst : s ≤ t) : RepSizeAtMost A t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hst, h3⟩

theorem fanA_lower (n m : Nat) (hn : 3 ≤ n) (hm : 3 ≤ m) (C : Circuit) (hC : FanInTwo C)
    (hR : Represents (fun (i : Fin n) (j : Fin m) =>
      (64478 : Nat).testBit (4 * min i.val 3 + min j.val 3)) C) : 6 ≤ C.size := by
  obtain ⟨k, hk⟩ : ∃ k, n + m = k + 1 := ⟨n + m - 1, by omega⟩
  have key : ∀ (K : Nat), n + m = K →
      HasCircuitSize K (fun x => C.eval (List.ofFn x)) C.size :=
    fun K _ => ⟨C, hC, le_rfl, fun x => rfl⟩
  have gen : ∀ (K : Nat), n + m = K → ∃ a b : Fin 3 → Fin K,
      PEqualNP.Outside.L_meta_17187.Transfer.Rep 3
        (fun x : Fin K → Bool => C.eval (List.ofFn x)) a b := by
    intro K hK
    subst hK
    refine ⟨fun u => Fin.castAdd m (Fin.castLE hn u), fun v => Fin.natAdd n (Fin.castLE hm v),
      fun u v => ?_, fun u v h => ?_⟩
    · have one : List.ofFn (PEqualNP.Outside.L_meta_17187.Transfer.ind
          (Fin.castAdd m (Fin.castLE hn u)) (Fin.natAdd n (Fin.castLE hm v))) =
          oneEach (Fin.castLE hn u) (Fin.castLE hm v) := by
        unfold oneEach
        rw [List.ofFn_add]
        congr 1
        · congr 1
          funext i
          have := i.isLt
          have := u.isLt
          have := v.isLt
          simp [PEqualNP.Outside.L_meta_17187.Transfer.ind, Fin.ext_iff]
          omega
        · congr 1
          funext i
          have := i.isLt
          have := u.isLt
          have := v.isLt
          simp [PEqualNP.Outside.L_meta_17187.Transfer.ind, Fin.ext_iff]
          omega
      show C.eval (List.ofFn _) = _
      rw [one, hR]
      show (64478 : Nat).testBit (4 * min (Fin.castLE hn u).val 3 + min (Fin.castLE hm v).val 3)
        = decide (u ≠ v)
      simp only [Fin.val_castLE]
      have tab : ∀ a b : Fin 3,
          (64478 : Nat).testBit (4 * min a.val 3 + min b.val 3) = decide (a ≠ b) := by decide
      exact tab u v
    · have h1 := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_castLE] at h1
      have := u.isLt
      omega
  obtain ⟨a, b, hab⟩ := gen (k + 1) hk
  have := PEqualNP.Outside.L_meta_17187.Transfer.bound_all k 3 (le_refl 3) _ a b hab C.size
    (key (k + 1) hk)
  omega

theorem fanB_lower (n m : Nat) (hn : 3 ≤ n) (hm : 3 ≤ m) (C : Circuit) (hC : FanInTwo C)
    (hR : Represents (fun (i : Fin n) (j : Fin m) =>
      !((64478 : Nat).testBit (4 * min i.val 3 + min j.val 3))) C) : 5 ≤ C.size := by
  have h := fanA_lower n m hn hm (addNot C (n + m)) (addNot_fan C _ hC) (by
    intro u v
    rw [addNot_eval _ _ _ (oe_len u v), hR u v]
    simp)
  rw [addNot_size] at h
  omega

theorem B_rep (n m : Nat) (hn : 3 ≤ n) (hm : 3 ≤ m) :
    Represents (fun (i : Fin n) (j : Fin m) =>
      !((64478 : Nat).testBit (4 * min i.val 3 + min j.val 3))) (CB n m) := by
  intro u v
  rw [CB_eval n m hn hm]
  dsimp only
  rw [tab_spec]
  simp

theorem A_rep (n m : Nat) (hn : 3 ≤ n) (hm : 3 ≤ m) :
    Represents (fun (i : Fin n) (j : Fin m) =>
      (64478 : Nat).testBit (4 * min i.val 3 + min j.val 3)) (addNot (CB n m) (n + m)) := by
  intro u v
  rw [addNot_eval _ _ _ (oe_len u v), CB_eval n m hn hm]
  dsimp only
  rw [tab_spec]

end PEqualNP.Outside.L_meta_33675

open PEqualNP.Outside.L_meta_33675 in
theorem PEqualNP.Outside.L_meta_33675 : ∀ (n m : Nat), 3 ≤ n → 3 ≤ m →
  let A := fun (i : Fin n) (j : Fin m) =>
    (64478 : Nat).testBit (4 * min i.val 3 + min j.val 3)
  let B := fun (i : Fin n) (j : Fin m) => !(A i j)
  ∀ (s k : Nat), 1 ≤ k →
    (PEqualNP.Represents.RepSizeAtMost A s ↔ n + m + 1 ≤ s) ∧
    ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ s ∧ PEqualNP.NotBracket.notCount C ≤ k ∧ PEqualNP.Represents.Represents A C)
      ↔ 6 ≤ s) ∧
    ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ s ∧ PEqualNP.Represents.Represents A C) ↔ 6 ≤ s) ∧
    (PEqualNP.Represents.RepSizeAtMost B s ↔ 5 ≤ s) ∧
    ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ s ∧ PEqualNP.Represents.Represents B C) ↔ 5 ≤ s) := by
  intro n m hn hm
  dsimp only
  intro s k hk
  have h30 := PEqualNP.Outside.L_meta_30581 n m hn hm
  dsimp only at h30
  obtain ⟨up, down⟩ := h30
  have fA : PEqualNP.MetaComplexity.FanInTwo (addNot (CB n m) (n + m)) := addNot_fan _ _ (fan_of_mono _ (CB_mono n m))
  have sA : (addNot (CB n m) (n + m)).size = 6 := by rw [addNot_size, CB_size]
  refine ⟨⟨fun h => ?_, fun h => repMono _ _ _ up h⟩, ⟨?_, fun h => ?_⟩, ⟨?_, fun h => ?_⟩,
    ⟨?_, fun h => ?_⟩, ⟨?_, fun h => ?_⟩⟩
  · by_contra hs
    exact down (repMono _ _ _ h (by omega))
  · rintro ⟨C, hC, hs, -, hR⟩
    have := fanA_lower n m hn hm C hC hR
    omega
  · exact ⟨addNot (CB n m) (n + m), fA, by omega, le_trans (addNot_notCount n m _) hk,
      A_rep n m hn hm⟩
  · rintro ⟨C, hC, hs, hR⟩
    have := fanA_lower n m hn hm C hC hR
    omega
  · exact ⟨addNot (CB n m) (n + m), fA, by omega, A_rep n m hn hm⟩
  · rintro ⟨C, hC, hs, hR⟩
    have := fanB_lower n m hn hm C (fan_of_mono C hC) hR
    omega
  · exact ⟨CB n m, CB_mono n m, by rw [CB_size]; omega, B_rep n m hn hm⟩
  · rintro ⟨C, hC, hs, hR⟩
    have := fanB_lower n m hn hm C hC hR
    omega
  · exact ⟨CB n m, fan_of_mono _ (CB_mono n m), by rw [CB_size]; omega, B_rep n m hn hm⟩

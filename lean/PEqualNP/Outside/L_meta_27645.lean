import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27645_aux
open PEqualNP.CircuitLowerBounds
private def push (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private def slots (g : Gate) := match g.op with | .not => 1 :: g.inputs | _ => g.inputs
private def R (k : Nat) (a b : Bool) : Prop := if k = 1 then (a = true → b = true) else a = b
private def start (x : Fin 9 → Bool) := push (push (List.ofFn x) ⟨.or,[0,4]⟩) ⟨.not,[1]⟩
private def target (x : Fin 9 → Bool) := ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
private def vec (k : Fin 9) (v : Bool) (i : Fin 9) : Bool :=
  let p : List Nat := if k.val ∈ [0,4,8] then [0,4,8] else if k.val ∈ [1,3] then [1,3,8] else if k.val ∈ [2,6] then [2,4,6] else [0,5,7]
  decide (i.val ∈ p) && (decide (i ≠ k) || v)
private theorem vectors : ∀ k : Fin 9, ¬ R k (target (vec k true)) (target (vec k false)) ∧
    ∀ i : Fin 11, i.val ≠ k.val → R k ((start (vec k true)).getD i false) ((start (vec k false)).getD i false) := by unfold R; decide
private abbrev Good (g : Gate) := (g.op = .not ∧ ∃ a, g.inputs = [a]) ∨ ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b])
private theorem newBit {k : Nat} {g : Gate} {w z : List Bool} (hg : Good g) (hm : k ∉ slots g)
    (hr : ∀ i, i ≠ k → R k (w.getD i false) (z.getD i false)) :
    R k (g.op.eval (g.inputs.map fun i => w.getD i false)) (g.op.eval (g.inputs.map fun i => z.getD i false)) := by
  rcases g with ⟨op,ins⟩
  rcases hg with ⟨rfl,a,rfl⟩ | ⟨ops,a,b,rfl⟩
  · simp [slots] at hm
    have h := hr a (Ne.symm hm.2)
    simpa [R,hm.1,GateOp.eval] using congrArg Bool.not (show w.getD a false = z.getD a false from by simpa [R,hm.1] using h)
  · rcases ops with rfl | rfl <;> simp [slots] at hm <;>
      have ha := hr a (Ne.symm hm.1) <;> have hb := hr b (Ne.symm hm.2) <;>
      by_cases hk : k = 1 <;> simp_all [R, GateOp.eval] <;> tauto
private theorem preserve {k : Nat} {gs : List Gate} {w z : List Bool} (good : ∀ g ∈ gs, Good g)
    (absent : k ∉ gs.flatMap slots) (len : w.length = z.length)
    (rel : ∀ i, i ≠ k → R k (w.getD i false) (z.getD i false)) :
    ∀ i, i ≠ k → R k ((gs.foldl push w).getD i false) ((gs.foldl push z).getD i false) := by
  induction gs generalizing w z with
  | nil => exact rel
  | cons g gs ih =>
    simp only [List.flatMap_cons,List.mem_append,not_or] at absent
    apply ih (fun t ht => good t (by simp [ht])) absent.2 (by simp [push,len])
    intro i hi
    by_cases lt : i < w.length
    · rw [push,push,List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ (len ▸ lt)]
      exact rel i hi
    · rw [push,push,List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]
      cases i - z.length with
      | zero => exact newBit (good g (by simp)) absent.1 rel
      | succ n => simp [List.getD_eq_getElem?_getD,R]
end PEqualNP.Outside.L_meta_27645_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_27645_aux

theorem PEqualNP.Outside.L_meta_27645 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1]⟩)) := by
  rintro ⟨⟨gates,out⟩, _, size, correct, hout, normal, _, live, hfirst, hsecond⟩
  cases gates with
  | nil => simp at hfirst
  | cons g tail =>
    simp only [List.head?_cons, Option.some.injEq] at hfirst
    subst g
    cases tail with
    | nil => simp at hsecond
    | cons g gs =>
      simp only [List.tail_cons,List.head?_cons,Option.some.injEq] at hsecond
      subst g
      let orG : Gate := ⟨.or,[0,4]⟩
      let notG : Gate := ⟨.not,[1]⟩
      let allG := orG :: notG :: gs
      change allG.length ≤ 11 at size
      change out + 1 = 9 + allG.length at hout
      have lens : allG.length = gs.length + 2 := by simp [allG]
      have good : ∀ g ∈ gs, Good g := by
        intro g hg
        have hm : g ∈ allG := by simp [allG,hg]
        obtain ⟨i,hi,he⟩ := List.getElem_of_mem hm
        have n := normal ⟨i,hi⟩
        change _ at n
        change allG[i] = g at he
        subst g
        rcases n with ⟨op,a,_,inp⟩ | ⟨ops,a,b,_,_,inp⟩
        · exact Or.inl ⟨op,a,inp⟩
        · exact Or.inr ⟨ops,a,b,inp⟩
      have cap : (gs.flatMap slots).length = 2 * gs.length := by
        suffices ∀ l : List Gate, (∀ g ∈ l, Good g) → (l.flatMap slots).length = 2 * l.length from this gs good
        intro l
        induction l with
        | nil => simp
        | cons g l ih =>
          intro hg
          have hh := hg g (by simp)
          have ll := ih (fun a ha => hg a (by simp [ha]))
          have two : (slots g).length = 2 := by
            rcases hh with ⟨op,a,inp⟩ | ⟨ops,a,b,inp⟩
            · simp [slots,op,inp]
            · rcases ops with op | op <;> simp [slots,op,inp]
          simp only [List.flatMap_cons,List.length_append,two,ll,List.length_cons]; omega
      have cover : Finset.range (9 + allG.length - 1) ⊆ (gs.flatMap slots).toFinset := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [List.mem_toFinset]
        by_cases small : k < 9
        · by_contra absent
          let j : Fin 9 := ⟨k,small⟩
          obtain ⟨bad,h⟩ := vectors j
          have len (v : Bool) : (start (vec j v)).length = 11 := by simp [start,push]
          have rel : ∀ i, i ≠ k → R k ((start (vec j true)).getD i false) ((start (vec j false)).getD i false) := by
            intro i hi
            by_cases lt : i < 11
            · exact h ⟨i,lt⟩ hi
            · rw [List.getD_eq_default _ _ (by rw [len]; omega),List.getD_eq_default _ _ (by rw [len]; omega)]; simp [R]
          have e := preserve good absent ((len true).trans (len false).symm) rel out (by omega)
          have cv (v : Bool) : (gs.foldl push (start (vec j v))).getD out false = target (vec j v) := correct _
          rw [cv,cv] at e
          exact bad e
        · let j : Fin allG.length := ⟨k-9,by omega⟩
          obtain ⟨t,ht,mem⟩ := live j (by dsimp [j]; omega)
          change 9 + j.val ∈ allG[t.val].inputs at mem
          have eqk : 9 + j.val = k := by dsimp [j]; omega
          rw [eqk] at mem
          have ht2 : 2 ≤ t.val := by
            by_contra! hn
            obtain ht0 | ht1 : t.val = 0 ∨ t.val = 1 := by omega
            · omega
            · simp [allG,ht1,notG] at mem; omega
          obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le ht2
          have ul : u < gs.length := by have hlt : t.val < allG.length := t.isLt; omega
          have em : k ∈ gs[u].inputs := by simpa [allG,hu,Nat.add_comm 2 u] using mem
          apply List.mem_flatMap.mpr
          exact ⟨gs[u],List.getElem_mem ..,by simp [slots]; split <;> simp_all⟩
      have bound := (Finset.card_le_card cover).trans (List.toFinset_card_le _)
      rw [Finset.card_range,cap] at bound
      omega

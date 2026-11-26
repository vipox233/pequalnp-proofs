import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20825

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def matrix (u v : Fin 5) : Bool := (17043521 : ℕ).testBit (5 * u.val + v.val)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wiresLength (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append,step,ih,Nat.add_assoc]

theorem wireSnoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases lt_trichotomy i w.length with h|rfl|h
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h,h.ne]
  · simp [List.getD_eq_getElem?_getD]
  · have h1 : w.length ≤ i := by omega
    have h2 : (w ++ [b]).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,List.getElem?_eq_none h2,h.ne']

theorem smallSupport (n : ℕ) (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) (S : Finset ℕ) :
    ∃ T : Finset ℕ, T.card ≤ S.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ T, x.getD i false = y.getD i false) →
      ∀ i ∈ S, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,by simp,fun _ _ _ _ same => same⟩
  | append_singleton gs g ih =>
    have prior : ∀ a ∈ gs, a.inputs.length ≤ 2 :=
      fun a ha => arity a (List.mem_append_left _ ha)
    have fan : g.inputs.length ≤ 2 := arity g (List.mem_append_right _ (List.mem_singleton_self _))
    let w := n+gs.length
    let U := if w ∈ S then S.erase w ∪ g.inputs.toFinset else S
    have small : U.card ≤ S.card+1 := by
      dsimp only [U]
      split_ifs with used
      · have h1 := Finset.card_union_le (S.erase w) g.inputs.toFinset
        have h2 := Finset.card_erase_add_one used
        have h3 := List.toFinset_card_le (l := g.inputs)
        omega
      · omega
    obtain ⟨T,bound,works⟩ := ih prior U
    refine ⟨T,by simp only [List.length_append,List.length_singleton]; omega,?_⟩
    intro x y hx hy equal i iq
    have X := (wiresLength gs x).trans (by rw [hx])
    have Y := (wiresLength gs y).trans (by rw [hy])
    change (gs.foldl step x).length = w at X
    change (gs.foldl step y).length = w at Y
    have old := works x y hx hy equal
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,step,wireSnoc,X,Y]
    by_cases atNew : i = w
    · have used : w ∈ S := atNew ▸ iq
      rw [ite_eq_left atNew,ite_eq_left atNew]
      congr 1
      apply List.map_congr_left
      intro j jRead
      apply old
      dsimp only [U]
      rw [ite_eq_left used]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr jRead)
    · rw [ite_eq_right atNew,ite_eq_right atNew]
      apply old
      dsimp only [U]
      split_ifs
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨atNew,iq⟩)
      · exact iq

theorem stepMono (g : Gate) (shape : g.op = .and ∨ g.op = .or) (x y : List Bool)
    (len : x.length = y.length)
    (le : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (step x g).getD i false = true → (step y g).getD i false = true := by
  intro i
  simp only [step,wireSnoc,len]
  split_ifs
  · rcases shape with isAnd|isOr
    · simp only [isAnd,GateOp.eval,List.all_eq_true,List.mem_map,id_eq]
      intro on b h
      obtain ⟨w,mem,rfl⟩ := h
      exact le w (on _ ⟨w,mem,rfl⟩)
    · simp only [isOr,GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
      rintro ⟨_,⟨w,mem,rfl⟩,on⟩
      exact ⟨_,⟨w,mem,rfl⟩,le w on⟩
  · exact le i

theorem foldMono (gs : List Gate)
    (shape : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (x y : List Bool) (len : x.length = y.length)
    (le : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl step x).getD i false = true → (gs.foldl step y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact le
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun a ha => shape a (List.mem_cons_of_mem _ ha))
      (step x g) (step y g) (by simp [step,len])
      (stepMono g (shape g (List.mem_cons_self)) x y len le)

def singleton (i : Fin 10) : List Bool := List.ofFn (fun k : Fin 10 => decide (k=i))

set_option maxHeartbeats 2000000 in
theorem essential :
    ∀ w : Fin 10, ∃ u v u' v' : Fin 5, ∃ s : Fin 10,
      matrix u v = true ∧ matrix u' v' = false ∧
      (∀ i : Fin 10, i ≠ w → (oneEach u v).getD i.val false = (singleton s).getD i.val false) ∧
      (∀ i : Fin 10, (singleton s).getD i.val false = true → (oneEach u' v').getD i.val false = true) := by
  intro w
  fin_cases w
  · exact ⟨0, 0, 1, 0, 5, by decide +kernel⟩
  · exact ⟨1, 1, 2, 1, 6, by decide +kernel⟩
  · exact ⟨2, 2, 3, 2, 7, by decide +kernel⟩
  · exact ⟨3, 3, 4, 3, 8, by decide +kernel⟩
  · exact ⟨4, 4, 0, 4, 9, by decide +kernel⟩
  · exact ⟨0, 0, 0, 1, 0, by decide +kernel⟩
  · exact ⟨1, 1, 1, 2, 1, by decide +kernel⟩
  · exact ⟨2, 2, 2, 3, 2, by decide +kernel⟩
  · exact ⟨3, 3, 3, 4, 3, by decide +kernel⟩
  · exact ⟨4, 4, 4, 0, 4, by decide +kernel⟩

theorem lower : ¬ RepSizeAtMost matrix 8 := by
  rintro ⟨C,shape,budget,rep⟩
  have arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (shape g hg).2
  have op : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using (shape g hg).1
  obtain ⟨T,small,support⟩ := smallSupport 10 C.gates arity {C.output}
  have eachLength (u v : Fin 5) : (oneEach u v).length = 10 := by simp [oneEach]
  have singleLength (s : Fin 10) : (singleton s).length = 10 := by simp [singleton]
  have missing {x : List Bool} {i : ℕ} (len : x.length = 10) (hi : 10 ≤ i) :
      x.getD i false = false := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (len.symm ▸ hi)]
    rfl
  have required (w : Fin 10) : w.val ∈ T := by
    by_contra unused
    obtain ⟨u,v,u',v',s,yes,no,same,monotone⟩ := essential w
    have sameOnT : ∀ i ∈ T, (oneEach u v).getD i false = (singleton s).getD i false := by
      intro i selected
      by_cases hi : i < 10
      · exact same ⟨i,hi⟩ (fun h => unused ((congrArg Fin.val h) ▸ selected))
      · rw [missing (eachLength u v) (by omega),missing (singleLength s) (by omega)]
    have eq : C.eval (oneEach u v) = C.eval (singleton s) :=
      support (oneEach u v) (singleton s) (eachLength u v) (singleLength s) sameOnT
        C.output (Finset.mem_singleton_self _)
    have order : ∀ i, (singleton s).getD i false = true → (oneEach u' v').getD i false = true := by
      intro i h
      by_cases hi : i < 10
      · exact monotone ⟨i,hi⟩ h
      · rw [missing (singleLength s) (by omega)] at h
        cases h
    have on : C.eval (singleton s) = true := eq.symm.trans ((rep u v).trans yes)
    have another : C.eval (oneEach u' v') = true := foldMono C.gates op _ _
      ((singleLength s).trans (eachLength u' v').symm) order C.output on
    exact Bool.false_ne_true (((rep u' v').trans no).symm.trans another)
  have all : Finset.range 10 ⊆ T := fun i hi => required ⟨i,Finset.mem_range.mp hi⟩
  have bound : 10 ≤ T.card := by simpa using Finset.card_le_card all
  change C.gates.length ≤ 8 at budget
  simp only [Finset.card_singleton] at small
  omega

end PEqualNP.Outside.L_meta_20825

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_20825 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (17043521 : ℕ).testBit (5 * u.val + v.val)) 9 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (17043521 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  constructor
  · let C : Circuit := ⟨[
      ⟨.and, [0,5]⟩, ⟨.and, [1,6]⟩, ⟨.and, [2,7]⟩, ⟨.and, [3,8]⟩, ⟨.and, [4,9]⟩,
      ⟨.or, [10,11]⟩, ⟨.or, [15,12]⟩, ⟨.or, [16,13]⟩, ⟨.or, [17,14]⟩], 18⟩
    refine ⟨C, ?_, by decide, ?_⟩
    · simp [C, Monotone2]
    · decide +kernel
  · exact PEqualNP.Outside.L_meta_20825.lower

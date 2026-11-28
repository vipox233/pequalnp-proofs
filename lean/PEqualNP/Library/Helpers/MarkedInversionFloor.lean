import Mathlib
import PEqualNP.Defs.NotBracket
import PEqualNP.Defs.MetaComplexity

namespace PEqualNP.MarkedInversionFloor
open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

private def tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: code gs a
    | _ => code gs a

private def mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

private theorem code_len (gs : List Gate) (w : List Bool) :
    (code gs w).length = (gs.filter mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [code,h,mark,List.filter_cons,ih]

private def ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

private theorem extend_order {x y : List Bool} (w : ordered x y) {a b : Bool}
    (ab : a=true → b=true) : ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length <;> simpa using ab <;> simp

private theorem output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : ordered x y) (same : code gs x=code gs y) :
    ordered (run gs x) (run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change ordered (run gs (tick x g)) (run gs (tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (extend_order w ?_) (by simpa only [code,tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [code,h,List.cons.injEq] at same
      apply ih rest (extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

private theorem input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp

theorem lower {n : Nat} (G H : Finset (Fin n × Fin n)) (sub : H⊆G)
    (S : Finset (Fin n))
    (active : S ⊆ H.image Prod.fst ∪ H.image Prod.snd)
    (indep : ∀ e∈G, ¬(e.1∈S ∧ e.2∈S))
    (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (tap : ↥H → Fin (n+2+C.size))
    (good : ∀ x : Fin n → Bool, (∀ e∈G, x e.1=true ∨ x e.2=true) →
      ∀ e, (C.wires (List.ofFn x ++ [false,true])).getD (tap e).val false = xor (x e.val.1) (x e.val.2)) :
    S.card < 2 ^ PEqualNP.NotBracket.notCount C := by
  classical
  let rank : ↥S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let x (t : Fin (S.card+1)) (i : Fin n) : Bool :=
    if hi : i∈S then decide ((rank ⟨i,hi⟩).val<t.val) else true
  have outside (t) (i) (hi : i∉S) : x t i=true := by simp [x,hi]
  have cover (t) (e) (he : e∈G) : x t e.1=true ∨ x t e.2=true := by
    by_cases h : e.1∈S
    · exact Or.inr (outside _ _ (fun h₂ => indep e he ⟨h,h₂⟩))
    · exact Or.inl (outside _ _ h)
  let inputs t := List.ofFn (x t) ++ [false,true]
  let len := (C.gates.filter mark).length
  let sig (t : Fin (S.card+1)) : Fin len → Bool := fun j =>
    (code C.gates (inputs t))[j.val]'(by rw [code_len]; exact j.isLt)
  have different (t u : Fin (S.card+1)) (lt : t<u) : sig t ≠ sig u := by
    intro equal
    have same : code C.gates (inputs t) = code C.gates (inputs u) := by
      apply List.ext_getElem (by simp [code_len])
      intro i h₁ h₂
      exact congrFun equal ⟨i,by simpa [len,code_len] using h₁⟩
    have growth : ordered (inputs t) (inputs u) := by
      apply input_order
      intro i
      by_cases h : i∈S
      · simp [x,h]; omega
      · simp [x,h]
    have ops (g) (hg : g∈C.gates) : g.op=.and ∨ g.op=.or ∨ g.op=.not := (fan g hg).1
    have monotone := output_order ops growth same
    have tlt : t.val<S.card := by have := u.isLt; omega
    let j : Fin S.card := ⟨t.val,tlt⟩
    let v := rank.symm j
    have start : x t v.val=false := by simp [x,v.property,v,j]
    have finish : x u v.val=true := by simp [x,v.property,v,j,lt]
    have marked := Finset.mem_union.mp (active v.property)
    have impossible (e : ↥H) (a : xor (x t e.val.1) (x t e.val.2)=true)
        (b : xor (x u e.val.1) (x u e.val.2)=false) : False := by
      have a' := (good (x t) (cover t) e).trans a
      have b' := (good (x u) (cover u) e).trans b
      have bad := monotone.2 (tap e).val a'
      exact Bool.noConfusion (bad.symm.trans b')
    rcases marked with h|h
    · obtain ⟨e,he,ev⟩ := Finset.mem_image.mp h
      have eo : e.2∉S := fun h => indep _ (sub he) ⟨ev ▸ v.property,h⟩
      exact impossible ⟨e,he⟩ (by simp [ev,start,outside t _ eo]) (by simp [ev,finish,outside u _ eo])
    · obtain ⟨e,he,ev⟩ := Finset.mem_image.mp h
      have eo : e.1∉S := fun h => indep _ (sub he) ⟨h,ev ▸ v.property⟩
      exact impossible ⟨e,he⟩ (by simp [ev,start,outside t _ eo]) (by simp [ev,finish,outside u _ eo])
  have inj : Function.Injective sig := by
    intro t u eq
    rcases lt_trichotomy t u with lt|same|gt
    · exact (different t u lt eq).elim
    · exact same
    · exact (different u t gt eq.symm).elim
  have card := Fintype.card_le_of_injective _ inj
  have lenEq : len = PEqualNP.NotBracket.notCount C := by
    unfold len PEqualNP.NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    cases h : g.op <;> simp [mark,h]
  simpa [lenEq] using card

end PEqualNP.MarkedInversionFloor

import PEqualNP.Library.Helpers.WireFallBalance

namespace PEqualNP.InverterPlacementControl

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

def inputs (t : Fin 5) := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]

def masks : Fin 3 → Nat := ![4,6,25]

def target (j : Fin 3) (t : Fin 5) := (masks j).testBit t.val

def observed (C : Circuit) (i : Nat) (t : Fin 5) := (C.wires (inputs t)).getD i false

private theorem primary (C : Circuit) (i : Nat) (h : i < 6) (t : Fin 5) :
    observed C i t=(inputs t).getD i false := by
  exact CoverCircuit.getD_run _ _ _ (by simpa [inputs] using h)

private def op3 : Fin 3 → GateOp := ![.and,.or,.not]

private theorem missesRaw (i : Fin 6) (j : Fin 3) :
    ¬ ∀ t : Fin 5, (inputs t).getD i.val false=target j t := by decide +revert

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
private theorem missesFirst (op : Fin 3) (a b : Option (Fin 6)) (j : Fin 3) :
    ¬ ∀ t : Fin 5, (op3 op).eval ((a.toList++b.toList).map (fun i => (inputs t).getD i.val false))=target j t := by
  decide +revert

private theorem first (C : Circuit) (fan : FanInTwo C) (back : ReadsBack 6 C)
    (existsGate : 0 < C.size) (j : Fin 3) : ¬ ∀ t, observed C 6 t=target j t := by
  intro fit
  let g := gateAt C 0
  have gm : g ∈ C.gates := by
    have eq : g=C.gates[0] := by simp [g, gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem existsGate]
    exact eq ▸ List.getElem_mem ..
  have ⟨op,arity⟩ := fan g gm
  have opidx : ∃ r : Fin 3, op3 r=g.op := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    rcases op with h | h | h
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
  obtain ⟨r,hr⟩ := opidx
  have args : ∀ i ∈ g.inputs, i<6 := fun i hi => back 0 existsGate i hi
  have packed : ∃ a b : Option (Fin 6), (a.toList++b.toList).map Fin.val=g.inputs := by
    cases eq : g.inputs with
    | nil => exact ⟨none,none,by simp⟩
    | cons i l =>
      have hi := args i (by simp [eq])
      cases l with
      | nil => exact ⟨some ⟨i,hi⟩,none,by simp⟩
      | cons k tail =>
        have hk := args k (by simp [eq])
        have ht : tail=[] := by simpa [eq] using arity
        exact ⟨some ⟨i,hi⟩,some ⟨k,hk⟩,by simp [ht]⟩
  obtain ⟨a,b,ab⟩ := packed
  apply missesFirst r a b j
  intro t
  have eq := WireFallBalance.wire_gate C 6 back (inputs t) (by simp [inputs]) 0 existsGate
  have ores : g.inputs.map (fun i => (C.wires (inputs t)).getD i false)=g.inputs.map (fun i => (inputs t).getD i false) :=
    List.map_congr_left (fun i hi => primary C i (args i hi) t)
  change observed C 6 t=g.op.eval _ at eq
  rw [ores] at eq
  rw [←ab,List.map_map,←hr] at eq
  exact eq.symm.trans (fit t)

theorem lower (C : Circuit) (fan : FanInTwo C) (back : ReadsBack 6 C)
    (tap : Fin 3 → Fin (6+C.size)) (fit : ∀ j t, observed C (tap j).val t=target j t) : 4 ≤ C.size := by
  have later (j : Fin 3) : 7≤(tap j).val := by
    by_contra! small
    by_cases hi : (tap j).val<6
    · apply missesRaw ⟨_,hi⟩ j
      intro t
      exact (primary C _ hi t).symm.trans (fit j t)
    · have eq : (tap j).val=6 := by omega
      have size := (tap j).isLt
      apply first C fan back (by omega) j
      simpa only [eq] using fit j
  have distinguish (i j : Fin 3) : (∀ t, target i t=target j t) → i=j := by decide +revert
  have inj : Function.Injective (fun j => (tap j).val) := by
    intro i j h
    exact distinguish i j (fun t => (fit i t).symm.trans ((congrArg (fun k => observed C k t) h).trans (fit j t)))
  have diff (i j : Fin 3) (h : i≠j) : (tap i).val≠(tap j).val := fun eq => h (inj eq)
  have := diff 0 1 (by decide)
  have := diff 0 2 (by decide)
  have := diff 1 2 (by decide)
  have := later 0
  have := later 1
  have := later 2
  have := (tap 0).isLt
  have := (tap 1).isLt
  have := (tap 2).isLt
  omega

private def witness : Circuit := ⟨[⟨.not,[2]⟩,⟨.and,[0,6]⟩,⟨.not,[7]⟩,⟨.and,[1,6]⟩],9⟩

theorem upper : ∃ (C : Circuit) (tap : Fin 3 → Fin (6+C.size)), FanInTwo C ∧ ReadsBack 6 C ∧
    NotBracket.notCount C=2 ∧ C.size=4 ∧ ∀ j t, observed C (tap j).val t=target j t := by
  refine ⟨witness,![9,7,8],?_,?_,?_,rfl,?_⟩
  · simp [FanInTwo,witness]
  · intro j hj
    change j<4 at hj
    interval_cases j <;> simp [gateAt,witness]
  · simp [NotBracket.notCount,witness]
  · decide

def five : Fin 5 → Nat := ![4,6,25,1,7]

private def fixed : Circuit := ⟨[⟨.not,[0]⟩,⟨.not,[2]⟩,⟨.and,[1,7]⟩,⟨.and,[0,7]⟩,⟨.or,[6,2]⟩],10⟩

theorem fixedLower (C : Circuit) (tap : Fin 5 → Fin (6+C.size))
    (fit : ∀ j t, observed C (tap j).val t=(five j).testBit t.val) : 5 ≤ C.size := by
  have baseMiss (i : Fin 6) (j : Fin 5) : ¬ ∀ t : Fin 5, (inputs t).getD i.val false=(five j).testBit t.val := by
    decide +revert
  have bound (j : Fin 5) : 6≤(tap j).val := by
    by_contra! small
    exact baseMiss ⟨_,small⟩ j (fun t => (primary C _ small t).symm.trans (fit j t))
  let index (j : Fin 5) : Fin C.size := ⟨(tap j).val-6,by have := (tap j).isLt; have := bound j; omega⟩
  have distinguish (i j : Fin 5) : (∀ t : Fin 5, (five i).testBit t.val=(five j).testBit t.val) → i=j := by
    decide +revert
  have inj : Function.Injective index := by
    intro i j eq
    have v := congrArg Fin.val eq
    change (tap i).val-6=(tap j).val-6 at v
    have same : (tap i).val=(tap j).val := by have := bound i; have := bound j; omega
    exact distinguish i j (fun t => (fit i t).symm.trans ((congrArg (fun k => observed C k t) same).trans (fit j t)))
  simpa using Fintype.card_le_of_injective index inj

theorem fixedUpper : ∃ (C : Circuit) (tap : Fin 5 → Fin (6+C.size)), FanInTwo C ∧ ReadsBack 6 C ∧
    NotBracket.notCount C=2 ∧ C.size=5 ∧
    C.gates.take 2=[⟨.not,[0]⟩,⟨.not,[2]⟩] ∧
    ∀ j t, observed C (tap j).val t=(five j).testBit t.val := by
  refine ⟨fixed,![8,9,10,6,7],?_,?_,?_,rfl,rfl,?_⟩
  · simp [FanInTwo,fixed]
  · intro j hj
    change j<5 at hj
    interval_cases j <;> simp [gateAt,fixed]
  · simp [NotBracket.notCount,fixed]
  · decide

end PEqualNP.InverterPlacementControl

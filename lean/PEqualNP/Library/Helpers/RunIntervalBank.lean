import PEqualNP.Library.Helpers.OrderedThresholdBank

namespace PEqualNP.RunIntervalBank

open FiniteGateBank OrderedThresholdBank

variable {m : Nat}

def cuts (k : Nat) (f : Nat → Fin m → Bool) : Finset Nat :=
  (Finset.range (k+1)).filter (fun e => 0 < e ∧ ∃ j, f (e-1) j=true ∧ f e j=false)

def starts (k : Nat) (f : Nat → Fin m → Bool) (j : Fin m) : Finset Nat :=
  (Finset.range (k+1)).filter (fun a => f a j=true ∧ (a=0 ∨ f (a-1) j=false))

private def stop (k : Nat) (f : Nat → Fin m → Bool) (j : Fin m) (a : Nat) : Nat :=
  Nat.find (show ∃ e, e=k+1 ∨ a < e ∧ f e j=false from ⟨k+1,Or.inl rfl⟩)

private theorem stop_spec {k a} {f : Nat → Fin m → Bool} {j : Fin m} :
    stop k f j a=k+1 ∨ a < stop k f j a ∧ f (stop k f j a) j=false := by
  unfold stop
  exact Nat.find_spec (p:=fun e => e=k+1 ∨ a < e ∧ f e j=false) _

private theorem stop_le {k a e} {f : Nat → Fin m → Bool} {j : Fin m}
    (h : e=k+1 ∨ a < e ∧ f e j=false) : stop k f j a ≤ e := Nat.find_min' _ h

private theorem interior {k a u} {f : Nat → Fin m → Bool} {j : Fin m}
    (one : f a j=true) (lo : a ≤ u) (hi : u < stop k f j a) : f u j=true := by
  by_contra! h
  have zero : f u j=false := Bool.eq_false_iff.mpr h
  by_cases eq : a=u
  · simp_all
  · have b := stop_le (k:=k) (Or.inr ⟨show a < u by omega,zero⟩)
    omega

private theorem ends {k a} {f : Nat → Fin m → Bool} {j : Fin m} (ha : a∈starts k f j) :
    stop k f j a=k+1 ∨ stop k f j a ∈ cuts k f := by
  rcases stop_spec (k:=k) (f:=f) (j:=j) (a:=a) with last | ⟨lt,zero⟩
  · exact Or.inl last
  · have upper := stop_le (a:=a) (f:=f) (j:=j) (Or.inl rfl : k+1=k+1 ∨ _)
    by_cases last : stop k f j a=k+1
    · exact Or.inl last
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,j,
        interior (k:=k) (Finset.mem_filter.mp ha).2.1 (by omega) (by omega),zero⟩)

private theorem represent (k : Nat) (f : Nat → Fin m → Bool) (j : Fin m) (u : Nat)
    (ku : u ≤ k) : f u j=true ↔ ∃ a ∈ starts k f j, a ≤ u ∧ u < stop k f j a := by
  constructor
  · intro one
    let P (a : Nat) := a ≤ u ∧ ∀ v, a ≤ v → v ≤ u → f v j=true
    have hp : ∃ a, P a := ⟨u,le_rfl,fun v lo hi => le_antisymm hi lo ▸ one⟩
    let a := Nat.find hp
    have prop : P a := Nat.find_spec hp
    have start : a=0 ∨ f (a-1) j=false := by
      by_cases za : a=0
      · exact Or.inl za
      · right
        apply Bool.eq_false_iff.mpr
        intro yes
        have prev : P (a-1) := by
          refine ⟨by have := prop.1; omega,?_⟩
          intro v lo hi
          by_cases eq : v=a-1
          · simpa [eq] using yes
          · exact prop.2 _ (by omega) hi
        have minimal := Nat.find_min' hp prev
        change a ≤ a-1 at minimal
        omega
    have au := prop.1
    refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),prop.2 _ le_rfl au,start⟩,au,?_⟩
    rcases stop_spec (k:=k) (f:=f) (j:=j) (a:=a) with last | ⟨lt,zero⟩
    · omega
    · by_contra! h
      have o := prop.2 _ lt.le h
      simp_all
  · rintro ⟨a,ha,lo,hi⟩
    exact interior (Finset.mem_filter.mp ha).2.1 lo hi

private def place (s : Finset Nat) (x : Nat) :=
  Finset.univ.sup (fun i : Fin s.card => if s.orderEmbOfFin rfl i ≤ x then i.val+1 else 0)

private theorem place_le (s : Finset Nat) (x : Nat) : place s x ≤ s.card := by
  apply Finset.sup_le
  intro i _
  split <;> have := i.isLt <;> omega

private theorem place_at (s : Finset Nat) (i : Fin s.card) (x : Nat) :
    i.val+1 ≤ place s x ↔ s.orderEmbOfFin rfl i ≤ x := by
  classical
  constructor
  · intro large
    by_contra! bad
    have upper : place s x ≤ i.val := by
      apply Finset.sup_le
      intro j _
      split
      · rename_i yes
        have lt : s.orderEmbOfFin rfl j < s.orderEmbOfFin rfl i := lt_of_le_of_lt yes bad
        have jj : j < i := (s.orderEmbOfFin rfl).lt_iff_lt.mp lt
        omega
      · omega
    omega
  · intro le
    have z := Finset.le_sup (s:=Finset.univ)
      (f:=fun j : Fin s.card => if s.orderEmbOfFin rfl j ≤ x then j.val+1 else 0) (Finset.mem_univ i)
    simpa only [place,if_pos le] using z

private def word (k x : Nat) (i : Fin k) := decide (i.val < x)
private def raw (k : Nat) (x : Fin (k+1)) := List.ofFn (word k x.val) ++ [false,true]

private theorem width (k) (x) : (raw k x).length=k+2 := by simp [raw]

private theorem basic (k : Nat) (v : Nat) :
    (empty (k+2)).has (raw k) (fun x => decide (v ≤ x.val)) := by
  by_cases zv : v=0
  · refine ⟨k+1,by simp [empty],?_⟩
    intro x
    simp [empty,raw,MetaComplexity.CoverCircuit.run,List.getD_eq_getElem?_getD,zv,
      List.getElem?_append_right (by simp : (List.ofFn (word k x.val)).length ≤ k+1)]
  · by_cases fits : v ≤ k
    · let i : Fin k := ⟨v-1,by omega⟩
      refine ⟨i.val,by have := i.isLt; simp [empty]; omega,?_⟩
      intro x
      change (List.ofFn (word k x.val) ++ [false,true]).getD i.val false=_
      rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using i.isLt : i.val < (List.ofFn (word k x.val)).length),word,i,show v-1 < x.val ↔ v ≤ x.val by omega]
    · refine ⟨k,by simp [empty],?_⟩
      intro x
      have no : ¬v ≤ x.val := by have := x.isLt; omega
      simp [raw,empty,MetaComplexity.CoverCircuit.run,List.getD_eq_getElem?_getD,no]


private theorem allOutputs {X J : Type} [DecidableEq J] {w : Nat} (xs : X → List Bool)
    (p : Net w) (js : Finset J) (cost : J → Nat) (f : J → X → Bool)
    (build : ∀ j ∈ js, ∀ u : Net w, (∀ a, p.has xs a → u.has xs a) →
      ∃ v, Grow xs u v (cost j) 0 ∧ v.has xs (f j)) :
    ∃ q, Grow xs p q (js.sum cost) 0 ∧ ∀ j ∈ js, q.has xs (f j) := by
  induction js using Finset.induction_on with
  | empty => exact ⟨p,by simpa using start xs p,by simp⟩
  | @insert j js hj ih =>
    obtain ⟨u,g,old⟩ := ih (fun i hi => build i (Finset.mem_insert_of_mem hi))
    obtain ⟨v,gv,new⟩ := build j (Finset.mem_insert_self ..) u g.1
    refine ⟨v,by simpa [Finset.sum_insert hj,Nat.add_comm] using chain g gv,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | h
    · exact new
    · exact gv.1 _ (old i h)

theorem upper (k b : Nat) (f : Nat → Fin m → Bool) (room : (cuts k f).card < 2^b) :
    ∃ (C : CircuitLowerBounds.Circuit) (tap : Fin m → Fin (k+2+C.size)),
      MetaComplexity.FanInTwo C ∧ MetaComplexity.NestedCover.ReadsBack (k+2) C ∧
      C.output < k+2+C.size ∧ NotBracket.notCount C=b ∧
      C.size ≤ b+4*(cuts k f).card+2*Finset.univ.sum (fun j => (starts k f j).card) ∧
      ∀ (x : Fin (k+1)) j, (C.wires (raw k x)).getD (tap j).val false=f x.val j := by
  classical
  let s := cuts k f
  let r (x : Fin (k+1)) := place s x.val
  let p := empty (k+2)
  have zero : p.has (raw k) (fun _ => false) := by
    convert basic k (k+1) using 2 with x
    simp [show ¬k+1 ≤ x.val from Nat.not_le_of_gt x.isLt]
  have known (i : Nat) (pos : 0 < i) (le : i ≤ s.card) : p.has (raw k) (high r i) := by
    let j : Fin s.card := ⟨i-1,by omega⟩
    convert basic k (s.orderEmbOfFin rfl j) using 2 with x
    have eq : i=j.val+1 := by dsimp [j]; omega
    simp only [high,r]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have hh := place_at s j x.val
    rwa [←eq] at hh
  obtain ⟨q,g,lows⟩ := decode (raw k) (width k) b s.card room r (fun x => place_le s x.val) p zero known
  have ending (j) (a) (ha : a∈starts k f j) : q.has (raw k) (fun x => decide (x.val < stop k f j a)) := by
    rcases ends ha with last | mem
    · convert g.1 _ (basic k 0) using 2 with x
      simp [last,x.isLt]
    · obtain ⟨i,eq⟩ : ∃ i : Fin s.card, s.orderEmbOfFin rfl i=stop k f j a := by
        exact (show stop k f j a∈Set.range (s.orderEmbOfFin rfl) by simpa [s] using mem)
      convert lows (i.val+1) (by omega) (by have := i.isLt; omega) using 2 with x
      apply Bool.eq_iff_iff.mpr
      simp only [low,decide_eq_true_eq]
      have hh := place_at s i x.val
      rw [eq] at hh
      change x.val < stop k f j a ↔ place s x.val < i.val+1
      omega
  obtain ⟨v,gv,out⟩ := allOutputs (raw k) q Finset.univ (fun j => 2*(starts k f j).card)
    (fun j x => f x.val j) (by
      intro j _ u keep
      let l := (starts k f j).toList
      let active (a : Nat) (x : Fin (k+1)) := decide (a ≤ x.val) && decide (x.val < stop k f j a)
      obtain ⟨w,gw,intervals⟩ := batch (raw:=raw k) u l active 1 0 (by
        intro a ha v preserve
        obtain ⟨w,g',h⟩ := binary (width k) v _ _ (preserve _ (keep _ (g.1 _ (basic k a))))
          (preserve _ (keep _ (ending j a (by simpa [l] using ha)))) true
        exact ⟨w,g',by simpa [active] using h⟩)
      obtain ⟨v,gv,h⟩ := anyList (width k) w (gw.1 _ (keep _ (g.1 _ zero))) l active intervals
      refine ⟨v,by simpa [l,two_mul] using chain gw gv,?_⟩
      convert h using 2 with x
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true,active,Bool.and_eq_true,decide_eq_true_eq,l,Finset.mem_toList]
      exact represent _ _ _ _ (by have := x.isLt; omega))
  let C : CircuitLowerBounds.Circuit := ⟨v.gates,0⟩
  have tap (j : Fin m) := out j (Finset.mem_univ _)
  let ts (j : Fin m) : Fin (k+2+C.size) := ⟨(tap j).choose,(tap j).choose_spec.1⟩
  have total := chain g gv
  refine ⟨C,ts,v.fan,v.readsBack,by simp [C],?_,?_,fun x j => (tap j).choose_spec.2 x⟩
  · change v.cost=b
    simpa [p,empty,Net.cost,NotBracket.notCount] using total.2.2
  · change v.gates.length ≤ _
    have h := total.2.1
    simpa [p,empty,s,Finset.mul_sum,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

end PEqualNP.RunIntervalBank

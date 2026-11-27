import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def gates69 (C : Circuit) := Finset.range C.size
def reads69 (C : Circuit) (w : Nat) := readsIn C (gates69 C) w
noncomputable def neg69 (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>(gateAt C k).op=.not)
noncomputable def special (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact ((Finset.range (N+C.size)).filter (fun w=>2≤reads69 C w)) ∪
    (neg69 C).image (fun k=>N+k)
noncomputable def ordinary (N : Nat) (C : Circuit) : Finset Nat := by
  classical exact (gates69 C).filter (fun k=>N+k∉special N C)
noncomputable def exits69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈gates69 C \ ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∉special N C))
noncomputable def entries69 (N : Nat) (C : Circuit) : Nat := by
  classical exact ∑k∈ordinary N C,(gateAt C k).inputs.countP (fun w=>decide (w∈special N C))
def once69 (N : Nat) (C : Circuit) := (Finset.range N).filter (fun w=>reads69 C w=1)
def shapes69 (C : Circuit) : Prop := ∀g∈C.gates,
  ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)

def tree69 (N : Nat) (C : Circuit) (S E : Finset Nat) : Prop := ∃ region : Finset Nat, ∃ root : Nat,
  let wires := S ∪ region.image (fun k=>N+k)
  let localReads := readsIn C region
  region ⊆ ordinary N C ∧ root∈wires ∧ localReads root=0 ∧
  (∀b∈E,b∉wires ∧ b<root ∧ localReads b=1) ∧
  (∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧ ∀w∈(gateAt C j).inputs, w∈wires ∨ w∈E) ∧
  (∀w∈wires,w≠root → localReads w=1 ∧ reads69 C w=1 ∧ C.output≠w)

theorem ordinary_reads69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    reads69 C (N+k)≤1 := by
  classical
  obtain ⟨hk,hn⟩:=Finset.mem_filter.mp h
  have lt : k<C.size := Finset.mem_range.mp hk
  by_contra! many
  exact hn (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),many⟩))

theorem ordinary_index69 {N : Nat} {C : Circuit} {k : Nat} (h : k∈ordinary N C) :
    k<C.size := Finset.mem_range.mp (Finset.mem_filter.mp h).1

end PEqualNP.Outside.L_meta_25569_aux

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def color69 (N : Nat) (C : Circuit) (w : Nat) : Bool :=
  if w∈special N C then true else if w<N then false else
    (gateAt C (w-N)).inputs.any (fun v => if hv : v<w then color69 N C v else false)
termination_by w

noncomputable def split69 (N : Nat) (C : Circuit) :=
  (ordinary N C).filter (fun j=>2≤((gateAt C j).inputs.filter (color69 N C)).length)

noncomputable def keep69 (N : Nat) (C : Circuit) := ordinary N C \ split69 N C

theorem color_special {N w : Nat} {C : Circuit} (h : w∈special N C) : color69 N C w=true := by
  rw [color69,ite_eq_left h]

theorem color_raw {N w : Nat} {C : Circuit} (hw : w<N) (h : w∉special N C) :
    color69 N C w=false := by rw [color69,ite_eq_right h,ite_eq_left hw]

theorem color_ordinary_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈ordinary N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true := by
  have ns := (Finset.mem_filter.mp hj).2
  rw [color69,ite_eq_right ns,ite_eq_right (by omega : ¬N+j<N),Nat.add_sub_cancel_left,List.any_eq_true]
  apply exists_congr
  intro w
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨h,by simpa [back j (ordinary_index69 hj) w h] using hc⟩

theorem color_keep_iff {N j : Nat} {C : Circuit} (back : ReadsBack N C)
    (hj : j∈keep69 N C) : color69 N C (N+j)=true ↔
      ∃ w∈(gateAt C j).inputs,color69 N C w=true :=
  color_ordinary_iff back (Finset.mem_sdiff.mp hj).1

theorem marked_keep_slots {N j : Nat} {C : Circuit} (hj : j∈keep69 N C) :
    ((gateAt C j).inputs.filter (color69 N C)).length≤1 := by
  obtain ⟨ord,no⟩ := Finset.mem_sdiff.mp hj
  by_contra! two
  exact no (Finset.mem_filter.mpr ⟨ord,two⟩)

theorem color_split_all {N j : Nat} {C : Circuit} (sh : shapes69 C) (hj : j∈split69 N C) :
    ∀ w∈(gateAt C j).inputs,color69 N C w=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  have jlt : j<C.gates.length := ordinary_index69 ord
  have mem : gateAt C j∈C.gates := by simp [gateAt,jlt]
  have len : (gateAt C j).inputs.length≤2 := by rcases sh _ mem with h|h <;> omega
  apply List.length_filter_eq_length_iff.mp
  have hl := List.length_filter_le (p:=color69 N C) (l:=(gateAt C j).inputs)
  omega

theorem color_split_self {N j : Nat} {C : Circuit} (back : ReadsBack N C) (hj : j∈split69 N C) :
    color69 N C (N+j)=true := by
  obtain ⟨ord,two⟩ := Finset.mem_filter.mp hj
  apply (color_ordinary_iff back ord).2
  rw [←List.countP_pos_iff,List.countP_eq_length_filter]
  omega

private lemma maskedCount69 (l : List Nat) (A : Finset Nat) :
    l.countP (fun w=>decide (w∈A)) = ∑w∈A,l.count w := by
  classical
  let f := l.filter (fun w=>decide (w∈A))
  have sub : f.toFinset ⊆ A := by
    intro w hw
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change f.length=_
  calc
    _ = ∑w∈f.toFinset,f.count w := (List.sum_toFinset_count_eq_length f).symm
    _ = ∑w∈A,f.count w := Finset.sum_subset sub (fun _ _ h =>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))
    _ = _ := Finset.sum_congr rfl (fun w hw=>List.count_filter (by simpa using hw))

private lemma countCover69 (l : List Nat) (p s a : Nat→Bool)
    (cover : ∀w∈l,p w=true → s w=true ∨ a w=true) : l.countP p≤l.countP s+l.countP a := by
  induction l with
  | nil => simp
  | cons w ws ih =>
    have tail := ih (fun v hv=>cover v (List.mem_cons_of_mem _ hv))
    have head := cover w List.mem_cons_self
    cases hp : p w <;> cases hs : s w <;> cases ha : a w <;> simp_all [List.countP_cons] <;> omega

private theorem countedSlots69 {N : Nat} {C : Circuit} (P A : Finset Nat)
    (p : Nat→Bool) (pg : P⊆ordinary N C) (ag : A⊆ordinary N C)
    (cover : ∀ j∈P, ∀w∈(gateAt C j).inputs,p w=true →
      w∈special N C ∨ w∈A.image (fun t=>N+t)) :
    (∑j∈P,(gateAt C j).inputs.countP p)≤entries69 N C+A.card := by
  classical
  let I := A.image (fun j=>N+j)
  let specialSlot := fun w=>decide (w∈special N C)
  have each (j : Nat) (hj : j∈P) : (gateAt C j).inputs.countP p ≤
      (gateAt C j).inputs.countP specialSlot + ∑w∈I,(gateAt C j).inputs.count w := by
    rw [←maskedCount69]
    apply countCover69
    intro w hw hp
    exact (cover j hj w hw hp).imp (fun h=>by simpa [specialSlot] using h) (fun h=>by simpa [I] using h)
  have sl : (∑ j∈P,(gateAt C j).inputs.countP specialSlot) ≤ entries69 N C :=
    Finset.sum_le_sum_of_subset_of_nonneg pg (fun _ _ _ => Nat.zero_le _)
  have rest (w : Nat) (hw : w∈I) : (∑ j∈P,(gateAt C j).inputs.count w) ≤ 1 := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    apply le_trans (b:=reads69 C (N+j)) _ (ordinary_reads69 (ag hj))
    unfold reads69 readsIn
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.zero_le _)
    exact fun q hq=>(Finset.mem_filter.mp (pg hq)).1
  have total := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_comm (s:=P) (t:=I)] at total
  have pool := Finset.sum_le_sum rest
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at pool
  have cap : I.card≤A.card := Finset.card_image_le
  omega

theorem splitCard69 {N : Nat} {C : Circuit} (_sh : shapes69 C) (back : ReadsBack N C) :
    (split69 N C).card≤entries69 N C := by
  classical
  let A := (ordinary N C).filter (fun j=>color69 N C (N+j)=true)
  have cover (j : Nat) (hj : j∈ordinary N C) (w : Nat) (hw : w∈(gateAt C j).inputs)
      (hl : color69 N C w=true) : w∈special N C ∨ w∈A.image (fun t=>N+t) := by
    by_cases sp : w∈special N C
    · exact Or.inl sp
    right
    have wire : w<N+j := back j (ordinary_index69 hj) w hw
    have mid : N≤w := by by_contra! z;rw [color_raw z sp] at hl;contradiction
    have eq : N+(w-N)=w := by omega
    have idx : w-N<C.size := by have := ordinary_index69 hj;omega
    have good : w-N∈ordinary N C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,by simpa only [eq] using sp⟩
    exact Finset.mem_image.mpr ⟨w-N,Finset.mem_filter.mpr ⟨good,by simpa only [eq] using hl⟩,eq⟩
  have account := countedSlots69 (ordinary N C) A (color69 N C) (fun _ h=>h)
    (fun _ h=>(Finset.mem_filter.mp h).1) cover
  have pay (j : Nat) (hj : j∈ordinary N C) :
      (if color69 N C (N+j)=true then 1 else 0) +
      (if 2≤((gateAt C j).inputs.filter (color69 N C)).length then 1 else 0) ≤
      (gateAt C j).inputs.countP (color69 N C) := by
    rw [List.countP_eq_length_filter]
    by_cases many : 2≤((gateAt C j).inputs.filter (color69 N C)).length
    · rw [ite_eq_left many];split <;> omega
    rw [ite_eq_right many]
    split
    · next hc =>
      have has := (color_ordinary_iff back hj).1 hc
      have pos := List.countP_pos_iff.mpr has
      rw [List.countP_eq_length_filter] at pos
      omega
    · omega
  have total := Finset.sum_le_sum pay
  rw [Finset.sum_add_distrib,←Finset.card_filter,←Finset.card_filter] at total
  change A.card+(split69 N C).card≤_ at total
  omega

theorem entrySlotsBound69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C) :
    (∑j∈keep69 N C,(gateAt C j).inputs.countP
      (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))) ≤ 2*entries69 N C := by
  classical
  have cap := countedSlots69 (keep69 N C) (split69 N C)
    (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
    (fun _ h=>(Finset.mem_sdiff.mp h).1) (fun _ h=>(Finset.mem_filter.mp h).1) (by
      intro j hj w hw h
      rcases of_decide_eq_true h with s|⟨low,idx⟩
      · exact Or.inl s
      · exact Or.inr (Finset.mem_image.mpr ⟨w-N,idx,by omega⟩))
  have splitBound := splitCard69 sh back
  omega

end PEqualNP.Outside.L_meta_25569_aux

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def pool69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  once69 N C ∪ P.image (fun k=>N+k)

def branch69 (N : Nat) (C : Circuit) (P : Finset Nat) (x y : Nat) : Prop :=
  x∈pool69 N C P ∧ ∃k∈P, y=N+k ∧ x∈(gateAt C k).inputs

abbrev walk69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  Relation.ReflTransGen (branch69 N C P)

def sink69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Prop :=
  ∀ y, ¬ branch69 N C P x y

noncomputable def owner69 (N : Nat) (C : Circuit) (P : Finset Nat) (x : Nat) : Nat := by
  classical exact if h : ∃y,walk69 N C P x y ∧ sink69 N C P y then h.choose else x

noncomputable def roots69 (N : Nat) (C : Circuit) (P : Finset Nat) :=
  (once69 N C).image (owner69 N C P)

noncomputable def src69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (once69 N C).filter (fun w=>owner69 N C P w=z)

noncomputable def reg69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact P.filter (fun k=>owner69 N C P (N+k)=z)

noncomputable def outside69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Finset Nat := by
  classical exact (reg69 N C P z).biUnion fun k =>
    (gateAt C k).inputs.toFinset.filter (fun w=>w∉pool69 N C P)

noncomputable def slots69 (N : Nat) (C : Circuit) (P : Finset Nat) (z : Nat) : Nat := by
  classical exact ∑ k∈reg69 N C P z,(gateAt C k).inputs.countP (fun w=>decide (w∉pool69 N C P))

variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem reads_le_one69 (hp : P⊆ordinary N C) {w : Nat} (hw : w∈pool69 N C P) : reads69 C w≤1 := by
  rcases Finset.mem_union.mp hw with h | h
  · exact (Finset.mem_filter.mp h).2.le
  · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp h;exact ordinary_reads69 (hp hk)

theorem reader69 {w i j : Nat} (one : reads69 C w≤1) (hi : i<C.size) (hj : j<C.size)
    (a : w∈(gateAt C i).inputs) (b : w∈(gateAt C j).inputs) : i=j := by
  by_contra ne
  have h:=Finset.add_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _)
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) ne
  have ai:=List.count_pos_iff.mpr a
  have bj:=List.count_pos_iff.mpr b
  change _ ≤ reads69 C w at h
  omega

theorem next_unique69 (hp : P⊆ordinary N C) : Relator.RightUnique (branch69 N C P) := by
  rintro w x y ⟨hw,i,hi,rfl,a⟩ ⟨_,j,hj,rfl,b⟩
  rw [reader69 (reads_le_one69 hp hw) (ordinary_index69 (hp hi)) (ordinary_index69 (hp hj)) a b]

theorem next_lt69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (h : branch69 N C P x y) : x<y ∧ y<N+C.size := by
  obtain ⟨_,k,hk,rfl,inp⟩:=h
  have lt:=ordinary_index69 (hp hk)
  exact ⟨back k lt x inp,by omega⟩

theorem walk_in69 {x y : Nat} (h : walk69 N C P x y) (hx : x∈pool69 N C P) :
    y∈pool69 N C P := by
  induction h with
  | refl => exact hx
  | tail _ e _ =>
    obtain ⟨_,k,hk,rfl,_⟩ := e
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)

theorem owner_spec69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (w : Nat) :
    walk69 N C P w (owner69 N C P w) ∧ sink69 N C P (owner69 N C P w) := by
  classical
  have exists' (i : Nat) : ∀x,N+C.size-x=i → ∃y,walk69 N C P x y ∧ sink69 N C P y := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro x eq
      by_cases e : ∃y,branch69 N C P x y
      · obtain ⟨y,hy⟩:=e
        obtain ⟨lt,bound⟩:=next_lt69 hp back hy
        obtain ⟨v,path,sink⟩:=ih (N+C.size-y) (by omega) y rfl
        exact ⟨v,path.head hy,sink⟩
      · exact ⟨x,.refl,fun y h=> e ⟨y,h⟩⟩
  have h:=exists' _ w rfl
  simpa only [owner69,dif_pos h] using h.choose_spec

theorem owner_same69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat}
    (e : branch69 N C P x y) : owner69 N C P x = owner69 N C P y := by
  have a := owner_spec69 hp back x
  have b := owner_spec69 hp back y
  have term {u v : Nat} (s : sink69 N C P u) (path : walk69 N C P u v) : u=v := by
    rcases path.cases_head with eq|⟨z,e,_⟩
    · exact eq
    · exact (s z e).elim
  rcases Relation.ReflTransGen.total_of_right_unique (next_unique69 hp)
    a.1 (b.1.head e) with h|h
  · exact term a.2 h
  · exact (term b.2 h).symm

theorem fiber69 (z w : Nat) :
    w∈src69 N C P z ∪ (reg69 N C P z).image (fun k=>N+k) ↔
      w∈pool69 N C P ∧ owner69 N C P w=z := by
  classical
  constructor
  · intro h
    rcases Finset.mem_union.mp h with a|b
    · obtain ⟨h,e⟩:=Finset.mem_filter.mp a;exact ⟨Finset.mem_union_left _ h,e⟩
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      obtain ⟨h,e⟩:=Finset.mem_filter.mp hk;exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ h),e⟩
  · rintro ⟨pool,e⟩
    rcases Finset.mem_union.mp pool with a|b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨a,e⟩)
    · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp b
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hk,e⟩))

theorem root_info69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    z∈pool69 N C P ∧ sink69 N C P z ∧ owner69 N C P z=z ∧ (src69 N C P z).Nonempty := by
  obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
  have sp:=owner_spec69 hp back u
  refine ⟨walk_in69 sp.1 (Finset.mem_union_left _ hu),sp.2,?_,⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩⟩
  have p:=(owner_spec69 hp back (owner69 N C P u)).1
  rcases p.cases_head with eq|⟨x,step,_⟩
  · exact eq.symm
  · exact (sp.2 x step).elim

end PEqualNP.Outside.L_meta_25569_aux

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {P : Finset Nat}

theorem root_zero69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z : Nat} (hz : z∈roots69 N C P) :
    readsIn C (reg69 N C P z) z=0 := by
  obtain ⟨pool,sink,_,_⟩:=root_info69 hp back hz
  apply Finset.sum_eq_zero
  intro j hj;apply List.count_eq_zero.mpr
  intro h;exact sink (N+j) ⟨pool,j,(Finset.mem_filter.mp hj).1,rfl,h⟩

theorem local_read69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {z w : Nat}
    (pool : w∈pool69 N C P) (ow : owner69 N C P w=z) (other : w≠z) :
    readsIn C (reg69 N C P z) w=1 ∧ reads69 C w=1 := by
  obtain ⟨way,_⟩:=owner_spec69 hp back w
  rw [ow] at way
  obtain ⟨_,⟨_,k,hk,rfl,hit⟩,_⟩:=way.cases_head.resolve_left other
  have eq := owner_same69 hp back (show branch69 N C P w (N+k) from ⟨pool,k,hk,rfl,hit⟩)
  have mem : k∈reg69 N C P z := Finset.mem_filter.mpr ⟨hk,eq.symm.trans ow⟩
  have le : (gateAt C k).inputs.count w ≤ readsIn C (reg69 N C P z) w :=
    Finset.single_le_sum (fun l _=>Nat.zero_le ((gateAt C l).inputs.count w)) mem
  have bound : readsIn C (reg69 N C P z) w ≤ reads69 C w :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun j hj =>
      Finset.mem_range.mpr (ordinary_index69 (hp (Finset.mem_filter.mp hj).1))) (fun _ _ _=>Nat.zero_le _)
  have counted:=List.count_pos_iff.mpr hit;have all:=reads_le_one69 hp pool
  omega

theorem pool_bound69 (hp : P⊆ordinary N C) {w : Nat} (pool : w∈pool69 N C P) : w<N+C.size := by
  rcases Finset.mem_union.mp pool with h|h
  · have lt:=Finset.mem_range.mp (Finset.mem_filter.mp h).1;omega
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h;have:=ordinary_index69 (hp hj);omega

theorem walk_le69 (hp : P⊆ordinary N C) (back : ReadsBack N C) {x y : Nat} (path : walk69 N C P x y) :
    x≤y := by
  induction path with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (next_lt69 hp back e).1.le

theorem outside_mem69 {z w : Nat} :
    w∈outside69 N C P z ↔ w∉pool69 N C P ∧ ∃k∈reg69 N C P z,w∈(gateAt C k).inputs := by
  classical
  simp only [outside69,Finset.mem_biUnion,Finset.mem_filter,List.mem_toFinset]
  grind

private theorem read_le_slots69 {z w : Nat} (out : w∉pool69 N C P) :
    readsIn C (reg69 N C P z) w ≤ slots69 N C P z := by
  classical
  apply Finset.sum_le_sum
  intro k _
  induction (gateAt C k).inputs with
  | nil => simp
  | cons a l ih =>
    simp only [decide_not] at ih
    by_cases eq : a=w
    · subst a;simp [List.count_cons,List.countP_cons,out,ih]
    · by_cases pa:a∈pool69 N C P <;> simp [List.count_cons,List.countP_cons,eq,pa,ih] <;> omega

theorem out_pos69 {z w : Nat} (h : w∈outside69 N C P z) :
    0<readsIn C (reg69 N C P z) w ∧ readsIn C (reg69 N C P z) w≤slots69 N C P z := by
  obtain ⟨no,k,hk,hx⟩:=outside_mem69.mp h
  exact ⟨(List.count_pos_iff.mpr hx).trans_le
    (Finset.single_le_sum (fun j _=>Nat.zero_le ((gateAt C j).inputs.count w)) hk),read_le_slots69 no⟩

theorem outside_card69 {z : Nat} : (outside69 N C P z).card ≤ slots69 N C P z := by
  classical
  unfold outside69 slots69
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro k _
  have h (l : List Nat) : (l.toFinset.filter (fun w=>w∉pool69 N C P)).card ≤
      l.countP (fun w=>decide (w∉pool69 N C P)) := by
    induction l with
    | nil => simp
    | cons w l ih =>
      simp only [decide_not] at ih
      by_cases hw:w∈pool69 N C P
      · simpa [Finset.filter_insert,hw,List.countP_cons] using ih
      · simp [Finset.filter_insert,hw,List.countP_cons]
        exact (Finset.card_insert_le _ _).trans (by omega)
  exact h _

theorem outside_empty69 {z : Nat} : outside69 N C P z=∅ ↔ slots69 N C P z=0 := by
  classical
  constructor
  · intro empty;apply Finset.sum_eq_zero;intro k hk
    apply List.countP_eq_zero.mpr
    intro w hw
    simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_not]
    by_contra out
    have h : w∈outside69 N C P z := outside_mem69.mpr ⟨out,k,hk,hw⟩
    simp [empty] at h
  · intro z0;apply Finset.card_eq_zero.mp;have le:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z);omega

theorem subtree69 (hp : P⊆ordinary N C) (back : ReadsBack N C) (sh : shapes69 C)
    (last : C.output+1=N+C.size) {z : Nat} (hz : z∈roots69 N C P)
    (slot : slots69 N C P z≤1) : tree69 N C (src69 N C P z) (outside69 N C P z) := by
  classical
  obtain ⟨zp,sink,zown,nonempty⟩:=root_info69 hp back hz
  have bound:=pool_bound69 hp zp
  refine ⟨reg69 N C P z,z,fun j hj=>hp (Finset.mem_filter.mp hj).1,
    (fiber69 z z).mpr ⟨zp,zown⟩,root_zero69 hp back hz,?_,?_,?_⟩
  · intro w hw
    obtain ⟨out,k,hk,read⟩:=outside_mem69.mp hw
    have lt:=back k (ordinary_index69 (hp (Finset.mem_filter.mp hk).1)) w read
    have path:=(owner_spec69 hp back (N+k)).1
    rw [(Finset.mem_filter.mp hk).2] at path
    have cmp:=walk_le69 hp back path
    obtain ⟨pos,le⟩:=out_pos69 hw
    exact ⟨fun h=>out ((fiber69 z w).mp h).1,by omega,by omega⟩
  · intro j hj
    obtain ⟨keep,own⟩:=Finset.mem_filter.mp hj
    have ord:=hp keep;have jl:=ordinary_index69 ord
    have mem : gateAt C j∈C.gates := by have h:j<C.gates.length:=jl;simp [gateAt,h]
    rcases sh _ mem with ao | no
    · refine ⟨ao.1,ao.2,?_⟩
      intro w wh
      by_cases pooled:w∈pool69 N C P
      · exact Or.inl ((fiber69 z w).mpr ⟨pooled,(owner_same69 hp back ⟨pooled,j,keep,rfl,wh⟩).trans own⟩)
      · exact Or.inr (outside_mem69.mpr ⟨pooled,j,hj,wh⟩)
    · have ns: N+j∉special N C := (Finset.mem_filter.mp ord).2
      apply (ns (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (show j∈neg69 C from Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jl,no.1⟩)))).elim
  · intro w hw diff
    obtain ⟨pool,own⟩:=(fiber69 z w).mp hw
    obtain ⟨loc,all⟩:=local_read69 hp back pool own diff
    have path:=(owner_spec69 hp back w).1
    rw [own] at path
    have le:=walk_le69 hp back path
    exact ⟨loc,all,by omega⟩

end PEqualNP.Outside.L_meta_25569_aux

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C:Circuit}
lemma keepSub69 : keep69 N C ⊆ ordinary N C := Finset.sdiff_subset
lemma colorOnce69 {w:Nat} (h:w∈once69 N C) : color69 N C w=false := by
  obtain ⟨hw,one⟩:=Finset.mem_filter.mp h
  have lo:=Finset.mem_range.mp hw
  apply color_raw lo
  intro hs
  rcases Finset.mem_union.mp hs with rep|notw
  · have high:2≤reads69 C w := (Finset.mem_filter.mp rep).2
    omega
  · obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp notw;omega
lemma colorOuter69 (back:ReadsBack N C) {j w:Nat} (hp:j∈keep69 N C) (hit:w∈(gateAt C j).inputs)
    (out:w∉pool69 N C (keep69 N C)) : color69 N C w=true := by
  classical
  have jj:=ordinary_index69 (keepSub69 hp)
  have wr:=back j jj w hit
  by_cases hs:w∈special N C
  · exact color_special hs
  by_cases low:w<N
  · have used:0<reads69 C w := by
      have h:=Finset.single_le_sum (f:=fun k=>(gateAt C k).inputs.count w) (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr jj)
      have count:=List.count_pos_iff.mpr hit
      change _≤reads69 C w at h
      omega
    have one:reads69 C w=1 := by
      by_contra! ne
      apply hs
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩)
    exact (out (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr low,one⟩))).elim
  · let k:=w-N
    have eq:N+k=w := by dsimp [k];omega
    have ord:k∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [k];omega),by rwa [eq]⟩
    by_cases sp:k∈split69 N C
    · exact eq ▸ color_split_self back sp
    · have kkeep:k∈keep69 N C:=Finset.mem_sdiff.mpr ⟨ord,sp⟩
      exact (out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,kkeep,eq⟩))).elim

lemma markedInputs69 (back:ReadsBack N C) {j:Nat} (h:j∈keep69 N C) :
    (gateAt C j).inputs.countP (color69 N C) = if color69 N C (N+j) then 1 else 0 := by
  have le:=marked_keep_slots h
  rw [←List.countP_eq_length_filter] at le
  have pos := color_keep_iff back h
  rw [←List.countP_pos_iff] at pos
  cases hx:color69 N C (N+j)
  · change (gateAt C j).inputs.countP (color69 N C)=0
    by_contra! ne
    have eq:=pos.mpr (by omega)
    rw [hx] at eq;contradiction
  · change (gateAt C j).inputs.countP (color69 N C)=1
    have hp:=pos.mp hx
    omega

lemma splitInputCount69 (L:List Nat) (p:Nat→Bool) (pool A:Finset Nat)
    (spec:∀w∈L, (p w=true ↔ w∉pool ∨ w∈A) ∧ (w∈A → w∈pool)) :
    L.countP p = L.countP (fun w=>decide (w∉pool)) + ∑w∈A,L.count w := by
  classical
  induction L with
  | nil => simp
  | cons x xs ih =>
    have t:=ih (fun w hw=>spec w (List.mem_cons_of_mem _ hw))
    simp only [List.countP_cons,List.count_cons,Finset.sum_add_distrib]
    have a:=spec x (by simp)
    by_cases xA:x∈A <;> by_cases xp:x∈pool <;> cases xx:p x <;>
      simp_all <;> omega
end PEqualNP.Outside.L_meta_25569_aux

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem conserved69 {N z:Nat} {C:Circuit} (back:ReadsBack N C)
    (hz:z∈roots69 N C (keep69 N C))
    (lr:∀ j∈reg69 N C (keep69 N C) z,
      readsIn C (reg69 N C (keep69 N C) z) (N+j)=if N+j=z then 0 else 1) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  classical
  let P:=keep69 N C
  let pool:=pool69 N C P
  let rg:=reg69 N C P z
  let hot:=rg.filter (fun j=>color69 N C (N+j)=true)
  let A:=hot.image (fun j=>N+j)
  have acard:A.card=hot.card:=Finset.card_image_of_injective _ (fun _ _ e=>Nat.add_left_cancel e)
  have rgKeep (j:Nat) (hj:j∈rg):j∈P:=(Finset.mem_filter.mp hj).1
  have memA {w:Nat} : w∈A ↔ w∈pool ∧ owner69 N C P w=z ∧ color69 N C w=true := by
    constructor
    · intro h;obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp h
      obtain ⟨jr,marked⟩:=Finset.mem_filter.mp hj
      exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (rgKeep _ jr)),(Finset.mem_filter.mp jr).2,marked⟩
    · rintro ⟨h,o,t⟩
      rcases Finset.mem_union.mp h with raw|gate
      · exact (by rw [colorOnce69 raw] at t; contradiction : False).elim
      · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp gate
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hj,o⟩,t⟩,rfl⟩
  have inEq (j:Nat) (hj:j∈rg) :
      (gateAt C j).inputs.countP (color69 N C) =
        (gateAt C j).inputs.countP (fun w=>decide (w∉pool)) + ∑w∈A,(gateAt C j).inputs.count w := by
    apply splitInputCount69
    intro w hit
    have memPool (h:w∈pool) : owner69 N C P w=z := by
      have p:=owner_same69 (P:=P) keepSub69 back (show branch69 N C P w (N+j) from ⟨h,j,rgKeep _ hj,rfl,hit⟩)
      exact p.trans (Finset.mem_filter.mp hj).2
    refine ⟨⟨fun t=>?_,?_⟩,fun h=>(memA.mp h).1⟩
    · by_cases pw:w∈pool
      · exact Or.inr (memA.mpr ⟨pw,memPool pw,t⟩)
      · exact Or.inl pw
    · rintro (out|inside)
      · exact colorOuter69 back (rgKeep _ hj) hit out
      · exact (memA.mp inside).2.2
  have calcAll : hot.card=slots69 N C P z+∑w∈A,readsIn C rg w := by
    calc
      hot.card = ∑j∈rg, if color69 N C (N+j) then 1 else 0 := by simp only [hot,Finset.card_filter]
      _ = ∑j∈rg,(gateAt C j).inputs.countP (color69 N C) :=
        Finset.sum_congr rfl (fun j hj=>(markedInputs69 back (rgKeep _ hj)).symm)
      _ = _ := by
        rw [Finset.sum_congr rfl inEq,Finset.sum_add_distrib]
        congr 1;exact Finset.sum_comm
  have lower : (∑w∈A,readsIn C rg w)+(if z∈A then 1 else 0)=A.card := by
    calc
      _ = (∑w∈A,if w=z then 0 else 1) + (∑w∈A,if w=z then 1 else 0) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro w hw;obtain ⟨j,m,rfl⟩:=Finset.mem_image.mp hw
          exact lr _ (Finset.mem_filter.mp m).1
        · simp
      _ = ∑_w∈A,1 := by
        rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro w _;split <;> simp_all
      _ = _ := by simp
  have root:=root_info69 (P:=P) keepSub69 back hz
  have za : z∈A ↔ color69 N C z=true := ⟨fun h=>(memA.mp h).2.2,fun h=>memA.mpr ⟨root.1,root.2.2.1,h⟩⟩
  change slots69 N C P z=_
  simp only [za] at lower
  omega
end PEqualNP.Outside.L_meta_25569_aux

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem fiberSlots69 {N z:Nat} {C:Circuit} (back:ReadsBack N C) (hz:z∈roots69 N C (keep69 N C)) :
    slots69 N C (keep69 N C) z = if color69 N C z then 1 else 0 := by
  apply conserved69 back hz
  intro j hj
  by_cases eq:N+j=z
  · rw [eq,ite_eq_left rfl]
    exact root_zero69 keepSub69 back hz
  · rw [ite_eq_right eq]
    obtain ⟨m,e⟩:=Finset.mem_filter.mp hj
    have pool:N+j∈pool69 N C (keep69 N C):=Finset.mem_union_right _ (Finset.mem_image_of_mem _ m)
    exact (local_read69 keepSub69 back pool e eq).1
end PEqualNP.Outside.L_meta_25569_aux

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

private theorem sum_reads_mask69 (l : List Nat) (A : Finset Nat) :
    (∑w∈A,l.count w) = l.countP (fun w=>decide (w∈A)) := by
  classical
  let f:=l.filter (fun w=>decide (w∈A))
  have sub:f.toFinset⊆A := fun _ hw=>of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
  rw [List.countP_eq_length_filter]
  change _=f.length
  calc
    _ = ∑w∈A,f.count w := Finset.sum_congr rfl (fun w hw=>(List.count_filter (by simpa using hw)).symm)
    _ = ∑w∈f.toFinset,f.count w := (Finset.sum_subset sub (fun _ _ h=>
      List.count_eq_zero.mpr (fun e=>h (List.mem_toFinset.mpr e)))).symm
    _ = _ := List.sum_toFinset_count_eq_length f

private theorem pure_sink69 {N z : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j))
    (hz : z∈roots69 N C (keep69 N C)) (zero : slots69 N C (keep69 N C) z=0) (out : z≠C.output) :
    z∉special N C ∧ ∃k∈gates69 C \ ordinary N C, z∈(gateAt C k).inputs := by
  classical
  obtain ⟨pool,sink,_,_⟩:=root_info69 keepSub69 back hz
  have slot:=fiberSlots69 back hz
  have off : color69 N C z=false := by cases h:color69 N C z <;> simp_all
  have ns : z∉special N C := fun h => by have a:=color_special h;rw [off] at a;contradiction
  have pos : 0<reads69 C z := by
    rcases Finset.mem_union.mp pool with raw|internal
    · have one : reads69 C z=1 := (Finset.mem_filter.mp raw).2;omega
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp internal
      have lt:=ordinary_index69 (keepSub69 hj)
      exact live j lt (by omega)
  have seek : ∃ k∈gates69 C, z∈(gateAt C k).inputs := by
    by_contra! no
    have none : reads69 C z=0 := Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (no j hj))
    omega
  obtain ⟨k,hk,hit⟩:=seek
  refine ⟨ns,k,Finset.mem_sdiff.mpr ⟨hk,?_⟩,hit⟩
  intro ord
  by_cases split:k∈split69 N C
  · have on:=color_split_all sh split z hit
    rw [off] at on;contradiction
  · exact sink (N+k) ⟨pool,k,Finset.mem_sdiff.mpr ⟨ord,split⟩,rfl,hit⟩

theorem pure_count69 {N : Nat} {C : Circuit} (sh : shapes69 C) (back : ReadsBack N C)
    (last : C.output+1=N+C.size) (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)).card ≤ exits69 N C+1 := by
  classical
  let T:=(roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z=0)
  let A:=T.erase C.output
  let gs:=gates69 C \ ordinary N C
  have obs (w : Nat) (hw:w∈A) : w∉special N C ∧ ∃k∈gs, w∈(gateAt C k).inputs := by
    obtain ⟨different,hh⟩:=Finset.mem_erase.mp hw
    obtain ⟨inR,zero⟩:=Finset.mem_filter.mp hh
    exact pure_sink69 sh back last live inR zero different
  have each (w:Nat) (hw:w∈A) : 1 ≤ ∑k∈gs,(gateAt C k).inputs.count w := by
    obtain ⟨k,hk,hit⟩:=(obs w hw).2
    exact (List.count_pos_iff.mpr hit).trans_le
      (Finset.single_le_sum (fun t _=>Nat.zero_le ((gateAt C t).inputs.count w)) hk)
  have bound : A.card≤exits69 N C := by
    calc
      _ = ∑ _∈A,1 := by simp
      _ ≤ ∑w∈A,∑k∈gs,(gateAt C k).inputs.count w := Finset.sum_le_sum each
      _ = ∑k∈gs,∑w∈A,(gateAt C k).inputs.count w := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        rw [sum_reads_mask69]
        exact List.countP_mono_left (fun w _ h => decide_eq_true ((obs w (of_decide_eq_true h)).1))
  change T.card≤exits69 N C+1
  have incl : T⊆insert C.output A := by
    intro z mem;by_cases e:z=C.output
    · exact Finset.mem_insert.mpr (Or.inl e)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨e,mem⟩))
  have step:=Finset.card_le_card incl
  have cap:=Finset.card_insert_le C.output A
  change T.card≤(insert C.output A).card at step
  omega
end PEqualNP.Outside.L_meta_25569_aux

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem mixed_count69 {N:Nat} {C:Circuit} (sh:shapes69 C) (back:ReadsBack N C) :
    ((roots69 N C (keep69 N C)).filter (fun z=>slots69 N C (keep69 N C) z≠0)).card≤2*entries69 N C := by
  classical
  let P:=keep69 N C
  let R:=(roots69 N C P).filter (fun z=>slots69 N C P z≠0)
  let f:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∉pool69 N C P))
  let g:=fun j=>(gateAt C j).inputs.countP (fun w=>decide (w∈special N C ∨ (N≤w ∧ w-N∈split69 N C)))
  have per (j:Nat) (hj:j∈P): f j≤g j := by
    apply List.countP_mono_left
    intro w hw out'
    have out:w∉pool69 N C P:=of_decide_eq_true out'
    apply decide_eq_true
    by_cases sp:w∈special N C
    · exact Or.inl sp
    · have color:=colorOuter69 back hj hw out
      have nle : N≤w:=by by_contra! h;rw [color_raw h sp] at color;contradiction
      have eq:N+(w-N)=w:=by omega
      have ji:=ordinary_index69 (keepSub69 hj)
      have wi:=back j ji w hw
      have ord:w-N∈ordinary N C:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by rwa [eq]⟩
      refine Or.inr ⟨nle,?_⟩
      by_contra ns
      have inside:w-N∈P:=Finset.mem_sdiff.mpr ⟨ord,ns⟩
      exact out (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,inside,eq⟩))
  have lower (z:Nat) (hz:z∈R) : 1≤slots69 N C P z := by
    have neq:slots69 N C P z≠0:=(Finset.mem_filter.mp hz).2
    omega
  change R.card≤_
  calc
    R.card = ∑_z∈R,1 := by simp
    _ ≤ ∑z∈R,slots69 N C P z := Finset.sum_le_sum lower
    _ = ∑j∈P.filter (fun i=>owner69 N C P (N+i)∈R), f j :=
      Finset.sum_fiberwise_eq_sum_filter P R (fun j=>owner69 N C P (N+j)) f
    _ ≤ ∑j∈P,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>Nat.zero_le _)
    _ ≤ ∑j∈P,g j := Finset.sum_le_sum per
    _ ≤ _ := entrySlotsBound69 sh back
end PEqualNP.Outside.L_meta_25569_aux

namespace PEqualNP.Outside.L_meta_25569_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem finish69 (N : Nat) (C : Circuit) (sh : shapes69 C) (back : ReadsBack N C)
    (_pos : 0<C.size) (last : C.output+1=N+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<reads69 C (N+j)) :
    ∃ pure chains : List (Finset Nat),
      pure.length≤exits69 N C+1 ∧ chains.length≤2*entries69 N C ∧
      (pure++chains).Pairwise (fun A B=>Disjoint A B) ∧
      (pure++chains).toFinset.biUnion (fun S=>S)=once69 N C ∧
      (∀S∈pure,S.Nonempty ∧ tree69 N C S ∅) ∧
      (∀S∈chains,S.Nonempty ∧ ∃b : Nat,tree69 N C S {b}) := by
  classical
  let P:=keep69 N C
  let roots:=roots69 N C P
  let Q:=roots.filter (fun z=>slots69 N C P z=0)
  let M:=roots.filter (fun z=>slots69 N C P z≠0)
  let leaf:=src69 N C P
  let qr:=Q.toList
  let mr:=M.toList
  have qmem (z:Nat) : z∈qr ↔ z∈roots ∧ slots69 N C P z=0 := by simp [qr,Q]
  have mmem (z:Nat) : z∈mr ↔ z∈roots ∧ slots69 N C P z≠0 := by simp [mr,M]
  have covered (z:Nat) : z∈qr++mr ↔ z∈roots := by
    rw [List.mem_append,qmem,mmem];tauto
  have nd : (qr++mr).Nodup := by
    refine List.nodup_append.mpr ⟨Q.nodup_toList,M.nodup_toList,?_⟩
    intro x hx y hy e;subst y;exact (mmem x|>.mp hy).2 ((qmem x|>.mp hx).2)
  have fiber {w z:Nat}: w∈leaf z ↔ w∈once69 N C ∧ owner69 N C P w=z := Finset.mem_filter
  have facts {z:Nat} (hz:z∈roots) : (leaf z).Nonempty ∧
      tree69 N C (leaf z) (outside69 N C P z) := by
    have count:=fiberSlots69 back hz
    have le : slots69 N C P z≤1 := by rw [count];split <;> decide
    exact ⟨(root_info69 keepSub69 back hz).2.2.2,subtree69 keepSub69 back sh last hz le⟩
  refine ⟨qr.map leaf,mr.map leaf,?_,?_,?_,?_,?_,?_⟩
  · simpa only [qr,List.length_map,Finset.length_toList] using pure_count69 sh back last live
  · simpa only [mr,List.length_map,Finset.length_toList] using mixed_count69 sh back
  · rw [←List.map_append,List.pairwise_map]
    apply nd.imp
    intro a b diff
    apply Finset.disjoint_left.mpr
    intro w ha hb;exact diff ((fiber.mp ha).2.symm.trans (fiber.mp hb).2)
  · rw [←List.map_append]
    ext w
    simp only [Finset.mem_biUnion,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨_,⟨z,_,rfl⟩,hit⟩;exact (fiber.mp hit).1
    · intro raw
      let z:=owner69 N C P w
      have root:z∈roots:=Finset.mem_image_of_mem _ raw
      exact ⟨leaf z,⟨z,(covered z).mpr root,rfl⟩,fiber.mpr ⟨raw,rfl⟩⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,zero⟩:=(qmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    rw [outside_empty69.mpr zero] at tree
    exact ⟨ne,tree⟩
  · intro S hs
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hs
    obtain ⟨rt,nz⟩:=(mmem z).mp hz
    obtain ⟨ne,tree⟩:=facts rt
    have card : (outside69 N C P z).card=1 := by
      have cap:=outside_card69 (N:=N) (C:=C) (P:=P) (z:=z)
      have count:=fiberSlots69 back rt
      have nonempty : (outside69 N C P z).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (fun h=>nz (outside_empty69.mp h))
      have pos:=Finset.card_pos.mpr nonempty
      change slots69 N C P z=_ at count
      split at count <;> omega
    obtain ⟨b,eq⟩:=Finset.card_eq_one.mp card
    exact ⟨ne,b,eq ▸ tree⟩
end PEqualNP.Outside.L_meta_25569_aux

theorem PEqualNP.Outside.L_meta_25569 :
∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  let special := ((Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)) ∪
    neg.image (fun k => n + k)
  let ordinaryGates := gates.filter (fun k => n + k ∉ special)
  let exits := ∑ k ∈ gates \ ordinaryGates,
    (gate k).inputs.countP (fun w => decide (w ∉ special))
  let entries := ∑ k ∈ ordinaryGates,
    (gate k).inputs.countP (fun w => decide (w ∈ special))
  let once := (Finset.range n).filter (fun w => reads w = 1)
  let tree := fun (S E : Finset ℕ) => ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
    region ⊆ ordinaryGates ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w)
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  0 < C.size → C.output + 1 = n + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads (n + j)) →
  ∃ pure chains : List (Finset ℕ),
    pure.length ≤ exits + 1 ∧ chains.length ≤ 2 * entries ∧
    (pure ++ chains).Pairwise (fun A B => Disjoint A B) ∧
    (pure ++ chains).toFinset.biUnion (fun S => S) = once ∧
    (∀ S ∈ pure, S.Nonempty ∧ tree S ∅) ∧
    (∀ S ∈ chains, S.Nonempty ∧ ∃ b : ℕ, tree S {b}) := by
  intro n C
  exact PEqualNP.Outside.L_meta_25569_aux.finish69 n C

import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.GraphSampleDistance

namespace PEqualNP.Outside.L_lib_1461_aux
open scoped BigOperators Classical
abbrev W (n : ℕ) := Finset (Fin n)
def lows (i : Fin n) := Finset.univ.filter (fun x : W n => i∉x)
theorem lowMem (i : Fin n) (x : W n) : x∈lows i ↔ i∉x := by simp [lows]
theorem lowCount (i : Fin n) : (lows i).card=2^(n-1) := by
  have eq : lows i=(Finset.univ.erase i).powerset := by
    ext x
    simp only [lowMem,Finset.mem_powerset]
    constructor
    · intro no j h; exact Finset.mem_erase.mpr ⟨fun eq => no (eq ▸ h),Finset.mem_univ _⟩
    · intro sub hi; exact (Finset.mem_erase.mp (sub hi)).1 rfl
  simp [eq,Finset.card_erase_of_mem]
theorem splitSum (i : Fin n) (f : W n → ℕ) : ∑x,f x=(lows i).sum (fun x => f x+f (insert i x)) := by
  classical
  let U := (lows i).image (insert i)
  have split : (Finset.univ : Finset (W n))=lows i ∪ U := by
    ext x; simp only [Finset.mem_univ,true_iff,Finset.mem_union,lowMem]
    by_cases h : i∈x
    · exact Or.inr (Finset.mem_image.mpr ⟨x.erase i,(lowMem ..).mpr (by simp),Finset.insert_erase h⟩)
    · exact Or.inl h
  have dis : Disjoint (lows i) U := by
    apply Finset.disjoint_left.mpr; intro x hx h
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp h
    exact (lowMem ..).mp hx (Finset.mem_insert_self ..)
  have inj {x y : W n} (a : x∈lows i) (b : y∈lows i) (eq : insert i x=insert i y) : x=y := by
    simpa [Finset.erase_insert ((lowMem ..).mp a),Finset.erase_insert ((lowMem ..).mp b)] using congrArg (fun z : W n => z.erase i) eq
  rw [split,Finset.sum_union dis,Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_image (fun _ => fun a _ b eq => inj a b eq)
def pairs (w : W n → ℕ) (i : Fin n) := (lows i).sum (fun x => min (w x) (w (insert i x)))
def gap (w : W n → ℕ) (i : Fin n) (x : W n) := (w x-w (insert i x))+(w (insert i x)-w x)
theorem massId (w : W n → ℕ) (i : Fin n) : ∑x,w x=2*pairs w i+(lows i).sum (gap w i) := by
  rw [splitSum i,pairs,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  unfold gap; omega
def Jump (w : W n → ℕ) (i : Fin n) (x : W n) := i∉x ∧ w x≠w (insert i x)
theorem onlyJump {w : W n → ℕ} (small : (lows i).sum (gap w i)≤1) {x y}
    (a : Jump w i x) (b : Jump w i y) : x=y := by
  classical
  by_contra ne
  have pos (z) (j : Jump w i z) : 0<gap w i z := by unfold gap; have := j.2; omega
  have sub : {x,y}⊆lows i := by
    intro z hz; simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl
    · exact (lowMem ..).mpr a.1
    · exact (lowMem ..).mpr b.1
  have sum := Finset.sum_le_sum_of_subset (f:=gap w i) sub
  simp [ne] at sum
  have upper := sum.trans small; have := pos x a; have := pos y b; omega
def flip (j : Fin n) (x : W n) := if j∈x then x.erase j else insert j x
theorem memFlip {j b : Fin n} (x : W n) : b∈flip j x ↔ (if b=j then b∉x else b∈x) := by
  unfold flip; split_ifs <;> simp_all
theorem flipIns {j l : Fin n} (hne : j≠l) (x : W n) : flip l (insert j x)=insert j (flip l x) := by
  ext b; by_cases bj : b=j <;> by_cases bl : b=l <;> simp_all [memFlip]
theorem noMove {w : W n → ℕ} {j : Fin n} (x : W n) (h : ∀y, y=x ∨ y=x.erase j → ¬ Jump w j y) :
    w (flip j x)=w x := by
  by_cases mem : j∈x
  · have z := h (x.erase j) (Or.inr rfl)
    simpa [flip,mem,Jump,Finset.insert_erase mem] using z
  · have z := h x (Or.inl rfl)
    simpa [flip,mem,Jump,eq_comm] using z

theorem noOpposite {w : W n → ℕ} (unique : ∀i x y,Jump w i x → Jump w i y → x=y)
    (i j l : Fin n) (ij : i≠j) (il : i≠l) (x y : W n) (lx : i∉x) (uy : i∈y)
    (jx : Jump w j x) (ly : Jump w l y) : False := by
  have jl : j≠l := by rintro rfl; exact lx ((unique j x y jx ly).symm ▸ uy)
  have stable (z : W n) (lo : i∉z) : w (flip l z)=w z := by
    apply noMove; intro z' shape jump
    have eq := unique l z' y jump ly
    have hi : i∈z' := eq.symm ▸ uy
    rcases shape with rfl|rfl
    · exact lo hi
    · exact lo (Finset.mem_of_mem_erase hi)
  have distinct : x≠flip l x := by
    intro eq
    have mem : l∈x ↔ l∈flip l x := by rw [←eq]
    simpa [memFlip] using mem
  apply distinct (unique j x (flip l x) jx ?_)
  constructor
  · simpa [memFlip,jl] using jx.1
  · rw [←flipIns jl,stable _ lx,stable _ (by simp [ij,lx])]
    exact jx.2

theorem flatSide {w : W n → ℕ} (unique : ∀i x y,Jump w i x → Jump w i y → x=y) (i : Fin n) :
    (∀x,i∉x → w x=w ∅) ∨ (∀x,i∉x → w (insert i x)=w {i}) := by
  classical
  by_cases jump : ∃j x,i≠j ∧ i∉x ∧ Jump w j x
  · right
    obtain ⟨j,z,ij,iz,jz⟩ := jump
    intro x
    induction x using Finset.induction_on with
    | empty => simp
    | @insert l x fresh ih =>
      intro no
      have il : i≠l := fun eq => no (eq ▸ Finset.mem_insert_self ..)
      have ox : i∉x := fun h => no (Finset.mem_insert_of_mem h)
      rw [Finset.insert_comm i l]
      rw [←ih ox]
      symm; by_contra neq
      exact noOpposite unique i j l ij il z (insert i x) iz (Finset.mem_insert_self ..) jz
        ⟨by simp [il.symm,fresh],neq⟩
  · left; intro x
    induction x using Finset.induction_on with
    | empty => simp
    | @insert j x fresh ih =>
      intro no
      have ij : i≠j := fun eq => no (eq ▸ Finset.mem_insert_self ..)
      have ox : i∉x := fun h => no (Finset.mem_insert_of_mem h)
      rw [←ih ox]; symm; by_contra neq
      exact jump ⟨j,x,ij,ox,fresh,neq⟩
end PEqualNP.Outside.L_lib_1461_aux

namespace PEqualNP.Outside.L_lib_1461_aux
open scoped BigOperators Classical
def Good (D m : ℕ) (w : W n → ℕ) := (∑x,w x)=m ∧ ∀i,pairs w i≥D
theorem necessary {D m : ℕ} {w : W n → ℕ} (pos : 0<n) (good : Good D m w) :
    2*D ≤ m ∧ (m≤2*D+1 → ∃c : ℕ, 2*(2^(n-1)*c) ≤ m+1 ∧ m≤2*(2^(n-1)*c)+1) := by
  classical
  let i : Fin n := ⟨0,pos⟩
  have identity j := (good.1.symm.trans (massId w j))
  have lb := good.2 i
  have eq := identity i
  refine ⟨by omega,?_⟩
  intro ub
  have small j : (lows j).sum (gap w j) ≤ 1 := by have := good.2 j; have := identity j; omega
  have uniq (j : Fin n) (x y : W n) : Jump w j x → Jump w j y → x=y := onlyJump (small j)
  obtain ⟨c,side⟩ : ∃c,∀x∈lows i,w x=c ∨ w (insert i x)=c := by
    rcases flatSide uniq i with z|z
    · exact ⟨w ∅,fun x hx => Or.inl (z x ((lowMem ..).mp hx))⟩
    · exact ⟨w {i},fun x hx => Or.inr (z x ((lowMem ..).mp hx))⟩
  obtain ⟨z,zlow,exc⟩ : ∃z∈lows i,∀x∈lows i,x≠z → w x=w (insert i x) := by
    by_cases ex : ∃z,Jump w i z
    · obtain ⟨z,jz⟩ := ex
      exact ⟨z,(lowMem ..).mpr jz.1,fun x hx ne => by by_contra hh; exact ne (uniq _ _ _ ⟨(lowMem ..).mp hx,hh⟩ jz)⟩
    · exact ⟨∅,(lowMem ..).mpr (by simp),fun x hx _ => by by_contra hh; exact ex ⟨x,(lowMem ..).mp hx,hh⟩⟩
  let T := (lows i).erase z
  have uniform (x) (hx : x∈T) : w x+w (insert i x)=2*c := by
    obtain ⟨ne,low⟩ := Finset.mem_erase.mp hx
    have he := exc x low ne; rcases side x low with h|h <;> omega
  have split : m=T.card*(2*c)+(w z+w (insert i z)) := by
    rw [←good.1,splitSum i]
    rw [←Finset.sum_erase_add _ _ zlow]
    congr 1
    exact Finset.sum_const_nat uniform
  have num : T.card+1=2^(n-1) := (Finset.card_erase_add_one zlow).trans (lowCount i)
  have gz : gap w i z≤1 := (Finset.single_le_sum (fun x _ => Nat.zero_le (gap w i x)) zlow).trans (small i)
  unfold gap at gz
  have mul : 2*(2^(n-1)*c)=T.card*(2*c)+2*c := by rw [←num]; ring
  refine ⟨c,?_⟩; rcases side z zlow with h|h <;> omega

theorem cubeCard (pos : 0<n) : Fintype.card (W n)=2*2^(n-1) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  simp [W,Fintype.card_finset,Nat.pow_succ,Nat.mul_comm]
def plus (c : ℕ) (x : W n) := if x=∅ then c+1 else c
def less (c : ℕ) (x : W n) := if x=∅ then c-1 else c
theorem profile {n : ℕ} (c : ℕ) :
    (∀ i : Fin n,pairs (fun _ => c) i=2^(n-1)*c) ∧
    (∀ i : Fin n,2^(n-1)*c≤pairs (plus c) i) ∧
    (∀ i : Fin n,2^(n-1)*c≤pairs (less c) i+1) := by
  classical
  refine ⟨fun i => by simp [pairs,lowCount],?_,?_⟩
  · intro i
    rw [←lowCount i,←Finset.sum_const_nat (s:=lows i) (f:=fun _ => c) (fun _ _ => rfl)]
    apply Finset.sum_le_sum; intro x _
    apply le_min <;> simp [plus] <;> split_ifs <;> omega
  · intro i
    have low : ∅∈lows i := (lowMem ..).mpr (by simp)
    have const (x : W n) (h : x∈(lows i).erase ∅) : min (less c x) (less c (insert i x))=c := by
      simp [less,(Finset.mem_erase.mp h).1]
    have er := Finset.sum_const_nat const
    have one := Finset.card_erase_add_one low
    have h := Finset.sum_erase_add (lows i) (fun x => min (less c x) (less c (insert i x))) low
    rw [er] at h
    have atEmpty : min (less c (∅ : W n)) (less c (insert i ∅))=c-1 := by simp [less]
    rw [atEmpty] at h
    unfold pairs
    rw [←lowCount i,←one,Nat.add_mul]; omega
theorem exactBanks (pos : 0<n) (D : ℕ) :
    ((∃w : W n → ℕ,Good D (2*D) w) ↔ 2^(n-1)∣D) ∧
    ((∃w : W n → ℕ,Good D (2*D+1) w) ↔ 2^(n-1)∣D ∨ 2^(n-1)∣D+1) := by
  classical
  constructor
  · constructor
    · rintro ⟨w,h⟩
      obtain ⟨c,a,b⟩ := (necessary pos h).2 (by omega)
      exact ⟨c,by omega⟩
    · rintro ⟨c,rfl⟩
      exact ⟨fun _ => c,by simp [cubeCard pos,Nat.mul_assoc],fun i => ((profile c).1 i).ge⟩
  · constructor
    · rintro ⟨w,h⟩
      obtain ⟨c,a,b⟩ := (necessary pos h).2 (by omega)
      by_cases eq : D=2^(n-1)*c
      · exact Or.inl ⟨_,eq⟩
      · exact Or.inr ⟨c,by omega⟩
    · rintro (⟨c,rfl⟩|⟨c,eq⟩)
      · refine ⟨plus c,?_,(profile c).2.1⟩
        have h (x : W n) : plus c x=c+(if x=∅ then 1 else 0) := by by_cases z : x=∅ <;> simp [plus,z]
        simp [h,Finset.sum_add_distrib,cubeCard pos,Nat.mul_assoc]
      · have cp : 0<c := by by_contra! h; simp [show c=0 by omega] at eq
        refine ⟨less c,?_,fun i => by have := (profile c).2.2 i; omega⟩
        have h (x : W n) : less c x+(if x=∅ then 1 else 0)=c := by by_cases z : x=∅ <;> simp [less,z] <;> omega
        have s := Finset.sum_congr (s₁:=Finset.univ) rfl (fun x _ => h x)
        simp only [Finset.sum_add_distrib] at s
        simp [cubeCard pos,Nat.mul_assoc,←eq] at s
        omega
end PEqualNP.Outside.L_lib_1461_aux

namespace PEqualNP.Outside.L_lib_1461_aux
open scoped BigOperators Classical
def freq (row : Fin m → W n) (x : W n) := (Finset.univ.filter (fun j => row j=x)).card
def kept (row : Fin m → W n) (lost : Finset (Fin m)) := (Finset.univ\lost).image row
def flipPair (A : Finset (W n)) (i : Fin n) := ∃x∈lows i,x∈A ∧ insert i x∈A
theorem allRows (row : Fin m → W n) : ∑x,freq row x=m := by
  have h := Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ row
  simpa [freq] using h
theorem realize (w : W n → ℕ) (total : ∑x,w x=m) : ∃ row : Fin m → W n, ∀x,freq row x=w x := by
  classical
  let K := (x : W n) × Fin (w x)
  let e : K ≃ Fin m := Fintype.equivFinOfCardEq (by simpa [K,Fintype.card_sigma] using total)
  let row (j : Fin m) := (e.symm j).1
  refine ⟨row,?_⟩
  intro x
  let slot : Fin (w x) ↪ Fin m := ⟨fun b => e ⟨x,b⟩,fun a b h => by exact Fin.ext (congrArg (fun z : K => z.2.val) (e.injective h))⟩
  have eq : Finset.univ.filter (fun j => row j=x)=Finset.univ.map slot := by
    ext j; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
    constructor
    · intro h
      obtain ⟨⟨z,b⟩,rfl⟩ := e.surjective j
      change (e.symm (e ⟨z,b⟩)).1=x at h; simp only [Equiv.symm_apply_apply] at h; subst z
      exact ⟨b,rfl⟩
    · rintro ⟨b,rfl⟩; change (e.symm (e ⟨x,b⟩)).1=x; simp
  unfold freq; rw [eq]; simp
theorem eraseIff (row : Fin m → W n) (d : ℕ) (i : Fin n) :
    (∀ lost : Finset (Fin m),lost.card≤d → flipPair (kept row lost) i) ↔ d+1≤pairs (freq row) i := by
  classical
  let fibre (x : W n) := Finset.univ.filter (fun j => row j=x)
  let pick (s : W n → Prop) (x : W n) := if s x then x else insert i x
  let cut (s : W n → Prop) := Finset.univ.filter (fun j => row j ∈ (lows i).image (pick s))
  have inj (s) {x y : W n} (hx : x∈lows i) (hy : y∈lows i) (e : pick s x=pick s y) : x=y := by
    have h (z) (hz : z∈lows i) : (pick s z).erase i=z := by
      have no := (lowMem ..).mp hz
      by_cases p : s z <;> simp [pick,p,Finset.erase_eq_of_notMem no,Finset.erase_insert no]
    exact (h x hx).symm.trans ((congrArg (fun z : W n => z.erase i) e).trans (h y hy))
  have cost s : (cut s).card=(lows i).sum (fun x => freq row (pick s x)) := by
    unfold cut
    rw [←Finset.sum_card_fiberwise_eq_card_filter,Finset.sum_image (fun a ha b hb e => inj s ha hb e)]
    rfl
  have survives (lost) (x : W n) : x∈kept row lost ↔ ¬ fibre x ⊆ lost := by
    simp only [kept,Finset.mem_image,Finset.mem_sdiff,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,live,rfl⟩ sub; exact live (sub (by simp [fibre]))
    · intro fail
      obtain ⟨j,inF,no⟩ := Finset.not_subset.mp fail
      exact ⟨j,no,(Finset.mem_filter.mp inF).2⟩
  constructor
  · intro robust; by_contra! low
    let s (x : W n) := freq row x≤freq row (insert i x)
    have budget : (cut s).card≤d := by
      rw [cost]; have h x : freq row (pick s x)=min (freq row x) (freq row (insert i x)) := by
        by_cases p : s x <;> simp only [pick,p,ite_true,ite_false]
        · exact (min_eq_left p).symm
        · exact (min_eq_right (Nat.le_of_not_ge p)).symm
      simpa only [h,pairs] using Nat.le_of_lt_succ low
    obtain ⟨x,hx,l,r⟩ := robust _ budget
    have dead : fibre (pick s x) ⊆ cut s := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2 ▸ Finset.mem_image_of_mem _ hx⟩
    by_cases p : s x
    · exact (survives _ _).mp l (by simpa [pick,p] using dead)
    · exact (survives _ _).mp r (by simpa [pick,p] using dead)
  · intro large lost budget; by_contra fail
    let s (x : W n) := fibre x ⊆ lost
    have dead (x) (hx : x∈lows i) : fibre (pick s x)⊆lost := by
      by_cases p : s x
      · simp only [pick,if_pos p]; exact p
      · simp only [pick,p,ite_false]; by_contra ok
        exact fail ⟨_,hx,(survives _ _).mpr p,(survives _ _).mpr ok⟩
    have sub : cut s ⊆ lost := by
      intro j hj
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hj).2
      exact dead x hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq.symm⟩)
    have lb : pairs (freq row) i ≤ (cut s).card := by
      rw [cost]; apply Finset.sum_le_sum; intro x _
      by_cases p : s x <;> simp [pick,p]
    exact (Nat.not_lt_of_ge (((Finset.card_le_card sub).trans budget))) (large.trans lb)
end PEqualNP.Outside.L_lib_1461_aux

namespace PEqualNP.Outside.L_lib_1461_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GraphSeedSamples
open scoped Classical
noncomputable def L (S : W n) := (bank ∅ S).toList
def Has (A : Finset (W n)) (S : W n) (p : ℕ) := ∃ C : Circuit, Monotone2 C ∧
    NestedCover.ReadsBack (L S).length C ∧ C.output<(L S).length+C.size ∧ C.size≤p ∧
    ∀ i : Fin n, ∃ j<(L S).length+C.size,∀x∈A,(C.wires ((L S).map (fun f => f x))).getD j false=inv i x
theorem budgetless (A : Finset (W n)) (S : W n) :
    (∃p,Has A S p) ↔ fits A (L S) (Finset.univ.image inv) := by
  constructor
  · rintro ⟨p,C,mo,rb,out,_,reads⟩
    refine ⟨C,mo,rb,out,?_⟩
    intro f hf; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf; exact reads i
  · rintro ⟨C,mo,rb,out,reads⟩
    exact ⟨C.size,C,mo,rb,out,le_rfl,fun i => reads _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
theorem emptyCircuit (A : Finset (W n)) (p : ℕ) : Has A Finset.univ p := by
  classical
  let S : W n := Finset.univ
  have zero : (fun _ : W n => false)∈L S := by simp [L,bank]
  refine ⟨⟨[],0⟩,by simp [Monotone2],by simp [NestedCover.ReadsBack],?_,Nat.zero_le _,?_⟩
  · change 0<(L S).length+0
    have := List.length_pos_of_mem zero; omega
  · intro i
    have hi : inv i∈L S := Finset.mem_toList.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hi
    refine ⟨j,by simpa [Circuit.size,L,S] using hj,?_⟩
    intro x _
    change ((L S).map (fun f => f x)).getD j false=inv i x
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,hj,eq]

theorem detects (A : Finset (W n)) :
    (∀S p,Has A S p ↔ S=Finset.univ) ↔ ∀i,flipPair A i := by
  classical
  let E : Finset (Fin n × Fin n) := ∅
  have cls (V : W n) : (∀ e∈E,e.1∈V ↔ e.2∈V) ↔ ∀i j : Fin n,id i=id j → (i∈V ↔ j∈V) := by simp [E]
  have th := (PEqualNP.GraphSeedSamples.criterion n n E id Function.surjective_id cls (Finset.univ.image inv)
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i))).1 A
  change preserves A E id (Finset.univ.image inv) ↔ tested A id at th
  have blockEq (i : Fin n) : block id i={i} := by ext j; simp [block]
  have cv (S : W n) : cover id S ↔ S=Finset.univ := by simp [cover,Finset.eq_univ_iff_forall]
  have test : tested A id ↔ ∀i,flipPair A i := by
    simp only [tested,blockEq,Finset.disjoint_singleton_right,Finset.union_singleton,flipPair,lowMem]
    constructor <;> intro H i <;> obtain ⟨x,h1,h2,h3⟩ := H i <;> exact ⟨x,h2,h1,h3⟩
  rw [←test,←th]
  constructor
  · intro h S
    rw [cv]; change fits A (L S) _ ↔ _
    rw [←budgetless]; exact ⟨fun ⟨p,hp⟩ => (h _ _).mp hp,fun eq => ⟨0,(h _ _).mpr eq⟩⟩
  · intro h S p
    constructor
    · intro hh; exact (cv _).mp ((h S).mp ((budgetless ..).mp ⟨p,hh⟩))
    · rintro rfl; exact emptyCircuit .. 
end PEqualNP.Outside.L_lib_1461_aux

namespace PEqualNP.Outside.L_lib_1461_aux
open scoped Classical
def Robust (d : ℕ) (row : Fin m → W n) := ∀lost : Finset (Fin m), lost.card≤d → ∀S p, Has (kept row lost) S p ↔ S=Finset.univ
theorem robust (row : Fin m → W n) (d : ℕ) : Robust d row ↔ ∀i,d+1≤pairs (freq row) i := by
  constructor
  · intro h i; apply (eraseIff row d i).mp; intro z small; exact (detects _).mp (h z small) i
  · intro h z small; apply (detects _).mpr; intro i; exact (eraseIff row d i).mpr (h i) z small
theorem banks (d m n : ℕ) : (∃row : Fin m → W n,Robust d row) ↔ ∃w : W n → ℕ,Good (d+1) m w := by
  constructor
  · rintro ⟨row,h⟩; exact ⟨_,allRows row,(robust row d).mp h⟩
  · rintro ⟨w,h⟩
    obtain ⟨row,eq⟩ := realize w h.1
    refine ⟨row,(robust row d).mpr ?_⟩
    simpa only [funext eq] using h.2
end PEqualNP.Outside.L_lib_1461_aux

namespace PEqualNP.Outside.L_lib_1461_aux
open PEqualNP.GraphSeedSamples PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
noncomputable def truth (P : Prop) := @decide P (Classical.propDecidable P)
theorem sameTruth (P : Prop) (d : Decidable P) : @decide P d=truth P := by unfold truth; congr 1
noncomputable def chooseF {α : Type*} (P : α → Prop) (A : Finset α) := @Finset.filter α P (fun _ => Classical.propDecidable _) A
theorem normFilter {α : Type*} (P : α → Prop) (d : DecidablePred P) (A : Finset α) : @Finset.filter α P d A=chooseF P A := by
  ext j; simp only [chooseF,Finset.mem_filter]
def inserted (i : Fin n) (A : W n) := insert i A
theorem sameInsert (d : DecidableEq (Fin n)) (i : Fin n) (A : W n) :
    @Insert.insert _ _ (@Finset.instInsert _ d) i A=inserted i A := by ext j; simp only [inserted,Finset.mem_insert]
theorem onRows (row : Fin m → W n) (lost : Finset (Fin m)) (S : W n) (p : ℕ) :
    Has (kept row lost) S p ↔ ∃ C : Circuit,Monotone2 C ∧ NestedCover.ReadsBack (L S).length C ∧
      C.output<(L S).length+C.size ∧ C.size≤p ∧ ∀i,∃j<(L S).length+C.size,∀z∉lost,
        (C.wires ((L S).map (fun g => g (row z)))).getD j false=inv i (row z) := by
  simp only [Has,kept,Finset.forall_mem_image,Finset.mem_sdiff,Finset.mem_univ,true_and]
end PEqualNP.Outside.L_lib_1461_aux
open PEqualNP.Outside.L_lib_1461_aux PEqualNP.GraphSeedSamples in
theorem PEqualNP.Outside.L_lib_1461 : ∀ (n d : Nat), 0 < n →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let D := d+1
  let keeps := fun (m : Nat) (row : Fin m → W) =>
    ∀ (lost : Finset (Fin m)), lost.card ≤ d → ∀ (S : W) (p : Nat),
      let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
      let neg := fun (i : Fin n) (x : W) => !(bit i x)
      let raw : Finset (W → Bool) := {fun _ => false, fun _ => true} ∪ Finset.univ.image bit
      let L := (raw ∪ S.image neg).toList
      (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
        C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ i : Fin n, ∃ j < L.length+C.size,
          ∀ k : Fin m, k ∉ lost → (C.wires (L.map (fun g => g (row k)))).getD j false = neg i (row k)) ↔
        S = Finset.univ
  let existsBank := fun m => ∃ row : Fin m → W, keeps m row
  (∀ (m : Nat) (row : Fin m → W),
    let w := fun x : W => (Finset.univ.filter (fun k => row k = x)).card
    keeps m row ↔ ∀ i : Fin n,
      D ≤ ∑ x ∈ (Finset.univ.filter (fun x : W => i ∉ x)), min (w x) (w (insert i x))) ∧
  (∀ m, existsBank m → 2*D ≤ m) ∧
  (existsBank (2*D) ↔ 2^(n-1) ∣ D) ∧
  (existsBank (2*D+1) ↔ 2^(n-1) ∣ D ∨ 2^(n-1) ∣ (D+1)) := by
  classical
  intro n d pos
  intro W' D' keeps' existsBank
  have eqKeep (m : ℕ) (row : Fin m → W n) : keeps' m row ↔ Robust d row := by
    unfold keeps' Robust
    apply forall_congr'; intro z
    apply imp_congr_right; intro _
    apply forall_congr'; intro S
    apply forall_congr'; intro p
    refine iff_congr ?_ Iff.rfl
    rw [onRows]
    dsimp only [W']
    generalize hl : Finset.toList _ = actual
    have eneg (i : Fin n) (x : W n) (h : Decidable (i∈x)) : (!(@decide (i∈x) h))=inv i x := by
      by_cases hit : i∈x <;> simp [hit,inv]
    have eb (i : Fin n) (h : ∀ x : W n,Decidable (i∈x)) : (fun x => @decide (i∈x) (h x))=bit i := by
      funext x; apply Bool.eq_iff_iff.mpr; simp [bit]
    have bt (i : Fin n) : bit i=(fun x : W n => truth (i∈x)) := by
      funext x; simp only [bit,sameTruth]
    have eq : actual=L S := by
      rw [←hl]
      unfold L
      congr 1
      ext f
      simp only [bank,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_image,Finset.image_empty,
        Finset.notMem_empty,or_false,Finset.mem_univ,true_and,eneg,eb]
      simp only [bt,sameTruth]
    rw [eq]
    simp only [eneg]
  have eqBank (m) : existsBank m ↔ ∃w : W n → ℕ,Good (d+1) m w := by
    simpa only [existsBank,eqKeep] using banks d m n
  refine ⟨?_,?_,?_,?_⟩
  · intro m row
    rw [eqKeep,robust]
    dsimp only [W',D',freq,pairs,lows]
    simp only [normFilter,sameInsert]
  · intro m hb
    obtain ⟨w,hw⟩ := (eqBank m).mp hb
    exact (necessary pos hw).1
  · exact (eqBank _).trans (exactBanks pos (d+1)).1
  · exact (eqBank _).trans (exactBanks pos (d+1)).2

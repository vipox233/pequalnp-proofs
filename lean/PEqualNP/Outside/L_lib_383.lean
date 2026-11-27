import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_383_aux
abbrev Word (n : Nat) := Fin n → Bool
abbrev State (d : Nat) := Word (d+1)
abbrev Payload (d : Nat) := Word d
abbrev Test (w : Nat) := Fin w → Word (w+1) → Bool

def splice {w : Nat} (a b : Word w) (i : Fin w) : Word (w+1) := fun j =>
  if h : i.val+j.val<w then a ⟨i.val+j.val,h⟩ else
    b ⟨i.val+j.val-w,by have := i.isLt;have := j.isLt;omega⟩

def SweepOk {w : Nat} (test : Test w) (a b : Word w) := ∀ i, test i (splice a b i)=true

lemma splice_head {w : Nat} (a b : Word w) (i : Fin w) : splice a b i 0=a i := by
  simp [splice,i.isLt]
lemma splice_last {w : Nat} (a b : Word w) (i : Fin w) :
    splice a b i (Fin.last w)=b i := by
  simp [splice,show ¬(i.val+w<w) by omega]

def tagOffset {d : Nat} (i : Fin (d+1)) : Fin ((d+1)+1) :=
  ⟨d+1-i.val,by omega⟩

lemma splice_tag {d : Nat} (a b : State d) (i : Fin (d+1)) :
    splice a b i (tagOffset i)=b 0 := by
  have e : i.val+(d+1-i.val)=d+1 := by have:=i.isLt;omega
  simp [splice,tagOffset,e]

def payload {d : Nat} (a : State d) : Payload d := fun j => a j.succ
def diff {d : Nat} (a h : Payload d) : Payload d := fun j => xor (a j) (h j)
def mask {d : Nat} (h : Payload d) (a : State d) : State d :=
  Fin.cases (a 0) (fun j => xor (a j.succ) (a 0 && h j))
def rise {d : Nat} (a : State d) : State d := Fin.cases true (payload a)

def maskTest {d : Nat} (h : Payload d) : Test (d+1) :=
  Fin.cases (fun p => p (Fin.last (d+1)) == p 0) (fun j p =>
    p (Fin.last (d+1)) == xor (p 0) (p (tagOffset j.succ) && h j))

lemma mask_ok {d : Nat} (h : Payload d) (a b : State d) :
    SweepOk (maskTest h) a b ↔ b=mask h a := by
  constructor
  · intro ok
    have tag : b 0=a 0 := by
      simpa [maskTest,splice_last,splice_head] using ok 0
    funext i
    refine Fin.cases (by simpa [mask] using tag) ?_ i
    intro j
    simpa [maskTest,splice_last,splice_head,splice_tag,mask,tag] using ok j.succ
  · rintro rfl i
    refine Fin.cases ?_ ?_ i
    · simp [maskTest,splice_last,splice_head,mask]
    · intro j
      simp [maskTest,splice_last,splice_head,splice_tag,mask]

def toggleTest {d : Nat} (h : Payload d) (A : Payload d → Payload d → Bool) : Test (d+1) :=
  Fin.cases (fun p =>
    if p (Fin.last (d+1)) == p 0 then true else
    if p 0 then false else A (fun j => p j.succ.castSucc) (diff (fun j => p j.succ.castSucc) h))
    (fun _ p => p (Fin.last (d+1)) == p 0)

lemma splice_payload {d : Nat} (a b : State d) (j : Fin d) :
    splice a b 0 j.succ.castSucc = a j.succ := by
  simp [splice]
  rfl

lemma toggle_proj {d : Nat} (h : Payload d) (i : Fin (d+1)) (p : Word ((d+1)+1)) :
    (∃ c : Bool, ∀ A, toggleTest h A i p=c) ∨
    ∃ u v, ∀ A, toggleTest h A i p=A u v := by
  refine Fin.cases ?_ (fun j=>Or.inl ⟨_,fun _ => rfl⟩) i
  simp only [toggleTest,Fin.cases_zero]
  split
  · exact Or.inl ⟨_,fun _=>rfl⟩
  · split
    · exact Or.inl ⟨_,fun _=>rfl⟩
    · exact Or.inr ⟨_,_,fun _=>rfl⟩

lemma toggle_ok {d : Nat} (h : Payload d) (A : Payload d → Payload d → Bool) (a b : State d) :
    SweepOk (toggleTest h A) a b ↔
      b=a ∨ (a 0=false ∧ A (payload a) (diff (payload a) h)=true ∧ b=rise a) := by
  have at0 : toggleTest h A 0 (splice a b 0)=
      (if b 0 == a 0 then true else if a 0 then false else A (payload a) (diff (payload a) h)) := by
    simp only [toggleTest,Fin.cases_zero,splice_last,splice_head,splice_payload]
    rfl
  have at1 (j : Fin d) : toggleTest h A j.succ (splice a b j.succ) = (b j.succ == a j.succ) := by
    simp [toggleTest,splice_last,splice_head]
  constructor
  · intro ok
    have pl (j : Fin d) : b j.succ=a j.succ := by simpa [at1] using ok j.succ
    have hd := ok 0
    rw [at0] at hd
    by_cases he : b 0=a 0
    · exact Or.inl (funext (fun i=>Fin.cases he pl i))
    · have e : a 0=false ∧ b 0=true ∧ A (payload a) (diff (payload a) h)=true := by
        cases ha : a 0 <;> cases hb : b 0 <;> simp_all
      exact Or.inr ⟨e.1,e.2.2,funext (fun i=>Fin.cases (by simpa [rise] using e.2.1)
        (fun j=>by simpa [rise,payload] using pl j) i)⟩
  · rintro (rfl|⟨ha,ht,rfl⟩) i
    · exact Fin.cases (by simp [at0]) (fun j=>by simp [at1]) i
    · exact Fin.cases (by simp [at0,rise,ha,ht]) (fun j=>by simp [at1,rise,payload]) i

lemma mask_twice {d : Nat} (h : Payload d) (a : State d) : mask h (mask h a)=a := by
  funext i
  refine Fin.cases (by simp [mask]) ?_ i
  intro j
  simp [mask]

lemma mask_off {d : Nat} (h : Payload d) {a : State d} (ha : a 0=false) : mask h a=a := by
  funext i; refine Fin.cases (by simp [mask]) (fun j=>by simp [mask,ha]) i

def switched {d : Nat} (h : Payload d) (a : State d) : State d :=
  Fin.cases true (diff (payload a) h)
lemma mask_rise {d : Nat} (a : State d) (h : Payload d) : mask h (rise a)=switched h a := by
  funext i;refine Fin.cases (by simp [mask,rise,switched]) (fun j=>by simp [mask,rise,switched,diff,payload]) i

end PEqualNP.Outside.L_lib_383_aux

namespace PEqualNP.Outside.L_lib_383_aux
open Classical

noncomputable def ways {w : Nat} : List (Test w) → Word w → Word w → Nat
  | [], a, b => if a=b then 1 else 0
  | t::ts,a,b => ∑ y, if SweepOk t a y then ways ts y b else 0

def tests {d : Nat} (A : Payload d → Payload d → Bool) (hs : List (Payload d)) : List (Test (d+1)) :=
  hs.flatMap (fun h => [maskTest h,toggleTest h A,maskTest h])

lemma len_tests {d : Nat} (A : Payload d → Payload d → Bool) (hs : List (Payload d)) :
    (tests A hs).length=3*hs.length := by
  induction hs with
  | nil => simp [tests]
  | cons h hs ih =>
    change (tests A hs).length+3=3*(hs.length+1)
    rw [ih];omega

private lemma applyMask {d : Nat} (h : Payload d) (fs : List (Test (d+1))) (a b : State d) :
    ways (maskTest h::fs) a b = ways fs (mask h a) b := by
  classical
  simp [ways,mask_ok]

private lemma applyToggle {d : Nat} (A : Payload d → Payload d → Bool) (h : Payload d)
    (fs : List (Test (d+1))) (a b : State d) :
    ways (toggleTest h A::fs) a b = ways fs a b +
      (if a 0=false ∧ A (payload a) (diff (payload a) h)=true then ways fs (rise a) b else 0) := by
  classical
  by_cases ho : a 0=false ∧ A (payload a) (diff (payload a) h)=true
  · have ne : a ≠ rise a := by
      intro he
      have := congrFun he 0
      simp [rise,ho.1] at this
    have point (y : State d) :
        (if SweepOk (toggleTest h A) a y then ways fs y b else 0) =
        (if y=a then ways fs y b else 0) + (if y=rise a then ways fs y b else 0) := by
      by_cases yh : y=a <;> by_cases yr : y=rise a <;> simp_all [toggle_ok]
    simp [ways,point,Finset.sum_add_distrib,ho]
  · have hnot (y) : SweepOk (toggleTest h A) a y ↔ y=a := by
      rw [toggle_ok]
      tauto
    simp [ways,hnot,ho]

lemma blockStep {d : Nat} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (h : Payload d) (a b : State d) :
    ways (tests A (h::hs)) a b = ways (tests A hs) a b +
      (if a 0=false ∧ A (payload a) (diff (payload a) h)=true then
        ways (tests A hs) (switched h a) b else 0) := by
  change ways (maskTest h :: toggleTest h A :: maskTest h :: tests A hs) a b = _
  rw [applyMask,applyToggle,applyMask,applyMask,mask_twice]
  by_cases ha : a 0=false
  · simp [mask_off h ha,mask_rise]
  · simp [mask,ha]

def hit {d : Nat} (A : Payload d → Payload d → Bool) (a b : State d) (h : Payload d) : Bool :=
  decide (a 0=false ∧ A (payload a) (diff (payload a) h)=true ∧ switched h a=b)

lemma ways_formula {d : Nat} (A : Payload d → Payload d → Bool) (hs : List (Payload d))
    (a b : State d) :
    ways (tests A hs) a b = (if a=b then 1 else 0) + (hs.filter (hit A a b)).length := by
  classical
  induction hs generalizing a with
  | nil => simp [tests,ways]
  | cons h hs ih =>
    rw [blockStep,ih,ih]
    have dead (k : Payload d) : hit A (switched h a) b k = false := by simp [hit,switched]
    have deadList : hs.filter (hit A (switched h a) b)=[] :=
      List.filter_eq_nil_iff.mpr (fun k _=>by simp [dead k])
    simp only [deadList,List.length_nil,Nat.add_zero]
    by_cases en : a 0=false ∧ A (payload a) (diff (payload a) h)=true
    · by_cases sw : switched h a=b
      · simp [hit,en.1,en.2,sw];omega
      · simp [hit,en.1,en.2,sw]
    · have hnot : hit A a b h=false := by simp [hit]; tauto
      simp [hnot,en]

noncomputable def keyList (d : Nat) : List (Payload d) :=
  (List.finRange (Fintype.card (Payload d))).map (Fintype.equivFin (Payload d)).symm

lemma keylen (d : Nat) : (keyList d).length=2^d := by simp [keyList]

lemma keyAll {d : Nat} (h : Payload d) : h ∈ keyList d := by
  apply List.mem_map.mpr
  exact ⟨Fintype.equivFin _ h,List.mem_finRange _,Equiv.symm_apply_apply _ _⟩

lemma keyNodup (d : Nat) : (keyList d).Nodup := by
  exact (List.nodup_finRange _).map (Equiv.injective _)

private lemma hit_iff {d : Nat} (A : Payload d → Payload d → Bool) (a b : State d) (h : Payload d) :
    hit A a b h=true ↔ a 0=false ∧ b 0=true ∧ A (payload a) (payload b)=true ∧
      h=diff (payload a) (payload b) := by
  simp only [hit,decide_eq_true_eq]
  constructor
  · rintro ⟨ha,he,sw⟩
    have pb : payload b = diff (payload a) h := by rw [←sw];rfl
    refine ⟨ha,by rw [←sw];rfl,pb ▸ he,?_⟩
    funext j
    simp [pb,diff]
  · rintro ⟨ha,hb,he,rfl⟩
    have e : diff (payload a) (diff (payload a) (payload b))=payload b := by
      funext j;simp [diff]
    exact ⟨ha,by rwa [e],funext (fun i=>Fin.cases (by simpa [switched] using hb.symm)
      (fun j=>by simp [switched,e,payload]) i)⟩

lemma net_result {d : Nat} (A : Payload d → Payload d → Bool) (a b : State d) :
    ways (tests A (keyList d)) a b = (if a=b then 1 else 0) +
      (if a 0=false ∧ b 0=true ∧ A (payload a) (payload b)=true then 1 else 0) := by
  classical
  rw [ways_formula]
  congr 1
  by_cases en : a 0=false ∧ b 0=true ∧ A (payload a) (payload b)=true
  · simp only [en,ite_true]
    let h := diff (payload a) (payload b)
    have only : (keyList d).filter (hit A a b) = [h] := by
      have nodup := (keyNodup d).filter (hit A a b)
      have mem (q) : q ∈ (keyList d).filter (hit A a b) ↔ q=h := by
        simp [List.mem_filter,hit_iff,keyAll,en.1,en.2.1,en.2.2,h]
      cases he : (keyList d).filter (hit A a b) with
      | nil => have := (mem h).mpr rfl; simp [he] at this
      | cons q qs =>
        have eu := (mem q).mp (by simp [he])
        rw [he,List.nodup_cons] at nodup
        cases qt : qs with
        | nil => simp [eu]
        | cons p ps =>
          have ep := (mem p).mp (by simp [he,qt])
          apply False.elim (nodup.1 (by simp [eu,←ep,qt]))
    simp [only]
  · have no (q : Payload d) : hit A a b q=false := by
      cases e : hit A a b q with
      | false => rfl
      | true =>
        obtain ⟨ha,hb,ht,_⟩ := (hit_iff ..).mp e
        exact False.elim (en ⟨ha,hb,ht⟩)
    simp [en,no]

end PEqualNP.Outside.L_lib_383_aux

namespace PEqualNP.Outside.L_lib_383_aux
open Classical

def GridOk {w : Nat} (fs : List (Test w)) (x : Fin (fs.length+1)→Word w) (a b : Word w) : Prop :=
  x 0=a ∧ x (Fin.last fs.length)=b ∧
    ∀ t : Fin fs.length, SweepOk fs[t.val] (x t.castSucc) (x t.succ)

private lemma gridNil {w} (x : Fin 1 → Word w) (a b : Word w) :
    GridOk [] x a b ↔ x 0=a ∧ a=b := by
  simp [GridOk,Fin.last_zero];rintro rfl;rfl

private lemma gridCons {w} (f : Test w) (fs : List (Test w))
    (a b s : Word w) (x : Fin (fs.length+1) → Word w) :
    GridOk (f::fs) (Fin.cons s x) a b ↔
      s=a ∧ SweepOk f s (x 0) ∧ GridOk fs x (x 0) b := by
  change (s=a ∧ x (Fin.last fs.length)=b ∧
    ∀ j : Fin (fs.length+1), SweepOk (f::fs)[j.val] (Fin.cons (α:=fun _=>Word w) s x j.castSucc) (x j))
      ↔ s=a ∧ SweepOk f s (x 0) ∧ GridOk fs x (x 0) b
  constructor
  · rintro ⟨rfl,e,h⟩
    exact ⟨rfl,h 0,rfl,e,fun i => h i.succ⟩
  · rintro ⟨rfl,t,_,e,h⟩
    exact ⟨rfl,e,fun j => Fin.cases t (fun i=>h i) j⟩

private lemma sumCons {w p : Nat} (f : (Fin (p+1) → Word w) → Nat) :
    ∑ x, f x = ∑ s : Word w, ∑ x : Fin p → Word w, f (Fin.cons (α:=fun _ => Word w) s x) := by
  have h := (Fin.consEquiv (n:=p) (fun _ => Word w)).sum_comp f
  rw [←h,Fintype.sum_prod_type]
  rfl

lemma count_grid {w : Nat} (fs : List (Test w)) (a b : Word w) :
    (∑ x : Fin (fs.length+1) → Word w, if GridOk fs x a b then 1 else 0) = ways fs a b := by
  classical
  induction fs generalizing a with
  | nil =>
    rw [sumCons]
    by_cases h : a=b <;> simp [gridNil,ways,h]
  | cons f fs ih =>
    rw [sumCons]
    simp only [gridCons]
    have hs (s) : (∑ x : Fin (fs.length+1) → Word w,
        if s=a ∧ SweepOk f s (x 0) ∧ GridOk fs x (x 0) b then 1 else 0) =
        if s=a then (∑ y, if SweepOk f a y then ways fs y b else 0) else 0 := by
      by_cases eq : s=a
      · subst s
        simp only [true_and,ite_true]
        simp_rw [←ih]
        have distribute (y : Word w) :
            (if SweepOk f a y then ∑ x, if GridOk fs x y b then 1 else 0 else 0 : Nat) =
            ∑ x, if SweepOk f a y then (if GridOk fs x y b then 1 else 0) else 0 := by
          by_cases p : SweepOk f a y <;> simp [p]
        simp_rw [distribute]
        rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)]
        apply Finset.sum_congr rfl
        intro x _
        have restrict (y : Word w) (neq : y ≠ x 0) : ¬GridOk fs x y b := fun h=>neq h.1.symm
        rw [Finset.sum_eq_single (x 0)]
        · split_ifs <;> simp_all
        · intro z _ ne
          simp [restrict z ne]
        · simp
      · simp [eq]
    exact (Finset.sum_congr rfl (fun s _=>hs s)).trans (by simp [ways])

def linearPos {m w : Nat} (i : Fin m) (j : Fin w) : Fin (m*w) :=
  ⟨i.val*w+j.val,by
    have := Nat.mul_le_mul_right w (show i.val+1≤m from i.isLt)
    rw [Nat.add_mul,Nat.one_mul] at this
    have := j.isLt;omega⟩

def regroup {m w P : Nat} (hw : 0<w) (eq : P=m*w) : (Word P) ≃ (Fin m→Word w) where
  toFun x i j := x ⟨(linearPos i j).val,eq ▸ (linearPos i j).isLt⟩
  invFun y i := y ⟨i.val/w,(Nat.div_lt_iff_lt_mul hw).mpr (eq ▸ i.isLt)⟩
    ⟨i.val % w,Nat.mod_lt _ hw⟩
  left_inv x := by
    funext j;apply congrArg x;apply Fin.ext;change j.val/w*w+j.val % w=j.val
    simpa [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div j.val w
  right_inv f := by
    funext i j
    change f ⟨(i.val*w+j.val)/w,_⟩ ⟨(i.val*w+j.val)%w,_⟩=f i j
    congr 1
    · apply Fin.ext;simp [Nat.add_comm _ j.val,Nat.add_mul_div_right,Nat.div_eq_of_lt j.isLt,hw]
    · apply Fin.ext;simp [Nat.mod_eq_of_lt j.isLt]

end PEqualNP.Outside.L_lib_383_aux

namespace PEqualNP.Outside.L_lib_383_aux
open Classical

def cutGrid {w m L : Nat} (eq : L=m*(w+1)) : (Word (L+w+1)) ≃ (Fin (m+1) → Word (w+1)) :=
  regroup (Nat.succ_pos _) (by rw [Nat.succ_mul,←eq];omega)

lemma read_at {w m L : Nat} (eq : L=m*(w+1)) (x : Word (L+w+1)) (q : Fin (m+1)) (j : Fin (w+1)) :
    x (Fin.ofNat (L+w+1) (q.val*(w+1)+j.val)) = cutGrid eq x q j := by
  apply congrArg x
  apply Fin.ext
  have lim := (linearPos q j).isLt
  change q.val*(w+1)+j.val < (m+1)*(w+1) at lim
  rw [Nat.succ_mul,←eq] at lim
  exact Nat.mod_eq_of_lt lim

def getPhase {w L : Nat} (fs : List (Test (w+1))) (eq : L=fs.length*(w+1)) (i : Fin L) : Word ((w+1)+1)→Bool :=
  (fs[ i.val/(w+1) ]'(by apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr; exact eq ▸ i.isLt))
    ⟨i.val % (w+1),Nat.mod_lt _ (Nat.succ_pos _)⟩

def rowIndex {m w L : Nat} (eq : L=m*(w+1)) (t : Fin m) (i : Fin (w+1)) : Fin L :=
  ⟨(linearPos t i).val,eq ▸ (linearPos t i).isLt⟩

lemma rowPhase {w L : Nat} (fs : List (Test (w+1))) (eq : L=fs.length*(w+1))
    (t : Fin fs.length) (i : Fin (w+1)) : getPhase fs eq (rowIndex eq t i)=fs[t.val] i := by
  have e : (t.val*(w+1)+i.val)/(w+1)=t.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.succ_pos _),Nat.div_eq_of_lt i.isLt,Nat.zero_add]
  unfold getPhase
  simp only [rowIndex,linearPos,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt i.isLt]
  exact congrFun (getElem_congr (c:=fs) rfl e (by omega)) i

lemma rowSplice {w m L : Nat} (eq : L=m*(w+1)) (x : Word (L+w+1)) (t : Fin m) (i : Fin (w+1)) :
    (fun j : Fin ((w+1)+1) => x (Fin.ofNat (L+w+1) ((rowIndex eq t i).val+j.val))) =
    splice (cutGrid eq x t.castSucc) (cutGrid eq x t.succ) i := by
  funext j
  unfold splice
  split
  · rename_i h
    rw [←read_at]; congr 2
    change t.val*(w+1)+i.val+j.val=t.val*(w+1)+(i.val+j.val)
    omega
  · rename_i h
    rw [←read_at];congr 2
    change t.val*(w+1)+i.val+j.val=(t.val+1)*(w+1)+(i.val+j.val-(w+1))
    rw [Nat.succ_mul];omega

def physOk {w L} (fs : List (Test (w+1))) (eq : L=fs.length*(w+1))
    (a b : Word (w+1)) (x : Word (L+w+1)) : Prop :=
  (∀ j : Fin (w+1), x (Fin.ofNat (L+w+1) j.val)=a j ∧ x (Fin.ofNat (L+w+1) (L+j.val))=b j) ∧
  ∀ i : Fin L, getPhase fs eq i (fun j=>x (Fin.ofNat (L+w+1) (i.val+j.val)))=true

lemma phys_grid {w L} (fs : List (Test (w+1))) (eq : L=fs.length*(w+1))
    (a b : Word (w+1)) (x : Word (L+w+1)) :
    physOk fs eq a b x ↔ GridOk fs (cutGrid eq x) a b := by
  have start (k : Fin (w+1)) : x (Fin.ofNat (L+w+1) k.val)=cutGrid eq x 0 k := by
    simpa using read_at eq x 0 k
  have fin (k : Fin (w+1)) : x (Fin.ofNat (L+w+1) (L+k.val))=cutGrid eq x (Fin.last fs.length) k := by
    simpa only [Fin.val_last,←eq] using read_at eq x (Fin.last fs.length) k
  constructor
  · rintro ⟨ends,all⟩
    refine ⟨funext (fun k=>(start k).symm.trans (ends k).1),funext (fun k=>(fin k).symm.trans (ends k).2),?_⟩
    intro t i
    simpa only [rowSplice,rowPhase] using all (rowIndex eq t i)
  · rintro ⟨a0,b0,h⟩
    refine ⟨fun k=>⟨(start k).trans (congrFun a0 k),(fin k).trans (congrFun b0 k)⟩,?_⟩
    intro j
    let t : Fin fs.length := ⟨j.val/(w+1),(Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr (eq ▸ j.isLt)⟩
    let i : Fin (w+1) := ⟨j.val % (w+1),Nat.mod_lt _ (Nat.succ_pos _)⟩
    have atRow : j=rowIndex eq t i := by
      apply Fin.ext
      change j.val=j.val/(w+1)*(w+1)+j.val % (w+1)
      simpa [Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div j.val (w+1)).symm
    rw [atRow,rowPhase,rowSplice]
    exact h t i

theorem phys_count {w L} (fs : List (Test (w+1))) (eq : L=fs.length*(w+1)) (a b : Word (w+1)) :
    (Finset.univ.filter (physOk fs eq a b)).card = ways fs a b := by
  classical
  calc
    _ = ∑ x, if physOk fs eq a b x then 1 else 0 := by rw [Finset.card_filter]
    _ = ∑ x, if GridOk fs (cutGrid eq x) a b then 1 else 0 := by simp_rw [phys_grid]
    _ = ∑ g, if GridOk fs g a b then 1 else 0 :=
      (cutGrid eq).sum_comp (fun g=>if GridOk fs g a b then 1 else 0)
    _ = _ := count_grid fs a b

end PEqualNP.Outside.L_lib_383_aux

namespace PEqualNP.Outside.L_lib_383_aux
abbrev Input (d : Nat) := Payload d → Payload d → Bool

def templates {d} (hs : List (Payload d)) : List (Input d → Test (d+1)) :=
  hs.flatMap (fun h=>[fun _=>maskTest h,fun A=>toggleTest h A,fun _=>maskTest h])
lemma templateMap {d} (hs : List (Payload d)) (A : Input d) :
    (templates hs).map (fun f=>f A)=tests A hs := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    change (maskTest h :: toggleTest h A :: maskTest h :: (templates hs).map (fun f=>f A))=
      maskTest h :: toggleTest h A :: maskTest h :: tests A hs
    rw [ih]

lemma templateProjection {d} (hs : List (Payload d)) {f : Input d → Test (d+1)} (mem : f∈templates hs)
    (i : Fin (d+1)) (p : Word ((d+1)+1)) :
    (∃ c : Bool, ∀ A, f A i p=c) ∨ ∃ u v, ∀ A, f A i p=A u v := by
  unfold templates at mem
  obtain ⟨h,_,e⟩ := List.mem_flatMap.mp mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at e
  rcases e with rfl|rfl|rfl
  · exact Or.inl ⟨_,fun _=>rfl⟩
  · exact toggle_proj h i p
  · exact Or.inl ⟨_,fun _=>rfl⟩

abbrev rowCount (d : Nat) := 3*(d+1)*2^d

lemma lengthRows (d : Nat) (A : Input d) :
    rowCount d=(tests A (keyList d)).length*(d+1) := by
  rw [len_tests,keylen];unfold rowCount;ring

noncomputable def enc (d : Nat) (A : Input d) (i : Fin (rowCount d)) : Word ((d+1)+1)→Bool :=
  getPhase (tests A (keyList d)) (lengthRows d A) i

lemma encProjection (d : Nat) (i : Fin (rowCount d)) (p : Word ((d+1)+1)) :
    (∃ c : Bool, ∀ A, enc d A i p=c) ∨ ∃ u v, ∀ A, enc d A i p=A u v := by
  let T := templates (keyList d)
  have len (A : Input d) : (tests A (keyList d)).length=T.length := by
    rw [←templateMap,List.length_map]
  have hi : i.val/(d+1)<T.length := by
    rw [←len (fun _ _=>false)]
    exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr ((lengthRows d _) ▸ i.isLt)
  let f := T[i.val/(d+1)]
  let j : Fin (d+1) := ⟨i.val % (d+1),Nat.mod_lt _ (by omega)⟩
  have eq (A : Input d) : enc d A i p=f A j p := by
    unfold enc getPhase f T j
    rw [getElem_congr_coll (templateMap (keyList d) A).symm,List.getElem_map]
  simp_rw [eq]
  exact templateProjection (keyList d) (List.getElem_mem hi) j p

end PEqualNP.Outside.L_lib_383_aux


open PEqualNP.Outside.L_lib_383_aux in
theorem PEqualNP.Outside.L_lib_383 : ∀ d : ℕ,
  let w := d + 1
  let D := Fin d → Bool
  let L := 3 * w * 2 ^ d
  ∃ enc : (D → D → Bool) → Fin L → (Fin (w + 1) → Bool) → Bool,
    (∀ row pat, (∃ c : Bool, ∀ M, enc M row pat = c) ∨
      ∃ u v : D, ∀ M, enc M row pat = M u v) ∧
    ∀ (A : D → D → Bool) (a b : Fin w → Bool),
      let ok := fun (x : Fin (L + w) → Bool) =>
        (∀ k : Fin w, x (Fin.ofNat (L + d + 1) k.val) = a k ∧
          x (Fin.ofNat (L + d + 1) (L + k.val)) = b k) ∧
        ∀ i : Fin L, enc A i (fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val))) = true
      (Finset.univ.filter ok).card =
        (if a = b then 1 else 0) +
        (if a 0 = false ∧ b 0 = true ∧ A (fun ia => a ia.succ) (fun ib => b ib.succ) = true
          then 1 else 0) := by
  intro d
  dsimp only
  refine ⟨enc d,encProjection d,?_⟩
  intro A a b
  apply Eq.trans _ ((phys_count (tests A (keyList d)) (lengthRows d A) a b).trans (net_result A a b))
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rfl

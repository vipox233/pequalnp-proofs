import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_392_aux


namespace Lib383
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

end Lib383

namespace Lib383
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
  · simp only [en]
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

end Lib383

namespace Lib383
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

end Lib383

namespace Lib383
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

end Lib383

namespace Lib383
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

end Lib383


open Lib383 in
private theorem lib383_spec : ∀ d : ℕ,
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


open Lib383

private lemma tests_getElem {d : Nat} (A : Input d) (hs : List (Payload d))
    (m : Nat) (hm : m < hs.length) :
    (tests A hs)[3 * m]'(by rw [len_tests]; omega) = maskTest hs[m] ∧
    (tests A hs)[3 * m + 1]'(by rw [len_tests]; omega) = toggleTest hs[m] A ∧
    (tests A hs)[3 * m + 2]'(by rw [len_tests]; omega) = maskTest hs[m] := by
  induction hs generalizing m with
  | nil => simp at hm
  | cons h hs ih =>
    cases m with
    | zero => simp [tests]
    | succ m =>
      have hm' : m < hs.length := by simp at hm; omega
      have hih := ih m hm'
      have hcons : tests A (h :: hs) = maskTest h :: toggleTest h A :: maskTest h :: tests A hs := rfl
      refine ⟨?_, ?_, ?_⟩
      · have e : 3 * (m + 1) = (3 * m) + 3 := by omega
        simpa [hcons, e] using hih.1
      · have e : 3 * (m + 1) + 1 = (3 * m + 1) + 3 := by omega
        simpa [hcons, e] using hih.2.1
      · have e : 3 * (m + 1) + 2 = (3 * m + 2) + 3 := by omega
        simpa [hcons, e] using hih.2.2

private def copyPat {w : Nat} (pat : Fin (w + 1) → Bool) : Bool :=
  pat (Fin.last w) == pat 0

private def mkStart {d : Nat} (u : Payload d) : State d :=
  Fin.cases false u

private def mkEnd {d : Nat} (v : Payload d) : State d :=
  Fin.cases true v

private def rotSeed (d padding : Nat) (u : Payload d) (r : Fin (d + 1)) : Bool :=
  mkStart u ⟨(r.val + ((d + 1) - padding % (d + 1))) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

private noncomputable def encFull (d padding : Nat) (A : Input d)
    (i : Fin (padding + 3 * (d + 1) * 2 ^ d)) (pat : Fin (d + 1 + 1) → Bool) : Bool :=
  if hlt : i.val < padding then
    copyPat pat
  else
    let r : Fin (rowCount d) := ⟨i.val - padding, by unfold rowCount; omega⟩
    if i.val = padding then
      (pat 0 == false) && enc d A r pat
    else
      enc d A r pat

private def probeFull (d padding : Nat) (u : Payload d) (targetMask : Payload d → Bool)
    (r : Fin (d + 1)) (pat : Fin (d + 1 + 1) → Bool) : Bool :=
  let okInit := pat (Fin.last (d + 1)) == rotSeed d padding u r
  if r.val = 0 then
    okInit && pat 0 && targetMask (fun j : Fin d => pat j.succ.castSucc)
  else
    okInit

private lemma enc_at_block {d : Nat} (A : Input d) (s : Nat) (hs : s < 3 * 2 ^ d)
    (j : Fin (d + 1)) :
    let idx : Fin (rowCount d) := ⟨s * (d + 1) + j.val, by
      have h1 : (s + 1) * (d + 1) ≤ (3 * 2 ^ d) * (d + 1) := Nat.mul_le_mul_right (d + 1) hs
      rw [Nat.succ_mul] at h1
      have h2 : (3 * 2 ^ d) * (d + 1) = rowCount d := by unfold rowCount; ring
      omega⟩
    enc d A idx =
      ((tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs)) j := by
  intro idx
  unfold enc
  have hs' : s < (tests A (keyList d)).length := by rw [len_tests, keylen]; exact hs
  have heq : idx = rowIndex (lengthRows d A) ⟨s, hs'⟩ j := by
    apply Fin.ext; rfl
  rw [heq, rowPhase]

private lemma maskTest_det {d : Nat} (h : Payload d) (j : Fin (d + 1))
    (p1 p2 : Word ((d + 1) + 1))
    (hpre : ∀ a : Fin (d + 1), p1 a.castSucc = p2 a.castSucc)
    (h1 : maskTest h j p1 = true) (h2 : maskTest h j p2 = true) :
    p1 (Fin.last (d + 1)) = p2 (Fin.last (d + 1)) := by
  refine Fin.cases ?_ ?_ j h1 h2
  · intro h1 h2
    simp only [maskTest, Fin.cases_zero, beq_iff_eq] at h1 h2
    have h0 := hpre 0
    simp only [Fin.castSucc_zero] at h0
    rw [h1, h2, h0]
  · intro k h1 h2
    simp only [maskTest, Fin.cases_succ, beq_iff_eq] at h1 h2
    have h0 := hpre 0
    simp only [Fin.castSucc_zero] at h0
    have htag_lt : (tagOffset k.succ).val < d + 1 := by
      have := k.isLt
      simp only [tagOffset, Fin.val_succ]; omega
    have htag := hpre ⟨(tagOffset k.succ).val, htag_lt⟩
    have htag_eq : (⟨(tagOffset k.succ).val, htag_lt⟩ : Fin (d + 1)).castSucc = tagOffset k.succ := by
      apply Fin.ext; rfl
    rw [htag_eq] at htag
    rw [h1, h2, h0, htag]

private lemma toggleTest_succ_det {d : Nat} (h : Payload d) (A : Input d) (k : Fin d)
    (p1 p2 : Word ((d + 1) + 1))
    (hpre : ∀ a : Fin (d + 1), p1 a.castSucc = p2 a.castSucc)
    (h1 : toggleTest h A k.succ p1 = true) (h2 : toggleTest h A k.succ p2 = true) :
    p1 (Fin.last (d + 1)) = p2 (Fin.last (d + 1)) := by
  simp only [toggleTest, Fin.cases_succ, beq_iff_eq] at h1 h2
  have h0 := hpre 0
  simp only [Fin.castSucc_zero] at h0
  rw [h1, h2, h0]

private lemma toggleTest_zero_true {d : Nat} (h : Payload d) (A : Input d)
    (p : Word ((d + 1) + 1))
    (hp0 : p 0 = true) (hok : toggleTest h A 0 p = true) :
    p (Fin.last (d + 1)) = true := by
  simp only [toggleTest, Fin.cases_zero, hp0] at hok
  cases hv : p (Fin.last (d + 1)) <;> simp [hv] at hok ⊢

private lemma toggleTest_zero_switch {d : Nat} (h : Payload d) (A : Input d)
    (p : Word ((d + 1) + 1))
    (hp0 : p 0 = false) (hlast : p (Fin.last (d + 1)) = true)
    (hok : toggleTest h A 0 p = true) :
    A (fun j => p j.succ.castSucc) (diff (fun j => p j.succ.castSucc) h) = true := by
  simp only [toggleTest, Fin.cases_zero, hp0, hlast] at hok
  simpa using hok

private lemma maskTest_zero_eq {d : Nat} (h : Payload d) (p : Word ((d + 1) + 1))
    (hok : maskTest h 0 p = true) :
    p (Fin.last (d + 1)) = p 0 := by
  simpa [maskTest] using hok

private lemma copy_periodic {w m len : Nat} (hw : 0 < w) (hm : m + w ≤ len)
    (f : Fin len → Bool)
    (hcopy : ∀ i : Nat, (hi : i < m) → f ⟨i + w, by omega⟩ = f ⟨i, by omega⟩) :
    ∀ t : Nat, (ht : t < m + w) → f ⟨t, by omega⟩ = f ⟨t % w, by
      have := Nat.mod_lt t hw
      omega⟩ := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    by_cases htw : t < w
    · congr 1; apply Fin.ext; dsimp only; exact (Nat.mod_eq_of_lt htw).symm
    · have h1 := hcopy (t - w) (by omega)
      have he1 : t - w + w = t := by omega
      simp only [he1] at h1
      rw [h1, ih (t - w) (by omega) (by omega)]
      congr 1; apply Fin.ext; dsimp only
      have he2 : t = (t - w) + w := by omega
      conv_rhs => rw [he2]
      rw [Nat.add_mod_right]

private lemma diff_invol {d : Nat} (u h : Payload d) : diff u (diff u h) = h := by
  funext j; simp [diff]

private lemma diff_inj {d : Nat} (u h1 h2 : Payload d) (heq : diff u h1 = diff u h2) : h1 = h2 := by
  have := congrArg (diff u) heq
  rwa [diff_invol, diff_invol] at this

private lemma getElem_eq_of_eq {α : Type*} (l : List α) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (he : i = j) :
    l[i]'hi = l[j]'hj := by
  subst he; rfl

private lemma find?_finRange_lt {N : Nat} (f : Fin N → Bool) (m m' : Fin N)
    (hf : (List.finRange N).find? f = some m) (hlt : m'.val < m.val) :
    f m' = false := by
  rcases List.find?_eq_some_iff_append.mp hf with ⟨_, xs, ys, heq, hxs⟩
  have hlen : xs.length = m.val := by
    have h1 : (List.finRange N)[xs.length]'(by rw [heq]; simp) = m := by simp [heq]
    have h2 : ((List.finRange N)[xs.length]'(by rw [heq]; simp)).val = xs.length := by simp
    rw [h1] at h2; exact h2.symm
  have hmem : m' ∈ xs := by
    have hlt_x : m'.val < xs.length := by omega
    have h1 : (List.finRange N)[m'.val]'(by simp) = xs[m'.val]'hlt_x := by
      simp [heq, List.getElem_append_left hlt_x]
    have h2 : (List.finRange N)[m'.val]'(by simp) = m' := by apply Fin.ext; simp
    rw [h2] at h1
    rw [h1]
    exact List.getElem_mem hlt_x
  simpa using hxs m' hmem

private theorem solve_392 (d padding : Nat) :
    let w := d + 1
    let D := 2 ^ d
    let Idx := Fin d → Bool
    let L := padding + 3 * w * D
    let n := L + d + 1
    let pos := fun coord : Nat => Fin.ofNat (L + d + 1) coord
    let Part := fun len : Nat => Fin len → (Fin (w + 1) → Bool) → Bool
    ∃ (encF : (Idx → Idx → Bool) → Part L) (probeF : Idx → (Idx → Bool) → Part w),
      ∀ A : Idx → Idx → Bool,
        let weight := ((Finset.univ : Finset (Idx × Idx)).filter
          (fun e => A e.1 e.2 = true)).card
        let passes := fun (word : Fin n → Bool) (h : Nat) =>
          ∀ i : Fin L, i.val < h → encF A i (fun j => word (pos (i.val + j.val))) = true
        (∀ h ≤ L,
          (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => passes x h)).image
            (fun base => fun t : Fin (w + h) => base (pos t.val))).card ≤
            (if h ≤ padding then 2 * D else D + weight)) ∧
        ∀ (u : Idx) (targetMask : Idx → Bool),
          ((Finset.univ : Finset (Fin n → Bool)).filter (fun y =>
            passes y L ∧ ∀ r : Fin w, probeF u targetMask r
              (fun a => y (pos (L + r.val + a.val))) = true)).card =
            ((Finset.univ : Finset Idx).filter
              (fun v => A u v = true ∧ targetMask v = true)).card := by
  intro w D Idx L n pos Part
  refine ⟨encFull d padding, probeFull d padding, ?_⟩
  intro A weight passes
  have hw_pos : 0 < w := Nat.succ_pos d
  have hpos_lt : ∀ (k : Nat) (hk : k < n), pos k = ⟨k, hk⟩ := by
    intro k hk
    apply Fin.ext
    simp only [pos, Fin.val_ofNat]
    exact Nat.mod_eq_of_lt hk
  constructor
  · intro h hhL
    let imgSet := ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => passes x h)).image
      (fun base => fun t : Fin (w + h) => base (pos t.val))
    change imgSet.card ≤ if h ≤ padding then 2 * D else D + weight
    have hpref_pass : ∀ p ∈ imgSet, ∀ i : Fin L, (hi : i.val < h) →
        encFull d padding A i (fun j : Fin (w + 1) => p ⟨i.val + j.val, by omega⟩) = true := by
      intro p hp i hi
      rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx i hi
    by_cases hhp : h ≤ padding
    · simp only [hhp, ↓reduceIte]
      have hcard_w : (Finset.univ : Finset (Fin w → Bool)).card = 2 * D := by
        simp [w, D, Nat.pow_succ, Nat.mul_comm]
      rw [← hcard_w]
      refine Finset.card_le_card_of_injOn (fun p => fun k : Fin w => p ⟨k.val, by omega⟩)
        (fun _ _ => Finset.mem_univ _) ?_
      intro p1 hp1 p2 hp2 heq
      have hcp : ∀ p ∈ imgSet, ∀ t : Nat, (ht : t < h + w) →
          p ⟨t, by omega⟩ = p ⟨t % w, by have := Nat.mod_lt t hw_pos; omega⟩ := by
        intro p hp
        refine copy_periodic hw_pos (show h + w ≤ w + h by omega) p ?_
        intro i hi
        have hrow := hpref_pass p hp ⟨i, by omega⟩ hi
        have hi_lt : i < padding := by omega
        simp only [encFull, hi_lt, ↓reduceDIte, copyPat, beq_iff_eq, Fin.val_zero, Nat.add_zero, Fin.val_last] at hrow
        exact hrow
      funext t
      have ht' : t.val < h + w := by omega
      rw [hcp p1 hp1 t.val ht', hcp p2 hp2 t.val ht']
      exact congrFun heq ⟨t.val % w, Nat.mod_lt t.val hw_pos⟩
    · simp only [hhp, ↓reduceIte]
      let targetSet : Finset (Sum Idx (Idx × Idx)) :=
        (Finset.univ : Finset Idx).image Sum.inl ∪
        ((Finset.univ : Finset (Idx × Idx)).filter (fun e => A e.1 e.2 = true)).image Sum.inr
      have htarget_card : targetSet.card ≤ D + weight := by
        calc targetSet.card
            ≤ ((Finset.univ : Finset Idx).image Sum.inl).card +
              (((Finset.univ : Finset (Idx × Idx)).filter (fun e => A e.1 e.2 = true)).image Sum.inr).card :=
                Finset.card_union_le _ _
          _ ≤ (Finset.univ : Finset Idx).card +
              ((Finset.univ : Finset (Idx × Idx)).filter (fun e => A e.1 e.2 = true)).card :=
                Nat.add_le_add Finset.card_image_le Finset.card_image_le
          _ = D + weight := by
                have hc : (Finset.univ : Finset Idx).card = D := by simp [Idx, D]
                rw [hc]
      refine le_trans ?_ htarget_card
      let uOf (p : Fin (w + h) → Bool) : Idx :=
        fun j : Fin d => p ⟨padding + j.succ.val, by omega⟩
      let isSw (p : Fin (w + h) → Bool) (m : Fin D) : Bool :=
        if hlt : (3 * m.val + 1) * w < h - padding then
          p ⟨padding + (3 * m.val + 1) * w + w, by omega⟩
        else false
      let firstSw (p : Fin (w + h) → Bool) : Option (Fin D) :=
        (List.finRange D).find? (isSw p)
      let label (p : Fin (w + h) → Bool) : Sum Idx (Idx × Idx) :=
        match firstSw p with
        | none => Sum.inl (uOf p)
        | some m =>
          let hm_key : m.val < (keyList d).length := by rw [keylen]; exact m.isLt
          Sum.inr (uOf p, diff (uOf p) (keyList d)[m.val])
      have hpad0 : ∀ p ∈ imgSet, p ⟨padding, by omega⟩ = false := by
        intro p hp
        have hrow := hpref_pass p hp ⟨padding, by
          have : 0 < 3 * w * D := by dsimp [w, D]; positivity
          omega⟩ (by dsimp; omega)
        simp only [encFull, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
          Fin.val_zero, Nat.add_zero] at hrow
        exact hrow.1
      have henc_row : ∀ p ∈ imgSet, ∀ r : Nat, (hr : r < h - padding) →
          enc d A ⟨r, by unfold rowCount; dsimp [L, w, D] at hhL; omega⟩
            (fun j : Fin (w + 1) => p ⟨padding + r + j.val, by omega⟩) = true := by
        intro p hp r hr
        have hrow := hpref_pass p hp ⟨padding + r, by omega⟩ (by dsimp; omega)
        have hnot : ¬ padding + r < padding := by omega
        simp only [encFull, hnot, ↓reduceDIte, Nat.add_sub_cancel_left] at hrow
        by_cases hr0 : padding + r = padding
        · have hrz : r = 0 := by omega
          subst hrz
          simp only [Nat.add_zero, ↓reduceIte, Bool.and_eq_true] at hrow ⊢
          exact hrow.2
        · simp only [hr0, ↓reduceIte] at hrow
          exact hrow
      have hsweep_row : ∀ p ∈ imgSet, ∀ s : Nat, (hs : s < 3 * D) → ∀ j : Fin w,
          (hr : s * w + j.val < h - padding) →
          ((tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs)) j
            (fun a : Fin (w + 1) => p ⟨padding + (s * w + j.val) + a.val, by omega⟩) = true := by
        intro p hp s hs j hr
        have h1 := henc_row p hp (s * w + j.val) hr
        have h2 := enc_at_block A s hs j
        rw [h2] at h1
        exact h1
      have htag_mono : ∀ p ∈ imgSet, ∀ s : Nat, (hs : s < 3 * D) →
          (hr : s * w < h - padding) →
          p ⟨padding + s * w, by omega⟩ = true →
          p ⟨padding + (s + 1) * w, by rw [Nat.succ_mul]; omega⟩ = true := by
        intro p hp s hs hr htrue
        have hrow := hsweep_row p hp s hs 0 (by simpa using hr)
        simp only [Fin.val_zero, Nat.add_zero] at hrow
        let pat0 : Word ((d + 1) + 1) := fun a => p ⟨padding + s * w + a.val, by omega⟩
        have hpat0_eq : pat0 0 = true := by simpa [pat0] using htrue
        have hm : s / 3 < (keyList d).length := by rw [keylen]; omega
        have htg := tests_getElem A (keyList d) (s / 3) hm
        have hmod3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
        have hres : pat0 (Fin.last (d + 1)) = true := by
          rcases hmod3 with hc | hc | hc
          · have he : s = 3 * (s / 3) := by omega
            have htst : (tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs) = maskTest (keyList d)[s / 3] :=
              (getElem_eq_of_eq (tests A (keyList d)) _ _ he).trans htg.1
            rw [htst] at hrow
            exact (maskTest_zero_eq _ pat0 hrow).trans hpat0_eq
          · have he : s = 3 * (s / 3) + 1 := by omega
            have htst : (tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs) = toggleTest (keyList d)[s / 3] A :=
              (getElem_eq_of_eq (tests A (keyList d)) _ _ he).trans htg.2.1
            rw [htst] at hrow
            exact toggleTest_zero_true _ _ pat0 hpat0_eq hrow
          · have he : s = 3 * (s / 3) + 2 := by omega
            have htst : (tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs) = maskTest (keyList d)[s / 3] :=
              (getElem_eq_of_eq (tests A (keyList d)) _ _ he).trans htg.2.2
            rw [htst] at hrow
            exact (maskTest_zero_eq _ pat0 hrow).trans hpat0_eq
        dsimp only [pat0] at hres
        have he_idx : padding + s * w + (Fin.last (d + 1)).val = padding + (s + 1) * w := by
          simp only [Fin.val_last, Nat.succ_mul]; dsimp [w]; omega
        exact Eq.trans (by apply congrArg p; apply Fin.ext; dsimp only; exact he_idx.symm) hres
      have htag_after : ∀ p ∈ imgSet, ∀ s0 s : Nat, (hle : s0 ≤ s) →
          (hs : s * w ≤ h - padding) →
          p ⟨padding + s0 * w, by have := Nat.mul_le_mul_right w hle; omega⟩ = true →
          p ⟨padding + s * w, by omega⟩ = true := by
        intro p hp s0 s hle
        induction s with
        | zero =>
          intro _ h0
          have : s0 = 0 := by omega
          subst this; exact h0
        | succ s ih =>
          intro hs h0
          by_cases heq : s0 = s + 1
          · subst heq; exact h0
          · have hprev := ih (by omega) (by rw [Nat.succ_mul] at hs; omega) h0
            have hs_lt : s < 3 * D := by
              have h1 : (s + 1) * w ≤ (3 * D) * w := by
                have h2 : (3 * D) * w = 3 * w * D := by ring
                dsimp [L] at hhL; omega
              have h2 := Nat.le_of_mul_le_mul_right h1 hw_pos
              omega
            exact htag_mono p hp s hs_lt (by rw [Nat.succ_mul] at hs; omega) hprev
      have hblock_win : ∀ p ∈ imgSet, ∀ s : Nat, (hs : s < 3 * D) →
          (hr : (s + 1) * w ≤ h - padding) →
          SweepOk ((tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs))
            (fun j : Fin w => p ⟨padding + s * w + j.val, by rw [Nat.succ_mul] at hr; omega⟩)
            (fun j : Fin w => p ⟨padding + (s + 1) * w + j.val, by omega⟩) := by
        intro p hp s hs hr j
        have hrow := hsweep_row p hp s hs j (by rw [Nat.succ_mul] at hr; omega)
        have hspl : splice (fun a : Fin w => p ⟨padding + s * w + a.val, by rw [Nat.succ_mul] at hr; omega⟩)
            (fun a : Fin w => p ⟨padding + (s + 1) * w + a.val, by omega⟩) j =
            (fun a : Fin (w + 1) => p ⟨padding + (s * w + j.val) + a.val, by rw [Nat.succ_mul] at hr; omega⟩) := by
          funext a
          unfold splice
          split
          · rename_i hlt
            apply congrArg p; apply Fin.ext; dsimp only; omega
          · rename_i hge
            apply congrArg p; apply Fin.ext; dsimp only; rw [Nat.succ_mul]; omega
        rw [hspl]
        exact hrow
      have hunswitched : ∀ p ∈ imgSet, ∀ k : Nat, (hk : 3 * k * w ≤ h - padding) →
          (hno : ∀ m : Fin D, m.val < k → isSw p m = false) →
          (fun j : Fin w => p ⟨padding + 3 * k * w + j.val, by omega⟩) = mkStart (uOf p) := by
        intro p hp k
        induction k with
        | zero =>
          intro _ _
          funext j
          refine Fin.cases ?_ ?_ j
          · simp only [mkStart, Fin.cases_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Fin.val_zero]
            exact hpad0 p hp
          · intro i
            simp only [mkStart, Fin.cases_succ, uOf, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
        | succ k ih =>
          intro hk hno
          have hk0 : 3 * k * w ≤ 3 * (k + 1) * w := Nat.mul_le_mul_right w (by omega)
          have hk1 : (3 * k + 1) * w ≤ 3 * (k + 1) * w := Nat.mul_le_mul_right w (by omega)
          have hk2 : (3 * k + 2) * w ≤ 3 * (k + 1) * w := Nat.mul_le_mul_right w (by omega)
          have hk2_eq : (3 * k + 1) * w + w = (3 * k + 2) * w := by ring
          have hk2_eq' : (3 * k + 1 + 1) * w = (3 * k + 2) * w := by ring
          have hk3_eq : (3 * k + 2 + 1) * w = 3 * (k + 1) * w := by ring
          have hpre : (fun j : Fin w => p ⟨padding + 3 * k * w + j.val, by omega⟩) = mkStart (uOf p) :=
            ih (by omega) (fun m hm => hno m (by omega))
          have hkD : k < D := by
            have h1 : 3 * (k + 1) * w ≤ (3 * D) * w := by
              have h2 : (3 * D) * w = 3 * w * D := by ring
              dsimp [L] at hhL; omega
            have h2 := Nat.le_of_mul_le_mul_right h1 hw_pos
            omega
          have hklen : k < (keyList d).length := by rw [keylen]; exact hkD
          have htg := tests_getElem A (keyList d) k hklen
          have hsw0 := hblock_win p hp (3 * k) (by omega) (by omega)
          rw [htg.1, hpre, mask_ok, mask_off _ rfl] at hsw0
          have hsw1 := hblock_win p hp (3 * k + 1) (by omega) (by omega)
          rw [htg.2.1, hsw0, toggle_ok] at hsw1
          have hbit_false : p ⟨padding + (3 * k + 1) * w + w, by omega⟩ = false := by
            have hno_k := hno ⟨k, hkD⟩ (by dsimp; omega)
            have hlt_k : (3 * k + 1) * w < h - padding := by omega
            simpa [isSw, hlt_k] using hno_k
          have hmid : (fun j : Fin w => p ⟨padding + (3 * k + 1 + 1) * w + j.val, by omega⟩) = mkStart (uOf p) := by
            rcases hsw1 with hEq | ⟨_, _, hRise⟩
            · exact hEq
            · have h0 := congrFun hRise 0
              simp only [rise, Fin.cases_zero, Fin.val_zero, Nat.add_zero] at h0
              have he : padding + (3 * k + 1 + 1) * w = padding + (3 * k + 1) * w + w := by omega
              simp only [he] at h0
              rw [hbit_false] at h0
              cases h0
          have hsw2 := hblock_win p hp (3 * k + 2) (by omega) (by omega)
          rw [htg.2.2] at hsw2
          have hmid' : (fun j : Fin w => p ⟨padding + (3 * k + 2) * w + j.val, by omega⟩) = mkStart (uOf p) := hmid
          rw [hmid', mask_ok, mask_off _ rfl] at hsw2
          simpa [hk3_eq] using hsw2
      refine Finset.card_le_card_of_injOn label ?_ ?_
      · intro p hp
        dsimp only [label]
        cases hfind : firstSw p with
        | none =>
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
        | some m =>
          have hmem := List.find?_some hfind
          have hlt_m : (3 * m.val + 1) * w < h - padding := by
            dsimp only [isSw] at hmem
            split at hmem
            · assumption
            · cases hmem
          have htrue_m : p ⟨padding + (3 * m.val + 1) * w + w, by omega⟩ = true := by
            dsimp only [isSw] at hmem
            simpa [hlt_m] using hmem
          have hno_before : ∀ m' : Fin D, m'.val < m.val → isSw p m' = false :=
            fun m' hm' => find?_finRange_lt (isSw p) m m' hfind hm'
          have hpre_m := hunswitched p hp m.val
            (by have : 3 * m.val * w ≤ (3 * m.val + 1) * w := Nat.mul_le_mul_right w (by omega); omega)
            hno_before
          have hm_len : m.val < (keyList d).length := by rw [keylen]; exact m.isLt
          have htg := tests_getElem A (keyList d) m.val hm_len
          have hsw0 := hblock_win p hp (3 * m.val) (by omega) (by omega)
          rw [htg.1, hpre_m, mask_ok, mask_off _ rfl] at hsw0
          have hrow_t := hsweep_row p hp (3 * m.val + 1) (by omega) 0 (by simpa using hlt_m)
          rw [htg.2.1] at hrow_t
          have hp0 : (fun a : Fin (w + 1) => p ⟨padding + ((3 * m.val + 1) * w + (0 : Fin w).val) + a.val, by simp only [Fin.val_zero]; omega⟩) 0 = false := by
            have := congrFun hsw0 0
            simpa [mkStart] using this
          have hplast : (fun a : Fin (w + 1) => p ⟨padding + ((3 * m.val + 1) * w + (0 : Fin w).val) + a.val, by simp only [Fin.val_zero]; omega⟩) (Fin.last w) = true := by
            simpa using htrue_m
          have hA := toggleTest_zero_switch (keyList d)[m.val] A _ hp0 hplast hrow_t
          have hpay : (fun j : Fin d => p ⟨padding + ((3 * m.val + 1) * w + (0 : Fin w).val) + j.succ.castSucc.val, by simp only [Fin.val_zero]; omega⟩) = uOf p := by
            funext j
            have := congrFun hsw0 j.succ
            simpa [mkStart] using this
          rw [hpay] at hA
          refine Finset.mem_union_right _ (Finset.mem_image_of_mem _ ?_)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hA
      · intro p1 hp1 p2 hp2 hlab
        have hu_eq : uOf p1 = uOf p2 := by
          dsimp only [label] at hlab
          cases h1 : firstSw p1 <;> cases h2 : firstSw p2 <;> simp [h1, h2] at hlab
          · exact hlab
          · exact hlab.1
        have hsw_eq : firstSw p1 = firstSw p2 := by
          dsimp only [label] at hlab
          cases h1 : firstSw p1 with
          | none =>
            cases h2 : firstSw p2 with
            | none => rfl
            | some _ => simp [h1, h2] at hlab
          | some m1 =>
            cases h2 : firstSw p2 with
            | none => simp [h1, h2] at hlab
            | some m2 =>
              simp only [h1, h2, Sum.inr.injEq, Prod.mk.injEq] at hlab
              have hdiff_eq : diff (uOf p1) ((keyList d)[m1.val]'(by rw [keylen]; exact m1.isLt)) =
                  diff (uOf p1) ((keyList d)[m2.val]'(by rw [keylen]; exact m2.isLt)) := by
                have h2 := hlab.2
                rw [← hlab.1] at h2
                exact h2
              have hkey_eq := diff_inj _ _ _ hdiff_eq
              have hval_eq : m1.val = m2.val :=
                (List.Nodup.getElem_inj_iff (keyNodup d)).mp hkey_eq
              congr 1; exact Fin.ext hval_eq
        have hcp : ∀ p ∈ imgSet, ∀ t : Nat, (ht : t < padding + w) →
            p ⟨t, by omega⟩ = p ⟨t % w, by have := Nat.mod_lt t hw_pos; omega⟩ := by
          intro p hp
          refine copy_periodic hw_pos (show padding + w ≤ w + h by omega) p ?_
          intro i hi
          have hrow := hpref_pass p hp ⟨i, by omega⟩ (by dsimp; omega)
          simp only [encFull, hi, ↓reduceDIte, copyPat, beq_iff_eq, Fin.val_zero, Nat.add_zero, Fin.val_last] at hrow
          exact hrow
        have hinit_eq : ∀ t : Nat, (ht : t < padding + w) → p1 ⟨t, by omega⟩ = p2 ⟨t, by omega⟩ := by
          have hs0_eq : ∀ k : Fin w, p1 ⟨padding + k.val, by omega⟩ = p2 ⟨padding + k.val, by omega⟩ := by
            intro k
            refine Fin.cases ?_ ?_ k
            · simp only [Fin.val_zero, Nat.add_zero, hpad0 p1 hp1, hpad0 p2 hp2]
            · intro j
              exact congrFun hu_eq j
          intro t ht
          rw [hcp p1 hp1 t ht, hcp p2 hp2 t ht]
          let k := (t % w + (w - padding % w)) % w
          have hk : k < w := Nat.mod_lt _ hw_pos
          have hmod : (padding + k) % w = t % w := by
            dsimp only [k]
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have h2 : padding + (w - padding % w) = (padding / w + 1) * w := by
              have e := Nat.div_add_mod padding w
              have hm := Nat.mod_lt padding hw_pos
              rw [Nat.succ_mul, Nat.mul_comm (padding / w) w]; omega
            have h3 : padding + (t % w + (w - padding % w)) = (padding / w + 1) * w + t % w := by omega
            rw [h3, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_mod]
          have h1 := hcp p1 hp1 (padding + k) (by omega)
          have h2 := hcp p2 hp2 (padding + k) (by omega)
          have h3 := hs0_eq ⟨k, hk⟩
          simp only [hmod] at h1 h2
          rw [← h1, ← h2, h3]
        have hall : ∀ t : Nat, (ht : t < w + h) → p1 ⟨t, ht⟩ = p2 ⟨t, ht⟩ := by
          intro t
          induction t using Nat.strong_induction_on with
          | ind t ih =>
            intro ht
            by_cases htp : t < padding + w
            · exact hinit_eq t htp
            · let r := t - padding - w
              have hr : r < h - padding := by omega
              let s := r / w
              let jval := r % w
              have hjlt : jval < w := Nat.mod_lt r hw_pos
              have hs_lt : s < 3 * D := by
                have h1 : r < (3 * D) * w := by
                  have h2 : (3 * D) * w = 3 * w * D := by ring
                  dsimp [L] at hhL; omega
                exact (Nat.div_lt_iff_lt_mul hw_pos).mpr h1
              have hr_eq : s * w + jval = r := by
                have e := Nat.div_add_mod r w
                dsimp only [s, jval] at e ⊢
                rw [Nat.mul_comm s w]; exact e
              have hpre_pat : ∀ a : Fin w,
                  p1 ⟨padding + (s * w + jval) + a.val, by omega⟩ =
                  p2 ⟨padding + (s * w + jval) + a.val, by omega⟩ := by
                intro a
                exact ih (padding + (s * w + jval) + a.val) (by omega) (by omega)
              have hrow1 : ((tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs_lt)) ⟨jval, hjlt⟩
                  (fun a : Fin (w + 1) => p1 ⟨padding + (s * w + jval) + a.val, by omega⟩) = true :=
                hsweep_row p1 hp1 s hs_lt ⟨jval, hjlt⟩ (by dsimp; omega)
              have hrow2 : ((tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs_lt)) ⟨jval, hjlt⟩
                  (fun a : Fin (w + 1) => p2 ⟨padding + (s * w + jval) + a.val, by omega⟩) = true :=
                hsweep_row p2 hp2 s hs_lt ⟨jval, hjlt⟩ (by dsimp; omega)
              have hm : s / 3 < (keyList d).length := by rw [keylen]; omega
              have htg := tests_getElem A (keyList d) (s / 3) hm
              have hmod3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
              have hlast_eq : padding + (s * w + jval) + w = t := by omega
              suffices hgoal :
                  (fun a : Fin (w + 1) => p1 ⟨padding + (s * w + jval) + a.val, by omega⟩) (Fin.last w) =
                  (fun a : Fin (w + 1) => p2 ⟨padding + (s * w + jval) + a.val, by omega⟩) (Fin.last w) by
                simpa [hlast_eq] using hgoal
              rcases hmod3 with hc | hc | hc
              · have he : s = 3 * (s / 3) := by omega
                have htst : (tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs_lt) = maskTest (keyList d)[s / 3] :=
                  (getElem_eq_of_eq (tests A (keyList d)) _ _ he).trans htg.1
                rw [htst] at hrow1 hrow2
                exact maskTest_det _ _ _ _ hpre_pat hrow1 hrow2
              · have he : s = 3 * (s / 3) + 1 := by omega
                have htst : (tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs_lt) = toggleTest (keyList d)[s / 3] A :=
                  (getElem_eq_of_eq (tests A (keyList d)) _ _ he).trans htg.2.1
                rw [htst] at hrow1 hrow2
                by_cases hj0 : jval = 0
                · have hj_fin : (⟨jval, hjlt⟩ : Fin w) = 0 := Fin.ext hj0
                  rw [hj_fin] at hrow1 hrow2
                  by_cases hp0 : p1 ⟨padding + (s * w + jval), by omega⟩ = true
                  · have hp02 : p2 ⟨padding + (s * w + jval), by omega⟩ = true := by
                      have := hpre_pat 0; simpa using this.symm.trans hp0
                    exact (toggleTest_zero_true _ _ _ (by simpa using hp0) hrow1).trans
                      (toggleTest_zero_true _ _ _ (by simpa using hp02) hrow2).symm
                  · have hlt_m : (3 * (s / 3) + 1) * w < h - padding := by rw [← he]; omega
                    let mFin : Fin D := ⟨s / 3, by omega⟩
                    have his1 : isSw p1 mFin = (fun a : Fin (w + 1) => p1 ⟨padding + (s * w + jval) + a.val, by omega⟩) (Fin.last w) := by
                      simp only [isSw, mFin, hlt_m, ↓reduceDIte, Fin.val_last]
                      congr 1; apply Fin.ext; dsimp only; rw [← he, hj0, Nat.add_zero]
                    have his2 : isSw p2 mFin = (fun a : Fin (w + 1) => p2 ⟨padding + (s * w + jval) + a.val, by omega⟩) (Fin.last w) := by
                      simp only [isSw, mFin, hlt_m, ↓reduceDIte, Fin.val_last]
                      congr 1; apply Fin.ext; dsimp only; rw [← he, hj0, Nat.add_zero]
                    rw [← his1, ← his2]
                    cases hfind1 : firstSw p1 with
                    | none =>
                      have hfind2 : firstSw p2 = none := hsw_eq.symm.trans hfind1
                      have hf1 := List.find?_eq_none.mp hfind1 mFin (List.mem_finRange mFin)
                      have hf2 := List.find?_eq_none.mp hfind2 mFin (List.mem_finRange mFin)
                      rw [Bool.eq_false_iff.mpr hf1, Bool.eq_false_iff.mpr hf2]
                    | some mStar =>
                      have hfind2 : firstSw p2 = some mStar := hsw_eq.symm.trans hfind1
                      by_cases hcmp : mFin.val < mStar.val
                      · rw [find?_finRange_lt (isSw p1) mStar mFin hfind1 hcmp,
                            find?_finRange_lt (isSw p2) mStar mFin hfind2 hcmp]
                      · by_cases heqm : mFin.val = mStar.val
                        · have heqf : mFin = mStar := Fin.ext heqm
                          rw [heqf, List.find?_some hfind1, List.find?_some hfind2]
                        · exfalso
                          have hlt_star : (3 * mStar.val + 1) * w < h - padding := by
                            have hm1 := List.find?_some hfind1
                            dsimp only [isSw] at hm1
                            split at hm1
                            · assumption
                            · cases hm1
                          have htrue_star : p1 ⟨padding + (3 * mStar.val + 2) * w, by
                              have : (3 * mStar.val + 2) * w = (3 * mStar.val + 1) * w + w := by rw [Nat.succ_mul]
                              omega⟩ = true := by
                            have hm1 := List.find?_some hfind1
                            simp only [isSw, hlt_star, ↓reduceDIte] at hm1
                            have he_st : padding + (3 * mStar.val + 2) * w = padding + (3 * mStar.val + 1) * w + w := by
                              rw [Nat.succ_mul]; omega
                            simpa [he_st] using hm1
                          have hta := htag_after p1 hp1 (3 * mStar.val + 2) s (by dsimp [mFin] at hcmp heqm; omega)
                            (by omega) htrue_star
                          have he_s : padding + (s * w + jval) = padding + s * w := by omega
                          simp only [he_s] at hp0
                          exact hp0 hta
                · have hj_fin : (⟨jval, hjlt⟩ : Fin w) = (⟨jval - 1, by omega⟩ : Fin d).succ := by
                    apply Fin.ext; simp; omega
                  rw [hj_fin] at hrow1 hrow2
                  exact toggleTest_succ_det _ _ _ _ _ hpre_pat hrow1 hrow2
              · have he : s = 3 * (s / 3) + 2 := by omega
                have htst : (tests A (keyList d))[s]'(by rw [len_tests, keylen]; exact hs_lt) = maskTest (keyList d)[s / 3] :=
                  (getElem_eq_of_eq (tests A (keyList d)) _ _ he).trans htg.2.2
                rw [htst] at hrow1 hrow2
                exact maskTest_det _ _ _ _ hpre_pat hrow1 hrow2
        funext t
        exact hall t.val t.isLt
  · intro u targetMask
    let okY : (Fin n → Bool) → Prop := fun y =>
      passes y L ∧ ∀ r : Fin w, probeFull d padding u targetMask r
        (fun a => y (pos (L + r.val + a.val))) = true
    let fibY (v : Idx) : Finset (Fin n → Bool) :=
      (Finset.univ.filter okY).filter (fun y => (fun j : Fin d => y (pos (L + j.succ.val))) = v)
    have hpart : (Finset.univ.filter okY).card = ∑ v : Idx, (fibY v).card := by
      have h1 := Finset.card_eq_sum_card_fiberwise (f := fun (y : Fin n → Bool) => fun j : Fin d => y (pos (L + j.succ.val)))
        (s := Finset.univ.filter okY) (t := (Finset.univ : Finset Idx)) (fun _ _ => Finset.mem_univ _)
      exact h1
    rw [hpart, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases htm : targetMask v = true
    · simp only [htm, and_true]
      let L0 : Nat := 3 * w * D
      let ok383 : (Fin (L0 + w) → Bool) → Prop := fun x =>
        (∀ k : Fin w, x (Fin.ofNat (L0 + d + 1) k.val) = mkStart u k ∧
          x (Fin.ofNat (L0 + d + 1) (L0 + k.val)) = mkEnd v k) ∧
        ∀ i : Fin L0, enc d A i (fun off => x (Fin.ofNat (L0 + d + 1) (i.val + off.val))) = true
      have hcard383 : (Finset.univ.filter ok383).card = if A u v = true then 1 else 0 := by
        classical
        have hpc := (phys_count (tests A (keyList d)) (lengthRows d A) (mkStart u) (mkEnd v)).trans
          (net_result A (mkStart u) (mkEnd v))
        have hne : mkStart u ≠ mkEnd v := by
          intro heq
          have h0 := congrFun heq 0
          simp [mkStart, mkEnd] at h0
        have ha0 : mkStart u 0 = false := rfl
        have hb0 : mkEnd v 0 = true := rfl
        have hpa : payload (mkStart u) = u := by funext j; rfl
        have hpb : payload (mkEnd v) = v := by funext j; rfl
        have hfilt : Finset.univ.filter ok383 = Finset.univ.filter (physOk (tests A (keyList d)) (lengthRows d A) (mkStart u) (mkEnd v)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rfl
        rw [hfilt, hpc]
        simp only [hne, ↓reduceIte, Nat.zero_add, ha0, hb0, hpa, hpb, true_and]
      rw [← hcard383]
      let toX (y : Fin n → Bool) : Fin (L0 + w) → Bool :=
        fun k => y ⟨padding + k.val, by have hk := k.isLt; dsimp [n, L, L0, w] at hk ⊢; omega⟩
      let fromX (x : Fin (L0 + w) → Bool) : Fin n → Bool :=
        fun t =>
          if hge : padding ≤ t.val then
            x ⟨t.val - padding, by have ht := t.isLt; dsimp [n, L, L0, w] at ht ⊢; omega⟩
          else
            rotSeed d padding u ⟨t.val % w, Nat.mod_lt t.val hw_pos⟩
      refine Finset.card_bij (fun y _ => toX y) ?_ ?_ ?_
      · intro y hy
        simp only [fibY, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        rcases hy with ⟨⟨hpass, hprobe⟩, hv⟩
        have hinit : ∀ r : Fin w, y ⟨r.val, by dsimp [n, L, w]; omega⟩ = rotSeed d padding u r := by
          intro r
          have hr := hprobe r
          have hwrap : pos (L + r.val + (d + 1)) = ⟨r.val, by dsimp [n, L, w]; omega⟩ := by
            apply Fin.ext
            simp only [pos, Fin.val_ofNat]
            have he : L + r.val + (d + 1) = r.val + (L + d + 1) := by omega
            rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          dsimp only [probeFull] at hr
          split at hr
          · simp only [Bool.and_eq_true, beq_iff_eq, Fin.val_last] at hr
            rw [hwrap] at hr
            exact hr.1.1
          · simp only [beq_iff_eq, Fin.val_last] at hr
            rw [hwrap] at hr
            exact hr
        have hcopy : ∀ t : Nat, (ht : t < padding + w) →
            y ⟨t, by dsimp [n, L, w]; omega⟩ = y ⟨t % w, by have hml := Nat.mod_lt t hw_pos; dsimp [n, L, w] at hml ⊢; omega⟩ := by
          refine copy_periodic hw_pos (show padding + w ≤ n by dsimp [n, L, w]; omega) y ?_
          intro i hi
          have hrow := hpass ⟨i, by dsimp [L]; omega⟩ (by dsimp; omega)
          simp only [encFull, hi, ↓reduceDIte, copyPat, beq_iff_eq, Fin.val_zero, Nat.add_zero, Fin.val_last] at hrow
          have he1 : pos (i + w) = ⟨i + w, by dsimp [n, L, w]; omega⟩ := hpos_lt _ (by dsimp [n, L, w]; omega)
          have he2 : pos i = ⟨i, by dsimp [n, L, w]; omega⟩ := hpos_lt _ (by dsimp [n, L, w]; omega)
          rw [he1, he2] at hrow
          exact hrow
        have hs0 : ∀ k : Fin w, y ⟨padding + k.val, by dsimp [n, L, w]; omega⟩ = mkStart u k := by
          intro k
          rw [hcopy (padding + k.val) (by omega), hinit ⟨(padding + k.val) % w, Nat.mod_lt _ hw_pos⟩]
          dsimp only [rotSeed]
          congr 1; apply Fin.ext; dsimp only
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          rw [Nat.add_assoc, Nat.add_comm k.val, ← Nat.add_assoc]
          have h2 : padding + (w - padding % w) = (padding / w + 1) * w := by
            have e := Nat.div_add_mod padding w
            have hm := Nat.mod_lt padding hw_pos
            rw [Nat.succ_mul, Nat.mul_comm (padding / w) w]
            omega
          rw [h2, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt k.isLt]
        have htag_end : y ⟨L, by dsimp [n, L, w]; omega⟩ = true := by
          have hr0 := hprobe 0
          simp only [probeFull, Fin.val_zero, ↓reduceIte, Bool.and_eq_true, Nat.add_zero] at hr0
          have he : pos L = ⟨L, by dsimp [n, L, w]; omega⟩ := hpos_lt L (by dsimp [n, L, w]; omega)
          rw [he] at hr0
          exact hr0.1.2
        refine ⟨fun k => ⟨?_, ?_⟩, fun i => ?_⟩
        · have hof : Fin.ofNat (L0 + d + 1) k.val = ⟨k.val, by omega⟩ := by
            apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          rw [hof]
          exact hs0 k
        · have hof : Fin.ofNat (L0 + d + 1) (L0 + k.val) = ⟨L0 + k.val, by omega⟩ := by
            apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          rw [hof]
          dsimp only [toX]
          have he : padding + (L0 + k.val) = L + k.val := by dsimp [L, L0]; omega
          simp only [he]
          have hend_k : ∀ m : Fin (d + 1), y ⟨L + m.val, by dsimp [n, L, w]; omega⟩ = mkEnd v m := by
            intro m
            refine Fin.cases ?_ ?_ m
            · simp only [mkEnd, Fin.cases_zero, Fin.val_zero, Nat.add_zero]; exact htag_end
            · intro j
              simp only [mkEnd, Fin.cases_succ]
              have := congrFun hv j
              have he2 : pos (L + j.succ.val) = ⟨L + j.succ.val, by dsimp [n, L, w]; omega⟩ :=
                hpos_lt _ (by dsimp [n, L, w]; omega)
              rw [he2] at this
              exact this
          exact hend_k k
        · have hrow := hpass ⟨padding + i.val, by have hi := i.isLt; dsimp [L, L0] at hi ⊢; omega⟩
            (by have hi := i.isLt; dsimp [L, L0] at hi ⊢; omega)
          have hnot : ¬ padding + i.val < padding := by omega
          simp only [encFull, hnot, ↓reduceDIte, Nat.add_sub_cancel_left] at hrow
          have hpat : (fun j : Fin (w + 1) => y (pos (padding + i.val + j.val))) =
              (fun off : Fin (w + 1) => toX y (Fin.ofNat (L0 + d + 1) (i.val + off.val))) := by
            funext off
            have hi := i.isLt
            have hoff := off.isLt
            have hlt1 : padding + i.val + off.val < n := by dsimp [n, L, L0, w] at hi hoff ⊢; omega
            have hlt2 : i.val + off.val < L0 + w := by dsimp [L0, w] at hi hoff ⊢; omega
            rw [hpos_lt _ hlt1]
            have hof : Fin.ofNat (L0 + d + 1) (i.val + off.val) = ⟨i.val + off.val, hlt2⟩ := by
              apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hlt2
            rw [hof]
            dsimp only [toX]
            congr 1; apply Fin.ext; dsimp only; omega
          rw [hpat] at hrow
          by_cases hi0 : padding + i.val = padding
          · simp only [hi0, ↓reduceIte, Bool.and_eq_true] at hrow
            exact hrow.2
          · simp only [hi0, ↓reduceIte] at hrow
            exact hrow
      · intro y1 hy1 y2 hy2 heq
        simp only [fibY, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
        have hinit : ∀ y, okY y → ∀ r : Fin w, y ⟨r.val, by dsimp [n, L, w]; omega⟩ = rotSeed d padding u r := by
          intro y hy r
          have hr := hy.2 r
          have hwrap : pos (L + r.val + (d + 1)) = ⟨r.val, by dsimp [n, L, w]; omega⟩ := by
            apply Fin.ext
            simp only [pos, Fin.val_ofNat]
            have he : L + r.val + (d + 1) = r.val + (L + d + 1) := by omega
            rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          dsimp only [probeFull] at hr
          split at hr
          · simp only [Bool.and_eq_true, beq_iff_eq, Fin.val_last] at hr
            rw [hwrap] at hr
            exact hr.1.1
          · simp only [beq_iff_eq, Fin.val_last] at hr
            rw [hwrap] at hr
            exact hr
        have hcopy : ∀ y, okY y → ∀ t : Nat, (ht : t < padding + w) →
            y ⟨t, by dsimp [n, L, w]; omega⟩ = y ⟨t % w, by have hml := Nat.mod_lt t hw_pos; dsimp [n, L, w] at hml ⊢; omega⟩ := by
          intro y hy
          refine copy_periodic hw_pos (show padding + w ≤ n by dsimp [n, L, w]; omega) y ?_
          intro i hi
          have hrow := hy.1 ⟨i, by dsimp [L]; omega⟩ (by dsimp; omega)
          simp only [encFull, hi, ↓reduceDIte, copyPat, beq_iff_eq, Fin.val_zero, Nat.add_zero, Fin.val_last] at hrow
          have he1 : pos (i + w) = ⟨i + w, by dsimp [n, L, w]; omega⟩ := hpos_lt _ (by dsimp [n, L, w]; omega)
          have he2 : pos i = ⟨i, by dsimp [n, L, w]; omega⟩ := hpos_lt _ (by dsimp [n, L, w]; omega)
          rw [he1, he2] at hrow
          exact hrow
        funext t
        by_cases hge : padding ≤ t.val
        · have ht := t.isLt
          have hk := congrFun heq ⟨t.val - padding, by dsimp [n, L, L0, w] at ht ⊢; omega⟩
          dsimp only [toX] at hk
          have he : padding + (t.val - padding) = t.val := by omega
          simpa [he] using hk
        · rw [hcopy y1 hy1.1 t.val (by omega), hcopy y2 hy2.1 t.val (by omega),
              hinit y1 hy1.1 ⟨t.val % w, Nat.mod_lt _ hw_pos⟩, hinit y2 hy2.1 ⟨t.val % w, Nat.mod_lt _ hw_pos⟩]
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        refine ⟨fromX x, ?_, ?_⟩
        · simp only [fibY, Finset.mem_filter, Finset.mem_univ, true_and]
          have hfrom_ge : ∀ t : Nat, padding ≤ t → (ht : t < n) →
              fromX x ⟨t, ht⟩ = x ⟨t - padding, by dsimp [n, L, L0, w] at ht ⊢; omega⟩ := by
            intro t hge ht
            simp only [fromX, hge, ↓reduceDIte]
          have hfrom_per : ∀ t : Nat, (ht : t < padding + w) →
              fromX x ⟨t, by dsimp [n, L, w]; omega⟩ = rotSeed d padding u ⟨t % w, Nat.mod_lt t hw_pos⟩ := by
            intro t ht
            by_cases hge : padding ≤ t
            · rw [hfrom_ge t hge (by dsimp [n, L, w]; omega)]
              have h1 := (hx.1 ⟨t - padding, by omega⟩).1
              have hof : Fin.ofNat (L0 + d + 1) (t - padding) = ⟨t - padding, by omega⟩ := by
                apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
              rw [hof] at h1
              rw [h1]
              dsimp only [rotSeed]
              congr 1; apply Fin.ext; dsimp only
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have he1 : t = padding + (t - padding) := by omega
              conv_rhs => rw [he1]
              rw [Nat.add_assoc, Nat.add_comm (t - padding), ← Nat.add_assoc]
              have h2 : padding + (w - padding % w) = (padding / w + 1) * w := by
                have e := Nat.div_add_mod padding w
                have hm := Nat.mod_lt padding hw_pos
                rw [Nat.succ_mul, Nat.mul_comm (padding / w) w]
                omega
              rw [h2, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
            · simp only [fromX, hge, ↓reduceDIte]
          have hfrom_end : ∀ k : Fin w, fromX x ⟨L + k.val, by dsimp [n, L, w]; omega⟩ = mkEnd v k := by
            intro k
            rw [hfrom_ge (L + k.val) (by dsimp [L]; omega) (by dsimp [n, L, w]; omega)]
            have h1 := (hx.1 k).2
            have hof : Fin.ofNat (L0 + d + 1) (L0 + k.val) = ⟨L0 + k.val, by omega⟩ := by
              apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
            rw [hof] at h1
            have he : L + k.val - padding = L0 + k.val := by dsimp [L, L0]; omega
            simpa [he] using h1
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro i _
            by_cases hip : i.val < padding
            · simp only [encFull, hip, ↓reduceDIte, copyPat, beq_iff_eq, Fin.val_zero, Nat.add_zero, Fin.val_last]
              rw [hpos_lt (i.val + w) (by dsimp [n, L, w]; omega), hpos_lt i.val (by dsimp [n, L, w]; omega)]
              rw [hfrom_per (i.val + w) (by omega), hfrom_per i.val (by omega)]
              congr 1; apply Fin.ext; dsimp only; rw [Nat.add_mod_right]
            · simp only [encFull, hip, ↓reduceDIte]
              have hpat : (fun j : Fin (w + 1) => fromX x (pos (i.val + j.val))) =
                  (fun off : Fin (w + 1) => x (Fin.ofNat (L0 + d + 1) ((i.val - padding) + off.val))) := by
                funext off
                have hi := i.isLt
                have hoff := off.isLt
                have hlt1 : i.val + off.val < n := by dsimp [n, L, w] at hi hoff ⊢; omega
                have hlt2 : (i.val - padding) + off.val < L0 + w := by dsimp [L, L0, w] at hi hoff ⊢; omega
                rw [hpos_lt _ hlt1, hfrom_ge _ (by omega) hlt1]
                have hof : Fin.ofNat (L0 + d + 1) ((i.val - padding) + off.val) = ⟨(i.val - padding) + off.val, hlt2⟩ := by
                  apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hlt2
                rw [hof]
                congr 1; apply Fin.ext; dsimp only; omega
              rw [hpat]
              have h383 := hx.2 ⟨i.val - padding, by have hi := i.isLt; dsimp [L, L0] at hi ⊢; omega⟩
              by_cases hi0 : i.val = padding
              · simp only [hi0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, Fin.val_zero, Nat.add_zero]
                refine ⟨?_, by simpa [hi0] using h383⟩
                rw [hpos_lt padding (by dsimp [n, L, w]; omega),
                    hfrom_ge padding (le_refl _) (by dsimp [n, L, w]; omega)]
                have h0 := (hx.1 0).1
                simpa [mkStart] using h0
              · simp only [hi0, ↓reduceIte]
                exact h383
          · intro r
            have hwrap : pos (L + r.val + (d + 1)) = ⟨r.val, by dsimp [n, L, w]; omega⟩ := by
              apply Fin.ext
              simp only [pos, Fin.val_ofNat]
              have he : L + r.val + (d + 1) = r.val + (L + d + 1) := by omega
              rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have hok_init : fromX x (pos (L + r.val + (d + 1))) = rotSeed d padding u r := by
              rw [hwrap, hfrom_per r.val (by omega)]
              congr 1; apply Fin.ext; dsimp only; exact Nat.mod_eq_of_lt r.isLt
            dsimp only [probeFull]
            split
            · rename_i hr0
              simp only [Bool.and_eq_true, beq_iff_eq, Fin.val_last]
              have he0 : pos (L + r.val + (0 : Fin (w + 1)).val) = ⟨L + 0, by dsimp [n, L, w]; omega⟩ := by
                rw [hpos_lt _ (by simp only [Fin.val_zero]; dsimp [n, L, w]; omega)]
                apply Fin.ext; simp only [Fin.val_zero]; omega
              refine ⟨⟨hok_init, ?_⟩, ?_⟩
              · rw [he0]; simpa [mkEnd] using hfrom_end 0
              · have hpay : (fun j : Fin d => fromX x (pos (L + r.val + j.succ.castSucc.val))) = v := by
                  funext j
                  have hej : pos (L + r.val + j.succ.castSucc.val) = ⟨L + j.succ.val, by dsimp [n, L, w]; omega⟩ := by
                    rw [hpos_lt _ (by simp only [Fin.val_castSucc]; dsimp [n, L, w]; omega)]
                    apply Fin.ext; simp only [Fin.val_castSucc]; omega
                  rw [hej]
                  simpa [mkEnd] using hfrom_end j.succ
                rw [hpay]; exact htm
            · simp only [beq_iff_eq, Fin.val_last]; exact hok_init
          · funext j
            rw [hpos_lt _ (by dsimp [n, L, w]; omega)]
            simpa [mkEnd] using hfrom_end j.succ
        · funext k
          simp only [toX, fromX, Nat.le_add_right, ↓reduceDIte, Nat.add_sub_cancel_left]
    · have htm' : targetMask v = false := Bool.eq_false_iff.mpr htm
      simp only [htm', Bool.false_eq_true, and_false, ↓reduceIte]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro y hy
      simp only [fibY, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have hr0 := hy.1.2 0
      simp only [probeFull, Fin.val_zero, ↓reduceIte, Bool.and_eq_true, Nat.add_zero] at hr0
      have hpay : (fun j : Fin d => y (pos (L + j.succ.castSucc.val))) = v := hy.2
      rw [hpay] at hr0
      exact htm hr0.2

end PEqualNP.Outside.L_lib_392_aux

theorem PEqualNP.Outside.L_lib_392 : ∀ d padding : ℕ,
  let w := d + 1
  let D := 2 ^ d
  let Idx := Fin d → Bool
  let L := padding + 3 * w * D
  let n := L + d + 1
  let pos := fun coord : ℕ => Fin.ofNat (L + d + 1) coord
  let Part := fun len : ℕ => Fin len → (Fin (w + 1) → Bool) → Bool
  ∃ (enc : (Idx → Idx → Bool) → Part L) (probe : Idx → (Idx → Bool) → Part w),
    ∀ A : Idx → Idx → Bool,
      let weight := ((Finset.univ : Finset (Idx × Idx)).filter
        (fun e => A e.1 e.2 = true)).card
      let passes := fun (word : Fin n → Bool) (h : ℕ) =>
        ∀ i : Fin L, i.val < h → enc A i (fun j => word (pos (i.val + j.val))) = true
      (∀ h ≤ L,
        (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => passes x h)).image
          (fun base => fun t : Fin (w + h) => base (pos t.val))).card ≤
          (if h ≤ padding then 2 * D else D + weight)) ∧
      ∀ (u : Idx) (targetMask : Idx → Bool),
        ((Finset.univ : Finset (Fin n → Bool)).filter (fun y =>
          passes y L ∧ ∀ r : Fin w, probe u targetMask r
            (fun a => y (pos (L + r.val + a.val))) = true)).card =
          ((Finset.univ : Finset Idx).filter
            (fun v => A u v = true ∧ targetMask v = true)).card := by
  intro d padding
  exact PEqualNP.Outside.L_lib_392_aux.solve_392 d padding

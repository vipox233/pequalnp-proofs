import Mathlib
import PEqualNP.Defs

-- The encoding solve_051 (namespace C051) is the merged L_clb_051 proof and bp_count (namespace C053)
-- is the merged L_clb_053 proof, both copied unchanged up to whitespace (credit to their authors).
namespace PEqualNP.Outside.L_clb_109
namespace C051


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
    have := Nat.mul_le_mul_right w (show i.val+1 ≤ m from i.isLt)
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


private def xorAll {w : Nat} (s : Fin w → Bool) : Bool :=
  (List.finRange w).foldl (fun acc j => xor acc (s j)) false

private def copyPat {w : Nat} (pat : Fin (w + 1) → Bool) : Bool :=
  pat (Fin.last w) == pat 0

private def parPat {w : Nat} (pat : Fin (w + 1) → Bool) : Bool :=
  pat (Fin.last w) == xorAll (fun j => pat j.castSucc)

private def mkStart {d : Nat} (u : Fin d → Bool) : Fin (d + 1) → Bool :=
  Fin.cases false u

private def mkEnd {d : Nat} (v : Fin d → Bool) : Fin (d + 1) → Bool :=
  Fin.cases true v

private def probeFun {d : Nat} (u v : Fin d → Bool) (r : Fin (d + 1))
    (pat : Fin (d + 1 + 1) → Bool) : Bool :=
  (pat 0 == mkEnd v r) && (pat (Fin.last (d + 1)) == mkStart u r)

private theorem foldl_xor_init {α : Type*} (l : List α) (f : α → Bool) (init : Bool) :
    l.foldl (fun acc x => xor acc (f x)) init = xor init (l.foldl (fun acc x => xor acc (f x)) false) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (xor init (f x)), ih (f x)]
    cases init <;> cases f x <;> cases xs.foldl (fun acc y => xor acc (f y)) false <;> rfl

private theorem foldl_xor_append {α : Type*} (l1 l2 : List α) (f : α → Bool) :
    (l1 ++ l2).foldl (fun acc x => xor acc (f x)) false =
      xor (l1.foldl (fun acc x => xor acc (f x)) false) (l2.foldl (fun acc x => xor acc (f x)) false) := by
  rw [List.foldl_append, foldl_xor_init]

private theorem xorAll_rot_ext {w : Nat} (s : Fin w → Bool) (r : Nat) (_hr : r ≤ w) :
    let ext : Nat → Bool := fun t =>
      if h : t % (w + 1) < w then s ⟨t % (w + 1), h⟩ else xorAll s
    xorAll (fun j : Fin w => ext (r + j.val)) = ext (r + w) := by
  intro ext
  have hlen_ext : ∀ a b,
      ((List.range b).map (fun j => ext (a + j))).foldl xor false =
        (List.range b).foldl (fun acc j => xor acc (ext (a + j))) false := by
    intro a b; rw [List.foldl_map]
  have hxor_range : xorAll s = (List.range w).foldl (fun acc j => xor acc (ext j)) false := by
    unfold xorAll
    have h1 : List.finRange w = (List.range w).attach.map (fun ⟨j, hj⟩ => ⟨j, List.mem_range.mp hj⟩) := by
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp
    have h2 : ∀ n (hn : n ≤ w),
        ((List.finRange w).take n).foldl (fun acc j => xor acc (s j)) false =
          (List.range n).foldl (fun acc j => xor acc (ext j)) false := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have htk : (List.finRange w).take (n + 1) = (List.finRange w).take n ++ [⟨n, by omega⟩] := by
          have hlt : n < (List.finRange w).length := by simp; omega
          rw [List.take_succ_eq_append_getElem hlt]
          simp
        rw [htk, List.range_succ, List.foldl_append, List.foldl_append, ih (by omega)]
        simp only [List.foldl_cons, List.foldl_nil, ext]
        have hmod : n % (w + 1) = n := Nat.mod_eq_of_lt (by omega)
        have hlt : n % (w + 1) < w := by rw [hmod]; omega
        simp only [hlt, ↓reduceDIte]
        congr 2
        apply Fin.ext
        exact hmod.symm
    have h3 := h2 w (Nat.le_refl w)
    rw [show (List.finRange w).take w = List.finRange w by rw [List.take_of_length_le (by simp)]] at h3
    exact h3
  have hxor_cyc : ∀ m, (List.range (w + 1)).foldl (fun acc j => xor acc (ext (m + j))) false = false := by
    have h0 : (List.range (w + 1)).foldl (fun acc j => xor acc (ext j)) false = false := by
      rw [List.range_succ, List.foldl_append, ← hxor_range]
      simp only [List.foldl_cons, List.foldl_nil, ext]
      have hmod : w % (w + 1) = w := Nat.mod_eq_of_lt (by omega)
      have hnot : ¬ w % (w + 1) < w := by omega
      simp only [hnot, ↓reduceDIte, Bool.xor_self]
    intro m
    induction m with
    | zero => simpa using h0
    | succ m ih =>
      have hstep1 : (List.range (w + 1)).foldl (fun acc j => xor acc (ext (m + j))) false =
          xor (ext m) ((List.range w).foldl (fun acc j => xor acc (ext (m + 1 + j))) false) := by
        rw [List.range_succ_eq_map, List.foldl_cons, Bool.false_xor, List.foldl_map, foldl_xor_init]
        have hfn : (fun acc j => xor acc (ext (m + (j + 1)))) = (fun acc j => xor acc (ext (m + 1 + j))) := by
          funext acc j; congr 2; omega
        rw [hfn]
        simp only [Nat.add_zero]
      have hstep2 : (List.range (w + 1)).foldl (fun acc j => xor acc (ext (m + 1 + j))) false =
          xor ((List.range w).foldl (fun acc j => xor acc (ext (m + 1 + j))) false) (ext (m + 1 + w)) := by
        rw [List.range_succ, List.foldl_append]
        simp
      have hper : ext (m + 1 + w) = ext m := by
        dsimp only [ext]
        have hmod : (m + 1 + w) % (w + 1) = m % (w + 1) := by
          rw [show m + 1 + w = m + (w + 1) by omega, Nat.add_mod_right]
        simp only [hmod]
      rw [hstep1] at ih
      rw [hstep2, hper]
      cases h1 : ext m <;> cases h2 : (List.range w).foldl (fun acc j => xor acc (ext (m + 1 + j))) false <;>
        simp_all
  have hsplit : (List.range (w + 1)).foldl (fun acc j => xor acc (ext (r + j))) false =
      xor (xorAll (fun j : Fin w => ext (r + j.val))) (ext (r + w)) := by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    congr 1
    unfold xorAll
    have h2 : ∀ n (hn : n ≤ w),
        ((List.finRange w).take n).foldl (fun acc j => xor acc (ext (r + j.val))) false =
          (List.range n).foldl (fun acc j => xor acc (ext (r + j))) false := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have htk : (List.finRange w).take (n + 1) = (List.finRange w).take n ++ [⟨n, by omega⟩] := by
          have hlt : n < (List.finRange w).length := by simp; omega
          rw [List.take_succ_eq_append_getElem hlt]
          simp
        rw [htk, List.range_succ, List.foldl_append, List.foldl_append, ih (by omega)]
        simp
    have h3 := h2 w (Nat.le_refl w)
    rw [show (List.finRange w).take w = List.finRange w by rw [List.take_of_length_le (by simp)]] at h3
    exact h3.symm
  have hc := hxor_cyc r
  rw [hsplit] at hc
  cases h1 : xorAll (fun j : Fin w => ext (r + j.val)) <;> cases h2 : ext (r + w) <;> simp_all

private theorem parity_block_unique {w n : Nat} (hn : 0 < n) (word : Fin n → Bool)
    (pos : Nat) (s : Fin w → Bool)
    (hinit : ∀ j : Fin w, word ⟨(pos + j.val) % n, Nat.mod_lt _ hn⟩ = s j)
    (hpar : ∀ r : Nat, r < w + 1 →
      parPat (fun k : Fin (w + 1) => word ⟨(pos + r + k.val) % n, Nat.mod_lt _ hn⟩) = true) :
    let ext : Nat → Bool := fun t =>
      if h : t % (w + 1) < w then s ⟨t % (w + 1), h⟩ else xorAll s
    ∀ t : Nat, t ≤ 2 * w → word ⟨(pos + t) % n, Nat.mod_lt _ hn⟩ = ext t := by
  intro ext t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    by_cases htw : t < w
    · have h1 := hinit ⟨t, htw⟩
      dsimp only [ext]
      have hmod : t % (w + 1) = t := Nat.mod_eq_of_lt (by omega)
      have hlt : t % (w + 1) < w := by rw [hmod]; omega
      simp only [hlt, ↓reduceDIte]
      rw [h1]
      congr 1
      apply Fin.ext
      exact hmod.symm
    · let r := t - w
      have hr : r < w + 1 := by dsimp [r]; omega
      have hp := hpar r hr
      simp only [parPat, beq_iff_eq, Fin.val_last] at hp
      have he1 : pos + r + w = pos + t := by dsimp [r]; omega
      have he2 : r + w = t := by dsimp [r]; omega
      rw [← he1, hp]
      have hwin : (fun j : Fin w => word ⟨(pos + r + j.val) % n, Nat.mod_lt _ hn⟩) =
          (fun j : Fin w => ext (r + j.val)) := by
        funext j
        have he3 : pos + r + j.val = pos + (r + j.val) := by omega
        rw [he3]
        exact ih (r + j.val) (by dsimp [r]; omega) (by dsimp [r]; omega)
      change xorAll (fun j : Fin w => word ⟨(pos + r + j.val) % n, Nat.mod_lt _ hn⟩) = ext t
      rw [hwin, xorAll_rot_ext s r (by omega), he2]

private theorem solve_051 (d b p q : Nat) :
    let w := d + 1
    let D := Fin d → Bool
    let B := b + 1
    let L := 3 * w * 2 ^ d
    let n := L + B * w + p * w + q * (w + 1)
    let hn : 0 < n := by dsimp [n, L, B, w]; positivity
    let Pattern := Fin (w + 1) → Bool
    ∃ (ctx : (D → D → Bool) → Fin n → Pattern → Bool)
      (probe : D → D → Fin w → Pattern → Bool),
      (∀ M N i, L ≤ i.val → ctx M i = ctx N i) ∧
      ∀ (A : D → D → Bool) (u v : D) (h : Fin B),
        let start := L + h.val * w
        let row := fun (i : Fin n) (pat : Pattern) =>
          if start ≤ i.val ∧ i.val < start + w then
            probe u v (Fin.ofNat (d + 1) (i.val - start)) pat
          else ctx A i pat
        let ok := fun (word : Fin n → Bool) => ∀ s : Fin n,
          row s (fun k => word ⟨(s.val + k.val) % n, Nat.mod_lt _ hn⟩) = true
        (Finset.univ.filter ok).card = (A u v).toNat := by
  intro w D B L n hn Pattern
  obtain ⟨enc, _, henc⟩ := lib383_spec d
  let P0 := L + B * w + p * w
  let ctx : (D → D → Bool) → Fin n → Pattern → Bool := fun A i pat =>
    if hi : i.val < L then enc A ⟨i.val, hi⟩ pat
    else if i.val < P0 then copyPat pat
    else parPat pat
  refine ⟨ctx, probeFun, ?_, ?_⟩
  · intro M N i hi
    funext pat
    simp only [ctx, show ¬ i.val < L by omega, ↓reduceDIte]
  · intro A u v h start row ok
    let a0 : Fin w → Bool := mkStart u
    let b0 : Fin w → Bool := mkEnd v
    let extU : Nat → Bool := fun t =>
      if ht : t % (w + 1) < w then a0 ⟨t % (w + 1), ht⟩ else xorAll a0
    let ok383 : (Fin (L + w) → Bool) → Prop := fun x =>
      (∀ k : Fin w, x (Fin.ofNat (L + d + 1) k.val) = a0 k ∧
        x (Fin.ofNat (L + d + 1) (L + k.val)) = b0 k) ∧
      ∀ i : Fin L, enc A i (fun off => x (Fin.ofNat (L + d + 1) (i.val + off.val))) = true
    have hcard383 : (Finset.univ.filter ok383).card = (A u v).toNat := by
      have hc := henc A a0 b0
      have hne : a0 ≠ b0 := by
        intro heq
        have h0 := congrFun heq 0
        simp [a0, b0, mkStart, mkEnd] at h0
      have ha0 : a0 0 = false := rfl
      have hb0 : b0 0 = true := rfl
      have hpa : (fun ia : Fin d => a0 ia.succ) = u := by funext ia; rfl
      have hpb : (fun ib : Fin d => b0 ib.succ) = v := by funext ib; rfl
      rw [hc]
      simp only [hne, ↓reduceIte, Nat.zero_add, ha0, hb0, hpa, hpb, true_and]
      cases A u v <;> rfl
    have hLw_le : L + w ≤ n := by
      have hBw : w ≤ B * w := Nat.le_mul_of_pos_left w (Nat.succ_pos b)
      dsimp only [n]
      omega
    have hstart_le : start + w ≤ P0 := by
      have h1 : (h.val + 1) * w ≤ B * w := Nat.mul_le_mul_right w (show h.val + 1 ≤ B by omega)
      rw [Nat.succ_mul] at h1
      dsimp only [start, P0]
      omega
    have hP0_eq : start + w + ((B - 1 - h.val) + p) * w = P0 := by
      dsimp only [start, P0]
      have e1 : h.val + 1 + (B - 1 - h.val) + p = B + p := by omega
      have e2 : (h.val + 1 + (B - 1 - h.val) + p) * w = (B + p) * w := congrArg (· * w) e1
      have e3 : (h.val + 1 + (B - 1 - h.val) + p) * w = h.val * w + w + ((B - 1 - h.val) + p) * w := by ring
      have e4 : (B + p) * w = B * w + p * w := by ring
      omega
    let tailBit (i : Nat) : Bool :=
      if i < start + w then b0 ⟨(i - L) % w, Nat.mod_lt _ (Nat.succ_pos d)⟩
      else if i < P0 then a0 ⟨(i - (start + w)) % w, Nat.mod_lt _ (Nat.succ_pos d)⟩
      else extU (i - P0)
    let toP (word : Fin n → Bool) : Fin (L + w) → Bool :=
      fun k => word ⟨k.val, by omega⟩
    let fromP (x : Fin (L + w) → Bool) : Fin n → Bool :=
      fun i => if hi : i.val < L + w then x ⟨i.val, hi⟩ else tailBit i.val
    have hfrom_to : ∀ (x : Fin (L + w) → Bool), toP (fromP x) = x := by
      intro x
      funext k
      simp [toP, fromP, k.isLt]
    have hok_unique : ∀ (word : Fin n → Bool), ok word →
        (∀ j : Fin w, word ⟨j.val, by omega⟩ = a0 j) ∧
        (∀ i : Nat, L ≤ i → (hin : i < n) → word ⟨i, hin⟩ = tailBit i) := by
      intro word hok
      have hprobe : ∀ r : Fin w,
          word ⟨start + r.val, by omega⟩ = b0 r ∧
          word ⟨(start + w + r.val) % n, Nat.mod_lt _ hn⟩ = a0 r := by
        intro r
        have hs_lt : start + r.val < n := by omega
        have hrow := hok ⟨start + r.val, hs_lt⟩
        have hin : start ≤ start + r.val ∧ start + r.val < start + w := by omega
        simp only [row, hin, and_self, ↓reduceIte] at hrow
        have hof : Fin.ofNat (d + 1) (start + r.val - start) = r := by
          apply Fin.ext
          simp only [Fin.val_ofNat, Nat.add_sub_cancel_left]
          exact Nat.mod_eq_of_lt r.isLt
        rw [hof] at hrow
        simp only [probeFun, Bool.and_eq_true, beq_iff_eq, Fin.val_zero, Nat.add_zero, Fin.val_last] at hrow
        have he1 : (start + r.val) % n = start + r.val := Nat.mod_eq_of_lt hs_lt
        have he2 : start + r.val + w = start + w + r.val := by omega
        have h1 : word ⟨start + r.val, hs_lt⟩ = b0 r := by
          have := hrow.1
          simp only [he1] at this
          exact this
        have h2 : word ⟨(start + w + r.val) % n, Nat.mod_lt _ hn⟩ = a0 r := by
          have he2' : (start + w + r.val) % n = (start + r.val + (d + 1)) % n := by
            congr 1; dsimp only [w]; omega
          exact Eq.trans (by congr 1; apply Fin.ext; dsimp only; exact he2') hrow.2
        exact ⟨h1, h2⟩
      have hback : ∀ m ≤ h.val, ∀ r : Fin w,
          word ⟨L + (h.val - m) * w + r.val, by
            have := Nat.mul_le_mul_right w (show h.val - m + 1 ≤ B by omega)
            rw [Nat.succ_mul] at this
            dsimp only [n]; omega⟩ = b0 r := by
        intro m
        induction m with
        | zero =>
          intro _ r
          simpa [start] using (hprobe r).1
        | succ m ih =>
          intro hm r
          have hih := ih (by omega) r
          let pos := L + (h.val - (m + 1)) * w
          have hpos_lt : pos + r.val < n := by
            have := Nat.mul_le_mul_right w (show h.val - (m + 1) + 1 ≤ B by omega)
            rw [Nat.succ_mul] at this; dsimp only [pos, n]; omega
          have hpos_not_start : ¬ (start ≤ pos + r.val ∧ pos + r.val < start + w) := by
            have hle : (h.val - (m + 1) + 1) * w ≤ h.val * w :=
              Nat.mul_le_mul_right w (by omega)
            rw [Nat.succ_mul] at hle
            dsimp only [pos, start]; omega
          have hrow := hok ⟨pos + r.val, hpos_lt⟩
          simp only [row, hpos_not_start, ↓reduceIte, ctx,
            show ¬ pos + r.val < L by dsimp [pos]; omega, ↓reduceDIte,
            show pos + r.val < P0 by
              have := Nat.mul_le_mul_right w (show h.val - (m + 1) + 1 ≤ B by omega)
              rw [Nat.succ_mul] at this; dsimp only [pos, P0]; omega] at hrow
          simp only [copyPat, beq_iff_eq, Fin.val_zero, Nat.add_zero, Fin.val_last] at hrow
          have he1 : (pos + r.val) % n = pos + r.val := Nat.mod_eq_of_lt hpos_lt
          have he2 : pos + r.val + w = L + (h.val - m) * w + r.val := by
            have h1 : h.val - m = h.val - (m + 1) + 1 := by omega
            dsimp only [pos]
            rw [h1, Nat.succ_mul]
            omega
          have hlt2 : L + (h.val - m) * w + r.val < n := by
            have := Nat.mul_le_mul_right w (show h.val - m + 1 ≤ B by omega)
            rw [Nat.succ_mul] at this; dsimp only [n]; omega
          have he3 : (pos + r.val + w) % n = L + (h.val - m) * w + r.val := by
            rw [he2, Nat.mod_eq_of_lt hlt2]
          simp only [he1, he3] at hrow
          rw [← hrow]
          exact hih
      have hfwd_copy : ∀ m ≤ (B - 1 - h.val) + p, ∀ r : Fin w,
          word ⟨(start + w + m * w + r.val) % n, Nat.mod_lt _ hn⟩ = a0 r := by
        intro m
        induction m with
        | zero =>
          intro _ r
          simpa using (hprobe r).2
        | succ m ih =>
          intro hm r
          have hih := ih (by omega) r
          let pos := start + w + m * w
          have hpos_ge : start + w ≤ pos + r.val := by dsimp [pos]; omega
          have hpos_ltP0 : pos + r.val < P0 := by
            have h1 : (h.val + 1 + m + 1) * w ≤ (B + p) * w :=
              Nat.mul_le_mul_right w (by omega)
            have h2 : (h.val + 1 + m + 1) * w = h.val * w + w + m * w + w := by ring
            have h3 : (B + p) * w = B * w + p * w := by ring
            dsimp only [pos, start, P0]
            omega
          have hpos_lt : pos + r.val < n := by dsimp only [n, P0] at hpos_ltP0 ⊢; omega
          have hrow := hok ⟨pos + r.val, hpos_lt⟩
          simp only [row, show ¬ (start ≤ pos + r.val ∧ pos + r.val < start + w) by omega, ↓reduceIte,
            ctx, show ¬ pos + r.val < L by dsimp [pos, start]; omega, ↓reduceDIte, hpos_ltP0] at hrow
          simp only [copyPat, beq_iff_eq, Fin.val_zero, Nat.add_zero, Fin.val_last] at hrow
          have he1 : pos + r.val + w = start + w + (m + 1) * w + r.val := by
            dsimp only [pos]; rw [Nat.succ_mul]; omega
          simp only [he1] at hrow
          rw [hrow]
          exact hih
      have hP0_win : ∀ r : Fin w, word ⟨(P0 + r.val) % n, Nat.mod_lt _ hn⟩ = a0 r := by
        intro r
        have h1 := hfwd_copy ((B - 1 - h.val) + p) (Nat.le_refl _) r
        have he : start + w + ((B - 1 - h.val) + p) * w + r.val = P0 + r.val := by omega
        simp only [he] at h1
        exact h1
      have hfwd_par : ∀ m < q, ∀ t ≤ 2 * w,
          word ⟨(P0 + m * (w + 1) + t) % n, Nat.mod_lt _ hn⟩ = extU t := by
        intro m
        induction m with
        | zero =>
          intro hq0 t ht
          have h0 : ∀ r : Fin w, word ⟨(P0 + r.val) % n, Nat.mod_lt _ hn⟩ = a0 r := hP0_win
          have hpar0 : ∀ r < w + 1,
              parPat (fun k : Fin (w + 1) => word ⟨(P0 + r + k.val) % n, Nat.mod_lt _ hn⟩) = true := by
            intro r hr
            have hlt : P0 + r < n := by
              have := Nat.le_mul_of_pos_left (w + 1) hq0
              dsimp only [n, P0]; omega
            have hrow := hok ⟨P0 + r, hlt⟩
            simp only [row, show ¬ (start ≤ P0 + r ∧ P0 + r < start + w) by omega, ↓reduceIte,
              ctx, show ¬ P0 + r < L by dsimp [P0]; omega, ↓reduceDIte,
              show ¬ P0 + r < P0 by omega] at hrow
            exact hrow
          simpa using parity_block_unique hn word P0 a0 h0 hpar0 t ht
        | succ m ih =>
          intro hm t ht
          have hih := ih (by omega)
          have hinit_m : ∀ r : Fin w, word ⟨(P0 + (m + 1) * (w + 1) + r.val) % n, Nat.mod_lt _ hn⟩ = a0 r := by
            intro r
            have h1 := hih (w + 1 + r.val) (by omega)
            have he : P0 + m * (w + 1) + (w + 1 + r.val) = P0 + (m + 1) * (w + 1) + r.val := by
              rw [Nat.succ_mul]; omega
            rw [he] at h1
            rw [h1]
            dsimp only [extU]
            have hmod : (w + 1 + r.val) % (w + 1) = r.val := by
              rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have hlt : (w + 1 + r.val) % (w + 1) < w := by rw [hmod]; exact r.isLt
            simp only [hlt, ↓reduceDIte]
            congr 1; apply Fin.ext; exact hmod
          have hpar_m : ∀ r < w + 1,
              parPat (fun k : Fin (w + 1) =>
                word ⟨(P0 + (m + 1) * (w + 1) + r + k.val) % n, Nat.mod_lt _ hn⟩) = true := by
            intro r hr
            have hlt : P0 + (m + 1) * (w + 1) + r < n := by
              have := Nat.mul_le_mul_right (w + 1) (show m + 1 + 1 ≤ q by omega)
              rw [Nat.succ_mul] at this
              dsimp only [n, P0]; omega
            have hrow := hok ⟨P0 + (m + 1) * (w + 1) + r, hlt⟩
            simp only [row, show ¬ (start ≤ P0 + (m + 1) * (w + 1) + r ∧
                P0 + (m + 1) * (w + 1) + r < start + w) by omega, ↓reduceIte,
              ctx, show ¬ P0 + (m + 1) * (w + 1) + r < L by dsimp [P0]; omega, ↓reduceDIte,
              show ¬ P0 + (m + 1) * (w + 1) + r < P0 by omega] at hrow
            exact hrow
          exact parity_block_unique hn word (P0 + (m + 1) * (w + 1)) a0 hinit_m hpar_m t ht
      constructor
      · intro j
        by_cases hq0 : q = 0
        · have he : P0 = n := by dsimp only [n, P0]; rw [hq0]; simp
          have h1 := hP0_win j
          have he2 : (P0 + j.val) % n = j.val := by
            rw [he, Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          simp only [he2] at h1
          exact h1
        · have h1 := hfwd_par (q - 1) (by omega) (w + 1 + j.val) (by omega)
          have he : P0 + (q - 1) * (w + 1) + (w + 1 + j.val) = n + j.val := by
            have e1 : (q - 1) * (w + 1) + (w + 1) = q * (w + 1) := by
              have hq1 : q = (q - 1) + 1 := by omega
              conv_rhs => rw [hq1, Nat.succ_mul]
            dsimp only [n, P0]; omega
          have hmod0 : (P0 + (q - 1) * (w + 1) + (w + 1 + j.val)) % n = j.val := by
            rw [he, Nat.add_comm n, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          simp only [hmod0] at h1
          rw [h1]
          dsimp only [extU]
          have hmod : (w + 1 + j.val) % (w + 1) = j.val := by
            rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hlt : (w + 1 + j.val) % (w + 1) < w := by rw [hmod]; exact j.isLt
          simp only [hlt, ↓reduceDIte]
          congr 1; apply Fin.ext; exact hmod
      · intro i hiL hin
        dsimp only [tailBit]
        by_cases h1 : i < start + w
        · simp only [h1, ↓reduceIte]
          let qm := (i - L) / w
          let rm := (i - L) % w
          have hrm : rm < w := Nat.mod_lt _ (Nat.succ_pos d)
          have hqm : qm ≤ h.val := by
            have hlt : i - L < (h.val + 1) * w := by
              rw [Nat.succ_mul]; dsimp [start] at h1; omega
            have hdiv := (Nat.div_lt_iff_lt_mul (show 0 < w by dsimp [w]; omega)).mpr hlt
            dsimp only [qm]; omega
          have hb := hback (h.val - qm) (Nat.sub_le h.val qm) ⟨rm, hrm⟩
          have he : L + (h.val - (h.val - qm)) * w + rm = i := by
            have e1 : h.val - (h.val - qm) = qm := Nat.sub_sub_self hqm
            have e2 := Nat.div_add_mod (i - L) w
            rw [e1, Nat.mul_comm qm w]
            dsimp only [qm, rm] at e2 ⊢
            omega
          simp only [he] at hb
          exact hb
        · by_cases h2 : i < P0
          · simp only [h1, h2, ↓reduceIte]
            let qm := (i - (start + w)) / w
            let rm := (i - (start + w)) % w
            have hrm : rm < w := Nat.mod_lt _ (Nat.succ_pos d)
            have hqm : qm ≤ (B - 1 - h.val) + p := by
              have hlt : i - (start + w) < ((B - 1 - h.val) + p) * w := by omega
              have hdiv := (Nat.div_lt_iff_lt_mul (show 0 < w by dsimp [w]; omega)).mpr hlt
              dsimp only [qm]; omega
            have hf := hfwd_copy qm hqm ⟨rm, hrm⟩
            have he : start + w + qm * w + rm = i := by
              have e2 := Nat.div_add_mod (i - (start + w)) w
              rw [Nat.mul_comm qm w]
              dsimp only [qm, rm] at e2 ⊢
              omega
            have hmod0 : (start + w + qm * w + rm) % n = i := by
              rw [he, Nat.mod_eq_of_lt hin]
            simp only [hmod0] at hf
            exact hf
          · simp only [h1, h2, ↓reduceIte]
            let qm := (i - P0) / (w + 1)
            let rm := (i - P0) % (w + 1)
            have hrm : rm < w + 1 := Nat.mod_lt _ (Nat.succ_pos w)
            have hqm : qm < q := by
              have hlt : i - P0 < q * (w + 1) := by dsimp [n, P0] at hin ⊢; omega
              exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos w)).mpr hlt
            have hp_eq := hfwd_par qm (by omega) rm (by omega)
            have he : P0 + qm * (w + 1) + rm = i := by
              have e2 := Nat.div_add_mod (i - P0) (w + 1)
              rw [Nat.mul_comm qm (w + 1)]
              dsimp only [qm, rm] at e2 ⊢
              omega
            have hmod0 : (P0 + qm * (w + 1) + rm) % n = i := by
              rw [he, Nat.mod_eq_of_lt hin]
            simp only [hmod0] at hp_eq
            rw [hp_eq]
            dsimp only [extU, rm]
            rw [Nat.mod_mod]
    have hfrom_ok : ∀ (x : Fin (L + w) → Bool), ok383 x → ok (fromP x) := by
      intro x hx
      have hfrom_start : ∀ j : Fin w, fromP x ⟨j.val, by omega⟩ = a0 j := by
        intro j
        have hlt : j.val < L + w := by omega
        simp only [fromP, hlt, ↓reduceDIte]
        have h1 := (hx.1 j).1
        have hof : Fin.ofNat (L + d + 1) j.val = ⟨j.val, hlt⟩ := by
          apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hlt
        rw [hof] at h1
        exact h1
      have hfrom_L : ∀ i : Nat, L ≤ i → (hin : i < n) → fromP x ⟨i, hin⟩ = tailBit i := by
        intro i hiL hin
        by_cases hiLw : i < L + w
        · simp only [fromP, hiLw, ↓reduceDIte]
          have h1 := (hx.1 ⟨i - L, by omega⟩).2
          have hof : Fin.ofNat (L + d + 1) (L + (i - L)) = ⟨i, hiLw⟩ := by
            apply Fin.ext; simp only [Fin.val_ofNat]; rw [show L + (i - L) = i by omega]; exact Nat.mod_eq_of_lt hiLw
          rw [hof] at h1
          rw [h1]
          dsimp only [tailBit]
          have hlt_s : i < start + w := by dsimp [start]; omega
          simp only [hlt_s, ↓reduceIte]
          congr 1; apply Fin.ext; exact (Nat.mod_eq_of_lt (by omega)).symm
        · simp only [fromP, hiLw, ↓reduceDIte]
      intro s
      by_cases hsL : s.val < L
      · have hnot_st : ¬ (start ≤ s.val ∧ s.val < start + w) := by dsimp [start]; omega
        simp only [row, hnot_st, ↓reduceIte, ctx, hsL, ↓reduceDIte]
        have heq_pat : (fun k : Fin (w + 1) => fromP x ⟨(s.val + k.val) % n, Nat.mod_lt _ hn⟩) =
            (fun k : Fin (w + 1) => x (Fin.ofNat (L + d + 1) (s.val + k.val))) := by
          funext k
          have hlt1 : s.val + k.val < L + w := by omega
          have hlt2 : s.val + k.val < n := by omega
          have hmod1 : (s.val + k.val) % n = s.val + k.val := Nat.mod_eq_of_lt hlt2
          simp only [fromP, hmod1, hlt1, ↓reduceDIte]
          congr 1
          apply Fin.ext
          simp only [Fin.val_ofNat]
          exact (Nat.mod_eq_of_lt hlt1).symm
        rw [heq_pat]
        exact hx.2 ⟨s.val, hsL⟩
      · by_cases hs_st : start ≤ s.val ∧ s.val < start + w
        · simp only [row, hs_st, and_self, ↓reduceIte, probeFun, Bool.and_eq_true, beq_iff_eq,
            Fin.val_zero, Nat.add_zero, Fin.val_last]
          have hof_val : (Fin.ofNat (d + 1) (s.val - start)).val = s.val - start := by
            simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          have h1 : fromP x ⟨s.val % n, Nat.mod_lt _ hn⟩ = b0 (Fin.ofNat (d + 1) (s.val - start)) := by
            have hmod : s.val % n = s.val := Nat.mod_eq_of_lt s.isLt
            simp only [hmod]
            rw [hfrom_L s.val (by omega) s.isLt]
            dsimp only [tailBit]
            simp only [hs_st.2, ↓reduceIte]
            congr 1
            apply Fin.ext
            dsimp only
            rw [hof_val]
            have he : s.val - L = h.val * w + (s.val - start) := by dsimp [start]; omega
            rw [he, Nat.mul_comm h.val w, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          have h2 : fromP x ⟨(s.val + w) % n, Nat.mod_lt _ hn⟩ = a0 (Fin.ofNat (d + 1) (s.val - start)) := by
            by_cases hwrap : s.val + w < n
            · have hmod : (s.val + w) % n = s.val + w := Nat.mod_eq_of_lt hwrap
              simp only [hmod]
              rw [hfrom_L (s.val + w) (by omega) hwrap]
              dsimp only [tailBit]
              have hnot1 : ¬ s.val + w < start + w := by omega
              simp only [hnot1, ↓reduceIte]
              by_cases hP0 : s.val + w < P0
              · simp only [hP0, ↓reduceIte]
                congr 1; apply Fin.ext; dsimp only; rw [hof_val]
                have he : s.val + w - (start + w) = s.val - start := by omega
                rw [he, Nat.mod_eq_of_lt (by omega)]
              · simp only [hP0, ↓reduceIte]
                dsimp only [extU]
                have hstP0 : start + w = P0 := by
                  have hz : (B - 1 - h.val) + p = 0 := by
                    by_contra hne
                    have : w ≤ ((B - 1 - h.val) + p) * w := Nat.le_mul_of_pos_left w (by omega)
                    omega
                  rw [hz, Nat.zero_mul, Nat.add_zero] at hP0_eq
                  exact hP0_eq
                have he : s.val + w - P0 = s.val - start := by omega
                have hmod2 : (s.val + w - P0) % (w + 1) = s.val - start := by
                  rw [he, Nat.mod_eq_of_lt (by omega)]
                have hlt2 : (s.val + w - P0) % (w + 1) < w := by rw [hmod2]; omega
                simp only [hlt2, ↓reduceDIte]
                congr 1; apply Fin.ext; dsimp only; rw [hof_val, hmod2]
            · have hst_eq : start + w = n := by
                have hz1 : (B - 1 - h.val) + p = 0 := by
                  by_contra hne
                  have : w ≤ ((B - 1 - h.val) + p) * w := Nat.le_mul_of_pos_left w (by omega)
                  dsimp only [n, P0] at hwrap hP0_eq; omega
                have hz2 : q = 0 := by
                  by_contra hne
                  have : w + 1 ≤ q * (w + 1) := Nat.le_mul_of_pos_left (w + 1) (by omega)
                  dsimp only [n, P0] at hwrap hP0_eq; omega
                rw [hz1, Nat.zero_mul, Nat.add_zero] at hP0_eq
                dsimp only [n, P0] at hP0_eq ⊢
                rw [hz2, Nat.zero_mul, Nat.add_zero]
                exact hP0_eq
              have hmod : (s.val + w) % n = s.val - start := by
                have he : s.val + w = (s.val - start) + n := by omega
                rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              simp only [hmod]
              have hst := hfrom_start (Fin.ofNat (d + 1) (s.val - start))
              simp only [hof_val] at hst
              exact hst
          exact ⟨h1, h2⟩
        · simp only [row, hs_st, ↓reduceIte, ctx, hsL, ↓reduceDIte]
          by_cases hsP0 : s.val < P0
          · simp only [hsP0, ↓reduceIte, copyPat, beq_iff_eq, Fin.val_zero, Nat.add_zero, Fin.val_last]
            have hmod1 : s.val % n = s.val := Nat.mod_eq_of_lt s.isLt
            simp only [hmod1]
            rw [hfrom_L s.val (by omega) s.isLt]
            by_cases hs_before : s.val < start
            · have hlt_sw : s.val + w < start + w := by omega
              have hlt_n : s.val + w < n := by omega
              have hmod2 : (s.val + w) % n = s.val + w := Nat.mod_eq_of_lt hlt_n
              simp only [hmod2]
              rw [hfrom_L (s.val + w) (by omega) hlt_n]
              dsimp only [tailBit]
              simp only [show s.val < start + w by omega, hlt_sw, ↓reduceIte]
              congr 1; apply Fin.ext; dsimp only
              have he : s.val + w - L = (s.val - L) + w := by omega
              rw [he, Nat.add_mod_right]
            · have hs_after : start + w ≤ s.val := by omega
              dsimp only [tailBit]
              simp only [show ¬ s.val < start + w by omega, hsP0, ↓reduceIte]
              have hdivP0 : (P0 - (start + w)) % w = 0 := by
                have he : P0 - (start + w) = ((B - 1 - h.val) + p) * w := by omega
                rw [he, Nat.mul_mod_left]
              by_cases hwrap : s.val + w < n
              · have hmod2 : (s.val + w) % n = s.val + w := Nat.mod_eq_of_lt hwrap
                simp only [hmod2]
                rw [hfrom_L (s.val + w) (by omega) hwrap]
                dsimp only [tailBit]
                simp only [show ¬ s.val + w < start + w by omega, ↓reduceIte]
                by_cases hP0' : s.val + w < P0
                · simp only [hP0', ↓reduceIte]
                  congr 1; apply Fin.ext; dsimp only
                  have he : s.val + w - (start + w) = (s.val - (start + w)) + w := by omega
                  rw [he, Nat.add_mod_right]
                · simp only [hP0', ↓reduceIte]
                  dsimp only [extU]
                  have hlt_w : s.val + w - P0 < w := by omega
                  have hmod_ext : (s.val + w - P0) % (w + 1) = s.val + w - P0 := Nat.mod_eq_of_lt (by omega)
                  have hlt_ext : (s.val + w - P0) % (w + 1) < w := by rw [hmod_ext]; exact hlt_w
                  simp only [hlt_ext, ↓reduceDIte]
                  congr 1; apply Fin.ext; dsimp only
                  rw [hmod_ext]
                  have he : s.val + w - (start + w) = (P0 - (start + w)) + (s.val + w - P0) := by omega
                  have he2 : (s.val - (start + w)) % w = (s.val + w - (start + w)) % w := by
                    rw [show s.val + w - (start + w) = (s.val - (start + w)) + w by omega, Nat.add_mod_right]
                  rw [he2, he, Nat.add_mod, hdivP0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt_w]
              · have hP0_eq_n : P0 = n := by
                  have hq0 : q = 0 := by
                    by_contra hqne
                    have : w + 1 ≤ q * (w + 1) := Nat.le_mul_of_pos_left (w + 1) (by omega)
                    dsimp only [n, P0] at hwrap hsP0; omega
                  dsimp only [n, P0]; rw [hq0]; simp
                have hlt_w : s.val + w - P0 < w := by omega
                have hmod2 : (s.val + w) % n = s.val + w - P0 := by
                  have he : s.val + w = (s.val + w - P0) + n := by omega
                  conv_lhs => rw [he]
                  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt_w (by omega))]
                simp only [hmod2]
                have hst := hfrom_start ⟨s.val + w - P0, hlt_w⟩
                rw [hst]
                congr 1; apply Fin.ext; dsimp only
                have he : s.val + w - (start + w) = (P0 - (start + w)) + (s.val + w - P0) := by omega
                have he2 : (s.val - (start + w)) % w = (s.val + w - (start + w)) % w := by
                  rw [show s.val + w - (start + w) = (s.val - (start + w)) + w by omega, Nat.add_mod_right]
                rw [he2, he, Nat.add_mod, hdivP0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt_w]
          · simp only [hsP0, ↓reduceIte, parPat, beq_iff_eq, Fin.val_last]
            have hbit_par : ∀ k : Fin (w + 1),
                fromP x ⟨(s.val + k.val) % n, Nat.mod_lt _ hn⟩ = extU (s.val - P0 + k.val) := by
              intro k
              by_cases hwrap : s.val + k.val < n
              · have hmod : (s.val + k.val) % n = s.val + k.val := Nat.mod_eq_of_lt hwrap
                simp only [hmod]
                rw [hfrom_L (s.val + k.val) (by omega) hwrap]
                dsimp only [tailBit]
                simp only [show ¬ s.val + k.val < start + w by omega,
                  show ¬ s.val + k.val < P0 by omega, ↓reduceIte]
                congr 1; omega
              · have hlt_w : s.val + k.val - n < w := by omega
                have hmod : (s.val + k.val) % n = s.val + k.val - n := by
                  have he : s.val + k.val = (s.val + k.val - n) + n := by omega
                  conv_lhs => rw [he]
                  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt_w (by omega))]
                simp only [hmod]
                rw [hfrom_start ⟨s.val + k.val - n, hlt_w⟩]
                dsimp only [extU]
                have he : s.val - P0 + k.val = (s.val + k.val - n) + q * (w + 1) := by
                  dsimp only [n, P0]; omega
                have hmod2 : (s.val - P0 + k.val) % (w + 1) = s.val + k.val - n := by
                  rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
                have hlt2 : (s.val - P0 + k.val) % (w + 1) < w := by rw [hmod2]; exact hlt_w
                simp only [hlt2, ↓reduceDIte]
                congr 1; apply Fin.ext; exact hmod2.symm
            have hlast := hbit_par (Fin.last w)
            simp only [Fin.val_last] at hlast
            rw [hlast]
            have hwin : (fun j : Fin w => fromP x ⟨(s.val + j.val) % n, Nat.mod_lt _ hn⟩) =
                (fun j : Fin w => extU ((s.val - P0) % (w + 1) + j.val)) := by
              funext j
              have h1 := hbit_par j.castSucc
              simp only [Fin.val_castSucc] at h1
              rw [h1]
              dsimp only [extU]
              have hmod : (s.val - P0 + j.val) % (w + 1) = ((s.val - P0) % (w + 1) + j.val) % (w + 1) :=
                (Nat.mod_add_mod _ _ _).symm
              simp only [hmod]
            change extU (s.val - P0 + w) = xorAll (fun j : Fin w => fromP x ⟨(s.val + j.val) % n, Nat.mod_lt _ hn⟩)
            rw [hwin, xorAll_rot_ext a0 ((s.val - P0) % (w + 1)) (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos w)))]
            dsimp only [extU]
            have hmod : (s.val - P0 + w) % (w + 1) = ((s.val - P0) % (w + 1) + w) % (w + 1) :=
              (Nat.mod_add_mod _ _ _).symm
            simp only [hmod]
    have hbij : (Finset.univ.filter ok).card = (Finset.univ.filter ok383).card := by
      refine Finset.card_bij (fun word _ => toP word) ?_ ?_ ?_
      · intro word hword
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword ⊢
        rcases hok_unique word hword with ⟨h0, htail⟩
        refine ⟨fun k => ⟨?_, ?_⟩, fun i => ?_⟩
        · have hof : Fin.ofNat (L + d + 1) k.val = ⟨k.val, by omega⟩ := by
            apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          rw [hof]; exact h0 k
        · have hof : Fin.ofNat (L + d + 1) (L + k.val) = ⟨L + k.val, by omega⟩ := by
            apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          rw [hof]
          have ht := htail (L + k.val) (by omega) (by omega)
          dsimp only [tailBit] at ht
          have hlt_st : L + k.val < start + w := by dsimp [start]; omega
          simp only [hlt_st, ↓reduceIte] at ht
          simpa [toP, Nat.mod_eq_of_lt k.isLt] using ht
        · have hrow := hword ⟨i.val, by omega⟩
          have hnot_st : ¬ (start ≤ i.val ∧ i.val < start + w) := by dsimp [start]; omega
          simp only [row, hnot_st, ↓reduceIte, ctx, i.isLt, ↓reduceDIte] at hrow
          have heq_pat : (fun off : Fin (w + 1) => toP word (Fin.ofNat (L + d + 1) (i.val + off.val))) =
              (fun off : Fin (w + 1) => word ⟨(i.val + off.val) % n, Nat.mod_lt _ hn⟩) := by
            funext off
            have hlt1 : i.val + off.val < L + w := by omega
            have hlt2 : i.val + off.val < n := by omega
            have hof : Fin.ofNat (L + d + 1) (i.val + off.val) = ⟨i.val + off.val, hlt1⟩ := by
              apply Fin.ext; simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hlt1
            rw [hof]
            simp only [toP, Nat.mod_eq_of_lt hlt2]
          rw [heq_pat]
          exact hrow
      · intro w1 hw1 w2 hw2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
        rcases hok_unique w1 hw1 with ⟨_, ht1⟩
        rcases hok_unique w2 hw2 with ⟨_, ht2⟩
        funext i
        by_cases hi : i.val < L + w
        · exact congrFun heq ⟨i.val, hi⟩
        · rw [ht1 i.val (by omega) i.isLt, ht2 i.val (by omega) i.isLt]
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact ⟨fromP x, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hfrom_ok x hx, hfrom_to x⟩
    rw [hbij, hcard383]

end C051

namespace C053
open BranchingProgram
abbrev Bits (m : Nat) := Fin m → Bool
abbrev Fn (m : Nat) := Bits m → Bool
abbrev Pool (m : Nat) := Finset (Fn m)
def input {m : Nat} (S : Finset (Fin m)) (a x : Bits m) :=
  List.ofFn (fun j => if j ∈ S then x j else a j)
def mix {m : Nat} (v : Fin m) (p : Fn m × Fn m) : Fn m :=
  fun x => if x v then p.2 x else p.1 x
def tCount {m : Nat} (S : Finset (Fin m)) (L : Program) :=
  (L.filter (fun st => st.var ∈ S.image Fin.val)).length

def Valid {m : Nat} (P : Program) (S : Finset (Fin m)) (a : Bits m) (offset : Nat) (G : Pool m) : Prop :=
  (∀ b : Bool, (fun _ => b) ∈ G) ∧
  ∀ i : Nat, offset ≤ i → i < P.length → ∃ g ∈ G,
    ∀ x fuel, P.length-i≤fuel → P.run (input S a x) fuel i=g x

lemma stepValid {m : Nat} {P : Program} {S : Finset (Fin m)} {a : Bits m}
    {q : Nat} {s : State} {G : Pool m} (fr : P.Forward) (reads : P.ReadsBelow m)
    (hs : P[q]?=some s) (hG : Valid P S a (q+1) G) :
    let v : Fin m := ⟨s.var,reads s (List.mem_of_getElem? hs)⟩
    ∃ p ∈ G ×ˢ G,
      if v∈S then Valid P S a q (insert (mix v p) G) else Valid P S a q G := by
  classical
  dsimp only
  let v : Fin m := ⟨s.var,reads s (List.mem_of_getElem? hs)⟩
  have readBit (x : Bits m) : (input S a x).getD s.var false = if v∈S then x v else a v := by
    simp [input,List.getD_eq_getElem?_getD,v,reads s (List.mem_of_getElem? hs)]
  let go (n : Next) (x : Bits m) (fuel : Nat) :=
    match n with
    | .out b => b
    | .state i => P.run (input S a x) fuel i
  have get (n : Next) (chosen : s.lo=n ∨ s.hi=n) :
      ∃ g ∈ G, ∀ x fuel, P.length-q≤fuel+1 → go n x fuel=g x := by
    cases n with
    | out b => exact ⟨_,hG.1 b,by intros;rfl⟩
    | state i =>
      have h := fr q s hs i chosen
      obtain ⟨g,mg,eq⟩:=hG.2 i (by omega) h.2
      exact ⟨g,mg,fun x fuel hf=>eq x fuel (by omega)⟩
  obtain ⟨lo,ml,el⟩:=get s.lo (Or.inl rfl)
  obtain ⟨hi,mh,eh⟩:=get s.hi (Or.inr rfl)
  refine ⟨(lo,hi),Finset.mem_product.mpr ⟨ml,mh⟩,?_⟩
  have current (x : Bits m) (f : Nat) (hf:P.length-q≤f) :
      P.run (input S a x) f q=(if (if v∈S then x v else a v) then hi x else lo x) := by
    have qlt : q<P.length := (List.getElem?_eq_some_iff.mp hs).1
    cases f with
    | zero => omega
    | succ f =>
      simp only [Program.run,hs,readBit x]
      by_cases e : (if v∈S then x v else a v)=true
      · cases ee : s.hi <;> simpa [go,e,ee] using eh x f hf
      · cases ee : s.lo <;> simpa [go,e,ee] using el x f hf
  by_cases inside : v∈S
  · rw [ite_eq_left inside]
    refine ⟨fun b=>Finset.mem_insert_of_mem (hG.1 b),?_⟩
    intro i qi ip
    by_cases e:i=q
    · subst i
      exact ⟨_,Finset.mem_insert_self ..,fun x f hf=>by simpa [inside,mix] using current x f hf⟩
    · obtain ⟨g,mg,h⟩:=hG.2 i (by omega) ip
      exact ⟨g,Finset.mem_insert_of_mem mg,h⟩
  · rw [ite_eq_right inside]
    refine ⟨hG.1,?_⟩
    intro i qi ip
    by_cases e:i=q
    · subst i
      by_cases av:a v=true
      · exact ⟨hi,mh,fun x f hf=>by simpa [inside,av] using current x f hf⟩
      · exact ⟨lo,ml,fun x f hf=>by simpa [inside,av] using current x f hf⟩
    · exact hG.2 i (by omega) ip

lemma bounds {m : Nat} (P : Program) (S : Finset (Fin m)) (fr : P.Forward) (reads : P.ReadsBelow m)
    (T : Program) (q : Nat) (suffix : P.drop q=T) (leq : q≤P.length) :
    ∃ F : Finset (Pool m), F.card≤(Nat.factorial (tCount S T+1))^2 ∧
      (∀ G∈F,G.card≤tCount S T+2) ∧ ∀ a, ∃ G∈F, Valid P S a q G := by
  classical
  induction T generalizing q with
  | nil =>
    let G : Pool m := {fun _=>false,fun _=>true}
    refine ⟨{G},by simp [tCount],?_,?_⟩
    · intro z hz
      obtain rfl:=Finset.mem_singleton.mp hz
      exact (Finset.card_insert_le ..).trans (by simp [tCount])
    · intro a
      have eq:=congrArg List.length suffix
      simp at eq
      exact ⟨G,by simp,fun b=>by cases b <;> simp [G],fun i qi ip=>by omega⟩
  | cons s T ih =>
    have drop : P.drop (q+1)=T := by rw [←List.drop_drop (i:=1) (j:=q),suffix];rfl
    have qlt : q<P.length := by have e:=congrArg List.length suffix;simp at e;omega
    have hs : P[q]?=some s := by
      have e : (P.drop q)[0]?=some s := by rw [suffix];rfl
      simpa only [List.getElem?_drop,Nat.add_zero] using e
    obtain ⟨F,hF,hsize,keep⟩:=ih (q+1) drop (by omega)
    let v : Fin m := ⟨s.var,reads s (List.mem_of_getElem? hs)⟩
    have mem : s.var∈S.image Fin.val ↔ v∈S := by
      constructor
      · rintro h
        obtain ⟨i,mi,e⟩:=Finset.mem_image.mp h
        exact (show i=v from Fin.ext e) ▸ mi
      · intro h
        exact Finset.mem_image.mpr ⟨v,h,rfl⟩
    by_cases hv:v∈S
    · have ct : tCount S (s::T)=tCount S T+1 := by
        unfold tCount
        rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using mem.mpr hv)];rfl
      let ex (G : Pool m) := (G ×ˢ G).image (fun p => insert (mix v p) G)
      refine ⟨F.biUnion ex,?_,?_,?_⟩
      · calc
          (F.biUnion ex).card ≤ ∑ G ∈ F, (ex G).card := Finset.card_biUnion_le
          _ ≤ ∑ _G ∈ F, (tCount S T+2)^2 := by
            apply Finset.sum_le_sum
            intro G mg
            exact (Finset.card_image_le).trans (by rw [Finset.card_product,pow_two];exact Nat.mul_le_mul (hsize G mg) (hsize G mg))
          _ = F.card * (tCount S T+2)^2 := by simp
          _ ≤ (Nat.factorial (tCount S (s::T)+1))^2 := by
            rw [ct,Nat.factorial_succ,mul_pow,Nat.mul_comm]
            exact Nat.mul_le_mul_left _ hF
      · intro H mh
        obtain ⟨G,mg,aa⟩:=Finset.mem_biUnion.mp mh
        obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp aa
        have h:=hsize G mg
        have e:=Finset.card_insert_le (mix v p) G
        rw [ct];omega
      · intro a
        obtain ⟨G,mg,hG⟩:=keep a
        obtain ⟨p,mp,ok⟩:=stepValid fr reads hs hG
        change (if v∈S then Valid P S a q (insert (mix v p) G) else Valid P S a q G) at ok
        exact ⟨_,Finset.mem_biUnion.mpr ⟨G,mg,Finset.mem_image.mpr ⟨p,mp,rfl⟩⟩,by simpa [hv] using ok⟩
    · have nh : s.var∉S.image Fin.val := fun e=>hv (mem.mp e)
      have ct : tCount S (s::T)=tCount S T := by
        unfold tCount
        rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using nh)]
      rw [ct]
      refine ⟨F,hF,hsize,?_⟩
      intro a
      obtain ⟨G,mg,hG⟩:=keep a
      obtain ⟨p,mp,ok⟩:=stepValid fr reads hs hG
      change (if v∈S then Valid P S a q (insert (mix v p) G) else Valid P S a q G) at ok
      exact ⟨G,mg,by simpa [hv] using ok⟩


theorem bp_count :
  ∀ (m : ℕ) (S : Finset (Fin m)) (P : PEqualNP.BranchingProgram.Program),
  P.Forward → P.ReadsBelow m →
  let t := (P.filter (fun st => st.var ∈ S.image Fin.val)).length
  let res := fun (a x : Fin m → Bool) =>
    P.eval (List.ofFn (fun j => if j ∈ S then x j else a j))
  (Finset.univ.image res).card ≤ (t + 2) * (Nat.factorial (t + 1)) ^ 2 := by
  classical
  intro m S P fr reads t res
  obtain ⟨F,cf,cg,keep⟩:=bounds P S fr reads P 0 (by simp) (by omega)
  have cover : Finset.univ.image res ⊆ F.biUnion id := by
    intro g mg
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp mg
    obtain ⟨G,mg,hG⟩:=keep a
    refine Finset.mem_biUnion.mpr ⟨G,mg,?_⟩
    by_cases h:0<P.length
    · obtain ⟨g,mem,eq⟩:=hG.2 0 (by omega) h
      have e : res a=g := funext (fun x=>eq x P.length (by omega))
      change res a ∈ G
      rw [e]
      exact mem
    · have emp : P=[] := List.length_eq_zero_iff.mp (by omega)
      subst P
      exact hG.1 false
  calc
    _ ≤ (F.biUnion id).card := Finset.card_le_card cover
    _ ≤ ∑ G ∈ F,G.card := Finset.card_biUnion_le
    _ ≤ ∑ _G ∈ F,(t+2) := Finset.sum_le_sum cg
    _ = (t+2)*F.card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ cf

end C053

open PEqualNP.BranchingProgram

theorem run_congr (P : Program) (x y : List Bool)
    (hxy : ∀ s ∈ P, x.getD s.var false = y.getD s.var false) :
    ∀ fuel q, P.run x fuel q = P.run y fuel q
  | 0, _ => rfl
  | fuel + 1, q => by
      cases hq : P[q]? with
      | none => simp only [Program.run, hq]
      | some s =>
        have hs : s ∈ P := by
          obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.1 hq
          exact e ▸ List.getElem_mem hlt
        simp only [Program.run, hq]
        rw [hxy s hs]
        generalize (if y.getD s.var false = true then s.hi else s.lo) = nx
        cases nx with
        | out b => rfl
        | state q' => exact run_congr P x y hxy fuel q'

theorem getD_ofFn {m : ℕ} (g : Fin m → Bool) (k : ℕ) :
    (List.ofFn g).getD k false = if h : k < m then g ⟨k, h⟩ else false := by
  by_cases h : k < m
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem res_const {m : ℕ} (S : Finset (Fin m)) (P : Program)
    (h0 : (P.filter (fun st => st.var ∈ S.image Fin.val)).length = 0) (a x x' : Fin m → Bool) :
    P.eval (List.ofFn (fun j => if j ∈ S then x j else a j)) =
      P.eval (List.ofFn (fun j => if j ∈ S then x' j else a j)) := by
  unfold Program.eval
  apply run_congr
  intro s hs
  have hn : ¬ (s.var ∈ S.image Fin.val) := by
    have e := List.length_eq_zero_iff.1 h0
    rw [List.filter_eq_nil_iff] at e
    simpa using e s hs
  rw [getD_ofFn, getD_ofFn]
  by_cases hk : s.var < m
  · have hj : (⟨s.var, hk⟩ : Fin m) ∉ S := by
      intro hm
      exact hn (Finset.mem_image.2 ⟨_, hm, rfl⟩)
    simp [hk, hj]
  · simp [hk]

theorem sum_filter_len {β : Type} [Fintype β] (p : β → State → Bool)
    (hd : ∀ s, (Finset.univ.filter (fun h => p h s = true)).card ≤ 1) :
    ∀ P : List State, ∑ h, (P.filter (p h)).length ≤ P.length
  | [] => by simp
  | s :: P => by
      simp only [← List.countP_eq_length_filter, List.countP_cons, List.length_cons]
      rw [Finset.sum_add_distrib]
      have e1 := sum_filter_len p hd P
      simp only [← List.countP_eq_length_filter] at e1
      have e2 : ∑ h, (if p h s = true then 1 else 0) ≤ 1 := by
        rw [Finset.sum_boole]
        simpa using hd s
      omega

theorem fact_le : ∀ t : ℕ, Nat.factorial (t + 1) ≤ (t + 1) ^ t
  | 0 => by simp
  | t + 1 => by
      rw [Nat.factorial_succ, pow_succ, Nat.mul_comm]
      apply Nat.mul_le_mul_right
      exact (fact_le t).trans (Nat.pow_le_pow_left (by omega) t)

theorem arith (d t : ℕ) (ht : 1 ≤ t)
    (hc : 2 ^ (4 ^ d) ≤ (t + 2) * (Nat.factorial (t + 1)) ^ 2) : 4 ^ d ≤ (4 * d + 2) * t := by
  by_cases hbig : 4 ^ d ≤ t
  · exact hbig.trans (Nat.le_mul_of_pos_left t (by omega))
  · push Not at hbig
    have h4 : (4 : ℕ) ^ d = 2 ^ (2 * d) := by rw [pow_mul]; norm_num
    have hf : Nat.factorial (t + 1) ≤ 2 ^ (2 * d * t) := by
      calc Nat.factorial (t + 1) ≤ (t + 1) ^ t := fact_le t
        _ ≤ (4 ^ d) ^ t := Nat.pow_le_pow_left (by omega) t
        _ = 2 ^ (2 * d * t) := by rw [h4, ← pow_mul]
    have ht2 : t + 2 ≤ 2 ^ (2 * t) := by
      have := Nat.lt_two_pow_self (n := t + 1)
      have h2 : 2 ^ (t + 1) ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 2 ^ (4 ^ d) ≤ 2 ^ ((4 * d + 2) * t) := by
      calc 2 ^ (4 ^ d) ≤ (t + 2) * (Nat.factorial (t + 1)) ^ 2 := hc
        _ ≤ 2 ^ (2 * t) * (2 ^ (2 * d * t)) ^ 2 :=
          Nat.mul_le_mul ht2 (Nat.pow_le_pow_left hf 2)
        _ = 2 ^ ((4 * d + 2) * t) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem card_mat (d : ℕ) : Fintype.card ((Fin d → Bool) → (Fin d → Bool) → Bool) = 2 ^ (4 ^ d) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_mul, (by norm_num : (4 : ℕ) = 2 * 2), mul_pow]

end PEqualNP.Outside.L_clb_109

open PEqualNP.Outside.L_clb_109 in
theorem PEqualNP.Outside.L_clb_109 : ∀ d b p q : ℕ,
  let w := d + 1
  let B := b + 1
  let L := 3 * w * 2 ^ d
  let n := L + B * w + p * w + q * (w + 1)
  let hn : 0 < n := Nat.add_pos_left (Nat.add_pos_left (Nat.add_pos_left (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos 2) (Nat.succ_pos d)) (Nat.pow_pos (Nat.succ_pos 1))) _) _) _
  let stride := 2 ^ (w + 1)
  let I := n * stride
  ∀ P : PEqualNP.BranchingProgram.Program,
    P.Forward → P.ReadsBelow I →
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let x := List.ofFn (fun a : Fin I =>
        table ⟨(a.val / stride) % n, Nat.mod_lt _ hn⟩ (fun j => a.val.testBit j.val))
      P.eval x = true ↔ ∃ word : Fin n → Bool, ∀ i : Fin n,
        table i (fun k => word ⟨(i.val + k.val) % n, Nat.mod_lt _ hn⟩) = true) →
    B * 4 ^ d ≤ (4 * d + 2) * P.size := by
  intro d b p q w B L n hn stride I P hfw hrd hF
  classical
  obtain ⟨ctx, probe, -, hc⟩ := C051.solve_051 d b p q
  let inp : (Fin n → (Fin (w + 1) → Bool) → Bool) → Fin I → Bool := fun table a =>
    table ⟨(a.val / stride) % n, Nat.mod_lt _ hn⟩ (fun j => a.val.testBit j.val)
  let blk : Fin B → Fin I → Bool := fun h a =>
    decide (L + h.val * w ≤ (a.val / stride) % n ∧ (a.val / stride) % n < L + h.val * w + w)
  let Sb : Fin B → Finset (Fin I) := fun h => Finset.univ.filter (fun a => blk h a = true)
  let tb : Fin B → ℕ := fun h => (P.filter (fun st => st.var ∈ (Sb h).image Fin.val)).length
  have per : ∀ h : Fin B, 4 ^ d ≤ (4 * d + 2) * tb h := by
    intro h
    let start := L + h.val * w
    let rowT := fun (A : (Fin d → Bool) → (Fin d → Bool) → Bool) (u v : Fin d → Bool)
        (i : Fin n) (pat : Fin (w + 1) → Bool) =>
      if start ≤ i.val ∧ i.val < start + w then
        probe u v (Fin.ofNat (d + 1) (i.val - start)) pat
      else ctx A i pat
    let res := fun (a x : Fin I → Bool) =>
      P.eval (List.ofFn (fun j => if j ∈ Sb h then x j else a j))
    have hval : ∀ A u v, P.eval (List.ofFn (inp (rowT A u v))) = A u v := by
      intro A u v
      have e := hF (rowT A u v)
      have c := hc A u v h
      cases hA : A u v
      · rw [hA] at c
        by_contra hne
        obtain ⟨word, hw⟩ := e.1 (by simpa using hne)
        have : word ∈ Finset.univ.filter (fun word : Fin n → Bool => ∀ s : Fin n,
            rowT A u v s (fun k => word ⟨(s.val + k.val) % n, Nat.mod_lt _ hn⟩) = true) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩
        have c' : (Finset.univ.filter (fun word : Fin n → Bool => ∀ s : Fin n,
            rowT A u v s (fun k => word ⟨(s.val + k.val) % n, Nat.mod_lt _ hn⟩) = true)).card
            = 0 := c
        rw [Finset.card_eq_zero] at c'
        rw [c'] at this
        simp at this
      · rw [hA] at c
        have c' : (Finset.univ.filter (fun word : Fin n → Bool => ∀ s : Fin n,
            rowT A u v s (fun k => word ⟨(s.val + k.val) % n, Nat.mod_lt _ hn⟩) = true)).card
            = 1 := c
        obtain ⟨word, hw⟩ := Finset.card_pos.1 (by rw [c']; norm_num)
        exact e.2 ⟨word, (Finset.mem_filter.1 hw).2⟩
    have hmerge : ∀ A A0 u v,
        (fun j => if j ∈ Sb h then inp (rowT A0 u v) j else inp (ctx A) j) = inp (rowT A u v) := by
      intro A A0 u v
      funext a
      by_cases hS : start ≤ (a.val / stride) % n ∧ (a.val / stride) % n < start + w
      · have : a ∈ Sb h := Finset.mem_filter.2 ⟨Finset.mem_univ _, decide_eq_true hS⟩
        simp only [this, ite_true, inp, rowT, hS, and_self]
      · have : a ∉ Sb h := by
          intro hm
          exact hS (of_decide_eq_true (Finset.mem_filter.1 hm).2)
        simp only [this, inp, rowT, hS, ite_false]
    have hT0 : ∀ A, res (inp (ctx A)) (inp (fun _ _ => false)) = false := by
      intro A
      let T0 := fun (i : Fin n) (pat : Fin (w + 1) → Bool) =>
        if start ≤ i.val ∧ i.val < start + w then false else ctx A i pat
      have em : (fun j => if j ∈ Sb h then inp (fun _ _ => false) j else inp (ctx A) j)
          = inp T0 := by
        funext a
        by_cases hS : start ≤ (a.val / stride) % n ∧ (a.val / stride) % n < start + w
        · have : a ∈ Sb h := Finset.mem_filter.2 ⟨Finset.mem_univ _, decide_eq_true hS⟩
          simp only [this, ite_true, inp, T0, hS, and_self]
        · have : a ∉ Sb h := by
            intro hm
            exact hS (of_decide_eq_true (Finset.mem_filter.1 hm).2)
          simp only [this, inp, T0, hS, ite_false]
      show P.eval (List.ofFn (fun j => if j ∈ Sb h then inp (fun _ _ => false) j
        else inp (ctx A) j)) = false
      rw [em]
      by_contra hne
      obtain ⟨word, hw⟩ := (hF T0).1 (by simpa using hne)
      have hlt : start < n := by
        have h1 : h.val * w + w ≤ B * w := by
          have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt h.isLt)
          rw [Nat.succ_mul] at this
          exact this
        show L + h.val * w < L + B * w + p * w + q * (w + 1)
        have : 0 < w := Nat.succ_pos d
        omega
      have := hw ⟨start, hlt⟩
      have hw0 : 0 < w := Nat.succ_pos d
      simp only [T0, le_refl, true_and, Nat.lt_add_of_pos_right hw0, ite_true] at this
      exact absurd this (by simp)
    have hfa : ∀ A u v, res (inp (ctx A)) (inp (rowT (fun _ _ => false) u v)) = A u v := by
      intro A u v
      show P.eval (List.ofFn (fun j => if j ∈ Sb h then inp (rowT (fun _ _ => false) u v) j
        else inp (ctx A) j)) = _
      rw [hmerge]
      exact hval A u v
    have hcnt := C053.bp_count I (Sb h) P hfw hrd
    have hsub : (Finset.univ.image (fun A : (Fin d → Bool) → (Fin d → Bool) → Bool =>
        res (inp (ctx A)))) ⊆ Finset.univ.image res := by
      intro f hf
      obtain ⟨A, _, rfl⟩ := Finset.mem_image.1 hf
      exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
    have hinj : Function.Injective (fun A : (Fin d → Bool) → (Fin d → Bool) → Bool =>
        res (inp (ctx A))) := by
      intro A A' e
      funext u v
      have := congrFun e (inp (rowT (fun _ _ => false) u v))
      simp only [hfa] at this
      exact this
    have c1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, card_mat] at c1
    have ht : 1 ≤ tb h := by
      by_contra h0
      have h0' : tb h = 0 := by omega
      have := res_const (Sb h) P h0' (inp (ctx (fun _ _ => true)))
        (inp (rowT (fun _ _ => false) (fun _ => false) (fun _ => false))) (inp (fun _ _ => false))
      have e1 := hfa (fun _ _ => true) (fun _ => false) (fun _ => false)
      have e2 := hT0 (fun _ _ => true)
      simp only [res] at e1 e2
      rw [this, e2] at e1
      exact absurd e1 (by simp)
    exact arith d (tb h) ht (c1.trans hcnt)
  have hd : ∀ s : PEqualNP.BranchingProgram.State, (Finset.univ.filter (fun h : Fin B =>
      decide (s.var ∈ (Sb h).image Fin.val) = true)).card ≤ 1 := by
    intro s
    apply Finset.card_le_one.2
    intro h1 m1 h2 m2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      Finset.mem_image, Sb, blk] at m1 m2
    obtain ⟨a1, k1, e1⟩ := m1
    obtain ⟨a2, k2, e2⟩ := m2
    have ea : a1 = a2 := Fin.ext (e1.trans e2.symm)
    subst ea
    apply Fin.ext
    rcases Nat.lt_trichotomy h1.val h2.val with lt | eq | gt
    · exfalso
      have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt lt)
      rw [Nat.succ_mul] at this
      omega
    · exact eq
    · exfalso
      have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt gt)
      rw [Nat.succ_mul] at this
      omega
  have total := sum_filter_len (fun h st => decide (st.var ∈ (Sb h).image Fin.val)) hd P
  calc B * 4 ^ d = ∑ _h : Fin B, 4 ^ d := by simp
    _ ≤ ∑ h, (4 * d + 2) * tb h := Finset.sum_le_sum (fun h _ => per h)
    _ = (4 * d + 2) * ∑ h, tb h := by rw [Finset.mul_sum]
    _ ≤ (4 * d + 2) * P.size := Nat.mul_le_mul_left _ total

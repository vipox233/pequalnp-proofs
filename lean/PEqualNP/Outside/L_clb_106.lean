import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_106_aux.TaggedTransfer
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

end PEqualNP.Outside.L_clb_106_aux.TaggedTransfer

namespace PEqualNP.Outside.L_clb_106_aux.TaggedTransfer
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

end PEqualNP.Outside.L_clb_106_aux.TaggedTransfer

namespace PEqualNP.Outside.L_clb_106_aux.TaggedTransfer
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
    change f ⟨(i.val*w+j.val)/w,_⟩ ⟨(i.val*w+j.val) % w,_⟩=f i j
    congr 1
    · apply Fin.ext;simp [Nat.add_comm _ j.val,Nat.add_mul_div_right,Nat.div_eq_of_lt j.isLt,hw]
    · apply Fin.ext;simp [Nat.mod_eq_of_lt j.isLt]

end PEqualNP.Outside.L_clb_106_aux.TaggedTransfer

namespace PEqualNP.Outside.L_clb_106_aux.TaggedTransfer
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

end PEqualNP.Outside.L_clb_106_aux.TaggedTransfer

namespace PEqualNP.Outside.L_clb_106_aux.TaggedTransfer
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

end PEqualNP.Outside.L_clb_106_aux.TaggedTransfer


namespace PEqualNP.Outside.L_clb_106_aux
open TaggedTransfer in
theorem taggedTransfer : ∀ d : ℕ,
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

end PEqualNP.Outside.L_clb_106_aux


namespace PEqualNP.Outside.L_clb_106_aux

abbrev W (n : ℕ) := Fin n → Bool
abbrev Rows (w k : ℕ) := Fin k → W (w + 1) → Bool

def glue {α : Type*} {m n : ℕ} (x : Fin m → α) (y : Fin n → α) (i : Fin (m+n)) : α :=
  if h : i.val < m then x ⟨i.val,h⟩ else y ⟨i.val-m,by omega⟩

def leftPart {α : Type*} {m n : ℕ} (x : Fin (m+n) → α) (i : Fin m) : α := x ⟨i.val,by omega⟩

def rightPart {α : Type*} {m n : ℕ} (x : Fin (m+n) → α) (j : Fin n) : α := x ⟨m+j.val,by omega⟩

@[simp] lemma left_glue {α : Type*} {m n : ℕ} (x : Fin m → α) (y : Fin n → α) :
    leftPart (glue x y) = x := by
  funext i
  simp [leftPart, glue, i.isLt]

@[simp] lemma right_glue {α : Type*} {m n : ℕ} (x : Fin m → α) (y : Fin n → α) :
    rightPart (glue x y) = y := by
  funext i
  simp [rightPart, glue]

@[simp] lemma glue_parts {α : Type*} {m n : ℕ} (x : Fin (m+n) → α) :
    glue (leftPart x) (rightPart x) = x := by
  funext i
  dsimp [glue, leftPart, rightPart]
  split_ifs with h
  · rfl
  · congr 1; apply Fin.ext; dsimp; omega

def feed {m : ℕ} (x : W m) (tail : ℕ → Bool) (i : ℕ) : Bool :=
  if h : i < m then x ⟨i,h⟩ else tail (i-m)

def extend {w : ℕ} (b : W w) (i : ℕ) : Bool := if h : i < w then b ⟨i,h⟩ else false

def readWord {m w : ℕ} (x : W m) (b : W w) (i : ℕ) : Bool := feed x (extend b) i

def initial {m w : ℕ} (x : W m) (b : W w) : W w := fun j => readWord x b j.val

def valid {m w : ℕ} (P : Rows w m) (x : W m) (b : W w) : Prop :=
  ∀ i, P i (fun j => readWord x b (i.val+j.val)) = true

def path {m w : ℕ} (P : Rows w m) (a b : W w) (x : W m) : Prop := initial x b = a ∧ valid P x b

noncomputable def count {m w : ℕ} (P : Rows w m) (a b : W w) : ℕ := by
  classical exact Fintype.card {x : W m // path P a b x}

lemma feed_glue {m n : ℕ} (x : W m) (y : W n) (tail : ℕ → Bool) (i : ℕ) :
    feed (glue x y) tail i = feed x (feed y tail) i := by
  by_cases h : i < m
  · have h' : i < m+n := by omega
    simp [feed,glue,h,h']
  · by_cases h' : i < m+n
    · have h'' : i-m<n := by omega
      simp [feed,glue,h,h',h'']
    · have h'' : ¬i-m<n := by omega
      simp [feed,glue,h,h',h'',Nat.sub_sub]

lemma read_glue_left {m n w : ℕ} (x : W m) (y : W n) (c : W w) {i : ℕ} (hi : i < m+w) :
    readWord (glue x y) c i = readWord x (initial y c) i := by
  unfold readWord
  rw [feed_glue]
  by_cases h : i<m
  · simp [feed,h]
  · have h' : i-m<w := by omega
    simp [feed,h,extend,h',initial,readWord]

lemma read_glue_right {m n w : ℕ} (x : W m) (y : W n) (c : W w) (i : ℕ) :
    readWord (glue x y) c (m+i) = readWord y c i := by
  unfold readWord
  rw [feed_glue]
  simp [feed]

lemma initial_glue {m n w : ℕ} (x : W m) (y : W n) (c : W w) :
    initial (glue x y) c = initial x (initial y c) := by
  funext i
  exact read_glue_left x y c (by omega)

lemma valid_glue {m n w : ℕ} (P : Rows w m) (Q : Rows w n) (x : W m) (y : W n) (c : W w) :
    valid (glue P Q) (glue x y) c ↔ valid P x (initial y c) ∧ valid Q y c := by
  have hl (i : Fin m) : (fun j : Fin (w+1) => readWord (glue x y) c (i.val+j.val)) =
      (fun j => readWord x (initial y c) (i.val+j.val)) := by
    funext j; apply read_glue_left; omega
  have hr (k : Fin n) : (fun j : Fin (w+1) => readWord (glue x y) c (m+k.val+j.val)) =
      (fun j => readWord y c (k.val+j.val)) := by
    funext j; rw [Nat.add_assoc,read_glue_right]
  constructor
  · intro h
    constructor
    · intro i
      have e := h ⟨i.val,by omega⟩
      simpa [glue,i.isLt,hl i] using e
    · intro k
      have e := h ⟨m+k.val,by omega⟩
      simpa [glue,hr k] using e
  · rintro ⟨hp,hq⟩ ⟨i,hi⟩
    by_cases h : i<m
    · simpa [glue,h,hl ⟨i,h⟩] using hp ⟨i,h⟩
    · let k : Fin n := ⟨i-m,by omega⟩
      have hk : i=m+k.val := by dsimp [k]; omega
      have ans : (glue P Q) ⟨m+k.val,by omega⟩
          (fun j => readWord (glue x y) c (m+k.val+j.val)) = true := by
        simpa [glue,hr k] using hq k
      simpa only [← hk] using ans

lemma path_glue {m n w : ℕ} (P : Rows w m) (Q : Rows w n) (a c : W w) (x : W m) (y : W n) :
    path (glue P Q) a c (glue x y) ↔ path P a (initial y c) x ∧ valid Q y c := by
  simp only [path,initial_glue,valid_glue,and_assoc]

lemma count_glue {m n w : ℕ} (P : Rows w m) (Q : Rows w n) (a c : W w) :
    count (glue P Q) a c = ∑ b : W w, count P a b * count Q b c := by
  classical
  let f (z : {z // path (glue P Q) a c z}) :
      Σ b : W w, {x // path P a b x} × {y // path Q b c y} := by
    let x := leftPart (m:=m) (n:=n) z.val
    let y := rightPart (m:=m) (n:=n) z.val
    have h := (path_glue P Q a c x y).mp (by simpa [x,y] using z.prop)
    exact ⟨initial y c, ⟨x,h.1⟩, ⟨y,rfl,h.2⟩⟩
  let g (z : Σ b : W w, {x // path P a b x} × {y // path Q b c y}) :
      {z // path (glue P Q) a c z} := by
    rcases z with ⟨b,⟨x,hx⟩,⟨y,hy,hv⟩⟩
    exact ⟨glue x y,(path_glue P Q a c x y).mpr ⟨hy.symm ▸ hx,hv⟩⟩
  have hfg : Function.LeftInverse g f := by
    intro z
    apply Subtype.ext
    exact glue_parts z.val
  have uniq {s t : Σ b : W w, {x // path P a b x} × {y // path Q b c y}}
      (hu : s.2.1.val = t.2.1.val) (hv : s.2.2.val = t.2.2.val) : s=t := by
    rcases s with ⟨b,⟨x,hx⟩,⟨y,hy,vy⟩⟩
    rcases t with ⟨b2,⟨x2,hx2⟩,⟨y2,hy2,vy2⟩⟩
    dsimp at hu hv
    subst x2; subst y2; subst b; subst b2; rfl
  have hgf : Function.RightInverse g f := by
    rintro ⟨b,⟨x,hx⟩,⟨y,hy,hv⟩⟩
    apply uniq
    · exact left_glue x y
    · exact right_glue x y
  have hc := Fintype.card_congr (Equiv.mk f g hfg hgf)
  simpa only [count,Fintype.card_sigma,Fintype.card_prod] using hc

def cyclicAt {n : ℕ} (hn : 0<n) (x : W n) (t : ℕ) : Bool := x ⟨t % n,Nat.mod_lt _ hn⟩

abbrev cyclic {n w : ℕ} (hn : 0<n) (P : Rows w n) (x : W n) : Prop :=
  ∀ i, P i (fun j => cyclicAt hn x (i.val+j.val)) = true

lemma count_ring {n w : ℕ} (hn : 0<n) (hw : w≤n) (P : Rows w n) :
    (Finset.univ.filter (cyclic hn P)).card = ∑ a : W w, count P a a := by
  classical
  let head (x : W n) : W w := fun j => cyclicAt hn x j.val
  have ini (x : W n) (a : W w) : initial x a = head x := by
    funext j
    have hj : j.val<n := by omega
    simp [initial,readWord,feed,head,cyclicAt,hj,Nat.mod_eq_of_lt hj]
  have rd (x : W n) {i : ℕ} (hi : i<n+w) : readWord x (head x) i = cyclicAt hn x i := by
    by_cases h : i<n
    · simp [readWord,feed,cyclicAt,h,Nat.mod_eq_of_lt h]
    · have hiw : i-n<w := by omega
      have hi' : i % n=(i-n) % n := Nat.mod_eq_sub_mod (by omega)
      simp [readWord,feed,h,extend,hiw,head,cyclicAt,hi']
  have cond (x : W n) : valid P x (head x) ↔ cyclic hn P x := by
    unfold valid cyclic
    have e (i : Fin n) : (fun j : Fin (w+1) => readWord x (head x) (i.val+j.val)) =
        (fun j => cyclicAt hn x (i.val+j.val)) := by funext j; apply rd; omega
    simp only [e]
  let equiv : {x // cyclic hn P x} ≃ Σ a : W w, {x // path P a a x} := {
    toFun := fun ⟨x,h⟩ => ⟨head x, ⟨x, ini x _, (cond x).mpr h⟩⟩
    invFun := fun ⟨a,⟨x,h,hv⟩⟩ => ⟨x, (cond x).mp (by rwa [(ini x a).symm.trans h])⟩
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨a,⟨x,h,hv⟩⟩
      have eq : head x = a := (ini x a).symm.trans h
      subst a
      rfl }
  simpa only [Fintype.card_subtype,Fintype.card_sigma,count] using Fintype.card_congr equiv

lemma id_count {w n : ℕ} (P : Rows w n) (xs : W w → W n)
    (hi : ∀ b, initial (xs b) b = b) (hv : ∀ b x, valid P x b ↔ x=xs b) (a b : W w) :
    count P a b = if a=b then 1 else 0 := by
  classical
  have h (x : W n) : path P a b x ↔ x=xs b ∧ a=b := by
    rw [path,hv]; constructor
    · rintro ⟨e,rfl⟩; exact ⟨rfl, e.symm.trans (hi b)⟩
    · rintro ⟨rfl,rfl⟩; exact ⟨hi _,rfl⟩
  simp only [count,Fintype.card_subtype,h]
  by_cases e : a=b <;> simp [e,Finset.filter_eq,Finset.filter_eq']

def Padding (w n : ℕ) : Prop := ∃ P : Rows w n, ∀ a b, count P a b = if a=b then 1 else 0

lemma pad_zero (w : ℕ) : Padding w 0 := by
  let P : Rows w 0 := fun i => Fin.elim0 i
  refine ⟨P,id_count P (fun _ i => Fin.elim0 i) ?_ ?_⟩
  · intro b; funext j; simp [initial,readWord,feed,extend,j.isLt]
  · intro b x; constructor
    · intro _; exact Subsingleton.elim _ _
    · intro _ i; exact Fin.elim0 i

lemma pad_add {w m n : ℕ} (hm : Padding w m) (hn : Padding w n) : Padding w (m+n) := by
  classical
  obtain ⟨P,hP⟩ := hm
  obtain ⟨Q,hQ⟩ := hn
  refine ⟨glue P Q,fun a b => ?_⟩
  rw [count_glue]
  simp [hP,hQ,ite_mul]

lemma pad_mult {w n : ℕ} (h : Padding w n) (p : ℕ) : Padding w (p*n) := by
  induction p with
  | zero => simpa using pad_zero w
  | succ p ih => simpa only [Nat.succ_mul] using pad_add ih h

def firstLast {w : ℕ} (pat : W (w+1)) : Bool := pat 0 == pat (Fin.last w)

lemma pad_copy (w : ℕ) : Padding w w := by
  let P : Rows w w := fun _ => firstLast
  refine ⟨P,id_count P id ?_ ?_⟩
  · intro b; funext j; simp [initial,readWord,feed,j.isLt]
  · intro b x
    have row (i : Fin w) : P i (fun j => readWord x b (i.val+j.val)) = true ↔ x i = b i := by
      have hi : ¬i.val+w<w := by omega
      simp [P,firstLast,readWord,feed,extend,hi,i.isLt]
    simp only [valid,row,id_eq,funext_iff]

def ones {w : ℕ} (x : W w) : ℕ := (List.ofFn x).count true

def evenBits {w : ℕ} (pat : W w) : Bool := decide (ones pat % 2 = 0)

def window {w : ℕ} (f : ℕ → Bool) (i : ℕ) : W w := fun j => f (i+j.val)

lemma adjacent_ones {w : ℕ} (f : ℕ → Bool) (i : ℕ) :
    ones (window (w:=w+1) f i) = ones (window (w:=w) f (i+1)) + (f i).toNat ∧
    ones (window (w:=w+1) f (i+1)) = ones (window (w:=w) f (i+1)) + (f (i+w+1)).toNat := by
  constructor
  · unfold ones
    rw [List.ofFn_succ]
    have hh : (fun j : Fin w => window f i j.succ) = window (w:=w) f (i+1) := by
      funext j; unfold window; congr 1; simp; omega
    rw [hh,List.count_cons]
    simp [window,Bool.toNat]
  · unfold ones
    rw [List.ofFn_succ' (window (w:=w+1) f (i+1)),List.concat_eq_append,List.count_append,List.count_singleton]
    have hh : (fun j : Fin w => window f (i+1) j.castSucc) = window (w:=w) f (i+1) := rfl
    rw [hh]
    simp [window,Bool.toNat,Nat.add_right_comm]

lemma adjacent_parity {w : ℕ} (f : ℕ → Bool) (i : ℕ)
    (h : evenBits (window (w:=w+1) f i) = true) :
    evenBits (window (w:=w+1) f (i+1)) = true ↔ f i=f (i+w+1) := by
  have ⟨h1,h2⟩ := adjacent_ones (w:=w) f i
  simp only [evenBits,decide_eq_true_eq,h1,h2] at h ⊢
  cases he : f i <;> cases hf : f (i+w+1) <;> simp [he,hf,Bool.toNat] at h ⊢ <;> omega

def parityWord {w : ℕ} (b : W w) : W (w+1) := Fin.snoc b (decide (ones b % 2 = 1))

lemma parity_word_even {w : ℕ} (b : W w) : evenBits (parityWord b) = true := by
  have e : ones (parityWord b) = ones b + (if ones b % 2 = 1 then 1 else 0) := by
    unfold ones parityWord
    rw [List.ofFn_succ' (Fin.snoc b _),List.concat_eq_append,List.count_append,List.count_singleton]
    simp [ones]
  simp only [evenBits,decide_eq_true_eq,e]
  split_ifs <;> omega

lemma pad_parity (w : ℕ) : Padding w (w+1) := by
  let P : Rows w (w+1) := fun _ => evenBits
  have fst (x : W (w+1)) (b : W w) : window (w:=w+1) (readWord x b) 0 = x := by
    funext j; simp [window,readWord,feed,j.isLt]
  have endpoints (x : W (w+1)) (b : W w) (i : Fin w) :
      readWord x b i.val = x i.castSucc ∧ readWord x b (i.val+w+1)=b i := by
    have hi : i.val<w+1 := by omega
    have hi' : ¬i.val+w+1<w+1 := by omega
    constructor
    · simp only [readWord,feed,hi,dif_pos]; congr 1
    · simp [readWord,feed,hi',extend,i.isLt]
  refine ⟨P,id_count P parityWord ?_ ?_⟩
  · intro b; funext i
    change readWord (parityWord b) b i.val=b i
    rw [(endpoints _ _ i).1]; exact Fin.snoc_castSucc _ _ _
  · intro b x
    constructor
    · intro h
      have hr (i : Fin (w+1)) : evenBits (window (w:=w+1) (readWord x b) i.val)=true := h i
      have base (i : Fin w) : x i.castSucc=b i := by
        have hnext := (adjacent_parity (w:=w) (readWord x b) i.val (hr i.castSucc)).mp (hr i.succ)
        rwa [(endpoints x b i).1,(endpoints x b i).2] at hnext
      have hv := hr 0
      change evenBits (window (readWord x b) 0)=true at hv
      rw [fst] at hv
      have ex : ones x = ones b + (x (Fin.last w)).toNat := by
        unfold ones
        rw [List.ofFn_succ' x,List.concat_eq_append,List.count_append,List.count_singleton]
        simp [base,Bool.toNat]
      have last : x (Fin.last w) = decide (ones b % 2=1) := by
        simp only [evenBits,decide_eq_true_eq,ex] at hv
        cases he : x (Fin.last w) <;> simp [he,Bool.toNat] at hv ⊢ <;> omega
      funext i
      exact Fin.lastCases (by simpa [parityWord] using last) (fun j => by simpa [parityWord] using base j) i
    · rintro rfl
      intro i
      have hall (t : ℕ) (ht : t<w+1) : evenBits (window (w:=w+1) (readWord (parityWord b) b) t)=true := by
        induction t with
        | zero => rw [fst]; exact parity_word_even b
        | succ t ih =>
          apply (adjacent_parity (w:=w) _ t (ih (by omega))).mpr
          let j : Fin w := ⟨t,by omega⟩
          have ⟨e1,e2⟩ := endpoints (parityWord b) b j
          change readWord (parityWord b) b j.val=readWord (parityWord b) b (j.val+w+1)
          rw [e1,e2]; exact Fin.snoc_castSucc _ _ _
      exact hall i.val i.isLt

abbrev Mat (d : ℕ) := W d → W d → Bool
abbrev len (d : ℕ) := 3*(d+1)*2^d
abbrev payload {d : ℕ} (a : W (d+1)) : W d := fun j => a j.succ

def projected {d m : ℕ} (E : Mat d → Rows (d+1) m) : Prop :=
  ∀ i p, (∃ c : Bool, ∀ M, E M i p = c) ∨ ∃ u v : W d, ∀ M, E M i p = M u v

abbrev fullOk {d m : ℕ} (P : Rows (d+1) m) (a b : W (d+1)) (z : W (m+(d+1))) :=
  (∀ j : Fin (d+1), z (Fin.ofNat (m+d+1) j.val) = a j ∧ z (Fin.ofNat (m+d+1) (m+j.val)) = b j) ∧
    ∀ i : Fin m, P i (fun j => z (Fin.ofNat (m+d+1) (i.val+j.val))) = true

lemma full_read {d m : ℕ} (x : W m) (b : W (d+1)) {t : ℕ} (h : t<m+(d+1)) :
    glue x b (Fin.ofNat (m+d+1) t) = readWord x b t := by
  have he : Fin.ofNat (m+d+1) t = (⟨t,h⟩ : Fin (m+(d+1))) :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  rw [he]
  by_cases hm : t<m
  · simp [glue,readWord,feed,hm]
  · have hd : t-m<d+1 := by omega
    simp [glue,readWord,feed,extend,hm,hd]

lemma full_glue {d m : ℕ} (P : Rows (d+1) m) (a b c : W (d+1)) (x : W m) :
    fullOk P a b (glue x c) ↔ path P a c x ∧ c=b := by
  have h0 (j : Fin (d+1)) : glue x c (Fin.ofNat (m+d+1) j.val) = initial x c j := full_read x c (by omega)
  have he (j : Fin (d+1)) : glue x c (Fin.ofNat (m+d+1) (m+j.val)) = c j := by
    rw [full_read x c (by omega)]
    simp [readWord,feed,extend,j.isLt]
  have hrows (i : Fin m) : (fun j : Fin (d+1+1) => glue x c (Fin.ofNat (m+d+1) (i.val+j.val))) =
      (fun j => readWord x c (i.val+j.val)) := by funext j; apply full_read; omega
  simp only [fullOk,h0,he,hrows,path,valid,funext_iff]
  grind

lemma full_count {d m : ℕ} (P : Rows (d+1) m) (a b : W (d+1)) :
    (Finset.univ.filter (fullOk P a b)).card = count P a b := by
  classical
  have hc (z : W (m+(d+1))) : fullOk P a b z ↔
      path P a (rightPart z) (leftPart z) ∧ rightPart z=b := by
    simpa only [glue_parts] using full_glue P a b (rightPart z) (leftPart z)
  let e : {z // fullOk P a b z} ≃ {x // path P a b x} := {
    toFun := fun ⟨z,hz⟩ => ⟨leftPart z, by simpa only [((hc z).mp hz).2] using ((hc z).mp hz).1⟩
    invFun := fun ⟨x,hx⟩ => ⟨glue x b,(full_glue P a b b x).mpr ⟨hx,rfl⟩⟩
    left_inv := by
      rintro ⟨z,hz⟩; apply Subtype.ext
      have h := ((hc z).mp hz).2
      change glue (leftPart z) b = z
      rw [←h,glue_parts]
    right_inv := by rintro ⟨x,hx⟩; apply Subtype.ext; exact left_glue x b }
  simpa only [count,Fintype.card_subtype] using Fintype.card_congr e

lemma transfer (d : ℕ) : ∃ E : Mat d → Rows (d+1) (len d), projected E ∧
    ∀ A a b, count (E A) a b = (if a=b then 1 else 0) +
      (if a 0=false ∧ b 0=true ∧ A (payload a) (payload b)=true then 1 else 0) := by
  obtain ⟨E,hE,hc⟩ := taggedTransfer d
  exact ⟨E,hE,fun A a b => (full_count (E A) a b).symm.trans (hc A a b)⟩

def pin {d m : ℕ} (tag : Bool) (P : Rows (d+1) m) : Rows (d+1) m :=
  fun i pat => if i.val=0 ∧ pat 0≠tag then false else P i pat

lemma pin_count {d m : ℕ} (hm : 0<m) (tag : Bool) (P : Rows (d+1) m) (a b : W (d+1)) :
    count (pin tag P) a b = if a 0=tag then count P a b else 0 := by
  classical
  have hpath (x : W m) : path (pin tag P) a b x ↔ path P a b x ∧ a 0=tag := by
    constructor
    · rintro ⟨ha,hv⟩
      have hz : readWord x b 0=a 0 := congrFun ha 0
      have tagok : a 0=tag := by
        by_contra h
        have t := hv ⟨0,hm⟩
        simp [pin,hz,h] at t
      refine ⟨⟨ha,?_⟩,tagok⟩
      intro i
      have t := hv i
      unfold pin at t
      split at t
      · contradiction
      · exact t
    · rintro ⟨⟨ha,hv⟩,ht⟩
      refine ⟨ha,fun i => ?_⟩
      have hz : readWord x b 0=tag := (congrFun ha 0).trans ht
      have h : ¬(i.val=0 ∧ readWord x b (i.val+0)≠tag) := by
        rintro ⟨e,ne⟩; apply ne; simpa [e] using hz
      simpa only [pin,Fin.val_zero,h,ite_false] using hv i
  by_cases h : a 0=tag <;> simp [count,Fintype.card_subtype,hpath,h]

def neg {n : ℕ} (x : W n) : W n := fun j => !(x j)

@[simp] lemma neg_neg {n : ℕ} (x : W n) : neg (neg x)=x := by funext j; simp [neg]

@[simp] lemma neg_eq_neg {n : ℕ} (a b : W n) : neg a=neg b ↔ a=b := by
  constructor
  · intro h; simpa only [neg_neg] using congrArg neg h
  · rintro rfl; rfl

def flipRows {w m : ℕ} (P : Rows w m) : Rows w m := fun i pat => P i (neg pat)

lemma read_neg {w m : ℕ} (x : W m) (b : W w) {t : ℕ} (ht : t<m+w) :
    readWord (neg x) (neg b) t = !(readWord x b t) := by
  by_cases h : t<m
  · simp [neg,readWord,feed,h]
  · have h' : t-m<w := by omega
    simp [neg,readWord,feed,extend,h,h']

lemma flip_count {w m : ℕ} (P : Rows w m) (a b : W w) :
    count (flipRows P) a b = count P (neg a) (neg b) := by
  classical
  have hp (x : W m) : path (flipRows P) a b x ↔ path P (neg a) (neg b) (neg x) := by
    have hi : initial (neg x) (neg b) = neg (initial x b) := by funext j; apply read_neg; omega
    have hr (i : Fin m) : (fun j : Fin (w+1) => readWord (neg x) (neg b) (i.val+j.val)) =
        neg (fun j => readWord x b (i.val+j.val)) := by funext j; apply read_neg; omega
    simp only [path,hi,neg_eq_neg,valid,hr,flipRows]
  let e : {x // path (flipRows P) a b x} ≃ {y // path P (neg a) (neg b) y} := {
    toFun := fun ⟨x,hx⟩ => ⟨neg x,(hp x).mp hx⟩
    invFun := fun ⟨y,hy⟩ => ⟨neg y,(hp (neg y)).mpr (by simpa only [neg_neg] using hy)⟩
    left_inv := fun x => Subtype.ext (neg_neg x.val)
    right_inv := fun y => Subtype.ext (neg_neg y.val) }
  exact Fintype.card_congr e

lemma combine_proj {d m n : ℕ} {P : Mat d → Rows (d+1) m} {Q : Mat d → Rows (d+1) n}
    (hP : projected P) (hQ : projected Q) : projected (fun A => glue (P A) (Q A)) := by
  intro i pat
  by_cases h : i.val<m
  · simpa [glue,h] using hP ⟨i.val,h⟩ pat
  · simpa [glue,h] using hQ ⟨i.val-m,by omega⟩ pat

lemma pin_proj {d m : ℕ} {P : Mat d → Rows (d+1) m} (hP : projected P) (t : Bool) :
    projected (fun A => pin t (P A)) := by
  intro i pat
  by_cases h : i.val=0 ∧ pat 0≠t
  · exact Or.inl ⟨false,fun _ => by simp [pin,h]⟩
  · simpa [pin,h] using hP i pat

def reverseMat {d : ℕ} (B : Mat d) : Mat d := fun x y => B (neg y) (neg x)

lemma back_proj {d m : ℕ} {P : Mat d → Rows (d+1) m} (hp : projected P) :
    projected (fun B => flipRows (P (reverseMat B))) := by
  intro i pat
  rcases hp i (neg pat) with ⟨c,h⟩ | ⟨u,v,h⟩
  · exact Or.inl ⟨c,fun M => h (reverseMat M)⟩
  · exact Or.inr ⟨neg v,neg u,fun M => h (reverseMat M)⟩

lemma fixed_proj {d k : ℕ} (P : Rows (d+1) k) : projected (fun _ : Mat d => P) :=
  fun i p => Or.inl ⟨P i p,fun _ => rfl⟩

lemma remove_pad {m n w : ℕ} (P : Rows w m) (Q : Rows w n)
    (hQ : ∀ a b, count Q a b=if a=b then 1 else 0) (a b : W w) :
    count (glue P Q) a b = count P a b := by
  classical
  rw [count_glue]
  simp [hQ,mul_ite]

def state {d : ℕ} (t : Bool) (u : W d) : W (d+1) := Fin.cases t u

@[simp] lemma state_zero {d : ℕ} (t : Bool) (u : W d) : state t u 0=t := rfl

@[simp] lemma payload_state {d : ℕ} (t : Bool) (u : W d) : payload (state t u)=u := by
  funext j; rfl

@[simp] lemma state_eq {d : ℕ} (t r : Bool) (u v : W d) : state t u=state r v ↔ t=r ∧ u=v := by
  constructor
  · intro h; exact ⟨congrFun h 0,by simpa only [payload_state] using congrArg payload h⟩
  · rintro ⟨rfl,rfl⟩; rfl

@[simp] lemma neg_state {d : ℕ} (t : Bool) (u : W d) : neg (state t u) = state (!t) (neg u) := by
  funext j; exact Fin.cases rfl (fun _ => rfl) j

lemma sum_states {d : ℕ} (f : W (d+1) → ℕ) :
    ∑ s, f s = (∑ u : W d, f (state false u)) + (∑ u : W d, f (state true u)) := by
  classical
  let e : (Bool × W d) ≃ W (d+1) := {
    toFun := fun z => state z.1 z.2
    invFun := fun s => (s 0,payload s)
    left_inv := by rintro ⟨t,u⟩; simp
    right_inv := by intro s; funext j; exact Fin.cases rfl (fun _ => rfl) j }
  rw [← Equiv.sum_comp e f,Fintype.sum_prod_type,Fintype.sum_bool]
  exact Nat.add_comm _ _

abbrev splitOk {m n w : ℕ} (hp : 0<m+n) (P : Rows w m) (Q : Rows w n) (x : W (m+n)) :=
  (∀ i, P i (fun j => cyclicAt hp x (i.val+j.val))=true) ∧
   ∀ k, Q k (fun j => cyclicAt hp x (m+k.val+j.val))=true

lemma split_iff {m n w : ℕ} (hp : 0<m+n) (P : Rows w m) (Q : Rows w n) (x : W (m+n)) :
    splitOk hp P Q x ↔ cyclic hp (glue P Q) x := by
  constructor
  · rintro ⟨h1,h2⟩ ⟨t,ht⟩
    by_cases h : t<m
    · simpa [glue,h] using h1 ⟨t,h⟩
    · let j : Fin n := ⟨t-m,by omega⟩
      have he : t=m+j.val := by dsimp [j]; omega
      have ans : glue P Q ⟨m+j.val,by omega⟩ (fun k => cyclicAt hp x (m+j.val+k.val))=true := by
        simpa [glue] using h2 j
      simpa only [←he] using ans
  · intro h
    constructor
    · intro i; simpa [glue,i.isLt] using h ⟨i.val,by omega⟩
    · intro j; simpa [glue] using h ⟨m+j.val,by omega⟩

lemma tables (d p q : ℕ) :
    let m := len d
    let n := m+p*(d+1)+q*(d+1+1)
    let hn : 0<m+n := by dsimp [m,n,len]; positivity
    ∃ (F : Mat d → Rows (d+1) m) (G : Mat d → Rows (d+1) n), projected F ∧ projected G ∧
      ∀ A B, (Finset.univ.filter (splitOk hn (F A) (G B))).card =
        (Finset.univ.filter (fun z : W d × W d => A z.1 z.2=true ∧ B z.1 z.2=true)).card := by
  classical
  intro m n hn
  obtain ⟨E,hE,hcount⟩ := transfer d
  obtain ⟨P,hP⟩ := pad_mult (pad_copy (d+1)) p
  obtain ⟨Q,hQ⟩ := pad_mult (pad_parity (d+1)) q
  let F (A : Mat d) := pin false (E A)
  let back (B : Mat d) := flipRows (pin false (E (reverseMat B)))
  let G (B : Mat d) := glue (glue (back B) P) Q
  refine ⟨F,G,pin_proj hE false,combine_proj (combine_proj (back_proj (pin_proj hE false)) (fixed_proj P)) (fixed_proj Q),?_⟩
  intro A B
  have hm : 0<len d := by unfold len; positivity
  have hw : d+1 ≤ m+n := by
    have hpow : 0<(2:ℕ)^d := by positivity
    have hle : d+1 ≤ len d := by unfold len; nlinarith [Nat.mul_le_mul_left (3*(d+1)) (show 1≤(2:ℕ)^d by omega)]
    dsimp only [m] at *; omega
  have eqs (a b : W (d+1)) : count (G B) a b = count (back B) a b :=
    (remove_pad _ Q hQ a b).trans (remove_pad _ P hP a b)
  let term (a b : W (d+1)) := count (F A) a b * count (back B) b a
  have evalTerm (t r : Bool) (u v : W d) : term (state t u) (state r v) =
      if t=false ∧ r=true ∧ A u v=true ∧ B u v=true then 1 else 0 := by
    dsimp only [term,F,back]
    rw [flip_count,pin_count hm,pin_count hm]
    simp only [hcount,neg_state,state_zero,state_eq,payload_state,reverseMat,neg_neg]
    cases t <;> cases r <;> cases ha : A u v <;> cases hb : B u v <;> simp [ha,hb]
  have inner (t : Bool) (u : W d) : (∑ b, term (state t u) b) =
      if t=false then ∑ v : W d, (if A u v=true ∧ B u v=true then 1 else 0) else 0 := by
    rw [sum_states]
    simp only [evalTerm]
    cases t <;> simp
  have hrows : (Finset.univ.filter (splitOk hn (F A) (G B))) =
      Finset.univ.filter (cyclic hn (glue (F A) (G B))) := by
    ext x; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact split_iff hn _ _ x
  rw [hrows,count_ring hn hw]
  calc
    (∑ a, count (glue (F A) (G B)) a a) = ∑ a, ∑ b, term a b := by
      simp only [count_glue,eqs,term]
    _ = (∑ u : W d, ∑ v : W d, if A u v=true ∧ B u v=true then 1 else 0) := by
      rw [sum_states]; simp only [inner]; simp
    _ = _ := by rw [Finset.card_filter,Fintype.sum_prod_type]

lemma distinguish {d s : ℕ} (msg : Mat d → Fin s) (finish : Fin s → Mat d → Bool)
    (h : ∀ A B, finish (msg A) B=true ↔ ∃ u v, A u v=true ∧ B u v=true) : 2^(4^d)≤s := by
  classical
  have inj : Function.Injective msg := by
    intro A B he
    funext u v
    let probe : Mat d := fun x y => decide (x=u ∧ y=v)
    have hp (M : Mat d) : finish (msg M) probe=true ↔ M u v=true := by
      rw [h]
      simp only [probe,decide_eq_true_eq]
      constructor
      · rintro ⟨_,_,hm,rfl,rfl⟩; exact hm
      · intro hm; exact ⟨u,v,hm,rfl,rfl⟩
    have hh : A u v=true ↔ B u v=true := by rw [←hp A,←hp B,he]
    cases ha : A u v <;> cases hb : B u v <;> simp_all
  have hc : Fintype.card (Mat d) = 2^(4^d) := by
    simp only [Mat,W,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,←pow_mul,←mul_pow]
    norm_num
  simpa only [hc,Fintype.card_fin] using Fintype.card_le_of_injective msg inj

end PEqualNP.Outside.L_clb_106_aux

open PEqualNP.Outside.L_clb_106_aux in
theorem PEqualNP.Outside.L_clb_106 : (∀ (d p q : ℕ),
  let w := d + 1
  let D := Fin d → Bool
  let L := 3 * w * 2 ^ d
  let R := L + p * w + q * (w + 1)
  let n := L + R
  let pos := fun (i : ℕ) => (⟨i % n, Nat.mod_lt _ (Nat.add_pos_left (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos 2) (Nat.succ_pos d)) (Nat.pow_pos (Nat.succ_pos 1))) _)⟩ : Fin n)
  let Part := fun k : ℕ => Fin k → (Fin (w + 1) → Bool) → Bool
  let accepts := fun (P : Part L) (Q : Part R) (word : Fin n → Bool) =>
    (∀ i : Fin L, P i (fun j => word (pos (i.val + j.val))) = true) ∧
    (∀ k : Fin R, Q k (fun t => word (pos (L + k.val + t.val))) = true)
  let projection := fun (k : ℕ) (enc : (D → D → Bool) → Part k) =>
    ∀ row pat, (∃ c : Bool, ∀ M, enc M row pat = c) ∨
      ∃ u v : D, ∀ M, enc M row pat = M u v
  ∃ (first : (D → D → Bool) → Part L) (last : (D → D → Bool) → Part R),
    projection L first ∧ projection R last ∧
    (∀ A B : D → D → Bool,
      (Finset.univ.filter (accepts (first A) (last B))).card =
        (Finset.univ.filter (fun e : D × D => A e.1 e.2 = true ∧ B e.1 e.2 = true)).card) ∧
    ∀ (s : ℕ) (save : Part L → Fin s) (finish : Fin s → Part R → Bool),
      (∀ A B, finish (save (first A)) (last B) = true ↔
        ∃ x, accepts (first A) (last B) x) → 2 ^ (4 ^ d) ≤ s) := by
  intro d p q w D L R n pos Part accepts projection
  obtain ⟨first,last,hf,hl,hc⟩ := tables d p q
  refine ⟨first,last,hf,hl,hc,?_⟩
  intro s save finish h
  apply distinguish (fun A => save (first A)) (fun st B => finish st (last B))
  intro A B
  rw [h]
  have eq : (Finset.univ.filter (accepts (first A) (last B))).card =
      (Finset.univ.filter (fun e : D × D => A e.1 e.2=true ∧ B e.1 e.2=true)).card := hc A B
  have posiff := congrArg (fun k : ℕ => 0<k) eq
  simpa only [Finset.card_pos,Finset.Nonempty,Finset.mem_filter,Finset.mem_univ,true_and,
    Prod.exists] using Iff.of_eq posiff

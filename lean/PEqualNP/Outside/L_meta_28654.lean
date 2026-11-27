import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28654_aux
-- Live-wire search adapted from L-meta-10852, following Vkuparin, ljste and jfsantoropereira.
-- Paired edge/independent-set inputs and the replacement circuit are specific to this graph.

abbrev B := BitVec 59
abbrev Sig := B × B
def top : B := BitVec.allOnes 59
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



-- Each bit position pairs a positive and a negative input row.
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
def Live : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target}
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live k t (insert (bin d a b) U))

lemma Live.stop : Live 0 0 {target} := ⟨rfl,rfl⟩

lemma Live.unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U) := Or.inl ⟨_,_,_,rfl,rfl,ha,hfresh,tail⟩

lemma Live.binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U)) := Or.inr ⟨_,_,_,_,rfl,ha,hb,hab,hfresh,tail⟩

lemma liveInd {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P k t (insert (neg a) U) tail → P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P k t (insert (bin d a b) U) tail → P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

lemma liveCases {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail
    · exact binary ha hb hab hf tail

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h using liveInd with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using liveInd with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 59
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 59 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 59
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 59 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 59)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 59) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 59 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 59)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def isNot (op : GateOp) : Bool := match op with | .not => true | _ => false

lemma isNot_iff (op : GateOp) : isNot op = true ↔ op = .not := by cases op <;> simp [isNot]

def witness (allow : Bool) (w : List Sig) (z : Sig) : Prop :=
  (allow = true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (allow = false ∧ ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness false w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨rfl,d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness (isNot g.op) w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness true w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨rfl,a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {flag : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness flag w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' + t + flag.toNat ≤ k+1+t' ∧ t' ≤ t+flag.toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by cases flag <;> simp <;> omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨flagOff,d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,by simp [flagOn] <;> omega,by simp [flagOn],Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,by simp [flagOff] <;> omega,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by cases flag <;> simp <;> omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k + gs.countP (fun g => isNot g.op) ≤ gs.length + t ∧ t ≤ gs.countP (fun g => isNot g.op) ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hcount,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hcnt,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    refine ⟨l,u,T,?_,?_,hu,hT⟩ <;>
      cases hf : isNot g.op <;> simp [List.countP_cons,hf] at hl hcnt ⊢ <;> omega

def bit (side : Bool) (i : Fin 59) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 59).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]


def evalT (T : ℕ) (x : Fin 8 → Bool) := Nat.testBit T (∑ i : Fin 8, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 59) (j : Fin 8) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 8 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (T : ℕ) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = evalT T x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample raw s i)
    rw [sample_list raw raw_id,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma necessary (raw : List Sig) (every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true) {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

def special : List Sig := []
def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest k t v (search k (t-1)) (search k t)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Live m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Live m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Live l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Live l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  induction h using liveCases with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf (by simp [special]) tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf (by simp [special]) (by simp [special]) tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Live m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    obtain ⟨rfl,rfl⟩ := h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl


lemma notCount (gs : List Gate)
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    gs.countP (fun g => isNot g.op) ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have rest : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j := by
      intro i j hi hj
      exact Fin.succ_inj.mp (single i.succ j.succ hi hj)
    by_cases hg : g.op = .not
    · have z : gs.countP (fun h => isNot h.op) = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
        intro h
        have hiNot : (gs.get i).op = .not := by rw [hi]; exact (isNot_iff _).mp h
        have eqn := single (0 : Fin (g::gs).length) i.succ hg hiNot
        exact Fin.succ_ne_zero i eqn.symm
      have hf : isNot g.op = true := (isNot_iff _).mpr hg
      simp [List.countP_cons,hf,z]
    · have flag : isNot g.op = false := Bool.eq_false_iff.mpr (fun h => hg ((isNot_iff _).mp h))
      simpa [List.countP_cons,flag] using ih rest

def root : List Sig := [(0x204430109869d3,0x410100820c1), (0xc7c4041161b86c,0x47c4041020b844), (0x110a4c399863670,0x10244399822270), (0x20b270d1e07f870,0x9250d1207f870), (0x40c3809e007c07f,0x828092007403a), (0x7efc00e0007ff80,0x7efc00c0005dd00), (0x7f0000ffff80000,0x7b00002cdd00000), (0x7fffff000000000,0x7e6d2a000000000)]

def goalTable : Nat := 0xfffffffefffffffefffffffafffffffafffffffeffffffeefefefafaeeee0000

theorem samples_match : ∀ b i, evalT goalTable (sample root b i) = b := by
  decide +kernel

def Blocked (k t : Nat) (v : List Sig) : Prop :=
  ∀ m ≤ k, ¬ Live m t v.toFinset

def Batch (k t : Nat) : List (List Sig) → Prop
  | [] => True
  | a :: rest => Blocked k t a ∧ Batch k t rest

theorem in_batch {k t ws w} (h : Batch k t ws) (mem : w ∈ ws) : Blocked k t w := by
  induction ws with
  | nil => simp at mem
  | cons a l ih =>
    rcases List.mem_cons.mp mem with rfl | m
    · exact h.1
    · exact ih h.2 m

def sameBank (w v : List Sig) : Bool :=
  w.all v.contains && v.all w.contains

theorem sameBank_eq {w v : List Sig} (h : sameBank w v = true) : w.toFinset = v.toFinset := by
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun h => List.contains_iff_mem.mp (List.all_eq_true.mp ha a h),
         fun h => List.contains_iff_mem.mp (List.all_eq_true.mp hb a h)⟩

def allowChild (states : List (List Sig)) (w : List Sig) : Bool :=
  !(states.any (sameBank w))

theorem allow_live {k t m states w} (bad : Batch k t states) (sz : m ≤ k)
    (live : Live m t w.toFinset) : allowChild states w = true := by
  have noMatch : states.any (sameBank w) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨v,hv,eq⟩ := List.any_eq_true.mp hh
    exact in_batch bad hv m sz (sameBank_eq eq ▸ live)
  simp [allowChild, noMatch]

theorem block_step {k t v} (unary binary : List (List Sig)) (hu : Batch k (t-1) unary)
    (hb : Batch k t binary) (nd : v.Nodup)
    (ok : stepTest k t v (allowChild unary) (allowChild binary) = false) : Blocked (k+1) t v := by
  intro m small h
  have good := reduced_step (u := allowChild unary) (b := allowChild binary) h small nd rfl
    (fun _ _ _ sz l => allow_live hu sz l) (fun _ _ _ sz l => allow_live hb sz l)
  exact Bool.false_ne_true (ok.symm.trans good)

theorem block_search {k t v} (nd : v.Nodup) (ok : search k t v = false) : Blocked k t v := by
  intro m small live
  exact Bool.false_ne_true (ok.symm.trans (search_complete live k small v nd rfl))

open PEqualNP.CircuitLowerBounds

def edgeFn (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def replacement : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [17, 16]⟩], 18⟩

theorem replacement_size : replacement.gates.length = 11 := rfl

theorem replacement_basis : ∀ g ∈ replacement.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [replacement]

set_option maxRecDepth 16000 in
theorem replacement_correct : ∀ x : Fin 8 → Bool, replacement.eval (List.ofFn x) = edgeFn x := by
  decide +kernel

theorem table_agrees : ∀ x : Fin 8 → Bool, edgeFn x = evalT goalTable x := by
  decide +kernel

-- Count binary gates even when the single NOT is discarded from a live plan.
theorem lower_with_not (gs : List Gate) (o : ℕ)
    (basis : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (oneNot : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (used : ∃ g ∈ gs, g.op = .not)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = edgeFn x)
    (zeroNot : Blocked 9 0 root) (one : Blocked 10 1 root) : 11 ≤ gs.length := by
  by_contra! small
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using basis
  have hout := circuit_target goalTable root rfl samples_match (⟨gs,o⟩ : Circuit) legal
    (fun x => (correct x).trans (table_agrees x))
  obtain ⟨k,t,S,hk,count,live,sub⟩ := extract gs root legal hout
  have eq := necessary root (by decide +kernel) live sub
  have hL : Live k t root.toFinset := eq.symm ▸ live
  have atMostOne := notCount gs oneNot
  have positive : 0 < gs.countP (fun g => isNot g.op) := by
    obtain ⟨g,hg,op⟩ := used
    by_contra! hz
    have absent := List.countP_eq_zero.mp (Nat.le_zero.mp hz) g hg
    exact absent ((isNot_iff _).mpr op)
  by_cases z : t = 0
  · subst t
    exact zeroNot k (by omega) hL
  · have u : t = 1 := by omega
    subst t
    exact one k (by omega) hL

def sig0 : Sig := (0x4053,0x0)
def sig1 : Sig := (0x204430109869d3,0x410100820c1)
def sig2 : Sig := (0x40c3809e007c07f,0x828092007403a)
def sig3 : Sig := (0x20b270d1e07f870,0x9250d1207f870)
def sig4 : Sig := (0x110a4c399863670,0x10244399822270)
def sig5 : Sig := (0xc7c4041161b86c,0x47c4041020b844)
def sig6 : Sig := (0x7f0000ffff80000,0x7b00002cdd00000)
def sig7 : Sig := (0x7fffff000000000,0x7e6d2a000000000)
def sig8 : Sig := (0x7efc00e0007ff80,0x7efc00c0005dd00)
def sig9 : Sig := (0x400000001806c,0x0)
def sig10 : Sig := (0x20000010980000,0x0)
def sig11 : Sig := (0x20400000006980,0x0)
def sig12 : Sig := (0x20443000000000,0x0)
def sig13 : Sig := (0xc0000411600000,0x0)
def sig14 : Sig := (0x100800200063600,0x0)
def sig15 : Sig := (0x110a4c000000000,0x0)
def sig16 : Sig := (0x200000d1e000000,0x0)
def sig17 : Sig := (0x20b270000000000,0x0)
def sig18 : Sig := (0x4000009e0000000,0x0)
def sig19 : Sig := (0x40c380000000000,0x0)
def sig20 : Sig := (0x40010006850,0x40010002040)
def sig21 : Sig := (0x40010802050,0x40010002040)
def sig22 : Sig := (0x440010002840,0x40010002040)
def sig23 : Sig := (0x840011003060,0x40010002040)
def sig24 : Sig := (0x200180060070,0x200100020030)
def sig25 : Sig := (0x240118063070,0x240110022070)
def sig26 : Sig := (0x304041001b860,0x104041000b840)
def sig27 : Sig := (0x40c00080007c000,0x8000800054000)
def sig28 : Sig := (0x820090007c070,0x8200900074030)
def sig29 : Sig := (0x42c7c39f09fe9ff,0x82c19300f60fb)
def sig30 : Sig := (0x20b000c0007f800,0x9000c0005d800)
def sig31 : Sig := (0x22b673d1e9ff9f3,0x9251d120ff8f1)
def sig32 : Sig := (0x60f3f0dfe07f87f,0x92d0d3207f87a)
def sig33 : Sig := (0x110000399800000,0x10000289800000)
def sig34 : Sig := (0x130e4f3999e7ff3,0x102453998a22f1)
def sig35 : Sig := (0x51cbccbf987f67f,0x182c4bb987627a)
def sig36 : Sig := (0x31ba7cf9f87fe70,0x19254f9b87fa70)
def sig37 : Sig := (0xc7c40000000000,0x46c00000000000)
def sig38 : Sig := (0xc7c0040001b800,0x47c00400009800)
def sig39 : Sig := (0xe7c43411f9f9ff,0x47c4141028b8c5)
def sig40 : Sig := (0x2cfe70d1f67f87c,0x4fe50d1227f874)
def sig41 : Sig := (0x4cffc0df167f87f,0x4fec0d3027f87e)
def sig42 : Sig := (0x1d7e4c799e7be7c,0x57e44799a2ba74)
def sig43 : Sig := (0x7e0000e00000000,0x7a0000000000000)
def sig44 : Sig := (0x7f0000000000000,0x7a0000000000000)
def sig45 : Sig := (0x7f0443ffff869d3,0x7b00412ddd820c1)
def sig46 : Sig := (0x7f0a4cffffe3670,0x7b02443ddd22270)
def sig47 : Sig := (0x7fc380fffffc07f,0x7b8280bedd7403a)
def sig48 : Sig := (0x7fb270ffffff870,0x7b9250fdfd7f870)
def sig49 : Sig := (0x7efc00000000000,0x7e6c00000000000)
def sig50 : Sig := (0x7fffff0109869d3,0x7e6d6b0100820c1)
def sig51 : Sig := (0x7fffff41161b86c,0x7e7d6a41020b844)
def sig52 : Sig := (0x7fffff9e007c07f,0x7eefaa92007403a)
def sig53 : Sig := (0x7efc40e1167ffec,0x7efc40c1025fd44)
def sig54 : Sig := (0x7efc43e109fffd3,0x7efc41c100dfdc1)
def sig55 : Sig := (0x7fffffe0007ff80,0x7efd2ac0005dd00)
def sig56 : Sig := (0x7efe70f1e07fff0,0x7efe50d1207fd70)
def sig57 : Sig := (0x7eff80fe007ffff,0x7efe80d2007dd3a)
def sig58 : Sig := (0x7fffffd1e07f870,0x7eff7ad1207f870)
def sig59 : Sig := (0x7fffffffff80000,0x7f6d2a2cdd00000)
def sig60 : Sig := (0x7fffff399863670,0x7f6f6e399822270)
def sig61 : Sig := (0x7f7c40ffff9b86c,0x7f7c406ddf0b844)
def sig62 : Sig := (0x7ffc00fffffff80,0x7ffc00ecdd5dd00)
def sig63 : Sig := (0x7ffe4cf9987fff0,0x7ffe44f9987ff70)
def sig64 : Sig := (0x103ff1fff8007f,0x103ff3fffa22ff)
def sig65 : Sig := (0xfffffffff,0x192d5fffffffff)
def sig66 : Sig := (0xffff00007ffff,0x4ffffd322fffff)
def sig67 : Sig := (0x7383bfbee9e4793,0x7b83bfbefdf47bb)
def sig68 : Sig := (0x6ef5b3c6679c98f,0x7efdbbc667ddd8f)
def sig69 : Sig := (0x5f4d8f2e1f8078f,0x7f6daf2edf8078f)
def sig70 : Sig := (0x3f3c7f61ff83f80,0x7f7d7f6dff8bfc5)
def sig71 : Sig := (0x7dfbbcfef67962c,0x7fffbefeff7df3e)
def sig72 : Sig := (0x4001160006c,0x40010202044)
def sig73 : Sig := (0x43010980053,0x410100820c1)
def sig74 : Sig := (0x103ff000000000,0x12a000000000)
def sig75 : Sig := (0x27011e000070,0x250112022070)
def sig76 : Sig := (0x3801e000007f,0x28012002003a)
def sig77 : Sig := (0x100001fff80000,0x100002cdd00000)
def sig78 : Sig := (0x1024c199800070,0x10244399822270)
def sig79 : Sig := (0x307ff1fff869ff,0x103ff3fffa22ff)
def sig80 : Sig := (0x110bff3fffe367f,0x103ff3fffa22ff)
def sig81 : Sig := (0x41c3ff9ffffc07f,0x183ffbffff62ff)
def sig82 : Sig := (0x21b3ffdfffff87f,0x193ffffffffaff)
def sig83 : Sig := (0xd7fff5fff9b87f,0x57fff7fffabaff)
def sig84 : Sig := (0x7f03ffffff8007f,0x7b03ff3fffa22ff)
def sig85 : Sig := (0x7fffff1fff8007f,0x7f6fff3fffa22ff)
def sig86 : Sig := (0x109869d3,0x410100820c1)
def sig87 : Sig := (0x41161b86c,0x104041020b844)
def sig88 : Sig := (0x9e007c07f,0x828092007403a)
def sig89 : Sig := (0xe0007ff80,0x9000c0005dd00)
def sig90 : Sig := (0xd1e07f870,0x9250d1207f870)
def sig91 : Sig := (0xffff80000,0x100002cdd00000)
def sig92 : Sig := (0x399863670,0x10244399822270)
def sig93 : Sig := (0x20443fffffffff,0x192d5fffffffff)
def sig94 : Sig := (0x110a4cfffffffff,0x192d5fffffffff)
def sig95 : Sig := (0x20b270fffffffff,0x192d5fffffffff)
def sig96 : Sig := (0x40c380fffffffff,0x192d5fffffffff)
def sig97 : Sig := (0xc7c40fffffffff,0x5fed5fffffffff)
def sig98 : Sig := (0x7f0000fffffffff,0x7b92d5fffffffff)
def sig99 : Sig := (0x7efc00fffffffff,0x7ffed5fffffffff)
def sig100 : Sig := (0x4430000069d3,0x410100820c1)
def sig101 : Sig := (0xa4c000063670,0x244110022270)
def sig102 : Sig := (0xc38000007c07f,0x828092007403a)
def sig103 : Sig := (0xb27000007f870,0x9250d1207f870)
def sig104 : Sig := (0xffff000000000,0x46d2a000000000)
def sig105 : Sig := (0x7c4000001b86c,0x47c4041020b844)
def sig106 : Sig := (0xfc0000007ff80,0x4fc00c0005dd00)
def sig107 : Sig := (0x2ffff0109fffff,0x4ffffd322fffff)
def sig108 : Sig := (0xcffff41167ffff,0x4ffffd322fffff)
def sig109 : Sig := (0x20ffffd1e07ffff,0x4ffffd322fffff)
def sig110 : Sig := (0x40ffff9e007ffff,0x4ffffd322fffff)
def sig111 : Sig := (0x11ffff39987ffff,0x5fffffbbafffff)
def sig112 : Sig := (0x7effffe0007ffff,0x7effffd322fffff)
def sig113 : Sig := (0x7fffff00007ffff,0x7effffd322fffff)
def sig114 : Sig := (0x20003000984193,0x1000080081)
def sig115 : Sig := (0x20823090e064010,0x8210902074030)
def sig116 : Sig := (0x4083809e0064013,0x828092007403a)
def sig117 : Sig := (0x11020c388860610,0x10204389820230)
def sig118 : Sig := (0x7383bf000000000,0x7a012a000000000)
def sig119 : Sig := (0x728000a00064780,0x7a8000800054500)
def sig120 : Sig := (0x730000bee980000,0x7b00002cdd00000)
def sig121 : Sig := (0x73c3bfbee9fc7ff,0x7b83bfbefdf47bb)
def sig122 : Sig := (0x7f83bfffffe4793,0x7b83bfbefdf47bb)
def sig123 : Sig := (0x7387ffbfe9e6fd3,0x7b83ffbffdf67fb)
def sig124 : Sig := (0x738bffbff9e77f3,0x7b83ffbffdf67fb)
def sig125 : Sig := (0x73b3ffffe9ffff3,0x7b93fffffdffffb)
def sig126 : Sig := (0x7fffffbee9e4793,0x7fefbfbefdf47bb)
def sig127 : Sig := (0x7fffbffee9fff93,0x7fffbffefdfdfbb)
def sig128 : Sig := (0x20403000184983,0x1000080081)
def sig129 : Sig := (0x40c18086001c00f,0x808082005400a)
def sig130 : Sig := (0x20b030c0601c800,0x9010c0205d800)
def sig131 : Sig := (0xc740040061880c,0x47c00400209804)
def sig132 : Sig := (0x6e0000c66780000,0x7a0000044500000)
def sig133 : Sig := (0x6ef5b3000000000,0x7e6d2a000000000)
def sig134 : Sig := (0x6ef400c0001c980,0x7efc00c0005dd00)
def sig135 : Sig := (0x7efdb3e667fff8f,0x7efdbbc667ddd8f)
def sig136 : Sig := (0x7fffffc6679c98f,0x7efdbbc667ddd8f)
def sig137 : Sig := (0x6ef5f3c76f9e9df,0x7efdfbc767dfdcf)
def sig138 : Sig := (0x6efdf3c7779f9ef,0x7efdfbc767dfdcf)
def sig139 : Sig := (0x6ef7b3de67fc9ff,0x7effbbd667fddbf)
def sig140 : Sig := (0x6ef7f3d7e7ff9ff,0x7efffbd767ffdff)
def sig141 : Sig := (0x7ff5b3ffff9c98f,0x7ffdbbeeffddd8f)
def sig142 : Sig := (0x20403000980183,0x1000080081)
def sig143 : Sig := (0x4041800e000000f,0x8002000000a)
def sig144 : Sig := (0x11080c281800600,0x10004289800200)
def sig145 : Sig := (0xc4c0000160000c,0x46c00000200004)
def sig146 : Sig := (0x5f00002e1f80000,0x7b00002cdd00000)
def sig147 : Sig := (0x5e4c00200000780,0x7e6c00000000500)
def sig148 : Sig := (0x5f4d8f000000000,0x7e6d2a000000000)
def sig149 : Sig := (0x7f4d8fffff8078f,0x7f6daf2edf8078f)
def sig150 : Sig := (0x7fffff2e1f8078f,0x7f6daf2edf8078f)
def sig151 : Sig := (0x5f4dcf2f1f86fdf,0x7f6def2fdf827cf)
def sig152 : Sig := (0x5f4fcf3f9fe37ff,0x7f6fef3fdfa27ff)
def sig153 : Sig := (0x5f7dcf6f1f9bfef,0x7f7def6fdf8bfcf)
def sig154 : Sig := (0x5fcf8fbe1ffc7ff,0x7fefafbedff47bf)
def sig155 : Sig := (0x7ffd8fee1ffff8f,0x7ffdafeedfddf8f)
def sig156 : Sig := (0x20443010982980,0x410100820c1)
def sig157 : Sig := (0x20307041e003800,0x105041200b840)
def sig158 : Sig := (0x11084c219803600,0x10044299802240)
def sig159 : Sig := (0xc3c40411603800,0x47c4041020b844)
def sig160 : Sig := (0x3f000061ff80000,0x7b00002cdd00000)
def sig161 : Sig := (0x3f3c7f000000000,0x7e6d2a000000000)
def sig162 : Sig := (0x3e3c00600003f80,0x7e7c00400009d00)
def sig163 : Sig := (0x3f3c7f61ff87fd3,0x7f7d7f6dff8bfc5)
def sig164 : Sig := (0x3f7c7f61ff9bfec,0x7f7d7f6dff8bfc5)
def sig165 : Sig := (0x7f3c7fffff83f80,0x7f7d7f6dff8bfc5)
def sig166 : Sig := (0x7fffff61ff83f80,0x7f7d7f6dff8bfc5)
def sig167 : Sig := (0x3f3e7f79ffe3ff0,0x7f7f7f7dffabff5)
def sig168 : Sig := (0x7ffc7fe1fffff80,0x7ffd7fedffdffc5)
def sig169 : Sig := (0x3fbe7ff1ffffff0,0x7fff7ffdffffff5)
def sig170 : Sig := (0x40c3809e007802c,0x828092007403a)
def sig171 : Sig := (0x20b230d0e079020,0x9210d0207d830)
def sig172 : Sig := (0x110a0c389061620,0x10204389820230)
def sig173 : Sig := (0xc780040161902c,0x47c00400209804)
def sig174 : Sig := (0x7d0000fef600000,0x7b00002cdd00000)
def sig175 : Sig := (0x7dfbbc000000000,0x7e6d2a000000000)
def sig176 : Sig := (0x7cf800e00079600,0x7efc00c0005dd00)
def sig177 : Sig := (0x7dfbbcfef67d67f,0x7fffbefeff7df3e)
def sig178 : Sig := (0x7ffbbcfffff962c,0x7fffbefeff7df3e)
def sig179 : Sig := (0x7fffbcfef67ffac,0x7fffbefeff7df3e)
def sig180 : Sig := (0x7ffffffef67962c,0x7fffbefeff7df3e)
def sig181 : Sig := (0x7dfbfcfff67fe7c,0x7ffffeffff7ff7e)
def sig182 : Sig := (0x7dfbfcfffe7b67c,0x7ffffeffff7ff7e)
def sig183 : Sig := (0x7dfffcfff67be6c,0x7ffffeffff7ff7e)
def sig184 : Sig := (0x1fff8007f,0x102d53fffa22ff)
def sig185 : Sig := (0x110a4c200063600,0x0)
def sig186 : Sig := (0x7183bcbee060600,0x7b83bebefd7473a)
def sig187 : Sig := (0x6cf1b0c6661800c,0x7efdbac6675dd0e)
def sig188 : Sig := (0x120c00200067f80,0x0)
def bank1 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank2 : List Sig := [sig9, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank3 : List Sig := [sig10, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank4 : List Sig := [sig11, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank5 : List Sig := [sig12, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank6 : List Sig := [sig13, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank7 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank8 : List Sig := [sig15, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank9 : List Sig := [sig16, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank10 : List Sig := [sig17, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank11 : List Sig := [sig18, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank12 : List Sig := [sig19, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank13 : List Sig := [sig20, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank14 : List Sig := [sig21, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank15 : List Sig := [sig22, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank16 : List Sig := [sig23, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank17 : List Sig := [sig1, sig24, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank18 : List Sig := [sig1, sig25, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank19 : List Sig := [sig1, sig26, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank20 : List Sig := [sig1, sig27, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank21 : List Sig := [sig1, sig28, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank22 : List Sig := [sig1, sig2, sig29, sig3, sig4, sig5, sig6, sig7, sig8]
def bank23 : List Sig := [sig1, sig2, sig30, sig3, sig4, sig5, sig6, sig7, sig8]
def bank24 : List Sig := [sig1, sig2, sig3, sig31, sig4, sig5, sig6, sig7, sig8]
def bank25 : List Sig := [sig1, sig2, sig3, sig32, sig4, sig5, sig6, sig7, sig8]
def bank26 : List Sig := [sig1, sig2, sig3, sig33, sig4, sig5, sig6, sig7, sig8]
def bank27 : List Sig := [sig1, sig2, sig3, sig4, sig34, sig5, sig6, sig7, sig8]
def bank28 : List Sig := [sig1, sig2, sig3, sig4, sig35, sig5, sig6, sig7, sig8]
def bank29 : List Sig := [sig1, sig2, sig3, sig4, sig36, sig5, sig6, sig7, sig8]
def bank30 : List Sig := [sig1, sig2, sig3, sig4, sig37, sig5, sig6, sig7, sig8]
def bank31 : List Sig := [sig1, sig2, sig3, sig4, sig38, sig5, sig6, sig7, sig8]
def bank32 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig39, sig6, sig7, sig8]
def bank33 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig40, sig6, sig7, sig8]
def bank34 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig41, sig6, sig7, sig8]
def bank35 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig42, sig6, sig7, sig8]
def bank36 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig43, sig6, sig7, sig8]
def bank37 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig44, sig6, sig7, sig8]
def bank38 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig45, sig7, sig8]
def bank39 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig46, sig7, sig8]
def bank40 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig7, sig8]
def bank41 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig7, sig8]
def bank42 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig49, sig7, sig8]
def bank43 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig50, sig8]
def bank44 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig51, sig8]
def bank45 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig52, sig8]
def bank46 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig53]
def bank47 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig54]
def bank48 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig55]
def bank49 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig56]
def bank50 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig57]
def bank51 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig58]
def bank52 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig59]
def bank53 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig60]
def bank54 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig61]
def bank55 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig62]
def bank56 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig63]
def bank57 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig55]
def bank58 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig8]
def bank59 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8]
def bank60 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8]
def bank61 : List Sig := [sig1, sig2, sig32, sig4, sig5, sig6, sig7, sig8]
def bank62 : List Sig := [sig1, sig2, sig3, sig4, sig64, sig5, sig6, sig7, sig8]
def bank63 : List Sig := [sig1, sig2, sig3, sig4, sig65, sig5, sig6, sig7, sig8]
def bank64 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig66, sig6, sig7, sig8]
def bank65 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig67, sig7, sig8]
def bank66 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig68]
def bank67 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig69]
def bank68 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig70]
def bank69 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig71]
def bank70 : List Sig := [sig72, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank71 : List Sig := [sig73, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank72 : List Sig := [sig1, sig74, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank73 : List Sig := [sig1, sig75, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank74 : List Sig := [sig1, sig76, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank75 : List Sig := [sig1, sig2, sig3, sig77, sig4, sig5, sig6, sig7, sig8]
def bank76 : List Sig := [sig1, sig2, sig3, sig78, sig4, sig5, sig6, sig7, sig8]
def bank77 : List Sig := [sig1, sig2, sig3, sig4, sig64, sig5, sig6, sig7, sig55]
def bank78 : List Sig := [sig1, sig2, sig3, sig4, sig64, sig39, sig6, sig7, sig8]
def bank79 : List Sig := [sig1, sig2, sig3, sig4, sig79, sig5, sig6, sig7, sig8]
def bank80 : List Sig := [sig1, sig2, sig3, sig4, sig80, sig5, sig6, sig7, sig8]
def bank81 : List Sig := [sig1, sig2, sig3, sig4, sig81, sig5, sig6, sig7, sig8]
def bank82 : List Sig := [sig1, sig2, sig3, sig4, sig82, sig5, sig6, sig7, sig8]
def bank83 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig83, sig6, sig7, sig8]
def bank84 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig84, sig7, sig8]
def bank85 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig85]
def bank86 : List Sig := [sig1, sig2, sig3, sig34, sig64, sig5, sig6, sig7, sig8]
def bank87 : List Sig := [sig1, sig2, sig31, sig4, sig64, sig5, sig6, sig7, sig8]
def bank88 : List Sig := [sig1, sig2, sig32, sig4, sig64, sig5, sig6, sig7, sig8]
def bank89 : List Sig := [sig86, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank90 : List Sig := [sig1, sig87, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank91 : List Sig := [sig1, sig88, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank92 : List Sig := [sig1, sig2, sig89, sig3, sig4, sig65, sig5, sig6, sig7]
def bank93 : List Sig := [sig1, sig2, sig89, sig3, sig4, sig5, sig6, sig7]
def bank94 : List Sig := [sig1, sig2, sig89, sig3, sig4, sig5, sig6, sig7, sig8]
def bank95 : List Sig := [sig1, sig2, sig90, sig3, sig4, sig5, sig6, sig7, sig8]
def bank96 : List Sig := [sig1, sig2, sig3, sig91, sig4, sig5, sig6, sig7, sig8]
def bank97 : List Sig := [sig1, sig2, sig3, sig92, sig4, sig5, sig6, sig7, sig8]
def bank98 : List Sig := [sig1, sig2, sig3, sig4, sig65, sig5, sig6, sig7, sig55]
def bank99 : List Sig := [sig1, sig2, sig3, sig4, sig65, sig39, sig6, sig7, sig8]
def bank100 : List Sig := [sig1, sig2, sig3, sig4, sig93, sig5, sig6, sig7, sig8]
def bank101 : List Sig := [sig1, sig2, sig3, sig4, sig94, sig5, sig6, sig7, sig8]
def bank102 : List Sig := [sig1, sig2, sig3, sig4, sig95, sig5, sig6, sig7, sig8]
def bank103 : List Sig := [sig1, sig2, sig3, sig4, sig96, sig5, sig6, sig7, sig8]
def bank104 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig97, sig6, sig7, sig8]
def bank105 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig98, sig7, sig8]
def bank106 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig99]
def bank107 : List Sig := [sig1, sig2, sig3, sig34, sig65, sig5, sig6, sig7, sig8]
def bank108 : List Sig := [sig1, sig2, sig31, sig4, sig65, sig5, sig6, sig7, sig8]
def bank109 : List Sig := [sig1, sig2, sig32, sig4, sig65, sig5, sig6, sig7, sig8]
def bank110 : List Sig := [sig100, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank111 : List Sig := [sig1, sig101, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank112 : List Sig := [sig1, sig102, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank113 : List Sig := [sig1, sig2, sig103, sig3, sig4, sig5, sig6, sig7, sig8]
def bank114 : List Sig := [sig1, sig2, sig3, sig4, sig104, sig5, sig6, sig7, sig8]
def bank115 : List Sig := [sig1, sig2, sig3, sig4, sig105, sig5, sig6, sig7, sig8]
def bank116 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig106, sig6, sig7, sig8]
def bank117 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig66, sig6, sig7, sig55]
def bank118 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig107, sig6, sig7, sig8]
def bank119 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig108, sig6, sig7, sig8]
def bank120 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig109, sig6, sig7, sig8]
def bank121 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig110, sig6, sig7, sig8]
def bank122 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig111, sig6, sig7, sig8]
def bank123 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig112]
def bank124 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig113]
def bank125 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig66, sig6, sig7, sig8]
def bank126 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig66, sig6, sig7, sig8]
def bank127 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig66, sig6, sig7, sig8]
def bank128 : List Sig := [sig1, sig2, sig32, sig4, sig5, sig66, sig6, sig7, sig8]
def bank129 : List Sig := [sig114, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank130 : List Sig := [sig1, sig115, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank131 : List Sig := [sig1, sig116, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank132 : List Sig := [sig1, sig2, sig3, sig117, sig4, sig5, sig6, sig7, sig8]
def bank133 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig118, sig6, sig7, sig8]
def bank134 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig119, sig6, sig7, sig8]
def bank135 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig120, sig6, sig7, sig8]
def bank136 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig67, sig7, sig55]
def bank137 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig121, sig7, sig8]
def bank138 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig122, sig7, sig8]
def bank139 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig123, sig7, sig8]
def bank140 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig124, sig7, sig8]
def bank141 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig125, sig7, sig8]
def bank142 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig126]
def bank143 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig127]
def bank144 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig67, sig7, sig8]
def bank145 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig67, sig7, sig8]
def bank146 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig67, sig7, sig8]
def bank147 : List Sig := [sig1, sig2, sig32, sig4, sig5, sig6, sig67, sig7, sig8]
def bank148 : List Sig := [sig128, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank149 : List Sig := [sig1, sig129, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank150 : List Sig := [sig1, sig2, sig130, sig3, sig4, sig5, sig6, sig7, sig8]
def bank151 : List Sig := [sig1, sig2, sig3, sig4, sig131, sig5, sig6, sig7, sig8]
def bank152 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig132, sig6, sig7, sig8]
def bank153 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig133, sig7, sig8]
def bank154 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig134, sig8]
def bank155 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig135]
def bank156 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig136]
def bank157 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig137]
def bank158 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig138]
def bank159 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig139]
def bank160 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig140]
def bank161 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig141]
def bank162 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig55, sig68]
def bank163 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig8, sig68]
def bank164 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8, sig68]
def bank165 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8, sig68]
def bank166 : List Sig := [sig1, sig2, sig32, sig4, sig5, sig6, sig7, sig8, sig68]
def bank167 : List Sig := [sig142, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank168 : List Sig := [sig1, sig143, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank169 : List Sig := [sig1, sig2, sig3, sig144, sig4, sig5, sig6, sig7, sig8]
def bank170 : List Sig := [sig1, sig2, sig3, sig4, sig145, sig5, sig6, sig7, sig8]
def bank171 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig146, sig6, sig7, sig8]
def bank172 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig147, sig7, sig8]
def bank173 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig148, sig7, sig8]
def bank174 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig149]
def bank175 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig150]
def bank176 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig151]
def bank177 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig152]
def bank178 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig153]
def bank179 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig154]
def bank180 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig155]
def bank181 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig55, sig69]
def bank182 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig8, sig69]
def bank183 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8, sig69]
def bank184 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8, sig69]
def bank185 : List Sig := [sig1, sig2, sig32, sig4, sig5, sig6, sig7, sig8, sig69]
def bank186 : List Sig := [sig156, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank187 : List Sig := [sig1, sig157, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank188 : List Sig := [sig1, sig157, sig2, sig4, sig5, sig6, sig7, sig8]
def bank189 : List Sig := [sig1, sig157, sig2, sig4, sig5, sig6, sig7, sig8, sig70]
def bank190 : List Sig := [sig1, sig2, sig3, sig158, sig4, sig5, sig6, sig7, sig8]
def bank191 : List Sig := [sig1, sig2, sig3, sig4, sig159, sig5, sig6, sig7, sig8]
def bank192 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig160, sig6, sig7, sig8]
def bank193 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig161, sig7, sig8]
def bank194 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig162, sig8]
def bank195 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig163]
def bank196 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig164]
def bank197 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig165]
def bank198 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig166]
def bank199 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig167]
def bank200 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig168]
def bank201 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig169]
def bank202 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig55, sig70]
def bank203 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig8, sig70]
def bank204 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8, sig70]
def bank205 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8, sig70]
def bank206 : List Sig := [sig1, sig2, sig32, sig4, sig5, sig6, sig7, sig8, sig70]
def bank207 : List Sig := [sig1, sig170, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank208 : List Sig := [sig1, sig2, sig171, sig3, sig4, sig5, sig6, sig7, sig8]
def bank209 : List Sig := [sig1, sig2, sig171, sig4, sig5, sig6, sig7, sig8]
def bank210 : List Sig := [sig1, sig2, sig171, sig4, sig5, sig6, sig7, sig8, sig71]
def bank211 : List Sig := [sig1, sig2, sig3, sig172, sig4, sig5, sig6, sig7, sig8]
def bank212 : List Sig := [sig1, sig2, sig3, sig172, sig5, sig6, sig7, sig8]
def bank213 : List Sig := [sig1, sig2, sig3, sig172, sig5, sig6, sig7, sig8, sig71]
def bank214 : List Sig := [sig1, sig2, sig3, sig4, sig173, sig5, sig6, sig7, sig8]
def bank215 : List Sig := [sig1, sig2, sig3, sig4, sig173, sig6, sig7, sig8]
def bank216 : List Sig := [sig1, sig2, sig3, sig4, sig173, sig6, sig7, sig8, sig71]
def bank217 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig174, sig6, sig7, sig8]
def bank218 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig175, sig7, sig8]
def bank219 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig176, sig8]
def bank220 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig177]
def bank221 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig178]
def bank222 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig179]
def bank223 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig180]
def bank224 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig181]
def bank225 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig182]
def bank226 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig183]
def bank227 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig55, sig71]
def bank228 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig8, sig71]
def bank229 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8, sig71]
def bank230 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8, sig71]
def bank231 : List Sig := [sig1, sig2, sig32, sig4, sig5, sig6, sig7, sig8, sig71]
def bank232 : List Sig := [sig1, sig2, sig3, sig4, sig184, sig5, sig6, sig7, sig55]
def bank233 : List Sig := [sig185, sig1, sig2, sig3, sig5, sig6, sig7, sig55]
def bank234 : List Sig := [sig17, sig1, sig2, sig3, sig4, sig5, sig6, sig55]
def bank235 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig50, sig55]
def bank236 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig55, sig59]
def bank237 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig55, sig60]
def bank238 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig55]
def bank239 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig55]
def bank240 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig55]
def bank241 : List Sig := [sig1, sig2, sig32, sig4, sig5, sig6, sig7, sig55]
def bank242 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig186, sig7, sig8]
def bank243 : List Sig := [sig11, sig2, sig3, sig4, sig39, sig6, sig7, sig8]
def bank244 : List Sig := [sig1, sig2, sig3, sig34, sig39, sig6, sig7, sig8]
def bank245 : List Sig := [sig1, sig2, sig31, sig4, sig39, sig6, sig7, sig8]
def bank246 : List Sig := [sig1, sig2, sig32, sig4, sig39, sig6, sig7, sig8]
def bank247 : List Sig := [sig2, sig29, sig3, sig4, sig39, sig6, sig7, sig8]
def bank248 : List Sig := [sig2, sig3, sig4, sig34, sig39, sig6, sig7, sig8]
def bank249 : List Sig := [sig2, sig3, sig4, sig39, sig6, sig45, sig7, sig8]
def bank250 : List Sig := [sig2, sig3, sig34, sig39, sig6, sig7, sig8]
def bank251 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8, sig187]
def bank252 : List Sig := [sig188, sig1, sig2, sig3, sig34, sig5, sig6, sig7]
def bank253 : List Sig := [sig1, sig2, sig31, sig34, sig5, sig6, sig7, sig8]
def bank254 : List Sig := [sig1, sig2, sig32, sig34, sig5, sig6, sig7, sig8]
def bank255 : List Sig := [sig2, sig3, sig34, sig5, sig39, sig6, sig7, sig8]
def bank256 : List Sig := [sig2, sig3, sig34, sig5, sig6, sig7, sig50, sig8]
def bank257 : List Sig := [sig2, sig3, sig34, sig5, sig6, sig7, sig8, sig54]

set_option maxRecDepth 16000 in
theorem excl0 : Blocked 8 0 bank1 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl1 : Blocked 8 0 bank2 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl2 : Blocked 8 0 bank3 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl3 : Blocked 8 0 bank4 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl4 : Blocked 8 0 bank5 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl5 : Blocked 8 0 bank6 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl6 : Blocked 8 0 bank7 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl7 : Blocked 8 0 bank8 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl8 : Blocked 8 0 bank9 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl9 : Blocked 8 0 bank10 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl10 : Blocked 8 0 bank11 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl11 : Blocked 8 0 bank12 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl12 : Blocked 8 0 bank13 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl13 : Blocked 8 0 bank14 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl14 : Blocked 8 0 bank15 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl15 : Blocked 8 0 bank16 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl16 : Blocked 8 0 bank17 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl17 : Blocked 8 0 bank18 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl18 : Blocked 8 0 bank19 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl19 : Blocked 8 0 bank20 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl20 : Blocked 8 0 bank21 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl21 : Blocked 8 0 bank22 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl22 : Blocked 8 0 bank23 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl23 : Blocked 8 0 bank24 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl24 : Blocked 8 0 bank25 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl25 : Blocked 8 0 bank26 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl26 : Blocked 8 0 bank27 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl27 : Blocked 8 0 bank28 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl28 : Blocked 8 0 bank29 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl29 : Blocked 8 0 bank30 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl30 : Blocked 8 0 bank31 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl31 : Blocked 8 0 bank32 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl32 : Blocked 8 0 bank33 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl33 : Blocked 8 0 bank34 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl34 : Blocked 8 0 bank35 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl35 : Blocked 8 0 bank36 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl36 : Blocked 8 0 bank37 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl37 : Blocked 8 0 bank38 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl38 : Blocked 8 0 bank39 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl39 : Blocked 8 0 bank40 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl40 : Blocked 8 0 bank41 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl41 : Blocked 8 0 bank42 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl42 : Blocked 8 0 bank43 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl43 : Blocked 8 0 bank44 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl44 : Blocked 8 0 bank45 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl45 : Blocked 8 0 bank46 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl46 : Blocked 8 0 bank47 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl47 : Blocked 8 0 bank48 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl48 : Blocked 8 0 bank49 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl49 : Blocked 8 0 bank50 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl50 : Blocked 8 0 bank51 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl51 : Blocked 8 0 bank52 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl52 : Blocked 8 0 bank53 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl53 : Blocked 8 0 bank54 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl54 : Blocked 8 0 bank55 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl55 : Blocked 8 0 bank56 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl56 : Blocked 8 0 bank57 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl57 : Blocked 8 0 bank58 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl58 : Blocked 8 0 bank59 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl59 : Blocked 8 0 bank60 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl60 : Blocked 8 0 bank61 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl61 : Blocked 9 0 root :=
  block_step [] [bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank17, bank18, bank19, bank20, bank21, bank22, bank23, bank24, bank25, bank26, bank27, bank28, bank29, bank30, bank31, bank32, bank33, bank34, bank35, bank36, bank37, bank38, bank39, bank40, bank41, bank42, bank43, bank44, bank45, bank46, bank47, bank48, bank49, bank50, bank51, bank52, bank53, bank54, bank55, bank56, bank57, bank58, bank59, bank60, bank61] (True.intro) (⟨excl0, excl1, excl2, excl3, excl4, excl5, excl6, excl7, excl8, excl9, excl10, excl11, excl12, excl13, excl14, excl15, excl16, excl17, excl18, excl19, excl20, excl21, excl22, excl23, excl24, excl25, excl26, excl27, excl28, excl29, excl30, excl31, excl32, excl33, excl34, excl35, excl36, excl37, excl38, excl39, excl40, excl41, excl42, excl43, excl44, excl45, excl46, excl47, excl48, excl49, excl50, excl51, excl52, excl53, excl54, excl55, excl56, excl57, excl58, excl59, excl60, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl62 : Blocked 8 0 bank70 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl63 : Blocked 8 0 bank71 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl64 : Blocked 8 0 bank72 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl65 : Blocked 8 0 bank73 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl66 : Blocked 8 0 bank74 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl67 : Blocked 8 0 bank75 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl68 : Blocked 8 0 bank76 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl69 : Blocked 8 0 bank77 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl70 : Blocked 8 0 bank78 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl71 : Blocked 8 0 bank79 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl72 : Blocked 8 0 bank80 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl73 : Blocked 8 0 bank81 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl74 : Blocked 8 0 bank82 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl75 : Blocked 8 0 bank83 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl76 : Blocked 8 0 bank84 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl77 : Blocked 8 0 bank85 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl78 : Blocked 8 0 bank86 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl79 : Blocked 8 0 bank87 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl80 : Blocked 8 0 bank88 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl81 : Blocked 9 0 bank62 :=
  block_step [] [bank70, bank71, bank72, bank73, bank74, bank75, bank76, bank77, bank78, bank79, bank80, bank81, bank82, bank83, bank84, bank85, bank86, bank87, bank88] (True.intro) (⟨excl62, excl63, excl64, excl65, excl66, excl67, excl68, excl69, excl70, excl71, excl72, excl73, excl74, excl75, excl76, excl77, excl78, excl79, excl80, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl82 : Blocked 8 0 bank89 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl83 : Blocked 8 0 bank90 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl84 : Blocked 8 0 bank91 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl85 : Blocked 8 0 bank92 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl86 : Blocked 8 0 bank93 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl87 : Blocked 8 0 bank94 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl88 : Blocked 8 0 bank95 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl89 : Blocked 8 0 bank96 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl90 : Blocked 8 0 bank97 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl91 : Blocked 8 0 bank98 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl92 : Blocked 8 0 bank99 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl93 : Blocked 8 0 bank100 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl94 : Blocked 8 0 bank101 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl95 : Blocked 8 0 bank102 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl96 : Blocked 8 0 bank103 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl97 : Blocked 8 0 bank104 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl98 : Blocked 8 0 bank105 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl99 : Blocked 8 0 bank106 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl100 : Blocked 8 0 bank107 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl101 : Blocked 8 0 bank108 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl102 : Blocked 8 0 bank109 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl103 : Blocked 9 0 bank63 :=
  block_step [] [bank89, bank90, bank91, bank92, bank93, bank94, bank95, bank96, bank97, bank98, bank99, bank100, bank101, bank102, bank103, bank104, bank105, bank106, bank107, bank108, bank109] (True.intro) (⟨excl82, excl83, excl84, excl85, excl86, excl87, excl88, excl89, excl90, excl91, excl92, excl93, excl94, excl95, excl96, excl97, excl98, excl99, excl100, excl101, excl102, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl104 : Blocked 8 0 bank110 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl105 : Blocked 8 0 bank111 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl106 : Blocked 8 0 bank112 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl107 : Blocked 8 0 bank113 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl108 : Blocked 8 0 bank114 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl109 : Blocked 8 0 bank115 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl110 : Blocked 8 0 bank116 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl111 : Blocked 8 0 bank117 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl112 : Blocked 8 0 bank118 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl113 : Blocked 8 0 bank119 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl114 : Blocked 8 0 bank120 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl115 : Blocked 8 0 bank121 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl116 : Blocked 8 0 bank122 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl117 : Blocked 8 0 bank123 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl118 : Blocked 8 0 bank124 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl119 : Blocked 8 0 bank125 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl120 : Blocked 8 0 bank126 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl121 : Blocked 8 0 bank127 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl122 : Blocked 8 0 bank128 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl123 : Blocked 9 0 bank64 :=
  block_step [] [bank110, bank111, bank112, bank113, bank114, bank115, bank116, bank117, bank118, bank119, bank120, bank121, bank122, bank123, bank124, bank125, bank126, bank127, bank128] (True.intro) (⟨excl104, excl105, excl106, excl107, excl108, excl109, excl110, excl111, excl112, excl113, excl114, excl115, excl116, excl117, excl118, excl119, excl120, excl121, excl122, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl124 : Blocked 8 0 bank129 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl125 : Blocked 8 0 bank130 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl126 : Blocked 8 0 bank131 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl127 : Blocked 8 0 bank132 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl128 : Blocked 8 0 bank133 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl129 : Blocked 8 0 bank134 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl130 : Blocked 8 0 bank135 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl131 : Blocked 8 0 bank136 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl132 : Blocked 8 0 bank137 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl133 : Blocked 8 0 bank138 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl134 : Blocked 8 0 bank139 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl135 : Blocked 8 0 bank140 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl136 : Blocked 8 0 bank141 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl137 : Blocked 8 0 bank142 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl138 : Blocked 8 0 bank143 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl139 : Blocked 8 0 bank144 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl140 : Blocked 8 0 bank145 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl141 : Blocked 8 0 bank146 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl142 : Blocked 8 0 bank147 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl143 : Blocked 9 0 bank65 :=
  block_step [] [bank129, bank130, bank131, bank132, bank133, bank134, bank135, bank136, bank137, bank138, bank139, bank140, bank141, bank142, bank143, bank144, bank145, bank146, bank147] (True.intro) (⟨excl124, excl125, excl126, excl127, excl128, excl129, excl130, excl131, excl132, excl133, excl134, excl135, excl136, excl137, excl138, excl139, excl140, excl141, excl142, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl144 : Blocked 8 0 bank148 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl145 : Blocked 8 0 bank149 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl146 : Blocked 8 0 bank150 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl147 : Blocked 8 0 bank151 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl148 : Blocked 8 0 bank152 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl149 : Blocked 8 0 bank153 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl150 : Blocked 8 0 bank154 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl151 : Blocked 8 0 bank155 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl152 : Blocked 8 0 bank156 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl153 : Blocked 8 0 bank157 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl154 : Blocked 8 0 bank158 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl155 : Blocked 8 0 bank159 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl156 : Blocked 8 0 bank160 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl157 : Blocked 8 0 bank161 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl158 : Blocked 8 0 bank162 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl159 : Blocked 8 0 bank163 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl160 : Blocked 8 0 bank164 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl161 : Blocked 8 0 bank165 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl162 : Blocked 8 0 bank166 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl163 : Blocked 9 0 bank66 :=
  block_step [] [bank148, bank149, bank150, bank151, bank152, bank153, bank154, bank155, bank156, bank157, bank158, bank159, bank160, bank161, bank162, bank163, bank164, bank165, bank166] (True.intro) (⟨excl144, excl145, excl146, excl147, excl148, excl149, excl150, excl151, excl152, excl153, excl154, excl155, excl156, excl157, excl158, excl159, excl160, excl161, excl162, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl164 : Blocked 8 0 bank167 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl165 : Blocked 8 0 bank168 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl166 : Blocked 8 0 bank169 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl167 : Blocked 8 0 bank170 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl168 : Blocked 8 0 bank171 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl169 : Blocked 8 0 bank172 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl170 : Blocked 8 0 bank173 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl171 : Blocked 8 0 bank174 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl172 : Blocked 8 0 bank175 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl173 : Blocked 8 0 bank176 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl174 : Blocked 8 0 bank177 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl175 : Blocked 8 0 bank178 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl176 : Blocked 8 0 bank179 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl177 : Blocked 8 0 bank180 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl178 : Blocked 8 0 bank181 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl179 : Blocked 8 0 bank182 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl180 : Blocked 8 0 bank183 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl181 : Blocked 8 0 bank184 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl182 : Blocked 8 0 bank185 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl183 : Blocked 9 0 bank67 :=
  block_step [] [bank167, bank168, bank169, bank170, bank171, bank172, bank173, bank174, bank175, bank176, bank177, bank178, bank179, bank180, bank181, bank182, bank183, bank184, bank185] (True.intro) (⟨excl164, excl165, excl166, excl167, excl168, excl169, excl170, excl171, excl172, excl173, excl174, excl175, excl176, excl177, excl178, excl179, excl180, excl181, excl182, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl184 : Blocked 8 0 bank186 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl185 : Blocked 8 0 bank187 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl186 : Blocked 8 0 bank188 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl187 : Blocked 8 0 bank189 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl188 : Blocked 8 0 bank190 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl189 : Blocked 8 0 bank191 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl190 : Blocked 8 0 bank192 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl191 : Blocked 8 0 bank193 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl192 : Blocked 8 0 bank194 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl193 : Blocked 8 0 bank195 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl194 : Blocked 8 0 bank196 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl195 : Blocked 8 0 bank197 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl196 : Blocked 8 0 bank198 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl197 : Blocked 8 0 bank199 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl198 : Blocked 8 0 bank200 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl199 : Blocked 8 0 bank201 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl200 : Blocked 8 0 bank202 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl201 : Blocked 8 0 bank203 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl202 : Blocked 8 0 bank204 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl203 : Blocked 8 0 bank205 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl204 : Blocked 8 0 bank206 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl205 : Blocked 9 0 bank68 :=
  block_step [] [bank186, bank187, bank188, bank189, bank190, bank191, bank192, bank193, bank194, bank195, bank196, bank197, bank198, bank199, bank200, bank201, bank202, bank203, bank204, bank205, bank206] (True.intro) (⟨excl184, excl185, excl186, excl187, excl188, excl189, excl190, excl191, excl192, excl193, excl194, excl195, excl196, excl197, excl198, excl199, excl200, excl201, excl202, excl203, excl204, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl206 : Blocked 8 0 bank207 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl207 : Blocked 8 0 bank208 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl208 : Blocked 8 0 bank209 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl209 : Blocked 8 0 bank210 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl210 : Blocked 8 0 bank211 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl211 : Blocked 8 0 bank212 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl212 : Blocked 8 0 bank213 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl213 : Blocked 8 0 bank214 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl214 : Blocked 8 0 bank215 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl215 : Blocked 8 0 bank216 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl216 : Blocked 8 0 bank217 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl217 : Blocked 8 0 bank218 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl218 : Blocked 8 0 bank219 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl219 : Blocked 8 0 bank220 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl220 : Blocked 8 0 bank221 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl221 : Blocked 8 0 bank222 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl222 : Blocked 8 0 bank223 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl223 : Blocked 8 0 bank224 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl224 : Blocked 8 0 bank225 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl225 : Blocked 8 0 bank226 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl226 : Blocked 8 0 bank227 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl227 : Blocked 8 0 bank228 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl228 : Blocked 8 0 bank229 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl229 : Blocked 8 0 bank230 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl230 : Blocked 8 0 bank231 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl231 : Blocked 9 0 bank69 :=
  block_step [] [bank207, bank208, bank209, bank210, bank211, bank212, bank213, bank214, bank215, bank216, bank217, bank218, bank219, bank220, bank221, bank222, bank223, bank224, bank225, bank226, bank227, bank228, bank229, bank230, bank231] (True.intro) (⟨excl206, excl207, excl208, excl209, excl210, excl211, excl212, excl213, excl214, excl215, excl216, excl217, excl218, excl219, excl220, excl221, excl222, excl223, excl224, excl225, excl226, excl227, excl228, excl229, excl230, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl232 : Blocked 9 1 bank1 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl233 : Blocked 9 1 bank2 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl234 : Blocked 9 1 bank3 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl235 : Blocked 9 1 bank4 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl236 : Blocked 9 1 bank5 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl237 : Blocked 9 1 bank6 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl238 : Blocked 9 1 bank7 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl239 : Blocked 9 1 bank8 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl240 : Blocked 9 1 bank9 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl241 : Blocked 9 1 bank10 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl242 : Blocked 9 1 bank11 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl243 : Blocked 9 1 bank12 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl244 : Blocked 9 1 bank13 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl245 : Blocked 9 1 bank14 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl246 : Blocked 9 1 bank15 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl247 : Blocked 9 1 bank16 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl248 : Blocked 9 1 bank17 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl249 : Blocked 9 1 bank18 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl250 : Blocked 9 1 bank19 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl251 : Blocked 9 1 bank20 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl252 : Blocked 9 1 bank21 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl253 : Blocked 9 1 bank22 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl254 : Blocked 9 1 bank23 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl255 : Blocked 9 1 bank24 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl256 : Blocked 9 1 bank25 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl257 : Blocked 9 1 bank26 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl258 : Blocked 9 1 bank27 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl259 : Blocked 9 1 bank28 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl260 : Blocked 9 1 bank29 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl261 : Blocked 9 1 bank30 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl262 : Blocked 9 1 bank31 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl263 : Blocked 9 1 bank32 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl264 : Blocked 9 1 bank33 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl265 : Blocked 9 1 bank34 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl266 : Blocked 9 1 bank35 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl267 : Blocked 9 1 bank36 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl268 : Blocked 9 1 bank37 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl269 : Blocked 9 1 bank38 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl270 : Blocked 9 1 bank39 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl271 : Blocked 9 1 bank40 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl272 : Blocked 9 1 bank41 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl273 : Blocked 9 1 bank42 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl274 : Blocked 9 1 bank43 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl275 : Blocked 9 1 bank44 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl276 : Blocked 9 1 bank45 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl277 : Blocked 9 1 bank46 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl278 : Blocked 9 1 bank47 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl279 : Blocked 9 1 bank48 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl280 : Blocked 9 1 bank49 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl281 : Blocked 9 1 bank50 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl282 : Blocked 9 1 bank51 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl283 : Blocked 9 1 bank52 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl284 : Blocked 9 1 bank53 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl285 : Blocked 9 1 bank54 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl286 : Blocked 9 1 bank55 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl287 : Blocked 9 1 bank56 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl288 : Blocked 8 0 bank232 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl289 : Blocked 8 1 bank233 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl290 : Blocked 8 1 bank234 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl291 : Blocked 8 1 bank235 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl292 : Blocked 8 1 bank236 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl293 : Blocked 8 1 bank237 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl294 : Blocked 8 1 bank238 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl295 : Blocked 8 1 bank239 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl296 : Blocked 8 1 bank240 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl297 : Blocked 8 1 bank241 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl298 : Blocked 9 1 bank57 :=
  block_step [bank232, bank98, bank117, bank136, bank162, bank181, bank202, bank227] [bank233, bank234, bank235, bank236, bank237, bank238, bank239, bank240, bank241] (⟨excl288, excl91, excl111, excl131, excl158, excl178, excl200, excl226, True.intro⟩) (⟨excl289, excl290, excl291, excl292, excl293, excl294, excl295, excl296, excl297, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl299 : Blocked 8 0 bank242 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl300 : Blocked 8 1 bank243 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl301 : Blocked 8 1 bank244 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl302 : Blocked 8 1 bank245 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl303 : Blocked 8 1 bank246 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl304 : Blocked 8 1 bank247 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl305 : Blocked 8 1 bank248 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl306 : Blocked 8 1 bank249 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl307 : Blocked 8 1 bank250 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl308 : Blocked 9 1 bank58 :=
  block_step [bank78, bank99, bank125, bank242, bank163, bank182, bank203, bank228] [bank243, bank238, bank244, bank245, bank246, bank247, bank248, bank249, bank250] (⟨excl70, excl92, excl119, excl299, excl159, excl179, excl201, excl227, True.intro⟩) (⟨excl300, excl294, excl301, excl302, excl303, excl304, excl305, excl306, excl307, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl309 : Blocked 8 0 bank251 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl310 : Blocked 8 1 bank252 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl311 : Blocked 8 1 bank253 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl312 : Blocked 8 1 bank254 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl313 : Blocked 8 1 bank255 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl314 : Blocked 8 1 bank256 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl315 : Blocked 8 1 bank257 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl316 : Blocked 9 1 bank59 :=
  block_step [bank86, bank107, bank126, bank145, bank251, bank183, bank204, bank229] [bank252, bank239, bank244, bank253, bank254, bank255, bank256, bank257, bank250] (⟨excl78, excl100, excl120, excl140, excl309, excl180, excl202, excl228, True.intro⟩) (⟨excl310, excl295, excl301, excl311, excl312, excl313, excl314, excl315, excl307, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl317 : Blocked 9 1 bank60 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl318 : Blocked 9 1 bank61 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl319 : Blocked 10 1 root :=
  block_step [bank62, bank63, bank64, bank65, bank66, bank67, bank68, bank69] [bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank17, bank18, bank19, bank20, bank21, bank22, bank23, bank24, bank25, bank26, bank27, bank28, bank29, bank30, bank31, bank32, bank33, bank34, bank35, bank36, bank37, bank38, bank39, bank40, bank41, bank42, bank43, bank44, bank45, bank46, bank47, bank48, bank49, bank50, bank51, bank52, bank53, bank54, bank55, bank56, bank57, bank58, bank59, bank60, bank61] (⟨excl81, excl103, excl123, excl143, excl163, excl183, excl205, excl231, True.intro⟩) (⟨excl232, excl233, excl234, excl235, excl236, excl237, excl238, excl239, excl240, excl241, excl242, excl243, excl244, excl245, excl246, excl247, excl248, excl249, excl250, excl251, excl252, excl253, excl254, excl255, excl256, excl257, excl258, excl259, excl260, excl261, excl262, excl263, excl264, excl265, excl266, excl267, excl268, excl269, excl270, excl271, excl272, excl273, excl274, excl275, excl276, excl277, excl278, excl279, excl280, excl281, excl282, excl283, excl284, excl285, excl286, excl287, excl298, excl308, excl316, excl317, excl318, True.intro⟩) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_28654_aux

open PEqualNP.Outside.L_meta_28654_aux in
theorem PEqualNP.Outside.L_meta_28654 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o basis single computes
  by_cases used : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact ⟨replacement.gates, replacement.output, replacement_basis,
      lower_with_not gates o basis single used computes excl61 excl319, replacement_correct⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    refine ⟨?_, (basis g hg).2⟩
    rcases (basis g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (used ⟨g, hg, h⟩).elim

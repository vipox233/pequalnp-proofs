import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26688_aux
-- Live-wire search adapted from L-meta-10852, following Vkuparin, ljste and jfsantoropereira.
-- Paired edge/independent-set inputs and the replacement circuit are specific to this graph.

abbrev B := BitVec 63
abbrev Sig := B × B
def top : B := BitVec.allOnes 63
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
  by_cases hi : i < 63
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 63 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 63
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 63 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 63)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 63) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 63 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 63)] <;> simp [hi]
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

def bit (side : Bool) (i : Fin 63) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 63).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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
def sample (raw : List Sig) (s : Bool) (i : Fin 63) (j : Fin 8) := bit s i (raw.getD j.val zero)
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

def root : List Sig := [(0x8208470429853f,0x4100208415), (0x37e36641b3846cc,0x17e16640b38444c), (0xc0dfe646236670c,0x405fe642222670c), (0x3030c478ff38670c,0x10104448ff38670c), (0x4041078083c0780f,0x4800240480a), (0x7f81f800fc007ff0,0x7e81e800f40033a0), (0x7ffe0000ffff8000,0x7bfa0000dd9d0000), (0x7fffffff00000000,0x6fefbb3600000000)]

def goalTable : Nat := 0xfffffffefffffffaffffffeeffffffaafffffefefffffafaffffeeeeaaaa0000

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
  decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 0, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 0, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 0, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def replacement : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [8, 1]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [12, 6]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [14, 7]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [17, 15]⟩], 18⟩

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

def sig0 : Sig := (0xf,0x0)
def sig1 : Sig := (0x8208470429853f,0x4100208415)
def sig2 : Sig := (0x4041078083c0780f,0x4800240480a)
def sig3 : Sig := (0x37e36641b3846cc,0x17e16640b38444c)
def sig4 : Sig := (0xc0dfe646236670c,0x405fe642222670c)
def sig5 : Sig := (0x3030c478ff38670c,0x10104448ff38670c)
def sig6 : Sig := (0x7fffffff00000000,0x6fefbb3600000000)
def sig7 : Sig := (0x7ffe0000ffff8000,0x7bfa0000dd9d0000)
def sig8 : Sig := (0x7f81f800fc007ff0,0x7e81e800f40033a0)
def sig9 : Sig := (0x80080004000530,0x0)
def sig10 : Sig := (0x82000004298000,0x0)
def sig11 : Sig := (0x82084700000000,0x0)
def sig12 : Sig := (0x3003000180046c0,0x0)
def sig13 : Sig := (0xc0c000062360000,0x0)
def sig14 : Sig := (0x3030c47800000000,0x0)
def sig15 : Sig := (0x4001000080007800,0x0)
def sig16 : Sig := (0x4040000083c00000,0x0)
def sig17 : Sig := (0x4041078000000000,0x0)
def sig18 : Sig := (0x400428050c,0x4000200404)
def sig19 : Sig := (0x8440020050c,0x4000200404)
def sig20 : Sig := (0x200440028040c,0x4000200404)
def sig21 : Sig := (0x4008300600c,0x40002004008)
def sig22 : Sig := (0x106000200600c,0x40002004008)
def sig23 : Sig := (0x4006000300400c,0x40002004008)
def sig24 : Sig := (0x40c30fc787e9fd3f,0x4c10260cc1f)
def sig25 : Sig := (0xc4606230670c,0x44402220670c)
def sig26 : Sig := (0xc36640230460c,0x416640220440c)
def sig27 : Sig := (0x3004601b38460c,0x1004400b38440c)
def sig28 : Sig := (0x37e366400000000,0x16e122400000000)
def sig29 : Sig := (0x37e00001b380000,0x17a000009180000)
def sig30 : Sig := (0x3fe3e671f39c7ff,0x17e16650b38c45d)
def sig31 : Sig := (0x437f37e49bf87ecf,0x17e16e40b784c4e)
def sig32 : Sig := (0xc01f80060006700,0x401e80020002300)
def sig33 : Sig := (0xc0dfe6400000000,0x405ba2400000000)
def sig34 : Sig := (0xc8ffe67663fe73f,0x405fe652222e71d)
def sig35 : Sig := (0x4c4dffe4e3f67f0f,0x405fee422626f0e)
def sig36 : Sig := (0xf7ffe647b3e67cc,0x57ffe642b3a674c)
def sig37 : Sig := (0x3000c000fc006700,0x10004000f4002300)
def sig38 : Sig := (0x30300000ff380000,0x10100000dd180000)
def sig39 : Sig := (0x30b2cc7fff39e73f,0x10104449ff38e71d)
def sig40 : Sig := (0x7071c7f8fff87f0f,0x101044c8ff786f0e)
def sig41 : Sig := (0x337ef67cff3867cc,0x117e566cff38674c)
def sig42 : Sig := (0x3c3dfe7cff3e670c,0x1415fe6cff3a670c)
def sig43 : Sig := (0x7ffe000000000000,0x6bea000000000000)
def sig44 : Sig := (0x7f81f80000000000,0x6e81a80000000000)
def sig45 : Sig := (0x7fffffff0429853f,0x6fefbb7700208415)
def sig46 : Sig := (0x7fffffff83c0780f,0x6fefbfb60240480a)
def sig47 : Sig := (0x7fffffff6236670c,0x6fefff762222670c)
def sig48 : Sig := (0x7fffffff1b3846cc,0x6fffbf760b38444c)
def sig49 : Sig := (0x7f800000fc000000,0x7a800000d4000000)
def sig50 : Sig := (0x7ffe0847ffff853f,0x7bfa0041ddbd8415)
def sig51 : Sig := (0x7fff0780fffff80f,0x7bfa0480dfdd480a)
def sig52 : Sig := (0x7ffec478ffffe70c,0x7bfa4448ffbd670c)
def sig53 : Sig := (0x7ffe3664ffffc6cc,0x7bfe1664dfbd444c)
def sig54 : Sig := (0x7f83f847fc29ffff,0x7e81e841f420b7b5)
def sig55 : Sig := (0x7fc1ff80ffc07fff,0x7e81ec80f6407baa)
def sig56 : Sig := (0x7f8dfe64fe367ffc,0x7e85fe64f62277ac)
def sig57 : Sig := (0x7fb1fc78ff387ffc,0x7e91ec48ff3877ac)
def sig58 : Sig := (0x7ffffffffc007ff0,0x7feffb36f40033a0)
def sig59 : Sig := (0x7ffff800fffffff0,0x7ffbe800fd9d33a0)
def sig60 : Sig := (0x7fffffffffff8000,0x7fffbb36dd9d0000)
def sig61 : Sig := (0x7ffffe64ff387ffc,0x7ffffe64ff3877ec)
def sig62 : Sig := (0x7ffffe64ffffe70c,0x7ffffe64ffbf670c)
def sig63 : Sig := (0x7fffffffff38670c,0x7fffff7eff38670c)
def sig64 : Sig := (0x7ffe3000ffffc6c0,0x7bfa0000dd9d0000)
def sig65 : Sig := (0x7fffffff180046c0,0x6fefbb3600000000)
def sig66 : Sig := (0x3330f478ff3867cc,0x10104448ff38670c)
def sig67 : Sig := (0xf0dfe647a3667cc,0x405fe642222670c)
def sig68 : Sig := (0x434137809bc07ecf,0x4800240480a)
def sig69 : Sig := (0x38238471c29c7ff,0x4100208415)
def sig70 : Sig := (0x4c4d0780e3f6780f,0x4800240480a)
def sig71 : Sig := (0xc8e0847663f853f,0x4100208415)
def sig72 : Sig := (0xf0c30007a3646c0,0x0)
def sig73 : Sig := (0x7071c7f883c0780f,0x4800240480a)
def sig74 : Sig := (0x30b2cc7f0429853f,0x4100208415)
def sig75 : Sig := (0x3330f478180046c0,0x0)
def sig76 : Sig := (0x7f8df800fe367ff0,0x7e81e800f40033a0)
def sig77 : Sig := (0x7fffffff62360000,0x6fefbb3600000000)
def sig78 : Sig := (0x3c3cc478ff3e670c,0x10104448ff38670c)
def sig79 : Sig := (0xf7e36647b3e46cc,0x17e16640b38444c)
def sig80 : Sig := (0x3c3cc47862360000,0x0)
def sig81 : Sig := (0x7fb1fc78fc007ff0,0x7e81e800f40033a0)
def sig82 : Sig := (0x7ffec478ffff8000,0x7bfa0000dd9d0000)
def sig83 : Sig := (0x3c3dfe7c6236670c,0x405fe642222670c)
def sig84 : Sig := (0x337ef67c1b3846cc,0x17e16640b38444c)
def sig85 : Sig := (0x37e3664180046c0,0x16e122400000000)
def sig86 : Sig := (0x3030c478fc006700,0x10004000f4002300)
def sig87 : Sig := (0x37e30001b3846c0,0x17a000009180000)
def sig88 : Sig := (0xc0df80062366700,0x401e80020002300)
def sig89 : Sig := (0xc0dfe6462360000,0x405ba2400000000)
def sig90 : Sig := (0x3030c478ff380000,0x10100000dd180000)
def sig91 : Sig := (0x7e07ff03ff800f,0x17e17ff0bffcc5f)
def sig92 : Sig := (0x1ffff00007fff,0x405ffff2262ffff)
def sig93 : Sig := (0xffffffff,0x101044c9ffffffff)
def sig94 : Sig := (0x4fcf3b8700c798f3,0x6fefbbb700c798f3)
def sig95 : Sig := (0x73f2019b9dc998f3,0x7bfa019bdddd98f3)
def sig96 : Sig := (0x7c81c99be4c7b933,0x7e81e99bf4c7bbb3)
def sig97 : Sig := (0x3fbef87f7c3f87f0,0x7ffffb7ffdbfb7f5)
def sig98 : Sig := (0x7f7df7b8fbd67ac0,0x7fffffbeffdf7bea)
def sig99 : Sig := (0x200470029800f,0x4100208415)
def sig100 : Sig := (0x40078003c0000f,0x4800240480a)
def sig101 : Sig := (0xc06640236000c,0x416640222440c)
def sig102 : Sig := (0x3004780338000c,0x1004480b38440c)
def sig103 : Sig := (0x7e07ff00000000,0x16e133600000000)
def sig104 : Sig := (0x7e000003ff8000,0x17a0000099d0000)
def sig105 : Sig := (0x7e06640338000c,0x17e16640b38444c)
def sig106 : Sig := (0xfe0fff07ff853f,0x17e17ff0bffcc5f)
def sig107 : Sig := (0x37e37ff1bffc6cf,0x17e17ff0bffcc5f)
def sig108 : Sig := (0x407f07ff83fff80f,0x17e17ff0bffcc5f)
def sig109 : Sig := (0xc7fffff63ffe70f,0x57fffff2bffef5f)
def sig110 : Sig := (0x307ec7ffffffe70f,0x117e57ffffffef5f)
def sig111 : Sig := (0x7fffffff03ff800f,0x6fffbfff0bffcc5f)
def sig112 : Sig := (0x7ffe07ffffff800f,0x7bfe17ffdfffcc5f)
def sig113 : Sig := (0x8470000053f,0x4100208415)
def sig114 : Sig := (0x107800000780f,0x4800240480a)
def sig115 : Sig := (0xc4780000670c,0x44482220670c)
def sig116 : Sig := (0x3664000046cc,0x416640220444c)
def sig117 : Sig := (0x1f80000007ff0,0x401e800200033a0)
def sig118 : Sig := (0x1ffff00000000,0x405bb3600000000)
def sig119 : Sig := (0x1fe640000670c,0x405fe642222670c)
def sig120 : Sig := (0x83ffff0429ffff,0x405ffff2262ffff)
def sig121 : Sig := (0xc0dffff62367fff,0x405ffff2262ffff)
def sig122 : Sig := (0x4041ffff83c07fff,0x405ffff2262ffff)
def sig123 : Sig := (0x37fffff1b387fff,0x57fffff2b7affff)
def sig124 : Sig := (0x3031ffffff387fff,0x1415ffffff7affff)
def sig125 : Sig := (0x7fffffff00007fff,0x6fefffff2262ffff)
def sig126 : Sig := (0x7f81fffffc007fff,0x7e85fffff662ffff)
def sig127 : Sig := (0x429853f,0x4100208415)
def sig128 : Sig := (0x83c0780f,0x4800240480a)
def sig129 : Sig := (0x6236670c,0x44402222670c)
def sig130 : Sig := (0x1b3846cc,0x1004400b38444c)
def sig131 : Sig := (0xfc007ff0,0x10004000f40033a0)
def sig132 : Sig := (0xffff8000,0x10100000dd9d0000)
def sig133 : Sig := (0xff38670c,0x10104448ff38670c)
def sig134 : Sig := (0x820847ffffffff,0x101044c9ffffffff)
def sig135 : Sig := (0x3030c478ffffffff,0x101044c9ffffffff)
def sig136 : Sig := (0x40410780ffffffff,0x101044c9ffffffff)
def sig137 : Sig := (0x37e3664ffffffff,0x117e56edffffffff)
def sig138 : Sig := (0xc0dfe64ffffffff,0x1415feedffffffff)
def sig139 : Sig := (0x7ffe0000ffffffff,0x7bfa44c9ffffffff)
def sig140 : Sig := (0x7f81f800ffffffff,0x7e91ecc9ffffffff)
def sig141 : Sig := (0x82080700018033,0x100008011)
def sig142 : Sig := (0x4041038000c01803,0x8000400802)
def sig143 : Sig := (0x34e3204000000c0,0x16e122400000040)
def sig144 : Sig := (0xc0d3a0400060000,0x405ba2400020000)
def sig145 : Sig := (0x4fce000000c78000,0x6bea000000850000)
def sig146 : Sig := (0x4f813800000018f0,0x6e81a800000010a0)
def sig147 : Sig := (0x4fcf3b8700000000,0x6fefbb3600000000)
def sig148 : Sig := (0x7fffffff00c798f3,0x6fefbbb700c798f3)
def sig149 : Sig := (0x4fcf3bc704ef9dff,0x6fefbbf700e79cf7)
def sig150 : Sig := (0x4fcf3f8783c7f8ff,0x6fefbfb702c7d8fb)
def sig151 : Sig := (0x4fcfffe762f7ffff,0x6feffff722e7ffff)
def sig152 : Sig := (0x4fff3fe71bffdeff,0x6fffbff70bffdcff)
def sig153 : Sig := (0x7fcffb87fcc7fff3,0x7feffbb7f4c7bbf3)
def sig154 : Sig := (0x7fff3b87ffff98f3,0x7fffbbb7dddf98f3)
def sig155 : Sig := (0x82000304098033,0x100008011)
def sig156 : Sig := (0x4040018081c01803,0x8000400802)
def sig157 : Sig := (0x3720000190800c0,0x17a000009180040)
def sig158 : Sig := (0x303000189d080000,0x10100008dd180000)
def sig159 : Sig := (0x73f2019b00000000,0x6bea011200000000)
def sig160 : Sig := (0x738000009c0018f0,0x7a800000d40010a0)
def sig161 : Sig := (0x73f200009dc98000,0x7bfa0000dd9d0000)
def sig162 : Sig := (0x7ffe019bffff98f3,0x7bfa019bdddd98f3)
def sig163 : Sig := (0x73f209df9de99dff,0x7bfa01dbddfd9cf7)
def sig164 : Sig := (0x73f3079b9fc9f8ff,0x7bfa059bdfddd8fb)
def sig165 : Sig := (0x73f2c5fbfff9ffff,0x7bfa45dbfffdffff)
def sig166 : Sig := (0x73fe37ff9ff9deff,0x7bfe17ffdffddcff)
def sig167 : Sig := (0x7ff3f99bfdc9fff3,0x7ffbe99bfdddbbf3)
def sig168 : Sig := (0x7fffffff9dc998f3,0x7fffbbbfdddd98f3)
def sig169 : Sig := (0x80080304018133,0x100008011)
def sig170 : Sig := (0x4001018080c03803,0x8000400802)
def sig171 : Sig := (0xc01c80060062100,0x401e80020022300)
def sig172 : Sig := (0x3000c018e4002100,0x10004008f4002300)
def sig173 : Sig := (0x7c81c99b00000000,0x6e81a91200000000)
def sig174 : Sig := (0x7c800000e4c78000,0x7a800000d4850000)
def sig175 : Sig := (0x7c81c800e4003930,0x7e81e800f40033a0)
def sig176 : Sig := (0x7f81f99bfcc7fff3,0x7e81e99bf4c7bbb3)
def sig177 : Sig := (0x7c83c9dfe4efbd3f,0x7e81e9dbf4e7bfb7)
def sig178 : Sig := (0x7cc1cf9be7c7f93f,0x7e81ed9bf6c7fbbb)
def sig179 : Sig := (0x7c8dffffe6f7ff3f,0x7e85fffff6e7ffbf)
def sig180 : Sig := (0x7cb1cdfbffffff3f,0x7e91eddbffffffbf)
def sig181 : Sig := (0x7fffffffe4c7b933,0x7feffbbff4c7bbb3)
def sig182 : Sig := (0x7fffc99bffffb933,0x7ffbe99bfddfbbb3)
def sig183 : Sig := (0x82084704298530,0x4100208415)
def sig184 : Sig := (0x33e3064183806c0,0x17e126409380444)
def sig185 : Sig := (0xc0cf86460360700,0x405fa6420222704)
def sig186 : Sig := (0x3030c0787c380700,0x10104048fd382704)
def sig187 : Sig := (0x3fbef87f00000000,0x6fefbb3600000000)
def sig188 : Sig := (0x3fbe00007c3f8000,0x7bfa0000dd9d0000)
def sig189 : Sig := (0x3f80f8007c0007f0,0x7e81e800f40033a0)
def sig190 : Sig := (0x3fbef87f7c3f87ff,0x7ffffb7ffdbfb7f5)
def sig191 : Sig := (0x7fbff87ffc3ffff0,0x7ffffb7ffdbfb7f5)
def sig192 : Sig := (0x7ffef87fffff87f0,0x7ffffb7ffdbfb7f5)
def sig193 : Sig := (0x7fffffff7c3f87f0,0x7ffffb7ffdbfb7f5)
def sig194 : Sig := (0x3fbefc7fff3fe7fc,0x7fffff7fffbff7fd)
def sig195 : Sig := (0x3fbffe7f7e3fe7fc,0x7fffff7fffbff7fd)
def sig196 : Sig := (0x3ffefe7f7f3fc7fc,0x7fffff7fffbff7fd)
def sig197 : Sig := (0x4041078083c07800,0x4800240480a)
def sig198 : Sig := (0x37c36201b1042c0,0x17e16240b184048)
def sig199 : Sig := (0xc0df62062166200,0x405fe2422026308)
def sig200 : Sig := (0x3030c438fb106200,0x10104408ff186308)
def sig201 : Sig := (0x7f7df7b800000000,0x6fefbb3600000000)
def sig202 : Sig := (0x7f7c0000fbd60000,0x7bfa0000dd9d0000)
def sig203 : Sig := (0x7f01f000f8007ac0,0x7e81e800f40033a0)
def sig204 : Sig := (0x7f7df7b8fbd67acf,0x7fffffbeffdf7bea)
def sig205 : Sig := (0x7ffdffb8ffd67ff0,0x7fffffbeffdf7bea)
def sig206 : Sig := (0x7ffff7b8fffffac0,0x7fffffbeffdf7bea)
def sig207 : Sig := (0x7ffffffffbd67ac0,0x7fffffbeffdf7bea)
def sig208 : Sig := (0x7f7df7f8fffe7fcc,0x7ffffffeffff7fee)
def sig209 : Sig := (0x7f7dfffcfbf67fcc,0x7ffffffeffff7fee)
def sig210 : Sig := (0x7f7ff7fcfbfe7ecc,0x7ffffffeffff7fee)
def sig211 : Sig := (0x7cffcfffe7ffb93f,0x7fffffffffffffff)
def sig212 : Sig := (0x3cbec87f643f8130,0x7ffffb7ffdbfb7f5)
def sig213 : Sig := (0x7371f7f8fff87fcf,0x101044c8ff786f0e)
def sig214 : Sig := (0x4f4dffe4fbf67fcf,0x405fee422626f0e)
def sig215 : Sig := (0x7c7dc7b8e3d63800,0x7fffffbeffdf7bea)
def sig216 : Sig := (0x33b2fc7fff39e7ff,0x10104449ff38e71d)
def sig217 : Sig := (0xf8ffe677e3fe7ff,0x405fe652222e71d)
def sig218 : Sig := (0x73f3ffff9dc9ffff,0x7fffffffffffffff)
def sig219 : Sig := (0x33b2f87f1c0987f0,0x7ffffb7ffdbfb7f5)
def sig220 : Sig := (0x7c7dc7f8fffe7f0f,0x101044c8ff786f0e)
def sig221 : Sig := (0x4f7f37e4fbfe7ecf,0x17e16e40b784c4e)
def sig222 : Sig := (0x7371f7b899c07ac0,0x7fffffbeffdf7bea)
def sig223 : Sig := (0x3cbecc7fff3fe73f,0x10104449ff38e71d)
def sig224 : Sig := (0xffe3e677f3fc7ff,0x17e16650b38c45d)
def sig225 : Sig := (0x4fcf3b87ffffffff,0x7fffffffffffffff)
def sig226 : Sig := (0xf8e38077c3f87f0,0x7ffffb7ffdbfb7f5)
def sig227 : Sig := (0x7c7dfffce3f67f0f,0x405fee422626f0e)
def sig228 : Sig := (0x737ff7fc9bf87ecf,0x17e16e40b784c4e)
def sig229 : Sig := (0x4f4d3380fbd67ac0,0x7fffffbeffdf7bea)
def sig230 : Sig := (0x3cbffe7f663fe73f,0x405fe652222e71d)
def sig231 : Sig := (0x33fefe7f1f39c7ff,0x17e16650b38c45d)
def sig232 : Sig := (0x3ff800f,0x1004c90bffcc5f)
def sig233 : Sig := (0x7ff0000000f,0x417ff0262cc5f)
def sig234 : Sig := (0x7fff,0x44c92262ffff)
def sig235 : Sig := (0x4f4d338000c618c0,0x6fefbbb600c718e2)
def sig236 : Sig := (0x30b2cc7f00000000,0x0)
def sig237 : Sig := (0x70f3cffffff9ff3f,0x101044c9ff78ef1f)
def sig238 : Sig := (0xf8e3807000780f0,0x6fefbb37008790f1)
def sig239 : Sig := (0x7071c7f800000000,0x0)
def sig240 : Sig := (0x7370019899c018c0,0x7bfa019adddd18e2)
def sig241 : Sig := (0xc8e0000663f8000,0x0)
def sig242 : Sig := (0x4ccfffe7e7ffff3f,0x405fee52262ef1f)
def sig243 : Sig := (0x33b2001b1c0980f0,0x7bfa011bdd9d90f1)
def sig244 : Sig := (0x4c4c0000e3f60000,0x0)
def sig245 : Sig := (0x7c01c198e0c63800,0x7e81e99af4c73ba2)
def sig246 : Sig := (0x38038001c0047f0,0x0)
def sig247 : Sig := (0x43ff3fe79ff9ffff,0x17e16e50b78cc5f)
def sig248 : Sig := (0x3c80c81b64078130,0x7e81e91bf487b3b1)
def sig249 : Sig := (0x4301300098007ec0,0x0)
def bank1 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank2 : List Sig := [sig9, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank3 : List Sig := [sig10, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank4 : List Sig := [sig11, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank5 : List Sig := [sig12, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank6 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig8]
def bank7 : List Sig := [sig13, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank8 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig7, sig8]
def bank9 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank10 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig6, sig7, sig8]
def bank11 : List Sig := [sig15, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank12 : List Sig := [sig16, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank13 : List Sig := [sig17, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank14 : List Sig := [sig18, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank15 : List Sig := [sig19, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank16 : List Sig := [sig20, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank17 : List Sig := [sig1, sig21, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank18 : List Sig := [sig1, sig22, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank19 : List Sig := [sig1, sig23, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank20 : List Sig := [sig1, sig2, sig24, sig3, sig4, sig5, sig6, sig7, sig8]
def bank21 : List Sig := [sig1, sig2, sig25, sig3, sig4, sig5, sig6, sig7, sig8]
def bank22 : List Sig := [sig1, sig2, sig26, sig3, sig4, sig5, sig6, sig7, sig8]
def bank23 : List Sig := [sig1, sig2, sig27, sig3, sig4, sig5, sig6, sig7, sig8]
def bank24 : List Sig := [sig1, sig2, sig28, sig3, sig4, sig5, sig6, sig7, sig8]
def bank25 : List Sig := [sig1, sig2, sig29, sig3, sig4, sig5, sig6, sig7, sig8]
def bank26 : List Sig := [sig1, sig2, sig3, sig30, sig4, sig5, sig6, sig7, sig8]
def bank27 : List Sig := [sig1, sig2, sig3, sig31, sig4, sig5, sig6, sig7, sig8]
def bank28 : List Sig := [sig1, sig2, sig3, sig32, sig4, sig5, sig6, sig7, sig8]
def bank29 : List Sig := [sig1, sig2, sig3, sig33, sig4, sig5, sig6, sig7, sig8]
def bank30 : List Sig := [sig1, sig2, sig3, sig4, sig34, sig5, sig6, sig7, sig8]
def bank31 : List Sig := [sig1, sig2, sig3, sig4, sig35, sig5, sig6, sig7, sig8]
def bank32 : List Sig := [sig1, sig2, sig3, sig4, sig36, sig5, sig6, sig7, sig8]
def bank33 : List Sig := [sig1, sig2, sig3, sig4, sig37, sig5, sig6, sig7, sig8]
def bank34 : List Sig := [sig1, sig2, sig3, sig4, sig38, sig5, sig6, sig7, sig8]
def bank35 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig39, sig6, sig7, sig8]
def bank36 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig40, sig6, sig7, sig8]
def bank37 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig41, sig6, sig7, sig8]
def bank38 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig42, sig6, sig7, sig8]
def bank39 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig43, sig6, sig7, sig8]
def bank40 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig44, sig6, sig7, sig8]
def bank41 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig45, sig7, sig8]
def bank42 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig46, sig7, sig8]
def bank43 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig7, sig8]
def bank44 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig7, sig8]
def bank45 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig49, sig7, sig8]
def bank46 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig50, sig8]
def bank47 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig51, sig8]
def bank48 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig52, sig8]
def bank49 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig53, sig8]
def bank50 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig54]
def bank51 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig55]
def bank52 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig56]
def bank53 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig57]
def bank54 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig58]
def bank55 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig59]
def bank56 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig60]
def bank57 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig61]
def bank58 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig62]
def bank59 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig63]
def bank60 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig8]
def bank61 : List Sig := [sig1, sig2, sig3, sig4, sig40, sig6, sig7, sig8]
def bank62 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8]
def bank63 : List Sig := [sig1, sig2, sig3, sig35, sig5, sig6, sig7, sig8]
def bank64 : List Sig := [sig1, sig2, sig30, sig4, sig5, sig6, sig7, sig8]
def bank65 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8]
def bank66 : List Sig := [sig12, sig13, sig1, sig2, sig5, sig6, sig7, sig8]
def bank67 : List Sig := [sig12, sig14, sig1, sig2, sig4, sig6, sig7, sig8]
def bank68 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig56]
def bank69 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig57]
def bank70 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig58]
def bank71 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig59]
def bank72 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig64, sig8]
def bank73 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig65, sig7, sig8]
def bank74 : List Sig := [sig12, sig1, sig2, sig4, sig66, sig6, sig7, sig8]
def bank75 : List Sig := [sig12, sig1, sig2, sig4, sig39, sig6, sig7, sig8]
def bank76 : List Sig := [sig12, sig1, sig2, sig4, sig40, sig6, sig7, sig8]
def bank77 : List Sig := [sig12, sig1, sig2, sig67, sig5, sig6, sig7, sig8]
def bank78 : List Sig := [sig12, sig1, sig2, sig34, sig5, sig6, sig7, sig8]
def bank79 : List Sig := [sig12, sig1, sig2, sig35, sig5, sig6, sig7, sig8]
def bank80 : List Sig := [sig12, sig1, sig68, sig4, sig5, sig6, sig7, sig8]
def bank81 : List Sig := [sig12, sig69, sig2, sig4, sig5, sig6, sig7, sig8]
def bank82 : List Sig := [sig1, sig69, sig2, sig4, sig5, sig6, sig7, sig8]
def bank83 : List Sig := [sig1, sig2, sig68, sig4, sig5, sig6, sig7, sig8]
def bank84 : List Sig := [sig1, sig68, sig4, sig5, sig6, sig7, sig8]
def bank85 : List Sig := [sig69, sig2, sig4, sig5, sig6, sig7, sig8]
def bank86 : List Sig := [sig12, sig13, sig1, sig2, sig5, sig6, sig59]
def bank87 : List Sig := [sig12, sig1, sig70, sig5, sig6, sig7, sig8]
def bank88 : List Sig := [sig12, sig71, sig2, sig5, sig6, sig7, sig8]
def bank89 : List Sig := [sig13, sig1, sig68, sig5, sig6, sig7, sig8]
def bank90 : List Sig := [sig13, sig69, sig2, sig5, sig6, sig7, sig8]
def bank91 : List Sig := [sig72, sig1, sig2, sig5, sig6, sig7, sig8]
def bank92 : List Sig := [sig12, sig14, sig1, sig2, sig4, sig7, sig58]
def bank93 : List Sig := [sig12, sig1, sig73, sig4, sig6, sig7, sig8]
def bank94 : List Sig := [sig12, sig74, sig2, sig4, sig6, sig7, sig8]
def bank95 : List Sig := [sig14, sig1, sig68, sig4, sig6, sig7, sig8]
def bank96 : List Sig := [sig14, sig69, sig2, sig4, sig6, sig7, sig8]
def bank97 : List Sig := [sig75, sig1, sig2, sig4, sig6, sig7, sig8]
def bank98 : List Sig := [sig13, sig14, sig1, sig2, sig3, sig6, sig7, sig8]
def bank99 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig7, sig76]
def bank100 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig52, sig8]
def bank101 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig53, sig8]
def bank102 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig8, sig59]
def bank103 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig8, sig60]
def bank104 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig77, sig7, sig8]
def bank105 : List Sig := [sig13, sig1, sig2, sig3, sig78, sig6, sig7, sig8]
def bank106 : List Sig := [sig13, sig1, sig2, sig3, sig39, sig6, sig7, sig8]
def bank107 : List Sig := [sig13, sig1, sig2, sig3, sig40, sig6, sig7, sig8]
def bank108 : List Sig := [sig13, sig1, sig2, sig79, sig5, sig6, sig7, sig8]
def bank109 : List Sig := [sig13, sig1, sig2, sig30, sig5, sig6, sig7, sig8]
def bank110 : List Sig := [sig13, sig1, sig2, sig31, sig5, sig6, sig7, sig8]
def bank111 : List Sig := [sig13, sig1, sig70, sig3, sig5, sig6, sig7, sig8]
def bank112 : List Sig := [sig13, sig71, sig2, sig3, sig5, sig6, sig7, sig8]
def bank113 : List Sig := [sig1, sig71, sig2, sig3, sig5, sig6, sig7, sig8]
def bank114 : List Sig := [sig1, sig2, sig70, sig3, sig5, sig6, sig7, sig8]
def bank115 : List Sig := [sig1, sig70, sig3, sig5, sig6, sig7, sig8]
def bank116 : List Sig := [sig71, sig2, sig3, sig5, sig6, sig7, sig8]
def bank117 : List Sig := [sig13, sig14, sig1, sig2, sig3, sig8, sig60]
def bank118 : List Sig := [sig13, sig1, sig73, sig3, sig6, sig7, sig8]
def bank119 : List Sig := [sig13, sig74, sig2, sig3, sig6, sig7, sig8]
def bank120 : List Sig := [sig14, sig1, sig70, sig3, sig6, sig7, sig8]
def bank121 : List Sig := [sig14, sig71, sig2, sig3, sig6, sig7, sig8]
def bank122 : List Sig := [sig80, sig1, sig2, sig3, sig6, sig7, sig8]
def bank123 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig6, sig7, sig81]
def bank124 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig6, sig82, sig8]
def bank125 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig47, sig7, sig8]
def bank126 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig48, sig7, sig8]
def bank127 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig7, sig8, sig58]
def bank128 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig7, sig8, sig60]
def bank129 : List Sig := [sig14, sig1, sig2, sig3, sig83, sig6, sig7, sig8]
def bank130 : List Sig := [sig14, sig1, sig2, sig3, sig34, sig6, sig7, sig8]
def bank131 : List Sig := [sig14, sig1, sig2, sig3, sig35, sig6, sig7, sig8]
def bank132 : List Sig := [sig14, sig1, sig2, sig84, sig4, sig6, sig7, sig8]
def bank133 : List Sig := [sig14, sig1, sig2, sig30, sig4, sig6, sig7, sig8]
def bank134 : List Sig := [sig14, sig1, sig2, sig31, sig4, sig6, sig7, sig8]
def bank135 : List Sig := [sig14, sig1, sig73, sig3, sig4, sig6, sig7, sig8]
def bank136 : List Sig := [sig14, sig74, sig2, sig3, sig4, sig6, sig7, sig8]
def bank137 : List Sig := [sig1, sig74, sig2, sig3, sig4, sig6, sig7, sig8]
def bank138 : List Sig := [sig1, sig2, sig73, sig3, sig4, sig6, sig7, sig8]
def bank139 : List Sig := [sig1, sig73, sig3, sig4, sig6, sig7, sig8]
def bank140 : List Sig := [sig74, sig2, sig3, sig4, sig6, sig7, sig8]
def bank141 : List Sig := [sig1, sig2, sig85, sig4, sig5, sig6, sig7, sig8]
def bank142 : List Sig := [sig1, sig2, sig3, sig4, sig86, sig6, sig7, sig8]
def bank143 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig44, sig7, sig58]
def bank144 : List Sig := [sig1, sig2, sig87, sig4, sig5, sig6, sig7, sig8]
def bank145 : List Sig := [sig1, sig2, sig3, sig88, sig5, sig6, sig7, sig8]
def bank146 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig49, sig59]
def bank147 : List Sig := [sig1, sig2, sig3, sig89, sig5, sig6, sig7, sig8]
def bank148 : List Sig := [sig1, sig2, sig3, sig4, sig90, sig6, sig7, sig8]
def bank149 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig43, sig8, sig60]
def bank150 : List Sig := [sig1, sig2, sig3, sig91, sig4, sig5, sig6, sig7, sig8]
def bank151 : List Sig := [sig1, sig2, sig3, sig4, sig92, sig5, sig6, sig7, sig8]
def bank152 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig93, sig6, sig7, sig8]
def bank153 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig94, sig7, sig8]
def bank154 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig95, sig8]
def bank155 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig96]
def bank156 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig97]
def bank157 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig98]
def bank158 : List Sig := [sig12, sig1, sig2, sig91, sig4, sig5, sig6, sig7, sig8]
def bank159 : List Sig := [sig13, sig1, sig2, sig3, sig91, sig5, sig6, sig7, sig8]
def bank160 : List Sig := [sig14, sig1, sig2, sig3, sig91, sig4, sig6, sig7, sig8]
def bank161 : List Sig := [sig99, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank162 : List Sig := [sig1, sig100, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank163 : List Sig := [sig1, sig2, sig101, sig3, sig4, sig5, sig6, sig7, sig8]
def bank164 : List Sig := [sig1, sig2, sig102, sig3, sig4, sig5, sig6, sig7, sig8]
def bank165 : List Sig := [sig1, sig2, sig103, sig3, sig4, sig5, sig6, sig7, sig8]
def bank166 : List Sig := [sig1, sig2, sig104, sig3, sig4, sig5, sig6, sig7, sig8]
def bank167 : List Sig := [sig1, sig2, sig105, sig3, sig4, sig5, sig6, sig7, sig8]
def bank168 : List Sig := [sig1, sig2, sig3, sig91, sig4, sig39, sig6, sig7, sig8]
def bank169 : List Sig := [sig1, sig2, sig3, sig91, sig4, sig40, sig6, sig7, sig8]
def bank170 : List Sig := [sig1, sig2, sig3, sig91, sig34, sig5, sig6, sig7, sig8]
def bank171 : List Sig := [sig1, sig2, sig3, sig91, sig35, sig5, sig6, sig7, sig8]
def bank172 : List Sig := [sig1, sig2, sig3, sig106, sig4, sig5, sig6, sig7, sig8]
def bank173 : List Sig := [sig1, sig2, sig3, sig107, sig4, sig5, sig6, sig7, sig8]
def bank174 : List Sig := [sig1, sig2, sig3, sig108, sig4, sig5, sig6, sig7, sig8]
def bank175 : List Sig := [sig1, sig2, sig3, sig4, sig109, sig5, sig6, sig7, sig8]
def bank176 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig110, sig6, sig7, sig8]
def bank177 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig111, sig7, sig8]
def bank178 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig112, sig8]
def bank179 : List Sig := [sig1, sig2, sig30, sig91, sig4, sig5, sig6, sig7, sig8]
def bank180 : List Sig := [sig1, sig2, sig31, sig91, sig4, sig5, sig6, sig7, sig8]
def bank181 : List Sig := [sig1, sig2, sig91, sig107, sig4, sig5, sig6, sig7, sig8]
def bank182 : List Sig := [sig1, sig2, sig107, sig4, sig5, sig6, sig7, sig8]
def bank183 : List Sig := [sig12, sig1, sig2, sig4, sig92, sig5, sig6, sig7, sig8]
def bank184 : List Sig := [sig13, sig1, sig2, sig3, sig92, sig5, sig6, sig7, sig8]
def bank185 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig92, sig6, sig7, sig8]
def bank186 : List Sig := [sig113, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank187 : List Sig := [sig1, sig114, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank188 : List Sig := [sig1, sig2, sig115, sig3, sig4, sig5, sig6, sig7, sig8]
def bank189 : List Sig := [sig1, sig2, sig116, sig3, sig4, sig5, sig6, sig7, sig8]
def bank190 : List Sig := [sig1, sig2, sig3, sig117, sig4, sig5, sig6, sig7, sig8]
def bank191 : List Sig := [sig1, sig2, sig3, sig118, sig4, sig5, sig6, sig7, sig8]
def bank192 : List Sig := [sig1, sig2, sig3, sig119, sig4, sig5, sig6, sig7, sig8]
def bank193 : List Sig := [sig1, sig2, sig3, sig4, sig92, sig39, sig6, sig7, sig8]
def bank194 : List Sig := [sig1, sig2, sig3, sig4, sig92, sig40, sig6, sig7, sig8]
def bank195 : List Sig := [sig1, sig2, sig3, sig4, sig120, sig5, sig6, sig7, sig8]
def bank196 : List Sig := [sig1, sig2, sig3, sig4, sig121, sig5, sig6, sig7, sig8]
def bank197 : List Sig := [sig1, sig2, sig3, sig4, sig122, sig5, sig6, sig7, sig8]
def bank198 : List Sig := [sig1, sig2, sig3, sig4, sig123, sig5, sig6, sig7, sig8]
def bank199 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig124, sig6, sig7, sig8]
def bank200 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig125, sig7, sig8]
def bank201 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig126]
def bank202 : List Sig := [sig1, sig2, sig3, sig34, sig92, sig5, sig6, sig7, sig8]
def bank203 : List Sig := [sig1, sig2, sig3, sig35, sig92, sig5, sig6, sig7, sig8]
def bank204 : List Sig := [sig1, sig2, sig3, sig92, sig121, sig5, sig6, sig7, sig8]
def bank205 : List Sig := [sig1, sig2, sig3, sig121, sig5, sig6, sig7, sig8]
def bank206 : List Sig := [sig1, sig2, sig30, sig4, sig92, sig5, sig6, sig7, sig8]
def bank207 : List Sig := [sig1, sig2, sig31, sig4, sig92, sig5, sig6, sig7, sig8]
def bank208 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig93, sig6, sig7, sig8]
def bank209 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig93, sig6, sig7, sig8]
def bank210 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig93, sig6, sig7, sig8]
def bank211 : List Sig := [sig127, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank212 : List Sig := [sig1, sig128, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank213 : List Sig := [sig1, sig2, sig129, sig3, sig4, sig5, sig6, sig7, sig8]
def bank214 : List Sig := [sig1, sig2, sig130, sig3, sig4, sig5, sig6, sig7, sig8]
def bank215 : List Sig := [sig1, sig2, sig3, sig4, sig131, sig5, sig6, sig7, sig8]
def bank216 : List Sig := [sig1, sig2, sig3, sig4, sig132, sig5, sig6, sig7, sig8]
def bank217 : List Sig := [sig1, sig2, sig3, sig4, sig133, sig5, sig6, sig7, sig8]
def bank218 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig134, sig6, sig7, sig8]
def bank219 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig135, sig6, sig7, sig8]
def bank220 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig136, sig6, sig7, sig8]
def bank221 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig137, sig6, sig7, sig8]
def bank222 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig138, sig6, sig7, sig8]
def bank223 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig139, sig8]
def bank224 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig140]
def bank225 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig93, sig6, sig7, sig8]
def bank226 : List Sig := [sig1, sig2, sig3, sig4, sig40, sig93, sig6, sig7, sig8]
def bank227 : List Sig := [sig1, sig2, sig3, sig4, sig93, sig135, sig6, sig7, sig8]
def bank228 : List Sig := [sig1, sig2, sig3, sig4, sig135, sig6, sig7, sig8]
def bank229 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig93, sig6, sig7, sig8]
def bank230 : List Sig := [sig1, sig2, sig3, sig35, sig5, sig93, sig6, sig7, sig8]
def bank231 : List Sig := [sig1, sig2, sig30, sig4, sig5, sig93, sig6, sig7, sig8]
def bank232 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig93, sig6, sig7, sig8]
def bank233 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig94, sig7, sig8]
def bank234 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig94, sig7, sig8]
def bank235 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig6, sig94, sig7, sig8]
def bank236 : List Sig := [sig141, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank237 : List Sig := [sig1, sig142, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank238 : List Sig := [sig1, sig2, sig143, sig3, sig4, sig5, sig6, sig7, sig8]
def bank239 : List Sig := [sig1, sig2, sig3, sig144, sig4, sig5, sig6, sig7, sig8]
def bank240 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig145, sig6, sig7, sig8]
def bank241 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig146, sig6, sig7, sig8]
def bank242 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig147, sig6, sig7, sig8]
def bank243 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig148, sig7, sig8]
def bank244 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig149, sig7, sig8]
def bank245 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig150, sig7, sig8]
def bank246 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig151, sig7, sig8]
def bank247 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig152, sig7, sig8]
def bank248 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig153]
def bank249 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig154]
def bank250 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig94, sig7, sig8]
def bank251 : List Sig := [sig1, sig2, sig3, sig4, sig40, sig6, sig94, sig7, sig8]
def bank252 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig94, sig7, sig8]
def bank253 : List Sig := [sig1, sig2, sig3, sig35, sig5, sig6, sig94, sig7, sig8]
def bank254 : List Sig := [sig1, sig2, sig30, sig4, sig5, sig6, sig94, sig7, sig8]
def bank255 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig94, sig7, sig8]
def bank256 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig95, sig8]
def bank257 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig7, sig95, sig8]
def bank258 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig6, sig7, sig95, sig8]
def bank259 : List Sig := [sig155, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank260 : List Sig := [sig1, sig156, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank261 : List Sig := [sig1, sig2, sig157, sig3, sig4, sig5, sig6, sig7, sig8]
def bank262 : List Sig := [sig1, sig2, sig3, sig4, sig158, sig5, sig6, sig7, sig8]
def bank263 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig159, sig6, sig7, sig8]
def bank264 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig160, sig7, sig8]
def bank265 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig161, sig7, sig8]
def bank266 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig162, sig8]
def bank267 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig163, sig8]
def bank268 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig164, sig8]
def bank269 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig165, sig8]
def bank270 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig166, sig8]
def bank271 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig167]
def bank272 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig168]
def bank273 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig95, sig8]
def bank274 : List Sig := [sig1, sig2, sig3, sig4, sig40, sig6, sig7, sig95, sig8]
def bank275 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig95, sig8]
def bank276 : List Sig := [sig1, sig2, sig3, sig35, sig5, sig6, sig7, sig95, sig8]
def bank277 : List Sig := [sig1, sig2, sig30, sig4, sig5, sig6, sig7, sig95, sig8]
def bank278 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig95, sig8]
def bank279 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig8, sig96]
def bank280 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig7, sig8, sig96]
def bank281 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig6, sig7, sig8, sig96]
def bank282 : List Sig := [sig169, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank283 : List Sig := [sig1, sig170, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank284 : List Sig := [sig1, sig2, sig3, sig171, sig4, sig5, sig6, sig7, sig8]
def bank285 : List Sig := [sig1, sig2, sig3, sig4, sig172, sig5, sig6, sig7, sig8]
def bank286 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig173, sig6, sig7, sig8]
def bank287 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig174, sig7, sig8]
def bank288 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig175, sig8]
def bank289 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig176]
def bank290 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig177]
def bank291 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig178]
def bank292 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig179]
def bank293 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig180]
def bank294 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig181]
def bank295 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig182]
def bank296 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig8, sig96]
def bank297 : List Sig := [sig1, sig2, sig3, sig4, sig40, sig6, sig7, sig8, sig96]
def bank298 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8, sig96]
def bank299 : List Sig := [sig1, sig2, sig3, sig35, sig5, sig6, sig7, sig8, sig96]
def bank300 : List Sig := [sig1, sig2, sig30, sig4, sig5, sig6, sig7, sig8, sig96]
def bank301 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8, sig96]
def bank302 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig8, sig97]
def bank303 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig7, sig8, sig97]
def bank304 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig6, sig7, sig8, sig97]
def bank305 : List Sig := [sig183, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank306 : List Sig := [sig1, sig2, sig184, sig3, sig4, sig5, sig6, sig7, sig8]
def bank307 : List Sig := [sig1, sig2, sig184, sig4, sig5, sig6, sig7, sig8]
def bank308 : List Sig := [sig1, sig2, sig184, sig4, sig5, sig6, sig7, sig8, sig97]
def bank309 : List Sig := [sig1, sig2, sig3, sig185, sig4, sig5, sig6, sig7, sig8]
def bank310 : List Sig := [sig1, sig2, sig3, sig185, sig5, sig6, sig7, sig8]
def bank311 : List Sig := [sig1, sig2, sig3, sig185, sig5, sig6, sig7, sig8, sig97]
def bank312 : List Sig := [sig1, sig2, sig3, sig4, sig186, sig5, sig6, sig7, sig8]
def bank313 : List Sig := [sig1, sig2, sig3, sig4, sig186, sig6, sig7, sig8]
def bank314 : List Sig := [sig1, sig2, sig3, sig4, sig186, sig6, sig7, sig8, sig97]
def bank315 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig187, sig6, sig7, sig8]
def bank316 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig7, sig8]
def bank317 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig189, sig8]
def bank318 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig190]
def bank319 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig191]
def bank320 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig192]
def bank321 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig193]
def bank322 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig194]
def bank323 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig195]
def bank324 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig196]
def bank325 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig8, sig97]
def bank326 : List Sig := [sig1, sig2, sig3, sig4, sig40, sig6, sig7, sig8, sig97]
def bank327 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8, sig97]
def bank328 : List Sig := [sig1, sig2, sig3, sig35, sig5, sig6, sig7, sig8, sig97]
def bank329 : List Sig := [sig1, sig2, sig30, sig4, sig5, sig6, sig7, sig8, sig97]
def bank330 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8, sig97]
def bank331 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig8, sig98]
def bank332 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig7, sig8, sig98]
def bank333 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig6, sig7, sig8, sig98]
def bank334 : List Sig := [sig1, sig197, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank335 : List Sig := [sig1, sig2, sig198, sig3, sig4, sig5, sig6, sig7, sig8]
def bank336 : List Sig := [sig1, sig2, sig198, sig4, sig5, sig6, sig7, sig8]
def bank337 : List Sig := [sig1, sig2, sig198, sig4, sig5, sig6, sig7, sig8, sig98]
def bank338 : List Sig := [sig1, sig2, sig3, sig199, sig4, sig5, sig6, sig7, sig8]
def bank339 : List Sig := [sig1, sig2, sig3, sig199, sig5, sig6, sig7, sig8]
def bank340 : List Sig := [sig1, sig2, sig3, sig199, sig5, sig6, sig7, sig8, sig98]
def bank341 : List Sig := [sig1, sig2, sig3, sig4, sig200, sig5, sig6, sig7, sig8]
def bank342 : List Sig := [sig1, sig2, sig3, sig4, sig200, sig6, sig7, sig8]
def bank343 : List Sig := [sig1, sig2, sig3, sig4, sig200, sig6, sig7, sig8, sig98]
def bank344 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig201, sig6, sig7, sig8]
def bank345 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig202, sig7, sig8]
def bank346 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig203, sig8]
def bank347 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig204]
def bank348 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig205]
def bank349 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig206]
def bank350 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig207]
def bank351 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig208]
def bank352 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig209]
def bank353 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8, sig210]
def bank354 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig7, sig8, sig98]
def bank355 : List Sig := [sig1, sig2, sig3, sig4, sig40, sig6, sig7, sig8, sig98]
def bank356 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig8, sig98]
def bank357 : List Sig := [sig1, sig2, sig3, sig35, sig5, sig6, sig7, sig8, sig98]
def bank358 : List Sig := [sig1, sig2, sig30, sig4, sig5, sig6, sig7, sig8, sig98]
def bank359 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8, sig98]
def bank360 : List Sig := [sig12, sig1, sig2, sig4, sig5, sig6, sig7, sig8, sig211]
def bank361 : List Sig := [sig1, sig68, sig91, sig4, sig5, sig6, sig7, sig8]
def bank362 : List Sig := [sig1, sig68, sig4, sig92, sig5, sig6, sig7, sig8]
def bank363 : List Sig := [sig1, sig68, sig4, sig5, sig93, sig6, sig7, sig8]
def bank364 : List Sig := [sig1, sig68, sig4, sig5, sig6, sig94, sig7, sig8]
def bank365 : List Sig := [sig1, sig68, sig4, sig5, sig6, sig7, sig95, sig8]
def bank366 : List Sig := [sig1, sig68, sig4, sig5, sig6, sig7, sig8, sig212]
def bank367 : List Sig := [sig1, sig68, sig4, sig5, sig6, sig7, sig8, sig98]
def bank368 : List Sig := [sig1, sig68, sig4, sig5, sig6, sig7, sig58]
def bank369 : List Sig := [sig1, sig68, sig4, sig5, sig6, sig7, sig59]
def bank370 : List Sig := [sig1, sig68, sig4, sig39, sig6, sig7, sig8]
def bank371 : List Sig := [sig1, sig68, sig4, sig213, sig6, sig7, sig8]
def bank372 : List Sig := [sig1, sig68, sig34, sig5, sig6, sig7, sig8]
def bank373 : List Sig := [sig1, sig68, sig214, sig5, sig6, sig7, sig8]
def bank374 : List Sig := [sig69, sig2, sig91, sig4, sig5, sig6, sig7, sig8]
def bank375 : List Sig := [sig69, sig2, sig4, sig92, sig5, sig6, sig7, sig8]
def bank376 : List Sig := [sig69, sig2, sig4, sig5, sig93, sig6, sig7, sig8]
def bank377 : List Sig := [sig69, sig2, sig4, sig5, sig6, sig94, sig7, sig8]
def bank378 : List Sig := [sig69, sig2, sig4, sig5, sig6, sig7, sig95, sig8]
def bank379 : List Sig := [sig69, sig2, sig4, sig5, sig6, sig7, sig8, sig97]
def bank380 : List Sig := [sig69, sig2, sig4, sig5, sig6, sig7, sig8, sig215]
def bank381 : List Sig := [sig69, sig2, sig4, sig5, sig6, sig7, sig58]
def bank382 : List Sig := [sig69, sig2, sig4, sig5, sig6, sig7, sig59]
def bank383 : List Sig := [sig69, sig2, sig4, sig216, sig6, sig7, sig8]
def bank384 : List Sig := [sig69, sig2, sig4, sig40, sig6, sig7, sig8]
def bank385 : List Sig := [sig69, sig2, sig217, sig5, sig6, sig7, sig8]
def bank386 : List Sig := [sig69, sig2, sig35, sig5, sig6, sig7, sig8]
def bank387 : List Sig := [sig13, sig1, sig2, sig3, sig5, sig6, sig7, sig8, sig218]
def bank388 : List Sig := [sig1, sig70, sig3, sig91, sig5, sig6, sig7, sig8]
def bank389 : List Sig := [sig1, sig70, sig3, sig92, sig5, sig6, sig7, sig8]
def bank390 : List Sig := [sig1, sig70, sig3, sig5, sig93, sig6, sig7, sig8]
def bank391 : List Sig := [sig1, sig70, sig3, sig5, sig6, sig94, sig7, sig8]
def bank392 : List Sig := [sig1, sig70, sig3, sig5, sig6, sig7, sig8, sig96]
def bank393 : List Sig := [sig1, sig70, sig3, sig5, sig6, sig7, sig8, sig219]
def bank394 : List Sig := [sig1, sig70, sig3, sig5, sig6, sig7, sig8, sig98]
def bank395 : List Sig := [sig1, sig70, sig3, sig5, sig6, sig8, sig59]
def bank396 : List Sig := [sig1, sig70, sig3, sig5, sig6, sig8, sig60]
def bank397 : List Sig := [sig1, sig70, sig3, sig39, sig6, sig7, sig8]
def bank398 : List Sig := [sig1, sig70, sig3, sig220, sig6, sig7, sig8]
def bank399 : List Sig := [sig1, sig70, sig30, sig5, sig6, sig7, sig8]
def bank400 : List Sig := [sig1, sig70, sig221, sig5, sig6, sig7, sig8]
def bank401 : List Sig := [sig71, sig2, sig3, sig91, sig5, sig6, sig7, sig8]
def bank402 : List Sig := [sig71, sig2, sig3, sig92, sig5, sig6, sig7, sig8]
def bank403 : List Sig := [sig71, sig2, sig3, sig5, sig93, sig6, sig7, sig8]
def bank404 : List Sig := [sig71, sig2, sig3, sig5, sig6, sig94, sig7, sig8]
def bank405 : List Sig := [sig71, sig2, sig3, sig5, sig6, sig7, sig8, sig96]
def bank406 : List Sig := [sig71, sig2, sig3, sig5, sig6, sig7, sig8, sig97]
def bank407 : List Sig := [sig71, sig2, sig3, sig5, sig6, sig7, sig8, sig222]
def bank408 : List Sig := [sig71, sig2, sig3, sig5, sig6, sig8, sig59]
def bank409 : List Sig := [sig71, sig2, sig3, sig5, sig6, sig8, sig60]
def bank410 : List Sig := [sig71, sig2, sig3, sig223, sig6, sig7, sig8]
def bank411 : List Sig := [sig71, sig2, sig3, sig40, sig6, sig7, sig8]
def bank412 : List Sig := [sig71, sig2, sig224, sig5, sig6, sig7, sig8]
def bank413 : List Sig := [sig71, sig2, sig31, sig5, sig6, sig7, sig8]
def bank414 : List Sig := [sig14, sig1, sig2, sig3, sig4, sig6, sig7, sig8, sig225]
def bank415 : List Sig := [sig1, sig73, sig3, sig91, sig4, sig6, sig7, sig8]
def bank416 : List Sig := [sig1, sig73, sig3, sig4, sig92, sig6, sig7, sig8]
def bank417 : List Sig := [sig1, sig73, sig3, sig4, sig93, sig6, sig7, sig8]
def bank418 : List Sig := [sig1, sig73, sig3, sig4, sig6, sig7, sig95, sig8]
def bank419 : List Sig := [sig1, sig73, sig3, sig4, sig6, sig7, sig8, sig96]
def bank420 : List Sig := [sig1, sig73, sig3, sig4, sig6, sig7, sig8, sig226]
def bank421 : List Sig := [sig1, sig73, sig3, sig4, sig6, sig7, sig8, sig98]
def bank422 : List Sig := [sig1, sig73, sig3, sig4, sig7, sig8, sig58]
def bank423 : List Sig := [sig1, sig73, sig3, sig4, sig7, sig8, sig60]
def bank424 : List Sig := [sig1, sig73, sig3, sig34, sig6, sig7, sig8]
def bank425 : List Sig := [sig1, sig73, sig3, sig227, sig6, sig7, sig8]
def bank426 : List Sig := [sig1, sig73, sig30, sig4, sig6, sig7, sig8]
def bank427 : List Sig := [sig1, sig73, sig228, sig4, sig6, sig7, sig8]
def bank428 : List Sig := [sig74, sig2, sig3, sig91, sig4, sig6, sig7, sig8]
def bank429 : List Sig := [sig74, sig2, sig3, sig4, sig92, sig6, sig7, sig8]
def bank430 : List Sig := [sig74, sig2, sig3, sig4, sig93, sig6, sig7, sig8]
def bank431 : List Sig := [sig74, sig2, sig3, sig4, sig6, sig7, sig95, sig8]
def bank432 : List Sig := [sig74, sig2, sig3, sig4, sig6, sig7, sig8, sig96]
def bank433 : List Sig := [sig74, sig2, sig3, sig4, sig6, sig7, sig8, sig97]
def bank434 : List Sig := [sig74, sig2, sig3, sig4, sig6, sig7, sig8, sig229]
def bank435 : List Sig := [sig74, sig2, sig3, sig4, sig7, sig8, sig58]
def bank436 : List Sig := [sig74, sig2, sig3, sig4, sig7, sig8, sig60]
def bank437 : List Sig := [sig74, sig2, sig3, sig230, sig6, sig7, sig8]
def bank438 : List Sig := [sig74, sig2, sig3, sig35, sig6, sig7, sig8]
def bank439 : List Sig := [sig74, sig2, sig231, sig4, sig6, sig7, sig8]
def bank440 : List Sig := [sig74, sig2, sig31, sig4, sig6, sig7, sig8]
def bank441 : List Sig := [sig1, sig2, sig232, sig3, sig4, sig5, sig6, sig7, sig8]
def bank442 : List Sig := [sig1, sig2, sig233, sig3, sig4, sig5, sig6, sig7, sig8]
def bank443 : List Sig := [sig1, sig2, sig234, sig3, sig4, sig5, sig6, sig7, sig8]
def bank444 : List Sig := [sig1, sig2, sig3, sig4, sig39, sig6, sig235, sig7, sig8]
def bank445 : List Sig := [sig236, sig1, sig2, sig3, sig4, sig6, sig7, sig8]
def bank446 : List Sig := [sig1, sig2, sig3, sig4, sig237, sig6, sig7, sig8]
def bank447 : List Sig := [sig1, sig2, sig3, sig34, sig39, sig6, sig7, sig8]
def bank448 : List Sig := [sig1, sig2, sig3, sig35, sig39, sig6, sig7, sig8]
def bank449 : List Sig := [sig1, sig2, sig30, sig4, sig39, sig6, sig7, sig8]
def bank450 : List Sig := [sig1, sig2, sig31, sig4, sig39, sig6, sig7, sig8]
def bank451 : List Sig := [sig2, sig3, sig4, sig39, sig6, sig45, sig7, sig8]
def bank452 : List Sig := [sig1, sig2, sig3, sig4, sig40, sig6, sig238, sig7, sig8]
def bank453 : List Sig := [sig239, sig1, sig2, sig3, sig4, sig6, sig7, sig8]
def bank454 : List Sig := [sig1, sig2, sig3, sig34, sig40, sig6, sig7, sig8]
def bank455 : List Sig := [sig1, sig2, sig3, sig35, sig40, sig6, sig7, sig8]
def bank456 : List Sig := [sig1, sig2, sig30, sig4, sig40, sig6, sig7, sig8]
def bank457 : List Sig := [sig1, sig2, sig31, sig4, sig40, sig6, sig7, sig8]
def bank458 : List Sig := [sig1, sig3, sig4, sig40, sig6, sig46, sig7, sig8]
def bank459 : List Sig := [sig1, sig2, sig3, sig34, sig5, sig6, sig7, sig240, sig8]
def bank460 : List Sig := [sig241, sig1, sig2, sig3, sig5, sig6, sig7, sig8]
def bank461 : List Sig := [sig1, sig2, sig3, sig242, sig5, sig6, sig7, sig8]
def bank462 : List Sig := [sig1, sig2, sig30, sig34, sig5, sig6, sig7, sig8]
def bank463 : List Sig := [sig1, sig2, sig31, sig34, sig5, sig6, sig7, sig8]
def bank464 : List Sig := [sig2, sig3, sig34, sig5, sig6, sig7, sig50, sig8]
def bank465 : List Sig := [sig1, sig2, sig3, sig35, sig5, sig6, sig7, sig243, sig8]
def bank466 : List Sig := [sig244, sig1, sig2, sig3, sig5, sig6, sig7, sig8]
def bank467 : List Sig := [sig1, sig2, sig30, sig35, sig5, sig6, sig7, sig8]
def bank468 : List Sig := [sig1, sig2, sig31, sig35, sig5, sig6, sig7, sig8]
def bank469 : List Sig := [sig1, sig3, sig35, sig5, sig6, sig7, sig51, sig8]
def bank470 : List Sig := [sig1, sig2, sig30, sig4, sig5, sig6, sig7, sig8, sig245]
def bank471 : List Sig := [sig246, sig1, sig2, sig4, sig5, sig6, sig7, sig8]
def bank472 : List Sig := [sig1, sig2, sig247, sig4, sig5, sig6, sig7, sig8]
def bank473 : List Sig := [sig2, sig30, sig4, sig5, sig6, sig7, sig8, sig54]
def bank474 : List Sig := [sig1, sig2, sig31, sig4, sig5, sig6, sig7, sig8, sig248]
def bank475 : List Sig := [sig249, sig1, sig2, sig4, sig5, sig6, sig7, sig8]
def bank476 : List Sig := [sig1, sig31, sig4, sig5, sig6, sig7, sig8, sig55]

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
theorem excl5 : Blocked 6 0 bank86 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl6 : Blocked 6 0 bank87 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl7 : Blocked 6 0 bank88 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl8 : Blocked 6 0 bank89 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl9 : Blocked 6 0 bank90 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl10 : Blocked 6 0 bank91 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl11 : Blocked 7 0 bank66 :=
  block_step [] [bank86, bank87, bank88, bank89, bank90, bank91] (True.intro) (⟨excl5, excl6, excl7, excl8, excl9, excl10, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl12 : Blocked 6 0 bank92 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl13 : Blocked 6 0 bank93 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl14 : Blocked 6 0 bank94 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl15 : Blocked 6 0 bank95 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl16 : Blocked 6 0 bank96 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl17 : Blocked 6 0 bank97 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl18 : Blocked 7 0 bank67 :=
  block_step [] [bank92, bank93, bank94, bank95, bank96, bank97] (True.intro) (⟨excl12, excl13, excl14, excl15, excl16, excl17, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl19 : Blocked 7 0 bank68 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl20 : Blocked 7 0 bank69 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl21 : Blocked 7 0 bank70 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl22 : Blocked 7 0 bank71 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl23 : Blocked 7 0 bank72 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl24 : Blocked 7 0 bank73 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl25 : Blocked 7 0 bank74 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl26 : Blocked 7 0 bank75 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl27 : Blocked 7 0 bank76 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl28 : Blocked 7 0 bank77 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl29 : Blocked 7 0 bank78 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl30 : Blocked 7 0 bank79 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl31 : Blocked 7 0 bank80 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl32 : Blocked 7 0 bank81 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl33 : Blocked 7 0 bank82 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl34 : Blocked 7 0 bank83 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl35 : Blocked 7 0 bank84 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl36 : Blocked 7 0 bank85 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl37 : Blocked 8 0 bank6 :=
  block_step [] [bank66, bank67, bank68, bank69, bank70, bank71, bank72, bank73, bank74, bank75, bank76, bank77, bank78, bank79, bank80, bank81, bank82, bank83, bank84, bank85] (True.intro) (⟨excl11, excl18, excl19, excl20, excl21, excl22, excl23, excl24, excl25, excl26, excl27, excl28, excl29, excl30, excl31, excl32, excl33, excl34, excl35, excl36, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl38 : Blocked 8 0 bank7 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl39 : Blocked 6 0 bank117 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl40 : Blocked 6 0 bank118 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl41 : Blocked 6 0 bank119 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl42 : Blocked 6 0 bank120 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl43 : Blocked 6 0 bank121 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl44 : Blocked 6 0 bank122 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl45 : Blocked 7 0 bank98 :=
  block_step [] [bank117, bank118, bank119, bank120, bank121, bank122] (True.intro) (⟨excl39, excl40, excl41, excl42, excl43, excl44, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl46 : Blocked 7 0 bank99 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl47 : Blocked 7 0 bank100 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl48 : Blocked 7 0 bank101 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl49 : Blocked 7 0 bank102 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl50 : Blocked 7 0 bank103 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl51 : Blocked 7 0 bank104 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl52 : Blocked 7 0 bank105 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl53 : Blocked 7 0 bank106 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl54 : Blocked 7 0 bank107 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl55 : Blocked 7 0 bank108 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl56 : Blocked 7 0 bank109 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl57 : Blocked 7 0 bank110 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl58 : Blocked 7 0 bank111 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl59 : Blocked 7 0 bank112 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl60 : Blocked 7 0 bank113 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl61 : Blocked 7 0 bank114 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl62 : Blocked 7 0 bank115 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl63 : Blocked 7 0 bank116 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl64 : Blocked 8 0 bank8 :=
  block_step [] [bank66, bank98, bank99, bank100, bank101, bank102, bank103, bank104, bank105, bank106, bank107, bank108, bank109, bank110, bank111, bank112, bank113, bank114, bank115, bank116] (True.intro) (⟨excl11, excl45, excl46, excl47, excl48, excl49, excl50, excl51, excl52, excl53, excl54, excl55, excl56, excl57, excl58, excl59, excl60, excl61, excl62, excl63, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl65 : Blocked 8 0 bank9 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl66 : Blocked 7 0 bank123 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl67 : Blocked 7 0 bank124 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl68 : Blocked 7 0 bank125 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl69 : Blocked 7 0 bank126 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl70 : Blocked 7 0 bank127 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl71 : Blocked 7 0 bank128 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl72 : Blocked 7 0 bank129 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl73 : Blocked 7 0 bank130 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl74 : Blocked 7 0 bank131 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl75 : Blocked 7 0 bank132 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl76 : Blocked 7 0 bank133 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl77 : Blocked 7 0 bank134 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl78 : Blocked 7 0 bank135 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl79 : Blocked 7 0 bank136 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl80 : Blocked 7 0 bank137 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl81 : Blocked 7 0 bank138 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl82 : Blocked 7 0 bank139 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl83 : Blocked 7 0 bank140 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl84 : Blocked 8 0 bank10 :=
  block_step [] [bank67, bank98, bank123, bank124, bank125, bank126, bank127, bank128, bank129, bank130, bank131, bank132, bank133, bank134, bank135, bank136, bank137, bank138, bank139, bank140] (True.intro) (⟨excl18, excl45, excl66, excl67, excl68, excl69, excl70, excl71, excl72, excl73, excl74, excl75, excl76, excl77, excl78, excl79, excl80, excl81, excl82, excl83, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl85 : Blocked 8 0 bank11 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl86 : Blocked 8 0 bank12 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl87 : Blocked 8 0 bank13 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl88 : Blocked 8 0 bank14 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl89 : Blocked 8 0 bank15 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl90 : Blocked 8 0 bank16 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl91 : Blocked 8 0 bank17 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl92 : Blocked 8 0 bank18 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl93 : Blocked 8 0 bank19 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl94 : Blocked 8 0 bank20 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl95 : Blocked 8 0 bank21 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl96 : Blocked 8 0 bank22 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl97 : Blocked 8 0 bank23 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl98 : Blocked 8 0 bank24 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl99 : Blocked 8 0 bank25 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl100 : Blocked 8 0 bank26 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl101 : Blocked 8 0 bank27 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl102 : Blocked 8 0 bank28 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl103 : Blocked 8 0 bank29 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl104 : Blocked 8 0 bank30 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl105 : Blocked 8 0 bank31 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl106 : Blocked 8 0 bank32 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl107 : Blocked 8 0 bank33 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl108 : Blocked 8 0 bank34 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl109 : Blocked 8 0 bank35 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl110 : Blocked 8 0 bank36 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl111 : Blocked 8 0 bank37 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl112 : Blocked 8 0 bank38 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl113 : Blocked 8 0 bank39 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl114 : Blocked 8 0 bank40 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl115 : Blocked 8 0 bank41 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl116 : Blocked 8 0 bank42 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl117 : Blocked 8 0 bank43 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl118 : Blocked 8 0 bank44 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl119 : Blocked 8 0 bank45 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl120 : Blocked 8 0 bank46 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl121 : Blocked 8 0 bank47 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl122 : Blocked 8 0 bank48 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl123 : Blocked 8 0 bank49 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl124 : Blocked 8 0 bank50 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl125 : Blocked 8 0 bank51 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl126 : Blocked 8 0 bank52 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl127 : Blocked 8 0 bank53 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl128 : Blocked 7 0 bank141 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl129 : Blocked 7 0 bank142 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl130 : Blocked 7 0 bank143 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl131 : Blocked 8 0 bank54 :=
  block_step [] [bank70, bank127, bank141, bank142, bank143] (True.intro) (⟨excl21, excl70, excl128, excl129, excl130, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl132 : Blocked 7 0 bank144 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl133 : Blocked 7 0 bank145 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl134 : Blocked 7 0 bank146 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl135 : Blocked 8 0 bank55 :=
  block_step [] [bank71, bank102, bank144, bank145, bank146] (True.intro) (⟨excl22, excl49, excl132, excl133, excl134, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl136 : Blocked 7 0 bank147 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl137 : Blocked 7 0 bank148 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl138 : Blocked 7 0 bank149 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl139 : Blocked 8 0 bank56 :=
  block_step [] [bank103, bank128, bank147, bank148, bank149] (True.intro) (⟨excl50, excl71, excl136, excl137, excl138, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl140 : Blocked 8 0 bank57 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl141 : Blocked 8 0 bank58 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl142 : Blocked 8 0 bank59 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl143 : Blocked 8 0 bank60 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl144 : Blocked 8 0 bank61 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl145 : Blocked 8 0 bank62 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl146 : Blocked 8 0 bank63 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl147 : Blocked 8 0 bank64 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl148 : Blocked 8 0 bank65 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl149 : Blocked 9 0 root :=
  block_step [] [bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank17, bank18, bank19, bank20, bank21, bank22, bank23, bank24, bank25, bank26, bank27, bank28, bank29, bank30, bank31, bank32, bank33, bank34, bank35, bank36, bank37, bank38, bank39, bank40, bank41, bank42, bank43, bank44, bank45, bank46, bank47, bank48, bank49, bank50, bank51, bank52, bank53, bank54, bank55, bank56, bank57, bank58, bank59, bank60, bank61, bank62, bank63, bank64, bank65] (True.intro) (⟨excl0, excl1, excl2, excl3, excl4, excl37, excl38, excl64, excl65, excl84, excl85, excl86, excl87, excl88, excl89, excl90, excl91, excl92, excl93, excl94, excl95, excl96, excl97, excl98, excl99, excl100, excl101, excl102, excl103, excl104, excl105, excl106, excl107, excl108, excl109, excl110, excl111, excl112, excl113, excl114, excl115, excl116, excl117, excl118, excl119, excl120, excl121, excl122, excl123, excl124, excl125, excl126, excl127, excl131, excl135, excl139, excl140, excl141, excl142, excl143, excl144, excl145, excl146, excl147, excl148, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl150 : Blocked 8 0 bank158 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl151 : Blocked 8 0 bank159 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl152 : Blocked 8 0 bank160 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl153 : Blocked 8 0 bank161 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl154 : Blocked 8 0 bank162 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl155 : Blocked 8 0 bank163 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl156 : Blocked 8 0 bank164 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl157 : Blocked 8 0 bank165 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl158 : Blocked 8 0 bank166 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl159 : Blocked 8 0 bank167 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl160 : Blocked 8 0 bank168 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl161 : Blocked 8 0 bank169 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl162 : Blocked 8 0 bank170 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl163 : Blocked 8 0 bank171 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl164 : Blocked 8 0 bank172 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl165 : Blocked 8 0 bank173 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl166 : Blocked 8 0 bank174 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl167 : Blocked 8 0 bank175 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl168 : Blocked 8 0 bank176 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl169 : Blocked 8 0 bank177 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl170 : Blocked 8 0 bank178 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl171 : Blocked 8 0 bank179 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl172 : Blocked 8 0 bank180 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl173 : Blocked 8 0 bank181 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl174 : Blocked 8 0 bank182 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl175 : Blocked 9 0 bank150 :=
  block_step [] [bank158, bank159, bank160, bank161, bank162, bank163, bank164, bank165, bank166, bank167, bank168, bank169, bank170, bank171, bank172, bank173, bank174, bank175, bank176, bank177, bank178, bank179, bank180, bank181, bank182] (True.intro) (⟨excl150, excl151, excl152, excl153, excl154, excl155, excl156, excl157, excl158, excl159, excl160, excl161, excl162, excl163, excl164, excl165, excl166, excl167, excl168, excl169, excl170, excl171, excl172, excl173, excl174, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl176 : Blocked 8 0 bank183 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl177 : Blocked 8 0 bank184 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl178 : Blocked 8 0 bank185 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl179 : Blocked 8 0 bank186 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl180 : Blocked 8 0 bank187 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl181 : Blocked 8 0 bank188 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl182 : Blocked 8 0 bank189 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl183 : Blocked 8 0 bank190 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl184 : Blocked 8 0 bank191 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl185 : Blocked 8 0 bank192 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl186 : Blocked 8 0 bank193 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl187 : Blocked 8 0 bank194 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl188 : Blocked 8 0 bank195 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl189 : Blocked 8 0 bank196 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl190 : Blocked 8 0 bank197 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl191 : Blocked 8 0 bank198 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl192 : Blocked 8 0 bank199 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl193 : Blocked 8 0 bank200 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl194 : Blocked 8 0 bank201 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl195 : Blocked 8 0 bank202 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl196 : Blocked 8 0 bank203 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl197 : Blocked 8 0 bank204 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl198 : Blocked 8 0 bank205 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl199 : Blocked 8 0 bank206 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl200 : Blocked 8 0 bank207 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl201 : Blocked 9 0 bank151 :=
  block_step [] [bank183, bank184, bank185, bank186, bank187, bank188, bank189, bank190, bank191, bank192, bank193, bank194, bank195, bank196, bank197, bank198, bank199, bank200, bank201, bank202, bank203, bank204, bank205, bank206, bank207] (True.intro) (⟨excl176, excl177, excl178, excl179, excl180, excl181, excl182, excl183, excl184, excl185, excl186, excl187, excl188, excl189, excl190, excl191, excl192, excl193, excl194, excl195, excl196, excl197, excl198, excl199, excl200, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl202 : Blocked 8 0 bank208 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl203 : Blocked 8 0 bank209 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl204 : Blocked 8 0 bank210 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl205 : Blocked 8 0 bank211 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl206 : Blocked 8 0 bank212 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl207 : Blocked 8 0 bank213 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl208 : Blocked 8 0 bank214 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl209 : Blocked 8 0 bank215 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl210 : Blocked 8 0 bank216 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl211 : Blocked 8 0 bank217 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl212 : Blocked 8 0 bank218 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl213 : Blocked 8 0 bank219 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl214 : Blocked 8 0 bank220 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl215 : Blocked 8 0 bank221 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl216 : Blocked 8 0 bank222 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl217 : Blocked 8 0 bank223 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl218 : Blocked 8 0 bank224 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl219 : Blocked 8 0 bank225 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl220 : Blocked 8 0 bank226 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl221 : Blocked 8 0 bank227 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl222 : Blocked 8 0 bank228 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl223 : Blocked 8 0 bank229 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl224 : Blocked 8 0 bank230 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl225 : Blocked 8 0 bank231 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl226 : Blocked 8 0 bank232 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl227 : Blocked 9 0 bank152 :=
  block_step [] [bank208, bank209, bank210, bank211, bank212, bank213, bank214, bank215, bank216, bank217, bank218, bank219, bank220, bank221, bank222, bank223, bank224, bank225, bank226, bank227, bank228, bank229, bank230, bank231, bank232] (True.intro) (⟨excl202, excl203, excl204, excl205, excl206, excl207, excl208, excl209, excl210, excl211, excl212, excl213, excl214, excl215, excl216, excl217, excl218, excl219, excl220, excl221, excl222, excl223, excl224, excl225, excl226, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl228 : Blocked 8 0 bank233 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl229 : Blocked 8 0 bank234 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl230 : Blocked 8 0 bank235 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl231 : Blocked 8 0 bank236 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl232 : Blocked 8 0 bank237 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl233 : Blocked 8 0 bank238 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl234 : Blocked 8 0 bank239 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl235 : Blocked 8 0 bank240 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl236 : Blocked 8 0 bank241 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl237 : Blocked 8 0 bank242 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl238 : Blocked 8 0 bank243 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl239 : Blocked 8 0 bank244 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl240 : Blocked 8 0 bank245 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl241 : Blocked 8 0 bank246 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl242 : Blocked 8 0 bank247 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl243 : Blocked 8 0 bank248 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl244 : Blocked 8 0 bank249 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl245 : Blocked 8 0 bank250 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl246 : Blocked 8 0 bank251 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl247 : Blocked 8 0 bank252 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl248 : Blocked 8 0 bank253 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl249 : Blocked 8 0 bank254 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl250 : Blocked 8 0 bank255 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl251 : Blocked 9 0 bank153 :=
  block_step [] [bank233, bank234, bank235, bank236, bank237, bank238, bank239, bank240, bank241, bank242, bank243, bank244, bank245, bank246, bank247, bank248, bank249, bank250, bank251, bank252, bank253, bank254, bank255] (True.intro) (⟨excl228, excl229, excl230, excl231, excl232, excl233, excl234, excl235, excl236, excl237, excl238, excl239, excl240, excl241, excl242, excl243, excl244, excl245, excl246, excl247, excl248, excl249, excl250, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl252 : Blocked 8 0 bank256 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl253 : Blocked 8 0 bank257 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl254 : Blocked 8 0 bank258 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl255 : Blocked 8 0 bank259 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl256 : Blocked 8 0 bank260 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl257 : Blocked 8 0 bank261 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl258 : Blocked 8 0 bank262 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl259 : Blocked 8 0 bank263 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl260 : Blocked 8 0 bank264 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl261 : Blocked 8 0 bank265 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl262 : Blocked 8 0 bank266 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl263 : Blocked 8 0 bank267 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl264 : Blocked 8 0 bank268 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl265 : Blocked 8 0 bank269 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl266 : Blocked 8 0 bank270 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl267 : Blocked 8 0 bank271 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl268 : Blocked 8 0 bank272 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl269 : Blocked 8 0 bank273 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl270 : Blocked 8 0 bank274 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl271 : Blocked 8 0 bank275 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl272 : Blocked 8 0 bank276 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl273 : Blocked 8 0 bank277 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl274 : Blocked 8 0 bank278 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl275 : Blocked 9 0 bank154 :=
  block_step [] [bank256, bank257, bank258, bank259, bank260, bank261, bank262, bank263, bank264, bank265, bank266, bank267, bank268, bank269, bank270, bank271, bank272, bank273, bank274, bank275, bank276, bank277, bank278] (True.intro) (⟨excl252, excl253, excl254, excl255, excl256, excl257, excl258, excl259, excl260, excl261, excl262, excl263, excl264, excl265, excl266, excl267, excl268, excl269, excl270, excl271, excl272, excl273, excl274, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl276 : Blocked 8 0 bank279 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl277 : Blocked 8 0 bank280 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl278 : Blocked 8 0 bank281 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl279 : Blocked 8 0 bank282 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl280 : Blocked 8 0 bank283 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl281 : Blocked 8 0 bank284 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl282 : Blocked 8 0 bank285 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl283 : Blocked 8 0 bank286 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl284 : Blocked 8 0 bank287 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl285 : Blocked 8 0 bank288 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl286 : Blocked 8 0 bank289 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl287 : Blocked 8 0 bank290 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl288 : Blocked 8 0 bank291 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl289 : Blocked 8 0 bank292 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl290 : Blocked 8 0 bank293 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl291 : Blocked 8 0 bank294 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl292 : Blocked 8 0 bank295 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl293 : Blocked 8 0 bank296 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl294 : Blocked 8 0 bank297 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl295 : Blocked 8 0 bank298 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl296 : Blocked 8 0 bank299 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl297 : Blocked 8 0 bank300 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl298 : Blocked 8 0 bank301 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl299 : Blocked 9 0 bank155 :=
  block_step [] [bank279, bank280, bank281, bank282, bank283, bank284, bank285, bank286, bank287, bank288, bank289, bank290, bank291, bank292, bank293, bank294, bank295, bank296, bank297, bank298, bank299, bank300, bank301] (True.intro) (⟨excl276, excl277, excl278, excl279, excl280, excl281, excl282, excl283, excl284, excl285, excl286, excl287, excl288, excl289, excl290, excl291, excl292, excl293, excl294, excl295, excl296, excl297, excl298, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl300 : Blocked 8 0 bank302 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl301 : Blocked 8 0 bank303 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl302 : Blocked 8 0 bank304 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl303 : Blocked 8 0 bank305 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl304 : Blocked 8 0 bank306 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl305 : Blocked 8 0 bank307 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl306 : Blocked 8 0 bank308 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl307 : Blocked 8 0 bank309 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl308 : Blocked 8 0 bank310 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl309 : Blocked 8 0 bank311 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl310 : Blocked 8 0 bank312 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl311 : Blocked 8 0 bank313 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl312 : Blocked 8 0 bank314 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl313 : Blocked 8 0 bank315 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl314 : Blocked 8 0 bank316 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl315 : Blocked 8 0 bank317 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl316 : Blocked 8 0 bank318 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl317 : Blocked 8 0 bank319 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl318 : Blocked 8 0 bank320 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl319 : Blocked 8 0 bank321 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl320 : Blocked 8 0 bank322 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl321 : Blocked 8 0 bank323 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl322 : Blocked 8 0 bank324 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl323 : Blocked 8 0 bank325 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl324 : Blocked 8 0 bank326 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl325 : Blocked 8 0 bank327 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl326 : Blocked 8 0 bank328 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl327 : Blocked 8 0 bank329 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl328 : Blocked 8 0 bank330 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl329 : Blocked 9 0 bank156 :=
  block_step [] [bank302, bank303, bank304, bank305, bank306, bank307, bank308, bank309, bank310, bank311, bank312, bank313, bank314, bank315, bank316, bank317, bank318, bank319, bank320, bank321, bank322, bank323, bank324, bank325, bank326, bank327, bank328, bank329, bank330] (True.intro) (⟨excl300, excl301, excl302, excl303, excl304, excl305, excl306, excl307, excl308, excl309, excl310, excl311, excl312, excl313, excl314, excl315, excl316, excl317, excl318, excl319, excl320, excl321, excl322, excl323, excl324, excl325, excl326, excl327, excl328, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl330 : Blocked 8 0 bank331 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl331 : Blocked 8 0 bank332 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl332 : Blocked 8 0 bank333 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl333 : Blocked 8 0 bank334 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl334 : Blocked 8 0 bank335 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl335 : Blocked 8 0 bank336 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl336 : Blocked 8 0 bank337 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl337 : Blocked 8 0 bank338 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl338 : Blocked 8 0 bank339 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl339 : Blocked 8 0 bank340 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl340 : Blocked 8 0 bank341 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl341 : Blocked 8 0 bank342 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl342 : Blocked 8 0 bank343 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl343 : Blocked 8 0 bank344 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl344 : Blocked 8 0 bank345 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl345 : Blocked 8 0 bank346 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl346 : Blocked 8 0 bank347 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl347 : Blocked 8 0 bank348 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl348 : Blocked 8 0 bank349 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl349 : Blocked 8 0 bank350 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl350 : Blocked 8 0 bank351 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl351 : Blocked 8 0 bank352 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl352 : Blocked 8 0 bank353 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl353 : Blocked 8 0 bank354 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl354 : Blocked 8 0 bank355 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl355 : Blocked 8 0 bank356 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl356 : Blocked 8 0 bank357 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl357 : Blocked 8 0 bank358 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl358 : Blocked 8 0 bank359 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl359 : Blocked 9 0 bank157 :=
  block_step [] [bank331, bank332, bank333, bank334, bank335, bank336, bank337, bank338, bank339, bank340, bank341, bank342, bank343, bank344, bank345, bank346, bank347, bank348, bank349, bank350, bank351, bank352, bank353, bank354, bank355, bank356, bank357, bank358, bank359] (True.intro) (⟨excl330, excl331, excl332, excl333, excl334, excl335, excl336, excl337, excl338, excl339, excl340, excl341, excl342, excl343, excl344, excl345, excl346, excl347, excl348, excl349, excl350, excl351, excl352, excl353, excl354, excl355, excl356, excl357, excl358, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl360 : Blocked 9 1 bank1 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl361 : Blocked 9 1 bank2 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl362 : Blocked 9 1 bank3 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl363 : Blocked 9 1 bank4 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl364 : Blocked 9 1 bank5 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl365 : Blocked 8 0 bank360 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl366 : Blocked 7 1 bank86 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl367 : Blocked 7 1 bank87 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl368 : Blocked 7 1 bank88 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl369 : Blocked 7 1 bank89 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl370 : Blocked 7 1 bank90 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl371 : Blocked 7 1 bank91 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl372 : Blocked 8 1 bank66 :=
  block_step [] [bank86, bank87, bank88, bank89, bank90, bank91] (True.intro) (⟨excl366, excl367, excl368, excl369, excl370, excl371, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl373 : Blocked 7 1 bank92 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl374 : Blocked 7 1 bank93 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl375 : Blocked 7 1 bank94 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl376 : Blocked 7 1 bank95 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl377 : Blocked 7 1 bank96 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl378 : Blocked 7 1 bank97 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl379 : Blocked 8 1 bank67 :=
  block_step [] [bank92, bank93, bank94, bank95, bank96, bank97] (True.intro) (⟨excl373, excl374, excl375, excl376, excl377, excl378, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl380 : Blocked 8 1 bank68 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl381 : Blocked 8 1 bank69 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl382 : Blocked 8 1 bank70 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl383 : Blocked 8 1 bank71 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl384 : Blocked 8 1 bank72 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl385 : Blocked 8 1 bank73 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl386 : Blocked 8 1 bank74 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl387 : Blocked 8 1 bank75 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl388 : Blocked 8 1 bank76 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl389 : Blocked 8 1 bank77 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl390 : Blocked 8 1 bank78 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl391 : Blocked 8 1 bank79 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl392 : Blocked 8 1 bank80 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl393 : Blocked 8 1 bank81 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl394 : Blocked 8 1 bank82 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl395 : Blocked 8 1 bank83 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl396 : Blocked 7 0 bank361 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl397 : Blocked 7 0 bank362 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl398 : Blocked 7 0 bank363 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl399 : Blocked 7 0 bank364 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl400 : Blocked 7 0 bank365 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl401 : Blocked 7 0 bank366 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl402 : Blocked 7 0 bank367 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl403 : Blocked 7 1 bank368 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl404 : Blocked 7 1 bank369 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl405 : Blocked 7 1 bank370 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl406 : Blocked 7 1 bank371 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl407 : Blocked 7 1 bank372 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl408 : Blocked 7 1 bank373 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl409 : Blocked 8 1 bank84 :=
  block_step [bank361, bank362, bank363, bank364, bank365, bank366, bank367] [bank89, bank95, bank368, bank369, bank370, bank371, bank372, bank373] (⟨excl396, excl397, excl398, excl399, excl400, excl401, excl402, True.intro⟩) (⟨excl369, excl376, excl403, excl404, excl405, excl406, excl407, excl408, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl410 : Blocked 7 0 bank374 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl411 : Blocked 7 0 bank375 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl412 : Blocked 7 0 bank376 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl413 : Blocked 7 0 bank377 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl414 : Blocked 7 0 bank378 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl415 : Blocked 7 0 bank379 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl416 : Blocked 7 0 bank380 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl417 : Blocked 7 1 bank381 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl418 : Blocked 7 1 bank382 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl419 : Blocked 7 1 bank383 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl420 : Blocked 7 1 bank384 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl421 : Blocked 7 1 bank385 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl422 : Blocked 7 1 bank386 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl423 : Blocked 8 1 bank85 :=
  block_step [bank374, bank375, bank376, bank377, bank378, bank379, bank380] [bank90, bank96, bank381, bank382, bank383, bank384, bank385, bank386] (⟨excl410, excl411, excl412, excl413, excl414, excl415, excl416, True.intro⟩) (⟨excl370, excl377, excl417, excl418, excl419, excl420, excl421, excl422, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl424 : Blocked 9 1 bank6 :=
  block_step [bank158, bank183, bank208, bank233, bank256, bank302, bank331, bank360] [bank66, bank67, bank68, bank69, bank70, bank71, bank72, bank73, bank74, bank75, bank76, bank77, bank78, bank79, bank80, bank81, bank82, bank83, bank84, bank85] (⟨excl150, excl176, excl202, excl228, excl252, excl300, excl330, excl365, True.intro⟩) (⟨excl372, excl379, excl380, excl381, excl382, excl383, excl384, excl385, excl386, excl387, excl388, excl389, excl390, excl391, excl392, excl393, excl394, excl395, excl409, excl423, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl425 : Blocked 9 1 bank7 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl426 : Blocked 8 0 bank387 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl427 : Blocked 7 1 bank117 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl428 : Blocked 7 1 bank118 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl429 : Blocked 7 1 bank119 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl430 : Blocked 7 1 bank120 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl431 : Blocked 7 1 bank121 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl432 : Blocked 7 1 bank122 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl433 : Blocked 8 1 bank98 :=
  block_step [] [bank117, bank118, bank119, bank120, bank121, bank122] (True.intro) (⟨excl427, excl428, excl429, excl430, excl431, excl432, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl434 : Blocked 8 1 bank99 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl435 : Blocked 8 1 bank100 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl436 : Blocked 8 1 bank101 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl437 : Blocked 8 1 bank102 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl438 : Blocked 8 1 bank103 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl439 : Blocked 8 1 bank104 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl440 : Blocked 8 1 bank105 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl441 : Blocked 8 1 bank106 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl442 : Blocked 8 1 bank107 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl443 : Blocked 8 1 bank108 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl444 : Blocked 8 1 bank109 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl445 : Blocked 8 1 bank110 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl446 : Blocked 8 1 bank111 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl447 : Blocked 8 1 bank112 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl448 : Blocked 8 1 bank113 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl449 : Blocked 8 1 bank114 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl450 : Blocked 7 0 bank388 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl451 : Blocked 7 0 bank389 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl452 : Blocked 7 0 bank390 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl453 : Blocked 7 0 bank391 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl454 : Blocked 7 0 bank392 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl455 : Blocked 7 0 bank393 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl456 : Blocked 7 0 bank394 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl457 : Blocked 7 1 bank395 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl458 : Blocked 7 1 bank396 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl459 : Blocked 7 1 bank397 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl460 : Blocked 7 1 bank398 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl461 : Blocked 7 1 bank399 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl462 : Blocked 7 1 bank400 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl463 : Blocked 8 1 bank115 :=
  block_step [bank388, bank389, bank390, bank391, bank392, bank393, bank394] [bank87, bank120, bank395, bank396, bank397, bank398, bank399, bank400] (⟨excl450, excl451, excl452, excl453, excl454, excl455, excl456, True.intro⟩) (⟨excl367, excl430, excl457, excl458, excl459, excl460, excl461, excl462, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl464 : Blocked 7 0 bank401 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl465 : Blocked 7 0 bank402 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl466 : Blocked 7 0 bank403 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl467 : Blocked 7 0 bank404 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl468 : Blocked 7 0 bank405 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl469 : Blocked 7 0 bank406 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl470 : Blocked 7 0 bank407 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl471 : Blocked 7 1 bank408 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl472 : Blocked 7 1 bank409 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl473 : Blocked 7 1 bank410 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl474 : Blocked 7 1 bank411 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl475 : Blocked 7 1 bank412 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl476 : Blocked 7 1 bank413 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl477 : Blocked 8 1 bank116 :=
  block_step [bank401, bank402, bank403, bank404, bank405, bank406, bank407] [bank88, bank121, bank408, bank409, bank410, bank411, bank412, bank413] (⟨excl464, excl465, excl466, excl467, excl468, excl469, excl470, True.intro⟩) (⟨excl368, excl431, excl471, excl472, excl473, excl474, excl475, excl476, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl478 : Blocked 9 1 bank8 :=
  block_step [bank159, bank184, bank209, bank234, bank280, bank303, bank332, bank387] [bank66, bank98, bank99, bank100, bank101, bank102, bank103, bank104, bank105, bank106, bank107, bank108, bank109, bank110, bank111, bank112, bank113, bank114, bank115, bank116] (⟨excl151, excl177, excl203, excl229, excl277, excl301, excl331, excl426, True.intro⟩) (⟨excl372, excl433, excl434, excl435, excl436, excl437, excl438, excl439, excl440, excl441, excl442, excl443, excl444, excl445, excl446, excl447, excl448, excl449, excl463, excl477, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl479 : Blocked 9 1 bank9 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl480 : Blocked 8 0 bank414 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl481 : Blocked 8 1 bank123 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl482 : Blocked 8 1 bank124 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl483 : Blocked 8 1 bank125 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl484 : Blocked 8 1 bank126 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl485 : Blocked 8 1 bank127 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl486 : Blocked 8 1 bank128 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl487 : Blocked 8 1 bank129 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl488 : Blocked 8 1 bank130 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl489 : Blocked 8 1 bank131 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl490 : Blocked 8 1 bank132 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl491 : Blocked 8 1 bank133 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl492 : Blocked 8 1 bank134 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl493 : Blocked 8 1 bank135 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl494 : Blocked 8 1 bank136 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl495 : Blocked 8 1 bank137 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl496 : Blocked 8 1 bank138 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl497 : Blocked 7 0 bank415 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl498 : Blocked 7 0 bank416 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl499 : Blocked 7 0 bank417 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl500 : Blocked 7 0 bank418 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl501 : Blocked 7 0 bank419 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl502 : Blocked 7 0 bank420 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl503 : Blocked 7 0 bank421 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl504 : Blocked 7 1 bank422 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl505 : Blocked 7 1 bank423 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl506 : Blocked 7 1 bank424 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl507 : Blocked 7 1 bank425 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl508 : Blocked 7 1 bank426 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl509 : Blocked 7 1 bank427 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl510 : Blocked 8 1 bank139 :=
  block_step [bank415, bank416, bank417, bank418, bank419, bank420, bank421] [bank93, bank118, bank422, bank423, bank424, bank425, bank426, bank427] (⟨excl497, excl498, excl499, excl500, excl501, excl502, excl503, True.intro⟩) (⟨excl374, excl428, excl504, excl505, excl506, excl507, excl508, excl509, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl511 : Blocked 7 0 bank428 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl512 : Blocked 7 0 bank429 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl513 : Blocked 7 0 bank430 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl514 : Blocked 7 0 bank431 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl515 : Blocked 7 0 bank432 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl516 : Blocked 7 0 bank433 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl517 : Blocked 7 0 bank434 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl518 : Blocked 7 1 bank435 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl519 : Blocked 7 1 bank436 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl520 : Blocked 7 1 bank437 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl521 : Blocked 7 1 bank438 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl522 : Blocked 7 1 bank439 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl523 : Blocked 7 1 bank440 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl524 : Blocked 8 1 bank140 :=
  block_step [bank428, bank429, bank430, bank431, bank432, bank433, bank434] [bank94, bank119, bank435, bank436, bank437, bank438, bank439, bank440] (⟨excl511, excl512, excl513, excl514, excl515, excl516, excl517, True.intro⟩) (⟨excl375, excl429, excl518, excl519, excl520, excl521, excl522, excl523, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl525 : Blocked 9 1 bank10 :=
  block_step [bank160, bank185, bank210, bank258, bank281, bank304, bank333, bank414] [bank67, bank98, bank123, bank124, bank125, bank126, bank127, bank128, bank129, bank130, bank131, bank132, bank133, bank134, bank135, bank136, bank137, bank138, bank139, bank140] (⟨excl152, excl178, excl204, excl254, excl278, excl302, excl332, excl480, True.intro⟩) (⟨excl379, excl433, excl481, excl482, excl483, excl484, excl485, excl486, excl487, excl488, excl489, excl490, excl491, excl492, excl493, excl494, excl495, excl496, excl510, excl524, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl526 : Blocked 9 1 bank11 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl527 : Blocked 9 1 bank12 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl528 : Blocked 9 1 bank13 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl529 : Blocked 9 1 bank14 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl530 : Blocked 9 1 bank15 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl531 : Blocked 9 1 bank16 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl532 : Blocked 9 1 bank17 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl533 : Blocked 9 1 bank18 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl534 : Blocked 9 1 bank19 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl535 : Blocked 9 1 bank20 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl536 : Blocked 9 1 bank21 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl537 : Blocked 9 1 bank22 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl538 : Blocked 9 1 bank23 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl539 : Blocked 9 1 bank24 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl540 : Blocked 9 1 bank25 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl541 : Blocked 9 1 bank26 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl542 : Blocked 9 1 bank27 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl543 : Blocked 9 1 bank28 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl544 : Blocked 9 1 bank29 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl545 : Blocked 9 1 bank30 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl546 : Blocked 9 1 bank31 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl547 : Blocked 9 1 bank32 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl548 : Blocked 9 1 bank33 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl549 : Blocked 9 1 bank34 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl550 : Blocked 9 1 bank35 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl551 : Blocked 9 1 bank36 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl552 : Blocked 9 1 bank37 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl553 : Blocked 9 1 bank38 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl554 : Blocked 9 1 bank39 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl555 : Blocked 9 1 bank40 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl556 : Blocked 9 1 bank41 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl557 : Blocked 9 1 bank42 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl558 : Blocked 9 1 bank43 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl559 : Blocked 9 1 bank44 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl560 : Blocked 9 1 bank45 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl561 : Blocked 9 1 bank46 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl562 : Blocked 9 1 bank47 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl563 : Blocked 9 1 bank48 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl564 : Blocked 9 1 bank49 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl565 : Blocked 9 1 bank50 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl566 : Blocked 9 1 bank51 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl567 : Blocked 9 1 bank52 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl568 : Blocked 9 1 bank53 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl569 : Blocked 8 0 bank441 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl570 : Blocked 8 1 bank141 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl571 : Blocked 8 1 bank142 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl572 : Blocked 8 1 bank143 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl573 : Blocked 9 1 bank54 :=
  block_step [bank441] [bank70, bank127, bank141, bank142, bank143] (⟨excl569, True.intro⟩) (⟨excl382, excl485, excl570, excl571, excl572, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl574 : Blocked 8 0 bank442 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl575 : Blocked 8 1 bank144 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl576 : Blocked 8 1 bank145 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl577 : Blocked 8 1 bank146 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl578 : Blocked 9 1 bank55 :=
  block_step [bank442] [bank71, bank102, bank144, bank145, bank146] (⟨excl574, True.intro⟩) (⟨excl383, excl437, excl575, excl576, excl577, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl579 : Blocked 8 0 bank443 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl580 : Blocked 8 1 bank147 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl581 : Blocked 8 1 bank148 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl582 : Blocked 8 1 bank149 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl583 : Blocked 9 1 bank56 :=
  block_step [bank443] [bank103, bank128, bank147, bank148, bank149] (⟨excl579, True.intro⟩) (⟨excl438, excl486, excl580, excl581, excl582, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl584 : Blocked 9 1 bank57 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl585 : Blocked 9 1 bank58 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl586 : Blocked 9 1 bank59 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl587 : Blocked 8 0 bank444 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl588 : Blocked 8 1 bank445 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl589 : Blocked 8 1 bank446 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl590 : Blocked 8 1 bank447 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl591 : Blocked 8 1 bank448 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl592 : Blocked 8 1 bank449 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl593 : Blocked 8 1 bank450 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl594 : Blocked 8 1 bank451 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl595 : Blocked 9 1 bank60 :=
  block_step [bank168, bank193, bank225, bank444, bank273, bank296, bank325, bank354] [bank75, bank106, bank445, bank446, bank447, bank448, bank449, bank450, bank451] (⟨excl160, excl186, excl219, excl587, excl269, excl293, excl323, excl353, True.intro⟩) (⟨excl387, excl441, excl588, excl589, excl590, excl591, excl592, excl593, excl594, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl596 : Blocked 8 0 bank452 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl597 : Blocked 8 1 bank453 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl598 : Blocked 8 1 bank454 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl599 : Blocked 8 1 bank455 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl600 : Blocked 8 1 bank456 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl601 : Blocked 8 1 bank457 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl602 : Blocked 8 1 bank458 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl603 : Blocked 9 1 bank61 :=
  block_step [bank169, bank194, bank226, bank452, bank274, bank297, bank326, bank355] [bank76, bank107, bank453, bank446, bank454, bank455, bank456, bank457, bank458] (⟨excl161, excl187, excl220, excl596, excl270, excl294, excl324, excl354, True.intro⟩) (⟨excl388, excl442, excl597, excl589, excl598, excl599, excl600, excl601, excl602, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl604 : Blocked 8 0 bank459 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl605 : Blocked 8 1 bank460 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl606 : Blocked 8 1 bank461 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl607 : Blocked 8 1 bank462 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl608 : Blocked 8 1 bank463 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl609 : Blocked 8 1 bank464 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl610 : Blocked 9 1 bank62 :=
  block_step [bank170, bank202, bank229, bank252, bank459, bank298, bank327, bank356] [bank78, bank460, bank130, bank447, bank454, bank461, bank462, bank463, bank464] (⟨excl162, excl195, excl223, excl247, excl604, excl295, excl325, excl355, True.intro⟩) (⟨excl390, excl605, excl488, excl590, excl598, excl606, excl607, excl608, excl609, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl611 : Blocked 8 0 bank465 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl612 : Blocked 8 1 bank466 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl613 : Blocked 8 1 bank467 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl614 : Blocked 8 1 bank468 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl615 : Blocked 8 1 bank469 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl616 : Blocked 9 1 bank63 :=
  block_step [bank171, bank203, bank230, bank253, bank465, bank299, bank328, bank357] [bank79, bank131, bank466, bank448, bank455, bank461, bank467, bank468, bank469] (⟨excl163, excl196, excl224, excl248, excl611, excl296, excl326, excl356, True.intro⟩) (⟨excl391, excl489, excl612, excl591, excl599, excl606, excl613, excl614, excl615, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl617 : Blocked 8 0 bank470 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl618 : Blocked 8 1 bank471 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl619 : Blocked 8 1 bank472 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl620 : Blocked 8 1 bank473 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl621 : Blocked 9 1 bank64 :=
  block_step [bank179, bank206, bank231, bank254, bank277, bank470, bank329, bank358] [bank471, bank109, bank133, bank449, bank456, bank462, bank467, bank472, bank473] (⟨excl171, excl199, excl225, excl249, excl273, excl617, excl327, excl357, True.intro⟩) (⟨excl618, excl444, excl491, excl592, excl600, excl607, excl613, excl619, excl620, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl622 : Blocked 8 0 bank474 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl623 : Blocked 8 1 bank475 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl624 : Blocked 8 1 bank476 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl625 : Blocked 9 1 bank65 :=
  block_step [bank180, bank207, bank232, bank255, bank278, bank474, bank330, bank359] [bank110, bank134, bank475, bank450, bank457, bank463, bank468, bank472, bank476] (⟨excl172, excl200, excl226, excl250, excl274, excl622, excl328, excl358, True.intro⟩) (⟨excl445, excl492, excl623, excl593, excl601, excl608, excl614, excl619, excl624, True.intro⟩) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16000 in
theorem excl626 : Blocked 10 1 root :=
  block_step [bank150, bank151, bank152, bank153, bank154, bank155, bank156, bank157] [bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank17, bank18, bank19, bank20, bank21, bank22, bank23, bank24, bank25, bank26, bank27, bank28, bank29, bank30, bank31, bank32, bank33, bank34, bank35, bank36, bank37, bank38, bank39, bank40, bank41, bank42, bank43, bank44, bank45, bank46, bank47, bank48, bank49, bank50, bank51, bank52, bank53, bank54, bank55, bank56, bank57, bank58, bank59, bank60, bank61, bank62, bank63, bank64, bank65] (⟨excl175, excl201, excl227, excl251, excl275, excl299, excl329, excl359, True.intro⟩) (⟨excl360, excl361, excl362, excl363, excl364, excl424, excl425, excl478, excl479, excl525, excl526, excl527, excl528, excl529, excl530, excl531, excl532, excl533, excl534, excl535, excl536, excl537, excl538, excl539, excl540, excl541, excl542, excl543, excl544, excl545, excl546, excl547, excl548, excl549, excl550, excl551, excl552, excl553, excl554, excl555, excl556, excl557, excl558, excl559, excl560, excl561, excl562, excl563, excl564, excl565, excl566, excl567, excl568, excl573, excl578, excl583, excl584, excl585, excl586, excl595, excl603, excl610, excl616, excl621, excl625, True.intro⟩) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_26688_aux

open PEqualNP.Outside.L_meta_26688_aux in
theorem PEqualNP.Outside.L_meta_26688 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 0, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 0, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 0, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 0, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 0, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 4, 6, 0, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o basis single computes
  by_cases used : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact ⟨replacement.gates, replacement.output, replacement_basis,
      lower_with_not gates o basis single used computes excl149 excl626, replacement_correct⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    refine ⟨?_, (basis g hg).2⟩
    rcases (basis g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (used ⟨g, hg, h⟩).elim

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_52928
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 256
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

def W (a : Nat) : Sig := BitVec.ofNat 256 a
def full : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | _ => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
set_option maxRecDepth 8192 in
theorem W_inj {a b : Nat} (ha : a < 2^256) (hb : b < 2^256) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^256) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 256) && decide (e.2.2 < 256) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^256 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^256 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 256).all (fun r => let q := rowOf vs w r
    Nat.blt q 256 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 256).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 256).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 256).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List Nat → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List Nat) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) := by
      cases ho : opOK u (Nat.mod c 4)
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb (Nat.mod c 4) _ _ ho hr hP (getD_ps hP (Nat.mod (Nat.div c 4) 32)) (getD_ps hP (Nat.div c 128))
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 256 && Nat.blt p.2 256 && T.testBit p.1 && !(T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx

def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 256 && Nat.blt n 256 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 256) (hn : n < 256), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
set_option maxRecDepth 8192 in
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^256) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^256 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 256
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3

def hiM : Nat → Nat
  | 0 => 0x2222222222222222222222222222222222222222222222222222222222222222
  | 1 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
  | 3 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff0000
  | 5 => 0xffffffff000000000000000000000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def loM : Nat → Nat
  | 0 => 0x4444444444444444444444444444444444444444444444444444444444444444
  | 1 => 0x3030303030303030303030303030303030303030303030303030303030303030
  | 2 => 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
  | 3 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff00000000
  | 5 => 0xffffffff000000000000000000000000ffffffff0000000000000000
  | _ => 0xffffffffffffffff00000000000000000000000000000000
def keM : Nat → Nat
  | 0 => 0x9999999999999999999999999999999999999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff
  | 4 => 0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff
  | 5 => 0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff
  | _ => 0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | _ => 64
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 256 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 256 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 7) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 7) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := (l.all fun i => Nat.blt i 7) && Nat.beq (permN l T) T
def sigL : List Nat → Row → Row
  | [] => id
  | i::l => fun r => sig i (sigL l r)
theorem sigL_surj (l : List Nat) (hl : l.all (fun i => Nat.blt i 7) = true) : Function.Surjective (sigL l) := by
  induction l with
  | nil => exact Function.surjective_id
  | cons i l ih =>
    simp only [List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hl
    intro r
    obtain ⟨x,hx⟩ := ih hl.2 (sig i r)
    exact ⟨x,by change sig i (sigL l x) = r; rw [hx,(swap_facts ⟨i,hl.1⟩ r).2]⟩
theorem perm_ok (l : List Nat) (hl : l.all (fun i => Nat.blt i 7) = true) (v : Nat) :
    W (permN l v) = rename (sigL l) (W v) := by
  induction l generalizing v with
  | nil => apply bit_ext; intro r; rw [bit_W,bit_rename,bit_W]; rfl
  | cons i l ih =>
    simp only [List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hl
    change W (permN l (swapN i v)) = _
    rw [ih hl.2,swap_ok i hl.1 v]
    apply bit_ext; intro r
    simp only [bit_rename]; rfl
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  simp only [symOK,Bool.and_eq_true] at hT
  obtain ⟨hl,hs⟩ := hT
  intro k' hk run
  have r2 := live_rename run (sigL l) (sigL_surj l hl)
  rw [←perm_ok l hl T,Nat.eq_of_beq_eq_true hs] at r2
  apply h k' hk
  have : ((s.map (permN l)).map W).toFinset = (s.map W).toFinset.image (rename (sigL l)) := by
    ext v
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,perm_ok l hl]
  rw [this]
  exact r2

abbrev StD := List Nat × List Nat × List Nat
def pick : List Nat → Nat → List Nat
  | [],_ => []
  | x::xs,m => bif Nat.beq (Nat.mod m 2) 1 then x :: pick xs (Nat.div m 2) else pick xs (Nat.div m 2)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List Nat) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := Array CutV × Array (Nat × Nat) × List KwD × Array (List Nat)
def Tabs.cuts (t : Tabs) : Array CutV := t.1
def Tabs.seps (t : Tabs) : Array (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : Array (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def ty (i n : Nat) : Bool := Nat.beq (Nat.mod i 4) n
def hintOK (u : Bool) (k : Nat) (next : Array (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif ty i 0 then (match t.cuts[Nat.div i 4]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif ty i 1 then (match t.seps[Nat.div i 4]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif ty i 2 then (match t.kws[Nat.div i 4]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else
    let q := Nat.div i 4
    match t.perms[Nat.mod q 16]?, next[Nat.div q 16]? with
    | some l, some s => beqL (sortN ((kidN rest a b z ka kb).map (permN l))) s
    | _, _ => false
def kidOK (u : Bool) (k : Nat) (next : Array (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : Array (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^256)
  | x::y::l => Nat.blt x y && asc (y::l)
set_option maxRecDepth 8192 in
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^256 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : Array (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) (st.2.2.map (pick st.2.1))
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : Array (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts.toList, CutP u R T c) ∧ t.seps.toList.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.toList.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts.toList, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.toList.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.toList.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List Nat)} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ (C.map (mkCut u Z)).toArray.toList, CutP u R T c := by
  intro c hc
  have hc' : c ∈ C.map (mkCut u Z) := by simpa using hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc'
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

set_option maxRecDepth 8192 in
theorem stStep {u R T E t k} {next : Array (List Nat)} {st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next.toList, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp

  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^256 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^256 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^256 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^256 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : ty i 0
      · rw [h1,cond_false] at hi
        cases h2 : ty i 1
        · rw [h2,cond_false] at hi
          cases h3 : ty i 2
          · rw [h3,cond_false] at hi
            dsimp only at hi
            cases hg : t.perms[Nat.mod (Nat.div i 4) 16]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              cases hs_opt : next[Nat.div (Nat.div i 4) 16]? with
              | none => rw [hg,hs_opt] at hi; exact Bool.noConfusion hi
              | some s =>
                rw [hg,hs_opt] at hi
                have hpl : l ∈ t.perms := by
                  rw [Array.getElem?_eq_some_iff] at hg
                  obtain ⟨hidx, rfl⟩ := hg
                  exact Array.getElem_mem hidx
                rw [←kid_fin]
                apply perm_sound l (List.all_eq_true.mp ht.p l (Array.mem_toList_iff.mpr hpl))
                have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                  rw [←beqL_ok hi]
                  ext v
                  simp only [List.mem_toFinset,List.mem_map,mem_sortN]
                rw [this]
                have hmem : s ∈ next := by
                  rw [Array.getElem?_eq_some_iff] at hs_opt
                  obtain ⟨hidx, rfl⟩ := hs_opt
                  exact Array.getElem_mem hidx
                exact hn s (Array.mem_toList_iff.mpr hmem)
          · rw [h3,cond_true] at hi
            cases hg : t.kws[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[Nat.div i 4]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            have hq : q ∈ t.seps := by
              rw [Array.getElem?_eq_some_iff] at hg
              obtain ⟨hidx, rfl⟩ := hg
              exact Array.getElem_mem hidx
            exact sep_sound (List.all_eq_true.mp ht.s q (Array.mem_toList_iff.mpr hq)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[Nat.div i 4]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          have hq : q ∈ t.cuts := by
            rw [Array.getElem?_eq_some_iff] at hg
            obtain ⟨hidx, rfl⟩ := hg
            exact Array.getElem_mem hidx
          exact cut_sound (ht.c q (Array.mem_toList_iff.mpr hq)) (opk ho4) nk hi
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst).toArray D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  simp at hs
  obtain ⟨b1, b2, hmem⟩ := hs
  exact hI (s, b1, b2) hmem
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : Array (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def LevelB (u : Bool) (T k : Nat) (B : List (List StD)) : Prop :=
  ∀ c ∈ B, ∀ st ∈ c, Impossible u (W T) k (st.1.map W).toFinset
def mkNext (B : List (List StD)) : Array (List Nat) :=
  (B.flatten.map Prod.fst).toArray
theorem levelStepB {u R T E t k B' B} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelB u T k B')
    (h : ∀ c ∈ B, levelOK u T t k (mkNext B') c = true) : LevelB u T (k+1) B := by
  intro c hc st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp (h c hc) st hst)
  intro s hs
  have hs' : s ∈ B'.flatten.map Prod.fst := by simpa [mkNext] using hs
  obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hs'
  obtain ⟨c', hc', hstc'⟩ := List.mem_flatten.mp hst'
  exact hI c' hc' st' hstc'
theorem lowSearchB {u R T E K B} (hB : baseOK T R E = true) (hI : LevelB u T K B)
    (h : (mkNext B).toList.contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  have h' : R.map xN ∈ B.flatten.map Prod.fst := by simpa [mkNext] using h
  obtain ⟨st, hst, e⟩ := List.mem_map.mp h'
  obtain ⟨c, hc, hstc⟩ := List.mem_flatten.mp hst
  have := hI c hc st hstc
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def pw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw1 : Nat := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def pw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def pw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def pw4 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def pw5 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def pw6 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def pw7 : Nat := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def pw8 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def pw9 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def pw10 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def pw11 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def pw12 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def pw13 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def pw14 : Nat := 0xfefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe
def pw15 : Nat := 0xccee0000ccee0000ccee0000ccee0000ccee0000ccee0000ccee0000ccee
def pw16 : Nat := 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8
def pw17 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
def pw18 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa
def pw19 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0
def pw20 : Nat := 0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe
def pw21 : Nat := 0xfafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa
def pw22 : Nat := 0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee
def pw23 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw24 : Nat := 0xcceecceecceecceecceecceecceecceecceecceecceecceecceecceecceeccee
def pw25 : Nat := 0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa
def pw26 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def pw27 : Nat := 0x5454545454545454545454545454545454545454545454545454545454545454
def pw28 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def pw29 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def pw30 : Nat := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa
def pw31 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa
def pw32 : Nat := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc
def pw33 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe
def pw34 : Nat := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e
def pw35 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0
def pw36 : Nat := 0x3332333233323332333233323332333233323332333233323332333233323332
def pw37 : Nat := 0x5554555455545554555455545554555455545554555455545554555455545554
def pw38 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def pw39 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee
def pw40 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee
def pw41 : Nat := 0x3232323232323232323232323232323232323232323232323232323232323232
def pw42 : Nat := 0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa
def pw43 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa
def pw44 : Nat := 0x3322332233223322332233223322332233223322332233223322332233223322
def pw45 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def pw46 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffc
def pw47 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc
def pw48 : Nat := 0x5544554455445544554455445544554455445544554455445544554455445544
def pw49 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def pw50 : Nat := 0x5550555055505550555055505550555055505550555055505550555055505550
def pw51 : Nat := 0x3330333033303330333033303330333033303330333033303330333033303330
def pw52 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def pw53 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def pw54 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def pw55 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def pw56 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def pw57 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def pw58 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def pw59 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def pw60 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def pw61 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def pw62 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def pw63 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def pw64 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def pw65 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def pw66 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def pw67 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def pw68 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def pw69 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def pw70 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def pw71 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def pw72 : Nat := 0xffeeeeeeffeeeeeeffeeeeeeffeeeeeeffeeeeeeffeeeeeeffeeeeeeffeeeeee
def pw73 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00
def pw74 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa
def pw75 : Nat := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc
def pw76 : Nat := 0xffffeeeeffffee00ffffeeeeffffee00ffffeeeeffffee00ffffeeeeffffee00
def pw77 : Nat := 0xffeeffeeffeeff00ffeeffeeffeeff00ffeeffeeffeeff00ffeeffeeffeeff00
def pw78 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeee
def pw79 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee
def pw80 : Nat := 0xf0f0fefe00000000f0f0fefe00000000f0f0fefe00000000f0f0fefe
def pw81 : Nat := 0xff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00ff00ee00
def pw82 : Nat := 0x77767776000000007776777600000000777677760000000077767776
def pw83 : Nat := 0xfffefffe00000000fffefffe00000000fffefffe00000000fffefffe
def pw84 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def pw85 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88
def pw86 : Nat := 0xffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888
def pw87 : Nat := 0xfefefefe00000000fefefefe00000000fefefefe00000000fefefefe
def pw88 : Nat := 0xffccccccffccccccffccccccffccccccffccccccffccccccffccccccffcccccc
def pw89 : Nat := 0x70707676000000007070767600000000707076760000000070707676
def pw90 : Nat := 0xffffeee0ffffeee0ffffeee0ffffeee0ffffeee0ffffeee0ffffeee0ffffeee0
def pw91 : Nat := 0xffffffffeeeee0e0ffffffffeeeee0e0ffffffffeeeee0e0ffffffffeeeee0e0
def pw92 : Nat := 0xffffffffeee0eee0ffffffffeee0eee0ffffffffeee0eee0ffffffffeee0eee0
def pw93 : Nat := 0xffffffffeee8eee8ffffffffeee8eee8ffffffffeee8eee8ffffffffeee8eee8
def pw94 : Nat := 0xffffe0e0ffffe0e0ffffe0e0ffffe0e0ffffe0e0ffffe0e0ffffe0e0ffffe0e0
def pw95 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc
def pw96 : Nat := 0xffffffffe0e0e0e0ffffffffe0e0e0e0ffffffffe0e0e0e0ffffffffe0e0e0e0
def pw97 : Nat := 0x10101010f0f0f0f010101010f0f0f0f010101010f0f0f0f010101010f0f0f0f0
def pw98 : Nat := 0xf0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0
def pw99 : Nat := 0xfefefefeeeeeeeeefefefefeeeeeeeeefefefefeeeeeeeeefefefefeeeeeeeee
def pw100 : Nat := 0xeeeeee00eeeeee00eeeeee00eeeeee00eeeeee00eeeeee00eeeeee00eeeeee
def pw101 : Nat := 0xfffff0f0ffff0000fffff0f0ffff0000fffff0f0ffff0000fffff0f0ffff0000
def pw102 : Nat := 0xffffffffffccccccffffffffffccccccffffffffffccccccffffffffffcccccc
def pw103 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000
def pw104 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0
def pw105 : Nat := 0xffffffffffffffccffffffffffffffccffffffffffffffccffffffffffffffcc
def pw106 : Nat := 0xffffffffccccffccffffffffccccffccffffffffccccffccffffffffccccffcc
def pw107 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaa
def pw108 : Nat := 0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc
def pw109 : Nat := 0xffaaffaa00000000ffaaffaa00000000ffaaffaa00000000ffaaffaa
def pw110 : Nat := 0xfffafffa00000000fffafffa00000000fffafffa00000000fffafffa
def pw111 : Nat := 0xff00ff30ff00ff30ff00ff30ff00ff30ff00ff30ff00ff30ff00ff30ff00ff30
def pw112 : Nat := 0xf0f0f0f0fffafffaf0f0f0f0fffafffaf0f0f0f0fffafffaf0f0f0f0fffafffa
def pw113 : Nat := 0xeeee000000000000eeee000000000000eeee000000000000eeee
def pw114 : Nat := 0xeee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0
def pw115 : Nat := 0xffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee
def pw116 : Nat := 0xffeeffe0ffeeffe0ffeeffe0ffeeffe0ffeeffe0ffeeffe0ffeeffe0ffeeffe0
def pw117 : Nat := 0x8888888888888888888888888888888888888888888888888888888888888888
def pw118 : Nat := 0xfef0fef0fef0fef0fef0fef0fef0fef0fef0fef0fef0fef0fef0fef0fef0fef0
def pw119 : Nat := 0xffffee00ffffee00ffffee00ffffee00ffffee00ffffee00ffffee00ffffee00
def pw120 : Nat := 0x1100ff001100ff001100ff001100ff001100ff001100ff001100ff001100ff00
def pw121 : Nat := 0xff00fe00ff00fe00ff00fe00ff00fe00ff00fe00ff00fe00ff00fe00ff00fe00
def pw122 : Nat := 0xfffe0000fffe0000fffe0000fffe0000fffe0000fffe0000fffe0000fffe
def pw123 : Nat := 0xffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000
def pw124 : Nat := 0xfffe0000fffe0000fffe0000fffe0000fffe0000fffe0000fffe0000fffe0000
def pw125 : Nat := 0xf0f0f0f0fef0fef0f0f0f0f0fef0fef0f0f0f0f0fef0fef0f0f0f0f0fef0fef0
def pw126 : Nat := 0xff000000ff00fe00ff000000ff00fe00ff000000ff00fe00ff000000ff00fe00
def pw127 : Nat := 0xf0f0fffe00000000f0f0fffe00000000f0f0fffe00000000f0f0fffe
def pw128 : Nat := 0xf0f0fffe0000ffeef0f0fffe0000ffeef0f0fffe0000ffeef0f0fffe0000ffee
def pw129 : Nat := 0xfefefe0000000000fefefe0000000000fefefe0000000000fefefe
def pw130 : Nat := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0fff0f0f0fff0f0f0fff0f0f0fff0f0f0
def pw131 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000
def pw132 : Nat := 0x1111000011110000111100001111000011110000111100001111000011110000
def pw133 : Nat := 0x3333000033330000333300003333000033330000333300003333000033330000
def pw134 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def pw135 : Nat := 0xff000000ffee0000ff000000ffee0000ff000000ffee0000ff000000ffee
def pw136 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
def pw137 : Nat := 0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee
def pw138 : Nat := 0x1010101010101010101010101010101010101010101010101010101010101010
def pw139 : Nat := 0xffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc
def pw140 : Nat := 0x33003300000000003300330000000000330033000000000033003300
def pw141 : Nat := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000
def pw142 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafa
def pw143 : Nat := 0xf0f0fefef0f0fefef0f0fefef0f0fefef0f0fefef0f0fefef0f0fefef0f0fefe
def pw144 : Nat := 0xffeeffee00000000ffeeffee00000000ffeeffee00000000ffeeffee
def pw145 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00
def pw146 : Nat := 0xf0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e
def pw147 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00
def pw148 : Nat := 0x1100110011001100110011001100110011001100110011001100110011001100
def pw149 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffffffffffeeffeeffffffffffeeffee
def pw150 : Nat := 0xfffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffe
def pw151 : Nat := 0xe0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e
def pw152 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00
def pw153 : Nat := 0x11001100000000001100110000000000110011000000000011001100
def pw154 : Nat := 0xfe00fe0000000000fe00fe0000000000fe00fe0000000000fe00fe00
def pw155 : Nat := 0xff00ff00fffefffeff00ff00fffefffeff00ff00fffefffeff00ff00fffefffe
def pw156 : Nat := 0xfefe000000000000fefe000000000000fefe000000000000fefe
def pw157 : Nat := 0xff00ff0001000100ff00ff0001000100ff00ff0001000100ff00ff0001000100
def pw158 : Nat := 0xffffffff0000eeeeffffffff0000eeeeffffffff0000eeeeffffffff0000eeee
def pw159 : Nat := 0xff00ff00ffeeffeeff00ff00ffeeffeeff00ff00ffeeffeeff00ff00ffeeffee
def pw160 : Nat := 0x1110111011101110111011101110111011101110111011101110111011101110
def pw161 : Nat := 0xf3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2
def pw162 : Nat := 0x33223322000000003322332200000000332233220000000033223322
def pw163 : Nat := 0xaaaaaaaaffeeffeeaaaaaaaaffeeffeeaaaaaaaaffeeffeeaaaaaaaaffeeffee
def pw164 : Nat := 0xbbbabbbabbbabbbabbbabbbabbbabbbabbbabbbabbbabbbabbbabbbabbbabbba
def p1_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p1_R : List Nat := [0, 1, 2]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
def p1_Z : List SliceD := []
theorem p1_Y : ∀ s ∈ p1_Z, SliceN true p1_R p1_T s := by intro s h; cases h
def p1_C : List (Nat × List Nat) := []
def p1_t : Tabs := ((p1_C.map (mkCut true p1_Z)).toArray, #[(6,4),(5,4),(3,1),(3,2),(6,2),(5,1)], [], #[[]])
theorem p1_W : TabsP true p1_R p1_T p1_t := ⟨cutsGood p1_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def p1_B0 : List (List StD) := []
def p1_N0 : Array (List Nat) := mkNext p1_B0
theorem p1_I0 : LevelB true p1_T 0 p1_B0 := by intro c hc; cases hc
def p1_B1 : List (List StD) := []
def p1_N1 : Array (List Nat) := mkNext p1_B1
theorem p1_I1 : LevelB true p1_T 1 p1_B1 := by intro c hc; cases hc
def p1_B2 : List (List StD) := []
def p1_N2 : Array (List Nat) := mkNext p1_B2
theorem p1_I2 : LevelB true p1_T 2 p1_B2 := by intro c hc; cases hc
def p1_D3_0 : List StD := [
([pw0,pw1,pw2],[1,5,9,13,17,21],[0xf,0x3a,0x35])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p1_C3x0 : levelOK true p1_T p1_t 2 p1_N2 p1_D3_0 = true := by decide +kernel
def p1_B3 : List (List StD) := [p1_D3_0]
def p1_N3 : Array (List Nat) := mkNext p1_B3
theorem p1_I3 : LevelB true p1_T 3 p1_B3 := levelStepB p1_B p1_W p1_I2 (by
  intro c hc
  unfold p1_B3 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p1_C3x0
  cases hc
  )
theorem p1_L : LowN true p1_R p1_T 4 := lowSearchB p1_B p1_I3 (by decide +kernel)
def p2_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8
def p2_R : List Nat := [0, 1, 2, 3]
def p2_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
def p2_Z : List SliceD := [(pw8,4,[0, 1, 2])]
theorem p2_Y : ∀ s ∈ p2_Z, SliceN true p2_R p2_T s := by
  unfold p2_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p2_B p1_B p1_L (by decide +kernel),by simp⟩
def p2_C : List (Nat × List Nat) := [(0,[])]
def p2_t : Tabs := ((p2_C.map (mkCut true p2_Z)).toArray, #[(6,4),(5,4),(3,1),(3,2),(6,2),(5,1),(9,1),(9,8),(14,12),(14,10)], [], #[[]])
theorem p2_W : TabsP true p2_R p2_T p2_t := ⟨cutsGood p2_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def p2_B0 : List (List StD) := []
def p2_N0 : Array (List Nat) := mkNext p2_B0
theorem p2_I0 : LevelB true p2_T 0 p2_B0 := by intro c hc; cases hc
def p2_B1 : List (List StD) := []
def p2_N1 : Array (List Nat) := mkNext p2_B1
theorem p2_I1 : LevelB true p2_T 1 p2_B1 := by intro c hc; cases hc
def p2_B2 : List (List StD) := []
def p2_N2 : Array (List Nat) := mkNext p2_B2
theorem p2_I2 : LevelB true p2_T 2 p2_B2 := by intro c hc; cases hc
def p2_B3 : List (List StD) := []
def p2_N3 : Array (List Nat) := mkNext p2_B3
theorem p2_I3 : LevelB true p2_T 3 p2_B3 := by intro c hc; cases hc
def p2_D4_0 : List StD := [
([pw0,pw1,pw2,pw3],[1,5,9,13,17,21,0,25,29,33,37],[0xf,0x3a,0x1c2,0x35,0x2c1,0x4d0])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p2_C4x0 : levelOK true p2_T p2_t 3 p2_N3 p2_D4_0 = true := by decide +kernel
def p2_B4 : List (List StD) := [p2_D4_0]
def p2_N4 : Array (List Nat) := mkNext p2_B4
theorem p2_I4 : LevelB true p2_T 4 p2_B4 := levelStepB p2_B p2_W p2_I3 (by
  intro c hc
  unfold p2_B4 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p2_C4x0
  cases hc
  )
theorem p2_L : LowN true p2_R p2_T 5 := lowSearchB p2_B p2_I4 (by decide +kernel)
def p3_T : Nat := 0xfeeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8
def p3_R : List Nat := [0, 1, 2, 3, 4]
def p3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw9,5,[0, 2, 3, 4]),(pw10,5,[0, 1, 4, 3]),(pw8,5,[0, 1, 4, 2]),(pw11,5,[0, 2, 3, 1]),(pw12,4,[0, 2, 3]),(pw13,4,[0, 1, 4])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p3_t : Tabs := ((p3_C.map (mkCut true p3_Z)).toArray, #[(18,16),(5,4),(3,1),(3,2),(12,8),(5,1),(12,4),(9,1),(9,8),(18,2),(17,1),(17,16),(14,10),(22,20),(14,6),(26,24),(22,6),(28,24),(26,10),(28,20),(5,6),(7,6),(11,10),(21,20),(25,24),(17,0),(12,10),(5,20),(9,24),(18,6),(9,10),(17,20)], [], #[[],[2],[1,3],[1,3,2],[2,1,3],[2,1,3,2],[3,2,1,2,3],[3,2,1,3,2,3]])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def p3_B0 : List (List StD) := []
def p3_N0 : Array (List Nat) := mkNext p3_B0
theorem p3_I0 : LevelB true p3_T 0 p3_B0 := by intro c hc; cases hc
def p3_B1 : List (List StD) := []
def p3_N1 : Array (List Nat) := mkNext p3_B1
theorem p3_I1 : LevelB true p3_T 1 p3_B1 := by intro c hc; cases hc
def p3_B2 : List (List StD) := []
def p3_N2 : Array (List Nat) := mkNext p3_B2
theorem p3_I2 : LevelB true p3_T 2 p3_B2 := by intro c hc; cases hc
def p3_B3 : List (List StD) := []
def p3_N3 : Array (List Nat) := mkNext p3_B3
theorem p3_I3 : LevelB true p3_T 3 p3_B3 := by intro c hc; cases hc
def p3_D4_0 : List StD := [
([pw14,pw0,pw1,pw2,pw3],[37,5,33,1,9,21,17,25,73,13,29,49,57],[0x7,0x18,0x61,0x181,0x1a,0x202,0x482,0x828,0x1088,0x4a0]),
([pw15,pw0,pw1,pw2,pw3],[33,13,5,1,9,17,21,25,29,37,49,57],[0x7,0x18,0x60,0x380,0x18,0x62,0x83,0x428,0x888,0x60]),
([pw0,pw1,pw2,pw3,pw16],[1,121,33,17,93,25,29,41,5,49,57,9,65,21,73,37],[0x7,0x1c,0x60,0x184,0x209,0x421,0x881,0x68,0x3008,0xc020])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C4x0 : levelOK true p3_T p3_t 3 p3_N3 p3_D4_0 = true := by decide +kernel
def p3_B4 : List (List StD) := [p3_D4_0]
def p3_N4 : Array (List Nat) := mkNext p3_B4
theorem p3_I4 : LevelB true p3_T 4 p3_B4 := levelStepB p3_B p3_W p3_I3 (by
  intro c hc
  unfold p3_B4 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p3_C4x0
  cases hc
  )
def p3_D5_0 : List StD := [
([pw17,pw0,pw1,pw2,pw3,pw18],[109,1,9,17,21,25,29,0,101,49,57,16,37],[0x1,0x6,0x18,0x60,0x80,0x6,0x18,0x60,0x100,0x20a,0x422,0x1802,0x18,0x18,0x60]),
([pw0,pw1,pw2,pw3,pw18,pw19],[1,9,45,93,69,25,29,5,113,41,53,57,16,65,117,17,4,37],[0x3,0x1c,0x60,0x80,0x304,0x401,0x821,0x3001,0x3,0x60,0x6010,0x8000,0x60,0x60,0x30200]),
([pw0,pw1,pw2,pw20,pw3,pw4],[5,9,13,33,29,25,41,37,49,21,1,57,17,65,8,11,12,3,73],[0x7,0x5,0x8,0x31,0xc1,0x302,0x400,0x822,0xc2,0x1000,0x230,0x2280,0xc020,0x30080,0x400a0]),
([pw21,pw0,pw1,pw2,pw3,pw4],[45,5,13,1,9,69,21,17,77,25,41,29,37,53,57,73],[0x7,0x18,0xe0,0x300,0x400,0x1a,0x43,0xa02,0x1003,0x2048,0x4208,0x18,0xa40,0x1060,0x9200]),
([pw22,pw0,pw1,pw23,pw2,pw3],[37,13,41,9,12,17,21,25,29,81,45,1,49,57],[0x7,0xd,0x10,0x60,0x180,0x20a,0x400,0x62,0x182,0x800,0x1028,0x2088,0x60,0x180,0x60]),
([pw22,pw0,pw1,pw2,pw3],[45,37,13,41,5,1,9,17,21,65,25,29,73,85,89,49,53,57,61],[0x1f,0x6a,0x382,0x1c02,0x65,0x2184,0x4c04,0x180a0,0x60420,0xd80]),
([pw0,pw1,pw24,pw2,pw3,pw4],[33,9,13,5,21,17,25,41,37,1,49,57,29,12,67,65,73],[0x7,0xd,0x34,0x45,0x184,0x200,0x422,0x842,0x182,0x30,0x1840,0x6100,0x30,0x8120,0x10140]),
([pw25,pw0,pw1,pw2,pw3,pw4],[5,1,9,17,21,29,41,25,33,45,37,49,57,65,73],[0x1,0x6,0x18,0x20,0x40,0x6,0x18,0x380,0x700,0x80a,0x1082,0x6,0x18,0x2408,0x4480]),
([pw26,pw0,pw1,pw2,pw3,pw4],[5,1,4,9,17,0,21,25,139,8,37,131,12,121,33,125,29,41,49,57,65,73],[0x1,0xe,0x70,0x380,0x1c00,0x6002,0xc010,0x10080,0x24400,0x40012,0x80082,0x20402,0x10090,0x100410,0x200480]),
([pw27,pw0,pw1,pw2,pw3,pw4],[5,9,53,1,21,49,17,29,25,41,37,33,57,65,73],[0x1,0xe,0x70,0x180,0x600,0x806,0x830,0x180,0xe00,0x32,0x1102,0x602,0x190,0x2410,0x4500])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C5x0 : levelOK true p3_T p3_t 4 p3_N4 p3_D5_0 = true := by decide +kernel
def p3_B5 : List (List StD) := [p3_D5_0]
def p3_N5 : Array (List Nat) := mkNext p3_B5
theorem p3_I5 : LevelB true p3_T 5 p3_B5 := levelStepB p3_B p3_W p3_I4 (by
  intro c hc
  unfold p3_B5 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p3_C5x0
  cases hc
  )
def p3_D6_0 : List StD := [
([pw0,pw1,pw23,pw2,pw3,pw4],[0,81,27,13,9,5,17,21,85,25,29,89,37,41,16,1,49,91,57,95,4,131,211,8,135,203,12,259,323,65,69,73,77],[0x1f,0x21,0x1c8,0xe08,0x7008,0x8005,0x30051,0xc0211,0x7011,0x7000c0,0x3800600,0x1c005000,0x6c0,0x60001040,0x180001200]),
([pw17,pw0,pw1,pw2,pw3,pw4],[12,5,1,0,9,16,17,4,21,395,455,25,8,29,403,451,3,41,45,93,97,37,101,49,53,57,61,65,69,73,77],[0x3,0x3c,0x7c0,0xf800,0x30001,0x40034,0xc0140,0x142800,0x650001,0x1800044,0x6000804,0x200035,0x2940,0x18200040,0x60200800]),
([pw0,pw1,pw2,pw28,pw3,pw4],[53,5,91,13,0,49,83,4,515,33,131,471,579,25,29,37,41,45,105,1,57,20,16,17,65,8,12,73,77],[0x1f,0xea,0x1f02,0x6202,0x38002,0x400b1,0x80090,0x302011,0x418011,0x800010,0x2060a0,0x14080a0,0x2206000,0x4418000,0x1800a000])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C6x0 : levelOK true p3_T p3_t 5 p3_N5 p3_D6_0 = true := by decide +kernel
def p3_B6 : List (List StD) := [p3_D6_0]
def p3_N6 : Array (List Nat) := mkNext p3_B6
theorem p3_I6 : LevelB true p3_T 6 p3_B6 := levelStepB p3_B p3_W p3_I5 (by
  intro c hc
  unfold p3_B6 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p3_C6x0
  cases hc
  )
def p3_D7_0 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[0,1,5,3,9,13,91,4,17,11,21,83,8,25,19,29,33,75,12,37,27,41,45,67,131,49,53,135,57,61,16,20,143,65,69,151,73,77],[0x7f,0xfa4,0x3f004,0xfc0004,0x7000183,0x38003003,0x402c0013,0x8000b580,0x7000c0180,0x38000c3000])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C7x0 : levelOK true p3_T p3_t 6 p3_N6 p3_D7_0 = true := by decide +kernel
def p3_B7 : List (List StD) := [p3_D7_0]
def p3_N7 : Array (List Nat) := mkNext p3_B7
theorem p3_I7 : LevelB true p3_T 7 p3_B7 := levelStepB p3_B p3_W p3_I6 (by
  intro c hc
  unfold p3_B7 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p3_C7x0
  cases hc
  )
theorem p3_L : LowN true p3_R p3_T 8 := lowSearchB p3_B p3_I7 (by decide +kernel)
def p4_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def p4_R : List Nat := [0, 1, 2, 3]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := [(pw29,4,[1, 2, 3]),(pw9,4,[0, 2, 3]),(pw10,4,[0, 1, 3]),(pw8,4,[0, 1, 2])]
theorem p4_Y : ∀ s ∈ p4_Z, SliceN true p4_R p4_T s := by
  unfold p4_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p4_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p4_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p4_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p4_B p1_B p1_L (by decide +kernel),by simp⟩
def p4_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[])]
def p4_t : Tabs := ((p4_C.map (mkCut true p4_Z)).toArray, #[(6,4),(5,4),(3,1),(3,2),(6,2),(5,1),(10,2),(9,1),(9,8),(10,8),(12,4),(12,8)], [], #[[]])
theorem p4_W : TabsP true p4_R p4_T p4_t := ⟨cutsGood p4_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def p4_B0 : List (List StD) := []
def p4_N0 : Array (List Nat) := mkNext p4_B0
theorem p4_I0 : LevelB true p4_T 0 p4_B0 := by intro c hc; cases hc
def p4_B1 : List (List StD) := []
def p4_N1 : Array (List Nat) := mkNext p4_B1
theorem p4_I1 : LevelB true p4_T 1 p4_B1 := by intro c hc; cases hc
def p4_B2 : List (List StD) := []
def p4_N2 : Array (List Nat) := mkNext p4_B2
theorem p4_I2 : LevelB true p4_T 2 p4_B2 := by intro c hc; cases hc
def p4_D3_0 : List StD := [
([pw23,pw30,pw28,pw3],[4,1,13,0,9,25,41,29],[0x7,0x1a,0x62,0x1c,0xa4,0xb0]),
([pw23,pw2,pw31,pw32],[33,17,45,4,13,5,0,9,1,21],[0x7,0x38,0x1c0,0x212,0x282,0xd0]),
([pw33,pw0,pw1,pw2],[25,5,29,1,17,41,9,13],[0x7,0xd,0x31,0x4a,0x82,0x48]),
([pw34,pw0,pw1,pw3],[5,13,1,9,17,25,41,29],[0x3,0xc,0x70,0xd,0xa1,0xa4]),
([pw1,pw30,pw31,pw35],[33,1,37,9,5,8,13,0,21,17],[0x7,0x1a,0xa,0x70,0x380,0x190]),
([pw36,pw0,pw2,pw3],[1,5,9,29,25,13,17,41],[0x7,0x5,0x19,0x22,0x1a,0xd0]),
([pw0,pw28,pw32,pw35],[33,5,1,13,8,9,4,17,21],[0x3,0xe,0xa,0x34,0x1c0,0xc4]),
([pw37,pw1,pw2,pw3],[5,1,9,13,25,29,17,41],[0x7,0x9,0x31,0x6,0x32,0xd0])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_C3x0 : levelOK true p4_T p4_t 2 p4_N2 p4_D3_0 = true := by decide +kernel
def p4_B3 : List (List StD) := [p4_D3_0]
def p4_N3 : Array (List Nat) := mkNext p4_B3
theorem p4_I3 : LevelB true p4_T 3 p4_B3 := levelStepB p4_B p4_W p4_I2 (by
  intro c hc
  unfold p4_B3 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p4_C3x0
  cases hc
  )
def p4_D4_0 : List StD := [
([pw1,pw23,pw2,pw30,pw3],[1,9,3,21,4,13,25,29,8,5,41,17],[0x1,0xe,0x32,0xc2,0x308,0x230,0x640,0x800,0x448,0xe0]),
([pw1,pw23,pw2,pw3,pw31],[1,9,17,21,67,29,4,13,33,45,12,5,25],[0x1,0xe,0x32,0xc2,0x304,0x520,0x8c0,0x224,0x8c,0x1000]),
([pw0,pw23,pw2,pw28,pw3],[5,13,3,17,0,9,29,25,8,1,41,21],[0x1,0xe,0x32,0xc2,0x308,0x230,0x680,0x800,0x488,0xe0]),
([pw0,pw23,pw2,pw3,pw32],[5,13,21,17,67,25,0,9,37,45,12,1,29],[0x1,0xe,0x32,0xc2,0x308,0x520,0x8c0,0x228,0x8c,0x1000]),
([pw0,pw1,pw2,pw20,pw3],[1,9,5,13,33,29,25,37,45,17,41,12,131],[0x7,0xc,0x10,0x64,0x3,0x80,0x61,0x100,0x640,0x1840]),
([pw38,pw0,pw1,pw2,pw3],[5,13,1,9,17,41,25,29],[0x3,0xc,0x10,0x60,0xd,0x3,0xc1,0xc,0xc4,0x60]),
([pw0,pw1,pw2,pw3,pw39],[33,9,13,21,17,29,25,5,1,45,8,195,41],[0x7,0x1c,0x64,0x80,0x1a,0x62,0x100,0x250,0xc10,0x1000]),
([pw40,pw0,pw1,pw2,pw3],[33,13,5,37,9,1,45,17,25,21,41],[0x7,0x38,0xc0,0x100,0x13,0x282,0x3,0x290,0x18,0x4c0]),
([pw1,pw2,pw30,pw3,pw31],[9,1,33,37,29,5,17,21,259,8,12,13,25],[0x3,0xe,0x1a,0x23,0x40,0x190,0x2a0,0x414,0xa20,0x1000]),
([pw0,pw1,pw30,pw28,pw3],[1,3,5,13,0,21,29,25,4,17,9],[0x7,0x8,0x34,0xc4,0x301,0x400,0xc1,0x230,0x2c0,0xe0]),
([pw41,pw0,pw1,pw2,pw3],[13,5,1,17,21,25,29,41],[0x3,0x4,0x18,0x60,0x3,0x3,0x62,0x18,0x60,0xa8]),
([pw0,pw1,pw30,pw3,pw35],[1,9,5,13,259,41,0,21,37,12,45,17,25],[0x7,0x8,0x34,0xc4,0x101,0x101,0x3,0x620,0x8c0,0x1000]),
([pw0,pw1,pw2,pw3,pw42],[1,9,5,33,21,29,13,37,4,323,41,17,25],[0x7,0x1c,0x2c,0x40,0x3,0xa1,0x301,0x430,0x800,0x1000]),
([pw43,pw0,pw1,pw2,pw3],[33,5,13,37,1,45,21,17,29,9,25],[0x7,0x18,0xe0,0x100,0x212,0x43,0x403,0x210,0x418,0x460]),
([pw0,pw1,pw2,pw31,pw32],[33,67,37,17,21,5,0,29,4,25,1],[0x7,0x18,0x20,0xc1,0x18,0x304,0x400,0x18,0x18,0x2c0]),
([pw44,pw0,pw1,pw2,pw3],[13,33,5,9,17,21,25,29,1,45],[0x7,0x8,0x30,0xc0,0x103,0x31,0xc1,0x130,0x1c0,0x250]),
([pw0,pw1,pw2,pw31,pw35],[1,9,33,259,45,5,0,29,8,41,17,25],[0x3,0x1c,0x20,0xc4,0x3,0x3,0x3,0x310,0x400,0x8c0]),
([pw45,pw0,pw1,pw2,pw3],[5,33,13,1,9,21,41,29,25,17,37],[0x7,0x18,0x20,0x1c0,0x19,0x203,0x83,0x18,0x488,0x2c0]),
([pw27,pw0,pw1,pw2,pw3],[5,9,1,21,17,29,25,41],[0x1,0x6,0x18,0x60,0x6,0x18,0x60,0x6,0x64,0xd0]),
([pw0,pw2,pw28,pw3,pw32],[13,5,33,25,1,21,17,387,8,12,37,9,29],[0x3,0x6,0xe,0x13,0x20,0xc8,0x150,0x608,0x910,0x1000]),
([pw0,pw1,pw28,pw3,pw35],[1,13,5,33,9,387,41,4,17,12,45,21,25],[0x7,0xc,0xc,0x6,0x10,0x61,0x181,0x640,0x980,0x1000]),
([pw0,pw1,pw2,pw3,pw46],[1,13,5,33,25,0,451,37,17,9,41,21,29],[0x7,0x6,0x1c,0x64,0x181,0x91,0x200,0x510,0x800,0x1000]),
([pw47,pw0,pw1,pw2,pw3],[33,5,37,1,9,45,17,21,25,13,29],[0x3,0x1c,0xe0,0x100,0x20a,0x202,0x403,0x4c,0x40c,0x460]),
([pw48,pw0,pw1,pw2,pw3],[13,9,37,1,21,17,29,25,5,45],[0x1,0xe,0x30,0xc0,0x106,0x130,0x1c0,0x32,0xc2,0x2a0]),
([pw0,pw1,pw2,pw32,pw35],[5,13,37,387,45,1,4,25,8,41,17,29],[0x3,0x3,0x3,0x3,0x1c,0x20,0xc4,0x310,0x400,0x8c0]),
([pw49,pw0,pw1,pw2,pw3],[5,13,1,37,9,17,41,25,29,33,21],[0x3,0x1c,0x20,0x1c0,0x7,0x3,0x281,0x40c,0x8c,0x4c0]),
([pw50,pw0,pw1,pw2,pw3],[5,9,1,21,45,17,29,41,25,13,37],[0x1,0x6,0x38,0x1c0,0x6,0x218,0x2c0,0x6,0x444,0xc8]),
([pw51,pw0,pw1,pw2,pw3],[13,5,1,17,45,21,25,41,29,9,33],[0x3,0x4,0x38,0x1c0,0x203,0x3,0x442,0x218,0x2c0,0xc8])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_C4x0 : levelOK true p4_T p4_t 3 p4_N3 p4_D4_0 = true := by decide +kernel
def p4_B4 : List (List StD) := [p4_D4_0]
def p4_N4 : Array (List Nat) := mkNext p4_B4
theorem p4_I4 : LevelB true p4_T 4 p4_B4 := levelStepB p4_B p4_W p4_I3 (by
  intro c hc
  unfold p4_B4 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p4_C4x0
  cases hc
  )
def p4_D5_0 : List StD := [
([pw0,pw1,pw23,pw2,pw3],[0,13,9,4,5,17,21,3,25,29,67,1,131,195,45,8,259,323,41,12,387,451],[0xf,0x19,0xe3,0x703,0x801,0x106c,0x230c,0x3c020,0x3c0100,0x44120]),
([pw0,pw1,pw2,pw30,pw3],[1,5,9,3,0,21,8,13,25,29,515,579,4,37,259,643,17,41,707,12,771,835],[0x1f,0x72,0xd0,0x712,0x865,0xf001,0x2301,0x10010,0x60160,0x380300]),
([pw0,pw1,pw2,pw3,pw31],[1,33,9,67,0,17,21,515,29,12,5,899,37,4,387,963,1027,45,8,771,1091,25],[0x1f,0xf2,0x312,0x610,0x65,0x1b01,0xe005,0x30320,0x1c0060,0x200010]),
([pw0,pw1,pw2,pw28,pw3],[1,5,131,13,4,17,579,8,0,33,259,1155,25,29,9,1219,21,41,1283,12,1347,1411],[0x1f,0xea,0xf02,0x3202,0xb1,0x4090,0xb011,0x10010,0x610a0,0x383000]),
([pw0,pw1,pw2,pw3,pw32],[37,5,195,13,4,17,21,25,899,33,12,0,387,1475,1219,1,1539,45,8,1347,1603,29],[0x1f,0x6a,0x782,0x380a,0x4071,0x491,0x8410,0x304a0,0x1c0060,0x200010]),
([pw0,pw1,pw2,pw3,pw35],[1,5,9,13,45,707,8,41,1027,33,12,0,771,1667,1283,1539,37,4,1347,1731,17,25],[0xf,0x7a,0x782,0x380a,0x4055,0x18481,0xe0005,0x4d0,0x100440,0x200040])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_C5x0 : levelOK true p4_T p4_t 4 p4_N4 p4_D5_0 = true := by decide +kernel
def p4_B5 : List (List StD) := [p4_D5_0]
def p4_N5 : Array (List Nat) := mkNext p4_B5
theorem p4_I5 : LevelB true p4_T 5 p4_B5 := levelStepB p4_B p4_W p4_I4 (by
  intro c hc
  unfold p4_B5 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p4_C5x0
  cases hc
  )
def p4_D6_0 : List StD := [
([pw0,pw1,pw2,pw3],[0,1,5,3,9,13,4,17,67,21,8,25,131,29,33,12,195,259,37,323,41,45],[0x7f,0x7a5,0xf805,0x106d2,0x6a842,0x388c80])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_C6x0 : levelOK true p4_T p4_t 5 p4_N5 p4_D6_0 = true := by decide +kernel
def p4_B6 : List (List StD) := [p4_D6_0]
def p4_N6 : Array (List Nat) := mkNext p4_B6
theorem p4_I6 : LevelB true p4_T 6 p4_B6 := levelStepB p4_B p4_W p4_I5 (by
  intro c hc
  unfold p4_B6 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p4_C6x0
  cases hc
  )
theorem p4_L : LowN true p4_R p4_T 7 := lowSearchB p4_B p4_I6 (by decide +kernel)
def p5_T : Nat := 0xfeeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8
def p5_R : List Nat := [0, 1, 2, 3, 4]
def p5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := [(pw11,7,[0, 1, 2, 3])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel),by simp⟩
def p5_C : List (Nat × List Nat) := [(0,[])]
def p5_t : Tabs := ((p5_C.map (mkCut true p5_Z)).toArray, #[(6,4),(5,4),(3,1),(3,2),(6,2),(5,1),(10,2),(9,1),(9,8),(18,2),(17,1),(17,16),(10,8),(18,16),(12,4),(12,8),(28,24),(28,20)], [], #[[],[2],[0],[0,2]])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def p5_B0 : List (List StD) := []
def p5_N0 : Array (List Nat) := mkNext p5_B0
theorem p5_I0 : LevelB true p5_T 0 p5_B0 := by intro c hc; cases hc
def p5_B1 : List (List StD) := []
def p5_N1 : Array (List Nat) := mkNext p5_B1
theorem p5_I1 : LevelB true p5_T 1 p5_B1 := by intro c hc; cases hc
def p5_B2 : List (List StD) := []
def p5_N2 : Array (List Nat) := mkNext p5_B2
theorem p5_I2 : LevelB true p5_T 2 p5_B2 := by intro c hc; cases hc
def p5_B3 : List (List StD) := []
def p5_N3 : Array (List Nat) := mkNext p5_B3
theorem p5_I3 : LevelB true p5_T 3 p5_B3 := by intro c hc; cases hc
def p5_B4 : List (List StD) := []
def p5_N4 : Array (List Nat) := mkNext p5_B4
theorem p5_I4 : LevelB true p5_T 4 p5_B4 := by intro c hc; cases hc
def p5_B5 : List (List StD) := []
def p5_N5 : Array (List Nat) := mkNext p5_B5
theorem p5_I5 : LevelB true p5_T 5 p5_B5 := by intro c hc; cases hc
def p5_B6 : List (List StD) := []
def p5_N6 : Array (List Nat) := mkNext p5_B6
theorem p5_I6 : LevelB true p5_T 6 p5_B6 := by intro c hc; cases hc
def p5_D7_0 : List StD := [
([pw0,pw1,pw2,pw3,pw4],[0,1,5,9,13,17,21,25,29,33,37,41,45,49,53,57,61,65,69],[0x1f,0x75,0x385,0x1c05,0x6b,0x2183,0x4c03,0x180a1,0x20421,0x40481])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C7x0 : levelOK true p5_T p5_t 6 p5_N6 p5_D7_0 = true := by decide +kernel
def p5_B7 : List (List StD) := [p5_D7_0]
def p5_N7 : Array (List Nat) := mkNext p5_B7
theorem p5_I7 : LevelB true p5_T 7 p5_B7 := levelStepB p5_B p5_W p5_I6 (by
  intro c hc
  unfold p5_B7 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p5_C7x0
  cases hc
  )
theorem p5_L : LowN true p5_R p5_T 8 := lowSearchB p5_B p5_I7 (by decide +kernel)
def p6_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8
def p6_R : List Nat := [0, 1, 2, 3]
def p6_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
def p6_Z : List SliceD := [(pw10,4,[0, 1, 3])]
theorem p6_Y : ∀ s ∈ p6_Z, SliceN true p6_R p6_T s := by
  unfold p6_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p6_B p1_B p1_L (by decide +kernel),by simp⟩
def p6_C : List (Nat × List Nat) := [(0,[])]
def p6_t : Tabs := ((p6_C.map (mkCut true p6_Z)).toArray, #[(6,4),(5,4),(3,1),(3,2),(6,2),(5,1),(10,2),(9,1),(9,8),(10,8)], [], #[[]])
theorem p6_W : TabsP true p6_R p6_T p6_t := ⟨cutsGood p6_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def p6_B0 : List (List StD) := []
def p6_N0 : Array (List Nat) := mkNext p6_B0
theorem p6_I0 : LevelB true p6_T 0 p6_B0 := by intro c hc; cases hc
def p6_B1 : List (List StD) := []
def p6_N1 : Array (List Nat) := mkNext p6_B1
theorem p6_I1 : LevelB true p6_T 1 p6_B1 := by intro c hc; cases hc
def p6_B2 : List (List StD) := []
def p6_N2 : Array (List Nat) := mkNext p6_B2
theorem p6_I2 : LevelB true p6_T 2 p6_B2 := by intro c hc; cases hc
def p6_B3 : List (List StD) := []
def p6_N3 : Array (List Nat) := mkNext p6_B3
theorem p6_I3 : LevelB true p6_T 3 p6_B3 := by intro c hc; cases hc
def p6_D4_0 : List StD := [
([pw0,pw1,pw2,pw3],[1,5,9,13,17,21,25,29,33,37,0],[0xf,0x3a,0x1c2,0x35,0x2c1,0x450])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_C4x0 : levelOK true p6_T p6_t 3 p6_N3 p6_D4_0 = true := by decide +kernel
def p6_B4 : List (List StD) := [p6_D4_0]
def p6_N4 : Array (List Nat) := mkNext p6_B4
theorem p6_I4 : LevelB true p6_T 4 p6_B4 := levelStepB p6_B p6_W p6_I3 (by
  intro c hc
  unfold p6_B4 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p6_C4x0
  cases hc
  )
theorem p6_L : LowN true p6_R p6_T 5 := lowSearchB p6_B p6_I4 (by decide +kernel)
def p7_T : Nat := 0xfffefefeffeeeee8fffefefeffeeeee8fffefefeffeeeee8fffefefeffeeeee8
def p7_R : List Nat := [0, 1, 2, 3, 4, 5]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17),(5,1,33)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw9,8,[0, 2, 3, 4, 5]),(pw29,8,[1, 2, 3, 4, 5]),(pw10,8,[0, 1, 3, 4, 5]),(pw8,8,[0, 1, 2, 5, 4]),(pw11,8,[0, 1, 2, 5, 3]),(pw52,8,[0, 1, 3, 4, 2]),(pw53,7,[0, 1, 3, 4]),(pw54,7,[0, 1, 2, 5]),(pw55,5,[1, 3, 4, 5]),(pw13,5,[0, 1, 4, 5]),(pw56,5,[0, 3, 4, 5]),(pw57,4,[1, 3, 4]),(pw58,4,[0, 3, 4]),(pw59,5,[0, 2, 5, 4]),(pw12,5,[0, 2, 5, 3]),(pw60,5,[0, 3, 4, 2]),(pw61,5,[1, 3, 4, 2]),(pw62,5,[1, 2, 5, 4]),(pw63,5,[0, 1, 3, 5]),(pw64,5,[0, 1, 2, 4]),(pw65,4,[1, 2, 5]),(pw66,4,[0, 1, 2]),(pw67,4,[0, 1, 5]),(pw68,4,[0, 1, 4]),(pw69,5,[0, 1, 2, 3]),(pw70,5,[1, 2, 5, 3]),(pw71,4,[0, 2, 5])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(2,[129]),(3,[129]),(4,[129]),(5,[129]),(6,[129]),(7,[129]),(8,[]),(0,[129]),(3,[257]),(4,[257]),(7,[257]),(0,[261]),(1,[261]),(9,[]),(10,[]),(1,[129]),(11,[]),(12,[]),(3,[261,129]),(4,[261,129]),(7,[129,261]),(3,[129,277]),(4,[129,277]),(13,[]),(14,[]),(15,[]),(7,[129,273]),(16,[]),(0,[514]),(1,[514]),(3,[129,406]),(4,[129,406]),(7,[129,402]),(17,[]),(0,[513]),(1,[513]),(3,[385,389]),(7,[385,389]),(1,[130]),(18,[]),(3,[257,150]),(7,[257,146]),(1,[257]),(6,[261]),(19,[]),(1,[521]),(20,[]),(21,[]),(3,[385]),(7,[385]),(0,[521,513]),(0,[129,277]),(22,[]),(23,[]),(2,[257]),(6,[257]),(2,[261,129]),(3,[257,129]),(7,[129,257]),(6,[129,261]),(1,[514,513]),(1,[513,521]),(3,[129,389]),(7,[129,389]),(1,[129,277]),(6,[129,257]),(0,[257,534]),(5,[129,277]),(3,[129,405]),(0,[261,22]),(1,[261,22]),(0,[129,534]),(1,[129,534]),(7,[129,401]),(6,[129,273]),(1,[257,534]),(0,[386,149]),(2,[129,406]),(24,[]),(0,[386,534]),(5,[129,406]),(1,[386,149]),(6,[129,402]),(1,[386,534]),(0,[261,20]),(0,[130,278]),(3,[129,278]),(2,[129,278]),(5,[129,405]),(1,[257,533]),(6,[261,257]),(1,[258,534]),(2,[261,22]),(1,[257,150]),(6,[257,146]),(0,[129,261]),(1,[513,525]),(0,[385,525]),(7,[389]),(6,[385]),(25,[]),(0,[257,533]),(0,[261,257]),(26,[]),(0,[129,405]),(1,[129,405]),(6,[129,385]),(6,[129,389]),(6,[129,401]),(6,[129,274])]
def p7_t : Tabs := ((p7_C.map (mkCut true p7_Z)).toArray, #[(6,4),(5,4),(3,1),(3,2),(6,2),(5,1),(10,2),(9,1),(9,8),(18,2),(17,1),(17,16),(34,2),(33,1),(33,32),(10,8),(18,16),(34,32),(28,20),(44,40),(28,12),(52,48),(36,4),(44,12),(56,48),(52,20),(56,40),(9,12),(13,12),(21,20),(24,20),(10,12),(14,12),(22,20),(41,40),(49,48),(42,40),(50,48),(9,40),(10,40),(6,12),(17,48),(36,12),(34,40),(42,8),(18,48),(33,0),(36,20),(5,12),(34,48),(33,40),(3,20),(33,48),(6,20),(5,20),(35,16),(7,16),(36,0),(11,1),(18,1),(3,32),(37,0),(38,0),(44,4),(7,4),(36,8),(10,0),(34,0),(3,0),(6,0),(49,1),(17,20),(24,0)], [], #[[],[3],[2,4],[2,4,3],[3,2,4],[3,2,4,3],[4,3,2,3,4],[4,3,2,4,3,4],[0],[0,3],[0,2,4],[0,2,4,3],[0,3,2,4],[0,3,2,4,3],[0,4,3,2,3,4],[0,4,3,2,4,3,4]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def p7_B0 : List (List StD) := []
def p7_N0 : Array (List Nat) := mkNext p7_B0
theorem p7_I0 : LevelB true p7_T 0 p7_B0 := by intro c hc; cases hc
def p7_B1 : List (List StD) := []
def p7_N1 : Array (List Nat) := mkNext p7_B1
theorem p7_I1 : LevelB true p7_T 1 p7_B1 := by intro c hc; cases hc
def p7_B2 : List (List StD) := []
def p7_N2 : Array (List Nat) := mkNext p7_B2
theorem p7_I2 : LevelB true p7_T 2 p7_B2 := by intro c hc; cases hc
def p7_B3 : List (List StD) := []
def p7_N3 : Array (List Nat) := mkNext p7_B3
theorem p7_I3 : LevelB true p7_T 3 p7_B3 := by intro c hc; cases hc
def p7_D4_0 : List StD := [
([pw2,pw72,pw73,pw74,pw75],[57,17,73,77,25,13,21,9,5,1,29,128],[0x7,0x1a,0x62,0xc2,0x15,0x124,0x284,0x430,0x490,0x8a0]),
([pw23,pw2,pw31,pw76,pw75],[77,17,73,13,5,81,29,33,89,9,1,21,25,37],[0x3,0x1c,0xe0,0x700,0x80a,0x62,0xa02,0x1048,0x20c,0x2240]),
([pw0,pw2,pw77,pw78,pw75],[13,21,17,29,25,5,89,9,73,77,220,69,81,1],[0x7,0x19,0x20,0xc1,0x114,0x204,0x86,0xc10,0x98,0x3080]),
([pw0,pw2,pw32,pw76,pw79],[13,21,17,73,9,41,25,5,81,244,89,29,1,61],[0x7,0x19,0x61,0x80,0x16,0x144,0x604,0x850,0x1018,0x2140]),
([pw80,pw0,pw1,pw2,pw81],[37,5,41,1,17,77,25,97,9,13,29,73],[0x7,0xd,0x31,0xc1,0x10a,0x202,0x442,0x108,0x448,0x850]),
([pw82,pw23,pw2,pw3,pw4],[57,1,9,17,77,25,93,37,101,33,81,73],[0x7,0x1c,0x64,0x184,0x20a,0x222,0x482,0x828,0x488,0x8a0]),
([pw83,pw23,pw84,pw3,pw4],[57,1,45,49,9,77,25,93,37,101,33,81,73],[0x7,0x38,0xc8,0x308,0x412,0x442,0x902,0x1050,0x910,0x1140]),
([pw83,pw23,pw2,pw85,pw4],[57,1,45,49,17,77,9,93,37,101,33,81,73],[0x7,0x38,0xc8,0x308,0x412,0x442,0x902,0x1050,0x910,0x1140]),
([pw83,pw23,pw2,pw3,pw86],[57,1,45,49,17,77,25,93,9,101,33,81,73],[0x7,0x38,0xc8,0x308,0x412,0x442,0x902,0x1050,0x910,0x1140]),
([pw87,pw0,pw2,pw88,pw73],[49,5,33,17,77,53,1,25,93,13,9,29],[0x7,0x19,0x61,0x181,0x202,0x442,0x882,0x440,0x98,0x8c0]),
([pw89,pw23,pw2,pw3,pw4],[45,1,9,17,77,25,93,37,101,73,81,85],[0x7,0x1c,0x64,0x184,0xb,0x222,0x3,0x228,0xc08,0x220]),
([pw80,pw23,pw84,pw3,pw4],[45,1,33,49,9,77,25,93,37,101,73,81,85],[0x7,0x38,0xc8,0x308,0x13,0x442,0x3,0x450,0x1810,0x440]),
([pw80,pw23,pw2,pw85,pw4],[45,1,33,49,17,77,9,93,37,101,73,81,85],[0x7,0x38,0xc8,0x308,0x13,0x442,0x3,0x450,0x1810,0x440]),
([pw80,pw23,pw2,pw3,pw86],[45,1,33,49,17,77,25,93,37,9,101,73,81],[0x7,0x38,0xc8,0x700,0x13,0x842,0x203,0x850,0x1210,0xa40]),
([pw80,pw0,pw2,pw3,pw88],[37,5,33,17,77,25,93,41,1,13,29,9],[0x7,0x19,0x61,0x181,0x202,0x422,0x902,0x38,0x900,0x520]),
([pw23,pw2,pw85,pw90,pw5],[45,117,77,9,73,57,37,1,49,81,17,89,25,93,101],[0x7,0x19,0xe0,0x121,0x18,0x640,0x904,0x1018,0x2108,0x4140]),
([pw23,pw2,pw3,pw86,pw91],[33,109,77,57,25,9,81,49,1,73,17,93,101,37],[0x7,0x19,0x61,0x181,0x210,0x64,0x484,0x230,0x890,0x3020]),
([pw23,pw2,pw3,pw86,pw92],[45,205,77,137,73,57,9,49,1,85,81,17,93,25,101],[0x7,0x19,0x61,0x181,0x214,0x444,0x884,0x450,0x3080,0x40c0]),
([pw23,pw2,pw3,pw4,pw93],[45,285,77,137,73,57,37,9,1,85,81,17,93,25,101],[0x7,0x19,0x61,0x181,0x214,0x444,0x884,0x450,0x3080,0x40c0])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK true p7_T p7_t 3 p7_N3 p7_D4_0 = true := by decide +kernel
def p7_B4 : List (List StD) := [p7_D4_0]
def p7_N4 : Array (List Nat) := mkNext p7_B4
theorem p7_I4 : LevelB true p7_T 4 p7_B4 := levelStepB p7_B p7_W p7_I3 (by
  intro c hc
  unfold p7_B4 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p7_C4x0
  cases hc
  )
def p7_D5_0 : List StD := [
([pw23,pw2,pw31,pw32,pw94,pw5],[33,109,77,173,13,201,9,37,81,49,89,85,17,88,41,53,101],[0x7,0x19,0x61,0x181,0x601,0x814,0x844,0x1180,0x604,0x2050,0x4090,0x8210,0x40c0,0x8240,0x10280]),
([pw23,pw2,pw3,pw18,pw95,pw96],[45,205,77,25,73,197,13,33,209,9,49,89,85,17,29,93,88,53],[0x7,0x19,0xe0,0x301,0xc01,0x18,0x1044,0x1204,0x2404,0x4048,0x4208,0x8408,0x10240,0x20440,0x20600]),
([pw97,pw23,pw3,pw18,pw95,pw5],[45,17,77,73,25,13,21,9,49,197,5,209,1,89,29,93,132,53],[0x7,0x1a,0x62,0xc2,0x106,0x19,0x620,0x1880,0x2101,0x4030,0x4090,0x8110,0x100a0,0x20120,0x20180]),
([pw23,pw98,pw3,pw18,pw95,pw5],[45,17,77,25,73,197,13,33,209,9,49,141,21,29,97,88,53],[0x7,0x19,0xe0,0x301,0xc01,0xe,0x1042,0x1202,0x406,0x2048,0x2208,0x4408,0x8240,0x10440,0x10600]),
([pw87,pw23,pw2,pw3,pw18,pw95],[89,49,45,17,77,25,93,13,53,9,73,197,5,209,1,21,29,100],[0x7,0x1a,0x62,0x182,0x302,0x18,0x420,0x1880,0x6200,0x428,0x8088,0x8208,0x100a0,0x10220,0x20280]),
([pw2,pw99,pw3,pw18,pw95,pw5],[45,17,77,73,25,13,21,9,11,49,197,5,209,1,89,29,97,132,53],[0x7,0x1a,0x62,0xc2,0x302,0x19,0xc20,0x3080,0x4201,0x8030,0x8090,0x10210,0x200a0,0x40220,0x40280]),
([pw100,pw2,pw3,pw4,pw74,pw75],[57,17,77,25,73,37,81,157,13,5,153,9,1,21,29,41,128],[0x7,0x19,0x61,0x380,0x1c00,0x1a,0x62,0x2102,0x2802,0x38,0x4108,0x4808,0x8120,0x8820,0x10900]),
([pw23,pw2,pw31,pw32,pw101,pw5],[33,17,85,161,13,5,193,9,1,37,81,49,101,21,132,41,53],[0x7,0x38,0x1c0,0x601,0x1801,0x2012,0x2082,0x602,0x806,0x4090,0x8210,0x10810,0x8280,0x10880,0x1a00]),
([pw23,pw2,pw3,pw4,pw74,pw102],[57,17,77,25,97,37,105,157,13,5,153,9,1,85,21,29,41,4],[0x7,0x19,0x61,0x380,0x1c00,0xe,0x2022,0x4102,0x4802,0x38,0x8108,0x8808,0x10120,0x10820,0x20900]),
([pw23,pw103,pw3,pw18,pw95,pw104],[45,11,77,25,73,197,13,5,209,9,1,17,117,85,229,29,132,21],[0x7,0x19,0xe0,0x700,0x1801,0x200c,0x2044,0x2204,0x4000,0x8048,0x8208,0x818,0x10240,0x20840,0x20a00]),
([pw23,pw2,pw3,pw4,pw74,pw105],[57,17,77,25,61,37,65,13,5,4,9,1,73,81,21,93,29,101,41],[0x7,0x19,0x61,0x190,0xe00,0x100a,0x2022,0x4082,0x4402,0x1028,0x8088,0x10000,0x200a0,0x40000,0x680]),
([pw23,pw2,pw3,pw4,pw74,pw106],[57,17,77,25,61,37,105,13,5,165,9,1,73,85,21,93,29,41,4],[0x7,0x19,0x61,0x190,0xe00,0x100a,0x2022,0x4082,0x4402,0x1028,0x8088,0x10408,0x200a0,0x20420,0x40480]),
([pw23,pw2,pw3,pw4,pw107,pw108],[33,17,77,57,29,37,65,13,5,9,1,85,21,97,25,93,101,41,128],[0x7,0x19,0x61,0x1c0,0x601,0x16,0x822,0x1082,0x1202,0x2030,0x4000,0x8210,0x100a0,0x20000,0x40280]),
([pw109,pw23,pw2,pw46,pw4,pw5],[1,13,5,73,17,97,9,41,37,53,33,57,81,49,21,77,101],[0x7,0x1a,0x62,0x182,0x200,0x411,0x841,0x1101,0x2801,0x4000,0x1110,0xa010,0x1c0,0x2060,0x12100]),
([pw110,pw23,pw2,pw32,pw4,pw5],[57,5,13,21,17,97,9,41,37,53,33,1,81,49,73,77,105],[0x7,0x1c,0x64,0x184,0x200,0x40a,0x842,0x1102,0x2003,0x4048,0x1108,0xa008,0x1c0,0x2060,0x12100]),
([pw23,pw2,pw111,pw18,pw95,pw5],[45,17,77,25,73,197,13,5,209,9,49,89,21,85,29,88,53],[0x7,0x19,0xe0,0x301,0xc01,0x1012,0x2042,0x206,0x406,0x4048,0x4208,0xc08,0x8240,0x10440,0x10600]),
([pw23,pw2,pw112,pw32,pw4,pw5],[33,5,21,57,13,9,1,37,81,49,17,73,89,97,41,53,101],[0x7,0x1a,0x62,0x182,0x20a,0x400,0x824,0x184,0x1204,0x2030,0x4090,0x8210,0x40a0,0x1220,0x10280]),
([pw109,pw49,pw23,pw2,pw4,pw5],[73,9,13,1,5,21,41,37,53,33,17,49,89,81,57,85,101],[0x7,0x1c,0x25,0xc4,0x100,0x20a,0x400,0xc2,0x1802,0x228,0x2088,0x4808,0x20a0,0x8820,0x10880]),
([pw113,pw23,pw2,pw3,pw18,pw75],[157,41,17,77,25,73,37,13,9,49,45,69,65,21,29,81],[0x1,0xe,0x32,0xc2,0x302,0x40c,0x430,0xc80,0x1500,0x34,0x2084,0x2104,0x4090,0x4110,0x8180]),
([pw114,pw23,pw30,pw32,pw4,pw5],[5,13,21,17,9,25,123,37,83,49,77,45,73,65,81,89,85,41,53,101],[0x1,0xe,0x34,0xc4,0x304,0xc02,0x3010,0x4080,0x8200,0x10012,0x20082,0x40202,0x20090,0x40210,0x80280]),
([pw80,pw0,pw23,pw2,pw3,pw95],[37,13,53,65,89,17,77,25,93,41,9,5,21,29,81,73,1],[0x7,0x19,0x61,0x181,0x601,0x800,0x1022,0x2082,0x4402,0x68,0x8088,0x14400,0x80a0,0x1420,0x2480]),
([pw0,pw114,pw28,pw39,pw4,pw5],[13,29,17,77,9,45,41,37,53,49,21,1,159,211,85,65,240,73,89,101],[0x7,0x19,0x20,0xc1,0x301,0x414,0x800,0x1084,0x2204,0xc010,0xd0,0x310,0x30080,0x60200,0x80280]),
([pw0,pw23,pw2,pw32,pw90,pw5],[45,13,123,77,73,9,41,25,53,49,219,173,65,81,61,89,17,29,101],[0x1,0xe,0x32,0xc2,0x302,0xc08,0x1030,0x6080,0x8200,0x30,0x12080,0x8208,0x200a0,0x320,0x40280]),
([pw0,pw23,pw2,pw3,pw95,pw91],[33,13,75,77,29,25,81,9,53,37,143,149,73,61,89,65,17,93,41],[0x1,0xe,0x32,0xc2,0x302,0xc08,0x1020,0x20c0,0xc200,0x1020,0xc8,0x10208,0xb0,0x20220,0x40280]),
([pw80,pw0,pw1,pw2,pw3,pw78],[37,13,41,9,17,77,25,93,89,81,45,21,29,5,1,73,259],[0x7,0xd,0x31,0xc1,0x301,0x40a,0x812,0x1042,0x2000,0x818,0x1048,0x4000,0x8050,0x30,0x10240]),
([pw87,pw0,pw1,pw2,pw81,pw4],[49,5,45,53,1,17,77,25,97,37,101,9,13,29,41,73,85],[0x7,0x19,0x61,0x181,0x601,0x812,0x1002,0x2082,0x4202,0x810,0x2090,0x4210,0x80a0,0x10220,0x8280]),
([pw87,pw115,pw0,pw1,pw2,pw3],[89,37,49,13,33,53,9,17,77,25,93,5,41,1,81,73,113,21,29],[0x7,0x1c,0x64,0x184,0x604,0x80a,0x3040,0x4082,0x8202,0x10048,0x20088,0x40208,0x200c0,0x40240,0x8280]),
([pw0,pw1,pw2,pw116,pw78,pw5],[197,9,13,187,77,29,25,33,53,49,155,61,73,17,81,85,89,240,93],[0x7,0x1c,0x64,0x80,0x304,0x412,0x62,0x800,0x302,0x3040,0xc010,0x10210,0x24040,0x40240,0x14200]),
([pw0,pw1,pw2,pw3,pw76,pw79],[141,9,13,21,17,227,73,41,37,5,195,1,77,81,244,89,25,93],[0x7,0x1c,0x64,0x184,0x200,0x1a,0x442,0x182,0x800,0x1050,0x2110,0xc010,0x10140,0x28040,0x2100]),
([pw83,pw117,pw23,pw2,pw3,pw4],[49,9,323,57,1,45,17,77,25,93,37,101,257,387,451,515,33,81,73],[0x7,0x38,0xc1,0x301,0xc01,0x1000,0x2042,0x4102,0x8402,0x10050,0x10110,0x20410,0x40140,0x20440,0x40500]),
([pw87,pw0,pw1,pw118,pw3,pw4],[49,5,45,53,1,17,77,73,93,37,101,9,13,109,41,125,25,81],[0x7,0x19,0x61,0x181,0x601,0x812,0x1002,0x2082,0x4202,0x810,0x8090,0x4210,0x100a0,0x20220,0x20280]),
([pw87,pw0,pw1,pw2,pw3,pw119],[49,5,45,53,1,17,77,73,93,37,101,9,13,193,41,161,81,25],[0x7,0x19,0x61,0x181,0x601,0x812,0x1002,0x2082,0x4202,0x810,0x8090,0x4210,0xe0,0x10220,0x20280]),
([pw87,pw120,pw0,pw1,pw2,pw4],[49,25,93,5,33,53,1,17,77,37,101,29,73,9,13,41,81],[0x7,0x19,0x61,0x181,0x601,0x80a,0x842,0x1082,0x1202,0x2048,0x4008,0x8208,0x2040,0x8240,0x10280]),
([pw87,pw0,pw1,pw2,pw121,pw4],[49,5,45,53,1,17,85,25,93,37,101,9,13,29,41,73,81],[0x7,0x19,0x61,0x181,0x601,0x812,0x1002,0x2082,0x4202,0x810,0x2090,0x4210,0x80a0,0x10220,0x8280]),
([pw87,pw122,pw0,pw1,pw2,pw3],[101,37,49,5,33,53,1,17,77,25,93,41,81,73,9,13,29],[0x7,0x1c,0x64,0x184,0x604,0x80a,0x842,0x1082,0x2202,0x4048,0x8008,0x10208,0x4040,0x10240,0x2280]),
([pw83,pw0,pw1,pw2,pw3,pw123],[49,5,53,1,17,77,25,93,37,105,9,13,29,41,81],[0x7,0xd,0x31,0xc1,0x301,0x40a,0x802,0x1042,0x2102,0x408,0x1048,0x2108,0x70,0x4110,0x4140]),
([pw83,pw0,pw1,pw2,pw3,pw124],[49,5,53,1,17,77,25,93,37,101,9,13,29,41,73,81],[0x7,0xd,0x31,0xc1,0x301,0x40a,0x802,0x1042,0x2102,0x408,0x1048,0x2108,0x4050,0x8110,0x4140]),
([pw83,pw122,pw0,pw1,pw2,pw3],[101,37,49,5,45,53,1,17,77,25,93,41,81,73,9,13,29],[0x7,0x1c,0x64,0x184,0x604,0x80a,0x842,0x1082,0x2202,0x4048,0x8008,0x10208,0x4040,0x10240,0x2280]),
([pw87,pw0,pw1,pw125,pw3,pw4],[49,5,45,53,1,17,77,73,93,37,101,9,13,109,41,125,25,81],[0x7,0x19,0x61,0x181,0x601,0x812,0x1002,0x2082,0x4202,0x810,0x8090,0x4210,0x100a0,0x20220,0x20280]),
([pw87,pw0,pw1,pw2,pw126,pw4],[49,5,45,53,1,17,77,25,93,37,101,9,13,29,41,73,81],[0x7,0x19,0x61,0x181,0x601,0x812,0x1002,0x2082,0x4202,0x810,0x2090,0x4210,0x80a0,0x10220,0x8280]),
([pw127,pw115,pw0,pw1,pw2,pw3],[89,49,37,45,13,53,9,17,77,25,93,5,65,1,85,81,73,33,21,29],[0x7,0x18,0x62,0x182,0x602,0x818,0x3040,0xc080,0x10200,0x20050,0x40090,0x80210,0x400c0,0x80240,0x10280]),
([pw0,pw1,pw2,pw128,pw3,pw5],[33,9,13,21,17,37,5,29,25,53,49,41,1,81,73,77,89,93],[0x7,0x1c,0x64,0x184,0x604,0x1a,0x1802,0x182,0x602,0x2030,0x4110,0x8410,0x4120,0x10420,0x20500]),
([pw129,pw0,pw1,pw2,pw3,pw4],[49,5,33,53,1,17,77,25,93,37,101,9,13,29,41,85,97],[0x7,0x19,0x61,0x181,0x601,0x812,0x1002,0x2082,0x4202,0x810,0x2090,0x4210,0xe0,0x8220,0x10280]),
([pw87,pw0,pw2,pw3,pw88,pw4],[49,5,33,17,77,25,93,53,1,37,101,13,29,9,41,85,579],[0x7,0x19,0x61,0x181,0x601,0x802,0x1022,0x2102,0x4202,0x38,0x2100,0x8208,0x1120,0x10220,0x4300]),
([pw87,pw0,pw1,pw3,pw130,pw4],[49,5,33,53,1,25,93,17,77,37,101,9,29,13,41,73,81],[0x7,0x19,0x61,0x181,0x601,0x812,0x1022,0x2002,0x4202,0x1030,0x810,0x4210,0x80a0,0x8220,0x10280]),
([pw87,pw0,pw1,pw2,pw131,pw73],[49,5,33,53,1,17,77,73,97,25,93,9,13,611,29,579,289],[0x7,0x19,0x61,0x181,0x601,0x812,0x1002,0x2082,0x4202,0x810,0x8090,0x4210,0x1a0,0x260,0x10000]),
([pw80,pw117,pw23,pw2,pw3,pw4],[49,9,643,45,1,33,17,77,25,93,37,101,257,707,771,835,81,73,85],[0x7,0x38,0xc1,0x301,0xc01,0x1000,0x2042,0x4102,0x18002,0x58,0x20110,0x18,0x20140,0x50040,0x20100]),
([pw80,pw132,pw0,pw1,pw2,pw3],[37,81,101,5,33,41,1,17,77,25,93,45,65,85,73,9,13,29],[0x7,0x19,0x61,0x181,0x601,0x800,0x1000,0x2082,0x4200,0x8048,0x10008,0x20208,0x8040,0x20240,0x4280]),
([pw80,pw0,pw1,pw2,pw3,pw18],[45,41,49,1,17,77,25,93,37,9,21,29,5,73],[0x7,0xe,0x32,0xc2,0x106,0x208,0x410,0x840,0x1000,0x208,0x848,0x208,0x2050,0x410,0x840]),
([pw80,pw133,pw0,pw1,pw2,pw3],[37,41,101,5,33,53,1,17,77,25,93,45,65,81,85,73,9,13,29],[0x7,0x19,0x61,0x181,0x601,0x808,0x1000,0x6080,0x8200,0x10048,0x20008,0x40208,0x10040,0x40240,0x8280]),
([pw80,pw0,pw1,pw2,pw131,pw3],[37,5,33,41,1,17,77,81,105,25,93,9,13,931,29,899,73],[0x7,0x19,0x61,0x181,0x601,0x812,0x1002,0x2082,0x4202,0x810,0x8090,0x4210,0x1a0,0x260,0x10000]),
([pw134,pw135,pw0,pw1,pw2,pw3],[37,81,13,113,89,9,129,17,25,73,5,41,1,77,33,29],[0x3,0x1c,0x70,0x80,0x300,0x405,0x1820,0x2003,0x301,0x4024,0x200c,0x8104,0x2060,0x8120,0x300]),
([pw117,pw23,pw2,pw3,pw4,pw92],[273,9,971,77,1031,73,1091,37,1155,49,45,285,137,57,1,85,81,17,93,25,101],[0x1,0xe,0x32,0xc2,0x302,0xc08,0x1420,0x2480,0x4600,0x8028,0x10088,0x20208,0x100a0,0xc0200,0x100280])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK true p7_T p7_t 4 p7_N4 p7_D5_0 = true := by decide +kernel
def p7_B5 : List (List StD) := [p7_D5_0]
def p7_N5 : Array (List Nat) := mkNext p7_B5
theorem p7_I5 : LevelB true p7_T 5 p7_B5 := levelStepB p7_B p7_W p7_I4 (by
  intro c hc
  unfold p7_B5 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p7_C5x0
  cases hc
  )
def p7_D6_0 : List StD := [
([pw136,pw23,pw2,pw3,pw18,pw95,pw5],[117,17,25,7,444,13,128,432,9,49,67,155,205,77,45,73,197,33,209,89,85,29,93,88,53],[0x1,0x2,0x1c,0xe0,0x1c0,0xe00,0x7000,0xc004,0x30020,0x44100,0x84200,0x8004,0x102020,0x102100,0x82200,0x200024,0x200104,0x400204,0x800120,0x1000220,0x1000300]),
([pw23,pw2,pw20,pw3,pw18,pw95,pw5],[205,117,17,45,73,25,213,13,5,217,9,1,89,49,77,21,97,128,88,56,219,259,29,93,53],[0x7,0x8,0x30,0x1c0,0xe00,0x3000,0x4000,0x34,0x8084,0x8404,0x3004,0x10020,0x60080,0xa0400,0x302000,0x4000a0,0x400420,0x802020,0x40480,0x1002080,0x1002400]),
([pw137,pw23,pw2,pw3,pw18,pw95,pw5],[45,77,17,73,25,132,13,0,140,9,4,49,197,57,209,69,89,141,221,21,29,93,101],[0x1,0x6,0x18,0xe0,0x700,0x800,0x6,0x18,0x3040,0xc200,0x70000,0x1c,0x80044,0x80204,0x6,0x100050,0x100210,0x210010,0x260,0x410040,0x410200]),
([pw138,pw23,pw2,pw3,pw18,pw95,pw5],[117,77,25,73,13,448,128,9,452,49,89,45,17,225,197,33,209,21,29,93,88,53],[0x1,0x2,0xc,0x70,0x1c0,0x600,0x3800,0x80c,0xc010,0x10880,0xe00,0x100c,0x21010,0x21080,0x1600,0x40014,0x40084,0x80204,0x100090,0x200210,0x200280]),
([pw23,pw103,pw2,pw3,pw18,pw95,pw5],[45,323,395,17,117,25,73,197,13,5,209,9,1,49,141,77,455,444,555,432,523,128,89,21,579,29,97,132,53],[0x7,0x19,0x61,0x380,0x1c00,0x6001,0x8000,0x30020,0xc0100,0x300800,0x400000,0x68,0x800108,0x800808,0x1002008,0x2000120,0x2000820,0x4002020,0x8000900,0x10002100,0x10002800]),
([pw23,pw2,pw3,pw4,pw73,pw74,pw75],[57,17,77,137,73,141,81,157,13,5,153,9,1,85,21,587,25,97,37,105,675,140,643,132,128],[0x7,0x19,0x61,0x9,0x380,0x1c00,0x16,0x2042,0x6,0x4102,0x4802,0x8050,0x10000,0x20110,0x20810,0x40000,0x80140,0x80840,0x300100,0xc00800,0x1000900]),
([pw134,pw23,pw2,pw3,pw18,pw95,pw5],[45,117,17,25,73,13,747,432,9,715,128,89,77,197,5,209,1,49,141,85,229,29,97,132,53],[0x3,0x4,0x18,0xe0,0x700,0x800,0x1003,0x19,0x6020,0x18100,0x60001,0x18,0x81020,0x81100,0x121000,0x200028,0x200108,0x420008,0x800120,0x1020020,0x1020100]),
([pw23,pw2,pw3,pw4,pw74,pw75,pw107],[57,17,77,29,97,37,81,157,33,153,9,1,208,21,140,25,41,93,13,132,164],[0x7,0x19,0x61,0x181,0xe00,0x1001,0xe,0x62,0x2002,0x2402,0x2002,0x68,0x4008,0x418,0x8000,0x10020,0x10420,0x10020,0x24400,0x40000,0x180400]),
([pw23,pw2,pw3,pw4,pw74,pw139],[77,57,17,129,97,25,61,81,37,141,93,13,5,4,208,165,9,1,268,85,21,132,29,775,41,847,643,943,124],[0xf,0x72,0x382,0x1c42,0x3e002,0x40025,0x80184,0x100c04,0x150004,0x1b0,0xc30,0x600000,0x3800900,0xd010100,0x10012800]),
([pw140,pw23,pw2,pw3,pw4,pw74,pw75],[57,300,140,17,971,100,29,37,81,13,436,232,77,25,97,157,5,165,9,1,21,233,41,132],[0x7,0x38,0x40,0x180,0x604,0x800,0x1009,0x6001,0x181,0x18200,0xe0000,0x3008,0x188,0x100208,0x140008,0x2180,0x6200,0x242000,0x400280,0x440080,0x840200]),
([pw109,pw23,pw2,pw32,pw4,pw5],[57,132,33,13,5,17,21,1027,164,97,9,37,41,216,436,53,77,113,1,81,141,89,49,835,1091,85,101,105],[0x1f,0x1e8,0x60a,0x3908,0xc100,0x30024,0x40605,0x180804,0x600005,0x1800460,0x2080820,0x610020,0x1e00,0x600600,0xc400800]),
([pw137,pw23,pw2,pw3,pw31,pw4,pw75],[33,49,17,77,29,1159,13,0,37,81,53,9,69,137,57,89,21,25,93,41],[0x1,0xe,0x32,0xc2,0x302,0xc02,0x100c,0x3010,0x5040,0x1300,0x9800,0x1c,0x10044,0x304,0x10804,0x20000,0x310,0x40810,0x80140,0x8840,0x80900]),
([pw23,pw2,pw3,pw18,pw75,pw141],[77,45,17,117,73,25,145,105,69,13,5,101,9,1,1239,344,157,41,1155,456,21,29,284,432,132,189,49,37],[0xf,0x72,0x782,0x3902,0x7c002,0x35,0x180204,0x101804,0xa0005,0x2002a0,0x601020,0x420030,0x3801200,0xc020280,0x4021800]),
([pw23,pw2,pw30,pw3,pw95,pw142,pw5],[65,5,21,45,25,73,9,1,197,37,49,89,85,81,432,29,237,56,13,53,93,88],[0x7,0xb,0x32,0xc2,0x302,0xc02,0x1000,0x34,0x2044,0x4000,0xc04,0x8010,0x30040,0x40000,0x80400,0x8050,0x8010,0x100410,0x200240,0x80440,0x80600]),
([pw0,pw23,pw2,pw143,pw3,pw95,pw5],[5,13,21,17,37,88,29,25,81,9,53,49,65,133,73,1,89,77,97,41,1283,93],[0x1,0xe,0x32,0xc2,0x302,0xc02,0x3008,0x3010,0x5080,0x8300,0x11800,0x20000,0x4088,0x20c,0x10808,0x40090,0x80210,0x100810,0x2c0,0x200880,0xe00]),
([pw113,pw0,pw23,pw2,pw3,pw4,pw75],[49,13,0,157,17,77,25,73,37,53,9,45,21,29,1155,81,89,69,149,65,85,101],[0x7,0x8,0x31,0xc1,0x100,0x601,0x800,0x1012,0x2042,0xc002,0x10402,0x20030,0x200c0,0x68000,0x90400,0xd0,0x108010,0x1410,0xc0,0x2440,0x208400]),
([pw0,pw23,pw2,pw3,pw95,pw79,pw141],[57,13,21,17,29,25,105,9,132,53,37,77,73,69,65,1367,149,460,101,189,41,128,89],[0x1,0xe,0x32,0xc2,0x100,0x602,0x808,0x1020,0x20c0,0x4000,0x18400,0x1028,0x8c,0x60008,0xc08,0xb0,0x1020,0x1420,0xc0080,0x100480,0x600400]),
([pw144,pw0,pw23,pw2,pw3,pw4,pw75],[49,13,124,69,157,17,77,25,73,37,105,53,9,33,21,29,41,89,97,81,61],[0x7,0x19,0x61,0x181,0x601,0x1801,0x2000,0x4022,0x8082,0x10202,0x21002,0x68,0x40088,0x80208,0x121000,0xe0,0x80220,0x5020,0x80280,0x9080,0x11200]),
([pw87,pw0,pw23,pw2,pw3,pw32,pw4],[49,13,53,89,61,17,77,25,93,9,37,101,5,21,263,96,41,161,129,1,81,29],[0x7,0x19,0x61,0x181,0x205,0xc01,0x1000,0x2022,0x4082,0x8202,0x10402,0x60,0x60080,0x88200,0x100400,0xe0,0x2220,0x100420,0x200000,0x100480,0x10600]),
([pw23,pw2,pw3,pw4,pw74,pw145,pw139],[57,17,77,61,37,81,13,5,241,208,9,1,21,93,25,132,41,49,140,53],[0x7,0x9,0x31,0xc8,0x301,0xe00,0x6,0x32,0x1042,0x6,0x1402,0x30,0x2040,0x4000,0x8000,0x10050,0x30,0x10410,0x22040,0x40440,0x80000]),
([pw0,pw114,pw23,pw2,pw32,pw4,pw5],[13,0,25,45,1219,77,73,9,41,37,53,49,61,124,17,29,1411,1479,1355,173,65,81,89,101],[0x7,0x8,0x31,0xc1,0x301,0xc01,0x1000,0x6004,0x8084,0x10204,0x20804,0xc0020,0x1000c0,0x200200,0x400800,0xc0,0x200220,0x400820,0x380,0xc80,0x800a00]),
([pw36,pw23,pw2,pw30,pw3,pw4,pw5],[1,9,5,21,164,13,0,29,25,41,37,53,49,65,73,69,17,81,89,93,101],[0x7,0x1a,0x62,0x182,0x602,0x1802,0x200c,0x2024,0x4104,0x2404,0x9004,0x10000,0x4108,0x20408,0x41008,0x1a0,0x620,0x1820,0x4500,0x81100,0x101400]),
([pw36,pw23,pw2,pw3,pw42,pw4,pw5],[1,9,5,21,164,29,56,0,41,37,53,49,33,65,13,69,73,17,81,77,25,93,101],[0x7,0x1a,0x62,0x80,0x302,0xc02,0x100c,0x1024,0x6004,0x2204,0x8804,0x10028,0x20000,0x40208,0x80808,0x100000,0x10220,0x200820,0x4300,0x4c00,0x400a00]),
([pw0,pw1,pw2,pw143,pw3,pw78,pw5],[45,9,13,21,17,37,41,29,25,5,53,49,1,77,73,105,81,89,97,1539,136,93],[0x7,0x1c,0x64,0x184,0x200,0xc04,0x1a,0x62,0x182,0x1000,0xc02,0x2000,0x4110,0x18010,0x20810,0x40120,0x18020,0x80820,0x110100,0x200900,0x30800]),
([pw113,pw0,pw1,pw2,pw3,pw4,pw79],[49,13,53,9,17,77,25,73,37,16,57,21,29,141,81,45,149,65,85,360,89,101],[0x7,0xd,0x31,0xc1,0x100,0x200,0x40a,0x812,0x1042,0x6002,0x8000,0x818,0x1048,0x14008,0x20000,0xd0,0x44010,0x180010,0xc0,0xc0,0x304000]),
([pw137,pw146,pw0,pw1,pw3,pw4,pw79],[77,17,49,13,53,9,25,73,37,81,100,21,57,29,41,245,249],[0x7,0x1c,0x34,0xc4,0x304,0x400,0x80a,0x822,0xc2,0x302,0x400,0x1028,0x2048,0x4108,0x8000,0x2060,0x4120,0x10000,0x1c0,0xc0,0x300]),
([pw0,pw1,pw2,pw3,pw78,pw79,pw141],[141,9,13,21,17,29,25,57,45,41,37,69,65,73,77,464,101,324,105,189,132,81,128,89],[0x7,0x1c,0x64,0x80,0x100,0x604,0x1a,0x62,0x800,0x1000,0x602,0x2050,0x4010,0x18010,0x4410,0x60040,0x2040,0x2440,0xd0000,0x300400,0xc00400]),
([pw144,pw0,pw1,pw2,pw3,pw4,pw79],[49,13,53,9,17,77,25,73,37,105,89,0,57,21,29,41,33,61,81,328,253],[0x7,0xd,0x31,0xc1,0x301,0xc01,0x100a,0x2012,0x4042,0x8102,0x10000,0x2018,0x4048,0x8108,0x20000,0x70,0x40110,0x80410,0x40140,0x100440,0x40100]),
([pw87,pw0,pw1,pw2,pw3,pw39,pw4],[49,13,33,53,9,17,77,25,93,89,37,101,113,21,29,5,41,1,85,81,73,1607,1667],[0x7,0x19,0x61,0x181,0x201,0xc01,0x1012,0x2022,0x4082,0x8000,0x10402,0x2030,0x4090,0x20000,0x10410,0xe0,0x40020,0x80420,0x100000,0x80480,0x600400]),
([pw137,pw115,pw0,pw1,pw2,pw3,pw5],[81,37,137,13,33,145,9,61,77,17,73,25,49,41,93,89,21,29],[0x3,0x1c,0xe0,0x300,0xc00,0x1000,0x200a,0x2042,0x203,0xc02,0xc002,0x4c,0x10208,0x20808,0x800c,0x10240,0x20840,0x8060,0xe00,0x300,0xc800]),
([pw0,pw1,pw114,pw2,pw39,pw4,pw5],[173,9,13,29,25,1379,77,45,41,37,53,49,1347,65,124,17,376,1735,1811,85,73,81,89,240,101],[0x7,0x1c,0x64,0x80,0x304,0xc04,0x1a,0x1042,0x2000,0x302,0xc02,0xc010,0x10000,0x20210,0x40810,0x180040,0x200240,0x400840,0x900200,0x500800,0x1000a00]),
([pw83,pw0,pw1,pw23,pw2,pw3,pw4],[49,13,53,9,89,17,77,25,93,37,101,1859,5,21,29,41,1,73,81],[0x7,0xd,0x11,0x61,0x181,0x601,0x80a,0x1000,0x2022,0x4082,0x8202,0x10000,0x2028,0x4088,0x8208,0x60,0x20080,0x40200,0x200a0,0x40220,0x20280]),
([pw87,pw117,pw23,pw2,pw20,pw3,pw4],[49,9,316,89,1,17,132,25,93,37,101,257,109,57,73,81,77,97,105],[0x7,0x19,0x29,0x40,0x181,0x601,0x800,0x26,0x4,0x86,0x206,0x1030,0x2000,0x4090,0x8210,0x10000,0x40a0,0x8220,0x20080,0x40200,0x4280]),
([pw87,pw0,pw1,pw147,pw2,pw3,pw4],[49,5,45,53,1,100,468,17,77,73,93,37,101,9,113,13,193,41,96,129,161,1923,25,1987,2055,81],[0x7,0x19,0x61,0x181,0x601,0x1801,0x2012,0x4022,0x8002,0x10202,0x20802,0xc0010,0x2010,0x100210,0x20810,0x2000a0,0x400000,0x1800800,0x380,0x2000880,0x2000a00]),
([pw87,pw148,pw0,pw1,pw2,pw3,pw4],[49,93,5,45,53,1,17,77,25,37,101,113,129,73,81,9,13,29,41],[0x3,0xd,0x31,0xc1,0x103,0x601,0x800,0x1000,0xc0,0x2000,0x4200,0x8024,0x10004,0x20104,0x40204,0x8020,0x20120,0x40220,0x1c0,0x4240,0x4300]),
([pw87,pw0,pw1,pw20,pw3,pw35,pw4],[49,5,53,1,24,73,93,17,89,37,101,9,57,109,13,41,69,125,261,77,1923,105,25,81],[0x7,0xd,0x10,0x61,0x181,0x601,0x80a,0x1000,0x2022,0x4002,0x8202,0x10000,0x20028,0x808,0x8208,0xc0020,0x180080,0x280200,0x400000,0x800220,0x800280]),
([pw144,pw0,pw1,pw2,pw39,pw4,pw145],[93,13,137,9,145,77,17,169,37,105,49,25,89,33,21,57,41,29,69,85,81,160,97],[0x7,0x19,0x60,0x80,0x301,0x1c00,0x200a,0x4042,0x8000,0x10102,0x20802,0x4048,0x40000,0x10108,0x20808,0x80040,0x100140,0x860,0x600100,0x1800,0x100900]),
([pw36,pw0,pw2,pw20,pw3,pw4,pw5],[1,5,9,61,0,29,25,41,37,53,49,13,33,77,17,73,81,89,65,265,69,93,101],[0x7,0x5,0x19,0x61,0x181,0x601,0x802,0x1000,0x62,0x182,0x602,0x2000,0xc040,0x14100,0x24400,0xc0040,0x140100,0x140400,0x8140,0x200440,0x400500]),
([pw144,pw0,pw1,pw2,pw3,pw4,pw149],[49,13,53,9,17,77,25,93,37,105,0,33,21,29,41,185,269,81,328,89,253,101],[0x7,0xd,0x31,0xc1,0x301,0x400,0x80a,0x1012,0x2042,0x4102,0x8000,0x1018,0x2048,0x4108,0x10000,0x70,0x20110,0xc0010,0x20140,0x100000,0x280100]),
([pw87,pw0,pw1,pw2,pw3,pw150,pw4],[49,5,33,53,1,17,77,25,93,208,37,101,9,13,29,57,41,69,73,85,81,97,2119,2179],[0x7,0x19,0x61,0x181,0x200,0xc01,0x1012,0x2002,0x4082,0x8000,0x10402,0x1010,0x4090,0x20000,0x10410,0x400a0,0x80000,0x100420,0x200000,0x40480,0xc00400]),
([pw83,pw0,pw1,pw2,pw3,pw39,pw4],[49,13,53,9,17,77,25,93,89,37,101,33,21,29,5,41,1,85,81,73,2243,2187],[0x7,0xd,0x31,0xc1,0x101,0x601,0x80a,0x1012,0x2042,0x4000,0x8202,0x1018,0x2048,0x10000,0x8208,0x70,0x20010,0x40210,0x80000,0x40240,0x300200]),
([pw83,pw0,pw1,pw2,pw20,pw3,pw4],[49,5,53,1,17,89,100,20,25,93,37,101,9,13,33,29,41,61,77,73,81,97,105],[0x7,0xd,0x31,0xc1,0x301,0xc01,0x100a,0x2002,0x4000,0x8102,0x10402,0x1008,0x20000,0x8108,0x10408,0x40000,0x80110,0x100410,0x200100,0x400400,0x80500]),
([pw36,pw0,pw2,pw3,pw150,pw4,pw5],[1,5,9,29,25,0,41,37,53,49,13,273,17,73,277,81,77,265,93,69,65,101],[0x7,0x5,0x19,0x20,0xc1,0x301,0x402,0x1a,0x800,0xc2,0x302,0x3010,0x4000,0x9080,0x11200,0x20000,0x2090,0x40210,0x180080,0x180200,0x200280]),
([pw83,pw0,pw1,pw2,pw3,pw150,pw4],[49,5,53,1,17,77,25,93,20,37,101,9,13,29,57,41,69,73,85,81,97,2307,2371],[0x7,0xd,0x31,0xc1,0x100,0x601,0x80a,0x1002,0x2042,0x4000,0x8202,0x808,0x2048,0x10000,0x8208,0x20050,0x40000,0x80210,0x100000,0x20240,0x600200]),
([pw83,pw0,pw1,pw2,pw3,pw4],[57,49,5,53,45,69,1,77,17,89,97,25,93,105,37,101,9,13,21,29,33,41,117,61,133,73,81,85],[0x1f,0x6a,0x382,0x1c02,0xe002,0x30044,0x60104,0x180804,0x604004,0x50140,0x880840,0x1204040,0x2000980,0xc004100,0x6004800]),
([pw87,pw14,pw0,pw1,pw2,pw3,pw4],[101,49,5,45,53,1,17,85,25,93,117,57,133,69,77,73,37,9,13,29,105],[0x3,0xe,0x32,0xc2,0x302,0x3,0xc04,0x3020,0x40c0,0x8100,0x10000,0x20024,0x40004,0x80104,0x100404,0x20020,0x80120,0x101020,0x8140,0xc0,0x8100]),
([pw151,pw87,pw0,pw1,pw20,pw3,pw4],[49,5,13,1,9,100,17,25,73,37,81,89,96,93,101,57,29,41,69,85,77],[0x1,0x6,0x18,0x20,0x1c0,0x640,0x822,0x1808,0x20,0x2880,0x4a00,0x1a,0x8000,0x10082,0x20202,0x40000,0x10088,0x20208,0x180080,0x180200,0x380]),
([pw87,pw0,pw1,pw2,pw152,pw3,pw4],[49,5,45,53,1,17,85,93,37,101,9,13,113,97,41,129,1923,77,261,81,25],[0x7,0x19,0x61,0x81,0x81,0x301,0x412,0x802,0x1002,0x3002,0x4102,0x410,0x8010,0xa010,0x4110,0x30020,0x42020,0x80120,0x100000,0x80100,0x80100]),
([pw153,pw146,pw0,pw1,pw3,pw4,pw5],[328,113,129,73,37,81,93,5,13,1,9,17,25,77,49,29,41,53,97,101],[0x1,0x2,0x4,0x8,0x30,0x40,0x180,0x600,0x3800,0x830,0x6800,0x680,0x9080,0x10090,0x24080,0x9200,0x10210,0x24200,0x1030,0x45000,0x84010]),
([pw154,pw87,pw0,pw1,pw2,pw3,pw4],[93,5,113,1,129,17,2435,100,25,37,81,49,45,53,77,253,97,101,9,13,41],[0x1,0x6,0x18,0xe0,0x100,0x600,0x1802,0x2808,0x4820,0x18800,0x20a00,0x4000a,0x80002,0x10006,0x100202,0x40008,0x10018,0x100208,0x4020,0x620,0x600]),
([pw87,pw0,pw1,pw2,pw3,pw155,pw4],[57,5,33,69,1,61,77,17,253,93,25,49,37,105,9,13,29,41,73,85,81,97,2503,2571],[0x7,0x38,0xc0,0x700,0x800,0x3200,0x4012,0x8002,0x10402,0x3,0x21002,0x4010,0x10410,0x18,0x21010,0x40480,0x80080,0x101080,0x200000,0x41400,0xc01000]),
([pw156,pw87,pw0,pw1,pw2,pw3,pw4],[49,57,5,69,1,77,17,73,25,37,45,65,97,105,101,189,9,13,29,117,133,85],[0x1,0x6,0x18,0x60,0x180,0x200,0x406,0x818,0x60,0x1100,0xe000,0x10014,0x20004,0x40104,0x82004,0x10010,0x40110,0x102010,0x1c0,0x200040,0x180]),
([pw87,pw0,pw1,pw2,pw157,pw3,pw4],[49,5,45,53,1,17,77,93,25,169,37,101,9,13,137,29,41,145,73,81,97,105],[0x7,0x19,0x61,0x80,0x301,0xc01,0x1012,0x2002,0x4002,0x8102,0x10402,0x1010,0x20010,0x8110,0x10410,0x60,0x40120,0x80420,0x100000,0x200400,0x40500]),
([pw87,pw0,pw1,pw2,pw131,pw3,pw4],[49,5,33,53,1,17,77,2635,2691,25,93,37,101,9,13,2787,96,29,41,2755,100,2819,85,73,81,2883],[0x7,0x19,0x61,0x181,0x601,0x1801,0x2012,0x4002,0x18002,0x20202,0x40802,0x2010,0x180010,0x20210,0x40810,0x300020,0x260,0x400820,0x800000,0x1000000,0x2000a00]),
([pw87,pw0,pw1,pw2,pw3,pw4,pw73],[49,5,33,53,1,17,77,73,93,81,101,9,13,113,117,129,133,85,2883,25,37],[0x7,0x19,0x61,0x181,0x601,0x101,0x812,0x1002,0x2082,0x4202,0x2002,0x810,0x8090,0x10210,0x8010,0xe0,0x20220,0x60,0x40280,0x80000,0x100000]),
([pw134,pw115,pw0,pw1,pw2,pw3,pw5],[37,81,13,113,9,129,17,25,73,89,5,41,1,77,49,105,33,29,53,229,97],[0x3,0xc,0x30,0x40,0x180,0x200,0x405,0x1810,0x2003,0x181,0xc001,0x10014,0x200c,0x20084,0x44004,0x2030,0x20090,0x44010,0x180,0x86000,0x104080]),
([pw137,pw0,pw1,pw2,pw3,pw4,pw158],[49,13,45,53,9,17,77,25,73,281,81,89,0,57,21,29,141,185,149,177,85,100,37],[0x7,0x19,0x61,0x181,0x601,0x1801,0x2012,0x4022,0x8082,0x10402,0x20802,0x4030,0x8090,0x40410,0x80810,0x1a0,0x100420,0x200820,0x180,0x180,0x400c00]),
([pw80,pw0,pw1,pw23,pw2,pw3,pw4],[49,13,53,9,89,17,77,25,93,37,101,2947,5,21,29,1315,81,1,1283,73,1539,3011,85],[0x7,0xd,0x11,0x61,0x181,0x601,0x80a,0x1000,0x2022,0x4082,0x18002,0x20000,0x2028,0x4088,0x50008,0x60,0x80080,0x310000,0x800a0,0x410020,0x80080]),
([pw113,pw0,pw1,pw2,pw3,pw4,pw158],[45,13,53,9,49,17,77,25,73,281,0,21,29,65,81,85,360,89,101],[0x3,0x1c,0x70,0x190,0x200,0x400,0xb,0x822,0x1082,0x3,0x3,0x828,0x1088,0x2008,0x2008,0x1a0,0xc020,0x30020,0x180,0x180,0x64000]),
([pw137,pw135,pw0,pw1,pw2,pw3,pw5],[81,37,57,13,33,69,9,61,77,17,73,25,1547,41,93,89,21,29],[0x3,0x1c,0xe0,0x300,0xc00,0x1000,0x200a,0x2042,0x203,0xc02,0xc002,0x4c,0x10208,0x20808,0xc,0x10240,0x20840,0x60,0xe00,0x300,0xc800]),
([pw80,pw0,pw1,pw2,pw143,pw3,pw4],[45,5,53,1,49,17,89,20,25,93,81,101,9,13,29,65,77,73,105,97],[0x3,0x1c,0x70,0x80,0x310,0xc10,0x100a,0x2002,0x3,0x4102,0x3,0x1008,0x8008,0x4108,0x8008,0x10000,0x20120,0x40420,0x80100,0x40400,0x20100]),
([pw80,pw0,pw1,pw2,pw3,pw4],[45,49,5,53,33,65,1,77,17,89,97,25,93,105,37,81,101,9,13,21,29,113,3075,3171,129,3107,3139,73,85,3203,3275],[0x1f,0x6a,0x382,0x1c02,0x1e002,0x60044,0xc0104,0x300804,0xc08005,0xa0140,0x1100840,0x6008060,0x8000980,0x1000a100,0x68008800]),
([pw23,pw2,pw3,pw42,pw46,pw4,pw5],[33,1,84,13,9,37,81,49,89,121,73,77,17,21,25,29,93,124,41,53,101],[0x3,0x3,0xe,0x16,0x62,0x182,0xe00,0x1000,0x2000,0x860,0x980,0x4000,0x8000,0x460,0x10480,0x20018,0x40028,0x80088,0x40030,0x80090,0x1000a0]),
([pw0,pw1,pw23,pw2,pw3,pw4,pw92],[3331,13,9,45,1451,77,1511,73,41,37,53,49,65,1419,1479,1743,84,1811,81,89,85,17,93,25,101],[0x7,0x8,0x32,0xc2,0x302,0xc02,0x1000,0x2024,0x4084,0x304,0xc04,0x18020,0x30080,0x40200,0x80800,0x1000a0,0x40220,0x200820,0x40280,0xc00800,0x1000a00])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C6x0 : levelOK true p7_T p7_t 5 p7_N5 p7_D6_0 = true := by decide +kernel
def p7_D6_1 : List StD := [
([pw83,pw0,pw1,pw2,pw3,pw35,pw4],[49,5,45,53,1,89,77,73,93,37,101,9,13,33,41,61,121,17,81,25],[0x7,0x19,0x61,0x181,0x21,0x601,0x812,0x1002,0x2002,0x1002,0x4202,0x810,0x8010,0x810,0x4210,0x100c0,0x20000,0x40240,0x80000,0x40280,0x40200]),
([pw36,pw0,pw2,pw31,pw32,pw4,pw5],[61,33,84,17,21,25,161,1,29,37,41,49,53,5,65,81,77,101],[0x7,0x18,0x61,0x181,0x600,0x1800,0x18,0x2000,0x4102,0x602,0x1802,0x18,0x18,0x8208,0x10808,0x4120,0x620,0x1820,0x700,0x1900,0x20a00]),
([pw36,pw0,pw2,pw32,pw42,pw4,pw5],[61,5,84,21,125,1,29,173,37,41,49,53,33,13,73,17,81,77,65,25,101],[0x7,0x19,0x61,0x80,0x300,0xc00,0x100a,0x1042,0x2000,0x302,0xc02,0x4048,0x8000,0x10108,0x20408,0xc0040,0x340,0xc40,0x80300,0x80c00,0x100500]),
([pw137,pw146,pw0,pw1,pw3,pw4,pw74],[77,17,53,57,153,9,1,25,73,37,81,49,100,21,69,29,41,13,89,249],[0x7,0x1c,0x64,0x184,0x604,0x1804,0x2002,0x2022,0x182,0x602,0x2002,0x4028,0x8080,0x10200,0x20000,0x80a0,0x10220,0xc0020,0x380,0x8080,0x10200]),
([pw87,pw0,pw1,pw30,pw3,pw35,pw4],[49,5,53,1,73,93,21,89,37,101,9,13,109,285,41,69,129,261,77,96,17,25,81],[0x7,0xd,0x5,0x31,0xc1,0x301,0x40a,0x800,0x1012,0x2042,0x4102,0x8008,0x10018,0x408,0x4108,0x60010,0x180040,0x4100,0x200000,0x400110,0x400140]),
([pw144,pw0,pw1,pw2,pw31,pw4,pw145],[93,33,137,69,9,1,77,17,97,169,37,105,49,29,89,61,21,13,41,81,25],[0x7,0x38,0xc0,0x301,0xc01,0x7000,0x8012,0x10080,0x20000,0x40402,0x6002,0x10090,0x18,0x40410,0xa010,0x10080,0x80480,0x20c0,0x40400,0x106000,0x82400]),
([pw144,pw0,pw1,pw2,pw3,pw4,pw107],[57,33,53,9,1,17,77,29,93,37,105,49,0,61,21,41,13,89,269,81,25],[0x7,0x1c,0x64,0x184,0x604,0x1804,0x200a,0x4020,0x83,0x8202,0x10000,0x4028,0x2088,0x8208,0x60008,0xe0,0x80220,0x4020,0x80280,0x100000,0x8200]),
([pw87,pw0,pw1,pw2,pw3,pw42,pw4],[49,5,33,53,1,21,77,29,93,37,101,9,73,13,41,129,69,17,81,25],[0x7,0x19,0x61,0x181,0x9,0x601,0x812,0x62,0x1082,0x2000,0x4202,0x810,0x8090,0x10010,0x4210,0x10a0,0x20000,0x40220,0x80000,0x1280,0x4200]),
([pw83,pw0,pw1,pw2,pw3,pw31,pw4],[49,33,53,1,17,77,29,93,37,101,9,21,193,5,41,61,81,25],[0x7,0xd,0x31,0xc1,0x5,0x301,0x408,0x810,0x1042,0x2000,0x4102,0x408,0x8048,0x408,0x4108,0x70,0x810,0x10110,0x20000,0x10140,0x4100]),
([pw83,pw0,pw1,pw2,pw30,pw3,pw4],[49,5,53,1,21,89,25,93,37,101,9,109,13,29,41,61,17,73,81],[0x7,0xd,0x31,0x5,0xc1,0x301,0x40a,0x812,0x1000,0x2042,0x4102,0x408,0x8008,0x2048,0x4108,0x10000,0x20050,0x40110,0x2040,0x4100,0x20140]),
([pw151,pw87,pw0,pw1,pw30,pw3,pw4],[49,5,21,109,1,9,17,100,25,73,37,81,89,69,77,93,101,13,29,41],[0x1,0xe,0x30,0xc4,0x304,0xc04,0x1082,0x2010,0x5080,0x9100,0x11400,0x32,0x20000,0x40102,0x80402,0x2010,0x40110,0x80410,0x40100,0x80400,0x700]),
([pw140,pw146,pw0,pw1,pw3,pw4,pw5],[17,328,96,5,113,129,29,37,81,93,13,1,9,25,77,49,41,53,97,101],[0x7,0x18,0x20,0x40,0x180,0x200,0x408,0x1800,0x6001,0x181,0xc001,0x1808,0x2018,0x10088,0x28008,0x42800,0x10880,0x28800,0x2180,0x4a000,0x88080]),
([pw36,pw0,pw2,pw32,pw35,pw4,pw5],[13,5,61,77,125,1,73,25,173,37,41,49,53,65,17,81,89,29,101],[0x3,0x1c,0x64,0x184,0x600,0x1800,0x3,0x3,0x3,0x602,0x1802,0x2040,0x4000,0x8208,0x10808,0x22080,0x600,0x1800,0x8280,0x10880,0x40a00]),
([pw36,pw0,pw2,pw3,pw46,pw4,pw5],[1,5,13,17,61,25,9,0,41,37,53,49,33,65,273,73,21,81,77,29,93,101],[0x7,0x19,0x31,0xc1,0x301,0xc01,0x6,0x1022,0x6002,0x302,0xc02,0x8028,0x10000,0x20208,0x40808,0x80000,0x8220,0x100820,0x300,0xc00,0x200a00]),
([pw83,pw0,pw1,pw2,pw3,pw42,pw4],[49,5,53,1,21,77,29,93,37,101,9,33,13,41,61,69,73,17,81,25],[0x7,0xd,0x31,0xc1,0x5,0x301,0x40a,0x812,0x842,0x1000,0x2102,0x408,0x4048,0x8008,0x2108,0x10050,0x20000,0x40110,0x80000,0x10140,0x2100])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C6x1 : levelOK true p7_T p7_t 5 p7_N5 p7_D6_1 = true := by decide +kernel
def p7_B6 : List (List StD) := [p7_D6_0,p7_D6_1]
def p7_N6 : Array (List Nat) := mkNext p7_B6
theorem p7_I6 : LevelB true p7_T 6 p7_B6 := levelStepB p7_B p7_W p7_I5 (by
  intro c hc
  unfold p7_B6 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p7_C6x0
  rcases List.mem_cons.mp hc with rfl | hc; · exact p7_C6x1
  cases hc
  )
def p7_D7_0 : List StD := [
([pw23,pw2,pw3,pw4,pw74,pw75],[100,77,57,48,17,11,73,75,25,137,147,203,19,81,83,37,141,139,211,140,0,20,157,168,13,132,5,4,153,9,1,85,96,21,267,323,395,403,451,547,29,611,663,483,515,579,695,455,551,41,615,655,487,519,583,687],[0x1f,0xfe4,0x7f004,0x7f80004,0x7aa80004,0x15b,0x8000a019,0x301080019,0x222000019,0x3c0000a140,0x7c001080100,0x790022000100,0xf800001088000,0xf2000022008000,0x2b980000]),
([pw23,pw2,pw30,pw3,pw32,pw4,pw5],[256,61,21,5,763,0,13,260,25,723,4,9,1,81,37,117,89,49,145,164,17,791,879,539,264,268,839,563,56,124,41,53,88,29,93,101,105],[0x1f,0x6a,0x38a,0x1c0a,0xe008,0x70008,0x180000,0x200185,0xc00805,0x1006005,0x2030005,0xc0001c0,0x30000840,0x41004040,0x82020040,0x300000000,0x1006180,0x402020180,0x41004800,0x82020800,0x1800024000]),
([pw137,pw0,pw23,pw2,pw3,pw4,pw75],[144,49,13,0,132,157,77,17,48,73,25,907,967,81,37,915,963,89,53,9,57,21,29,707,272,41,711,69,145,149,85,93,101],[0x1f,0x30,0x1c2,0x1e02,0x1e002,0xe000a,0x100010,0x200184,0x1c00404,0x7004004,0xa0014,0x80001c0,0x18000600,0x28006000,0x80a0010,0x6c0,0x40006080,0x2a0080,0x6600,0x80480400,0x102084000]),
([pw0,pw23,pw2,pw28,pw3,pw39,pw4,pw5],[33,13,79,17,164,9,29,25,124,41,37,53,49,125,129,61,161,1,81,89,21,1047,88,1115,73,93,108,1163,101],[0x1,0xe,0x32,0xc2,0x100,0x602,0x1802,0x6008,0x8030,0x14080,0x20000,0x40400,0x81000,0x100000,0x200088,0xc00008,0x40408,0x81008,0xe0,0x30,0x620,0x1820,0x1000000,0x40480,0x2001080,0xc000400,0x81000,0x10001400]),
([pw137,pw0,pw23,pw2,pw3,pw32,pw4,pw5],[164,13,0,61,77,17,124,25,979,140,9,4,81,37,49,57,21,135,41,739,89,173,145,69,177,29,93,101],[0x7,0x8,0x30,0x1c0,0xe00,0x3000,0x4000,0x8000,0x10022,0x20082,0x602,0x42002,0x180002,0x30,0x600080,0x800600,0x3000,0x1500000,0xb0,0x10420,0x3020,0x30,0x2000000,0x3080,0x4100080,0x42400,0x4100400,0x8102000]),
([pw0,pw23,pw2,pw3,pw4,pw75,pw145],[132,5,17,13,21,48,97,276,280,775,37,41,284,93,9,49,1251,547,77,69,1043,145,81,149,20,1,1295,208,181,967,85,25,0,53],[0x3,0x3c,0x3c8,0x1c88,0x6009,0x38088,0xc0024,0x380140,0xc80400,0x3086000,0x3c088000,0x40164,0x40400404,0x6014,0x48024,0x401540,0x6041,0x80000001,0x5c00,0x409400,0x30000e000]),
([pw0,pw23,pw2,pw28,pw3,pw46,pw4,pw5],[5,13,507,17,88,871,25,56,1379,41,37,53,49,125,1,84,61,73,81,89,77,124,9,29,93,101],[0x1,0xe,0x12,0x62,0x182,0x602,0x1802,0x6008,0x1c000,0x24040,0xc000,0x44400,0x85000,0x100000,0x20048,0x200000,0x40408,0x81008,0x50,0x400000,0x600,0x1800,0x800000,0x20440,0x1001040,0x600,0x1800,0x2001400]),
([pw0,pw23,pw2,pw3,pw46,pw4,pw5],[124,5,17,13,288,256,539,25,104,531,4,9,1443,37,41,112,49,53,268,77,61,1,73,84,81,133,89,145,21,88,29,93,101,105],[0x3,0x7c,0x398,0x1c18,0xe018,0x70018,0x380004,0x700080,0xa00c00,0x3202000,0xc210000,0x480084,0x10000001,0x100a024,0x4090004,0x60000000,0x1402080,0x80050180,0xe800,0x70800,0x300012000]),
([pw109,pw1,pw23,pw2,pw3,pw4,pw5],[164,0,9,13,57,132,33,5,17,21,292,97,29,4,25,37,41,216,212,53,140,1,296,643,89,49,77,113,81,141,85,101,105],[0xf,0xf8,0x709,0x7808,0x38009,0xc0001,0x300000,0x704,0xc01005,0x38004,0x3400404,0xc000140,0x1850,0x30008040,0x3000050,0x4001501,0x50008100,0x7000100,0x10009800,0x2001801,0x182008000]),
([pw137,pw0,pw1,pw23,pw2,pw3,pw4,pw79],[49,13,53,9,132,17,77,25,73,37,81,0,272,57,21,29,41,69,140,48,89],[0x7,0xd,0x10,0x61,0x181,0x601,0x800,0x100a,0x2000,0x4022,0x8082,0x10202,0x10,0x20000,0x4028,0x8088,0x10208,0x40000,0x60,0x180,0x600,0x10,0x1a0,0x620,0x180020,0x380,0x180,0x600]),
([pw137,pw0,pw1,pw2,pw3,pw4,pw79],[57,49,13,53,69,9,77,17,48,73,25,1483,1543,81,37,1491,1539,132,0,21,272,29,137,41,141,185,145,149,140,177,85,100,89,1603,93,101],[0xf,0x3a,0x1c2,0x1e02,0x1e002,0x60000,0x35,0x180184,0x600404,0x1804004,0x2020000,0x801a0,0x4200420,0x8804020,0x30000000,0x6c0,0x40006080,0x380000180,0x6600,0x500000600,0x900006000]),
([pw0,pw1,pw2,pw20,pw3,pw39,pw4,pw5],[113,9,13,21,17,33,29,25,5,41,37,53,49,61,1,77,1687,88,1755,81,89,124,1747,236,8,12,105,300,1795,73,93,120,1803,101],[0x7,0x1c,0x20,0xc4,0x100,0x604,0x1804,0x1a,0x2000,0xc2,0x4000,0x602,0x1802,0x8000,0x10090,0x60010,0x80410,0x101010,0x600080,0x3a00000,0x4000400,0x18001000,0x20000000,0x80480,0x40001080,0x180000400,0x101000,0x200001400]),
([pw137,pw0,pw1,pw2,pw3,pw39,pw4,pw5],[137,13,33,145,9,61,77,17,124,25,1555,208,81,37,49,21,29,57,41,89,69,85,73,93,156,1859,101],[0x7,0x38,0xc0,0x700,0x800,0x3000,0x4000,0x13,0x8082,0x10202,0x20000,0x42002,0x80003,0x8090,0x10210,0x100000,0x42010,0x80018,0x2c0,0x200080,0x3080,0xc0,0x400000,0x3200,0x880200,0x3002000,0x880000,0x4082000]),
([pw0,pw1,pw23,pw2,pw3,pw4,pw79,pw145],[232,13,9,57,21,17,1063,97,41,37,132,53,49,69,1031,140,77,1671,304,81,20,1935,1543,48,93,169,25,124,89],[0x7,0x8,0x32,0xc2,0x302,0x400,0x1802,0x2000,0x34,0x4084,0x304,0x8000,0x1804,0x10020,0x60080,0x80200,0x100000,0x601000,0x10020,0x80220,0x1800020,0x11020,0x80200,0x3000080,0x4000000,0x80200,0x81200,0x18001000]),
([pw0,pw1,pw23,pw2,pw3,pw150,pw4,pw5],[236,13,9,5,21,17,29,25,308,41,37,53,49,1,312,77,73,84,81,89,85,97,93,128,1995,132,1987,101],[0x7,0x8,0x32,0xc2,0x100,0x602,0x1802,0x2000,0x34,0xc4,0x4000,0x604,0x1804,0x8020,0x10080,0x20000,0x40400,0x81000,0x100a0,0x100000,0x40420,0x9020,0x200000,0x10480,0x401080,0x1800400,0x6001000,0x8001400]),
([pw144,pw0,pw1,pw23,pw2,pw3,pw4,pw5],[4,13,124,0,9,164,132,12,20,77,17,97,25,73,105,37,49,296,33,21,29,41,1123,89,61,1091,81,1731,300,101],[0x7,0x38,0x1c4,0x600,0x3800,0xc000,0x10000,0x20012,0x40000,0x80402,0x101002,0x208002,0xc00002,0x1000000,0x80410,0x101010,0x208010,0x2800010,0x600,0x1800,0x4008000,0x18800000,0x1600,0x4008400,0x600,0x4009000,0x801800,0x20808000]),
([pw87,pw0,pw1,pw23,pw2,pw20,pw3,pw4],[49,13,53,9,89,17,132,25,93,37,101,2051,5,21,100,29,41,1,96,48,1627,73,81,77,97,105],[0x7,0xd,0x11,0x31,0x40,0x181,0x601,0x80a,0x1000,0x2022,0x4000,0x8082,0x10202,0x20000,0x2028,0x40000,0x8088,0x10208,0x180020,0x4000,0x200080,0x400200,0x800000,0x2000a0,0x400220,0x1000080,0x2000200,0x200280]),
([pw87,pw0,pw1,pw23,pw2,pw3,pw4],[48,49,13,53,100,9,96,89,77,17,97,25,93,105,37,101,316,5,21,29,1187,320,41,1191,1,1155,1159,73,2115,1795,1875,2179,81,2119,1799,1867,2183,85],[0x1f,0x6b,0x93,0x382,0x1c02,0xe002,0x10074,0x20010,0x50205,0x380804,0xe04004,0x1000040,0x250220,0x2090820,0x4414020,0x10311,0xf8000800,0x1f00004000,0x8000b00,0x2100004200,0x108004800]),
([pw0,pw1,pw2,pw3,pw4,pw79,pw145],[69,57,9,13,17,21,48,276,97,137,304,37,41,141,132,5,49,53,232,145,149,140,1,77,81,85,24,93,2267,324,12,169,2327,25,1543,89],[0xf,0xf8,0x788,0x3808,0xc000,0x3000a,0x40074,0xc0104,0x101804,0x600000,0x30005,0x800550,0x3000810,0x1c000050,0x810050,0x21000d00,0x1c8000500,0x200004000,0x29000800,0x21010800,0xc48010400]),
([pw0,pw1,pw2,pw20,pw3,pw150,pw4,pw5],[1,9,5,13,33,29,25,2403,41,37,53,49,61,2371,77,17,73,1755,81,89,116,2451,12,105,328,2499,97,93,120,2571,100,2627,101],[0x7,0xc,0x10,0x64,0x80,0x304,0xc04,0x3,0x1000,0x61,0x2000,0x301,0xc01,0x4000,0x18040,0x20000,0x48200,0x88800,0x300040,0x400000,0x800200,0x3000800,0x4000000,0x10240,0x8000840,0x30000200,0xc0000800,0x100000a00]),
([pw0,pw1,pw2,pw3,pw150,pw4,pw5],[1,5,9,13,17,21,25,29,33,308,2723,45,37,41,117,49,53,137,61,236,2691,65,133,145,73,77,328,2459,85,81,136,89,116,2451,97,93,16,2763,2827,20,2755,2819,101,105],[0xf,0x3a,0x1c2,0xe00,0x7002,0x38002,0x35,0x400c1,0x380000,0x403001,0x818001,0x3000050,0x1c000000,0x64001010,0x82008010,0x700000000,0x21001040,0x904008040,0x7040001000,0x38004008000,0xc0000009000]),
([pw144,pw0,pw1,pw2,pw3,pw39,pw4,pw5],[137,13,145,9,77,17,124,25,1555,20,105,37,49,33,21,29,57,41,89,69,85,81,97,2307,160,2891,2435,300,101],[0x3,0xc,0x30,0x1c0,0x200,0xc00,0x1000,0x200a,0x4022,0x8082,0x10000,0x20802,0x40003,0x4028,0x8088,0x80000,0x20808,0x4000c,0xb0,0x100020,0x200820,0x30,0x400000,0x200880,0x840080,0x3000800,0xc040000,0x10040800]),
([pw144,pw0,pw1,pw2,pw3,pw4,pw5],[57,20,13,124,5,69,0,9,164,1,77,8,17,328,97,12,25,152,73,105,16,37,160,2435,304,49,61,33,21,113,29,41,141,89,332,300,129,149,296,81,85,101],[0x1f,0x3e0,0x3c00,0x7c000,0x780000,0x3800000,0xc000084,0x30001004,0x48010004,0x180200004,0xe00000005,0x1010001080,0x44010080,0x2080200080,0x42000000a0,0x33400,0x18000201000,0xa00003400,0x8000214000,0x200034000,0x20200280000]),
([pw87,pw0,pw1,pw2,pw20,pw3,pw4],[320,49,5,53,100,316,1,96,48,17,89,2947,20,97,25,93,105,37,101,9,13,21,57,29,113,41,117,69,129,133,1627,77,73,2243,81,2247,3011,2499,2887,3099,3015,2503,2883,3103],[0x1f,0xea,0xf02,0x1010,0xe002,0x70002,0x180044,0x300204,0x400010,0x1804004,0x6020004,0x280240,0x8000080,0x10804040,0x22020040,0xc0000100,0x300004300,0xc00020300,0xf000006000,0xf0000030000,0x500024000]),
([pw87,pw0,pw1,pw2,pw3,pw4],[96,57,49,320,5,53,100,33,69,316,1,77,48,17,89,3139,97,3203,25,93,3271,3331,3143,105,3207,37,101,3267,3335,9,13,21,29,113,41,117,129,133,73,81,85,3395,3459,3531,3539],[0xff,0x765,0x7844,0x3f8004,0x1fc00004,0x60000651,0xc0002051,0x300040019,0xc02000019,0xa0002440,0x1100040640,0x2402000640,0x4000043840,0x18002003040,0x1ec002040000]),
([pw0,pw1,pw23,pw2,pw143,pw3,pw4,pw5],[336,13,9,5,21,17,4,88,29,25,931,81,53,49,1,0,56,899,340,3611,128,16,8,73,1475,120,89,77,105,97,37,132,3651,93,101],[0x7,0x8,0x32,0xc2,0x302,0xc02,0x3002,0x4000,0x34,0x18004,0x304,0x20804,0x3004,0xc0020,0x700080,0x800200,0x3000800,0x4002000,0x8000000,0x800220,0x10000820,0x4002020,0x20000200,0x50000800,0x180002000,0x800200,0x200002200,0x400002800]),
([pw113,pw0,pw1,pw23,pw2,pw3,pw4,pw5],[4,13,0,9,344,77,17,73,25,37,49,348,45,21,29,1003,81,995,89,65,971,963,1547,156,1539,352,85,93,101],[0x7,0xd,0x10,0x60,0x180,0x200,0x400,0x80a,0x1000,0x2042,0x4102,0x18002,0x60002,0x80000,0x2048,0x4108,0x110008,0x240008,0x60,0x180,0xc10000,0x3040000,0x1c0,0x4010040,0x60,0x180,0x8040100,0x10050000]),
([pw137,pw22,pw0,pw1,pw2,pw3,pw4,pw5],[348,132,16,20,141,13,45,149,9,65,77,17,73,25,81,3595,128,49,57,69,37,89,3587,21,29,85,93,101],[0xf,0x70,0x380,0xc00,0x3000,0x1c000,0x20000,0x40030,0x80180,0xc00,0x3000,0x100000,0x600002,0x130,0x800820,0x1002020,0x4030,0x200030,0x800900,0x1002100,0x4180,0x200180,0x3800,0x2004800,0xc00,0x3000,0x4202000,0x8204000]),
([pw137,pw0,pw1,pw2,pw3,pw159,pw4,pw5],[57,13,33,69,9,61,77,17,152,3731,25,12,81,37,1483,21,29,41,85,73,93,89,156,3779,101],[0x7,0x38,0xc0,0x700,0x800,0x3000,0x4000,0x13,0x8082,0x10402,0x3,0x22002,0x3,0x8090,0x10410,0x18,0x22010,0x18,0x4c0,0x40080,0x3080,0xc0,0x80000,0x3400,0x300400,0xc02000,0x300000,0x1202000]),
([pw0,pw1,pw2,pw143,pw3,pw4,pw5],[1,5,9,13,17,21,16,45,88,33,25,29,113,81,356,120,49,53,141,0,65,56,61,129,336,149,340,3739,77,73,136,105,89,360,97,12,8,37,20,3843,3907,93,101],[0xf,0x3a,0x3c2,0x1c02,0xe082,0x70002,0x35,0x780001,0x800c01,0x1102001,0x2030001,0x1c000000,0x64000410,0x8400a010,0x304010010,0xc40000400,0x308400a000,0x1c200010000,0x6000a400,0x20400010400,0x40080012000]),
([pw113,pw137,pw0,pw1,pw2,pw3,pw4,pw5],[16,57,13,69,9,77,17,73,25,37,3587,45,65,81,3723,156,1539,21,29,141,149,85,93,89,101],[0x1,0x6,0x18,0x60,0x180,0x200,0x400,0x806,0x1018,0x60,0x180,0xe000,0x10000,0x16,0x20044,0x40104,0x82004,0x6,0x20050,0x40110,0x102010,0x18,0x1c0,0x202040,0x60,0x180,0xc00100,0x1802000]),
([pw113,pw0,pw1,pw2,pw3,pw4,pw5],[45,4,13,0,5,65,9,1,77,8,17,360,73,12,25,160,3723,156,37,3715,352,49,21,117,29,137,81,364,89,57,133,145,348,69,105,85,93,97,101],[0x1f,0xea,0xf00,0xf000,0x70000,0x380000,0x65,0xc00404,0x3004004,0xc020005,0x38100004,0x40400440,0x81004040,0x104000060,0x310000040,0x5500,0xc04000400,0x10100d00,0x402d000,0x3010004000,0x4414000000]),
([pw0,pw23,pw2,pw3,pw35,pw46,pw4,pw5],[5,13,1243,77,1235,73,3971,288,164,9,41,37,53,49,61,1,84,81,89,121,17,124,25,88,93,0,101],[0x1,0xe,0x32,0xc2,0x302,0xc02,0x3002,0xc000,0xc000,0x18000,0x18200,0x28800,0x4a000,0x80028,0x100000,0x200000,0x20808,0x42008,0x400000,0x800000,0x20820,0x1002020,0x2000000,0x20800,0x42000,0xe00,0x3200,0x4002800]),
([pw0,pw1,pw114,pw23,pw2,pw3,pw4,pw5],[368,13,9,0,4,45,1323,77,1315,73,41,37,53,49,65,1291,1283,372,124,17,88,25,4043,128,4035,132,1931,84,1923,81,89,85,93,101],[0x7,0x1a,0x20,0xc2,0x302,0xc02,0x3002,0x1c,0x4000,0x8084,0x10204,0xc04,0x3004,0x20000,0xc0080,0x300200,0xc00800,0x3002000,0xc000080,0x18000200,0x20000800,0x40002000,0x80000280,0x20000880,0x40002080,0x20000a00,0x100002200,0x200002800]),
([pw0,pw1,pw2,pw3,pw35,pw150,pw4,pw5],[1,9,5,13,33,45,41,37,53,49,61,65,121,77,73,17,376,81,89,25,380,93,372,28,4107,24,4099,101],[0x7,0xc,0x14,0xc,0x20,0xc4,0x304,0x3,0x401,0x3,0x800,0xc1,0x301,0x7000,0x8000,0x10000,0x22080,0x42200,0x80000,0x100000,0x24080,0x204200,0x400000,0x20080,0x40200,0x1800080,0x6000200,0x8000280]),
([pw113,pw0,pw1,pw2,pw3,pw4,pw5,pw141],[45,13,5,65,9,1,77,17,73,25,384,324,21,29,57,69,85,97,189,105,101,81,89],[0x7,0x38,0xc0,0x300,0x400,0x800,0x400,0x13,0x1082,0x2202,0x3,0x4002,0x3,0x1090,0x2210,0x18,0x8010,0x18,0x380,0x10080,0xc0,0xc0,0x300,0x20200,0x300,0x1c0000,0x200000,0x400000]),
([pw160,pw0,pw1,pw23,pw2,pw3,pw4,pw5],[236,288,17,77,25,73,37,81,49,89,308,13,9,45,21,29,41,53,65,93,101],[0x1,0x2,0x1,0xc,0x30,0xc0,0x300,0x1c00,0x2000,0x4804,0x8810,0x10840,0x20900,0x40000,0x5004,0x9010,0x11040,0x21100,0xc,0x30,0xc0,0x300,0x34,0xc4,0x10c,0x70,0x80110,0x100140]),
([pw0,pw1,pw2,pw3,pw4,pw74,pw75,pw107],[57,451,69,17,21,29,97,37,41,33,153,53,208,145,157,140,1,132,4175,77,81,25,93,49,164],[0x7,0x18,0x61,0x180,0x200,0xc01,0x1000,0x18,0x2024,0x180,0xc004,0x10000,0x60004,0x80028,0x100088,0x18,0x18,0x18,0x1000a0,0x8020,0x860,0x200000,0x180,0x180,0x180,0x408800,0x800000,0x1020800]),
([pw0,pw1,pw2,pw3,pw4,pw74,pw139],[61,57,388,232,515,17,21,204,25,137,176,37,41,141,208,5,4,165,53,4271,129,97,69,149,93,49,1,77,81,85,132,29,180,124],[0x1f,0xe6,0x706,0x3802,0xc000,0xf0006,0x100061,0x600101,0x801801,0x3400001,0x4004000,0x80005a0,0x30000820,0x3000060,0x400e0,0x10200900,0x3200100,0xc0000000,0x102001800,0x100041800,0x202050000]),
([pw109,pw0,pw1,pw2,pw32,pw4,pw5],[57,25,33,12,5,145,0,61,17,21,392,164,97,132,29,37,41,216,224,53,296,643,113,141,49,129,208,1,89,81,85,77,101,105],[0x1f,0xe2,0xf02,0x7002,0x38802,0xc0800,0x300884,0x400304,0x5005,0x818004,0x1000805,0x2000380,0xc000000,0x38080,0x110000a0,0x4700,0x60008100,0x91000100,0x1d000,0x11005000,0x301008000]),
([pw137,pw0,pw1,pw2,pw3,pw4,pw74,pw79],[57,53,153,9,69,17,77,25,73,37,81,49,132,20,21,29,41,13,140,96,4291,89],[0x7,0x1a,0x62,0x182,0x602,0x1802,0x2000,0x19,0x4020,0x8080,0x10200,0x20000,0x1000,0x4028,0x8088,0x10208,0x40008,0x40000,0x1a0,0x620,0x4020,0x180020,0x380,0x8080,0x180,0x10200,0x600,0x200000]),
([pw0,pw1,pw2,pw3,pw4,pw74,pw79,pw145],[57,9,69,17,21,137,97,37,41,13,132,165,53,145,157,140,1,77,81,24,4379,208,4439,25,93,49,396],[0x7,0x18,0x61,0x180,0x200,0x400,0x1801,0x1a,0x2042,0x182,0xc002,0x10000,0x1006,0x20008,0x40088,0x18,0x180008,0x21008,0x40080,0x8040,0x600040,0x800000,0x180,0x40080,0x41080,0x1000000,0x2009000,0x4201000]),
([pw0,pw1,pw2,pw20,pw3,pw42,pw4,pw5],[1,9,5,109,21,33,29,73,13,41,37,53,49,61,129,88,2371,77,17,81,89,84,4499,236,0,12,105,244,4547,25,93,101],[0x7,0x1c,0x20,0xc4,0x100,0x604,0x1804,0x3,0x2000,0x4041,0x18001,0x601,0x1801,0x20000,0xd0,0x40000,0x80410,0x101010,0x600040,0x3a00000,0x4000400,0x18001000,0x20000000,0x4c0,0x40001040,0x600,0x1800,0x80001400]),
([pw0,pw1,pw2,pw30,pw3,pw150,pw4,pw5],[1,9,5,109,21,13,29,25,400,41,37,53,49,61,65,17,73,404,81,89,124,97,93,188,4619,24,4675,101],[0x7,0x1c,0x20,0xc4,0x100,0x604,0x1804,0x3,0x2001,0xc1,0x4000,0x601,0x1801,0x8000,0x10090,0x20000,0x40410,0x81010,0xc0,0x100000,0x600,0x1800,0x200000,0x10480,0x401080,0x1800400,0x6001000,0x8001400]),
([pw144,pw0,pw1,pw2,pw3,pw31,pw4,pw5],[137,33,69,9,1,77,17,12,29,396,208,124,0,20,105,37,49,61,21,193,13,41,89,81,25,4419,4483,300,101],[0x3,0x1c,0x60,0x380,0x3c00,0xc000,0x10000,0x2000a,0x40040,0x80102,0x100000,0x208002,0x400003,0x40048,0x20108,0xc,0x208008,0xc,0x160,0x40040,0x808040,0x60,0x1000000,0x808100,0x2400100,0x208000,0xc400000,0x10408000]),
([pw87,pw0,pw1,pw2,pw30,pw20,pw3,pw4],[49,5,53,1,21,89,24,25,93,37,101,9,109,13,100,29,41,96,69,17,4315,73,81,97,105],[0x7,0xd,0x31,0x5,0x40,0x181,0x601,0x80a,0x1012,0x2000,0x4000,0x8082,0x10202,0x808,0x20008,0x40000,0x8088,0x10208,0x80000,0x100000,0x200090,0x400210,0x4000,0x8080,0x10200,0x800080,0x1000200,0x200280]),
([pw87,pw0,pw1,pw2,pw30,pw3,pw4],[96,49,5,53,100,69,1,21,89,4739,316,97,25,93,105,37,101,9,109,13,29,113,41,117,129,133,17,73,4355,81,4359,4547,4859,4551,4863],[0x1f,0x6a,0x383,0x41b,0x3802,0x1c002,0x20445,0x40095,0x80010,0x301004,0xc08004,0x204c1,0x471,0x1101040,0x2408040,0x4000001,0x18001081,0x60008081,0x180101001,0x600408001,0x28009000]),
([pw0,pw1,pw2,pw161,pw3,pw4,pw5],[1,5,164,13,77,21,0,84,25,29,33,37,41,117,49,53,137,65,236,9,129,69,17,73,81,216,89,16,20,408,93,101,105],[0xf,0x3a,0xca,0x702,0x3802,0x1c002,0x60021,0xe0041,0x100301,0x21801,0x20c001,0x400004,0x800130,0x3000820,0x4004030,0x344,0xa001800,0x3000c000,0x1800900,0x60004104,0x180004800]),
([pw41,pw0,pw1,pw3,pw35,pw4,pw5],[13,77,5,8,56,32,1,12,121,73,17,84,21,37,41,196,49,24,53,61,109,117,96,65,412,69,88,25,192,81,93,89,101,105],[0xf,0x70,0x392,0x1c02,0xe012,0x70002,0x80015,0x100214,0x1405,0x206004,0x450014,0x1880200,0x881400,0x886000,0x20d0000,0xc000000,0x3000a200,0x40410200,0x2000a400,0x80410400,0x300012000]),
([pw0,pw1,pw2,pw3,pw18,pw75,pw141],[69,45,416,420,771,17,21,117,25,29,424,344,5,101,141,49,41,428,145,105,149,140,1,73,77,188,208,432,132,189,20,37,16],[0x1f,0xe2,0x706,0x1800,0x6006,0x18802,0x20069,0x40301,0x180009,0x600000,0x18801,0x1800120,0xa0060,0x2002060,0x1030020,0x4080300,0x2700,0x810500,0x38082000,0xc0098000,0x10001a000]),
([pw0,pw1,pw2,pw30,pw3,pw95,pw142,pw5],[5,835,65,109,21,45,29,25,41,81,188,53,49,133,1,197,37,85,73,432,89,56,16,93,88],[0x7,0x19,0x20,0xc1,0x301,0x400,0x1801,0x2014,0x2004,0xc0,0x4000,0x18004,0x1800,0x20000,0x40090,0x310,0x80000,0x101010,0xc0,0x200100,0x400000,0x1800,0xc0,0xc0,0x801080,0x1010100,0x1900,0x11800]),
([pw162,pw0,pw1,pw2,pw3,pw4,pw5,pw75],[13,33,5,300,17,21,25,29,37,41,436,57,49,157,69,1,77,81,97,105,89],[0x7,0x8,0x30,0xc0,0x300,0x400,0x400,0x3,0x31,0xc1,0x301,0x1801,0x3,0x30,0xc0,0x300,0x7000,0x8000,0x10050,0x20110,0x11010,0x30,0x20140,0x41040,0xc0,0x81100,0x300,0x100000]),
([pw0,pw1,pw2,pw3,pw4,pw74,pw145,pw139],[57,1219,61,17,21,137,97,37,41,5,208,140,4911,69,1,77,81,169,93,25,132,49,124,53],[0x7,0x18,0x61,0x180,0x200,0x401,0x1801,0x18,0x2004,0x180,0x2004,0x404,0x4000,0x8008,0x10088,0x18,0x8008,0x18,0x10080,0x60040,0x80000,0x100000,0x180,0x10080,0x180,0x240400,0x440800,0x800000]),
([pw51,pw0,pw1,pw2,pw31,pw4,pw5],[84,4,201,33,29,288,1,17,77,12,21,25,73,164,37,81,240,49,89,244,65,9,440,312,113,109,5,41,53,137,69,101,105],[0x1f,0x61,0x790,0x3811,0x1c011,0xe0011,0x700008,0x3800089,0x4000001,0x8014008,0x30020008,0x200181,0x301800,0x8304000,0x50220000,0x1980,0x1c081,0x60180,0x8005800,0x100a0800,0x180024000]),
([pw36,pw0,pw1,pw2,pw30,pw3,pw4,pw5],[4,5,84,1,8,21,164,88,12,0,25,29,37,41,49,53,1347,65,109,13,4171,2371,236,17,73,81,89,93,101],[0x7,0x8,0x70,0x384,0xc00,0x3000,0xc000,0x30002,0x40022,0x80000,0xc02,0x3002,0xc002,0x120020,0x620000,0xc00,0x3000,0xc000,0x800000,0x1000420,0x2001020,0x4004020,0xc00,0x3000,0xc000,0x1001400,0x8004400,0x10005000]),
([pw0,pw1,pw2,pw3,pw42,pw150,pw4,pw5],[1,9,5,33,21,29,13,4963,41,37,53,49,61,236,2691,65,73,17,4507,81,77,25,4499,93,0,240,5003,244,4995,101],[0x7,0x1c,0x2c,0x40,0x80,0x304,0xc04,0x3,0x1021,0x6001,0x8000,0x301,0xc01,0x10030,0x20000,0x40000,0x80210,0x100810,0x200000,0x400000,0x10220,0x800820,0x1000000,0x300,0xc00,0x6000200,0x18000800,0x20000a00]),
([pw36,pw0,pw1,pw2,pw3,pw42,pw4,pw5],[164,5,84,1,21,29,56,0,37,41,49,53,1411,65,33,13,4235,4227,2691,236,73,17,81,77,25,93,101],[0x7,0x8,0x15,0x64,0x80,0x300,0xc00,0x3002,0x4012,0x4022,0x8000,0x302,0xc02,0x12010,0x22020,0xc2000,0x300,0xc00,0x100030,0x200000,0x400110,0x800410,0x1000000,0x100120,0x2000420,0x300,0xc00,0x4000500]),
([pw36,pw0,pw1,pw2,pw3,pw4,pw5],[13,0,5,84,2691,236,1,17,21,164,25,29,56,37,16,41,196,49,20,53,408,65,312,33,117,137,192,69,73,77,81,89,93,101,105],[0xf,0x70,0x382,0x1c02,0x1e000,0x1e0000,0x600025,0x185,0x800c04,0x100a004,0x20a0004,0x3001a0,0x4200c20,0x820a000,0x82a0000,0x30000480,0x40112080,0xa0020080,0x50002400,0x104120400,0x600022000]),
([pw0,pw163,pw1,pw2,pw3,pw4,pw5],[124,5,61,33,9,13,17,21,113,25,29,37,41,444,89,53,300,69,0,1,77,8,328,97,12,73,105,16,20,49,436,296,129,149,81,85,101],[0x3,0x3c,0x1e0,0x628,0x3820,0x1c020,0xe0011,0x700040,0x3800201,0xc002800,0xf000c000,0x1000000d0,0x614,0x200001810,0x28011,0x500241,0xc00000840,0x10c040,0x400800a00,0x808201,0x1004008800]),
([pw0,pw1,pw2,pw3,pw42,pw46,pw4,pw5],[1,3971,5,33,13,164,4963,41,37,53,49,61,124,4931,9,121,73,77,17,21,81,89,25,29,93,236,4,0,101],[0x7,0xc,0xc,0x10,0x64,0x184,0x604,0x801,0x801,0x3001,0x4000,0x181,0x601,0x38000,0x40000,0x80000,0x120100,0x220400,0x400000,0x800000,0x110100,0x1010400,0xe001000,0x180,0x600,0x180,0x600,0x10000500]),
([pw36,pw0,pw1,pw2,pw3,pw35,pw4,pw5],[13,5,1,8,77,164,12,73,56,84,4,0,37,41,49,53,33,65,4875,4867,4931,236,121,17,81,89,25,93,101],[0x3,0x4,0x38,0x1c0,0xe20,0x3000,0xc000,0x3,0x3,0x10002,0x3,0x3002,0xc002,0x60010,0xa0080,0x320000,0x3000,0xc000,0x400090,0x800000,0x1001010,0x2004010,0x4000000,0x1001080,0x8004080,0x1001000,0x2004000,0x10005000]),
([pw0,pw164,pw1,pw2,pw3,pw4,pw5],[84,13,65,5,9,236,17,33,21,25,29,37,41,117,49,53,137,0,1,16,240,20,244,69,73,77,81,89,93,101,105],[0x3,0x3c,0x1c8,0x688,0x3808,0x1c008,0x60034,0x20141,0x20601,0x181800,0x60c000,0x151,0x611,0x1814,0x80c010,0x3000240,0x4100841,0xa004040,0x5000a00,0x10404201,0x60004800])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C7x0 : levelOK true p7_T p7_t 6 p7_N6 p7_D7_0 = true := by decide +kernel
def p7_B7 : List (List StD) := [p7_D7_0]
def p7_N7 : Array (List Nat) := mkNext p7_B7
theorem p7_I7 : LevelB true p7_T 7 p7_B7 := levelStepB p7_B p7_W p7_I6 (by
  intro c hc
  unfold p7_B7 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p7_C7x0
  cases hc
  )
def p7_D8_0 : List StD := [
([pw0,pw23,pw2,pw28,pw3,pw4,pw5],[0,5,88,17,13,56,92,32,27,4,9,25,29,75,37,41,83,49,96,53,48,100,8,125,1,155,104,73,195,129,275,108,81,199,133,267,89,21,347,351,387,451,563,391,455,555,112,93,97,101,105],[0x3,0x1fc,0x6b4,0x3870,0x1c070,0x3e0070,0x3c0008c,0x14006a4,0x7d000800,0xf81004000,0x1001320000,0x2000000001,0x400800088c,0x810000408c,0x100032008c,0x70004001c04,0x38008000c404,0x3a0404,0x40018c004800,0x1800004320800,0x6000080324000]),
([pw0,pw1,pw23,pw2,pw20,pw3,pw4,pw5],[56,88,60,13,9,5,17,21,32,25,29,235,92,37,41,243,49,53,48,1,203,211,603,667,8,73,116,707,787,81,120,711,779,89,100,77,859,863,97,124,899,979,105,128,903,971,132,44,1027,1091,93,101],[0x1f,0x22,0x1cc,0x2,0x1e08,0xf008,0x71008,0x80001,0x1d4,0x1,0x100614,0x206014,0x70014,0xc00142,0x1000002,0x1e000200,0x1e0002000,0x600050000,0x800400100,0x1002000340,0x2020002140,0x200050140,0x3c000000200,0x3c0000002000,0x3c00000050000,0x22002200,0x4004000010200,0x8040000012000]),
([pw0,pw1,pw2,pw20,pw3,pw4,pw5],[88,1,5,60,9,13,56,17,21,33,25,92,29,113,116,37,41,117,120,49,96,53,48,100,61,129,133,32,667,77,73,1179,81,1183,89,97,12,1219,1283,1363,1427,105,16,1223,1287,1355,1419,20,1475,1539,136,93,101],[0x7f,0x1e5,0x201,0x7c44,0x78844,0xf80844,0x193,0x1000040,0x200140b,0x401800b,0xe8000b,0x38000000,0xc8000481,0x308008081,0x408c80081,0x1f800004400,0x7e0000048000,0x3800000c80000,0x400014004c400,0x8000800c84400,0x10020000cc8000]),
([pw137,pw0,pw1,pw23,pw2,pw3,pw4,pw5],[44,4,13,0,132,9,140,20,77,88,17,48,73,124,25,1611,1671,81,128,37,1619,1667,579,49,144,57,21,29,291,148,41,295,89,163,69,259,263,131,100,152,771,1735,156,775,1731,643,85,93,97,101,105],[0x1f,0x6b,0x90,0xf00,0x1f000,0x3e0000,0xc00001,0x1000074,0x2000010,0x4000c04,0x38004004,0xe0080004,0x321000005,0x400000040,0x5000c20,0x809004020,0x1041080020,0x2101000021,0x4000000d00,0x38000005000,0x1c00000a0000,0x200100400011,0x5500,0x4000000a0400,0x100000d01,0xa5000,0x1800100004000,0x6000100080000]),
([pw137,pw0,pw1,pw2,pw3,pw4,pw5],[140,57,20,144,13,0,132,5,69,9,4,1,100,77,8,48,17,152,73,12,1795,25,1867,1927,1991,156,81,16,1799,37,1875,1923,1987,44,643,49,96,21,148,29,137,41,141,89,145,149,85,160,93,97,101,105],[0xff,0xf69,0x1f000,0x1fe0000,0x1fe000000,0xe00000000,0x35b,0x7000019011,0x1c000220011,0x64022000011,0x84200000053,0x2000019248,0x108000200248,0x220020000248,0x80000000348,0x27b000,0x400026019000,0x8020001b040,0x800026260000,0x3080200220040,0xc080220000040]),
([pw0,pw1,pw23,pw2,pw3,pw35,pw4,pw5],[164,124,76,13,9,5,77,80,32,379,73,36,371,4,2083,483,37,41,52,49,53,48,1,347,339,0,2051,451,8,859,1179,12,851,1171,2115,84,899,2179,1283,1687,2263,2007,2307,81,28,89,24,88,121,17,25,93,128,132,101,105],[0x1f,0x22,0x3c8,0x1c88,0xe088,0x70088,0x380088,0x400001,0x800154,0x1000c14,0xe000014,0x70014,0x380014,0x70000140,0x380000c00,0x7fc00000000,0x180000050000,0x600000280000,0x1800000000442,0x2000000000002,0x80000050140,0x200000280140,0x4800000000000,0x80000050c00,0x8000000280c00,0x10080000050000,0x20200000280000,0xc0000000090000]),
([pw0,pw1,pw2,pw3,pw4,pw74,pw75],[132,69,57,168,172,3,140,24,17,21,25,29,137,37,41,141,20,5,4,153,53,145,149,0,157,49,1,73,77,81,85,176,180,2371,2467,2519,2403,2435,2551,2375,2471,2511,2407,2439,2543],[0x7f,0x384,0x1c54,0xe054,0x30000,0x1c004d,0x382,0x200c0b,0x40600b,0x380004b,0x4010000,0x18000580,0x60002180,0x2000380,0x100380,0x1a8002400,0xe82000c40,0x7080100c01,0x38102006040,0x1c0100106001,0x2940049]),
([pw0,pw1,pw2,pw30,pw20,pw3,pw4,pw5],[1,5,9,60,56,88,109,21,13,25,29,113,37,41,117,49,53,96,61,129,133,17,2587,184,73,2651,81,2655,89,0,2691,116,2695,120,100,97,84,2755,2835,105,188,2759,2827,24,2883,2947,93,101],[0x1f,0xf2,0x120,0x20,0xe02,0x7002,0x38012,0x9d,0x31,0x40010,0x80601,0x103001,0x38001,0x200010,0xc00010,0x3000290,0xc001090,0x10028090,0x20000020,0xc0000610,0x300003010,0x400038010,0x7800000200,0x78000001000,0x380000028000,0x5001200,0x400800008200,0x808000009000]),
([pw41,pw0,pw1,pw2,pw3,pw4,pw5],[56,13,0,5,8,88,60,1,17,21,4,25,12,29,3019,37,16,41,3027,49,20,53,96,61,113,117,65,100,69,73,3075,81,3079,89,192,196,93,97,101,105],[0x3f,0xc1,0x725,0x7801,0x78001,0x780001,0x80002b,0x32b,0x1002809,0x2028009,0x680009,0x800321,0x4802860,0x4828060,0x18a80020,0x60000921,0x180008121,0x200480121,0xca0008800,0x3008480800,0xc008488000]),
([pw0,pw1,pw2,pw30,pw3,pw32,pw4,pw5],[61,5,200,60,67,164,84,109,21,13,25,113,64,4,37,41,117,49,53,204,129,0,88,161,1,72,145,17,3159,8,3247,2459,81,89,12,3207,2483,56,124,2755,2795,1283,3283,3323,28,208,29,93,188,24,101,105],[0x1f,0x1e2,0x240,0x1c06,0x2806,0x1c002,0xe0006,0x100109,0x300009,0xc00441,0x1000040,0x200c009,0x4060001,0x8000020,0x10081500,0xe0080100,0x102084100,0x2000a0100,0x1c00001400,0xfe000000000,0x10000200c000,0x2000000e0000,0x400000400000,0x102005400,0x8000000a1400,0x100000200c000,0x20000000e0000,0xc000000024000]),
([pw0,pw1,pw2,pw3,pw4,pw74,pw145],[140,1,57,212,9,355,24,17,21,208,97,164,137,37,216,41,141,220,20,5,4,165,53,224,3155,61,228,65,93,2627,1155,232,3099,3331,2435,3407,77,81,85,12,169,25,49],[0x3f,0x1c4,0x1e0d,0x3e005,0xc0000,0x70020d,0x1d2,0x3800602,0xc02a002,0x1f0000013,0xe82400202,0x10000004c0,0x60000020c0,0x100001c0,0x10004000c0,0x2004822600,0x18010800601,0x20000040000,0x1402a001,0x2004422200,0x48010d00201]),
([pw0,pw1,pw2,pw30,pw3,pw42,pw4,pw5],[1,5,9,419,56,164,84,109,21,33,73,29,113,37,41,117,49,53,96,2395,61,2691,236,3207,64,88,65,2755,3459,69,77,81,72,89,12,240,244,25,93,188,24,101,105],[0x1f,0x1e2,0x240,0x1c02,0x40,0xe002,0x70012,0x80115,0x700011,0x1900801,0x1e000001,0x4006001,0x20030001,0x40000020,0x1000d10,0x20,0x180002110,0x200050110,0x850,0x400000040,0x900006010,0x1000070010,0x2000000010,0x80002c00,0x4000050800,0x8100006000,0x10000070000,0x60000012000]),
([pw0,pw1,pw2,pw3,pw42,pw4,pw5],[164,1,5,80,9,483,236,84,77,33,56,21,73,29,13,37,216,41,117,240,49,96,53,137,244,248,2491,64,2483,61,0,65,3523,1283,3587,3651,72,252,69,17,81,89,25,93,16,20,101,105],[0x7f,0xf85,0x3285,0x4080,0xf8005,0x1f00005,0x60008d2,0x380020c2,0xfc0000042,0x10800a8042,0x6001500042,0x3980,0x8000000001,0x11002088880,0x20001100980,0x40000000400,0x1000008b080,0x82009102080,0x1010000a8000,0x202001500000,0xc02001188000]),
([pw109,pw0,pw1,pw2,pw3,pw4,pw5],[140,57,20,164,33,12,208,5,1,0,9,3747,17,8,21,252,97,29,4,25,37,16,41,216,224,53,515,113,141,49,244,2499,61,220,65,89,69,77,81,85,101,105],[0xff,0xf08,0xf008,0xf0069,0xf00008,0x3000008,0x4000519,0x8005019,0x3005b,0x10500019,0x2000005b,0x4000d500,0x180020148,0x600d00100,0x1820008140,0x2000029048,0xc240901000,0x2860001040,0x4000130048,0x20030048,0x30220100040]),
([pw0,pw1,pw2,pw3,pw35,pw42,pw4,pw5],[1,5,9,2083,80,77,33,64,84,73,248,164,13,37,41,117,49,53,137,3387,3379,61,3779,236,124,65,2179,3843,69,121,21,81,240,89,244,29,56,93,4,28,24,101,105],[0x1f,0x1e2,0x742,0x902,0x1100,0xe002,0x70002,0x80125,0x300301,0xc00105,0xf000001,0x2006001,0x10030001,0x20000320,0x40000100,0x900,0x180002120,0x600010120,0x800000100,0x1000000100,0x180002300,0x2400010300,0x4000000900,0x180002100,0x600010100,0x8100006000,0x10400030000,0x60000012000]),
([pw51,pw0,pw1,pw2,pw3,pw4,pw5],[84,13,4,5,3907,76,1,17,0,77,12,21,25,73,8,29,37,16,81,240,49,20,89,244,124,65,9,3403,3395,33,41,45,53,57,69,93,101,105],[0x1f,0x61,0xf81,0xf101,0xf0001,0xf00001,0x700002a,0x800008b,0x30001009,0xc0090008,0x300900008,0x4000281,0x4003001,0x47090000,0x505900000,0x3281,0xd0081,0x500281,0x53001,0x800901001,0x3000910000])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C8x0 : levelOK true p7_T p7_t 7 p7_N7 p7_D8_0 = true := by decide +kernel
def p7_B8 : List (List StD) := [p7_D8_0]
def p7_N8 : Array (List Nat) := mkNext p7_B8
theorem p7_I8 : LevelB true p7_T 8 p7_B8 := levelStepB p7_B p7_W p7_I7 (by
  intro c hc
  unfold p7_B8 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p7_C8x0
  cases hc
  )
def p7_D9_0 : List StD := [
([pw0,pw1,pw23,pw2,pw3,pw4,pw5],[0,4,13,9,5,17,21,35,25,29,43,37,41,51,49,53,59,1,3,11,19,27,32,77,8,67,131,219,283,36,73,12,75,139,211,275,40,81,16,83,147,203,267,44,89,20,91,155,195,259,323,327,85,48,52,335,93,97,343,101,105],[0xf,0x11,0xe6,0x706,0x3806,0x1c006,0x20003,0x40069,0x80309,0x101809,0x20c009,0x1fc00020,0xfe0000100,0x7f000000800,0x3f80000004000,0x4000060c00120,0x18003000400820,0x20180000c04020,0x40003060000900,0x380080020004100,0x1c00081000004800]),
([pw0,pw1,pw2,pw30,pw3,pw4,pw5],[4,1,5,9,35,8,109,21,13,25,29,113,37,41,117,49,53,24,411,56,0,61,451,131,60,515,579,64,583,65,68,69,17,73,667,81,671,89,12,707,771,851,16,711,775,843,20,72,93,97,101,105],[0x1f,0xe5,0x120,0xe05,0x7005,0x38005,0x400aa,0x3f80002,0xd200602,0x71003002,0x80038002,0x100000021,0x6000002a0,0x18000010a0,0x20000280a0,0x3c008080600,0x3c0040083000,0x400000038000,0x800a48001200,0x3000000028200,0xc000000029000]),
([pw0,pw1,pw2,pw3,pw35,pw4,pw5],[76,1,5,323,9,13,80,8,77,667,12,73,659,33,84,4,899,771,995,28,37,41,45,24,49,53,57,699,691,61,0,931,803,963,65,69,121,17,81,89,25,93,16,20,101,105],[0x7f,0x3a4,0x3c04,0x7c064,0x780004,0x7800004,0x8000192,0x30000c02,0x3c0004013,0x400380002,0x803800002,0x1000000d80,0x2000000480,0x4000180180,0x8001800180,0x10000000080,0x4000180c00,0x20001800c00,0x44000180000,0x88001800000,0x300001900000])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C9x0 : levelOK true p7_T p7_t 8 p7_N8 p7_D9_0 = true := by decide +kernel
def p7_B9 : List (List StD) := [p7_D9_0]
def p7_N9 : Array (List Nat) := mkNext p7_B9
theorem p7_I9 : LevelB true p7_T 9 p7_B9 := levelStepB p7_B p7_W p7_I8 (by
  intro c hc
  unfold p7_B9 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p7_C9x0
  cases hc
  )
def p7_D10_0 : List StD := [
([pw0,pw1,pw2,pw3,pw4,pw5],[0,1,5,3,9,13,4,8,17,67,21,12,25,75,29,33,16,37,83,41,45,20,49,91,53,57,99,107,61,115,65,123,69,131,73,77,135,81,85,24,89,28,143,93,97,151,101,105],[0x7f,0x7e4,0xf844,0x1f0044,0x3e00044,0x4000593,0x18005803,0x600b0003,0x181600003,0xe00001980,0x7000030180,0x18800600180,0x22400031800,0x1c0000601800,0xe00000630000])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C10x0 : levelOK true p7_T p7_t 9 p7_N9 p7_D10_0 = true := by decide +kernel
def p7_B10 : List (List StD) := [p7_D10_0]
def p7_N10 : Array (List Nat) := mkNext p7_B10
theorem p7_I10 : LevelB true p7_T 10 p7_B10 := levelStepB p7_B p7_W p7_I9 (by
  intro c hc
  unfold p7_B10 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p7_C10x0
  cases hc
  )
theorem p7_L : LowN true p7_R p7_T 11 := lowSearchB p7_B p7_I10 (by decide +kernel)
def p8_T : Nat := 0xfffffffffffffffcfffffffefefaeea0fffffffffffffffcfffffffefefaeea0
def p8_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p8_E : List (Nat × Nat × Nat) := [(0,4,5),(1,8,10),(2,1,5),(3,1,9),(4,1,17),(5,1,33),(6,2,66)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw29,11,[5, 6, 1, 2, 4, 3])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p8_B p7_B p7_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[])]
def p8_t : Tabs := ((p8_C.map (mkCut true p8_Z)).toArray, #[(10,8),(5,4),(67,65),(7,6),(20,16),(9,8),(5,1),(10,2),(9,1),(20,4),(17,1),(17,16),(34,2),(33,1),(33,32),(66,2),(67,3),(7,3),(14,12),(19,3),(26,24),(34,32),(68,4),(14,6),(28,24),(36,4),(36,32),(68,64),(28,12),(26,18),(40,8),(40,32),(72,8),(72,64),(48,16),(48,32),(80,16),(80,64),(96,32),(96,64)], [], #[[],[3,2,3]])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def p8_B0 : List (List StD) := []
def p8_N0 : Array (List Nat) := mkNext p8_B0
theorem p8_I0 : LevelB true p8_T 0 p8_B0 := by intro c hc; cases hc
def p8_B1 : List (List StD) := []
def p8_N1 : Array (List Nat) := mkNext p8_B1
theorem p8_I1 : LevelB true p8_T 1 p8_B1 := by intro c hc; cases hc
def p8_B2 : List (List StD) := []
def p8_N2 : Array (List Nat) := mkNext p8_B2
theorem p8_I2 : LevelB true p8_T 2 p8_B2 := by intro c hc; cases hc
def p8_B3 : List (List StD) := []
def p8_N3 : Array (List Nat) := mkNext p8_B3
theorem p8_I3 : LevelB true p8_T 3 p8_B3 := by intro c hc; cases hc
def p8_B4 : List (List StD) := []
def p8_N4 : Array (List Nat) := mkNext p8_B4
theorem p8_I4 : LevelB true p8_T 4 p8_B4 := by intro c hc; cases hc
def p8_B5 : List (List StD) := []
def p8_N5 : Array (List Nat) := mkNext p8_B5
theorem p8_I5 : LevelB true p8_T 5 p8_B5 := by intro c hc; cases hc
def p8_B6 : List (List StD) := []
def p8_N6 : Array (List Nat) := mkNext p8_B6
theorem p8_I6 : LevelB true p8_T 6 p8_B6 := by intro c hc; cases hc
def p8_B7 : List (List StD) := []
def p8_N7 : Array (List Nat) := mkNext p8_B7
theorem p8_I7 : LevelB true p8_T 7 p8_B7 := by intro c hc; cases hc
def p8_B8 : List (List StD) := []
def p8_N8 : Array (List Nat) := mkNext p8_B8
theorem p8_I8 : LevelB true p8_T 8 p8_B8 := by intro c hc; cases hc
def p8_B9 : List (List StD) := []
def p8_N9 : Array (List Nat) := mkNext p8_B9
theorem p8_I9 : LevelB true p8_T 9 p8_B9 := by intro c hc; cases hc
def p8_B10 : List (List StD) := []
def p8_N10 : Array (List Nat) := mkNext p8_B10
theorem p8_I10 : LevelB true p8_T 10 p8_B10 := by intro c hc; cases hc
def p8_D11_0 : List StD := [
([pw0,pw1,pw2,pw3,pw4,pw5,pw6],[0,1,5,9,13,17,21,25,29,33,37,41,45,49,53,57,61,65,69,73,77,81,85,89,93,97,101,105,109,113,117,121,125,129,133,137,141,145,149,153,157],[0x1f,0xe5,0x345,0x1c05,0xe005,0x30005,0xc0023,0x30b,0x300403,0x406003,0x81000b,0x3000121,0xca1,0xc002021,0x10810021,0x60000501,0x180002101,0x600010101,0x1800002401,0x6000010401,0x18000012001])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8_C11x0 : levelOK true p8_T p8_t 10 p8_N10 p8_D11_0 = true := by decide +kernel
def p8_B11 : List (List StD) := [p8_D11_0]
def p8_N11 : Array (List Nat) := mkNext p8_B11
theorem p8_I11 : LevelB true p8_T 11 p8_B11 := levelStepB p8_B p8_W p8_I10 (by
  intro c hc
  unfold p8_B11 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact p8_C11x0
  cases hc
  )
theorem p8_L : LowN true p8_R p8_T 12 := lowSearchB p8_B p8_I11 (by decide +kernel)
def ptop_T : Nat := 0xfffffffffffffffffffffffffffffffcfffffffffffffffafffeffeefefeee00
def ptop_R : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def ptop_E : List (Nat × Nat × Nat) := [(0,8,9),(1,8,10),(2,16,20),(3,1,9),(4,1,17),(5,1,33),(6,1,65),(7,2,130)]
theorem ptop_B : baseOK ptop_T ptop_R ptop_E = true := by decide +kernel
def ptop_Z : List SliceD := [(pw9,12,[0, 2, 3, 4, 5, 6, 7])]
theorem ptop_Y : ∀ s ∈ ptop_Z, SliceN true ptop_R ptop_T s := by
  unfold ptop_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptop_B p8_B p8_L (by decide +kernel),by simp⟩
def ptop_C : List (Nat × List Nat) := [(0,[])]
def ptop_t : Tabs := ((ptop_C.map (mkCut true ptop_Z)).toArray, #[(10,8),(9,8),(131,129),(67,66),(20,16),(133,129),(13,12),(10,2),(9,1),(18,2),(17,1),(17,16),(34,2),(33,1),(33,32),(68,4),(65,1),(130,2),(131,3),(70,66),(14,12),(18,16),(34,32),(67,3),(132,4),(13,5),(28,24),(20,4),(37,5),(52,48),(28,12),(56,48),(40,8),(72,8),(72,64),(136,8),(136,128),(56,24),(52,36),(80,16),(80,64),(144,16),(144,128),(96,32),(96,64),(160,32),(160,128),(192,64),(192,128)], [], #[[],[4,3,4],[0,6],[0,4,3,4,6]])
theorem ptop_W : TabsP true ptop_R ptop_T ptop_t := ⟨cutsGood ptop_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def ptop_B0 : List (List StD) := []
def ptop_N0 : Array (List Nat) := mkNext ptop_B0
theorem ptop_I0 : LevelB true ptop_T 0 ptop_B0 := by intro c hc; cases hc
def ptop_B1 : List (List StD) := []
def ptop_N1 : Array (List Nat) := mkNext ptop_B1
theorem ptop_I1 : LevelB true ptop_T 1 ptop_B1 := by intro c hc; cases hc
def ptop_B2 : List (List StD) := []
def ptop_N2 : Array (List Nat) := mkNext ptop_B2
theorem ptop_I2 : LevelB true ptop_T 2 ptop_B2 := by intro c hc; cases hc
def ptop_B3 : List (List StD) := []
def ptop_N3 : Array (List Nat) := mkNext ptop_B3
theorem ptop_I3 : LevelB true ptop_T 3 ptop_B3 := by intro c hc; cases hc
def ptop_B4 : List (List StD) := []
def ptop_N4 : Array (List Nat) := mkNext ptop_B4
theorem ptop_I4 : LevelB true ptop_T 4 ptop_B4 := by intro c hc; cases hc
def ptop_B5 : List (List StD) := []
def ptop_N5 : Array (List Nat) := mkNext ptop_B5
theorem ptop_I5 : LevelB true ptop_T 5 ptop_B5 := by intro c hc; cases hc
def ptop_B6 : List (List StD) := []
def ptop_N6 : Array (List Nat) := mkNext ptop_B6
theorem ptop_I6 : LevelB true ptop_T 6 ptop_B6 := by intro c hc; cases hc
def ptop_B7 : List (List StD) := []
def ptop_N7 : Array (List Nat) := mkNext ptop_B7
theorem ptop_I7 : LevelB true ptop_T 7 ptop_B7 := by intro c hc; cases hc
def ptop_B8 : List (List StD) := []
def ptop_N8 : Array (List Nat) := mkNext ptop_B8
theorem ptop_I8 : LevelB true ptop_T 8 ptop_B8 := by intro c hc; cases hc
def ptop_B9 : List (List StD) := []
def ptop_N9 : Array (List Nat) := mkNext ptop_B9
theorem ptop_I9 : LevelB true ptop_T 9 ptop_B9 := by intro c hc; cases hc
def ptop_B10 : List (List StD) := []
def ptop_N10 : Array (List Nat) := mkNext ptop_B10
theorem ptop_I10 : LevelB true ptop_T 10 ptop_B10 := by intro c hc; cases hc
def ptop_B11 : List (List StD) := []
def ptop_N11 : Array (List Nat) := mkNext ptop_B11
theorem ptop_I11 : LevelB true ptop_T 11 ptop_B11 := by intro c hc; cases hc
def ptop_D12_0 : List StD := [
([pw0,pw1,pw2,pw3,pw4,pw5,pw6,pw7],[0,1,5,9,13,17,21,25,29,33,37,41,45,49,53,57,61,65,69,73,77,81,85,89,93,97,101,105,109,113,117,121,125,129,133,137,141,145,149,153,157,161,165,169,173,177,181,185,189,193],[0x1f,0xe5,0x315,0x1c05,0xe005,0x30015,0xc0005,0x300023,0x30b,0x400c03,0x806003,0x1010003,0x204000b,0xc000121,0x10000461,0x60002021,0x130021,0x2040061,0x180000501,0x300002101,0xc00010101,0x3000040101,0xc000002401,0x30000010401,0xc0000040401,0x300000012001,0xc00000042001,0x3000000050001])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptop_C12x0 : levelOK true ptop_T ptop_t 11 ptop_N11 ptop_D12_0 = true := by decide +kernel
def ptop_B12 : List (List StD) := [ptop_D12_0]
def ptop_N12 : Array (List Nat) := mkNext ptop_B12
theorem ptop_I12 : LevelB true ptop_T 12 ptop_B12 := levelStepB ptop_B ptop_W ptop_I11 (by
  intro c hc
  unfold ptop_B12 at hc
  rcases List.mem_cons.mp hc with rfl | hc; · exact ptop_C12x0
  cases hc
  )
theorem ptop_L : LowN true ptop_R ptop_T 13 := lowSearchB ptop_B ptop_I12 (by decide +kernel)

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [0, 7]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [3, 5]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.and, [9, 8]⟩,
    ⟨.or, [2, 15]⟩,
    ⟨.or, [12, 8]⟩,
    ⟨.and, [14, 17]⟩,
    ⟨.or, [13, 7]⟩,
    ⟨.and, [16, 19]⟩,
    ⟨.or, [18, 20]⟩], 21⟩
theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.gates.length = 14 := rfl
def theInputs : List Sig := rootsW [0,1,2,3,4,5,6,7]
def graph : Sig := W ptop_T
theorem graph_proper : proper graph := (baseOK_ok ptop_B).prop
def sample (r : Row) (i : Fin 8) : Bool := bit r (theInputs.getD i.val zero)
theorem theList : List.ofFn (fun i : Fin 8 => theInputs.getD i.val zero) = theInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = theInputs.map (bit r) := by
  rw [←theList,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem theTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem theEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates theInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k theInputs.toFinset := by
  have b := baseOK_ok ptop_B
  have goalEq : (execute C.gates theInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (theEval C legal C.output r).trans ((computes (sample r)).trans (theTable r).symm)
  have out := get_rep (u:=true) (execute C.gates theInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptop_T) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates theInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : theInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = theInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run theInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 12 theInputs.toFinset := by
  intro k small run
  have steps := list_run run theInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (theInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptop_L q bank built hit
  omega
theorem replaceShort (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 14 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · refine ⟨gates,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨ops,arity⟩ := fit g hg
    refine ⟨?_,arity⟩
    rcases ops with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (mono g hg c).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_52928

theorem PEqualNP.Outside.L_meta_52928 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_52928.replaceShort gates o fit correct

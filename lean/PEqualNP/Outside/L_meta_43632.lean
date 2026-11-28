import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43632_aux.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 128
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

def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
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
theorem bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
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
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

structure BaseP (T : Nat) (R : List Nat) : Prop where
  lt : T < 2^128
  plain : plainWord (W T) = true
  nodup : (rootsW R).Nodup
  plainR : (rootsW R).all plainWord = true
  ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a
  prop : proper (W T)

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

theorem lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
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
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
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

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
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
theorem av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

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

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
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

theorem sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List Nat × List Nat × List (List Nat)
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
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 100 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-100]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
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
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
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
def stOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK k next (st.2.1.filterMap fun i => K[i]?) (st.2.2.1.filterMap fun i => P[i]?) st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T K P k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset
theorem cutsGood {R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut Z), CutP R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {R T E K P k next st} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T K P k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
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
  have good : ∀ c ∈ st.2.1.filterMap (fun i => K[i]?), CutP R T c := by
    intro c hc
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hc
    exact hK c (List.mem_of_getElem? hi)
  have hs : ∀ q ∈ st.2.2.1.filterMap (fun i => P[i]?), sepOK T q = true := by
    intro q hq
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hq
    exact List.all_eq_true.mp hP q (List.mem_of_getElem? hi)
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp

  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
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
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 100
      · rw [hb,cond_false] at hi
        cases hg : (st.2.2.1.filterMap (fun i => P[i]?))[i-100]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.filterMap (fun i => K[i]?))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
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
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {R T E K P k D' D} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hI : LevelN R T k D') (h : levelOK T K P k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hK hP ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {T : Nat} {K : List CutV} {P : List (Nat × Nat)} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T K P k next ((D.drop (i*c)).take c) = true) : levelOK T K P k next D = true := by
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
theorem lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def w0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def w1 : Nat := 0xcccccccccccccccccccccccccccccccc
def w2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def w3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def w4 : Nat := 0x88888888888888888888888888888888
def w5 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def w6 : Nat := 0x22222222222222222222222222222222
def w7 : Nat := 0x44444444444444444444444444444444
def w8 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def w9 : Nat := 0xfafafafafafafafafafafafafafafafa
def w10 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def w11 : Nat := 0x50505050505050505050505050505050
def w12 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def w13 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def w14 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
def w15 : Nat := 0x55005500550055005500550055005500
def w16 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def w17 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def w18 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def w19 : Nat := 0x30303030303030303030303030303030
def w20 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
def w21 : Nat := 0xffccffccffccffccffccffccffccffcc
def w22 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc
def w23 : Nat := 0x33003300330033003300330033003300
def w24 : Nat := 0xf000f000f000f000f000f000f000f000
def w25 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def w26 : Nat := 0xf000f000f000f000f000f000f000f0
def w27 : Nat := 0xf000f000f000f000f000f000f000f00
def w28 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def w29 : Nat := 0x70707070707070707070707070707070
def w30 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88
def w31 : Nat := 0x77007700770077007700770077007700
def w32 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
def w33 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def w34 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00
def w35 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def w36 : Nat := 0xecececececececececececececececec
def w37 : Nat := 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c
def w38 : Nat := 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0
def w39 : Nat := 0x5f005f005f005f005f005f005f005f00
def w40 : Nat := 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8
def w41 : Nat := 0x32323232323232323232323232323232
def w42 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00
def w43 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa
def w44 : Nat := 0xeecceecceecceecceecceecceecceecc
def w45 : Nat := 0x44cc44cc44cc44cc44cc44cc44cc44cc
def w46 : Nat := 0xfaf0faf0faf0faf0faf0faf0faf0faf0
def w47 : Nat := 0x50f050f050f050f050f050f050f050f0
def w48 : Nat := 0xcc88cc88cc88cc88cc88cc88cc88cc88
def w49 : Nat := 0x33223322332233223322332233223322
def w50 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0
def w51 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def w52 : Nat := 0xff0cff0cff0cff0cff0cff0cff0cff0c
def w53 : Nat := 0xf300f300f300f300f300f300f300f300
def w54 : Nat := 0xff30ff30ff30ff30ff30ff30ff30ff30
def w55 : Nat := 0xcf00cf00cf00cf00cf00cf00cf00cf00
def w56 : Nat := 0xf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fc
def w57 : Nat := 0xf030f030f030f030f030f030f030f030
def w58 : Nat := 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0
def w59 : Nat := 0xc0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0
def w60 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def w61 : Nat := 0xcc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0c
def w62 : Nat := 0xcfcccfcccfcccfcccfcccfcccfcccfcc
def w63 : Nat := 0xc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0cc
def w64 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def w65 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000
def w66 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def w67 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def w68 : Nat := 0x55550000555500005555000055550000
def w69 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
def w70 : Nat := 0xcccc0000cccc0000cccc0000cccc
def w71 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
def w72 : Nat := 0xf0f00000f0f00000f0f00000f0f0
def w73 : Nat := 0xff000000ff000000ff000000ff000000
def w74 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def w75 : Nat := 0xff000000ff000000ff000000ff00
def w76 : Nat := 0xff000000ff000000ff000000ff0000
def w77 : Nat := 0x80808080808080808080808080808080
def w78 : Nat := 0x880088008800880088008800880088
def w79 : Nat := 0xffff8888ffff8888ffff8888ffff8888
def w80 : Nat := 0x8888000088880000888800008888
def w81 : Nat := 0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0
def w82 : Nat := 0xa000a000a000a000a000a000a000a0
def w83 : Nat := 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0
def w84 : Nat := 0xa0a00000a0a00000a0a00000a0a0
def w85 : Nat := 0x8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c
def w86 : Nat := 0xffffaa00ffffaa00ffffaa00ffffaa00
def w87 : Nat := 0x55ff000055ff000055ff000055ff0000
def w88 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa0000
def w89 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa
def w90 : Nat := 0x88cc88cc88cc88cc88cc88cc88cc88cc
def w91 : Nat := 0xa0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0
def w92 : Nat := 0x4444cccc4444cccc4444cccc4444cccc
def w93 : Nat := 0x5050f0f05050f0f05050f0f05050f0f0
def w94 : Nat := 0xffaaff00ffaaff00ffaaff00ffaaff00
def w95 : Nat := 0x5500ff005500ff005500ff005500ff00
def w96 : Nat := 0xcccc8888cccc8888cccc8888cccc8888
def w97 : Nat := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0
def w98 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa00
def w99 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa
def w100 : Nat := 0x8888cccc8888cccc8888cccc8888cccc
def w101 : Nat := 0xa0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0
def w102 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def w103 : Nat := 0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a
def w104 : Nat := 0x40404040404040404040404040404040
def w105 : Nat := 0xc000c000c000c000c000c000c000c000
def w106 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def w107 : Nat := 0xc000c000c000c000c000c000c000c0
def w108 : Nat := 0x3f003f003f003f003f003f003f003f00
def w109 : Nat := 0xc0c00000c0c00000c0c00000c0c00000
def w110 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0
def w111 : Nat := 0xc0c00000c0c00000c0c00000c0c0
def w112 : Nat := 0x3f3f00003f3f00003f3f00003f3f0000
def w113 : Nat := 0x30f030f030f030f030f030f030f030f0
def w114 : Nat := 0xaa22aa22aa22aa22aa22aa22aa22aa22
def w115 : Nat := 0x3030f0f03030f0f03030f0f03030f0f0
def w116 : Nat := 0xaaaa2222aaaa2222aaaa2222aaaa2222
def w117 : Nat := 0xf0f03030f0f03030f0f03030f0f03030
def w118 : Nat := 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc
def w119 : Nat := 0xaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0a
def w120 : Nat := 0xc0ccccc0c0ccccc0c0ccccc0c0ccccc
def w121 : Nat := 0xaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0a
def w122 : Nat := 0xcccc0c0ccccc0c0ccccc0c0ccccc0c0c
def w123 : Nat := 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def w124 : Nat := 0xcccccc00cccccc00cccccc00cccccc00
def w125 : Nat := 0xf0f0f000f0f0f000f0f0f000f0f0f000
def w126 : Nat := 0xcccc00cccccc00cccccc00cccccc00cc
def w127 : Nat := 0xf0f000f0f0f000f0f0f000f0f0f000f0
def w128 : Nat := 0xcc00cccccc00cccccc00cccccc00cccc
def w129 : Nat := 0xf000f0f0f000f0f0f000f0f0f000f0f0
def w130 : Nat := 0xff80ff80ff80ff80ff80ff80ff80ff80
def w131 : Nat := 0xffff8080ffff8080ffff8080ffff8080
def w132 : Nat := 0x7f007f007f007f007f007f007f007f00
def w133 : Nat := 0x7f7f00007f7f00007f7f00007f7f0000
def w134 : Nat := 0x88f888f888f888f888f888f888f888f8
def w135 : Nat := 0x88088808880888088808880888088808
def w136 : Nat := 0x8888f8f88888f8f88888f8f88888f8f8
def w137 : Nat := 0x88880808888808088888080888880808
def w138 : Nat := 0x88888800888888008888880088888800
def w139 : Nat := 0x77777700777777007777770077777700
def w140 : Nat := 0xa0eca0eca0eca0eca0eca0eca0eca0ec
def w141 : Nat := 0xa020a020a020a020a020a020a020a020
def w142 : Nat := 0xa0a0ececa0a0ececa0a0ececa0a0ecec
def w143 : Nat := 0xa0a02020a0a02020a0a02020a0a02020
def w144 : Nat := 0xa0a0a000a0a0a000a0a0a000a0a0a000
def w145 : Nat := 0x5f5f5f005f5f5f005f5f5f005f5f5f00
def w146 : Nat := 0x40c040c040c040c040c040c040c040c0
def w147 : Nat := 0xb030b030b030b030b030b030b030b030
def w148 : Nat := 0x8c0c8c0c8c0c8c0c8c0c8c0c8c0c8c0c
def w149 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def w150 : Nat := 0xc080c080c080c080c080c080c080c080
def w151 : Nat := 0x3f2a3f2a3f2a3f2a3f2a3f2a3f2a3f2a
def w152 : Nat := 0x30703070307030703070307030703070
def w153 : Nat := 0xfcf8fcf8fcf8fcf8fcf8fcf8fcf8fcf8
def w154 : Nat := 0xc080c080c080c080c080c080c080c08
def w155 : Nat := 0xc4c0c4c0c4c0c4c0c4c0c4c0c4c0c4c
def w156 : Nat := 0xfcecfcecfcecfcecfcecfcecfcecfcec
def w157 : Nat := 0x30203020302030203020302030203020
def w158 : Nat := 0x80c080c080c080c080c080c080c080c0
def w159 : Nat := 0x70307030703070307030703070307030
def w160 : Nat := 0x4c0c4c0c4c0c4c0c4c0c4c0c4c0c4c0c
def w161 : Nat := 0xd5c0d5c0d5c0d5c0d5c0d5c0d5c0d5c0
def w162 : Nat := 0x4040c0c04040c0c04040c0c04040c0c0
def w163 : Nat := 0xb0b03030b0b03030b0b03030b0b03030
def w164 : Nat := 0x8c8c0c0c8c8c0c0c8c8c0c0c8c8c0c0c
def w165 : Nat := 0xeaeac0c0eaeac0c0eaeac0c0eaeac0c0
def w166 : Nat := 0xc0c08080c0c08080c0c08080c0c08080
def w167 : Nat := 0x3f3f2a2a3f3f2a2a3f3f2a2a3f3f2a2a
def w168 : Nat := 0x30307070303070703030707030307070
def w169 : Nat := 0xfcfcf8f8fcfcf8f8fcfcf8f8fcfcf8f8
def w170 : Nat := 0xc0c08080c0c08080c0c08080c0c0808
def w171 : Nat := 0xc0c4c4c0c0c4c4c0c0c4c4c0c0c4c4c
def w172 : Nat := 0xfcfcececfcfcececfcfcececfcfcecec
def w173 : Nat := 0x30302020303020203030202030302020
def w174 : Nat := 0x8080c0c08080c0c08080c0c08080c0c0
def w175 : Nat := 0x70703030707030307070303070703030
def w176 : Nat := 0x4c4c0c0c4c4c0c0c4c4c0c0c4c4c0c0c
def w177 : Nat := 0xd5d5c0c0d5d5c0c0d5d5c0c0d5d5c0c0
def w178 : Nat := 0xea00ea00ea00ea00ea00ea00ea00ea00
def w179 : Nat := 0xea00ea00ea00ea00ea00ea00ea00ea
def w180 : Nat := 0xeaea0000eaea0000eaea0000eaea0000
def w181 : Nat := 0xeaea0000eaea0000eaea0000eaea
def w182 : Nat := 0xffff00c0ffff00c0ffff00c0ffff00c0
def w183 : Nat := 0xff3f0000ff3f0000ff3f0000ff3f0000
def w184 : Nat := 0xffff3f00ffff3f00ffff3f00ffff3f00
def w185 : Nat := 0xc0ff0000c0ff0000c0ff0000c0ff0000
def w186 : Nat := 0xff00ffc0ff00ffc0ff00ffc0ff00ffc0
def w187 : Nat := 0xff003f00ff003f00ff003f00ff003f00
def w188 : Nat := 0xff3fff00ff3fff00ff3fff00ff3fff00
def w189 : Nat := 0xc000ff00c000ff00c000ff00c000ff00
def w190 : Nat := 0xc0c0c000c0c0c000c0c0c000c0c0c000
def w191 : Nat := 0x3f3f3f003f3f3f003f3f3f003f3f3f00
def w192 : Nat := 0xc0c0ffc0c0c0ffc0c0c0ffc0c0c0ffc0
def w193 : Nat := 0xc0c000c0c0c000c0c0c000c0c0c000c0
def w194 : Nat := 0xc0ffc0c0c0ffc0c0c0ffc0c0c0ffc0c0
def w195 : Nat := 0xc000c0c0c000c0c0c000c0c0c000c0c0
def w196 : Nat := 0xfcf0cc00fcf0cc00fcf0cc00fcf0cc00
def w197 : Nat := 0x50d050d050d050d050d050d050d050d0
def w198 : Nat := 0xa8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a
def w199 : Nat := 0xfcccf000fcccf000fcccf000fcccf000
def w200 : Nat := 0x5050d0d05050d0d05050d0d05050d0d0
def w201 : Nat := 0xa0a8a8a0a0a8a8a0a0a8a8a0a0a8a8a
def w202 : Nat := 0x44c444c444c444c444c444c444c444c4
def w203 : Nat := 0x22a222a222a222a222a222a222a222a2
def w204 : Nat := 0x4444c4c44444c4c44444c4c44444c4c4
def w205 : Nat := 0x2222a2a22222a2a22222a2a22222a2a2
def w206 : Nat := 0x444444cc444444cc444444cc444444cc
def w207 : Nat := 0x505050f0505050f0505050f0505050f0
def w208 : Nat := 0x222222aa222222aa222222aa222222aa
def w209 : Nat := 0x303030f0303030f0303030f0303030f0
def w210 : Nat := 0xa0a0aaa0a0a0aaa0a0a0aaa0a0a0aaa
def w211 : Nat := 0xc0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc
def w212 : Nat := 0x3030f0303030f0303030f0303030f030
def w213 : Nat := 0xc0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c
def w214 : Nat := 0x30f0303030f0303030f0303030f03030
def w215 : Nat := 0xccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c
def w216 : Nat := 0x707070f0707070f0707070f0707070f0
def w217 : Nat := 0x4c4c4ccc4c4c4ccc4c4c4ccc4c4c4ccc
def w218 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def w219 : Nat := 0xfcfca800fcfca800fcfca800fcfca800
def w220 : Nat := 0xa800fcfca800fcfca800fcfca800fcfc
def w221 : Nat := 0xfca8fc00fca8fc00fca8fc00fca8fc00
def w222 : Nat := 0xa8fc00fca8fc00fca8fc00fca8fc00fc
def w223 : Nat := 0x6a6a6a6a6a6a6a6a6a6a6a6a6a6a6a6a
def w224 : Nat := 0x3fc03fc03fc03fc03fc03fc03fc03fc0
def w225 : Nat := 0x3f3fc0c03f3fc0c03f3fc0c03f3fc0c0
def w226 : Nat := 0xfcfc3c00fcfc3c00fcfc3c00fcfc3c00
def w227 : Nat := 0xfc3cfc00fc3cfc00fc3cfc00fc3cfc00
def p1_T : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def p1_R : List Nat := [0, 1, 2]
def p1_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
theorem p1_L : LowN p1_R p1_T 2 := lowCount p1_B (by decide +kernel)
def p2_T : Nat := 0xfefefefefefefefefefefefefefefefe
def p2_R : List Nat := [0, 1, 2]
def p2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
theorem p2_L : LowN p2_R p2_T 2 := lowCount p2_B (by decide +kernel)
def p3_T : Nat := 0x80808080808080808080808080808080
def p3_R : List Nat := [0, 1, 2]
def p3_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
theorem p3_L : LowN p3_R p3_T 2 := lowCount p3_B (by decide +kernel)
def p4_T : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
theorem p4_L : LowN p4_R p4_T 2 := lowCount p4_B (by decide +kernel)
def p5_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def p5_R : List Nat := [0, 1]
def p5_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
theorem p5_L : LowN p5_R p5_T 1 := lowCount p5_B (by decide +kernel)
def p6_T : Nat := 0x88888888888888888888888888888888
def p6_R : List Nat := [0, 1]
def p6_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_L : LowN p6_R p6_T 1 := lowCount p6_B (by decide +kernel)
def p7_T : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def p7_R : List Nat := [0, 1, 2, 3]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
theorem p7_S0 : SliceN p7_R p7_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) p7_B p1_B p1_L (by decide +kernel)
theorem p7_S1 : SliceN p7_R p7_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]) := mkSlice (w:=1) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S2 : SliceN p7_R p7_T (0x55555555555555555555555555555555,2,[1, 2, 3]) := mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel)
theorem p7_S3 : SliceN p7_R p7_T (0x33333333333333333333333333333333,2,[0, 2, 3]) := mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel)
theorem p7_S4 : SliceN p7_R p7_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) p7_B p5_B p5_L (by decide +kernel)
theorem p7_S5 : SliceN p7_R p7_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) p7_B p6_B p6_L (by decide +kernel)
theorem p7_S6 : SliceN p7_R p7_T (0x3030303030303030303030303030303,1,[0, 3]) := mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel)
theorem p7_S7 : SliceN p7_R p7_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) p7_B p6_B p6_L (by decide +kernel)
theorem p7_S8 : SliceN p7_R p7_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]) := mkSlice (w:=1) p7_B p5_B p5_L (by decide +kernel)
theorem p7_S9 : SliceN p7_R p7_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,1,[0, 3]) := mkSlice (w:=6) p7_B p5_B p5_L (by decide +kernel)
theorem p7_S10 : SliceN p7_R p7_T (0x55005500550055005500550055005500,1,[1, 2]) := mkSlice (w:=8) p7_B p6_B p6_L (by decide +kernel)
theorem p7_S11 : SliceN p7_R p7_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,2,[0, 1, 3]) := mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel)
theorem p7_S12 : SliceN p7_R p7_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) p7_B p1_B p1_L (by decide +kernel)
theorem p7_S13 : SliceN p7_R p7_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) p7_B p5_B p5_L (by decide +kernel)
theorem p7_S14 : SliceN p7_R p7_T (0xff00ff00ff00ff00ff00ff00ff00ff,2,[0, 1, 2]) := mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel)
theorem p7_S15 : SliceN p7_R p7_T (0x330033003300330033003300330033,1,[0, 2]) := mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel)
theorem p7_S16 : SliceN p7_R p7_T (0xcc00cc00cc00cc00cc00cc00cc00cc00,1,[0, 2]) := mkSlice (w:=10) p7_B p5_B p5_L (by decide +kernel)
theorem p7_S17 : SliceN p7_R p7_T (0xf000f000f000f000f000f000f000f000,1,[0, 1]) := mkSlice (w:=12) p7_B p5_B p5_L (by decide +kernel)
theorem p7_S18 : SliceN p7_R p7_T (0xf000f000f000f000f000f000f000f,1,[0, 1]) := mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel)
def p7_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]),(0x55555555555555555555555555555555,2,[1, 2, 3]),(0x33333333333333333333333333333333,2,[0, 2, 3]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3]),(0x3030303030303030303030303030303,1,[0, 3]),(0x50505050505050505050505050505050,1,[1, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,1,[0, 3]),(0x55005500550055005500550055005500,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,2,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff,2,[0, 1, 2]),(0x330033003300330033003300330033,1,[0, 2]),(0xcc00cc00cc00cc00cc00cc00cc00cc00,1,[0, 2]),(0xf000f000f000f000f000f000f000f000,1,[0, 1]),(0xf000f000f000f000f000f000f000f,1,[0, 1])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨p7_S0,p7_S1,p7_S2,p7_S3,p7_S4,p7_S5,p7_S6,p7_S7,p7_S8,p7_S9,p7_S10,p7_S11,p7_S12,p7_S13,p7_S14,p7_S15,p7_S16,p7_S17,p7_S18,by simp⟩
def p7_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[])]
def p7_P : List (Nat × Nat) := [(4,5),(12,14),(2,3),(1,3),(10,14),(1,5),(6,14),(8,9),(1,9),(5,6),(0,3),(3,6),(0,5),(3,10),(0,9),(1,7),(1,11),(1,13)]
def p7_K : List CutV := p7_C.map (mkCut p7_Z)
theorem p7_W : ∀ c ∈ p7_K, CutP p7_R p7_T c := cutsGood p7_Y (by decide +kernel)
theorem p7_Q : p7_P.all (sepOK p7_T) = true := by decide +kernel
noncomputable def p7_D5 : List StD := [
([w0,w1,w2,w3],[],[0,1,2,3,4,5,6,7,8],[[100,101,102,103],[102,104,100,105],[100,106,107,108],[103,105,101,104],[103,108,101,106],[105,108,104,106]])]
noncomputable def p7_D4 : List StD := [
([w4,w0,w1,w2,w3],[0,1,2,3,4,5,6,7],[9],[[0],[1],[2],[2],[100,2,3],[2,4],[2,4],[3,5],[3,5],[6,7]]),
([w0,w1,w5,w2,w3],[0,1,3,5,2,4,8,9],[9],[[100,0,1],[2],[3,1],[3,1],[4],[5,0],[5,0],[0],[0],[6,7]]),
([w6,w0,w1,w2,w3],[3,1,2,4,0,9,10],[10,5],[[0],[1],[2,3],[2,3],[2,4,100],[2,3],[2,3],[3,4],[3,4],[101,5,6]]),
([w7,w0,w1,w2,w3],[0,2,4,5,3,1,8],[10,6],[[0],[1],[2,3],[2,3],[4,5,100],[3,2],[3,2],[2,3],[2,3],[6,101]]),
([w8,w0,w1,w2,w3],[9,2,4,8,11,5,7,6],[11],[[0],[1],[2],[1],[1,3],[100,1,4],[1,3],[3,5,6],[7,5],[3,6]]),
([w0,w1,w2,w9,w3],[7,8,9,4,6,2],[11],[[0,1],[100,2,3],[4],[0,1],[1,0],[0],[3,2],[5],[1,0],[0]]),
([w10,w0,w1,w2,w3],[6,2,8,4,9,7,10],[12,3],[[0],[1,2],[3],[1,2],[1,2],[1,4,100],[1,2],[2,5],[101,4,6],[2,4]]),
([w11,w0,w1,w2,w3],[9,8,7,2,6,4],[12,6],[[0],[1,2],[3],[1,2],[2,1],[4,5,100],[2,1],[1,2],[4,101],[1,2]]),
([w12,w0,w1,w2,w3],[12,2,4,13,14,15,7,5,10],[13],[[0],[1],[1],[2],[1,3],[1,3],[100,1,4],[5,6,7],[3,7,8],[3,6,8]]),
([w0,w1,w2,w3,w13],[10,8,4,12,14,16,13,2],[13],[[0,1],[0,2],[100,3,1],[4],[1,5,2],[2,0,6],[0],[1,0,6],[0],[7]]),
([w14,w0,w1,w2,w3],[14,2,13,4,12,7],[14,3],[[0],[1,2],[1,2],[3],[1,2],[1,2],[1,4,100],[101,5],[2,4],[2,4]]),
([w15,w0,w1,w2,w3],[12,14,10,2,13,4],[14,4],[[0],[1,2],[1,2],[3],[2,4],[2,4],[1,5,100],[5,101],[1,2],[1,2]]),
([w0,w16,w1,w2,w3],[6,9,15,4,7,16,8],[14],[[0,1],[0,1],[0,1],[2,3,100],[4],[5],[0,1],[2,6],[0,1],[0,1]]),
([w0,w1,w2,w17,w3],[7,16,6,9,8,4],[2],[[0,1,2],[2,3],[2,1],[0,1,100],[0,1],[4],[2,3],[5],[2,0],[2,0]]),
([w18,w0,w1,w2,w3],[9,8,16,7,6,4],[2,15],[[0,100],[1],[2],[0],[3,0,4],[4,0],[3,5],[5,3,101],[4,0],[4,0]]),
([w19,w0,w1,w2,w3],[6,7,4,16,9,5,8],[0,15],[[0,100],[1],[2],[0],[0,3],[0,4],[5,3,6],[6,3,101],[0,4],[0,3,4]]),
([w0,w20,w1,w2,w3],[6,16,4,14,10,9],[12],[[0,1],[0,1],[0,2,100],[3,1],[4],[2,1],[5],[2,1],[0,3],[0,1,3]]),
([w0,w1,w2,w3,w21],[10,16,15,9,14,4],[2],[[0,1,2],[0,3,100],[2,1],[2,1],[2,1],[0,3],[4],[2,0],[2,0],[5]]),
([w22,w0,w1,w2,w3],[16,14,9,10,15,4],[2,16],[[0,100],[1],[0],[2],[3,0,4],[3,5],[4,0],[4,0],[5,3,101],[4,0]]),
([w23,w0,w1,w2,w3],[9,10,16,4,15,5,13],[7,16],[[0,100],[1],[2],[3],[4,0],[5,0,6],[4,2],[4,2],[6,0,101],[4,0,2]]),
([w0,w1,w24,w2,w3],[15,13,17,6,8,16,9],[10],[[0,1,100],[0,2],[3,1,2],[0,2],[1,2],[0,2,4],[1,2],[5],[6],[3,0]]),
([w0,w1,w2,w3,w25],[10,16,9,18,17,13,6],[10],[[0,1,100],[0,2,3],[3,1],[3,1],[3,1,4],[3,0],[3,0],[0,2],[5],[6]]),
([w26,w0,w1,w2,w3],[16,10,13,9,6,17,18],[0,17],[[0,100],[1],[2],[3],[1,0,4],[1,5,4],[6,0],[6,0,5],[4,1,6],[4,0,101]]),
([w27,w0,w1,w2,w3],[17,16,6,15,13,9,18],[7,17],[[0,100],[0],[1],[2],[3,4,5],[6,0],[3,0],[3,0,6],[4,0],[3,5,101]])]
noncomputable def p7_D3 : List StD := [
([w0,w1,w28,w3],[2,9,6,17,15,18],[],[[0,1,2],[0,1,2],[0,3,4],[4,3,5],[2,1],[2,1]]),
([w29,w0,w1,w3],[2,13,17,18,16,8,10],[],[[0,1],[1,2,3],[1,4],[0,5],[0,5],[3,6]]),
([w0,w1,w2,w30],[2,16,15,17,6,18],[],[[0,1,2],[0,3,4],[0,1,2],[2,1],[4,3,5],[2,1]]),
([w31,w0,w1,w2],[2,16,18,17,6,10,15,13,5],[],[[0,1,2],[2,3,4],[4,5,6],[0,7],[0,7],[2,8,6]]),
([w0,w1,w32,w3],[6,13,16,2,5,18,17],[],[[0,1,2],[0,1,3],[4,2,5],[5,2,6],[0,4],[0,2,1]]),
([w33,w0,w1,w3],[2,13,17,18,16,7,8],[],[[0,1],[2,0,3],[1,4],[5,1],[5,2,6],[1,2]]),
([w0,w1,w34,w2],[15,13,16,18,5,17],[],[[0,1,2],[0,2],[3,1,4],[1,4,5],[0,2],[0,2]]),
([w35,w0,w1,w2],[2,8,17,18,13,16,10],[],[[0,1],[2,0,3],[1,4,5],[6,1],[6,2,4],[1,2]]),
([w0,w36,w2,w3],[2,13,9,18,16,17,8],[],[[0,1],[0,2,3],[0,4,3],[1,4,5],[1,2,5],[6,2]]),
([w37,w0,w2,w3],[2,16,8,17,13,4,10,15],[],[[0,1,2],[2,1,3],[4,3],[0,5],[0,2],[2,6,7]]),
([w0,w1,w2,w38],[2,8,17,18,10,13],[],[[0,1],[0,2,3],[0,1],[1,2],[3,2],[1,4,5]]),
([w39,w0,w1,w2],[2,8,13,10,5,15],[],[[0,1],[2,3],[1,3,2],[0,1],[0,2],[1,4,5]]),
([w0,w40,w2,w3],[2,8,6,13,17,15,9],[],[[0,1],[2,3,4],[5,1,4],[1,0],[2,4,3],[1,6]]),
([w41,w0,w2,w3],[2,13,8,10,5,9],[],[[0,1],[2,0],[1,3],[4,1],[4,2],[1,5,2]]),
([w0,w1,w2,w42],[15,13,9,18,8,2,17],[],[[0,1,2],[3,1,2],[0,4,5],[0,6,3],[1,2,6],[0,2,4]]),
([w43,w0,w1,w2],[2,8,10,9,13,17],[],[[0,1],[2,3,4],[1,0],[2,1],[2,3,4],[1,5]]),
([w0,w44,w2,w3],[2,9,13,16,18,17],[],[[0,1,2],[0,1,2],[0,3,4],[4,3,5],[2,1,5],[2,1,3]]),
([w45,w0,w2,w3],[2,13,18,17,4,10],[],[[0,1],[2,3],[1,3],[0,1],[0,4],[1,5]]),
([w0,w1,w46,w3],[2,13,17,18,10],[],[[0,1],[0,1],[0,2,3],[3,2],[1,2],[1,4]]),
([w47,w0,w1,w3],[2,17,18,16,4,13,8,10],[],[[0,1,2],[2,3,4],[4,3],[0,5],[0,6],[2,7]]),
([w0,w48,w2,w3],[2,18,10,17,13,15],[],[[0,1],[2,3,4],[5,3],[1,3],[1,0],[4,2]]),
([w49,w0,w2,w3],[2,13,18,17,10,5,8],[],[[0,1],[2,3],[1,0],[4,1],[5,3,6],[1,4]]),
([w0,w1,w50,w3],[10,8,17,18,13],[],[[0,1],[0,2,3],[3,1,2],[1,2],[3,0],[1,0,4]]),
([w51,w0,w1,w3],[2,13,17,8,10,7],[],[[0,1],[2,3],[1,0],[4,1],[5,2,3],[1,2]]),
([w0,w16,w17,w3],[18,9,6,17],[15],[[0,1],[2,1],[0,3],[100],[2,1],[0,1,2]]),
([w0,w1,w2,w52],[10,9,6,2,17,8,15,16],[],[[0,1,2],[0,1,2],[3,4,5],[6,4,7],[2,0,1],[2,0,1]]),
([w0,w1,w2,w53],[15,9,6,17,18],[],[[0,1],[2,1],[0,3],[0,3,4],[2,1],[0,1,2]]),
([w0,w1,w2,w54],[10,9,6,2,17,18],[],[[0,1,2],[0,1,2],[3,4,5],[5,4],[2,0,1],[2,0,1]]),
([w0,w1,w55,w2],[6,9,2,8,16,15],[],[[0,1],[2,3],[0,1],[0,1],[3,4,5],[0,1]]),
([w0,w20,w2,w21],[6,16,9,15],[16],[[0,1],[0,2],[3,1],[3,1],[100],[0,1,3]]),
([w0,w1,w56,w3],[15,9,2,6,16],[],[[0,1],[2,1,3],[0,4],[0,4],[3,1],[0,1,3]]),
([w0,w1,w57,w3],[6,16,17,15,18],[],[[0,1],[0,2],[3,1],[3,1],[0,2,4],[0,1,3]]),
([w0,w1,w58,w3],[15,16,2,17,18],[],[[0,1],[2,3,4],[0,1],[0,1],[4,3],[0,1]]),
([w0,w59,w1,w3],[2,9,18,15,16,6],[],[[0,1,2],[3,1],[2,4],[2,4,3],[3,1,4],[2,1,5]]),
([w0,w1,w24,w25],[15,16,17,18],[17],[[0,1],[0,2],[3,1],[3,1,2],[0,2,3],[100]]),
([w0,w60,w2,w3],[2,16,6,17,18,9],[],[[0,1,2],[2,3],[4,1],[4,1,3],[2,3,4],[2,1,5]]),
([w0,w61,w2,w3],[2,16,6,17,18,15],[],[[0,1,2],[2,3],[4,1],[4,1,3],[2,3,4],[2,1,5]]),
([w0,w62,w2,w3],[2,16,15,18,17],[],[[0,1,2],[3,4],[2,1],[2,1],[3,4],[2,1]]),
([w0,w63,w2,w3],[2,9,15,18,17,6],[],[[0,1,2],[3,1],[2,4],[2,4,3],[3,1,4],[2,1,5]])]
def p7_D2 : List StD := []
theorem p7_I2 : LevelN p7_R p7_T 2 p7_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C3x0 : levelOK p7_T p7_K p7_P 2 (p7_D2.map Prod.fst) ((p7_D3.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C3x1 : levelOK p7_T p7_K p7_P 2 (p7_D2.map Prod.fst) ((p7_D3.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C3x2 : levelOK p7_T p7_K p7_P 2 (p7_D2.map Prod.fst) ((p7_D3.drop (2*16)).take 16) = true := by decide +kernel
theorem p7_I3 : LevelN p7_R p7_T 3 p7_D3 := levelStep p7_B p7_W p7_Q p7_I2 (chunks 16 p7_D3 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C3x0
  · exact p7_C3x1
  · exact p7_C3x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK p7_T p7_K p7_P 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C4x1 : levelOK p7_T p7_K p7_P 3 (p7_D3.map Prod.fst) ((p7_D4.drop (1*16)).take 16) = true := by decide +kernel
theorem p7_I4 : LevelN p7_R p7_T 4 p7_D4 := levelStep p7_B p7_W p7_Q p7_I3 (chunks 16 p7_D4 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  · exact p7_C4x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK p7_T p7_K p7_P 4 (p7_D4.map Prod.fst) ((p7_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p7_I5 : LevelN p7_R p7_T 5 p7_D5 := levelStep p7_B p7_W p7_Q p7_I4 (chunks 16 p7_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C5x0
  ))
theorem p7_L : LowN p7_R p7_T 6 := lowSearch p7_B p7_I5 (by decide +kernel)
def p8_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p8_R : List Nat := [0, 1, 2]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
theorem p8_S0 : SliceN p8_R p8_T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) p8_B p6_B p6_L (by decide +kernel)
theorem p8_S1 : SliceN p8_R p8_T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) p8_B p6_B p6_L (by decide +kernel)
theorem p8_S2 : SliceN p8_R p8_T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) p8_B p5_B p5_L (by decide +kernel)
theorem p8_S3 : SliceN p8_R p8_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) p8_B p5_B p5_L (by decide +kernel)
theorem p8_S4 : SliceN p8_R p8_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) p8_B p6_B p6_L (by decide +kernel)
theorem p8_S5 : SliceN p8_R p8_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) p8_B p5_B p5_L (by decide +kernel)
def p8_Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨p8_S0,p8_S1,p8_S2,p8_S3,p8_S4,p8_S5,by simp⟩
def p8_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p8_P : List (Nat × Nat) := [(4,5),(1,3),(0,3),(2,3),(2,6),(1,5)]
def p8_K : List CutV := p8_C.map (mkCut p8_Z)
theorem p8_W : ∀ c ∈ p8_K, CutP p8_R p8_T c := cutsGood p8_Y (by decide +kernel)
theorem p8_Q : p8_P.all (sepOK p8_T) = true := by decide +kernel
noncomputable def p8_D3 : List StD := [
([w0,w1,w2],[0,1,2,3,4,5],[0,1,2,3,4,5],[[0,1,100,2,3,101,102],[4,1,103,5,3,100],[4,0,101,5,2,104,105]])]
def p8_D2 : List StD := []
theorem p8_I2 : LevelN p8_R p8_T 2 p8_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p8_C3x0 : levelOK p8_T p8_K p8_P 2 (p8_D2.map Prod.fst) ((p8_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem p8_I3 : LevelN p8_R p8_T 3 p8_D3 := levelStep p8_B p8_W p8_Q p8_I2 (chunks 16 p8_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C3x0
  ))
theorem p8_L : LowN p8_R p8_T 4 := lowSearch p8_B p8_I3 (by decide +kernel)
def p9_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def p9_R : List Nat := [0, 1, 2, 3]
def p9_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
theorem p9_S0 : SliceN p9_R p9_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p9_B p8_B p8_L (by decide +kernel)
def p9_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨p9_S0,by simp⟩
def p9_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p9_P : List (Nat × Nat) := []
def p9_K : List CutV := p9_C.map (mkCut p9_Z)
theorem p9_W : ∀ c ∈ p9_K, CutP p9_R p9_T c := cutsGood p9_Y (by decide +kernel)
theorem p9_Q : p9_P.all (sepOK p9_T) = true := by decide +kernel
noncomputable def p9_D4 : List StD := [
([w0,w1,w2,w3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def p9_D3 : List StD := []
theorem p9_I3 : LevelN p9_R p9_T 3 p9_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C4x0 : levelOK p9_T p9_K p9_P 3 (p9_D3.map Prod.fst) ((p9_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p9_I4 : LevelN p9_R p9_T 4 p9_D4 := levelStep p9_B p9_W p9_Q p9_I3 (chunks 16 p9_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C4x0
  ))
theorem p9_L : LowN p9_R p9_T 5 := lowSearch p9_B p9_I4 (by decide +kernel)
def p10_T : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def p10_R : List Nat := [0, 1, 2, 3]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
theorem p10_S0 : SliceN p10_R p10_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) p10_B p8_B p8_L (by decide +kernel)
def p10_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨p10_S0,by simp⟩
def p10_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p10_P : List (Nat × Nat) := []
def p10_K : List CutV := p10_C.map (mkCut p10_Z)
theorem p10_W : ∀ c ∈ p10_K, CutP p10_R p10_T c := cutsGood p10_Y (by decide +kernel)
theorem p10_Q : p10_P.all (sepOK p10_T) = true := by decide +kernel
noncomputable def p10_D4 : List StD := [
([w0,w1,w2,w3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def p10_D3 : List StD := []
theorem p10_I3 : LevelN p10_R p10_T 3 p10_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C4x0 : levelOK p10_T p10_K p10_P 3 (p10_D3.map Prod.fst) ((p10_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p10_I4 : LevelN p10_R p10_T 4 p10_D4 := levelStep p10_B p10_W p10_Q p10_I3 (chunks 16 p10_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C4x0
  ))
theorem p10_L : LowN p10_R p10_T 5 := lowSearch p10_B p10_I4 (by decide +kernel)
def p11_T : Nat := 0xa880a880a880a880a880a880a880a880
def p11_R : List Nat := [0, 1, 2, 3]
def p11_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
theorem p11_S0 : SliceN p11_R p11_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]) := mkSlice (w:=1) p11_B p8_B p8_L (by decide +kernel)
def p11_Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨p11_S0,by simp⟩
def p11_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p11_P : List (Nat × Nat) := []
def p11_K : List CutV := p11_C.map (mkCut p11_Z)
theorem p11_W : ∀ c ∈ p11_K, CutP p11_R p11_T c := cutsGood p11_Y (by decide +kernel)
theorem p11_Q : p11_P.all (sepOK p11_T) = true := by decide +kernel
noncomputable def p11_D4 : List StD := [
([w0,w1,w2,w3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def p11_D3 : List StD := []
theorem p11_I3 : LevelN p11_R p11_T 3 p11_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p11_C4x0 : levelOK p11_T p11_K p11_P 3 (p11_D3.map Prod.fst) ((p11_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p11_I4 : LevelN p11_R p11_T 4 p11_D4 := levelStep p11_B p11_W p11_Q p11_I3 (chunks 16 p11_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C4x0
  ))
theorem p11_L : LowN p11_R p11_T 5 := lowSearch p11_B p11_I4 (by decide +kernel)
def p12_T : Nat := 0x80008000800080008000800080008000
def p12_R : List Nat := [0, 1, 2, 3]
def p12_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
theorem p12_L : LowN p12_R p12_T 3 := lowCount p12_B (by decide +kernel)
def p13_T : Nat := 0x88808880888088808880888088808880
def p13_R : List Nat := [0, 1, 2, 3]
def p13_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
theorem p13_L : LowN p13_R p13_T 3 := lowCount p13_B (by decide +kernel)
def p14_T : Nat := 0xe8a8a880e8a8a880e8a8a880e8a8a880
def p14_R : List Nat := [0, 1, 2, 3, 4]
def p14_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
theorem p14_S0 : SliceN p14_R p14_T (0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4]) := mkSlice (w:=2) p14_B p7_B p7_L (by decide +kernel)
theorem p14_S1 : SliceN p14_R p14_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6,[0, 1, 3, 4]) := mkSlice (w:=4) p14_B p7_B p7_L (by decide +kernel)
theorem p14_S2 : SliceN p14_R p14_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]) := mkSlice (w:=1) p14_B p9_B p9_L (by decide +kernel)
theorem p14_S3 : SliceN p14_R p14_T (0xaa00aa00aa00aa00aa00aa00aa00aa,4,[1, 2, 4]) := mkSlice (w:=1) p14_B p8_B p8_L (by decide +kernel)
theorem p14_S4 : SliceN p14_R p14_T (0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]) := mkSlice (w:=8) p14_B p10_B p10_L (by decide +kernel)
theorem p14_S5 : SliceN p14_R p14_T (0xaaaa0000aaaa0000aaaa0000aaaa,4,[1, 2, 3]) := mkSlice (w:=1) p14_B p8_B p8_L (by decide +kernel)
theorem p14_S6 : SliceN p14_R p14_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p14_B p10_B p10_L (by decide +kernel)
theorem p14_S7 : SliceN p14_R p14_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p14_B p11_B p11_L (by decide +kernel)
theorem p14_S8 : SliceN p14_R p14_T (0xff000000ff000000ff000000ff000000,4,[0, 1, 2]) := mkSlice (w:=24) p14_B p8_B p8_L (by decide +kernel)
theorem p14_S9 : SliceN p14_R p14_T (0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]) := mkSlice (w:=0) p14_B p11_B p11_L (by decide +kernel)
theorem p14_S10 : SliceN p14_R p14_T (0x55555555555555555555555555555555,3,[1, 2, 3, 4]) := mkSlice (w:=0) p14_B p12_B p12_L (by decide +kernel)
theorem p14_S11 : SliceN p14_R p14_T (0x8080808080808080808080808080808,1,[3, 4]) := mkSlice (w:=3) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S12 : SliceN p14_R p14_T (0x33333333333333333333333333333333,3,[0, 2, 3, 4]) := mkSlice (w:=0) p14_B p13_B p13_L (by decide +kernel)
theorem p14_S13 : SliceN p14_R p14_T (0x22222222222222222222222222222222,2,[2, 3, 4]) := mkSlice (w:=1) p14_B p4_B p4_L (by decide +kernel)
theorem p14_S14 : SliceN p14_R p14_T (0x330033003300330033003300330033,2,[0, 2, 4]) := mkSlice (w:=0) p14_B p3_B p3_L (by decide +kernel)
theorem p14_S15 : SliceN p14_R p14_T (0x55005500550055005500550055005500,2,[1, 2, 4]) := mkSlice (w:=8) p14_B p3_B p3_L (by decide +kernel)
theorem p14_S16 : SliceN p14_R p14_T (0x3300000033000000330000003300,1,[0, 2]) := mkSlice (w:=8) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S17 : SliceN p14_R p14_T (0x330000003300000033000000330000,1,[0, 2]) := mkSlice (w:=16) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S18 : SliceN p14_R p14_T (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) p14_B p3_B p3_L (by decide +kernel)
theorem p14_S19 : SliceN p14_R p14_T (0x50505050505050505050505050505050,2,[1, 3, 4]) := mkSlice (w:=4) p14_B p3_B p3_L (by decide +kernel)
theorem p14_S20 : SliceN p14_R p14_T (0x30303030303030303030303030303030,2,[0, 3, 4]) := mkSlice (w:=4) p14_B p4_B p4_L (by decide +kernel)
theorem p14_S21 : SliceN p14_R p14_T (0x300030003000300030003000300030,1,[0, 4]) := mkSlice (w:=4) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S22 : SliceN p14_R p14_T (0x50005000500050005000500050005000,1,[1, 4]) := mkSlice (w:=12) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S23 : SliceN p14_R p14_T (0xf000f000f000f000f000f000f000f,2,[0, 1, 4]) := mkSlice (w:=0) p14_B p3_B p3_L (by decide +kernel)
theorem p14_S24 : SliceN p14_R p14_T (0xf0000000f0000000f0000000f00,1,[0, 1]) := mkSlice (w:=8) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S25 : SliceN p14_R p14_T (0xf0000000f0000000f0000000f0000,1,[0, 1]) := mkSlice (w:=16) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S26 : SliceN p14_R p14_T (0x50500000505000005050000050500000,1,[1, 3]) := mkSlice (w:=20) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S27 : SliceN p14_R p14_T (0x88888888888888888888888888888888,2,[2, 3, 4]) := mkSlice (w:=3) p14_B p2_B p2_L (by decide +kernel)
theorem p14_S28 : SliceN p14_R p14_T (0x880088008800880088008800880088,1,[2, 4]) := mkSlice (w:=3) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S29 : SliceN p14_R p14_T (0x3333000033330000333300003333,2,[0, 2, 3]) := mkSlice (w:=0) p14_B p3_B p3_L (by decide +kernel)
theorem p14_S30 : SliceN p14_R p14_T (0x8888000088880000888800008888,1,[2, 3]) := mkSlice (w:=3) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S31 : SliceN p14_R p14_T (0x20202020202020202020202020202020,1,[3, 4]) := mkSlice (w:=5) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S32 : SliceN p14_R p14_T (0x40404040404040404040404040404040,1,[3, 4]) := mkSlice (w:=6) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S33 : SliceN p14_R p14_T (0x3030000030300000303000003030,1,[0, 3]) := mkSlice (w:=4) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S34 : SliceN p14_R p14_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]) := mkSlice (w:=1) p14_B p4_B p4_L (by decide +kernel)
theorem p14_S35 : SliceN p14_R p14_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]) := mkSlice (w:=2) p14_B p4_B p4_L (by decide +kernel)
theorem p14_S36 : SliceN p14_R p14_T (0xc000c000c000c000c000c000c000c,1,[0, 4]) := mkSlice (w:=2) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S37 : SliceN p14_R p14_T (0x44004400440044004400440044004400,1,[2, 4]) := mkSlice (w:=10) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S38 : SliceN p14_R p14_T (0x44440000444400004444000044440000,1,[2, 3]) := mkSlice (w:=18) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S39 : SliceN p14_R p14_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,2,[1, 3, 4]) := mkSlice (w:=5) p14_B p2_B p2_L (by decide +kernel)
theorem p14_S40 : SliceN p14_R p14_T (0xa000a000a000a000a000a000a000a0,1,[1, 4]) := mkSlice (w:=5) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S41 : SliceN p14_R p14_T (0xf0f00000f0f00000f0f00000f0f,2,[0, 1, 3]) := mkSlice (w:=0) p14_B p3_B p3_L (by decide +kernel)
theorem p14_S42 : SliceN p14_R p14_T (0xa0a00000a0a00000a0a00000a0a0,1,[1, 3]) := mkSlice (w:=5) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S43 : SliceN p14_R p14_T (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S44 : SliceN p14_R p14_T (0xc000c000c000c000c000c000c000c000,1,[0, 4]) := mkSlice (w:=14) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S45 : SliceN p14_R p14_T (0xc0c00000c0c00000c0c00000c0c00000,1,[0, 3]) := mkSlice (w:=22) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S46 : SliceN p14_R p14_T (0x220022002200220022002200220022,1,[2, 4]) := mkSlice (w:=1) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S47 : SliceN p14_R p14_T (0xaa000000aa000000aa000000aa00,1,[1, 2]) := mkSlice (w:=9) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S48 : SliceN p14_R p14_T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S49 : SliceN p14_R p14_T (0xf0000000f0000000f0000000f0,1,[0, 1]) := mkSlice (w:=4) p14_B p6_B p6_L (by decide +kernel)
theorem p14_S50 : SliceN p14_R p14_T (0xaa000000aa000000aa000000aa0000,1,[1, 2]) := mkSlice (w:=17) p14_B p5_B p5_L (by decide +kernel)
theorem p14_S51 : SliceN p14_R p14_T (0x55000000550000005500000055000000,1,[1, 2]) := mkSlice (w:=24) p14_B p6_B p6_L (by decide +kernel)
def p14_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6,[0, 1, 3, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa,4,[1, 2, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]),(0xaaaa0000aaaa0000aaaa0000aaaa,4,[1, 2, 3]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xff000000ff000000ff000000ff000000,4,[0, 1, 2]),(0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]),(0x55555555555555555555555555555555,3,[1, 2, 3, 4]),(0x8080808080808080808080808080808,1,[3, 4]),(0x33333333333333333333333333333333,3,[0, 2, 3, 4]),(0x22222222222222222222222222222222,2,[2, 3, 4]),(0x330033003300330033003300330033,2,[0, 2, 4]),(0x55005500550055005500550055005500,2,[1, 2, 4]),(0x3300000033000000330000003300,1,[0, 2]),(0x330000003300000033000000330000,1,[0, 2]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0x50505050505050505050505050505050,2,[1, 3, 4]),(0x30303030303030303030303030303030,2,[0, 3, 4]),(0x300030003000300030003000300030,1,[0, 4]),(0x50005000500050005000500050005000,1,[1, 4]),(0xf000f000f000f000f000f000f000f,2,[0, 1, 4]),(0xf0000000f0000000f0000000f00,1,[0, 1]),(0xf0000000f0000000f0000000f0000,1,[0, 1]),(0x50500000505000005050000050500000,1,[1, 3]),(0x88888888888888888888888888888888,2,[2, 3, 4]),(0x880088008800880088008800880088,1,[2, 4]),(0x3333000033330000333300003333,2,[0, 2, 3]),(0x8888000088880000888800008888,1,[2, 3]),(0x20202020202020202020202020202020,1,[3, 4]),(0x40404040404040404040404040404040,1,[3, 4]),(0x3030000030300000303000003030,1,[0, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]),(0xc000c000c000c000c000c000c000c,1,[0, 4]),(0x44004400440044004400440044004400,1,[2, 4]),(0x44440000444400004444000044440000,1,[2, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,2,[1, 3, 4]),(0xa000a000a000a000a000a000a000a0,1,[1, 4]),(0xf0f00000f0f00000f0f00000f0f,2,[0, 1, 3]),(0xa0a00000a0a00000a0a00000a0a0,1,[1, 3]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(0xc000c000c000c000c000c000c000c000,1,[0, 4]),(0xc0c00000c0c00000c0c00000c0c00000,1,[0, 3]),(0x220022002200220022002200220022,1,[2, 4]),(0xaa000000aa000000aa000000aa00,1,[1, 2]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0xf0000000f0000000f0000000f0,1,[0, 1]),(0xaa000000aa000000aa000000aa0000,1,[1, 2]),(0x55000000550000005500000055000000,1,[1, 2])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨p14_S0,p14_S1,p14_S2,p14_S3,p14_S4,p14_S5,p14_S6,p14_S7,p14_S8,p14_S9,p14_S10,p14_S11,p14_S12,p14_S13,p14_S14,p14_S15,p14_S16,p14_S17,p14_S18,p14_S19,p14_S20,p14_S21,p14_S22,p14_S23,p14_S24,p14_S25,p14_S26,p14_S27,p14_S28,p14_S29,p14_S30,p14_S31,p14_S32,p14_S33,p14_S34,p14_S35,p14_S36,p14_S37,p14_S38,p14_S39,p14_S40,p14_S41,p14_S42,p14_S43,p14_S44,p14_S45,p14_S46,p14_S47,p14_S48,p14_S49,p14_S50,p14_S51,by simp⟩
def p14_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(1,[(0,0,1)]),(3,[]),(4,[]),(5,[]),(6,[]),(1,[(3,0,1)]),(0,[(0,0,1)]),(0,[(3,0,1)]),(0,[(0,0,2)]),(1,[(0,0,2)]),(7,[]),(8,[]),(0,[(1,0,2)]),(1,[(1,0,2)]),(0,[(2,0,2)]),(1,[(2,0,2)]),(0,[(3,0,2)]),(1,[(3,0,2)]),(0,[(0,0,3)]),(1,[(0,0,3)]),(9,[]),(0,[(1,0,3)]),(1,[(1,0,3)]),(0,[(2,0,3)]),(1,[(2,0,3)]),(0,[(3,0,3)]),(1,[(3,0,3)]),(1,[(0,1,2)]),(1,[(2,1,2)]),(1,[(0,1,3)]),(1,[(2,1,3)]),(0,[(0,1,2)]),(0,[(2,1,2)]),(0,[(0,1,3)]),(0,[(2,1,3)]),(0,[(0,2,3)]),(1,[(0,2,3)]),(0,[(1,2,3)]),(1,[(1,2,3)]),(0,[(2,2,3)]),(1,[(2,2,3)]),(0,[(3,2,3)]),(1,[(3,2,3)]),(0,[(2,0,1)]),(10,[]),(5,[(0,0,1)]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(3,[(0,0,1)]),(18,[]),(0,[(1,0,1)]),(19,[]),(3,[(3,0,1)]),(20,[]),(21,[]),(22,[]),(23,[]),(24,[]),(25,[]),(5,[(3,0,1)]),(26,[]),(27,[]),(8,[(0,0,1)]),(28,[]),(29,[]),(3,[(1,0,2)]),(30,[]),(31,[]),(8,[(0,0,2)]),(1,[(2,0,1)]),(8,[(0,1,2)]),(32,[]),(0,[(1,1,2)]),(33,[]),(0,[(1,1,3)]),(8,[(3,0,1)]),(1,[(1,0,1)]),(34,[]),(3,[(2,0,1)]),(35,[]),(36,[]),(37,[]),(5,[(2,0,1)]),(38,[]),(39,[]),(5,[(1,1,2)]),(40,[]),(41,[]),(42,[]),(43,[]),(5,[(2,0,2)]),(8,[(3,0,2)]),(5,[(2,1,2)]),(7,[(0,1,2)]),(1,[(2,1,2),(0,0,2)]),(0,[(2,1,2),(0,0,2)]),(44,[]),(4,[(0,1,2)]),(3,[(2,0,2)]),(3,[(2,1,2)]),(1,[(2,1,3),(0,0,3)]),(0,[(2,1,3),(0,0,3)]),(45,[]),(6,[(0,1,2)]),(46,[]),(0,[(3,1,2)]),(1,[(1,1,2)]),(8,[(2,1,2)]),(1,[(3,1,2)]),(0,[(3,1,3)]),(1,[(1,1,3)]),(1,[(3,1,3)]),(8,[(3,1,2)]),(5,[(0,0,2)]),(3,[(0,1,2)]),(1,[(0,1,2),(1,2,3)]),(9,[(0,2,3)]),(3,[(0,0,2)]),(1,[(0,1,3),(1,2,3)]),(9,[(2,0,1)]),(0,[(0,1,2),(1,2,3)]),(6,[(0,2,3)]),(6,[(2,2,3)]),(0,[(0,1,3),(1,2,3)]),(9,[(2,0,2)]),(0,[(0,2,3),(1,2,3)]),(1,[(0,2,3),(1,2,3)]),(47,[]),(48,[]),(49,[]),(5,[(0,1,2)]),(8,[(2,0,1)]),(0,[(0,0,1),(1,2,4)]),(1,[(0,0,1),(1,2,4)]),(0,[(0,0,1),(1,3,4)]),(1,[(0,0,1),(1,3,4)]),(0,[(0,0,1),(1,0,1)]),(0,[(0,0,1),(3,0,1)]),(0,[(3,0,1),(2,0,1)]),(1,[(2,0,1),(3,0,1)]),(0,[(2,0,1),(3,0,1)]),(1,[(3,0,1),(2,0,1)]),(1,[(3,0,1),(0,0,1)]),(0,[(0,0,1),(1,0,2)]),(0,[(0,0,1),(3,0,2)]),(0,[(0,0,1),(2,2,4)]),(1,[(0,0,1),(2,2,4)]),(0,[(0,0,1),(1,0,3)]),(0,[(0,0,1),(3,0,3)]),(0,[(0,0,1),(1,1,3)]),(0,[(0,0,1),(3,1,3)]),(1,[(0,0,1),(2,3,4)]),(0,[(0,0,1),(2,3,4)]),(0,[(3,0,1),(0,0,1)]),(0,[(3,0,1),(1,1,2)]),(0,[(3,0,1),(1,1,3)]),(0,[(2,1,3),(3,0,1)]),(8,[(0,0,2),(0,1,2)]),(3,[(1,0,1)]),(5,[(1,0,1)]),(5,[(3,0,2)]),(3,[(3,0,2)]),(8,[(2,0,2)]),(1,[(2,1,3),(3,0,1)]),(0,[(1,0,1),(0,0,1)]),(0,[(1,0,1),(3,0,1)]),(0,[(0,0,1),(2,0,1)]),(0,[(2,0,1),(0,0,1)]),(0,[(0,1,2),(2,0,1)]),(0,[(0,1,3),(2,0,1)]),(5,[(3,1,2)]),(3,[(3,1,2)]),(0,[(0,0,2),(0,1,4)]),(0,[(0,0,2),(0,1,2)]),(8,[(1,1,2)]),(0,[(0,1,2),(2,0,2)]),(1,[(0,0,2),(2,1,2)]),(0,[(2,1,2),(2,0,2)]),(0,[(0,0,2),(2,1,2)]),(0,[(1,0,2),(0,1,4)]),(50,[]),(0,[(0,1,3),(2,0,3)]),(0,[(0,0,3),(0,1,3)]),(0,[(0,0,3),(0,1,4)]),(1,[(0,0,3),(2,1,3)]),(0,[(2,1,3),(2,0,3)]),(0,[(0,0,3),(2,1,3)]),(0,[(1,0,3),(0,1,4)]),(0,[(1,0,1),(0,2,4)]),(0,[(1,0,1),(0,3,4)]),(0,[(1,1,2),(2,1,2)]),(0,[(0,1,2),(1,1,2)]),(0,[(3,1,2),(0,1,2)]),(0,[(2,1,2),(3,1,2)]),(0,[(1,1,3),(2,1,3)]),(0,[(0,1,3),(1,1,3)]),(0,[(3,1,3),(0,1,3)]),(0,[(2,1,3),(3,1,3)]),(0,[(2,1,2),(3,1,3)]),(0,[(1,2,3),(0,1,2)]),(0,[(2,1,2),(2,2,3)]),(0,[(0,1,3),(3,2,3)]),(0,[(2,1,3),(0,1,2)]),(0,[(2,1,3),(3,1,2)]),(0,[(1,2,3),(0,1,3)]),(0,[(2,1,3),(3,2,3)]),(0,[(0,1,2),(2,2,3)]),(0,[(1,2,3),(2,1,2)]),(0,[(0,0,1),(3,2,4)]),(0,[(0,0,1),(3,3,4)]),(8,[(0,0,1),(1,2,3)]),(0,[(1,0,1),(3,0,3)]),(8,[(1,0,2)]),(8,[(1,0,1)]),(0,[(0,0,1),(3,1,2)]),(3,[(0,0,1),(1,0,1)]),(8,[(0,1,2),(1,1,2)]),(5,[(0,0,1),(1,0,1)]),(0,[(1,0,2),(0,3,4)]),(0,[(1,0,3),(0,2,4)]),(0,[(1,0,3),(3,2,4)]),(5,[(1,0,1),(0,0,1)]),(3,[(1,0,1),(0,0,1)]),(3,[(0,0,1),(1,2,3)]),(5,[(0,0,1),(1,2,3)]),(5,[(0,0,1),(2,2,3)]),(0,[(2,1,2),(1,2,3)]),(0,[(0,1,2),(3,3,4)]),(0,[(1,0,2),(3,1,4)]),(8,[(0,1,2),(0,0,3)]),(0,[(1,0,1),(3,2,4)]),(3,[(0,0,1),(2,2,3)]),(51,[]),(8,[(0,1,2),(3,0,3)])]
def p14_P : List (Nat × Nat) := [(12,13),(28,30),(5,7),(10,11),(26,30),(3,7),(6,7),(22,30),(3,11),(14,30),(18,19),(3,19),(9,11),(9,13),(5,13),(5,21),(20,21),(1,7),(1,19),(4,7),(7,14),(6,30),(8,11),(2,11),(17,19),(17,21),(7,22),(16,19),(2,19),(3,27),(4,13),(8,13),(1,11),(1,13),(4,21),(1,21),(2,7),(6,15),(6,23),(18,30),(10,30),(20,30),(12,30),(11,14),(24,30),(25,30),(3,15),(9,15),(3,23),(7,9),(8,30)]
def p14_K : List CutV := p14_C.map (mkCut p14_Z)
theorem p14_W : ∀ c ∈ p14_K, CutP p14_R p14_T c := cutsGood p14_Y (by decide +kernel)
theorem p14_Q : p14_P.all (sepOK p14_T) = true := by decide +kernel
noncomputable def p14_D8 : List StD := [
([w0,w1,w2,w3,w64],[0,1],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[[100,101,0,102],[103,104,1,105],[106,107,100,108],[100,109,110,111],[112,113,0,1,101],[102,114,0,101],[102,115,0,101],[105,108,1,104],[105,111,1,104],[108,111,107,109]])]
noncomputable def p14_D7 : List StD := [
([w4,w0,w1,w2,w3,w64],[0,2,3,4,5,6,7],[13,5,14,8,15,11,0,4,16,7,9,1],[[0],[0,1],[100,2,101],[3,102,4,103],[5,104,6,105],[0,1,106],[107,1,2,100],[3,108,109,106,1],[5,106,110,108,1],[0,100,2],[0,3,102,111],[0,5,104,111],[3,103,2,100,101],[5,105,2,107,100],[3,5,102,109,110]]),
([w7,w0,w1,w2,w3,w64],[0,2,1,5,4,7,6,8],[1,4,7,9,0,12,17,18,8,11],[[0],[0,1,100],[1,2,101],[1,3,102,4],[1,5,103,6],[0,1,104],[1,101,7],[1,4,102],[1,6,103],[0,105,7,106],[0,4,105],[0,6,107],[4,7,101,108],[6,7,101,109],[4,6,102]]),
([w8,w0,w1,w2,w3,w64],[1,9,6,4,5,7],[12,2,8,14,11,15,1,3,10,7,9,4],[[0],[100,1,101],[0,2],[3,102,4,103],[2,104,5,105],[106,1,2,100],[0,2,107],[3,108,109,107,2],[2,107,110,108,3],[0,100,1],[3,103,1,100,101],[2,105,1,106,100],[0,3,102,111],[0,2,104,111],[2,3,102,109,110]]),
([w11,w0,w1,w2,w3,w64],[4,1,0,6,10],[1,4,7,9,3,13,17,14,15,11],[[0,1],[0,2,100],[0,1,101],[0,3,102],[0,3,103],[0,100,4],[0,1,104],[0,102,3],[0,3,103],[1,105,4,106],[0,4,100,107],[3,4,100,108],[0,1,105],[1,3,109],[0,3,102]]),
([w12,w0,w1,w2,w3,w64],[4,5,0,1,6,7,11,12,13,14],[12,13,16,19,10,20,7,6,5,15,11,21],[[0,1],[0,2,100],[0,3,101],[0,4],[0,5,4],[0,102,6,103],[0,104,7,102],[0,105,106,8],[0,107,9,102],[100,101,6,7,108],[0,6,100],[4,109,6,9,110],[0,7,101],[4,110,7,9,109],[0,106,4,111]]),
([w0,w1,w2,w3,w13,w64],[4,15,16,14,6,13,0,1,5],[0,22,3,20,12,13,5,7],[[0,100,1,101],[0,102,2,100],[0,103,3,4],[0,5],[0,3,100],[104,105,1,2,106],[0,1,3],[0,1,6],[3,4],[0,2,3],[0,2,7],[3,4],[0,107],[0,3,8],[0,3]]),
([w14,w0,w1,w2,w3,w64],[4,13,5,6,17,18,14],[0,22,3,7,23,12,13,5,15,11],[[0,1],[0,2],[0,2],[0,3],[0,2],[0,100,4,101],[0,102,5,100],[0,103,2,104],[0,6,100],[105,106,4,5,107],[0,2],[3,108,4,6,105],[0,2],[3,109,5,6,106],[0,2]]),
([w15,w0,w1,w2,w3,w64],[4,14,0,1,6,19,20,13],[1,4,7,9,16,10,23,12,13,14,15,8,11],[[0,1],[0,2,100],[0,3,101],[0,102],[0,1,103,4],[0,104,5,100],[0,105,6,101],[0,7,4,106],[0,4,103],[107,108,5,6,100],[0,5,100,109],[4,5,100,110],[0,6,101,111],[4,6,101,112],[0,4,103]]),
([w65,w0,w1,w2,w3,w64],[6,14,0,1,13,4,21,22,23],[24,25,0,19,3,6,26,9,5,14,8,21],[[0,1],[0,2,100],[0,3,101],[0,1,4],[0,5],[0,102,6,103],[0,104,7,102],[0,105,1,102],[0,106,107,8],[100,101,6,7,108],[5,109,1,6,110],[0,6,100],[5,110,1,7,109],[0,7,101],[0,107,5,111]]),
([w0,w1,w2,w3,w64,w66],[4,24,25,14,23,6,0,1,7],[16,27,10,26,12,13,5,9],[[0,100,1,101],[0,102,2,100],[0,100,3],[0,3,103],[0,4],[104,105,1,2,106],[0,1,3],[3,5],[0,1,6],[0,2,3],[3,5],[0,2,7],[0,3,8,5],[0,5],[0,3,107]]),
([w67,w0,w1,w2,w3,w64],[23,6,7,4,26,27,14],[16,27,10,9,28,12,13,5,14,2,8],[[0],[1,2],[1,2],[1,2],[1,3],[1,100,4,101],[1,102,5,100],[1,6,100],[0,1,103,2,104],[105,106,4,5,107],[3,108,4,6,109],[0,1,2],[3,110,5,6,107],[0,1,2],[0,1,2]]),
([w68,w0,w1,w2,w3,w64],[6,14,0,1,4,28,29,23],[1,4,7,9,0,3,28,12,13,14,15,8,11],[[0,1],[0,2,100],[0,3,101],[0,1,102,4],[0,103],[0,104,5,100],[0,105,6,101],[0,4,102],[0,7,4,106],[107,108,5,6,100],[4,5,100,109],[0,5,100,110],[4,6,101,111],[0,6,101,112],[0,4,102]]),
([w0,w16,w1,w2,w3,w64],[4,0,1,14,23],[3,6,0,12,13,7,8,9,10,11,24,25],[[100,101,0],[1,102,103],[2,100,104],[101,105,100,106],[100,107,108,109],[1,2],[1],[0,106,3,105],[4,109,3,107],[1,2],[1,110,103],[1,103,110],[2,111,104],[2,104,111],[106,109,105,107]]),
([w0,w20,w1,w2,w3,w64],[4,13,0,30,14,1,23],[3,0,28,4,9,24,17,14,2,5,11],[[0,1,100],[0,2,101],[0,100,3,101],[0,1,100],[0,100,4,102],[0,2,4],[0,3,5,103],[0,2],[0,4,104,6],[2,105,3,106],[0,2,107],[2,108,4,105],[0,3,103],[109,110,3,4,103],[0,104,107]]),
([w22,w0,w1,w2,w3,w64],[14,4,1,0,5,31],[6,5,11,1,22,3,4,14,9,12],[[0,1,100],[0,1],[0,2,101],[0,3],[0,4,102],[3,103,1,104],[105,106,1,5,100],[0,100,107],[0,108,1,100],[3,109,5,103],[0,3,107],[0,3,109],[0,101,5],[0,102,5,101],[0,102,4]]),
([w0,w69,w1,w2,w3,w64],[23,4,6,0,32,14,1],[10,0,4,7,12,17,2,15,5,8],[[0,1,100,2],[2,3,101],[2,100,4,101],[2,100,5,101],[0,2,100],[0,3,5],[0,4,6,102],[0,5,103,1],[0,3],[3,104,4,105],[3,106,5,104],[0,3,107],[108,109,4,5,102],[0,4,102],[0,103,107]]),
([w70,w0,w1,w2,w3,w64],[14,4,0,6,1,7,33],[6,5,8,1,0,3,4,7,15,24],[[0,1,100],[0,2,3],[0,4,101],[0,5,102],[0,2],[2,103,3,104],[105,106,3,6,100],[0,107,3,100],[0,100,108],[2,109,6,103],[0,2,109],[0,2,108],[0,102,6,101],[0,101,6],[0,102,5]]),
([w0,w1,w24,w2,w3,w64],[4,34,13,1,14,0,6],[0,19,3,28,1,25,17,2,15,9,8,5],[[0,100,1,101],[0,2,100],[0,3,102],[0,2,100],[0,100,4,103],[0,1,5,104],[3,105,1,106],[0,1,104],[107,108,1,4,104],[0,3,4],[0,3],[0,4,109,6],[0,3,110],[3,111,4,105],[0,109,110]]),
([w26,w0,w1,w2,w3,w64],[14,6,0,1,4,5,35],[6,2,15,0,1,4,3,8,9,13],[[0,1,100],[0,2,101],[0,3,4],[0,3],[0,5,102],[103,104,4,6,100],[3,105,4,106],[0,100,107],[0,108,4,100],[3,109,6,105],[0,101,6],[0,102,6,101],[0,3,107],[0,3,109],[0,102,5]]),
([w0,w1,w71,w2,w3,w64],[6,36,23,1,14,0,4],[0,19,16,3,1,13,17,2,14,7,5,11],[[0,100,1,101],[0,2,102],[0,3,103],[0,102,4,100],[0,2,102],[0,1,5,104],[3,105,1,106],[107,108,1,4,104],[0,1,104],[0,3,4],[0,4,109,6],[0,3],[3,110,4,105],[0,3,111],[0,109,111]]),
([w72,w0,w1,w2,w3,w64],[14,4,0,1,6,7,37],[6,2,14,0,1,4,3,7,11,25],[[0,1,100],[0,2,101],[0,3,4],[0,5,102],[0,3],[103,104,4,6,100],[3,105,4,106],[0,107,4,100],[0,100,108],[3,109,6,105],[0,102,6,101],[0,101,6],[0,3,109],[0,3,108],[0,102,5]]),
([w0,w1,w2,w73,w3,w64],[4,38,39,23,14,13,7,5],[0,19,3,12,13,5],[[0,100,1,101],[0,102,2,100],[0,3,4],[0,5,4],[0,3,4],[103,104,1,2,105],[0,1,4],[0,1,4],[3,1,4],[0,2,4],[0,2,4],[3,2,4],[0,6],[0,3,7],[0,3]]),
([w0,w1,w2,w3,w64,w74],[40,4,41,5,6,7],[0,1,2,3,4,7,6,9,12,13,5],[[100,101,0,1,102],[103,104,1,2,100],[1,3,105,4,106],[4,5,107,1,100],[3,106,1],[108,109,0,2,101],[1,102,0,3],[4,102,0,5],[3,102,0],[1,110,2,3],[4,109,2,5],[3,110,2],[1,4,5,3],[3,4],[1]]),
([w75,w0,w1,w2,w3,w64],[7,4,0,1,6,5,42,43,13,14],[3,12,13,0,5,15,11,29],[[0,1,100],[0,2,101],[0,3,102],[0,1,4],[0,5],[1,103,6,100],[1,100,7,103],[1,8,9],[0,1,100],[101,102,6,7,104],[1,6,9],[0,105,6,101],[1,7,9],[0,106,7,102],[0,1,107]]),
([w76,w0,w1,w2,w3,w64],[5,6,0,1,7,13,44,45,23,14],[10,24,25,0,5,14,8,29],[[0,1,100],[0,2,101],[0,3,102],[0,4],[0,1,5],[1,103,6,100],[1,100,7,103],[0,1,100],[1,8,9],[101,102,6,7,104],[0,105,6,101],[1,6,9],[0,106,7,102],[1,7,9],[0,1,107]])]
noncomputable def p14_D6 : List StD := [
([w77,w4,w0,w1,w2,w3,w64],[46,10,4,47,6,9,48,3,49,50,51,52,53],[],[[0],[0],[],[1],[2,3],[3,4],[5],[6],[7],[3,8],[3,8],[5,9],[3,7,10],[3,8],[3,8],[9,5],[9,5],[9,5],[8,7],[8,7],[11,12]]),
([w77,w0,w1,w2,w3,w64],[46,9,8,10,4,50,14,6,3,48,52,47,54,55,56,53,57],[22,3,10,12,14,18,8,13,11,9],[[0],[1,2],[3],[4,5,6],[7,5,6],[1,8,9,100],[1,8,9,101],[10,11,102,12,9,101],[12,11,101,13,14,102],[8,1,103],[14,1,104,15],[9,1,103,16,105],[10,8,106,12],[9,8,107,13,108],[9,10,104,16,15,109,108]]),
([w29,w4,w0,w1,w2,w3,w64],[58,10,6,9,4,59,49,60,3,61,62,63],[],[[0],[0,1],[2,0],[3],[4,5,6],[2,5,6],[1],[7],[8],[5,6],[5,6],[1,9],[8,1],[5,6],[5,6],[1,5],[9,1],[9,1],[6,5],[6,5],[10,11]]),
([w29,w0,w1,w2,w3,w64],[0,10,58,3,60,9,49,4,14,59,6,64,65,66,67,68,63],[22,3,10,12,14,18,5,8,11,9],[[0,1,2,3],[1,4,3],[3,5],[4,6,7,8,9],[10,6,8,9],[1,3,4,100],[3,101,1],[11,9,102,12,6,101],[12,9,101,13,4,102],[3,1,103],[4,1,104,12],[12,1,103,13,105],[4,3,106,107],[14,3,106,108],[14,4,104,15,16,109,108]]),
([w4,w0,w1,w2,w3,w30,w64],[15,4,52,69,14,53,70,49,63,17],[],[[0],[1],[2,3],[1,4],[1],[2,3],[0,1],[5,1],[2,0,6],[0,1],[5,1],[2,0],[1,0,5],[1],[2,0],[1,5],[2,3],[7,6,8],[9],[1,5],[2,3]]),
([w78,w4,w0,w1,w2,w3,w64],[11,4,70,3,71,15,6,53,17,52,72],[],[[0],[0],[1],[2,3,4],[5],[6,4,7],[8],[1],[7,4],[1,2],[7,2,4],[1,7],[7,1],[9,2],[7,1],[9,4],[1,2],[9,2,4],[1,2],[10,2],[1,7]]),
([w4,w0,w1,w2,w3,w64,w79],[24,73,72,69,6,14,57,70,49,71,26],[],[[0],[1],[2,3],[2,3],[4,5],[4],[0,2],[6,3],[6,3],[2,0,7],[0,2],[2,0],[2,0],[4,0,6],[4],[8,7,9],[2,6],[2,3],[2,6],[2,3],[10]]),
([w80,w4,w0,w1,w2,w3,w64],[21,6,70,3,74,4,72,24,26,53,52],[],[[0],[0],[1],[2,3,4],[5,4,6],[7],[8],[1],[6,4],[6,2,4],[1,2],[1,8],[9,1],[10,1,2],[6,2],[6,4],[6,2,4],[1,2],[10,2],[1,2],[1,9,10]]),
([w4,w8,w0,w1,w2,w3,w64],[9,46,4,1,49,57,6,53,75,3],[],[[0,1],[0],[2],[0,3],[2,4,5],[6,4,7],[1],[5,0],[2],[2,8,4],[4,8],[0,2],[2,5],[5,4],[7,2],[0,9],[2,0,7],[6,0,5],[2,7],[4,5,6],[2,5,6]]),
([w4,w8,w1,w2,w3,w64],[9,1,46,4,3,57,76,49,6,53,70,75],[3,14,23,11,28,0,8,15,9],[[0,1,2],[0,3],[0,1,4,100],[3,5,101,6,7,100,102],[8,9,100,6,7,103,104],[0,4,105],[3],[3,5,106,10,11,101],[8,7,103,10,11,107],[4,0],[3,0,101,9],[8,0,107,5],[3,4,106,9],[8,4,103,5],[8,3,101,5,9,108,103]]),
([w11,w4,w1,w2,w3,w64],[58,77,10,4,3,9,6,51,49],[30,16,0,3,11,28,31,14,15,9],[[0,1],[2,3,4],[4,3,5],[3,6,100,101],[3,6,101,102],[2,3],[4,7,103,2],[3,8,103,7],[6,8,104,7,105],[4,2,106],[3,2,107],[6,2,108],[3,4,106],[6,4,104],[3,6,109]]),
([w4,w0,w16,w2,w3,w64],[0,3,8,6,52,56,72,78,49,48,53,59,54,55,4,79,70,68,63],[12,14,32,11,18,1,31,16,30,0,8,9],[[0],[1,2,3],[1,4,100],[5,6,101,7,8,100,102],[9,4,100,7,8,103,104],[1,3,10,105,4],[1,5,106],[4,11,107,12,8,101,108],[6,11,109,13,5,103,107],[0],[5,6,14,10,15,105],[3,4,16,15,105],[4,1,110,12],[6,1,103,13],[6,4,101,17,18,111,103]]),
([w26,w4,w0,w1,w2,w3,w64],[14,70,4,62,0,80,6,53,35,1,49,54],[],[[0],[1,2,3],[1,4],[2],[5],[6,3,7],[8],[2],[7,9],[2,0],[3,0,10],[2,7],[7,2],[3,1],[7,1,2],[11,8],[2,1],[3,1,8],[2,1],[10,1,3],[2,7]]),
([w72,w4,w0,w1,w2,w3,w64],[14,70,6,81,0,49,82,37,57,1,55],[],[[0],[1,2,3],[1,4],[2],[5,3],[6],[7],[2],[8,9],[3,0,5],[2,0],[2,7],[8,2],[8,1,2],[3,1],[10,7],[3,1,5],[2,1],[5,1,3],[2,1],[2,8]]),
([w4,w0,w1,w2,w3,w64,w74],[40,83,53,41,57,4,6,70,55],[5],[[0],[1],[2,3,100],[4,1,5],[2,1,6],[1],[0,5],[2,5],[4,6],[2,5],[5,7],[8,0],[5,0,2],[6,0,4],[0,2],[5,2],[6,4],[100,2],[5,2],[6],[5]]),
([w0,w81,w1,w2,w3,w64],[9,8,6,4,64,3,75,14,49],[0,10,12,18,8,11,9],[[0,1],[0,2,100],[0,1,2],[3,101,2,100],[2,100,3,101],[0,4,5,1],[1,2],[3,6,7,8],[2,6,7,4],[1,0,102],[3,0,102],[2,0,103],[3,1,104],[2,1,105],[2,3,106]]),
([w7,w8,w1,w2,w3,w64],[84,46,9,6,3,76,4,85,8,75],[23,10,3,22,14,8,15,11,9],[[0,1],[2,3,4],[3,0,2],[3,5,100,6,101],[3,6,101,102],[2,7,103,8],[3],[6,9,104,7,105],[3,9,106,7,107],[7,2,103,8],[6,2,103],[3,2,106],[6,8,105],[3,8,107],[3,6,108]]),
([w77,w8,w0,w1,w2,w3,w64],[0,77,8,4,75,6,3,9,56,49,85,64,57,53],[],[[0],[1],[2],[],[3,4],[4,5],[6],[7],[8],[9,4],[9,4],[6,7,10],[6,11],[11,4,12],[13,4],[10,6],[4,7],[4,7],[9,4],[9,4],[11,12,13]]),
([w37,w8,w0,w1,w2,w3,w64],[0,1,9,3,4,49,75,8,86,87,79,88,89],[],[[0],[1,2],[3],[4,1],[4,5,6],[6,5],[7],[2],[8],[5,6],[5,6],[2,7],[7,9],[10,5],[10,5],[2,7],[6,2],[6,2],[5,6],[5,6],[11,12]]),
([w37,w0,w1,w2,w3,w64],[46,8,9,3,86,75,4,14,49,6,55,79,54,90,91,89],[0,3,10,13,2,14,15,8,11,9],[[0,1,2],[2,3],[1,4,2],[4,5,6,7,8],[9,5,7,8],[2,100,1],[1,2,4,101],[10,11,102,12,5,100],[12,11,100,10,4,102],[1,2,103],[4,2,104,105],[13,2,104,106],[4,1,107,12],[12,1,103,10,108],[13,4,105,14,15,109,106]]),
([w8,w0,w1,w2,w3,w38,w64],[16,53,92,93,4,14,64,76,75,89,18],[],[[0],[1,2],[3],[4,5],[4],[1,2],[1,2],[0,4],[6,0,7],[0,4],[1,2],[6,0],[4,1],[6,1],[8,7,9],[4,0,1],[4],[6,0],[10],[4,1],[6,1]]),
([w82,w8,w0,w1,w2,w3,w64],[4,12,76,9,94,16,6,49,18,64,53,95],[],[[0],[1],[2,3,4],[0],[5],[6,4,7],[8],[9,4],[0],[0,2],[7,2,4],[10,0],[0,8],[9,2],[10,0],[9,4],[0,2],[11,2],[0,2],[7,2,4],[0,10]]),
([w8,w0,w1,w2,w3,w64,w83],[25,57,92,6,14,95,76,75,94,27],[],[[0],[1,2],[3],[1,2],[3,4],[3],[1,2],[0,3],[1,2],[5,0,6],[0,3],[5,0],[7,6,8],[3,1],[5,1],[5,0],[3,0,1],[3],[3,1],[5,1],[9]]),
([w84,w8,w0,w1,w2,w3,w64],[22,76,9,96,6,49,25,27,53,64],[],[[0],[0],[1,2,3],[4],[5,3],[6],[7],[8,3],[4],[5,1,3],[4,1],[8,3],[4,7],[9,1],[8,1,5],[9,3],[9,1],[3,1],[5,1,3],[4,1],[3,8,9]]),
([w8,w0,w16,w1,w3,w64],[46,1,9,10,6,64,56,49,78,75,48,53,79,65,66,4,76,91,89],[12,13,8,33,15,11,4,10,23,3,14,9],[[0,1],[2,3,4],[2,5,100,101],[6,7,102,8,9,101,103],[10,5,101,8,9,104,105],[2,4,11,106,5],[2,6,100],[5,12,107,13,7,102,108],[13,12,109,14,6,104,107],[1],[6,7,15,11,12,106],[4,5,16,12,106],[5,2,110,13],[10,2,100,14,104],[10,5,102,17,18,111,104]]),
([w22,w8,w0,w1,w2,w3,w64],[14,76,6,88,64,1,9,53,46,10,4,75,65,31],[],[[0],[1,2,3],[4],[1,5],[6],[2,3,7],[8],[7,6],[9],[10,0],[3,0,11],[7,3,10],[10,7],[3,1],[7,1,10],[12,6,13],[10,1],[11,1,3],[10,1],[3,1,11],[3,7]]),
([w70,w8,w0,w1,w2,w3,w64],[14,76,4,97,32,75,9,46,57,10,6,66,33],[],[[0],[1,2,3],[4],[1,4],[2,3,5],[6],[7],[8,6],[9],[3,0,5],[10,0],[8,3,10],[10,8],[8,1,5],[3,1],[11,6,12],[5,1,3],[5,1,6],[3,1,5],[10,1],[3,8]]),
([w8,w0,w1,w2,w3,w64,w74],[41,57,40,4,14,6,53,76,66],[2],[[0],[1,2,100],[3],[1,4,3],[5,4],[4],[1,3],[0,3],[1,5],[6,3],[3,7],[8,0],[3,6],[5,1],[100,1],[3,0,6],[5,0,1],[0,1],[3,5],[5],[3]]),
([w85,w0,w1,w2,w3,w64],[0,10,58,4,9,55,49,14,75,6,3],[3,10,13,14,15,11,9],[[0,1,2,3],[1,3],[4,5,1],[3,6,7,8],[9,6,7,8],[1,3,10],[10,3,100],[3,101,9,100],[9,100,3,101],[10,1,102],[3,1,103],[9,1,104],[3,8,10,102],[9,8,10,105],[3,9,106]]),
([w45,w0,w1,w2,w3,w64],[17,83,11,4,55,1,89,6,75,14,88,62,13,54,98,91],[13,5,0,10,12,15,11,9],[[0,1,2],[2,3],[4,100,5,6,101],[3,2],[7,8,1,6,9],[2,3,102],[10,3,103,11,102],[2,1,3,102,12],[13,3,102,1,103],[104,2,100],[3,2,104],[14,2,104,1,105],[3,8,100],[13,10,100,1,8,105,106],[3,15,107,14]]),
([w47,w0,w1,w2,w3,w64],[14,99,58,12,66,94,4,6,88,62,13,65,49,100,68],[12,2,16,19,3,13,11,18,9],[[0,1,2,3],[4,100,2,5,101],[3,6],[6,3],[7,8,0,5],[9,6,102,8,103],[3,6,104],[3,1,6,104,10],[11,6,104,1,102],[3,105,100],[4,6,12,100],[11,9,100,1,8,106,107],[6,3,105],[13,3,105,1,106],[6,14,108,13]]),
([w0,w1,w2,w3,w86],[4,13,14,5,0,1],[16,6,10,12,13,2,5,15,11],[[0,100,101],[0,102,100],[0,1,2],[0,2,3],[103,104,105,106],[0,2],[2,107,4],[0,2],[2,108,5],[0,2,3]]),
([w87,w0,w1,w2,w3],[4,14,6,5,0,1,13],[15,11,0,6,3,12,13,2,5,8,14],[[0,1,2,3],[2,4,100],[2,5,101],[0,2,3],[0,102,103],[0,104,102],[0,6,2,102],[105,106,107,108],[0,109,110],[0,110,109]]),
([w12,w0,w16,w1,w2,w3,w64],[17,13,101,1,19,88,6,62,79,56,12,11,14],[12,13,6,20,9],[[0],[1],[2,0,100],[2,3,101],[4],[2],[5,6,102],[7,5],[5,7],[103,8,2],[8,9],[10],[11],[1,8,12],[5,8],[10,11],[2,8,100],[7,5],[2,8,101],[5,7],[2,104]]),
([w22,w12,w0,w1,w2,w64],[4,19,14,11,12,6,5,31,88,102],[5,11,32,33,14,16,10,6,12,13],[[0,1],[0,2,3],[0],[2,4,100],[2,5,101,6],[0,2],[0,1,3,102],[0,7,103],[0,2,104],[3,0,105],[8,0,106,9,105],[2,0,107],[108,3,9,109],[2,3,108],[2,8,100,9]]),
([w26,w12,w0,w1,w2,w64],[4,20,88,14,12,11,6,5,35,62,103],[2,15,32,8,16,19,10,6,13,12],[[0,1],[0,2,3,4],[3,5,100],[0],[3,6,101,7],[0,3],[0,8,102],[0,1,4,103],[0,3,103],[9,0,104,2,105],[2,0,106,4],[3,0,107],[4,108,10,109],[3,9,100,2],[3,2,108,4]]),
([w0,w16,w1,w2,w3,w13,w64],[65,6,104,54,48,19,78,16,15,4,56,17],[20],[[0,1,2],[3,2],[0,2],[100,0,4],[5],[0,6],[7],[8],[9,6],[1],[1,2,6],[7,0],[10,0],[0,5],[0,2,6],[10,3],[3,7],[3,2,6],[11],[4,2,10],[2]]),
([w0,w48,w1,w2,w3,w64],[15,4,62,14,6,54,1,89,5],[0,3,20,13,5],[[0,1],[0,1,100],[101,1,2,100],[1,102,3,4],[3,1,100],[0,1],[5,103,6,7,104],[0,1,3],[3,2,4],[0,103],[1,0,3],[3,0,4],[1,3],[3,4],[1,3,8]]),
([w0,w48,w2,w3,w64],[6,15,5,14,1,4],[0,3,20,12,13,5],[[0,100,1],[0,101,100],[0,2,102],[0,100,3],[103,104,4,105],[2,5],[0,3],[2,5],[0,3],[0,2,5]]),
([w0,w1,w50,w2,w3,w64],[4,88,9,16,5,6,14,65,94],[0,22,3,20,12,2],[[100,0,1,101],[1,0,2,3],[1,0,102,3],[0,103,4,5],[5,100,0,6],[7,104,8,2,105],[3,104],[0,4],[5,1,6],[0],[0,3,4],[5,6],[0,3,4],[5,3,6],[0,4]]),
([w0,w1,w50,w3,w64],[4,16,5,6,14,0],[0,3,20,12,13,2],[[0,100,101],[0,101,1],[0,102,2,3],[0,3,100,4],[103,104,105,5],[0,2],[3,4],[0,2],[3,4],[0,2]]),
([w0,w1,w2,w3,w88],[6,5,21,14,4],[0,6,3,12,13,2,5],[[0,100,101],[0,102,100],[0,1,101],[0,2,3,4],[103,104,105,106],[1,4],[0,2,3],[1,4],[0,3],[0,1,4]]),
([w89,w0,w1,w2,w3],[14,4,21,6,5],[0,3,20,12,13,2,5],[[0,1,2],[0,2,3],[0,3],[0,1,3,4],[1,100,101],[1,101,100],[0,1,102,3],[103,104,105,106],[0,1],[0,1]]),
([w14,w0,w16,w1,w2,w3,w64],[11,5,4,105,56,15,65,104,54,79,86,17,6,14,78],[23],[[0],[1,2],[3,0,4],[3,4],[5],[3,4],[6,2,7],[8,4,7],[6,4,7],[9,3,100],[6,4,9],[10],[11],[2,1],[12,7,13],[11,8],[4,3],[6,7,14],[4,3],[8,7,14],[4,3]]),
([w90,w0,w1,w2,w3,w64],[0,19,15,70,4,54,1,69,6,14,62,88,13,63,75,49],[13,5,0,10,14,15,11,9],[[0,1,2,3],[1,4],[5,100,6,7,101],[4,1],[8,7,9,10],[1,4,102],[11,4,103,10,102],[4,12,8,102],[5,4,102,3,103],[1,100,13],[4,1,104],[8,1,105],[4,14,100,15],[5,8,10,105,11,106],[4,8,107]]),
([w91,w0,w1,w2,w3,w64],[9,20,14,76,65,94,6,12,4,88,62,13,89,49,75],[12,2,16,19,3,11,18,8,9],[[0,1,2,3],[4,100,0,5,101],[1,6],[7,8,1],[6,5,2,9],[10,6,102,9,103],[1,6,104],[8,11,6,104],[4,6,104,8,102],[1,100,12],[5,8,13,100,14],[4,6,9,105,10,106],[8,1,107],[6,1,105],[6,8,108]]),
([w15,w0,w16,w1,w2,w3,w64],[15,4,56,1,11,88,62,48,86,19,14,20,75,49],[9,6,23],[[0],[1],[2,0],[2,3],[4],[2,100],[5,1,101],[6,2,5],[5,2,6],[5,7,102],[100,2],[8],[9],[1,10],[5,10,7],[9,11],[2,9,12],[6,5],[2,11,13],[5,6],[2,100]]),
([w92,w0,w1,w2,w3,w64],[26,83,21,6,54,1,89,4,75,79,14,97,62,106],[13,5,0,3,6,15,34,24,14,35,9],[[0,1,2],[2,3],[4,100,5,6,101],[7,8,1,9,10],[3,2],[2,3,102],[11,3,103,12,102],[12,3,104,1,102],[2,1,3,105,106],[107,2,100],[13,2,107,1,108],[3,2,105],[13,11,101,1,8,100],[3,8,105,109],[3,6,110,12,105]]),
([w93,w0,w1,w2,w3,w64],[27,88,22,65,0,63,6,4,49,14,79,81,107,99],[12,2,0,19,3,6,11,28,25,18,8,9],[[0,1,2],[3,100,4,5,101],[2,6],[7,8,9,10],[6,2],[11,5,102,1,6,103],[1,6,104,2],[1,6,105,3,102],[2,6,106,107],[2,108,100],[12,11,101,3,8,100],[3,6,1,106,109],[12,2,108,13,110],[6,2,106],[6,5,111,1,106]]),
([w0,w1,w2,w94,w64],[6,14,7,23,0,1],[0,6,3,12,13,2,5,14,8],[[0,100,101],[0,102,100],[0,1,2],[0,3,1],[103,104,105,106],[1,107,4],[0,1],[1,108,5],[0,1],[0,1,2]]),
([w95,w0,w1,w2,w64],[4,14,19,7,1,6,23],[14,8,0,6,3,28,12,13,2,5,11,15],[[0,1,2,3],[0,2,100],[0,4,101],[0,1,3,5],[0,102,103],[0,104,102],[0,5,6,105],[106,107,108,109],[5,110,111],[5,111,110]]),
([w65,w0,w16,w1,w2,w3,w64],[26,6,48,1,28,65,54,21,22,79,4,14,81,97],[24,25,6,26,9,21],[[0],[1],[2,0,100],[2,3,101],[2],[4],[5,1,102],[6,2,7],[5,2,8],[9,2],[103,9,5],[8],[7],[10,9,11],[1,9,11],[7,6],[12,5,7],[2,7,100],[13,6,8],[2,8,101],[2,104,105]]),
([w70,w65,w0,w1,w2,w3],[6,28,14,21,22,4,7,33,97,108],[5,8,18,35,15,0,3,6,24,13],[[0,1],[0,2,3],[0],[2,4,100],[2,5,101,6],[0,2],[0,1,3,102],[0,7,103],[0,2,104],[3,0,105],[8,0,106,9,105],[2,0,107],[108,3,9,109],[2,3,108],[2,8,100,9]]),
([w72,w65,w0,w1,w2,w3],[6,29,14,22,21,4,7,37,81,109],[2,14,18,11,0,19,3,6,25,12],[[0,1],[0,2,3],[2,4,100],[0],[2,5,101,6],[0,2],[0,7,102],[0,1,3,103],[0,2,103],[8,0,104,9,105],[3,0,106],[2,0,107],[3,108,9,109],[2,8,100,9],[2,3,108]]),
([w0,w16,w1,w2,w3,w64,w66],[66,4,110,55,78,56,28,86,24,6,48,1,26],[26],[[0,1,2],[3,2],[0,2],[0,4],[100,0,5],[6],[7],[8],[1,2,4],[9,4],[1],[8,3],[0,2,4],[10,0],[0,6],[3,2,4],[10,3],[3,11],[5,2,10],[2],[12]]),
([w0,w96,w1,w2,w3,w64],[24,4,81,6,14,55,1,69,7],[0,10,13,5],[[0,1],[0,1,100],[101,1,2,100],[1,101,3,4],[2,1,100,3,4],[0,1],[5,102,6,7,103],[1,4],[0,3,4],[0,102],[1,0,4],[3,0,4],[1,2,4],[3,4],[1,3,8]]),
([w0,w96,w2,w3,w64],[4,24,14,1,6,7],[0,10,12,13,5],[[0,100,1],[0,101,100],[0,101,2],[0,2,100],[102,103,3,104],[0,2],[2,4],[0,2],[2,4],[0,2,5,4]]),
([w0,w1,w97,w2,w3,w64],[6,97,9,25,4,14,65,94,7],[16,22,3,12,2],[[100,0,1,101],[1,0,2,3],[1,0,102,3],[4,100,0,5],[0,102,3,5],[6,103,7,2,104],[3,103],[4,1,5],[0,5],[0],[4,5],[0,3,5],[4,3,5],[0,3,5],[0,4,8]]),
([w0,w1,w97,w3,w64],[6,25,4,14,0,7],[16,3,12,13,2],[[0,100,101],[0,101,1],[0,2,100,3],[0,101,2,3],[102,103,104,4],[2,3],[0,3],[2,3],[0,3],[0,2,5]]),
([w0,w1,w2,w98,w64],[4,11,14,6,7],[16,6,10,12,13,2,5],[[0,100,101],[0,102,100],[0,1,2,3],[0,2,101],[103,104,105,106],[0,1,2],[2,3],[0,2],[2,3],[0,2,4,3]]),
([w99,w0,w1,w2,w64],[14,6,11,4,7],[30,23,12,13,2,5],[[0,1,2],[0,2,3],[0,3],[0,1,3,4],[1,100,101],[1,101,100],[0,1,100],[102,103,104,105],[0,1],[0,1]]),
([w67,w0,w16,w1,w2,w3,w64],[21,7,6,111,48,24,55,110,66,78,79,90,26,4],[28],[[0],[1,2],[3,0,4],[3,4],[3,4],[5],[6,2,7],[6,4,7],[8,4,7],[6,4,9],[10,3,100],[11],[12],[13,7,9],[2,1],[12,6],[8,7,9],[4,3],[6,7,9],[4,3],[4,3]]),
([w100,w0,w1,w2,w3,w64],[0,28,24,6,55,1,69,4,14,81,97,23,68,62,49],[13,5,0,3,6,28,14,15,11,7],[[0,1,2,3],[1,3],[4,100,5,6,101],[7,6,8,9],[3,1],[1,3,102],[10,3,103,9,102],[4,3,104,7,102],[3,11,7,105],[1,100,12],[7,1,106],[3,1,107],[4,7,9,100,10],[3,13,107,14,108],[3,7,109]]),
([w101,w0,w1,w2,w3,w64],[9,29,6,66,94,4,81,14,97,23,91,49,75],[12,2,0,19,3,6,28,11,18,8,7],[[0,1,2],[3,100,0,4,101],[1,2],[5,6,7,8],[2,1],[6,2,102,8,103],[1,2,104],[3,2,105,5,102],[2,9,5,106],[1,100,10],[3,5,8,100,6],[2,11,107,12,108],[5,1,109],[2,1,107],[2,5,110]]),
([w68,w0,w16,w1,w2,w3,w64],[24,6,48,1,21,97,81,56,90,28,14,29,75,49],[7,6,28],[[0],[1],[2,0],[2,3],[2,100],[4],[5,1,101],[6,2,5],[5,2,6],[100,2],[5,7,102],[8],[9],[5,10,7],[1,10],[9,11],[6,5],[2,9,12],[5,6],[2,11,13],[2,100]]),
([w77,w0,w16,w1,w2,w3,w64],[46,10,8,97,49,3,81,55,79,9,75,62],[9],[[0],[1],[2],[1],[3],[4],[3],[5,3,6],[3,5],[7,4,8],[3,4,7],[5],[9],[3,8],[4,8],[5,9],[6,3],[10,4],[3,5],[4,5],[3,100,11]]),
([w0,w16,w1,w102,w2,w3,w64],[110,6,48,10,79,49,90,46,58,1,84,75],[],[[0,1],[0,2],[3],[0,2],[4,2],[4,0,5],[6],[7],[8],[5,0],[1,4,5],[9,2,3],[8,10],[11,0],[2,4,11],[3,2,7],[0],[4],[5,0],[2,4,5],[2,0]]),
([w103,w0,w16,w1,w2,w3,w64],[9,58,1,79,75,110,85,51,77,46,112,104],[],[[0],[1],[2,0],[0,1,2],[3,4],[3,4],[5],[5,6],[5,7],[3,4],[3,4],[8],[9],[4,3],[4,3],[8,6],[4,3],[4,3],[6,3],[6,3],[10,5,11]]),
([w103,w0,w1,w2,w3,w64],[9,46,77,4,79,14,75,6,68,48,91,104,110,56,63,89],[1,19,4,36,6,8,37,11,38,12,14,9],[[0],[1,2],[0,1,2],[3,4,5,6],[7,4,5,6],[1,8,100,9,101],[2,10,102,9,103],[104,4,11,6,105,106],[104,4,12,6,107,108],[2,1,109],[13,1,110,14],[9,1,109,8,100],[13,2,105,15],[9,2,107,10],[9,13,105,8,11,111,107]]),
([w104,w0,w16,w1,w2,w3,w64],[58,9,3,48,79,56,97,81,8,10,75,49],[9],[[0],[1],[2],[1],[3,4],[5,4],[6,3],[7,3,6],[6,3,7],[4,3],[4,5],[8],[9],[5,4,6],[3,4,10],[8,9],[5,4,7],[3,4,10],[5,4,6],[3,4,11],[3,100,5]]),
([w0,w105,w16,w1,w2,w3,w64],[97,104,81,55,35,31,113,56,30,34,75,49],[],[[0,1],[0,1],[2,0],[0,1],[3,1],[0,3],[4],[5],[4],[6],[7,1],[8],[9],[0,7],[10,1],[8,9],[2,0],[10,1],[0,2],[11,1],[0,1,7]]),
([w0,w16,w1,w2,w3,w106,w64],[55,104,66,79,65,114,80,14,113,62,78,88,35],[],[[0,1],[0,1],[2,1],[0,1],[0,1],[3,0,4],[5],[6],[7,3],[8],[9,1],[5,2],[2,3,4],[2,4],[4,1,2],[0,3,10],[0,5,6],[11,0,1],[12],[9,1],[9,1]]),
([w107,w0,w16,w1,w2,w3,w64],[78,34,30,80,75,55,104,97,115,35,49,62],[6],[[0,100],[1],[2],[1],[3],[4],[5,6],[5,6],[7,6],[5,0],[7,0],[8],[9],[4,0],[4,0,6],[9,5],[4,0,7],[4,0,6],[5,0],[10,0,4],[7,6,11]]),
([w108,w0,w16,w1,w2,w3,w64],[104,65,80,1,34,62,55,116,113,4,79,56,54],[],[[0,1],[2],[3,1,2],[2,3],[4],[0],[1,0],[5,0],[1,0],[5,0],[1,6],[7],[8],[9,10],[5,0],[7,1],[11,1],[1,0,5],[6,7,12],[12,0,6],[5,0]]),
([w0,w109,w16,w1,w2,w3,w64],[55,110,65,37,33,75,117,32,36,6,49,48],[],[[0,1],[0,1],[0,1],[2,1],[0,2],[2,0],[3],[4],[3],[5,1],[6],[7],[8],[5,1],[5,9],[7,2],[5,1],[2,8,5],[0,1,10],[8,0,5],[11,1]]),
([w0,w16,w1,w2,w3,w64,w110],[55,104,65,118,82,97,14,79,117,81,78,54,110,37],[],[[0,1],[0,1],[2,1],[0,1],[2,0],[2,0],[3],[4],[5,6,7],[6,1],[8],[3,2],[9,2,4],[2,1,10],[2,3],[0,3,5],[11,0],[4,3],[5,1,12],[5,7],[13]]),
([w111,w0,w16,w1,w2,w3,w64],[78,36,32,110,82,55,65,115,37,81,75,54],[6],[[0,100],[1],[2],[1],[3],[4],[5,3],[5,3],[6,3],[5,0],[6,0],[7],[8],[9,0,3],[10,0],[8,5],[9,0,3],[6,0],[5,0],[11,0],[9,3]]),
([w112,w0,w16,w1,w2,w3,w64],[65,55,82,1,81,36,110,119,117,6,104,66,54],[],[[0,1],[2],[0,2,3],[2,3],[4],[5],[0,6],[1,6],[0,4],[1,0],[0,1],[7],[8],[4,6],[9,10],[7,0],[4,0,6],[0,8,11],[1,4,12],[12,1],[4,6]]),
([w0,w16,w1,w2,w73,w3,w64],[55,6,38,65,39,78,81,4,48,42,44,56],[6],[[0,1,100],[0,2],[3,4],[0,5],[0,3],[3,0],[4],[2],[1,5],[6,5,7],[1,5],[2,0],[3,2,5],[6,2],[3,2,5],[0,4,5],[0,4,5],[8,0],[9],[10],[11,6]]),
([w0,w16,w1,w2,w3,w64,w74],[55,6,104,65,41,40,4,14,66,78,54,110,44,42],[6],[[0,1,2],[0,2],[3,2],[0,2],[3,0],[100,0],[4],[5],[6,7],[1,2,7],[7],[4,3],[8,3],[3,2,8],[3,5],[0,4,9],[10,0],[0,4],[11,2],[12],[13]]),
([w75,w0,w16,w1,w2,w3,w64],[78,54,0,65,38,40,6,110,66,115,42,4,56],[29],[[0,1],[0],[0,2,3],[0,1],[4],[5],[1,6,7],[1,7],[3,7],[8,0],[1,0],[9],[10],[11,0],[6,0],[10,1],[8,0],[3,0],[12,0],[1,0],[12,7,100]]),
([w76,w0,w16,w1,w2,w3,w64],[78,66,1,55,40,38,6,104,54,90,44,4,48],[29],[[0,1],[0],[0,1],[0,2,3],[4],[5],[1,6,7],[3,7],[1,7],[1,0],[8,0],[9],[10],[11,0],[6,0],[10,3],[1,0],[12,0],[3,0],[8,0],[12,7,100]]),
([w113,w0,w1,w2,w3,w64],[4,66,81,35,14,30,6,104,75,13,65,120],[3,6,0,28,12,18,11,9],[[0,1,100,2,101],[3,1,4,5],[0],[0,2,4,3],[6,7,4,8],[2,0,102,3],[1,0,100,2,5],[0,9,100],[2,0,100,1,103],[1,3,104,5],[0,3,104],[10,3,104,1,105],[0,2,5,3],[5,106,11],[0,107,2]]),
([w26,w0,w20,w1,w2,w64],[14,121,4,80,35,30,5,13],[6,15,8,23,0,3,33],[[0,1,2,100],[2,0,3],[0,3,4,5],[2],[0,6,101],[2,7,102,103],[4,2,104],[5,2,105],[0,2,100],[0],[2,5,4],[0,2,102],[5,4,106],[0,4,101],[0,5,106]]),
([w0,w20,w1,w71,w2,w3,w64],[66,6,81,36,4,121,14,122,1,30],[3,16],[[0,1,100],[2,3],[0,4,101],[0,2],[0,5,6],[2,0],[6],[1,4],[7,8],[3],[1,6],[0,3],[0,3,9],[3,2],[5,0],[6],[2,6,4],[9],[7,2,6],[6,5],[2,7]]),
([w0,w20,w1,w2,w64,w74],[4,13,6,40,66,123,14,41,44],[3,0,6,39,13,2,5],[[0,1,2,100],[3,0,101],[4,0,100,5,101],[6,0,100],[6,0,102],[3,0,6],[0,5,7,103],[0,3,2],[6,0,8],[4,3,104,5],[6,3,105],[6,3,105],[6,104,5],[6,106,5],[0]]),
([w114,w0,w1,w2,w3,w64],[17,14,11,4,91,1,51,79,6,88,63,5],[5,13,1,10,6,12],[[0,1],[2,3],[4,100,5,6,101],[1,2,3],[1,7,8,6],[2,3,102],[9,3,103,104],[1,2,3,103],[1,3,104],[105,2,10,101],[1,2,3],[1,2,105],[1,3],[1,9,100,7],[1,3,11]]),
([w0,w1,w57,w2,w3,w64],[34,63,60,66,81,4,31,14,75,88,6,5],[0,6,3,12,14,5,11],[[0,1,100,2],[3,101,4,2,5,100],[3,102,4,2,6],[3,101,7,8],[4,1,100,3,2,7],[2,0,1,5],[3,0,103,1,6],[2,0,104,1],[7,0,103],[6,7],[0,2,4,5],[7,9,10,1],[0,6,7],[7,6,105],[4,2,104,7,11,106]]),
([w22,w0,w1,w24,w2,w64],[4,14,113,1,34,5,13,31],[6,11,0,3,32,14],[[0,1,100],[0],[0,1,2],[1,3,4],[1,5,101],[4,0,102],[0,6,102],[7,0,103],[1,0,100],[0,2,4,7],[7,4,104],[1,4,104],[1],[0,1,105],[1,7,101]]),
([w115,w0,w1,w2,w3,w64],[6,66,81,37,33,32,4,91,5,120,23,88],[3,6,0,11,28,12,2,18,8,7],[[0,1,100,2,101],[3,1,4,5],[0],[6,7,8,2],[0,5],[2,0,102,3],[1,0,100,2,5],[1,0,101,9,100],[0,10,103,104],[1,3,105,5],[1,2,106,3,9,105],[0,3,107],[5,108,9],[0,5,3],[0,109,11]]),
([w0,w69,w1,w24,w2,w3,w64],[124,4,55,34,6,65,32,33,5,125,14],[10,0],[[0,1,100],[2,3],[2,4,101],[5,6],[2,5],[0,2],[7],[0,1],[0,6],[0,8,1],[3],[5,3],[2,3],[9,3,5],[3,10],[10],[6],[0,10],[6,10],[0,2],[0,9]]),
([w72,w0,w69,w1,w2,w3],[14,125,6,82,37,32,7,23],[6,14,11,28,0,3,12,8],[[0,1,2,100],[2,0,3],[0,3,4,5],[2],[0,6,101],[2,7,102,103],[4,2,104],[5,2,105],[0,2,100],[0],[2,5,4],[0,2,102],[5,4,106],[0,4,101],[0,5,107]]),
([w0,w69,w1,w2,w3,w74],[23,4,6,40,65,126,14,41,42],[10,0,6,40,12,17,2,5],[[0,1,2,100],[3,2,101],[4,2,100,5,101],[6,2,100],[6,2,102],[3,0,6],[0,5,7,103],[0,3,1],[6,0,8],[4,3,104,5,105],[6,3,106],[6,3,106],[6,107,5],[6,107,5],[0]]),
([w116,w0,w1,w2,w3,w64],[26,14,21,127,6,91,1,51,4,97,63,75,7],[5,13,1,3,6,24],[[0,1],[2,3,4],[5,100,6,7,101],[1,5,8,7],[1,2,4],[2,4,102],[9,4,103,104],[1,4,104],[1,2,4,103],[105,2,10,101],[1,2,105],[1,2,4],[1,9,100,11],[1,4],[1,4,12]]),
([w0,w1,w117,w2,w3,w64],[36,68,67,65,81,6,33,14,75,97,4,7],[0,6,3,12,14,5],[[0,1,100,2],[3,101,4,2,5,100],[3,102,4,2,6],[7,1,101,2],[3,100,7,8],[2,0,1,5],[3,0,103,1,6],[7,0,104],[2,0,103,1,6],[6,7],[7,9,10,1],[0,2,6],[7,6,105],[0,6,7],[2,7,104,11]]),
([w70,w0,w1,w71,w2,w3],[14,122,6,117,1,36,7,23,33],[6,8,0,15,34,3,13,14],[[0,1,2,100],[2],[2,0,3],[0,4,5],[0,6,101],[5,2,102],[2,7,103,104],[8,2,105],[0,2,100],[2,3,5,8],[8,5,106],[0,5,107],[0],[0,2,103],[0,8,101]]),
([w118,w0,w1,w2,w3,w64],[4,81,97,35,115,34,23,75,88,7,31,13,54],[0,6,3,28,13,15,11,9],[[0,1,100,2,101],[0],[3,4,5],[0,2,3,1],[6,7,4,8,9],[1,0,100,2,5],[2,0,102,1,10],[0,11,100],[1,0,100,4,103],[10,5,104],[0,2,5,10],[5,105,4],[0,1,10,104],[12,8,104,4,7,10,106],[0,107,1]]),
([w0,w1,w24,w2,w64,w74],[55,4,128,13,6,41,129,40,130,45],[0,19,3,6,41,12,2,5],[[0,1,100,2,101],[0,1,3,4,100],[5,1,102],[6,1,100],[6,1,103],[1,2,7,104],[5,0,105,2],[6,105,2],[6,106,2],[5,1,8],[1,5,4],[6,1,9],[6,5,107],[6,5,107],[1]]),
([w119,w0,w1,w2,w3,w64],[18,14,63,0,85,12,4,23,62,91,79,5],[2,12,16,6,4,13],[[0,1],[2,100,3,4,101],[5,6],[1,5,4,6],[1,2,7,4],[8,2,102,6,103],[5,6,104],[1,5,4,102],[1,2,103,4],[4,105,2,5,9,101],[1,6],[1,8,100,10],[1,4,6],[1,4,105,2],[1,6,11]]),
([w0,w61,w1,w2,w3,w64],[55,88,4,35,86,89,30,14,75,23,5],[6,3,0,13,2,8,11],[[0,100,1,2,101],[0,102,1,3,4],[1,5,101,6,4],[0,100,7,8],[7,5,100,4],[3,7],[2,0,3],[2,3,6],[7,8,9,1],[6,0,103,3],[4,3,6,7],[7,3,104],[0,6,105,3],[7,1,103,6],[7,105,10,106]]),
([w120,w0,w1,w2,w3,w64],[6,55,88,37,36,4,75,14,97,33,115,23],[0,6,3,11,28,13,14,5,7],[[0,1,100,2,101],[0],[3,1,4],[5,6,7,8],[0,2,3,4],[1,0,100,2,4],[2,0,102,9],[1,0,101,10,100],[0,11,103,104],[9,1,105,4],[4,106,10],[0,2,4,9],[1,8,107,9,10,105],[0,6,9,103],[0,108,2]]),
([w0,w1,w71,w2,w3,w74],[54,6,131,23,4,41,14,40,43],[0,19,16,3,6,42,12,2,5],[[0,1,100,2,101],[0,1,3,4,102],[5,1,103],[6,1,102],[6,1,104],[1,2,7,105],[5,0,106,2],[6,107,2],[6,107,2],[5,1,6],[1,5,4],[6,1,8],[6,5,108],[6,5,108],[1]]),
([w121,w0,w1,w2,w3,w64],[14,63,0,85,22,132,6,91,4,81,7],[2,12,0,6,4,25],[[0],[1,100,2,3,101],[4,5,6],[0,7,8,3],[0,1,4,3,6],[9,1,102,6,103],[4,6,104],[0,6,103],[0,1,4,3,102],[3,105,1,4,7,101],[0,9,100,7],[0,6],[0,3,105,4],[0,3,6],[0,6,10]]),
([w0,w122,w1,w2,w3,w64],[81,88,4,37,90,91,32,14,75,7],[6,3,0,13,2,8],[[0,100,1,2,101],[0,102,1,3,4],[1,5,101,0,4,6],[1,5,100,7,4],[0,100,7,8],[3,7],[4,3],[2,0,7,5],[3,6],[6,3,103],[7,0,104,3],[4,3,6,7],[7,6,105],[4,1,103,5,6,3],[0,1,105,5,7,9]]),
([w0,w1,w2,w73,w74],[6,133,134,23,14,38,39],[0,19,3,6,12,13,5,14,8,29],[[0,100,1,101],[0,102,2,100],[0,3,4],[0,4,103],[104,105,1,2,106],[0,1,4],[4,107,1,5],[0,2,4],[4,108,2,6],[0,4,109]]),
([w123,w0,w1,w2,w3,w64],[6,14,63,0,135,91,1,136,137,4,7],[2,12,5,13,1,4,6],[[0,1],[2,100,3,4,101],[5,102,6,4,103],[0],[0,1],[0,104,7],[0,105,8],[1,0,106],[0,106,1],[101,103,2,5,100],[1,9],[0,1],[1,9],[0,1],[0,1,10]]),
([w0,w124,w1,w2,w3,w64],[81,104,4,40,125,91,14,121,89,55,1,137,7],[6,3,0,5,4,13,2,14],[[0,100,1,2,101],[0,102,1,3,4],[101,5,0,4,100],[6,5,100,7],[0,8,100,6,4],[3,6],[9,103,10,5,104],[2,0,3,6],[3,2,4],[3,105,11],[4,0,106,3,6],[6,3,106],[4,103,6,0],[6,103,1],[0,4,107,3,5,12,1]]),
([w0,w1,w125,w2,w3,w64],[63,88,122,104,4,41,68,14,138,85,0,136,97,7],[0,2,19,6,3,1,12,5,8],[[100,0,1,2,101,102],[1,103,3,2,4,100],[1,104,3,2,5],[1,6,103,3,7,8],[7,0,100,2],[9,101,0,10,105],[5,106,11],[2,101,0,7,12],[7,101,1],[5,7],[2,5,7],[5,2],[2,5,107,7],[7,1,107,0],[7,108,5,13]]),
([w0,w126,w1,w2,w3,w64],[55,4,88,42,81,13,14,1,91,65,75,7],[3,6,0,13,5,12,14],[[0,1,100,2,101],[0,1,102,2,3],[2,1,100,4,101],[0,1,5,6],[4,1,100,0,6],[1],[0,103,7,8,104],[1,3],[3,6],[9,0,103,3],[1,3,6],[6,3,105],[0,1,4,6],[6,2,103,10],[1,6,11,106]]),
([w0,w1,w127,w2,w3,w64],[54,4,88,137,43,13,14,85,0,62,7],[0,19,6,3,12,2,13,8],[[0,1,100,2,101],[0,1,100,3,102],[2,1,103,3,4],[1,5,6],[0,1,100,6],[7,104,3,8,105],[4,0,104],[1,6],[3,9,104,6,2],[1],[1,4],[4,6],[1,4,6],[0,2,106,4,6],[1,6,10,107]]),
([w0,w128,w1,w2,w3,w64],[81,6,97,44,14,23,55,1,89,66,5],[0,6,3,13,5,14,15],[[0,1,100,2,101],[0,1,100,2,3],[2,1,102,0,100],[4,1,101],[0,1,5,4],[1],[6,103,7,8,104],[3,4],[1,3],[9,3,103],[4,0,105,2,3],[1,3,4],[4,2,104,0],[1,4],[0,1,4,10,106]]),
([w0,w1,w129,w2,w3,w64],[81,6,88,45,14,23,85,137,0,55,97,5],[0,19,3,6,12,2,8,11],[[0,1,100,2,101],[2,1,102,0,100],[2,1,102,0,3],[2,1,103,4],[0,1,5,4],[6,104,7,8,105],[3,9,104],[4,0,105,10],[1,2,4],[1],[3,4],[1,3],[4,3,106],[1,3,4],[0,1,4,11,107]])]
noncomputable def p14_D5 : List StD := [
([w37,w4,w0,w2,w3,w64],[46,9,10,81,70,4,6,8,49,90,89,55,91],[17],[[0,1],[0,1],[2,1],[3,4,5],[6,4],[1],[1,7,100],[3,8],[9,8,10],[1,3,9],[11,8,12],[3,8,10],[8,3],[8,11,9],[3,10,12]]),
([w4,w0,w1,w2,w130,w64],[139,83,140,55,3,19,89,49,141,51,70,6,91],[],[[0],[1],[2,3],[4,0,5],[6,0,7],[2,3],[2,8,9],[3,7,10],[6,3,7],[3,2],[9,2],[9,2],[3,4,6],[7,3,8],[11,6,12]]),
([w4,w0,w1,w2,w3,w131],[139,83,142,55,91,49,3,143,51,89,81],[],[[0],[1],[2,3],[4,0,5],[6,0,5],[2,3],[2,7,8],[3,5,4],[9,3,5],[3,2],[8,2],[8,2],[3,7,5],[5,3,6],[10,4]]),
([w29,w77,w0,w1,w3,w64],[0,9,144,145,55,81,89,49,48,146,60,67,91,51],[17],[[0],[1,2,3],[4,1],[4,5,6],[7,4,8],[9],[100],[5,10],[6,11],[4,3],[4,7,12],[5,4],[5,3],[13,3],[5,6,12]]),
([w103,w77,w1,w2,w3,w64],[0,81,9,91,51,89,147,148,104,110,49],[6],[[0],[1,2],[2,1],[3,4],[1,4,5],[6],[7],[1,8,100],[4,9,100],[4,3],[1,3],[4,5],[10,1],[10,3,8],[1,3]]),
([w37,w77,w0,w2,w3,w64],[0,81,9,51,91,49,149,86,90,89,150],[17],[[0],[1,2],[3,2],[1,4],[3,5],[6],[100],[1,7],[3,8],[2,1,3],[4,3],[1,3,9],[5,1],[5,4,10],[1,4]]),
([w77,w0,w1,w2,w130,w64],[104,4,49,14,141,140,81,51,91,89],[],[[0],[],[],[1],[2,3],[4,5,6],[5,4,7],[8,2],[6,2,9],[7,4,5],[6,2],[7,2],[2,4],[2,4],[6,8]]),
([w132,w77,w0,w1,w2,w64],[14,91,151,152,81,49,86,60,153,56,89,154,51],[6],[[0],[1,2,3],[4,1],[5,4],[4,1],[100],[6],[7],[5],[4,8],[1,4,9],[4,5,10],[9,1,11],[12,5],[5,1,11]]),
([w77,w0,w1,w2,w3,w131],[110,51,14,6,143,142,81,91,89,49],[],[[0],[],[],[1,2],[3],[4,5,6],[5,1,4],[7,1],[6,1,8],[1,4,5],[1,5],[1,5],[9,4],[9,4],[6,7]]),
([w133,w77,w0,w1,w2,w3],[14,89,155,156,51,49,157,158,56,90,67,159,160,48,91],[6],[[0],[1,2,3],[4,1],[5,6,7],[8,1],[100],[9],[10],[4],[11,12,13],[1,4],[14,4],[4,1],[4,5],[5,1,11]]),
([w29,w4,w8,w1,w3,w64],[144,10,6,4,89,91,161,146,60,49,3,81,75],[],[[0],[0,1],[2,0],[3,4],[2,5],[6,7],[8],[5,9],[4,9],[10,1,11],[5,12],[4,12],[11,5],[12,4],[11,4,5]]),
([w29,w4,w0,w16,w3,w64],[58,10,9,56,81,49,75,3,60,63,55,54,68,67],[],[[0],[0,1],[1,2],[3,4,5],[5,6],[1],[7,1],[4,5],[6,5],[4,8,9],[10,5,11],[4,5,9],[4,9,8],[5,12,13],[4,9,12]]),
([w29,w8,w0,w1,w3,w64],[0,10,9,144,145,8,3,4,75,49,60,91,89],[17],[[0,1,2],[2,3,4],[5,6],[7,8,9],[9,8],[6],[6,1,100],[9,8],[9,8],[6,4,10],[11,8],[12,8],[8,4],[8,4],[10,11,12]]),
([w26,w29,w0,w1,w3,w64],[60,56,54,62,63,10,162,35,49],[17],[[0,1],[2,0,3],[4,5,100],[6],[4,3],[7,0],[0,4],[0,2],[2,3,8],[2,0,4],[3,2],[2,0,4],[0,4],[3,8],[0,4]]),
([w72,w29,w0,w1,w3,w64],[91,6,55,60,81,68,10,163,49,164,67],[17],[[0,1],[2,3,4],[5,6,100],[0,4],[7],[0,1],[1,0],[2,4,8],[1,0],[2,9],[0,8],[4,2],[4,0],[10,5],[4,0]]),
([w4,w8,w0,w16,w3,w64],[9,46,6,90,56,49,91,48,89,54,55],[],[[0,1],[0],[0,2,3],[4,5,6],[7,5,8],[1],[0,2],[4,9],[5,10,7],[0,2,6],[6,5],[8,4],[4,8],[2,6],[4,6,7]]),
([w37,w4,w8,w2,w3,w64],[68,9,4,91,81,6,8,88,49,89,90,54,55,150],[],[[0,1],[1],[2,0],[2,3,4],[5,0],[1,4],[1,6,7],[0,8],[9,8],[10],[0,11,12],[4,12],[8,0],[7,3,13],[4,0]]),
([w4,w8,w16,w3,w64],[9,1,46,6,3,48,56,91,66,165,49,65,89,55,54,75,4,79,53,57],[8,9,11],[[0,1,2],[0,1,3,4,5],[6,7,8,9,10,11],[5,12,11,8,10],[0,5],[6,7,13,14,15],[5,10,14,13,15],[6,10,16,12,17,18],[3,10,7,17,19],[5,6,100,7,12,101,102]]),
([w4,w16,w102,w2,w3,w64],[48,90,10,58,55,65,56,49,75,46,79,54,110],[],[[0,1],[2],[0,3,4,5],[6,5],[0,7,8],[9],[3],[6,10,7],[0,10,7],[2,0,9],[4,0,11],[11,4],[4,8,7],[0,4],[0,12]]),
([w103,w4,w16,w2,w3,w64],[46,9,58,55,54,65,110,75,49,79,81],[],[[0,1],[2],[0,2],[3,4],[4,3],[5,6],[3,6,5],[7,5,8],[5,6],[0],[7,6],[7,9],[3,4],[4,3],[10,6]]),
([w134,w0,w1,w2,w3,w64],[0,6,54,58,55,11,75,1,19,49,89,166,53,62],[],[[0,1],[1,0],[2,3,4],[5,6,7,8],[1,9,10],[2,11,12],[10,11],[13,2],[2,9,10],[2,10],[11,9,12],[13,9],[9,2,11],[2,13,9],[11,10]]),
([w135,w0,w1,w2,w3,w64],[139,56,58,46,75,49,55,86,53,54,89],[],[[0],[1],[1,2,3],[1,0],[4,0,5],[6,7,8],[8,7],[6,4,9],[8,4],[6,10],[4,5],[4,5],[5,4],[5,4],[7,8]]),
([w4,w0,w61,w2,w3,w64],[35,86,56,55,30,49,75,53,54],[17],[[0],[1,2],[3,4,100],[1,5,6],[6,5],[3,1,7],[7,1],[3,5,8],[7,1],[1,0],[0,6],[6,5],[1,6,0],[5,3,6],[1,7]]),
([w136,w0,w1,w2,w3,w64],[0,4,55,58,54,49,14,21,167,68,91,81],[],[[0,1],[1,0],[2,3,4],[1,5,6],[7,5,6],[2,8,9],[10,8],[2,5,9],[11,2],[2,8,10],[11,5],[8,5,9],[2,9,5],[5,2,8],[8,9]]),
([w137,w0,w1,w2,w3,w64],[139,83,54,58,6,4,90,53,55,91,81,70],[],[[0],[1],[2,3,4],[5,0],[4,0],[2,6,7],[7,6],[8,2],[2,8],[2,9],[10,7,9],[6,11],[8,2],[2,8],[6,7,9]]),
([w4,w0,w122,w2,w3,w64],[37,70,83,55,32,81,49,90,53,91],[17],[[0],[1,2],[3,4,100],[5,1,6],[7,1],[1,7,8],[9,5,7],[3,1],[5,1],[3,0],[5,1,6],[0,1],[3,1],[6,1,7],[5,9]]),
([w138,w0,w1,w2,w3,w64],[139,98,55,1,11,19,121,53,70,81,91],[],[[0],[1],[2,3],[4,0,5],[1,0],[2,6,7],[7,6],[2,6,8],[7,2,9],[2,10],[6,7,10],[6,8],[2,7],[6,2],[6,7,10]]),
([w139,w0,w1,w2,w3,w64],[0,55,14,83,70,136,19,11,28,21,91,168,169],[],[[0,1,2],[3,4],[5,1],[6,2,7],[8,2,9],[1,5],[10,11],[1,4],[5,1],[1,5],[12,4],[11,4],[1,4],[5,1],[11,10]]),
([w4,w123,w1,w2,w3,w64],[55,0,6,137,14,91,81,4,70],[36,31],[[0,1],[2],[0,3,100],[3,4],[2,4],[0,1],[5,6,101],[0,2],[2,0],[0,5],[7,5,8],[2,8],[0,8],[2,0],[2,5]]),
([w4,w0,w124,w2,w3,w64],[40,121,98,91,137,14,70,53,125,55],[17],[[0],[1,2],[3,4,100],[1,5,4],[1,5],[6,1,7],[3,1],[3,1],[7,6,8],[9,3],[0,1],[0,6],[8,6],[1,3],[1,0,3]]),
([w8,w0,w1,w2,w130,w64],[170,53,99,9,4,75,140,85,65,91,68,6],[43],[[0],[1],[2],[3,0,4],[1,0,5],[1,6,7],[100,1,8],[9,4],[1,5],[7,6,10],[5,1,3],[5,6],[7,1,4],[7,5],[11,1,9]]),
([w8,w0,w1,w2,w3,w131],[170,53,99,91,75,142,85,65,68,4],[43],[[0],[1],[2],[3,0,4],[1,0,4],[1,5,6],[100,1,7],[3,4],[1,4],[6,3,8],[4,1,3],[4,5],[6,1,4],[6,3,4],[9,1]]),
([w37,w8,w0,w16,w3,w64],[0,1,9,4,56,91,75,49,8,86,65,89,90,88],[],[[0],[1,2],[3,1,2],[4,5,6],[6,7],[8],[2,8],[5,6],[7,6],[2,9,5],[5,6],[10,6,11],[6,11,9],[6,5,12],[13,5,11]]),
([w22,w37,w0,w2,w3,w64],[86,56,65,88,53,8,9,75],[17],[[0,1],[2,0,3],[4,5,100],[6],[4,3],[4,0],[0,6],[0,2],[2,3,7],[2,0,4],[3,2],[2,0,4],[0,4],[3,7],[0,4]]),
([w70,w37,w0,w2,w3,w64],[90,48,55,97,8,86,75,9,14,171,91],[17],[[0,1],[2,0,3],[2,4,100],[5,3,6],[7],[2,0,3],[0,7],[6,3],[0,8],[3,0,9],[2,0,10],[3,2],[2,6,3],[0,2],[0,10]]),
([w8,w16,w1,w102,w3,w64],[172,173,56,55,8,75,49,86,174,79,88,65,66,110,48],[],[[0,1],[2,0,3],[4],[2,5,6],[6,3,5],[7],[8],[2,9,5],[5,9],[4,0],[2,0,5],[5,0],[10,5,11],[11,2,12],[2,13,14]]),
([w103,w8,w16,w1,w3,w64],[0,46,9,144,1,88,75,65,79,175,148,55,77,91,89],[],[[0,1,2],[3],[4,2],[5,6,7],[7,6,8],[9,10],[7,1,11],[8,6],[5,6],[12],[6,8],[5,8],[6,7,8],[6,5],[5,13,14]]),
([w140,w0,w1,w2,w3,w64],[1,19,15,65,4,89,75,53,166,88,63],[],[[0,1,2],[3,1,4],[4,0],[4,1],[5,6],[7,8],[3,8,5],[9,3],[3,6,5],[3,5,10],[6,3,8],[3,5,6],[8,5],[9,6],[8,5]]),
([w141,w0,w1,w2,w3,w64],[170,65,0,4,56,88,75,53,60,89,63],[],[[0],[1,2,3],[4],[3,0],[5,0,6],[7,5,8],[1,8,7],[5,1],[1,6,7],[1,9,10],[6,1,8],[1,5,6],[8,6,7],[5,6],[5,7]]),
([w8,w0,w1,w57,w3,w64],[176,65,60,56,75,14,89,63,88],[17],[[0],[1,0,100],[2,3],[2,4,5],[6,4],[7,2],[1,2,6],[8,1],[1,2,6],[1,6,2],[2,1],[1,6,4],[2,4,6],[8,4],[2,6]]),
([w142,w0,w1,w2,w3,w64],[76,170,6,0,4,68,167,91,97,66],[],[[0,1],[2,3],[0,2],[4,0],[2,0],[5,6],[0,6,7],[5,0,6],[8,0],[9,5],[9,0],[6,0],[8,0,5],[6,0],[6,5]]),
([w143,w0,w1,w2,w3,w64],[170,65,0,6,48,4,63,67,89,91,76,66,97,75],[],[[0],[1,2,3],[4],[5,0],[3,0],[6,7],[1,7,8],[9,1,7],[1,10],[1,6],[11,1],[1,8,10],[12,8,13],[7,6,9],[7,6,9]]),
([w8,w0,w1,w117,w3,w64],[177,66,67,48,97,14,75,68,91],[17],[[0],[1,0,100],[2,3],[4,5,6],[2,5],[7,2],[1,2,8],[1,2,7],[4,1],[1,7],[1,4,6],[2,1],[4,6],[2,6,8],[2,7]]),
([w144,w0,w1,w2,w3,w64],[170,66,0,100,138,178,68,91,97,76],[],[[0],[1,2],[3],[4,5],[3,0],[6,4],[1,4,7],[1,4,6],[8,1],[1,6],[1,7,9],[4,1],[4,6,8],[4,7],[4,6]]),
([w145,w0,w1,w2,w3,w64],[170,76,137,0,66,99,178,138,68,179],[],[[0,1],[2,3,4],[5,1],[6,7],[6,0],[8,6],[1,2,4],[2,1],[2,1],[4,2],[2,1],[2,1],[9,1],[6,1],[6,8]]),
([w8,w123,w1,w2,w3,w64],[66,14,170,136,6,68,9,1,76,4],[19,22],[[0,1,2],[0,3,100],[4],[3,1],[3,1],[5,6,101],[0,7],[0,4],[4,0],[0,5],[0,8],[4,0],[9,5,8],[4,8],[4,5]]),
([w8,w0,w1,w125,w3,w64],[170,68,136,122,76,91,138,97,66],[17],[[0],[1,2,100],[2,0],[1,0,2],[2,0],[1,3],[4,3,5],[1,4,6],[7,3,4],[8,1],[3,4],[6,1],[3,1,4],[3,6],[3,1,6]]),
([w146,w0,w1,w2,w3,w64],[66,58,14,86,60,6,55,56,97,81,75,65,88],[9],[[0,1,2],[3],[4],[3,2],[5,2],[6,7,8],[0,7,9],[0,10,11],[8,0],[0,6],[0,8,9],[10,0,11],[6,9,8],[12,6,10],[7,100]]),
([w0,w147,w1,w2,w3,w64],[97,0,170,81,180,75,65,66,4,56,6,88,91],[17],[[0,1,2],[3,0],[0,3],[4,5,6],[0,5,7],[6,1,8],[9],[0,1,3],[10,2],[6,4,100],[3,0],[5,4],[0,3],[11,5],[0,12]]),
([w18,w45,w0,w2,w3,w64],[86,56,81,88,11,83,98,55,68,90,75,54],[17],[[0,1],[2,0,3],[4],[0,5],[6,3,5],[2,0,3],[7,8,100],[0,4],[9,3,8],[3,0,2],[3,10,8],[2,0,7],[0,2,11],[3,7,10],[0,8,2]]),
([w26,w45,w0,w1,w2,w64],[35,11,75,83,91,181,98,4,54,1,97,103,88,81],[],[[0,1,2],[3,2,4],[2,1],[5],[6,4],[3,0],[7],[8,9,10],[2,3,10],[8,7,11],[12,7,13],[8,2,3],[8,11],[2,3,11],[8,2,3]]),
([w148,w0,w1,w2,w3,w64],[70,10,58,139,56,6,81,86,88,75,54,55,68,97],[17],[[0,1,2,3],[4],[4,1],[4,0],[5,0],[6,7,8],[8,6],[8,9,10],[6,7,11],[10,12,100],[6,13],[9,8],[7,6,10],[8,9],[6,12]]),
([w19,w47,w0,w1,w3,w64],[0,4,56,88,62,166,99,66,60,80,35,65,91,97],[17],[[0,1,2],[3,1,4],[5],[1,6],[3,4],[3,4],[7,0,100],[8,9,10],[3,4],[4,3],[3,11],[11,7],[7,11],[4,3],[3,12,13]]),
([w22,w47,w0,w1,w2,w64],[35,68,97,88,4,14,75,98,62,99,65,102],[],[[0,1,2],[1,3,4],[4],[2,1],[2,1],[2,4,5],[6,0],[4],[3,5,7],[8,2],[2,4,8],[2,4,9],[10,11],[6,3],[3,6]]),
([w0,w16,w1,w2,w3,w86],[88,6,110,62,78,79,28,115,120,4,55,66,44],[],[[0,1,2],[3,0],[0,2],[0,4],[5,2,6],[7],[8],[9,2,4],[0,4,5],[10,11],[11,2,4],[3,0],[10,2,4],[0,3],[0,2,12]]),
([w0,w1,w2,w17,w3,w86],[62,166,88,182,79,68,91,120,115,44],[],[[0,1,2],[2,0],[0,1],[0,3],[4,1],[5,6],[7],[1,3],[0,2],[8],[1,3],[2,0],[1,3],[0,3],[0,5,9]]),
([w18,w0,w1,w2,w3,w86],[62,4,88,56,166,14,115,79,28,55,68,86,44],[17],[[0,1,2],[3],[4],[1,5],[0,2],[0,2],[2,0],[0,6],[7,6,8],[9,10,100],[11,6],[0,2],[9,6],[2,0],[0,10,12]]),
([w19,w0,w1,w2,w3,w86],[88,4,62,166,56,14,120,79,28,66,91,60,44],[17],[[0,1,2],[3],[4],[1,5],[0,2],[2,0],[0,2],[0,6],[7,6,8],[9,10,100],[9,6],[2,0],[11,6],[0,2],[0,10,12]]),
([w87,w0,w16,w1,w2,w3],[79,24,28,62,88,40,44,4,48,86,60,14,55,66,65,97],[6],[[0,1,2],[3,0],[3,0],[4,0],[3,5,6],[3,7,100],[3,4],[4,3],[0,8],[9],[10],[7,0,11],[12,13],[13,0,14],[12,0,15]]),
([w87,w0,w1,w2,w17,w3],[182,28,79,62,88,6,40,44,167,68,91,67,166,81,86,97,14],[],[[0,1,2],[3,1],[4,2],[5,1],[3,6,7],[3,4],[4,3],[3,5],[2,8],[9,10],[11],[12,2,13],[14],[12,2,15],[12,2,16]]),
([w18,w87,w0,w1,w2,w3],[62,88,56,166,14,115,28,79,40,44,90,55,68,86,81,97],[17],[[0,1],[0,1],[2],[3],[2,4],[5,6,7],[0,1],[1,0],[0,8,9],[0,1],[1,0],[0,10,7],[11,12,100],[13,7,14],[11,7,15]]),
([w19,w87,w0,w1,w2,w3],[0,62,97,166,56,14,24,79,67,88,40,66,91,81],[17],[[0,1],[2,1],[3],[4],[2,5,3],[2,6,7],[1,0],[8,1,9],[1,10,2],[1,2],[2,1],[1,8,7],[11,12,100],[11,2,13],[2,7]]),
([w0,w1,w149,w2,w3,w64],[62,56,88,14,104,79,86,55,66,135],[],[[0,1,2],[0,1,3],[2,0],[0,4],[5,1],[1,6],[1,7,8],[1,5,9],[0,2],[1,9],[1,3],[0,3,4],[1,5,9],[2,0],[0,4]]),
([w12,w0,w1,w57,w2,w64],[183,60,81,97,14,62,181,180,88,79,66,184],[],[[0],[1,0,2],[1,2,3],[1,2,3],[1,4,2],[5,1,6],[7,1,5],[8,1,5],[9,1],[1,6],[10,6,11],[5,4,6],[4],[8,4,5],[8,4,5]]),
([w12,w0,w61,w1,w2,w64],[185,11,81,86,97,14,79,62,186,88,55],[],[[0],[1,0,2],[2,0],[3,2,4],[2,5],[6,3],[7,3,8],[9,3,7],[6,3],[5],[3,1],[7,5,9],[10,8],[7,5,6],[9,5,6]]),
([w0,w150,w1,w2,w3,w64],[9,4,46,55,56,88,62,187,78,97,86,60,6,104],[],[[0,1,2],[3,4,5],[5,4,6],[3,7,8],[9,3],[10],[11],[1,8],[5,8,12],[3,7],[4,7,8],[6,5],[3,8],[5,3,6],[4,13]]),
([w151,w0,w1,w2,w3,w64],[46,4,9,86,56,14,6,54,104,65,79,48,78],[],[[0,1,2],[3,4],[0,1],[1,5],[6,5],[7,4,8],[9,4,8],[10,7,11],[7,4,10],[4,7,9],[4,9],[9,8,12],[4,7],[7,8,12],[4,8]]),
([w0,w16,w48,w2,w3,w64],[62,4,104,65,56,78,115,15,1,48],[],[[0,1,2],[0,2],[3,0],[0,2],[3,4,5],[3,1,6],[7],[1,5],[0,2],[3,8],[4,3],[0,2],[4,5],[9,0,5],[0,2]]),
([w0,w16,w1,w50,w3,w64],[65,6,104,54,88,78,115,0,4,56],[],[[0,1,2],[3,2],[0,2],[4,0],[0,5],[6],[3,1,7],[8,5],[1,2,4],[0,7,3],[9,0],[0,2,5],[9,3],[3,2,4],[4,2]]),
([w0,w16,w1,w2,w3,w88],[65,4,104,54,56,26,86,60,14,6,78],[6],[[0,1,2],[3,2],[0,2],[100,0],[0,4,5],[6],[7],[1,8],[9,2,8],[3,0],[4,0],[0,2,10],[4,3],[3,2,10],[4,2]]),
([w89,w0,w16,w1,w2,w3],[26,56,21,14,6,78,48,104,54,65,55,115,120],[],[[0,1,2],[3,4],[5,0,6],[5,6],[1,6,7],[8,1,7],[8,1,7],[9,1,7],[10,5],[11],[12],[1,3],[8,9],[1,5],[1,5]]),
([w152,w0,w1,w2,w3,w64],[0,6,78,62,67,104,65,120,89,60],[17],[[0,1],[1,0],[2],[0,2],[1,2],[3,4,5],[6,3],[3,4,5],[6,7],[6,8,100],[9,6],[3,5],[9,7],[4,3,7],[3,5]]),
([w18,w0,w48,w2,w3,w64],[104,6,90,48,15,4,14,62,54,115,1,86],[3,17],[[0,1,100],[2,3],[4],[5,6],[0,6,1],[4,2],[100,0],[7,0],[8,9],[8,10,101],[4,9],[2,0,7],[11,8],[2,0,9],[2,0,7]]),
([w0,w150,w48,w2,w3,w64],[54,6,104,65,62,78,90,67,4,56],[],[[0,1,2],[0,2],[3,2],[4,0],[0,5],[6],[7],[8,5],[1,2,4],[0,3],[9,3],[3,2,4],[9,0],[0,2,5],[4,2]]),
([w0,w48,w2,w153,w3,w64],[62,166,104,89,15,1,60,182,86,167],[],[[0,1,2],[3,0,1],[4,0,1],[0,2],[3,1],[5,3],[6],[1,7],[0,2],[8],[1,3],[9,0,7],[1,7],[9,0,7],[0,2]]),
([w154,w0,w48,w2,w3,w64],[104,4,56,166,14,6,62,54,86,115,1],[3,17],[[0,1,100],[2],[3],[1,4],[0,4,5],[6,0],[100,0],[6,0],[7,8,9],[7,10,101],[8,9],[6,0],[8,7],[7,0,9],[6,0]]),
([w152,w0,w48,w2,w3,w64],[15,4,166,56,14,6,62,60,104,89,65,67,120],[17],[[0,1],[2],[3],[0,4],[5,4],[6,7,8],[9,6,7],[6,8],[9,7],[10,9,100],[7,10],[6,8],[7,9],[11,6,12],[6,8]]),
([w155,w0,w1,w2,w3,w64],[46,4,9,56,14,62,6,90,104,88,54,115,63,86],[17],[[0,1,2],[3],[1,0],[1,4],[5,4,6],[5,7,8],[9,5],[5,7,8],[10,11],[10,12,100],[13,11],[5,8],[13,10],[7,5,9],[5,8]]),
([w19,w0,w1,w50,w3,w64],[104,4,166,0,56,14,6,9,62,88,65,120,60],[0,17],[[0,1,100],[2],[3,1,4],[1,5],[0,5,6],[100,0],[7,0,8],[9,0],[10,11],[10,3,101],[12,10],[10,0,11],[12,11],[9,0],[9,0]]),
([w0,w150,w1,w50,w3,w64],[88,4,104,54,56,78,86,0,65],[],[[0,1,2],[3,0],[0,2],[0,2],[3,4,5],[6],[7],[1,5],[0,2],[3,8],[4,5],[8,0,5],[4,3],[0,2],[0,2]]),
([w0,w1,w50,w156,w3,w64],[63,166,9,46,16,88,187],[],[[0,1],[2,1,3],[4,1],[5,6],[0,1],[6],[6],[1,0],[6],[6],[1,6],[5,0],[1,6],[6],[1,0]]),
([w155,w0,w1,w50,w3,w64],[16,4,56,0,14,63,88,86,62,187,115,54,90],[],[[0,1],[2],[3],[0,4],[5,4,6],[5,6,7],[6,7,8],[6,9,10],[5,7],[11,5,9],[7,5],[12,6,10],[7,10],[6,5],[6,5]]),
([w157,w0,w1,w50,w3,w64],[88,4,182,78,6,60,46,187],[0],[[0,1,100],[2],[3],[1,2],[0,2,4],[100,0],[0,5,6],[0,7],[7],[7],[5,7],[7],[5,7],[0,7],[0,7]]),
([w0,w1,w2,w17,w3,w88],[63,166,89,104,136,120,167,182,115],[],[[0,1],[2,1],[1,3],[4,3],[0,1],[0,2],[5],[1,0],[6,2,7],[8],[1,2],[4,0,7],[1,5],[6,0,5],[1,0]]),
([w18,w0,w1,w2,w3,w88],[104,6,97,48,167,4,14,63,90,137,115,54,86],[17],[[0,1,2],[3],[4],[5,2,6],[0,6,1],[7,0,8],[2,0],[9,0],[2,10],[11,7,100],[9,2,7],[8,0,10],[2,10,12],[8,0,10],[2,0,12]]),
([w19,w0,w1,w2,w3,w88],[104,6,81,167,48,4,14,89,67,136,120,65,60],[17],[[0,1,2],[3],[4],[5,2,6],[0,6,1],[2,0],[7,0,8],[9,0],[2,10],[11,7,100],[2,10,12],[8,0,10],[9,2,7],[8,0,10],[2,0,12]]),
([w89,w0,w1,w2,w17,w3],[26,166,21,182,167,89,63,104,91,120,115],[],[[0,1,2],[3,0,4],[3,4],[3,0,4],[1,4,5],[6,1],[5,1],[1,7],[8,3,4],[6,5],[9],[1,3],[10],[1,3],[1,3]]),
([w89,w18,w0,w1,w2,w3],[14,6,26,86,21,115,90,104,78,182,63,55],[3,17],[[0,1],[2,3,4],[5,2,6],[5,6],[3,6,7],[7,1,100],[8],[9],[3,0],[10,3],[100,3,7],[11,5],[11,10,101],[3,5],[3,5]]),
([w89,w19,w0,w1,w2,w3],[0,6,14,26,60,21,120,67,104,167,48,89,91,65],[0,17],[[0,1,2],[3,4,5],[6,0,7],[6,7],[4,7,8],[8,1,100],[9],[10],[4,2],[100,4,8],[11,4],[12,6,7],[13,11,101],[4,6],[4,6]]),
([w158,w0,w1,w2,w3,w64],[9,6,46,90,67,91,80,35,4,14,63,48,89,55,65,56,62],[],[[0,1,2],[3],[4],[5,6,7,8],[1,9],[10,11],[12,11],[13,11,14],[10,13,14],[11,10,12],[15,10],[11,12,16],[13,12],[11,10,13],[11,10,15]]),
([w159,w0,w1,w2,w3,w64],[0,6,48,4,62,14,67,63,65,60,88,81,97],[],[[0,1],[1,0],[2],[3,0],[1,4,5],[4,6,7],[8,4],[4,6,8],[7,9],[8,7],[9,7],[4,10],[9,11,12],[6,4,10],[4,7]]),
([w90,w0,w16,w2,w3,w64],[0,19,15,48,90,1,65,11,78,62,63,88,54,56,70],[],[[0,1,2],[3,4],[3,5,6],[7,1],[3,8],[9,3,10],[11,3,9],[9,3,12],[10,13],[1],[13,10],[3,14],[13,12],[3,9,11],[3,10,9]]),
([w160,w0,w1,w2,w3,w64],[46,6,9,48,4,35,80,14,62,90,88,54,86,89,97,81],[],[[0,1,2],[3],[1,0],[4,5,6],[1,7],[8,9,10],[10,8],[8,9,11],[11,12,13],[11,13],[12,14,15],[8,10],[12,11],[9,8,10],[8,13]]),
([w91,w0,w16,w1,w3,w64],[9,48,46,54,56,62,88,89,65,90,76],[],[[0,1,2],[1,0],[1,0,3],[4,3],[1,5,6],[5,1,7],[5,1,6],[5,1,8],[7,4],[9],[4,7],[1,10],[4,8],[1,6,5],[1,7,4]]),
([w0,w1,w161,w2,w3,w64],[62,48,88,46,104,89,56,90,63,80,35],[],[[0,1,2],[0,1,3],[2,0],[0,1,4],[5,6],[1,7],[1,5,8],[6,8],[0,2],[1,3],[6,9,10],[0,4],[6,5],[1,0,2],[0,4]]),
([w162,w0,w1,w2,w3,w64],[88,58,14,90,67,4,62,48,65,55,81,97],[9],[[0,1,2],[3],[4],[5,2],[0,2,3],[6,0],[0,6],[0,7,8],[8,9],[7,9,8],[10,8,11],[6,0],[9,10,11],[0,6],[0,100]]),
([w0,w163,w1,w2,w3,w64],[65,0,62,67,88,66,48,4,81,97,89],[17],[[0,1,2],[2,3,4],[0,2],[2,0],[0,5],[0,1,3],[6],[7,8,9],[3,1],[0,10,100],[5,0],[0,4,2],[9,8],[3,2,4],[2,10]]),
([w18,w92,w0,w2,w3,w64],[90,48,81,97,21,83,55,63,54,62],[17],[[0,1],[2,0,3],[4],[2,3],[0,5],[2,0,3],[6,7,100],[2,3],[0,4],[3,0,2],[6,0,8],[2,6],[3,2],[0,6],[0,7,9]]),
([w72,w92,w0,w1,w2,w3],[37,21,62,97,6,81,55,1,88,83,109],[],[[0,1,2],[3,4,5],[2,1],[4],[2,5,3],[2,0,3],[4],[6,7,8],[5,3],[2,3],[3,2],[2,4,9],[6,10],[5,3],[3,5]]),
([w164,w0,w1,w2,w3,w64],[81,10,97,48,37,82,55,90,54,63,88,62],[17],[[0,1,2],[3],[3,1],[0,2],[3,4,5],[0,2],[2,0],[6,7,8],[0,6],[6,9,100],[0,2],[7,10,11],[2,0],[7,6],[0,9,10]]),
([w19,w93,w0,w1,w3,w64],[0,6,48,97,81,167,99,65,67,82,37,88,66,89],[17],[[0,1,2],[3,1,4],[5],[3,4],[1,6],[3,4],[7,0,100],[3,4],[8,9,10],[4,3],[11,7],[3,12],[4,3],[7,11,12],[3,13,11]]),
([w70,w93,w0,w1,w2,w3],[37,63,88,6,81,66,62,97,99,108],[],[[0,1,2],[1,3],[3],[2,1],[2,1],[2,3,4],[5,0,6],[3],[6,4,7],[4,2],[2,3,4],[2,3,8],[5,9],[4,7],[7,4]]),
([w0,w16,w1,w2,w94,w64],[81,6,104,97,79,19,78,115,120,54,65,42],[],[[0,1,2],[0,2],[3,0],[4,2,5],[0,6],[7],[8],[0,4],[1,2,6],[9,10],[0,3],[10,2,6],[3,0],[9,2,6],[0,2,11]]),
([w0,w1,w2,w17,w94,w64],[81,97,6,79,15,19,182,63,89,120,167,90,42],[],[[0,1],[1,0],[0,2],[3,4,5],[0,6],[7,8],[9],[0,1],[10,3,6],[11],[1,0],[10,3,6],[0,6],[2,3,6],[0,7,12]]),
([w18,w0,w1,w2,w94,w64],[81,6,97,48,167,14,79,15,19,115,54,63,90,42],[17],[[0,1,2],[3],[4],[0,2],[1,5],[0,2],[2,0],[6,7,8],[0,9],[10,11,100],[0,2],[12,6,9],[2,0],[10,6,9],[0,11,13]]),
([w19,w0,w1,w2,w94,w64],[97,6,81,167,48,14,79,15,19,120,65,89,67,42],[17],[[0,1,2],[3],[4],[0,2],[1,5],[2,0],[0,2],[6,7,8],[0,9],[10,11,100],[2,0],[10,6,9],[0,2],[12,6,9],[0,11,13]]),
([w95,w0,w16,w1,w2,w64],[78,19,79,97,81,40,42,6,66,90,67,14,54,48,88],[6],[[0,1,2],[3,2],[4,1],[3,2],[3,5,6],[3,7,100],[4,3],[3,4],[2,8,3],[9],[10],[7,2,11],[12,8],[13,2,8],[12,2,14]]),
([w95,w0,w1,w2,w17,w64],[79,15,19,81,97,4,40,42,166,63,89,67,167,62,90,88,14],[],[[0,1,2],[3,0],[4,0],[5,0],[3,6,7],[3,4],[4,3],[3,5],[0,8],[9,10],[11],[12,0,13],[14],[12,0,15],[11,0,16]]),
([w18,w95,w0,w1,w2,w64],[79,97,81,48,167,14,15,19,40,42,86,54,63,90,62,88],[17],[[0,1],[2,1],[3],[4],[0,5,3],[0,6,7],[2,0],[1,0],[1,8,9],[2,1],[1,2],[0,10],[11,12,100],[13,0,14],[11,0,15]]),
([w19,w95,w0,w1,w2,w64],[0,81,97,167,48,14,120,19,79,40,42,60,66,89,67,88],[17],[[0,1],[2,1],[3],[4],[3,5],[6,7,8],[1,0],[2,1],[1,9,10],[1,2],[2,1],[1,11,8],[12,13,100],[14,8,12],[14,8,15]]),
([w0,w1,w165,w2,w3,w64],[81,48,97,14,79,110,90,54,65,188],[],[[0,1,2],[0,1,3],[2,0],[4,1],[0,5],[1,6],[1,7,8],[0,2],[1,4,9],[1,9],[0,3,4],[1,3],[2,0],[1,4,9],[0,5]]),
([w65,w0,w1,w117,w2,w3],[189,67,62,88,14,81,190,191,97,79,65,192],[],[[0],[1,0,2],[1,2,3],[1,2,3],[1,4,2],[5,1,6],[7,1,5],[8,1,5],[9,1],[1,6],[10,6,11],[5,4,6],[4],[8,4,5],[8,4,5]]),
([w65,w0,w122,w1,w2,w3],[193,21,62,90,88,14,79,81,194,97,54],[],[[0],[1,0,2],[2,0],[3,2,4],[2,5],[6,3],[7,3,8],[9,3,7],[6,3],[5],[3,1],[7,5,9],[10,8],[7,5,6],[9,5,6]]),
([w0,w166,w1,w2,w3,w64],[9,6,46,54,48,97,81,88,195,78,90,67,4,110],[],[[0,1,2],[3,4,5],[5,4,6],[7,3],[3,8,9],[10],[11],[5,9,12],[1,9],[3,8],[6,5],[4,7,9],[5,3,6],[3,9],[4,13]]),
([w167,w0,w1,w2,w3,w64],[46,6,9,90,48,4,14,55,110,66,78,79,56],[],[[0,1,2],[3,4],[0,1],[5,6],[1,6],[7,4,8],[9,4,8],[7,4,10],[11,7,12],[4,7,9],[9,8,10],[4,9],[7,8,10],[4,7],[4,8]]),
([w0,w16,w96,w2,w3,w64],[66,6,110,0,28,48,78,81,90,24,1,56],[],[[0,1,2],[3,2,4],[0,2],[0,5,6],[7,0],[0,1,8],[9],[7,2],[1,6],[0,10],[0,2,6],[3,0],[11,2,6],[5,6],[5,2]]),
([w0,w16,w1,w97,w3,w64],[66,6,110,55,48,78,97,90,0],[],[[0,1,2],[3,2],[0,2],[0,4,5],[6,0],[7],[3,1,8],[6,2],[1,5],[0,8,3],[0,2,5],[4,0],[3,2,5],[4,3],[4,2]]),
([w0,w16,w1,w2,w98,w64],[66,6,110,55,48,17,90,67,4,14,78],[6],[[0,1,2],[3,2],[0,2],[0,4,5],[100,0],[6],[7],[8,2,9],[1,9],[3,0],[0,2,10],[4,0],[3,2,10],[4,3],[4,2]]),
([w99,w0,w16,w1,w2,w64],[17,48,11,14,110,4,78,56,55,66,54,86,60],[],[[0,1,2],[3,4,5],[6,0,7],[6,4,7],[1,4],[8,1,4],[8,1,4],[9,1,4],[10,4],[11],[12],[1,3],[8,9],[1,6],[1,6]]),
([w168,w0,w1,w2,w3,w64],[0,4,56,14,81,60,110,66,120,91,67],[17],[[0,1],[1,0],[2],[1,3],[0,3],[4,5,6],[7,4],[7,8],[4,5,6],[7,9,100],[4,6],[10,7],[5,4,8],[10,8],[4,6]]),
([w18,w0,w96,w2,w3,w64],[110,4,86,56,24,14,6,55,115,81,1,90],[10,17],[[0,1,100],[2,3],[4],[0,5,1],[6,5],[4,2],[100,0],[7,8],[9,0],[7,10,101],[2,0,8],[4,8],[2,0,8],[11,7],[2,0,9]]),
([w0,w166,w96,w2,w3,w64],[81,6,110,66,48,78,90,67,55],[],[[0,1,2],[0,2],[3,0],[3,4,5],[0,2],[6],[7],[0,2],[1,5],[8,3],[0,2],[4,3],[8,0,5],[4,5],[0,2]]),
([w0,w96,w2,w169,w3,w64],[81,167,110,91,24,1,67,182,90,166],[],[[0,1,2],[3,0,1],[4,0,1],[3,1],[0,2],[5,3],[6],[0,2],[1,7],[8],[9,0,7],[1,3],[9,0,7],[1,7],[0,2]]),
([w170,w0,w96,w2,w3,w64],[110,6,48,167,14,4,81,55,115,1,32,119,90],[10,17],[[0,1,100],[2],[3],[0,4,5],[1,4],[6,0],[100,0],[7,8],[6,0],[7,9,101],[6,0],[10,8,11],[7,0,8],[12,7],[6,0]]),
([w168,w0,w96,w2,w3,w64],[24,6,167,48,4,14,81,67,110,91,66,60,120],[17],[[0,1],[2],[3],[4,5],[0,5],[6,7,8],[9,6,7],[9,7],[6,8],[10,9,100],[6,8],[7,10],[11,6,12],[7,9],[6,8]]),
([w171,w0,w1,w2,w3,w64],[46,6,9,48,81,14,4,86,110,97,55,115,68,90],[17],[[0,1,2],[3],[1,0],[4,5,6],[1,5],[4,7,8],[9,4],[10,11],[4,7,8],[10,12,100],[4,8],[13,11],[7,4,9],[13,10],[4,8]]),
([w19,w0,w1,w97,w3,w64],[110,6,167,0,48,14,4,9,60,66,120,97,67],[16,17],[[0,1,100],[2],[3,1,4],[0,5,6],[1,5],[100,0],[7,0,8],[9,10],[11,0],[9,3,101],[8,0,10],[12,9],[8,0,10],[12,10],[8,0,11]]),
([w0,w166,w1,w97,w3,w64],[97,6,110,55,48,78,90,0,66],[],[[0,1,2],[3,0],[0,2],[3,4,5],[0,2],[6],[7],[0,2],[1,5],[3,8],[8,0,5],[4,5],[0,2],[4,3],[0,2]]),
([w0,w1,w97,w172,w3,w64],[68,167,9,46,25,97,195],[],[[0,1],[2,1,3],[4,1],[0,1],[5,6],[6],[6],[6],[1,0],[6],[5,0],[1,6],[6],[1,6],[1,0]]),
([w171,w0,w1,w97,w3,w64],[55,6,97,48,0,68,14,90,110,86,115],[17],[[0,1,2],[3],[4],[5,2],[1,6],[0,2],[2,7,8],[0,7,5],[2,0],[0,5,100],[9,2,10],[7,5],[0,5,2],[7,0],[2,5]]),
([w173,w0,w1,w97,w3,w64],[97,6,167,48,14,4,60,46,66,120,67,110],[16,17],[[0,1,100],[2],[3],[0,4,5],[1,4],[100,0],[0,6,7],[8,9],[0,6,8],[8,7,101],[6,0,9],[10,8],[0,9,6],[10,9],[0,11]]),
([w0,w1,w2,w17,w98,w64],[68,167,91,110,136,120,166,182,115],[],[[0,1],[2,1],[1,3],[0,1],[4,3],[0,2],[5],[6,2,7],[1,0],[8],[4,0,7],[1,2],[6,0,5],[1,5],[1,0]]),
([w18,w0,w1,w2,w98,w64],[110,4,88,56,166,14,6,68,86,90,137,55,115],[17],[[0,1,2],[3],[4],[0,5,1],[6,2,5],[7,0,8],[2,0],[2,9,7],[10,0],[11,7,100],[8,0,12],[9,2,7],[8,0,12],[2,11,9],[2,0,9]]),
([w19,w0,w1,w2,w98,w64],[110,6,62,167,48,14,4,91,67,136,66,120],[17],[[0,1,2],[3],[4],[0,5,6],[1,2,5],[2,0],[7,0,8],[2,8,7],[9,0],[10,7,100],[10,0,11],[2,10,8],[9,0,11],[8,2,7],[2,0,8]]),
([w99,w0,w1,w2,w17,w64],[17,167,11,182,166,91,68,110,89,60,86],[],[[0,1,2],[3,0,4],[3,4],[3,0,4],[1,4,5],[6,1],[5,1],[1,7],[8,3,4],[6,5],[9],[1,3],[10],[1,3],[1,3]]),
([w99,w18,w0,w1,w2,w64],[110,4,14,17,90,11,115,86,56,166,68,54],[23,17],[[0,1,2],[3,4,5],[6,0,7],[6,0,7],[4,0],[0,1,100],[8],[9],[4,2],[10,0,4],[100,0],[11,0],[11,10,101],[4,6],[4,6]]),
([w99,w19,w0,w1,w2,w64],[0,4,14,17,67,11,120,60,110,182,78,91,89,66],[30,17],[[0,1,2],[3,4,5],[6,0,7],[6,7],[4,7,8],[8,1,100],[9],[10],[4,2],[100,4,8],[11,4],[12,6,7],[13,11,101],[4,6],[4,6]]),
([w174,w0,w1,w2,w3,w64],[9,14,46,86,60,89,6,68,56,91,48,54,66,81],[],[[0,1,2],[3],[4],[3,1],[5,1,6],[7,8],[9,8],[7,10],[11,8,12],[8,7,9],[8,9,13],[10,7],[8,7,11],[10,9],[8,7,10]]),
([w175,w0,w1,w2,w3,w64],[0,110,6,48,4,68,14,60,66,81,67,97,62,88],[],[[0,1,2],[2,0],[3],[4,5,6],[2,0],[5,7],[8,7,9],[5,10],[9,7,8],[8,5],[7,11,9],[10,5],[7,5,11],[10,12,13],[7,5,9]]),
([w100,w0,w16,w2,w3,w64],[0,28,24,56,86,1,66,97,81,21,68,48,55,70],[],[[0,1,2],[3,4],[3,5,6],[3,7,8],[9,1],[7,3,10],[7,3,8],[10,11],[7,3,12],[1],[3,13],[11,10],[3,8,7],[11,12],[3,10,7]]),
([w176,w0,w1,w2,w3,w64],[46,4,9,56,14,6,81,86,97,55,90,54,91,88,62],[],[[0,1,2],[3],[1,0],[1,4],[5,4],[6,7,8],[8,6],[9,10,11],[6,7,9],[9,12],[6,8],[10,13,14],[7,6,8],[10,9],[6,12]]),
([w101,w0,w16,w1,w3,w64],[9,56,46,55,81,97,48,91,66,86,76],[],[[0,1,2],[1,0],[1,0,3],[1,4,5],[6,3],[4,1,7],[4,1,5],[7,6],[4,1,8],[9],[1,10],[6,7],[1,5,4],[6,8],[1,7,4]]),
([w0,w1,w177,w2,w3,w64],[81,56,97,46,91,48,110,86,54,68,82,37],[],[[0,1,2],[0,1,3],[2,0],[4,5],[0,1,6],[1,7],[1,4,8],[0,2],[5,9],[1,3],[0,4],[5,10,11],[1,0,2],[5,4],[0,4]]),
([w0,w16,w1,w2,w130,w64],[140,104,97,81,110,19,78,115,88,54,62],[],[[0,1,2],[3,0],[0,1,2],[4,1,5],[2,6],[7],[0],[2,4],[8,1],[0,9],[3,0],[10,0],[2,3],[8,1],[2,1,4]]),
([w132,w0,w16,w1,w2,w64],[110,15,19,4,81,56,97,66,86,60,62,79,54,88],[6],[[0,1,2],[3,0,4],[4,0],[5,0,6],[4,0],[4,3,100],[4,5,6],[6,4],[4,5,7],[8],[9],[10,11],[12,7],[10,7,11],[12,10,13]]),
([w0,w16,w1,w2,w3,w131],[142,110,97,81,88,54,115,117,62],[],[[0,1,2],[3,0],[0,1,2],[4,5],[2,1],[6],[0],[2,1],[4,6,7],[0,5],[3,0],[8,0],[2,1],[4,8],[2,1]]),
([w133,w0,w16,w1,w2,w3],[81,24,66,4,82,117,56,62,54,88,104,6,90,67,79,97],[6],[[0,1,2],[3,4,5,6],[7,1],[8,4,9],[0,10,6],[0,11,100],[0,9],[2,0],[2,8],[12],[13],[0,14],[8,2],[0,14],[15,0]]),
([w77,w1,w102,w2,w3,w64],[90,173,81,104,4,110,9,48,144,54,62,66,56,88],[],[[0],[],[1],[2,3,4],[0,5],[2,6],[7,8,9],[2,5],[7,3,10],[6,2],[10,5,9],[2,3,11],[12,2,9],[7,3,13],[2,3,5]]),
([w0,w16,w1,w178,w2,w64],[88,196,110,62,48,17,79,56,90,35,81,55],[],[[0,1,2],[3,0],[0,4,5],[0,1,2],[6,2,7],[8],[7,2,9],[1],[0,6],[7,1,10],[1,11],[3,0],[7,2,9],[0,2,4],[0,3]]),
([w179,w0,w16,w1,w2,w64],[17,48,11,35,4,79,81,34,56,110,54,65,86,60,14,78],[],[[0,1,2],[3,4,5],[6,0],[3,5,7],[1,8,9],[10,1,9],[10,1,9],[11,1,9],[5,8],[12],[13],[1,5,14],[10,11],[1,5,15],[1,5,15]]),
([w0,w16,w1,w180,w2,w3],[81,197,110,65,79,48,86,37,62,54,56],[],[[0,1,2],[0,1],[0,2],[3,0],[4,3,5],[6],[5,4,7],[1],[0,2],[3,1,8],[1,9],[0,1],[5,4,7],[0,2],[10,0,9]]),
([w181,w0,w16,w1,w2,w3],[26,56,21,37,6,79,62,36,48,110,55,66,86,60,14,78],[],[[0,1,2],[3,4,5],[6,0],[3,5,7],[1,8,9],[10,1,9],[10,1,9],[11,1,9],[5,8],[12],[13],[1,5,14],[10,11],[1,5,15],[1,5,15]]),
([w103,w104,w1,w2,w3,w64],[86,56,10,54,55,68,175,48,79,148,81,62,110],[],[[],[0,1],[2,0],[0,3],[3,4],[5],[6],[7,8],[1,8],[1,9,3],[1,8,10],[7,8,11],[1,3],[3,4],[1,12,7]]),
([w0,w105,w1,w2,w106,w64],[62,104,66,81,115,198,199,55,54],[],[[0,1],[0,1],[2,0],[0,1],[3,2],[4],[5],[],[0,1],[2,6,7],[2,6,3],[0,1],[6,3],[8,0,7],[0,1]]),
([w0,w16,w1,w2,w3,w182],[62,110,66,78,54,115,120,81,117,55],[],[[0,1],[0,1],[2,0],[0,3],[4,1],[5],[6],[7,1],[0,3,8],[4,2],[2,1,3],[0,2,8],[9,1,3],[4,0,3],[0,1,7]]),
([w0,w16,w1,w2,w3,w183],[62,6,104,66,54,115,120,81,78,55],[],[[0,1,2],[0,2],[3,0],[0,2],[4,3],[5],[6],[7,5],[0,2],[4,3],[3,8],[0,2],[9,4],[4,0,8],[0,2]]),
([w107,w108,w0,w1,w2,w64],[54,4,79,86,200,62,110,56,35,78,81,66,201],[],[[],[0,1,2],[3],[4],[5,6],[5,0],[7,8,9],[7,0],[2,9,10],[0,6],[11,5],[0,6],[0,12],[5,2],[0,2,9]]),
([w0,w16,w1,w2,w3,w184],[54,4,110,66,79,56,86,60,14,36,78,62,44],[],[[0,1,2],[0,2],[3,2],[3,0],[4,0,5],[6],[7],[1,2,8],[9,4,8],[0,3],[3,2,10],[11,3,4],[5,0],[9,0,4],[5,2,12]]),
([w0,w16,w185,w1,w2,w3],[54,4,110,66,36,79,37,86,60,81,62,56],[],[[0,1,2],[0,2],[0,2],[3,2],[3,0],[4,5,6],[7],[8],[1,2,9],[10,3,4],[0,5,6],[9,2],[0,3],[3,2,9],[11,0]]),
([w0,w109,w1,w2,w3,w110],[54,110,66,115,202,81,203,62,55],[],[[0,1],[0,1],[2,1],[2,0],[0,1],[3],[4],[5,1],[],[0,6],[2,1,5],[7,2,6],[8,0],[0,6],[5,1]]),
([w0,w16,w1,w2,w186,w64],[54,110,66,115,120,81,62,104,55],[],[[0,1],[0,1],[2,1],[2,0],[0,1],[3],[4],[5,1],[6,3,7],[0,2],[2,1,5],[6,2,7],[8,0],[0,6,8],[5,1]]),
([w0,w16,w1,w2,w187,w64],[66,4,110,55,78,81,86,60,62,65,54],[],[[0,1,2],[3,2],[0,2],[0,4],[5,0],[6],[7],[1,2,4],[8,4],[3,0],[0,2,4],[8,0,9],[3,2,4],[10,3],[5,2]]),
([w111,w112,w0,w1,w2,w3],[78,6,79,90,204,81,104,55,115,37,62,65,205],[],[[],[0,1,2],[3],[4],[5,6],[5,7],[8,0],[9,0],[2,0,10],[5,6],[11,5],[2,0,7],[0,12,7],[5,0,2],[7,0]]),
([w0,w16,w1,w2,w188,w64],[55,6,104,65,79,48,90,67,34,35,14,81,78,42],[],[[0,1,2],[0,2],[3,2],[4,0,5],[3,0],[6],[7],[8,4,9],[1,2,10],[0,3],[11,3,4],[3,2,12],[8,0,4],[5,0],[5,2,13]]),
([w0,w189,w16,w1,w2,w64],[55,48,65,104,34,79,35,56,90,67,62],[],[[0,1,2],[0,1,3],[0,1,3],[2,1,3],[2,0],[4,5,6],[7,2],[0,5,6],[1,3,7],[8],[9],[1,3,10],[0,2],[1,3,10],[1,0]]),
([w0,w16,w1,w2,w73,w74],[62,6,104,65,78,90,133,55,88],[6,29],[[0,1,2],[0,2],[3,0],[0,4],[100,2],[5],[6],[1,2,4],[0,4],[6,7],[3,2,4],[0,3,6],[7,2,4],[8,0],[101]]),
([w0,w190,w1,w2,w3,w64],[65,6,104,55,115,120,34,113,136,81,66,78,62],[],[[0,1,2],[3,2],[0,2],[3,0],[0,3],[4],[5],[6,1,7],[1,2,4],[0,8,3],[9,0,10],[0,2,10],[3,9,11],[8,2,3],[9,2,12]]),
([w191,w0,w1,w2,w3,w64],[104,65,115,0,113,34,36,55,136,66,78,110],[],[[0,1],[2,1],[3,2],[4,2,5],[0,2,6],[7,0],[1,0],[7,0],[1,7],[1,8,7],[9,1],[1,0,9],[7,10],[8,0,7],[0,11]]),
([w0,w16,w124,w2,w3,w64],[55,104,65,14,115,40,81,110,62,1,78,54],[],[[0,1],[0,1],[2,1],[0,1],[2,0],[2,3,4],[5],[6,3,7],[8,1],[0,9,2],[5,2],[2,1,8],[0,6,10],[11,0],[6,1,7]]),
([w0,w16,w1,w125,w3,w64],[65,104,54,55,115,0,136,66,88],[],[[0,1],[2,1],[0,1],[3,0],[0,3],[4],[2,4,5],[6,4],[6,1,4],[0,5,2],[7,0],[0,1,7],[3,2],[2,1,3],[8,1]]),
([w0,w192,w1,w2,w3,w64],[55,104,66,54,0,115,6,78,65,88],[],[[0,1],[0,1],[2,1],[0,1],[3,0],[2,4,5],[0,3],[6,5],[6,1,5],[0,2],[2,7],[8,1,2],[0,3],[3,0],[9,1]]),
([w0,w193,w1,w2,w3,w64],[54,6,110,88,115,120,65,66,55,81],[],[[0,1,2],[0,2],[3,2],[3,0],[0,2],[4],[5],[1,2,4],[1,4],[0,6],[7,2,6],[6,3,7],[8,0],[0,8],[3,2,9]]),
([w0,w194,w1,w2,w3,w64],[54,55,104,65,0,115,34,113,6,66,48,110],[],[[0,1],[0,2],[3,2],[1,0],[0,1],[3,4,5],[0,1],[6,5,7],[8,2,5],[0,3],[9,3],[3,2,9],[1,0],[0,1],[10,2,11]]),
([w0,w195,w1,w2,w3,w64],[54,6,104,66,90,67,34,14,113,78,48,55,88],[],[[0,1,2],[0,2],[3,2],[3,0],[0,3],[4],[5],[6,7,8],[1,2,7],[0,3],[3,9],[10,2,3],[11,0],[0,2,9],[10,2,12]]),
([w113,w0,w1,w71,w3,w64],[88,6,81,14,36,4,89,120,66,65,206],[44],[[0,1,2],[3,4],[1,3],[4,2,3],[0,3,1],[2,0],[0,5,6],[0,7],[2,7],[8,6,100],[2,7,8],[9,0,7],[2,6,5],[10],[0,2]]),
([w113,w0,w1,w2,w64,w74],[66,6,81,40,14,207,97,137,120,104,208],[],[[0,1,2],[0,3,4],[5],[1,4],[6,2],[2,6],[0,2],[2,0],[7,0],[0,7],[7,0],[2,0,6],[8,9],[6,2],[10]]),
([w0,w1,w2,w196,w3,w64],[81,121,88,104,182,66,54,122],[],[[0,1,2],[2,0],[0,1,3],[2,1,3],[0,4],[5,4,6],[1,4],[0,4,5],[1,2,4],[4,6],[7,0,4],[1,3,2],[0,1,7],[1,3,2],[0,3,2]]),
([w120,w0,w20,w2,w3,w64],[81,88,115,78,0,66,117,6,68,54,36,55],[44],[[0,1],[2,3],[2,4],[0,2,5],[6,1],[0,7,8],[1,0],[1,2],[0,2],[9,8,100],[10],[1,2,7],[11,0,2],[1,2,9],[0,1]]),
([w0,w20,w1,w71,w2,w74],[66,6,104,54,4,89,137,14,68,209,179,122,81],[],[[0,1,2],[3,2],[0,4,5],[0,2],[6,0],[7],[1,2,4],[3,8],[9],[0,2],[0,6],[6,0],[7],[10],[11,3,12]]),
([w0,w20,w1,w125,w2,w64],[66,138,68,81,122,104,14,97,0,137],[],[[0,1,2],[3,4,5],[0,4,5],[0,3],[3,0],[6],[3,2,7],[4,2,7],[1,2],[0,8,3],[0,9],[9,0],[6],[3,4],[4,5,6]]),
([w197,w0,w1,w2,w3,w64],[14,58,10,66,86,60,6,68,56,99,97,65,88,79],[6],[[0,1,2],[3,1,4],[5],[4,0],[6,0],[7,8],[3,8,100],[3,9],[10,3],[3,7],[3,9],[11,3],[8,7,9],[12,9,13],[8,7,10]]),
([w198,w0,w1,w2,w3,w64],[76,4,0,6,68,60,89,170,62,85],[],[[0],[1,2],[0,1],[1,0],[3,0],[4,5],[6,5],[4,7,8],[6,5],[9,4],[5,7],[8,4,6],[5,4,6],[9,7,8],[5,4,6]]),
([w115,w0,w1,w24,w3,w64],[66,4,62,34,14,210,6,91,120,97,211],[44],[[0,1,2],[0,3,4],[1,4],[1,4],[3,2,4],[2,5],[0,6,7],[0,8],[9,0],[0,5,100],[0,5,8],[2,0,5],[10],[2,7,6],[2,9]]),
([w115,w0,w1,w2,w3,w74],[66,4,62,40,14,212,88,120,137,110,213],[],[[0,1,2],[0,3,4],[5],[1,4],[6,2],[2,6],[0,2],[0,7],[8,0],[0,8],[0,7],[2,0,6],[7,9],[6,2],[10]]),
([w0,w1,w2,w199,w3,w64],[62,125,97,110,182,65,137,117,138],[],[[0,1,2],[2,0],[0,1,3],[0,4],[2,1,3],[5,4,6],[1,4],[1,2,4],[0,4,5],[4,7],[1,3,2],[8,0,4],[1,3,2],[0,1,7],[0,3,2]]),
([w118,w0,w69,w2,w3,w64],[62,125,97,106,35,34,14,137,63,115,54],[44],[[0,1,2],[1,3],[4,5],[1,2,4],[0,6,7],[0,1,8],[2,0],[0,9],[2,1,9],[10,8,100],[1,8],[5],[1,9],[10,0,9],[0,2]]),
([w0,w69,w1,w24,w2,w74],[137,4,110,62,6,91,97,106,138,63,214,65,215,178],[],[[0,1,2],[3,2],[0,4,5],[6,0],[0,2],[7],[1,2,4],[8,9],[10],[0,2],[11,0],[0,6,3],[12],[13],[6,3]]),
([w0,w69,w1,w125,w2,w3],[62,122,63,138,97,110,65,14,88,0,137],[],[[0,1,2],[0,3,4],[4,3,5],[4,0],[0,3,6],[7],[0,2,8],[3,2,8],[1,2],[0,9],[6,10],[10,4,6],[7],[0,3],[3,5,4]]),
([w200,w0,w1,w2,w3,w64],[97,58,14,65,137,76,4,63,48,88,99,66,68],[6],[[0,1,2],[3,1,4],[5],[0,2,6],[6,2],[7,0,8],[0,8,100],[9,3],[0,10],[3,7],[11,0,3],[3,9,10],[0,10,12],[8,7,9],[0,7,9]]),
([w201,w0,w1,w2,w3,w64],[76,6,0,4,68,67,91,63,170,85,81],[],[[0],[1,2],[0,1],[3,0],[1,0],[4,5],[6,5],[4,5],[7,8,9],[9,4],[10,6],[5,4],[9,4],[5,6],[5,4]]),
([w118,w0,w1,w2,w64,w74],[68,6,78,81,34,128,97,115,136,54,214],[],[[0,1],[2],[2,0],[1,0],[3,0,4],[3,5],[6,3],[3,7],[8,7],[9,5],[5,7],[3,4],[8,7],[6,3],[10]]),
([w0,w124,w1,w24,w2,w64],[81,138,110,97,121,91,14,1,55,207,125,136],[],[[0,1,2],[0,2],[3,4,5],[3,0],[0,2],[6],[0,2],[3,7],[1,6],[0,2],[8,9],[10,6,9],[6],[0,2],[11,6]]),
([w202,w0,w1,w2,w3,w64],[14,0,70,56,60,6,81,91,83,55,62,89,54],[6],[[0,1],[2],[3,4],[3,0],[5,0],[6,3,100],[7,3],[7,8,9],[6,3,8],[3,7,9],[3,7,6],[10,8,11],[3,6,8],[12,7],[3,7,6]]),
([w203,w0,w1,w2,w3,w64],[70,0,4,6,68,86,216,91,139,88,97,51,63],[],[[0],[0,1],[2,1],[1,0],[3,0],[4,5],[6,5,7],[4,8,9],[10,5,8],[11,4,6],[5,6,8],[11,4,6],[5,4,8],[9,7,12],[5,4,10]]),
([w120,w0,w1,w2,w3,w74],[63,4,78,62,36,131,88,115,136,55,209],[],[[0,1],[2],[2,0],[1,0],[3,0,4],[3,5],[6,3],[3,7],[8,7],[9,5],[5,7],[3,4],[8,7],[6,3],[10]]),
([w0,w124,w1,w71,w2,w3],[136,122,110,62,88,14,40,1,54,121],[],[[0,1,2],[3,0],[0,2],[4,2],[0,5],[5],[3,6],[0,7,4],[1,2,5],[3,6],[8,0],[9,2,5],[5],[3,2,5],[0,2,5]]),
([w204,w0,w1,w2,w3,w64],[14,0,70,48,67,4,62,91,54,83,81,55],[6],[[0,1],[2],[3,4],[5,0],[3,0],[6,3,100],[7,3],[6,3,7],[8,9],[3,7,8],[10,7],[3,9],[11,8],[3,6,7],[3,7]]),
([w205,w0,w1,w2,w3,w64],[70,0,6,4,63,90,217,91,139,97,51,110],[],[[0],[0,1],[2,1],[3,0],[1,0],[4,5],[6,5,7],[7,5],[4,8,9],[10,4,6],[10,4,6],[5,6,8],[9,8,11],[5,4,7],[5,4,7]]),
([w206,w0,w1,w2,w3,w64],[14,0,70,51,91,21,62,98,136,83],[],[[0,1],[2],[3,4],[3,0,4],[3,0,5],[6,7,8],[4,3],[4,3],[8,3,9],[3,4],[3,4],[3,9,7],[8,9],[7,4],[6,4,7]]),
([w207,w0,w1,w2,w3,w64],[14,58,10,85,63,76,6,97,100,137,99,107],[],[[0,1,2],[3,1,4],[5],[3,0,6],[3,0,4],[4,3],[7,8,9],[9,3,10],[4,3],[3,4],[9,4],[8,10],[3,10,11],[3,4],[7,4,11]]),
([w208,w0,w1,w2,w3,w64],[70,0,91,51,63,121,139,125],[],[[0],[0,1],[2,3],[1,0],[1,0],[4,5],[2,3],[2,3],[4,3],[3,2],[3,2],[3,6,5],[7,6],[5,2],[5,2]]),
([w209,w0,w1,w2,w3,w64],[97,6,62,14,0,78,120,85,91,137,110],[],[[0,1,2],[3,4],[5],[0,3,4],[1,2,3],[2,0],[0,2],[2,6],[0,6],[7,8,9],[9,0,6],[2,6,9],[0,6,10],[7,2],[0,8]]),
([w210,w0,w1,w2,w3,w64],[76,63,0,85,58,46,178,91,138,122,170],[],[[0],[1,2,3],[0,4,5],[6,3],[1,0,3],[1,3],[7,8],[7,3],[1,3],[3,1],[9,1],[8,10],[3,10,9],[3,1],[8,1,7]]),
([w211,w0,w1,w2,w3,w64],[110,6,97,78,0,63,62,115,51,136,88],[],[[0,1,2],[3],[3,4],[0,2],[1,3],[5,0,6],[2,0],[6,7],[2,0],[8,5,9],[8,0],[6,7,10],[2,0],[9,5,7],[2,0]]),
([w212,w0,w1,w2,w3,w64],[97,6,62,14,0,78,178,120,85,136,60,88,91],[17],[[0,1,2],[3,4],[5],[0,3,6],[1,2,3],[2,0],[0,2],[2,7],[0,7],[8,9,100],[10,0,7],[2,7,11],[0,7,9],[8,2],[0,12]]),
([w18,w0,w126,w2,w3,w64],[62,98,88,115,78,42,4,137,51,86,110,81],[17],[[0,1,2],[3,4],[5],[6,3],[0,2],[0,2],[2,0],[0,3],[7,3],[8,7,100],[7,3],[0,2],[9,3],[2,0],[0,10,11]]),
([w213,w0,w1,w2,w3,w64],[62,6,88,56,0,35,80,115,81,51,137,86,110],[17],[[0,1,2],[3],[3,4],[3,5,6],[0,2],[0,2],[2,0],[0,7],[8,7],[9,10,100],[8,7,10],[0,2],[11,7],[2,0],[0,12,8]]),
([w19,w0,w1,w127,w3,w64],[110,4,62,166,0,56,14,100,88,120,97,85,60],[17],[[0,1,2],[3],[4,1,5],[0,6,1],[7,2,6],[2,0],[8,0],[2,9],[10,0],[11,4,100],[12,0,9],[2,8],[10,0],[8,2],[2,0,10]]),
([w214,w0,w1,w2,w3,w64],[88,4,62,14,0,78,120,97,85,136,81,89],[17],[[0,1,2],[3,4],[5],[1,3],[0,2],[2,0],[0,2],[0,6],[7,6],[8,9,100],[10,6,7],[2,0],[7,6,9],[0,2],[0,11]]),
([w18,w0,w128,w2,w3,w64],[81,106,97,115,78,44,62,6,51,137,90,63],[17],[[0,1,2],[3,4],[5],[0,2],[6,3,7],[0,2],[2,0],[6,3],[0,3],[8,9,100],[0,2],[6,3,5],[2,0],[10,3],[0,11,6]]),
([w215,w0,w1,w2,w3,w64],[62,6,97,48,0,113,14,115,51,137,81,90,63],[17],[[0,1,2],[3],[1,4],[5,2,6],[0,6,1],[0,2],[2,0],[0,7],[2,7],[8,9,100],[8,2],[0,7,9],[2,7,10],[11,0,7],[0,12]]),
([w19,w0,w1,w129,w3,w64],[97,6,81,182,0,78,88,120,85,67,89],[17],[[0,1,2],[3],[4,1,5],[0,2],[1,3],[2,0],[0,2],[6,7],[0,7],[8,4,100],[2,0],[9,6,7],[0,2],[6,7,9],[0,10,6]])]
noncomputable def p14_D4 : List StD := [
([w0,w1,w28,w130,w64],[218,104,81,89,99,62,51,58,56,54],[],[[0,1,2],[3,1,4],[5,0],[2,0],[6,3],[2,0,7],[5,0,1],[8,0],[9,0],[2,1,5]]),
([w29,w0,w1,w130,w64],[89,81,99,51,4,54,97,62],[],[[0,1,2],[3,0],[4,0,1],[5,2],[1,6],[7,3,5],[0,3],[1,6],[3,0],[1,0,7]]),
([w0,w1,w28,w3,w131],[218,110,62,89,99,219,51,55,54],[],[[0,1,2],[3,1,4],[2,0],[3,0,5],[6,3],[6,0,1],[2,0,3],[7,0],[8,0],[2,1,3]]),
([w29,w0,w1,w3,w131],[89,220,99,51,97,55,54,62],[],[[0,1,2],[3,0],[4,0,5],[6,1],[5,4],[5,3,6],[0,3],[3,4],[3,0],[4,0,7]]),
([w37,w0,w2,w130,w64],[62,221,140,51,89,54,97,222,55],[],[[0,1,2],[3,2],[3,1,2],[0,1,4],[2,0,3],[0,3,5],[4,3],[6,4,7],[5,0,8],[0,4]]),
([w37,w0,w2,w3,w131],[54,97,182,142,51,89,55,62],[],[[0,1],[0,2,3],[4,1],[4,2,3],[1,4,5],[6,0],[0,4,5],[1,0,6],[0,6],[1,5,7]]),
([w133,w0,w1,w2,w130],[89,51,54,14,55,62,97],[],[[0,1],[1,0],[2,3,4],[5,0],[2,6],[0,1],[4,1,2],[1,0],[1,6],[4,0]]),
([w132,w0,w1,w2,w131],[62,51,54,14,97,55,89],[],[[0,1,2],[1,3],[4,2,3],[0,3,4],[0,4],[4,0],[2,1,5],[1,6],[0,6],[2,0,5]]),
([w132,w133,w0,w1,w2],[97,89,14,55,51,54],[],[[0,1,2],[3,4,5],[4,0],[0,1,3],[0,3],[4,1],[5,3],[3,0],[0,4,1],[3,1]]),
([w216,w0,w1,w3,w64],[89,58,10,51,55,54,97,62],[],[[0,1,2],[3,0],[4,0],[5,4],[4,6],[4,3,5],[0,3],[3,6],[3,0],[6,0,7]]),
([w0,w36,w2,w130,w64],[63,97,54,104,110,19,85,56,65,14],[],[[0,1,2],[1,3],[4,3,5],[0,6],[6,0],[7,0],[8,3,9],[1,4],[6,0],[1,0,4]]),
([w0,w36,w2,w3,w131],[63,97,54,110,88,85,65,66],[],[[0,1,2],[1,3],[4,5,6],[0,3,1],[5,0],[7,0],[6,4,7],[1,3],[4,0],[1,0,3]]),
([w217,w0,w2,w3,w64],[54,0,97,89,66,65,62,55],[],[[0,1,2],[0,1,3],[4,2,5],[5,3,4],[2,6],[4,0],[0,4],[2,0,7],[0,6,7],[2,3,6]]),
([w146,w0,w17,w3,w64],[97,58,89,166,62,182,167,56,65,223,55],[17],[[0,1,2],[100],[0,2,3],[4,5,6],[0,7],[4,8],[0,9,2],[7,0,8],[8,2,10],[0,2,4]]),
([w0,w16,w17,w3,w86],[55,166,89,56,62,224,28,104],[17],[[0,1,2],[3,4],[0,5],[2,0,6],[100],[1,2],[4,5,7],[0,5],[0,2],[4,2]]),
([w218,w1,w2,w3,w86],[4,166,60,86,14,89,28,63,62,88],[],[[0,1,2],[0,1,3],[0,4],[5,4,6],[1,7,5],[1,7],[8,5],[1,5],[9,7],[1,5]]),
([w0,w1,w2,w219,w3],[62,88,89,24,28,182,63,137,136],[],[[0,1],[1,0],[2,3,4],[0,5],[2,6],[0,1],[7,5],[1,0],[8,2],[0,2]]),
([w87,w0,w16,w17,w3],[224,28,89,62,104,65,55,166,56],[17],[[0,1,2],[3,4],[5,1,6],[3,2],[2,7],[3,8],[3,5],[100],[7,2],[6,5]]),
([w220,w0,w1,w2,w3],[89,28,24,106,125,107,62,122,88,167,91,55,137,63],[],[[0,1,2],[3,0,4],[5,6,7],[3,0],[6,8],[0,6,8],[6,9,10],[11,0],[12,10,13],[11,0]]),
([w87,w218,w1,w2,w3],[63,24,28,62,88,14,89,166],[],[[0,1,2],[3,1],[4,0],[3,0],[0,4,3],[4,3],[3,5],[0,6],[7,0],[7,6]]),
([w0,w149,w17,w3,w64],[62,58,63,56,104,223,135,55],[45],[[0,1,2],[100,0,3],[0,4],[2,5],[3,1,6],[5,2],[0,4],[3,6],[6,0,7],[0,2]]),
([w151,w0,w17,w3,w64],[46,166,9,56,63,104,182,137,79,225,223,78],[17],[[0,1,2],[100,0,3],[1,4],[5,6,7],[3,5],[8,5,9],[4,10],[3,8,11],[9,4,11],[9,4,10]]),
([w0,w16,w17,w3,w88],[63,166,56,137,226],[],[[0,1],[2,3],[3,4],[0,4],[4],[1,0],[3,4],[2,4],[4],[4]]),
([w89,w0,w16,w17,w3],[26,223,21,182,167,78,48,225,63,104,55],[17],[[0,1,2],[3,4],[5,0,6],[1,7,8],[8,1],[1,9],[10,7,9],[100],[1,3],[1,5]]),
([w0,w150,w153,w3,w64],[63,104,55,48,223,167,182,78],[17],[[0,1,2],[1,3],[2,1],[0,2,4],[100],[4,0],[5,1,6],[2,7],[3,0,2],[4,0]]),
([w0,w150,w156,w3,w64],[9,104,167,48,88,63,224,223],[17],[[0,1,2],[1,3],[4,1],[5,6,7],[100],[7,5],[2,1,4],[7,6],[3,1,6],[4,1]]),
([w218,w1,w2,w3,w88],[6,167,67,90,4,226],[],[[0,1,2],[0,1,3],[4,5],[0,5],[5],[5],[1,5],[5],[1,5],[1,5]]),
([w89,w218,w1,w2,w3],[26,6,14,62,88,167,104,4,63,89,166],[],[[0,1,2],[3,0],[4,3],[3,5,6],[1,5,6],[1,5,6],[7,2],[5,8,9],[10,8],[10,9]]),
([w162,w0,w17,w3,w64],[182,58,10,166,48,88,225,65,55,63],[17],[[0,1,2],[100],[3,0],[3,0],[4,5],[5,6,7],[7,8],[8,7],[4,5,8],[5,9]]),
([w0,w16,w17,w94,w64],[63,167,48,104,137,224,0,225,42],[17],[[0,1],[2,3],[4,3],[0,5,4],[100],[4,0],[1,3,5],[5,6],[2,0,5],[7,0,8]]),
([w218,w1,w2,w94,w64],[70,167,67,90,137,89,0,63,68,97,91],[],[[0,1,2],[1,3],[4,0],[1,0],[1,4,5],[4,6,7],[1,5,8],[9,5,8],[1,7,10],[1,5,8]]),
([w0,w1,w2,w221,w64],[63,104,81,89,97,137,182,136],[],[[0,1,2],[3,1,4],[5,1],[0,6,2],[0,3],[2,0,4],[5,1,6],[4,2],[7,0,6],[2,0,6]]),
([w95,w0,w16,w17,w64],[224,19,91,137,63,56,65,223,78],[17],[[0,1,2],[3,4],[5,1,6],[7,2,4],[2,7],[3,5],[3,7,4],[100],[3,2],[6,4,8]]),
([w222,w0,w1,w2,w64],[91,19,15,63,83,76,166,86,97,65,89,62,88],[],[[0,1,2],[3,0,4],[5,6,7],[3,0,8],[3,6],[0,6],[3,6],[9,0,3],[9,10,11],[12,0,3]]),
([w95,w218,w1,w2,w64],[4,15,65,166,63,89,14,62,88],[],[[0,1,2],[3,1,4],[3,5],[3,4],[0,2],[0,3,5],[2,6],[3,4,5],[7,5],[8,4]]),
([w0,w165,w17,w3,w64],[182,58,10,97,48,91,225,110,188,65],[45],[[0,1,2],[100,3,4],[5,6],[3,7],[4,1,8],[3,0,7],[6,0],[8,3,9],[4,8],[3,5]]),
([w167,w0,w17,w3,w64],[46,166,9,56,182,117,36,110,91,224,225,79,223],[17],[[0,1,2],[100,0,3],[1,4],[5,4,6],[3,7],[8,9,10],[11,7,12],[3,7,9],[10,9],[10,7]]),
([w0,w16,w17,w98,w64],[91,167,48,88,225,137,227],[],[[0,1],[2,3],[0,4],[5,6],[6],[5,6],[1,0],[6],[2,3,6],[3,0,4]]),
([w99,w0,w16,w17,w64],[17,225,11,182,166,78,56,223,91,110,65],[17],[[0,1,2],[3,4],[5,0,6],[1,7,8],[8,1],[1,9],[10,7,9],[100],[1,3],[1,5]]),
([w0,w166,w169,w3,w64],[91,166,56,110,224,225,81],[17],[[0,1],[2,3],[0,4,5],[6,3],[100],[1,3,4],[5,0],[2,0,4],[5,4],[5,0]]),
([w0,w166,w172,w3,w64],[9,110,167,48,91,225,65,166,182,56,78],[17],[[0,1,2],[1,3],[4,5],[6,1],[100],[7,1,8],[2,4],[9,1,6],[3,10],[5,1]]),
([w218,w1,w2,w98,w64],[6,167,67,90,11,14,4,137,91,81,88,62,166,97],[],[[0,1,2],[0,1,3],[4,5,6],[0,5],[1,7,8],[7,4,9],[1,10,11],[12,9,13],[1,8],[1,8]]),
([w99,w218,w1,w2,w64],[17,4,97,81,166,91,60,6,228],[],[[0,1,2],[3,0],[2,3],[2,4,5],[1,4,6],[1,4,5],[7,8],[8],[8],[8]]),
([w132,w0,w16,w17,w64],[91,15,19,166,80,229,56,65,97,223,79,88,55],[17],[[0,1,2],[3,4,5],[6,0,7],[5,0],[0,3],[6,8],[7,9,10],[100],[11,0,10],[7,10,12]]),
([w133,w0,w16,w17,w3],[97,24,79,166,230,48,55,91,167,225,65],[17],[[0,1,2],[3,2,4],[5,1,6],[0,7],[0,8,7],[0,5],[2,9],[100],[0,2],[6,0,10]]),
([w223,w1,w2,w3,w64],[86,56,10,65,55,79,62,97,48,110],[36],[[0,1],[2,0,1],[0,3],[3,4],[1,100,4],[1,3],[3,5,6],[1,5,7],[8,4],[1,9,7]]),
([w179,w0,w16,w17,w64],[17,225,11,35,166,79,65,56,223,110,182,78],[17],[[0,1,2],[3,4,5],[6,0,7],[1,8,9],[6,1,9],[1,9],[5,8],[100],[1,5,10],[1,5,11]]),
([w181,w0,w16,w17,w3],[26,223,21,37,167,182,78,48,225,110,55,224],[17],[[0,1,2],[3,4,5],[6,0,7],[1,8,9],[10,1,9],[1,9],[10,8,11],[100],[1,5],[1,6]]),
([w224,w0,w1,w2,w64],[55,6,65,115,34,110,78,88,79],[46],[[0,1,2],[3,2],[0,3,4],[1,3],[0,5],[2,5],[2,0],[0,100],[2,6],[7,0,8]]),
([w0,w16,w17,w3,w182],[65,110,231,88,97,82,117,78],[47],[[0,1],[1,2],[3,0],[0,1],[100],[4,1],[3,5,6],[2,0],[0,3,7],[3,1,4]]),
([w108,w0,w1,w2,w183],[110,65,115,120,78,97,55,137,88],[],[[0,1],[2,1],[3,4],[0,2,5],[6,0],[1,0],[1,4],[1,7],[1,0,4],[8,0]]),
([w0,w16,w17,w3,w183],[97,167,89,48,88,224,137,55],[17],[[0,1,2],[0,3],[4,5],[0,5],[100],[0,2,6],[1,5],[7,0,5],[3,2,5],[0,2,4]]),
([w0,w16,w17,w3,w184],[88,110,56,224,137,44],[17],[[0,1],[0,2],[0,3],[4,1],[100],[4,1,3],[0,3,4],[2,1,3],[0,3],[0,1,5]]),
([w0,w16,w185,w17,w3],[88,110,137,56,225,65,89,97,55],[17],[[0,1],[2,1],[0,3],[0,4,5],[0,6],[100],[2,1,7],[4,0,8],[0,1,4],[3,1,5]]),
([w225,w0,w1,w2,w3],[97,6,55,115,78,37,4,48,110,81],[48],[[0,1,2],[3,4],[5,1,2],[0,3,6],[2,0],[0,7,8],[2,4],[2,100],[9,0],[0,4,2]]),
([w0,w16,w17,w186,w64],[55,110,232,224,81,88,104],[49],[[0,1],[1,2],[0,3],[4,0],[100],[4,1],[5,3,6],[0,1,3],[2,0],[4,1]]),
([w112,w0,w1,w2,w187],[81,55,115,78,120,88,137,65],[],[[0,1],[2,3],[4,1],[0,2,5],[0,5],[5,0],[1,3],[1,6,7],[0,3,6],[1,0,3]]),
([w0,w16,w17,w187,w64],[81,110,233,88,224,137,55],[17],[[0,1],[0,2],[3,4],[0,1],[100],[0,1],[3,4,5],[6,0,4],[2,3,4],[0,1]]),
([w0,w16,w17,w188,w64],[55,167,110,48,137,35,182,225],[17],[[0,1,2],[2,3],[4,0],[4,0],[100],[4,2,5],[1,6],[0,2],[3,0],[7,2]]),
([w0,w189,w16,w17,w64],[55,225,65,110,34,35,104,88],[17],[[0,1,2],[0,1,3],[1,3],[2,0],[4,3,5],[0,2],[1,3],[100],[1,6,7],[1,0]]),
([w191,w0,w1,w2,w73],[110,6,55,115,78,38,88,137,65],[],[[0,1,2],[3,4],[5,2,3],[0,3,1],[2,0],[6,0],[2,4],[2,7,8],[7,0,4],[2,0,4]]),
([w0,w192,w17,w3,w64],[55,65,88,56,166,80,35,182,117,110,104],[],[[0,1],[2,3],[0,1],[1,0],[0,1],[4,5,6],[2,7,8],[0,1],[1,0],[2,9,10]]),
([w0,w193,w17,w3,w64],[88,110,56,224,65,166,117,81],[17],[[0,1],[0,2],[0,3],[4,1],[100],[5,1,3],[0,3,6],[2,1,3],[4,0,3],[0,1,7]]),
([w0,w194,w17,w3,w64],[65,110,48,55,34,182,166,225],[],[[0,1],[1,2],[3,0],[0,1],[0,3],[4,1,5],[6,5],[3,0],[0,3],[7,1]]),
([w0,w195,w17,w3,w64],[65,166,104,48,55,182,225,88],[17],[[0,1,2],[2,3],[4,0],[0,4],[100],[1,5],[1,2,5],[4,0],[0,2,4],[6,2,7]]),
([w113,w0,w1,w71,w74],[88,122,81,14,131,110,137,234,179],[50],[[0,1,2],[3,4],[1,3],[0,2],[2,0],[0,1,5],[6,1,5],[6,7,100],[2,0],[8]]),
([w120,w0,w20,w2,w74],[110,4,88,14,40,137,6,104,55,209,81],[50],[[0,1,2],[0,3,1],[3,4],[5,2,3],[2,6,7],[2,0],[5,0],[8,0,100],[9],[2,8,10]]),
([w115,w0,w1,w24,w74],[110,137,55,128,6,235,62,104,210,178],[50],[[0,1],[2,1,3],[0,4],[5,2,6],[2,0],[1,4,7],[1,0],[1,0,100],[1,8,6],[9]]),
([w118,w0,w69,w2,w74],[55,6,97,110,207,137,104,214,81],[50],[[0,1,2],[1,3],[0,3,4],[5,2,3],[0,3],[2,3],[5,0],[0,6,100],[7],[2,0,8]])]
noncomputable def p14_D3 : List StD := [
([w146,w218,w3,w64],[104,10,89,81,137,79,62,65,55],[],[[0,1,2],[3,2,4],[4,5,6],[4,7],[2,8,3],[3,2,6]]),
([w218,w16,w3,w86],[55,110,65,137,89,104,62],[],[[0,1],[0,2],[3,0],[3,1,4],[3,5,6],[6,1,4]]),
([w0,w16,w219,w3],[62,110,137,224],[],[[0,1],[2,1],[0,3],[0,3,2],[2,1,3],[0,1,3]]),
([w87,w218,w16,w3],[81,24,104,137,62,167,89,78],[],[[0,1,2],[3,2,4],[0,2,4],[0,5,6],[3,7],[0,6,3]]),
([w151,w218,w3,w64],[46,137,9,89,91,55,236],[],[[0,1,2],[1,3],[1,4],[5,6],[3,5,6],[6]]),
([w218,w16,w3,w88],[89,104,81,137,62],[],[[0,1,2],[3,1],[0,4],[2,0,3],[3,1,4],[2,0,4]]),
([w89,w218,w16,w3],[26,62,21,104,89,55,166],[],[[0,1,2],[1,3],[1,3],[4,3,5],[5,3],[6,4]]),
([w218,w150,w3,w64],[9,137,46,55,187],[],[[0,1,2],[3,4],[4],[1,4],[1,4],[4]]),
([w162,w218,w3,w64],[55,58,89,137,82,37,65,62],[],[[0,1,2],[3,2],[3,4,5],[0,6],[2,0,3],[7,2]]),
([w218,w16,w94,w64],[89,104,55,137,91,81],[],[[0,1,2],[3,1],[0,2,3],[3,0],[3,1,4],[5,0,4]]),
([w0,w16,w221,w64],[89,104,81,137,224],[],[[0,1,2],[3,1],[0,4,2],[2,0,3],[3,1,4],[2,0,4]]),
([w95,w218,w16,w64],[137,15,91,89,81,166,78],[],[[0,1,2],[0,3],[4,2],[2,5],[0,6],[0,2]]),
([w167,w218,w3,w64],[46,137,9,89,91,78,56,65,223,104],[],[[0,1,2],[1,3],[1,3],[4,5,6],[7,5],[8,4,9]]),
([w218,w16,w98,w64],[56,166,91,78,65,110,81,137],[],[[0,1,2],[0,3],[4,3],[1,5,6],[7,2],[6,2]]),
([w99,w218,w16,w64],[17,56,78,81,166,89,230,65,167,91],[],[[0,1,2],[3,4,5],[3,6,5],[1,4,5],[5,2,7],[8,9]]),
([w218,w166,w3,w64],[9,166,46,56,65,195],[],[[0,1,2],[3,4],[4,5],[1,5],[5],[5]]),
([w132,w218,w16,w64],[56,15,65,166,80,81,91,237,137],[],[[0,1,2],[3,4,5],[5,6],[0,3,6],[2,7],[8,6]]),
([w133,w218,w16,w3],[81,24,237,137,82,91,167,89],[],[[0,1,2],[3,4,5],[0,5],[0,6,5],[3,2],[0,7,3]]),
([w179,w218,w16,w64],[17,81,11,91,89,238],[],[[0,1,2],[1,3],[1,3],[4,5],[4,5],[5]]),
([w181,w218,w16,w3],[26,48,78,37,89,36,91,229,56,166,110,85],[],[[0,1,2],[3,4,5],[6,4,7],[1,7,6],[6,2,8],[9,10,11]]),
([w218,w16,w3,w182],[231,110,78,89,48,81,230,82,117],[],[[0,1],[0,2],[3,1,4],[5,1],[6,7,8],[5,1]]),
([w218,w16,w3,w183],[239,167,89,78,48,81,137,82,230],[],[[0,1,2],[0,3],[2,3,4],[5,2,6],[1,7,8],[5,2,8]]),
([w218,w16,w3,w184],[56,166,110,78,137,240,230,44],[],[[0,1,2],[0,3],[4,2],[1,2,5],[4,5],[6,2,7]]),
([w0,w16,w226,w3],[91,110,65,137,182,56],[],[[0,1,2],[3,1],[0,2,3],[2,0,3],[3,1,4],[5,0,2]]),
([w218,w16,w185,w3],[56,166,110,237,241,36,89,37,81],[],[[0,1,2],[3,2,4],[0,3],[5,6,7],[1,2,8],[8,2]]),
([w218,w16,w186,w64],[81,110,91,78,56,85,104],[],[[0,1],[2,3,4],[0,1],[0,1],[5,2,6],[0,1]]),
([w218,w16,w187,w64],[56,166,110,78,81,85,91,137],[],[[0,1,2],[0,3],[4,2],[1,2,4],[5,6,7],[4,2]]),
([w218,w16,w188,w64],[81,110,91,78,137,104,240],[],[[0,1],[2,3,4],[0,1],[0,1],[4,5,6],[0,1]]),
([w0,w16,w227,w64],[81,110,91,104,137,182],[],[[0,1],[2,3,4],[0,1],[0,1],[4,3,5],[0,1]]),
([w218,w189,w16,w64],[91,104,137,237,241,35,81,62],[],[[0,1,2],[3,1,4],[2,3],[2,0,5],[6,0],[2,1,7]]),
([w218,w192,w3,w64],[91,104,62,137,78,80,35],[],[[0,1,2],[0,1,2],[3,4],[3,5,6],[2,0,1],[2,0,1]]),
([w218,w193,w3,w64],[62,110,78,137,35,91,81],[],[[0,1],[0,2],[3,1],[3,1,4],[0,5,3],[0,1,6]]),
([w218,w194,w3,w64],[81,110,137,78,82,37],[],[[0,1],[2,3],[0,1],[0,1],[2,4,5],[0,1]]),
([w218,w195,w3,w64],[81,104,137,78,91,62],[],[[0,1],[2,1],[0,3],[0,4,2],[2,1,4],[0,1,5]])]
def p14_D2 : List StD := []
theorem p14_I2 : LevelN p14_R p14_T 2 p14_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C3x0 : levelOK p14_T p14_K p14_P 2 (p14_D2.map Prod.fst) ((p14_D3.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C3x1 : levelOK p14_T p14_K p14_P 2 (p14_D2.map Prod.fst) ((p14_D3.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C3x2 : levelOK p14_T p14_K p14_P 2 (p14_D2.map Prod.fst) ((p14_D3.drop (2*16)).take 16) = true := by decide +kernel
theorem p14_I3 : LevelN p14_R p14_T 3 p14_D3 := levelStep p14_B p14_W p14_Q p14_I2 (chunks 16 p14_D3 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C3x0
  · exact p14_C3x1
  · exact p14_C3x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x0 : levelOK p14_T p14_K p14_P 3 (p14_D3.map Prod.fst) ((p14_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x1 : levelOK p14_T p14_K p14_P 3 (p14_D3.map Prod.fst) ((p14_D4.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x2 : levelOK p14_T p14_K p14_P 3 (p14_D3.map Prod.fst) ((p14_D4.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x3 : levelOK p14_T p14_K p14_P 3 (p14_D3.map Prod.fst) ((p14_D4.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x4 : levelOK p14_T p14_K p14_P 3 (p14_D3.map Prod.fst) ((p14_D4.drop (4*16)).take 16) = true := by decide +kernel
theorem p14_I4 : LevelN p14_R p14_T 4 p14_D4 := levelStep p14_B p14_W p14_Q p14_I3 (chunks 16 p14_D4 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C4x0
  · exact p14_C4x1
  · exact p14_C4x2
  · exact p14_C4x3
  · exact p14_C4x4
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x0 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x1 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x2 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x3 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x4 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x5 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x6 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (6*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x7 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (7*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x8 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (8*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x9 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (9*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x10 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (10*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x11 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (11*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x12 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (12*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x13 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (13*16)).take 16) = true := by decide +kernel
theorem p14_I5 : LevelN p14_R p14_T 5 p14_D5 := levelStep p14_B p14_W p14_Q p14_I4 (chunks 16 p14_D5 14 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C5x0
  · exact p14_C5x1
  · exact p14_C5x2
  · exact p14_C5x3
  · exact p14_C5x4
  · exact p14_C5x5
  · exact p14_C5x6
  · exact p14_C5x7
  · exact p14_C5x8
  · exact p14_C5x9
  · exact p14_C5x10
  · exact p14_C5x11
  · exact p14_C5x12
  · exact p14_C5x13
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C6x0 : levelOK p14_T p14_K p14_P 5 (p14_D5.map Prod.fst) ((p14_D6.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C6x1 : levelOK p14_T p14_K p14_P 5 (p14_D5.map Prod.fst) ((p14_D6.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C6x2 : levelOK p14_T p14_K p14_P 5 (p14_D5.map Prod.fst) ((p14_D6.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C6x3 : levelOK p14_T p14_K p14_P 5 (p14_D5.map Prod.fst) ((p14_D6.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C6x4 : levelOK p14_T p14_K p14_P 5 (p14_D5.map Prod.fst) ((p14_D6.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C6x5 : levelOK p14_T p14_K p14_P 5 (p14_D5.map Prod.fst) ((p14_D6.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C6x6 : levelOK p14_T p14_K p14_P 5 (p14_D5.map Prod.fst) ((p14_D6.drop (6*16)).take 16) = true := by decide +kernel
theorem p14_I6 : LevelN p14_R p14_T 6 p14_D6 := levelStep p14_B p14_W p14_Q p14_I5 (chunks 16 p14_D6 7 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C6x0
  · exact p14_C6x1
  · exact p14_C6x2
  · exact p14_C6x3
  · exact p14_C6x4
  · exact p14_C6x5
  · exact p14_C6x6
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C7x0 : levelOK p14_T p14_K p14_P 6 (p14_D6.map Prod.fst) ((p14_D7.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C7x1 : levelOK p14_T p14_K p14_P 6 (p14_D6.map Prod.fst) ((p14_D7.drop (1*16)).take 16) = true := by decide +kernel
theorem p14_I7 : LevelN p14_R p14_T 7 p14_D7 := levelStep p14_B p14_W p14_Q p14_I6 (chunks 16 p14_D7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C7x0
  · exact p14_C7x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C8x0 : levelOK p14_T p14_K p14_P 7 (p14_D7.map Prod.fst) ((p14_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem p14_I8 : LevelN p14_R p14_T 8 p14_D8 := levelStep p14_B p14_W p14_Q p14_I7 (chunks 16 p14_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C8x0
  ))
theorem p14_L : LowN p14_R p14_T 9 := lowSearch p14_B p14_I8 (by decide +kernel)

def cofactorWord : Sig := W 0xe8a8a880e8a8a880e8a8a880e8a8a880

theorem cofactorLower : Lower true (rootsW [0,1,2,3,4]) cofactorWord 9 :=
  p14_L

end PEqualNP.Outside.L_meta_43632_aux.Model

namespace PEqualNP.Outside.L_meta_43632_aux.Model

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def readInputs {n : Nat} (raw : List Sig) (r : Row) (i : Fin n) : Bool :=
  bit r (raw.getD i.val zero)

theorem countFromTable {n bound : Nat} {raw : List Sig} {word : Sig}
    {f : (Fin n → Bool) → Bool}
    (rawList : List.ofFn (fun i : Fin n => raw.getD i.val zero) = raw)
    (plainRaw : raw.all plainWord = true)
    (plainGoal : bit 0 word = false)
    (properGoal : proper word)
    (table : ∀ r, f (readInputs raw r) = bit r word)
    (low : Lower true raw word bound)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    bound ≤ gs.countP (fun g => !isNot g) := by
  have encoded : (execute gs raw).getD o zero = word := by
    apply bit_ext
    intro r
    have bits : List.ofFn (readInputs (n := n) raw r) = raw.map (bit r) := by
      calc
        _ = (List.ofFn (fun i : Fin n => raw.getD i.val zero)).map (bit r) := by
          rw [List.map_ofFn]
          rfl
        _ = raw.map (bit r) := by rw [rawList]
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), ← bits]
    exact (heval (readInputs raw r)).trans (table r)
  have result := get_rep (u := true) (execute gs raw) o
  rw [encoded] at result
  unfold Repr at result
  rw [nrm_id plainGoal] at result
  obtain ⟨k, S, hk, run, roots⟩ := extract (u := true) gs raw legal (by simp) properGoal
    (result.resolve_right (fun h => h properGoal))
  rw [nrm_map plainRaw] at roots
  have asList := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplies : supply true (raw.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (roots a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, reach, hit, le⟩ := contraction (observe_proper properGoal) asList
    (raw.map observe) Reach.start supplies
  have hbound := low q bank reach hit
  omega

end PEqualNP.Outside.L_meta_43632_aux.Model

namespace PEqualNP.Outside.L_meta_43632

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_43632_aux.Model
open scoped BigOperators

def fullRoots : List Sig := rootsW [0, 1, 2, 3, 4, 5]

def fullWord : Sig := W 0xfeeaeee0eeeae000feeaeee0eeeae000

def posted (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276809440 * 2 ^ 32 + 4008370176)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def fixedRows (r : Row) : Row := Fin.ofNat 128 ((r.val <<< 1) &&& 126)

private theorem fixedAvailable (a : Sig) (ha : a ∈ fullRoots) :
    Available true ((rootsW [0, 1, 2, 3, 4]).map observe) (observe (rename fixedRows a)) := by
  have wordCheck : fullRoots.all (fun w => decide (rename fixedRows w = zero ∨
      rename fixedRows w ∈ rootsW [0, 1, 2, 3, 4])) = true := by decide +kernel
  rcases of_decide_eq_true (List.all_eq_true.mp wordCheck a ha) with hz | hin
  · exact .inr (.inl ⟨false, hz ▸ funext bit_zero⟩)
  · exact .inl (List.mem_map_of_mem hin)

private theorem fixedEssential : Essential fullWord fullRoots (W (xN 0)) := by
  refine ⟨12, 13, by decide +kernel, ?_⟩
  intro v hv hne
  have check : fullRoots.all (fun w => decide (w ≠ W (xN 0) → bit 12 w = bit 13 w)) = true :=
    by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp check v hv)) hne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem fullBound : Lower true fullRoots fullWord 10 := by
  have hpin : rename fixedRows (W (xN 0)) = zero := by decide +kernel
  have hconstant : ∀ a ∈ ({W (xN 0)} : Finset Sig), Constant (observe (rename fixedRows a)) := by
    intro a ha
    have ea := Finset.mem_singleton.mp ha
    rw [ea, hpin]
    exact ⟨false, funext bit_zero⟩
  have hneed : ∀ a ∈ ({W (xN 0)} : Finset Sig), Essential fullWord fullRoots a := by
    intro a ha
    exact (Finset.mem_singleton.mp ha).symm ▸ fixedEssential
  have hl := lower_slice (T := fullWord) (G := cofactorWord) (roots := fullRoots)
    (other := rootsW [0, 1, 2, 3, 4])
    (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
    (by unfold proper; decide +kernel) fixedRows (by decide +kernel) fixedAvailable {W (xN 0)} hneed hconstant 9 cofactorLower
  simpa using hl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem binaryLower (bound : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) :
    10 ≤ gs.countP (fun g => !isNot g) :=
  countFromTable (n := 6) (raw := fullRoots) (word := fullWord) (f := posted)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by unfold proper; decide +kernel) (by decide +kernel) bound gs o legal heval

end PEqualNP.Outside.L_meta_43632

namespace PEqualNP.Outside.L_meta_43632
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

def upperCircuit : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.and, [6, 8]⟩,
  ⟨.or, [0, 7]⟩,
  ⟨.or, [4, 7]⟩,
  ⟨.and, [4, 10]⟩,
  ⟨.or, [9, 12]⟩,
  ⟨.and, [6, 11]⟩,
  ⟨.or, [5, 14]⟩,
  ⟨.and, [13, 15]⟩], 16⟩

theorem upperSize : upperCircuit.size = 11 := rfl

theorem upperAllowed : Monotone2 upperCircuit := by
  intro g hg
  simp [upperCircuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
theorem upperTable : ∀ x : Fin 6 → Bool,
    upperCircuit.eval (List.ofFn x) =
      Nat.testBit (4276809440 * 2 ^ 32 + 4008370176)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_43632

namespace PEqualNP.Outside.L_meta_43632

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_43632_aux.Model

private theorem solve
    (lower : ∀ (gates : List Gate) (o : ℕ),
      (∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) →
      (∀ x : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = posted x) →
      10 ≤ gates.countP (fun g => !isNot g))
    (s : ℕ) (hs : HasCircuitSize 6 posted s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = posted x := by
  obtain ⟨⟨gates, output⟩, hlegal, hsize, htable⟩ := hs
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g, hg, hneg⟩ := hnot
    have hbinary := lower gates output hlegal htable
    have hshort : gates.countP (fun g => !isNot g) < gates.length := by
      by_contra! h
      have hcount := Nat.le_antisymm List.countP_le_length h
      have hkeep := List.countP_eq_length.mp hcount g hg
      simp [isNot, hneg] at hkeep
    refine ⟨upperCircuit, upperAllowed, ?_, upperTable⟩
    change gates.length ≤ s at hsize
    rw [upperSize]
    omega
  · refine ⟨⟨gates, output⟩, ?_, hsize, htable⟩
    intro g hg
    obtain ⟨hops, harity⟩ := hlegal g hg
    refine ⟨?_, harity⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hops ⊢
    exact hops.elim Or.inl (fun h => Or.inr (h.resolve_right (fun e => hnot ⟨g, hg, e⟩)))

end PEqualNP.Outside.L_meta_43632

theorem PEqualNP.Outside.L_meta_43632 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008370176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4008370176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_43632.solve
    (PEqualNP.Outside.L_meta_43632.binaryLower PEqualNP.Outside.L_meta_43632.fullBound)

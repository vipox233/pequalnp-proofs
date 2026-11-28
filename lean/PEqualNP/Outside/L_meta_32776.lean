import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_32776

namespace Base

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace ForestCore

open PEqualNP.CircuitLowerBounds

abbrev Sig := BitVec 512

def zero : Sig := 0

def one : Sig := BitVec.allOnes 512

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

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val

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

abbrev Row := Fin 512

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

theorem restoreInput {α : Type} [DecidableEq α] (U : Finset α) (a : α) :
    (if a ∈ U then insert a (U.erase a) else U.erase a) = U := by
  by_cases ha : a ∈ U
  · rw [if_pos ha, Finset.insert_erase ha]
  · rw [if_neg ha, Finset.erase_eq_of_notMem ha]

theorem restoreInputs {α : Type} [DecidableEq α] (U : Finset α) (a b : α) (hab : a ≠ b) :
    let s := (U.erase a).erase b
    let t := if b ∈ U then insert b s else s
    (if a ∈ U then insert a t else t) = U := by
  have member : b ∈ U.erase a ↔ b ∈ U := by
    rw [Finset.mem_erase]
    exact ⟨And.right, fun h => ⟨Ne.symm hab, h⟩⟩
  have inner : (if b ∈ U then insert b ((U.erase a).erase b) else (U.erase a).erase b) = U.erase a := by
    by_cases hb : b ∈ U
    · rw [if_pos hb, Finset.insert_erase (member.mpr hb)]
    · rw [if_neg hb, Finset.erase_eq_of_notMem (fun h => hb (member.mp h))]
  dsimp only
  rw [inner]
  exact restoreInput U a

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
      rw [kept_fin, kept_fin, er]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
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

def inputs : List Sig := [((((((((0xaaaaaaaa <<< 60) ||| 0xaaaaaaaaaaaaaaa) <<< 60) ||| 0xaaaaaaaaaaaaaaa) <<< 120) ||| ((0xaaaaaaaaaaaaaaa <<< 60) ||| 0xaaaaaaaaaaaaaaa)) <<< 240) ||| ((((0xaaaaaaaaaaaaaaa <<< 60) ||| 0xaaaaaaaaaaaaaaa) <<< 120) ||| ((0xaaaaaaaaaaaaaaa <<< 60) ||| 0xaaaaaaaaaaaaaaa))),((((((((0xcccccccc <<< 60) ||| 0xccccccccccccccc) <<< 60) ||| 0xccccccccccccccc) <<< 120) ||| ((0xccccccccccccccc <<< 60) ||| 0xccccccccccccccc)) <<< 240) ||| ((((0xccccccccccccccc <<< 60) ||| 0xccccccccccccccc) <<< 120) ||| ((0xccccccccccccccc <<< 60) ||| 0xccccccccccccccc))),((((((((0xf0f0f0f0 <<< 60) ||| 0xf0f0f0f0f0f0f0f) <<< 60) ||| 0xf0f0f0f0f0f0f0) <<< 120) ||| ((0xf0f0f0f0f0f0f0f <<< 60) ||| 0xf0f0f0f0f0f0f0)) <<< 240) ||| ((((0xf0f0f0f0f0f0f0f <<< 60) ||| 0xf0f0f0f0f0f0f0) <<< 120) ||| ((0xf0f0f0f0f0f0f0f <<< 60) ||| 0xf0f0f0f0f0f0f0))),((((((((0xff00ff00 <<< 60) ||| 0xff00ff00ff00ff0) <<< 60) ||| 0xff00ff00ff00ff) <<< 120) ||| ((0xff00ff00ff00f <<< 60) ||| 0xf00ff00ff00ff00)) <<< 240) ||| ((((0xff00ff00ff00ff0 <<< 60) ||| 0xff00ff00ff00ff) <<< 120) ||| ((0xff00ff00ff00f <<< 60) ||| 0xf00ff00ff00ff00))),((((((((0xffff0000 <<< 60) ||| 0xffff0000ffff000) <<< 60) ||| 0xffff0000ffff00) <<< 120) ||| ((0xffff0000ffff0 <<< 60) ||| 0xffff0000ffff)) <<< 240) ||| ((((0xffff0000fff <<< 60) ||| 0xf0000ffff0000ff) <<< 120) ||| ((0xff0000ffff0000f <<< 60) ||| 0xfff0000ffff0000))),((((((((0xffffffff <<< 60) ||| 0xfffffff) <<< 60) ||| 0xf00000000ffffff) <<< 120) ||| ((0xff00000000fffff <<< 60) ||| 0xfff00000000ffff)) <<< 240) ||| ((((0xffff00000000fff <<< 60) ||| 0xfffff00000000ff) <<< 120) ||| ((0xffffff00000000f <<< 60) ||| 0xfffffff00000000))),((((((((0xffffffff <<< 60) ||| 0xffffffff0000000) <<< 60) ||| 0xffffff) <<< 120) ||| ((0xffffffffff00000 <<< 60) ||| 0xffff)) <<< 240) ||| ((((0xffffffffffff000 <<< 60) ||| 0xff) <<< 120) ||| ((0xffffffffffffff0 <<< 60) ||| 0x0))),((((((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffff000000) <<< 120) ||| ((0x0 <<< 60) ||| 0xffff)) <<< 240) ||| ((((0xfffffffffffffff <<< 60) ||| 0xfffffffffffff00) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))),((((((((0xffffffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffffffffff) <<< 120) ||| ((0xfffffffffffffff <<< 60) ||| 0xfffffffffff0000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))]

def graph : Sig := ((((((((0xffffffff <<< 60) ||| 0xfffffefefffefff) <<< 60) ||| 0xefefaee00ffffff) <<< 120) ||| ((0xfffffffefefffef <<< 60) ||| 0xffefefaee00ffff)) <<< 240) ||| ((((0xfffffffffefefff <<< 60) ||| 0xefffefefaee00ff) <<< 120) ||| ((0xfffffffffffefef <<< 60) ||| 0xffefffefefaee00)))

theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl

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
      rw [kept_fin, kept_fin, er, he, Finset.erase_insert_eq_erase,
        Finset.erase_insert_of_ne (Ne.symm hab), Finset.erase_insert_eq_erase]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
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

abbrev Choice := Nat × Sig × Sig

def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2

def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))

theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h

def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d

theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

abbrev Move := Sig × Sig × Row

def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩

def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)

def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r

def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)

def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r

def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a

theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)

theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w

theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)

theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)

theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1

theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none

def vars (m : Nat) := (selected m).map Prod.snd

def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)

def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]

def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)

def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1

def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1

def cube6 : Nat → Nat
  | 0 => ((((((0x10000000 <<< 60) ||| 0x1000000) <<< 120) ||| ((0x100000 <<< 60) ||| 0x10000)) <<< 240) ||| ((((0x1000 <<< 60) ||| 0x100) <<< 120) ||| ((0x10 <<< 60) ||| 0x1)))
  | 1 => ((((((0x1000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x10000 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x100 <<< 60) ||| 0x0) <<< 60) ||| 0x1))
  | 2 => ((((((0x100000 <<< 60) ||| 0x10000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x10) <<< 60) ||| 0x1))
  | 3 => ((((((0x10000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1))
  | 4 => ((((0x1000 <<< 60) ||| 0x100) <<< 120) ||| ((0x10 <<< 60) ||| 0x1))
  | 5 => ((((0x100 <<< 60) ||| 0x0) <<< 60) ||| 0x1)
  | 6 => 0x10000000000000001
  | _ => 0x1

def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)

def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none

def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one

theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat

def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))

def chartGoal (m : Nat) : Sig := graphGoal m

def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)

def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)

theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0

theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

abbrev BoundPool := Sig × Nat × Nat × List Sig

def BoundPool.domain (c : BoundPool) : Sig := c.1

def BoundPool.bound (c : BoundPool) : Nat := c.2.1

def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1

def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)

theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 663

abbrev Signals := Bits × Bits

abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn

theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def pairSig (r s : Fin 663 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)

def properPairs (T : Sig) (r s : Fin 663 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false

theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 663 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩

def faithful (r s : Fin 663 → Row) (x : Decor) := x.2 = pairSig r s x.1

def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]

theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)

theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp

theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)

def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])

theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 663) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])

theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel

theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel

theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel

theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel

theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel

theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel

theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel

theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel

theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel

theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r

theorem asRow_bit (cols : Nat → Bits) (i : Fin 663) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]

def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))

theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction

theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)

theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 663) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]

theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 663) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide)]

abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)

def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a

def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl

theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))

theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921

def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool

def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)

def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _

theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)

theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))

def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 663 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst

theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 663) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 663 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true

def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]

theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]

def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))

def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]

theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)

theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p

theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)

def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))

def Forest.mask (g : Forest) : Nat := g.1

def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)

def Forest.cap (g : Forest) : Nat := g.2.1

def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1

def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1

def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1

def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1

def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws

theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask

def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v

theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 663) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i

theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 663) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp

def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws

theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)

def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16

def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth

def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)

def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst

def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n

theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true

def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 663) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws

theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2

def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old

theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h

theorem baseKnown : Known true [] := by simp [Known]

def g42Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 180) ||| ((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb)) <<< 360) ||| ((((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 180) ||| ((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb))), ((((((((0x7 <<< 60) ||| 0xf000f000f000) <<< 60) ||| 0xf000f000f000f00) <<< 180) ||| ((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000)) <<< 360) ||| ((((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f) <<< 180) ||| ((((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00) <<< 60) ||| 0xf000f000f000f0)))),
    (0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd) <<< 180) ||| ((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd)) <<< 360) ||| ((((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd) <<< 180) ||| ((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd))), ((((((((0xf000f000f000f <<< 60) ||| 0xf000f000f000) <<< 60) ||| 0xf000f000f000f00) <<< 180) ||| ((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000)) <<< 300) ||| ((((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f) <<< 120) ||| ((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00)))),
    (0x0, 0x0),
    (((((((((0x6 <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 180) ||| ((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee)) <<< 360) ||| ((((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 180) ||| ((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee))), ((((((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000) <<< 180) ||| ((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f)) <<< 300) ||| ((((((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00) <<< 60) ||| 0xf000f000f000f0) <<< 120) ||| ((0xf000f000f000f <<< 60) ||| 0xf000f000f000)))),
    (0x0, 0x0)]

def g42C : List ColumnInfo := []

def g42D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0

def g42L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g42D3)
  | _ => emptyPacking

def g42I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g42 : Forest := ⟨42, 3, fun i => (g42Y[i]?).getD (0,0), g42C, [[]], g42L, g42I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g42P3n0 : block g42 3 0 1 = true := by decide +kernel

theorem g42B3 : block g42 3 0 1 = true := g42P3n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g42T : checkedTables g42 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g42 0 0 0 = true)
  · exact (rfl : block g42 1 0 0 = true)
  · exact (rfl : block g42 2 0 0 = true)
  · exact g42B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g42G : graphValid g42 (boundsBefore []) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low42 : Lower true (varsX 42) (graphGoal 42) 4 := lower_forest (g:=g42) (i:=0) (hints:=1052720) (before_sound [] baseKnown) g42G g42T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K42 := extendKnown [] 4 [(42,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V42 : Known true K42 := extend_ok (m:=42) baseKnown low42 (by decide +kernel)

def g84Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 180) ||| ((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb)) <<< 360) ||| ((((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 180) ||| ((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb))), ((((((((0x7 <<< 60) ||| 0xf000f000f000) <<< 60) ||| 0xf000f000f000f00) <<< 180) ||| ((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000)) <<< 360) ||| ((((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f) <<< 180) ||| ((((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00) <<< 60) ||| 0xf000f000f000f0)))),
    (0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd) <<< 180) ||| ((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd)) <<< 360) ||| ((((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd) <<< 180) ||| ((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd))), ((((((((0xf000f000f000f <<< 60) ||| 0xf000f000f000) <<< 60) ||| 0xf000f000f000f00) <<< 180) ||| ((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000)) <<< 300) ||| ((((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f) <<< 120) ||| ((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00)))),
    (0x0, 0x0),
    (((((((((0x6 <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 180) ||| ((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee)) <<< 360) ||| ((((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 180) ||| ((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee))), ((((((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000) <<< 180) ||| ((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f)) <<< 300) ||| ((((((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00) <<< 60) ||| 0xf000f000f000f0) <<< 120) ||| ((0xf000f000f000f <<< 60) ||| 0xf000f000f000))))]

def g84C : List ColumnInfo := []

def g84D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0

def g84L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g84D3)
  | _ => emptyPacking

def g84I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g84 : Forest := ⟨84, 3, fun i => (g84Y[i]?).getD (0,0), g84C, [[]], g84L, g84I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g84P3n0 : block g84 3 0 1 = true := by decide +kernel

theorem g84B3 : block g84 3 0 1 = true := g84P3n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g84T : checkedTables g84 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g84 0 0 0 = true)
  · exact (rfl : block g84 1 0 0 = true)
  · exact (rfl : block g84 2 0 0 = true)
  · exact g84B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g84G : graphValid g84 (boundsBefore K42) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low84 : Lower true (varsX 84) (graphGoal 84) 4 := lower_forest (g:=g84) (i:=0) (hints:=33686528) (before_sound K42 V42) g84G g84T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K84 := extendKnown K42 4 [(84,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V84 : Known true K84 := extend_ok (m:=84) V42 low84 (by decide +kernel)

def g98Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 180) ||| ((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb)) <<< 360) ||| ((((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 180) ||| ((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb))), ((((((((0x7 <<< 60) ||| 0xf000f000f000) <<< 60) ||| 0xf000f000f000f00) <<< 180) ||| ((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000)) <<< 360) ||| ((((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f) <<< 180) ||| ((((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00) <<< 60) ||| 0xf000f000f000f0)))),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd) <<< 180) ||| ((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd)) <<< 360) ||| ((((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd) <<< 180) ||| ((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd))), ((((((((0xf000f000f000f <<< 60) ||| 0xf000f000f000) <<< 60) ||| 0xf000f000f000f00) <<< 180) ||| ((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000)) <<< 300) ||| ((((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f) <<< 120) ||| ((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00)))),
    (((((((((0x6 <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 180) ||| ((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee)) <<< 360) ||| ((((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 180) ||| ((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee))), ((((((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000) <<< 180) ||| ((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f)) <<< 300) ||| ((((((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00) <<< 60) ||| 0xf000f000f000f0) <<< 120) ||| ((0xf000f000f000f <<< 60) ||| 0xf000f000f000))))]

def g98C : List ColumnInfo := []

def g98D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0

def g98L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g98D3)
  | _ => emptyPacking

def g98I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g98 : Forest := ⟨98, 3, fun i => (g98Y[i]?).getD (0,0), g98C, [[]], g98L, g98I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g98P3n0 : block g98 3 0 1 = true := by decide +kernel

theorem g98B3 : block g98 3 0 1 = true := g98P3n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g98T : checkedTables g98 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g98 0 0 0 = true)
  · exact (rfl : block g98 1 0 0 = true)
  · exact (rfl : block g98 2 0 0 = true)
  · exact g98B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g98G : graphValid g98 (boundsBefore K84) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low98 : Lower true (varsX 98) (graphGoal 98) 4 := lower_forest (g:=g98) (i:=0) (hints:=17825872) (before_sound K84 V84) g98G g98T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K98 := extendKnown K84 4 [(98,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V98 : Known true K98 := extend_ok (m:=98) V84 low98 (by decide +kernel)

def g100Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 180) ||| ((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb)) <<< 360) ||| ((((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 180) ||| ((((0xbbbbbbbbbbbbbbb <<< 60) ||| 0xbbbbbbbbbbbbbbb) <<< 60) ||| 0xbbbbbbbbbbbbbbb))), ((((((((0x7 <<< 60) ||| 0xf000f000f000) <<< 60) ||| 0xf000f000f000f00) <<< 180) ||| ((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000)) <<< 360) ||| ((((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f) <<< 180) ||| ((((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00) <<< 60) ||| 0xf000f000f000f0)))),
    (0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd) <<< 180) ||| ((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd)) <<< 360) ||| ((((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd) <<< 180) ||| ((((0xddddddddddddddd <<< 60) ||| 0xddddddddddddddd) <<< 60) ||| 0xddddddddddddddd))), ((((((((0xf000f000f000f <<< 60) ||| 0xf000f000f000) <<< 60) ||| 0xf000f000f000f00) <<< 180) ||| ((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000)) <<< 300) ||| ((((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f) <<< 120) ||| ((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00)))),
    (((((((((0x6 <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 180) ||| ((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee)) <<< 360) ||| ((((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 180) ||| ((((0xeeeeeeeeeeeeeee <<< 60) ||| 0xeeeeeeeeeeeeeee) <<< 60) ||| 0xeeeeeeeeeeeeeee))), ((((((((0xf000f000f000f0 <<< 60) ||| 0xf000f000f000f) <<< 60) ||| 0xf000f000f000) <<< 180) ||| ((((0xf000f000f000f00 <<< 60) ||| 0xf000f000f000f0) <<< 60) ||| 0xf000f000f000f)) <<< 300) ||| ((((((0xf000f000f000 <<< 60) ||| 0xf000f000f000f00) <<< 60) ||| 0xf000f000f000f0) <<< 120) ||| ((0xf000f000f000f <<< 60) ||| 0xf000f000f000))))]

def g100C : List ColumnInfo := []

def g100D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0

def g100L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g100D3)
  | _ => emptyPacking

def g100I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g100 : Forest := ⟨100, 3, fun i => (g100Y[i]?).getD (0,0), g100C, [[]], g100L, g100I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g100P3n0 : block g100 3 0 1 = true := by decide +kernel

theorem g100B3 : block g100 3 0 1 = true := g100P3n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g100T : checkedTables g100 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g100 0 0 0 = true)
  · exact (rfl : block g100 1 0 0 = true)
  · exact (rfl : block g100 2 0 0 = true)
  · exact g100B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g100G : graphValid g100 (boundsBefore K98) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low100 : Lower true (varsX 100) (graphGoal 100) 4 := lower_forest (g:=g100) (i:=0) (hints:=35652864) (before_sound K98 V98) g100G g100T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K100 := extendKnown K98 4 [(100,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V100 : Known true K100 := extend_ok (m:=100) V98 low100 (by decide +kernel)

def g46Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x2 <<< 60) ||| 0xf57abd5eaf57abd) <<< 60) ||| 0x5eaf57abd5eaf57) <<< 180) ||| ((((0xabd5eaf57abd5ea <<< 60) ||| 0xf57abd5eaf57abd) <<< 60) ||| 0x5eaf57abd5eaf57)) <<< 360) ||| ((((((0xabd5eaf57abd5ea <<< 60) ||| 0xf57abd5eaf57abd) <<< 60) ||| 0x5eaf57abd5eaf57) <<< 180) ||| ((((0xabd5eaf57abd5ea <<< 60) ||| 0xf57abd5eaf57abd) <<< 60) ||| 0x5eaf57abd5eaf57))), ((((((((0x7 <<< 60) ||| 0xe00ff8000000007) <<< 60) ||| 0xfc01ff000000000) <<< 180) ||| ((((0xff803fe00000000 <<< 60) ||| 0x1ff007fc0000000) <<< 60) ||| 0x3fe00ff8000000)) <<< 360) ||| ((((((0x7fc01ff000000 <<< 60) ||| 0xff803fe00000) <<< 60) ||| 0x1ff007fc0000) <<< 180) ||| ((((0x3fe00ff8000 <<< 60) ||| 0x7fc01ff000) <<< 60) ||| 0xff803fe00)))),
    (((((((((0x3 <<< 60) ||| 0x59acd66b359acd6) <<< 60) ||| 0x6b359acd66b359a) <<< 180) ||| ((((0xcd66b359acd66b3 <<< 60) ||| 0x59acd66b359acd6) <<< 60) ||| 0x6b359acd66b359a)) <<< 360) ||| ((((((0xcd66b359acd66b3 <<< 60) ||| 0x59acd66b359acd6) <<< 60) ||| 0x6b359acd66b359a) <<< 180) ||| ((((0xcd66b359acd66b3 <<< 60) ||| 0x59acd66b359acd6) <<< 60) ||| 0x6b359acd66b359a))), ((((((((0x7 <<< 60) ||| 0xfff0000001ff007) <<< 60) ||| 0xfffe0000003fe00) <<< 180) ||| ((((0xffffc0000007fc0 <<< 60) ||| 0x1ffff8000000ff8) <<< 60) ||| 0x3ffff0000001ff)) <<< 360) ||| ((((((0x7fffe0000003f <<< 60) ||| 0xe00ffffc0000007) <<< 60) ||| 0xfc01ffff8000000) <<< 180) ||| ((((0xff803ffff000000 <<< 60) ||| 0x1ff007fffe00000) <<< 60) ||| 0x3fe00ffffc0000)))),
    (((((((((0x4 <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3) <<< 180) ||| ((((0xf1f8fc7e3f1f8fc <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3)) <<< 360) ||| ((((((0xf1f8fc7e3f1f8fc <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3) <<< 180) ||| ((((0xf1f8fc7e3f1f8fc <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3))), ((((((((0x1ffff8 <<< 60) ||| 0x3ffff) <<< 60) ||| 0x7fff) <<< 180) ||| ((((0xe00000000000fff <<< 60) ||| 0xfc00000000001ff) <<< 60) ||| 0xff800000000003f)) <<< 300) ||| ((((((0xfff000000000007 <<< 60) ||| 0xfffe00000000000) <<< 60) ||| 0xffffc0000000000) <<< 120) ||| ((0x1ffff8000000000 <<< 60) ||| 0x3ffff000000000)))),
    (0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc) <<< 180) ||| ((((0xfe7f3f9fcfe7f3f <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc)) <<< 360) ||| ((((((0xfe7f3f9fcfe7f3f <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc) <<< 180) ||| ((((0xfe7f3f9fcfe7f3f <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc))), ((((((((0x3fe00000 <<< 60) ||| 0x7fc0000) <<< 60) ||| 0xff8000) <<< 180) ||| ((((0x1ff000 <<< 60) ||| 0x3fe00) <<< 60) ||| 0x7fc0)) <<< 300) ||| ((((((0xff8 <<< 60) ||| 0x1ff) <<< 60) ||| 0x3f) <<< 120) ||| ((0xe00000000000007 <<< 60) ||| 0xfc0000000000000)))),
    (0x0, 0x0)]

def g46C : List ColumnInfo := [(4,0,42,0,4)]

def g46D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0

def g46L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g46D4)
  | _ => emptyPacking

def g46I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g46 : Forest := ⟨46, 4, fun i => (g46Y[i]?).getD (0,0), g46C, [[]], g46L, g46I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46P4n0 : block g46 4 0 1 = true := by decide +kernel

theorem g46B4 : block g46 4 0 1 = true := g46P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46T : checkedTables g46 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g46 0 0 0 = true)
  · exact (rfl : block g46 1 0 0 = true)
  · exact (rfl : block g46 2 0 0 = true)
  · exact (rfl : block g46 3 0 0 = true)
  · exact g46B4

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46G : graphValid g46 (boundsBefore K100) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low46 : Lower true (varsX 46) (graphGoal 46) 5 := lower_forest (g:=g46) (i:=0) (hints:=1054000) (before_sound K100 V100) g46G g46T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K46 := extendKnown K100 5 [(46,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V46 : Known true K46 := extend_ok (m:=46) V100 low46 (by decide +kernel)

def g54Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0x6b6b6b6b6b6b6b6) <<< 60) ||| 0xb6b6b6b6b6b6b6b) <<< 180) ||| ((((0x6b6b6b6b6b6b6b6 <<< 60) ||| 0xb6b6b6b6b6b6b6b) <<< 60) ||| 0x6b6b6b6b6b6b6b6)) <<< 360) ||| ((((((0xb6b6b6b6b6b6b6b <<< 60) ||| 0x6b6b6b6b6b6b6b6) <<< 60) ||| 0xb6b6b6b6b6b6b6b) <<< 180) ||| ((((0x6b6b6b6b6b6b6b6 <<< 60) ||| 0xb6b6b6b6b6b6b6b) <<< 60) ||| 0x6b6b6b6b6b6b6b6))), ((((((((0xff000000ff00ff <<< 60) ||| 0xff000000ff00f) <<< 60) ||| 0xf00ff000000ff00) <<< 180) ||| ((((0xff00ff000000ff0 <<< 60) ||| 0xff00ff000000ff) <<< 60) ||| 0xff00ff000000f)) <<< 300) ||| ((((((0xf00ff00ff000000 <<< 60) ||| 0xff00ff00ff00000) <<< 60) ||| 0xff00ff00ff0000) <<< 120) ||| ((0xff00ff00ff000 <<< 60) ||| 0xff00ff00ff00)))),
    (((((((((0x5 <<< 60) ||| 0xbdbdbdbdbdbdbdb) <<< 60) ||| 0xdbdbdbdbdbdbdbd) <<< 180) ||| ((((0xbdbdbdbdbdbdbdb <<< 60) ||| 0xdbdbdbdbdbdbdbd) <<< 60) ||| 0xbdbdbdbdbdbdbdb)) <<< 360) ||| ((((((0xdbdbdbdbdbdbdbd <<< 60) ||| 0xbdbdbdbdbdbdbdb) <<< 60) ||| 0xdbdbdbdbdbdbdbd) <<< 180) ||| ((((0xbdbdbdbdbdbdbdb <<< 60) ||| 0xdbdbdbdbdbdbdbd) <<< 60) ||| 0xbdbdbdbdbdbdbdb))), ((((((((0x7 <<< 60) ||| 0xf000000000000ff) <<< 60) ||| 0xff000000000000f) <<< 180) ||| ((((0xfff000000000000 <<< 60) ||| 0xffff00000000000) <<< 60) ||| 0xffff0000000000)) <<< 360) ||| ((((((0xffff000000000 <<< 60) ||| 0xffff00000000) <<< 60) ||| 0xffff0000000) <<< 180) ||| ((((0xffff000000 <<< 60) ||| 0xffff00000) <<< 60) ||| 0xffff0000)))),
    (0x0, 0x0),
    (((((((((0x6 <<< 60) ||| 0x3e3e3e3e3e3e3e3) <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 180) ||| ((((0x3e3e3e3e3e3e3e3 <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 60) ||| 0x3e3e3e3e3e3e3e3)) <<< 360) ||| ((((((0xe3e3e3e3e3e3e3e <<< 60) ||| 0x3e3e3e3e3e3e3e3) <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 180) ||| ((((0x3e3e3e3e3e3e3e3 <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 60) ||| 0x3e3e3e3e3e3e3e3))), ((((((((0xff00ffff00 <<< 60) ||| 0xff00ffff0) <<< 60) ||| 0xff00ffff) <<< 180) ||| ((((0xff00fff <<< 60) ||| 0xf00000000ff00ff) <<< 60) ||| 0xff00000000ff00f)) <<< 300) ||| ((((((0xfff00000000ff00 <<< 60) ||| 0xffff00000000ff0) <<< 60) ||| 0xffff00000000ff) <<< 120) ||| ((0xffff00000000f <<< 60) ||| 0xf00ffff00000000)))),
    (((((((((0x7 <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc)) <<< 360) ||| ((((((0xfcfcfcfcfcfcfcf <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc))), ((((((((0xffff000000 <<< 60) ||| 0xffff00000) <<< 60) ||| 0xffff0000) <<< 180) ||| ((((0xffff000 <<< 60) ||| 0xffff00) <<< 60) ||| 0xffff0)) <<< 300) ||| ((((((0xffff <<< 60) ||| 0xfff) <<< 60) ||| 0xf000000000000ff) <<< 120) ||| ((0xff000000000000f <<< 60) ||| 0xfff000000000000)))),
    (0x0, 0x0)]

def g54C : List ColumnInfo := []

def g54D3 (j : Nat) : Nat := if j = 0 then 0xf else 0

def g54L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g54D3)
  | _ => emptyPacking

def g54I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g54 : Forest := ⟨54, 3, fun i => (g54Y[i]?).getD (0,0), g54C, [[]], g54L, g54I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54P3n0 : block g54 3 0 1 = true := by decide +kernel

theorem g54B3 : block g54 3 0 1 = true := g54P3n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54T : checkedTables g54 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g54 0 0 0 = true)
  · exact (rfl : block g54 1 0 0 = true)
  · exact (rfl : block g54 2 0 0 = true)
  · exact g54B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54G : graphValid g54 (boundsBefore K46) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low54 : Lower true (varsX 54) (graphGoal 54) 4 := lower_forest (g:=g54) (i:=0) (hints:=1180752) (before_sound K46 V46) g54G g54T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K54 := extendKnown K46 4 [(54,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V54 : Known true K54 := extend_ok (m:=54) V46 low54 (by decide +kernel)

def g60Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0x7b7b7b7b7b7b7b7) <<< 60) ||| 0xb7b7b7b7b7b7b7b) <<< 180) ||| ((((0x7b7b7b7b7b7b7b7 <<< 60) ||| 0xb7b7b7b7b7b7b7b) <<< 60) ||| 0x7b7b7b7b7b7b7b7)) <<< 360) ||| ((((((0xb7b7b7b7b7b7b7b <<< 60) ||| 0x7b7b7b7b7b7b7b7) <<< 60) ||| 0xb7b7b7b7b7b7b7b) <<< 180) ||| ((((0x7b7b7b7b7b7b7b7 <<< 60) ||| 0xb7b7b7b7b7b7b7b) <<< 60) ||| 0x7b7b7b7b7b7b7b7))), ((((((((0xff0000000000ff <<< 60) ||| 0xff0000000000f) <<< 60) ||| 0xf00ff0000000000) <<< 180) ||| ((((0xff00ff000000000 <<< 60) ||| 0xff00ff00000000) <<< 60) ||| 0xff00ff0000000)) <<< 300) ||| ((((((0xff00ff000000 <<< 60) ||| 0xff00ff00000) <<< 60) ||| 0xff00ff0000) <<< 120) ||| ((0xff00ff000 <<< 60) ||| 0xff00ff00)))),
    (((((((((0x5 <<< 60) ||| 0xadadadadadadada) <<< 60) ||| 0xdadadadadadadad) <<< 180) ||| ((((0xadadadadadadada <<< 60) ||| 0xdadadadadadadad) <<< 60) ||| 0xadadadadadadada)) <<< 360) ||| ((((((0xdadadadadadadad <<< 60) ||| 0xadadadadadadada) <<< 60) ||| 0xdadadadadadadad) <<< 180) ||| ((((0xadadadadadadada <<< 60) ||| 0xdadadadadadadad) <<< 60) ||| 0xadadadadadadada))), ((((((((0x7 <<< 60) ||| 0xf00000000ff00ff) <<< 60) ||| 0xff00000000ff00f) <<< 180) ||| ((((0xfff00000000ff00 <<< 60) ||| 0xffff00000000ff0) <<< 60) ||| 0xffff00000000ff)) <<< 360) ||| ((((((0xffff00000000f <<< 60) ||| 0xf00ffff00000000) <<< 60) ||| 0xff00ffff0000000) <<< 180) ||| ((((0xff00ffff000000 <<< 60) ||| 0xff00ffff00000) <<< 60) ||| 0xff00ffff0000)))),
    (((((((((0x6 <<< 60) ||| 0x3e3e3e3e3e3e3e3) <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 180) ||| ((((0x3e3e3e3e3e3e3e3 <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 60) ||| 0x3e3e3e3e3e3e3e3)) <<< 360) ||| ((((((0xe3e3e3e3e3e3e3e <<< 60) ||| 0x3e3e3e3e3e3e3e3) <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 180) ||| ((((0x3e3e3e3e3e3e3e3 <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 60) ||| 0x3e3e3e3e3e3e3e3))), ((((((((0xff00ffff00 <<< 60) ||| 0xff00ffff0) <<< 60) ||| 0xff00ffff) <<< 180) ||| ((((0xff00fff <<< 60) ||| 0xf00000000ff00ff) <<< 60) ||| 0xff00000000ff00f)) <<< 300) ||| ((((((0xfff00000000ff00 <<< 60) ||| 0xffff00000000ff0) <<< 60) ||| 0xffff00000000ff) <<< 120) ||| ((0xffff00000000f <<< 60) ||| 0xf00ffff00000000)))),
    (((((((((0x7 <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc)) <<< 360) ||| ((((((0xfcfcfcfcfcfcfcf <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc))), ((((((((0xffff000000 <<< 60) ||| 0xffff00000) <<< 60) ||| 0xffff0000) <<< 180) ||| ((((0xffff000 <<< 60) ||| 0xffff00) <<< 60) ||| 0xffff0)) <<< 300) ||| ((((((0xffff <<< 60) ||| 0xfff) <<< 60) ||| 0xf000000000000ff) <<< 120) ||| ((0xff000000000000f <<< 60) ||| 0xfff000000000000)))),
    (0x0, 0x0)]

def g60C : List ColumnInfo := []

def g60D3 (j : Nat) : Nat := if j = 0 then 0xf else 0

def g60L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g60D3)
  | _ => emptyPacking

def g60I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g60 : Forest := ⟨60, 3, fun i => (g60Y[i]?).getD (0,0), g60C, [[]], g60L, g60I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g60P3n0 : block g60 3 0 1 = true := by decide +kernel

theorem g60B3 : block g60 3 0 1 = true := g60P3n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g60T : checkedTables g60 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g60 0 0 0 = true)
  · exact (rfl : block g60 1 0 0 = true)
  · exact (rfl : block g60 2 0 0 = true)
  · exact g60B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g60G : graphValid g60 (boundsBefore K54) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low60 : Lower true (varsX 60) (graphGoal 60) 4 := lower_forest (g:=g60) (i:=0) (hints:=2249728) (before_sound K54 V54) g60G g60T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K60 := extendKnown K54 4 [(60,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V60 : Known true K60 := extend_ok (m:=60) V54 low60 (by decide +kernel)

def g78Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0x7b7b7b7b7b7b7b7) <<< 60) ||| 0xb7b7b7b7b7b7b7b) <<< 180) ||| ((((0x7b7b7b7b7b7b7b7 <<< 60) ||| 0xb7b7b7b7b7b7b7b) <<< 60) ||| 0x7b7b7b7b7b7b7b7)) <<< 360) ||| ((((((0xb7b7b7b7b7b7b7b <<< 60) ||| 0x7b7b7b7b7b7b7b7) <<< 60) ||| 0xb7b7b7b7b7b7b7b) <<< 180) ||| ((((0x7b7b7b7b7b7b7b7 <<< 60) ||| 0xb7b7b7b7b7b7b7b) <<< 60) ||| 0x7b7b7b7b7b7b7b7))), ((((((((0xff0000000000ff <<< 60) ||| 0xff0000000000f) <<< 60) ||| 0xf00ff0000000000) <<< 180) ||| ((((0xff00ff000000000 <<< 60) ||| 0xff00ff00000000) <<< 60) ||| 0xff00ff0000000)) <<< 300) ||| ((((((0xff00ff000000 <<< 60) ||| 0xff00ff00000) <<< 60) ||| 0xff00ff0000) <<< 120) ||| ((0xff00ff000 <<< 60) ||| 0xff00ff00)))),
    (((((((((0x5 <<< 60) ||| 0xadadadadadadada) <<< 60) ||| 0xdadadadadadadad) <<< 180) ||| ((((0xadadadadadadada <<< 60) ||| 0xdadadadadadadad) <<< 60) ||| 0xadadadadadadada)) <<< 360) ||| ((((((0xdadadadadadadad <<< 60) ||| 0xadadadadadadada) <<< 60) ||| 0xdadadadadadadad) <<< 180) ||| ((((0xadadadadadadada <<< 60) ||| 0xdadadadadadadad) <<< 60) ||| 0xadadadadadadada))), ((((((((0x7 <<< 60) ||| 0xf00000000ff00ff) <<< 60) ||| 0xff00000000ff00f) <<< 180) ||| ((((0xfff00000000ff00 <<< 60) ||| 0xffff00000000ff0) <<< 60) ||| 0xffff00000000ff)) <<< 360) ||| ((((((0xffff00000000f <<< 60) ||| 0xf00ffff00000000) <<< 60) ||| 0xff00ffff0000000) <<< 180) ||| ((((0xff00ffff000000 <<< 60) ||| 0xff00ffff00000) <<< 60) ||| 0xff00ffff0000)))),
    (((((((((0x6 <<< 60) ||| 0x3e3e3e3e3e3e3e3) <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 180) ||| ((((0x3e3e3e3e3e3e3e3 <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 60) ||| 0x3e3e3e3e3e3e3e3)) <<< 360) ||| ((((((0xe3e3e3e3e3e3e3e <<< 60) ||| 0x3e3e3e3e3e3e3e3) <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 180) ||| ((((0x3e3e3e3e3e3e3e3 <<< 60) ||| 0xe3e3e3e3e3e3e3e) <<< 60) ||| 0x3e3e3e3e3e3e3e3))), ((((((((0xff00ffff00 <<< 60) ||| 0xff00ffff0) <<< 60) ||| 0xff00ffff) <<< 180) ||| ((((0xff00fff <<< 60) ||| 0xf00000000ff00ff) <<< 60) ||| 0xff00000000ff00f)) <<< 300) ||| ((((((0xfff00000000ff00 <<< 60) ||| 0xffff00000000ff0) <<< 60) ||| 0xffff00000000ff) <<< 120) ||| ((0xffff00000000f <<< 60) ||| 0xf00ffff00000000)))),
    (0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc)) <<< 360) ||| ((((((0xfcfcfcfcfcfcfcf <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc))), ((((((((0xffff000000 <<< 60) ||| 0xffff00000) <<< 60) ||| 0xffff0000) <<< 180) ||| ((((0xffff000 <<< 60) ||| 0xffff00) <<< 60) ||| 0xffff0)) <<< 300) ||| ((((((0xffff <<< 60) ||| 0xfff) <<< 60) ||| 0xf000000000000ff) <<< 120) ||| ((0xff000000000000f <<< 60) ||| 0xfff000000000000))))]

def g78C : List ColumnInfo := []

def g78D3 (j : Nat) : Nat := if j = 0 then 0xf else 0

def g78L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g78D3)
  | _ => emptyPacking

def g78I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g78 : Forest := ⟨78, 3, fun i => (g78Y[i]?).getD (0,0), g78C, [[]], g78L, g78I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78P3n0 : block g78 3 0 1 = true := by decide +kernel

theorem g78B3 : block g78 3 0 1 = true := g78P3n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78T : checkedTables g78 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g78 0 0 0 = true)
  · exact (rfl : block g78 1 0 0 = true)
  · exact (rfl : block g78 2 0 0 = true)
  · exact g78B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78G : graphValid g78 (boundsBefore K60) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low78 : Lower true (varsX 78) (graphGoal 78) 4 := lower_forest (g:=g78) (i:=0) (hints:=16782896) (before_sound K60 V60) g78G g78T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K78 := extendKnown K60 4 [(78,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V78 : Known true K78 := extend_ok (m:=78) V60 low78 (by decide +kernel)

def g86Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x2 <<< 60) ||| 0xd56ab55aad56ab5) <<< 60) ||| 0x5aad56ab55aad56) <<< 180) ||| ((((0xab55aad56ab55aa <<< 60) ||| 0xd56ab55aad56ab5) <<< 60) ||| 0x5aad56ab55aad56)) <<< 360) ||| ((((((0xab55aad56ab55aa <<< 60) ||| 0xd56ab55aad56ab5) <<< 60) ||| 0x5aad56ab55aad56) <<< 180) ||| ((((0xab55aad56ab55aa <<< 60) ||| 0xd56ab55aad56ab5) <<< 60) ||| 0x5aad56ab55aad56))), ((((((((0x7 <<< 60) ||| 0xe00ff80001ff007) <<< 60) ||| 0xfc01ff00003fe00) <<< 180) ||| ((((0xff803fe00007fc0 <<< 60) ||| 0x1ff007fc0000ff8) <<< 60) ||| 0x3fe00ff80001ff)) <<< 360) ||| ((((((0x7fc01ff00003f <<< 60) ||| 0xe00ff803fe00007) <<< 60) ||| 0xfc01ff007fc0000) <<< 180) ||| ((((0xff803fe00ff8000 <<< 60) ||| 0x1ff007fc01ff000) <<< 60) ||| 0x3fe00ff803fe00)))),
    (((((((((0x3 <<< 60) ||| 0x79bcde6f379bcde) <<< 60) ||| 0x6f379bcde6f379b) <<< 180) ||| ((((0xcde6f379bcde6f3 <<< 60) ||| 0x79bcde6f379bcde) <<< 60) ||| 0x6f379bcde6f379b)) <<< 360) ||| ((((((0xcde6f379bcde6f3 <<< 60) ||| 0x79bcde6f379bcde) <<< 60) ||| 0x6f379bcde6f379b) <<< 180) ||| ((((0xcde6f379bcde6f3 <<< 60) ||| 0x79bcde6f379bcde) <<< 60) ||| 0x6f379bcde6f379b))), ((((((((0x7 <<< 60) ||| 0xfff000000000007) <<< 60) ||| 0xfffe00000000000) <<< 180) ||| ((((0xffffc0000000000 <<< 60) ||| 0x1ffff8000000000) <<< 60) ||| 0x3ffff000000000)) <<< 360) ||| ((((((0x7fffe00000000 <<< 60) ||| 0xffffc0000000) <<< 60) ||| 0x1ffff8000000) <<< 180) ||| ((((0x3ffff000000 <<< 60) ||| 0x7fffe00000) <<< 60) ||| 0xffffc0000)))),
    (0x0, 0x0),
    (((((((((0x4 <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3) <<< 180) ||| ((((0xf1f8fc7e3f1f8fc <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3)) <<< 360) ||| ((((((0xf1f8fc7e3f1f8fc <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3) <<< 180) ||| ((((0xf1f8fc7e3f1f8fc <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3))), ((((((((0x1ffff8 <<< 60) ||| 0x3ffff) <<< 60) ||| 0x7fff) <<< 180) ||| ((((0xe00000000000fff <<< 60) ||| 0xfc00000000001ff) <<< 60) ||| 0xff800000000003f)) <<< 300) ||| ((((((0xfff000000000007 <<< 60) ||| 0xfffe00000000000) <<< 60) ||| 0xffffc0000000000) <<< 120) ||| ((0x1ffff8000000000 <<< 60) ||| 0x3ffff000000000)))),
    (0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc) <<< 180) ||| ((((0xfe7f3f9fcfe7f3f <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc)) <<< 360) ||| ((((((0xfe7f3f9fcfe7f3f <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc) <<< 180) ||| ((((0xfe7f3f9fcfe7f3f <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc))), ((((((((0x3fe00000 <<< 60) ||| 0x7fc0000) <<< 60) ||| 0xff8000) <<< 180) ||| ((((0x1ff000 <<< 60) ||| 0x3fe00) <<< 60) ||| 0x7fc0)) <<< 300) ||| ((((((0xff8 <<< 60) ||| 0x1ff) <<< 60) ||| 0x3f) <<< 120) ||| ((0xe00000000000007 <<< 60) ||| 0xfc0000000000000))))]

def g86C : List ColumnInfo := [(2,0,84,0,4)]

def g86D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0

def g86L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g86D4)
  | _ => emptyPacking

def g86I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g86 : Forest := ⟨86, 4, fun i => (g86Y[i]?).getD (0,0), g86C, [[]], g86L, g86I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86P4n0 : block g86 4 0 1 = true := by decide +kernel

theorem g86B4 : block g86 4 0 1 = true := g86P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86T : checkedTables g86 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g86 0 0 0 = true)
  · exact (rfl : block g86 1 0 0 = true)
  · exact (rfl : block g86 2 0 0 = true)
  · exact (rfl : block g86 3 0 0 = true)
  · exact g86B4

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86G : graphValid g86 (boundsBefore K78) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (graphGoal 86) 5 := lower_forest (g:=g86) (i:=0) (hints:=16909408) (before_sound K78 V78) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K86 := extendKnown K78 5 [(86,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V78 low86 (by decide +kernel)

def g90Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x2 <<< 60) ||| 0xfafafafafafafaf) <<< 60) ||| 0xafafafafafafafa) <<< 180) ||| ((((0xfafafafafafafaf <<< 60) ||| 0xafafafafafafafa) <<< 60) ||| 0xfafafafafafafaf)) <<< 360) ||| ((((((0xafafafafafafafa <<< 60) ||| 0xfafafafafafafaf) <<< 60) ||| 0xafafafafafafafa) <<< 180) ||| ((((0xfafafafafafafaf <<< 60) ||| 0xafafafafafafafa) <<< 60) ||| 0xfafafafafafafaf))), ((((((((0xff00000000ff00 <<< 60) ||| 0xff00000000ff0) <<< 60) ||| 0xff00000000ff) <<< 180) ||| ((((0xff00000000f <<< 60) ||| 0xf0000ff00000000) <<< 60) ||| 0xff0000ff0000000)) <<< 300) ||| ((((((0xff0000ff000000 <<< 60) ||| 0xff0000ff00000) <<< 60) ||| 0xff0000ff0000) <<< 120) ||| ((0xff0000ff000 <<< 60) ||| 0xff0000ff00)))),
    (0x0, 0x0),
    (((((((((0x4 <<< 60) ||| 0xbcbcbcbcbcbcbcb) <<< 60) ||| 0xcbcbcbcbcbcbcbc) <<< 180) ||| ((((0xbcbcbcbcbcbcbcb <<< 60) ||| 0xcbcbcbcbcbcbcbc) <<< 60) ||| 0xbcbcbcbcbcbcbcb)) <<< 360) ||| ((((((0xcbcbcbcbcbcbcbc <<< 60) ||| 0xbcbcbcbcbcbcbcb) <<< 60) ||| 0xcbcbcbcbcbcbcbc) <<< 180) ||| ((((0xbcbcbcbcbcbcbcb <<< 60) ||| 0xcbcbcbcbcbcbcbc) <<< 60) ||| 0xbcbcbcbcbcbcbcb))), ((((((((0x7 <<< 60) ||| 0xf0000ff00ff0000) <<< 60) ||| 0xff0000ff00ff000) <<< 180) ||| ((((0xff0000ff00ff00 <<< 60) ||| 0xff0000ff00ff0) <<< 60) ||| 0xff0000ff00ff)) <<< 360) ||| ((((((0xff0000ff00f <<< 60) ||| 0xf0000ff0000ff00) <<< 60) ||| 0xff0000ff0000ff0) <<< 180) ||| ((((0xff0000ff0000ff <<< 60) ||| 0xff0000ff0000f) <<< 60) ||| 0xf00ff0000ff0000)))),
    (((((((((0x7 <<< 60) ||| 0x2f2f2f2f2f2f2f2) <<< 60) ||| 0xf2f2f2f2f2f2f2f) <<< 180) ||| ((((0x2f2f2f2f2f2f2f2 <<< 60) ||| 0xf2f2f2f2f2f2f2f) <<< 60) ||| 0x2f2f2f2f2f2f2f2)) <<< 360) ||| ((((((0xf2f2f2f2f2f2f2f <<< 60) ||| 0x2f2f2f2f2f2f2f2) <<< 60) ||| 0xf2f2f2f2f2f2f2f) <<< 180) ||| ((((0x2f2f2f2f2f2f2f2 <<< 60) ||| 0xf2f2f2f2f2f2f2f) <<< 60) ||| 0x2f2f2f2f2f2f2f2))), ((((((((0xffffff <<< 60) ||| 0xfffff) <<< 60) ||| 0xf0000000000ffff) <<< 180) ||| ((((0xff0000000000fff <<< 60) ||| 0xfff0000000000ff) <<< 60) ||| 0xffff0000000000f)) <<< 300) ||| ((((((0xfffff0000000000 <<< 60) ||| 0xffffff000000000) <<< 60) ||| 0xffffff00000000) <<< 120) ||| ((0xffffff0000000 <<< 60) ||| 0xffffff000000)))),
    (0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc)) <<< 360) ||| ((((((0xfcfcfcfcfcfcfcf <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc))), ((((((((0xffff000000 <<< 60) ||| 0xffff00000) <<< 60) ||| 0xffff0000) <<< 180) ||| ((((0xffff000 <<< 60) ||| 0xffff00) <<< 60) ||| 0xffff0)) <<< 300) ||| ((((((0xffff <<< 60) ||| 0xfff) <<< 60) ||| 0xf000000000000ff) <<< 120) ||| ((0xff000000000000f <<< 60) ||| 0xfff000000000000))))]

def g90C : List ColumnInfo := []

def g90D3 (j : Nat) : Nat := if j = 0 then 0xf else 0

def g90L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g90D3)
  | _ => emptyPacking

def g90I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g90 : Forest := ⟨90, 3, fun i => (g90Y[i]?).getD (0,0), g90C, [[]], g90L, g90I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g90P3n0 : block g90 3 0 1 = true := by decide +kernel

theorem g90B3 : block g90 3 0 1 = true := g90P3n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g90T : checkedTables g90 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g90 0 0 0 = true)
  · exact (rfl : block g90 1 0 0 = true)
  · exact (rfl : block g90 2 0 0 = true)
  · exact g90B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g90G : graphValid g90 (boundsBefore K86) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low90 : Lower true (varsX 90) (graphGoal 90) 4 := lower_forest (g:=g90) (i:=0) (hints:=17174576) (before_sound K86 V86) g90G g90T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K90 := extendKnown K86 4 [(90,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V90 : Known true K90 := extend_ok (m:=90) V86 low90 (by decide +kernel)

def g102Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0xab6adab6adab6ad) <<< 60) ||| 0xab6adab6adab6ad) <<< 180) ||| ((((0xab6adab6adab6ad <<< 60) ||| 0xab6adab6adab6ad) <<< 60) ||| 0xab6adab6adab6ad)) <<< 360) ||| ((((((0xab6adab6adab6ad <<< 60) ||| 0xab6adab6adab6ad) <<< 60) ||| 0xab6adab6adab6ad) <<< 180) ||| ((((0xab6adab6adab6ad <<< 60) ||| 0xab6adab6adab6ad) <<< 60) ||| 0xab6adab6adab6ad))), ((((((((0xffc00ffc00 <<< 60) ||| 0xffc00ffc00) <<< 60) ||| 0xffc00ffc00) <<< 180) ||| ((((0xffc00ffc00 <<< 60) ||| 0xffc00ffc00) <<< 60) ||| 0xffc00ffc00)) <<< 300) ||| ((((((0xffc00ffc00 <<< 60) ||| 0xffc00ffc00) <<< 60) ||| 0xffc00ffc00) <<< 120) ||| ((0xffc00ffc00 <<< 60) ||| 0xffc00ffc00)))),
    (((((((((0x6 <<< 60) ||| 0xcdb36cdb36cdb36) <<< 60) ||| 0xcdb36cdb36cdb36) <<< 180) ||| ((((0xcdb36cdb36cdb36 <<< 60) ||| 0xcdb36cdb36cdb36) <<< 60) ||| 0xcdb36cdb36cdb36)) <<< 360) ||| ((((((0xcdb36cdb36cdb36 <<< 60) ||| 0xcdb36cdb36cdb36) <<< 60) ||| 0xcdb36cdb36cdb36) <<< 180) ||| ((((0xcdb36cdb36cdb36 <<< 60) ||| 0xcdb36cdb36cdb36) <<< 60) ||| 0xcdb36cdb36cdb36))), ((((((((0xfffff00000 <<< 60) ||| 0xfffff00000) <<< 60) ||| 0xfffff00000) <<< 180) ||| ((((0xfffff00000 <<< 60) ||| 0xfffff00000) <<< 60) ||| 0xfffff00000)) <<< 300) ||| ((((((0xfffff00000 <<< 60) ||| 0xfffff00000) <<< 60) ||| 0xfffff00000) <<< 120) ||| ((0xfffff00000 <<< 60) ||| 0xfffff00000)))),
    (0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0xf1fc7f1fc7f1fc7) <<< 60) ||| 0xf1fc7f1fc7f1fc7) <<< 180) ||| ((((0xf1fc7f1fc7f1fc7 <<< 60) ||| 0xf1fc7f1fc7f1fc7) <<< 60) ||| 0xf1fc7f1fc7f1fc7)) <<< 360) ||| ((((((0xf1fc7f1fc7f1fc7 <<< 60) ||| 0xf1fc7f1fc7f1fc7) <<< 60) ||| 0xf1fc7f1fc7f1fc7) <<< 180) ||| ((((0xf1fc7f1fc7f1fc7 <<< 60) ||| 0xf1fc7f1fc7f1fc7) <<< 60) ||| 0xf1fc7f1fc7f1fc7))), ((((((((0x3ff0000000000 <<< 60) ||| 0x3ff0000000000) <<< 60) ||| 0x3ff0000000000) <<< 180) ||| ((((0x3ff0000000000 <<< 60) ||| 0x3ff0000000000) <<< 60) ||| 0x3ff0000000000)) <<< 300) ||| ((((((0x3ff0000000000 <<< 60) ||| 0x3ff0000000000) <<< 60) ||| 0x3ff0000000000) <<< 120) ||| ((0x3ff0000000000 <<< 60) ||| 0x3ff0000000000)))),
    (((((((((0xfe3f8fe3f8fe3f8 <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 180) ||| ((((0xfe3f8fe3f8fe3f8 <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 60) ||| 0xfe3f8fe3f8fe3f8)) <<< 300) ||| ((((((0xfe3f8fe3f8fe3f8 <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 120) ||| ((0xfe3f8fe3f8fe3f8 <<< 60) ||| 0xfe3f8fe3f8fe3f8))), ((((((((0xffc000000000000 <<< 60) ||| 0xffc000000000000) <<< 60) ||| 0xffc000000000000) <<< 180) ||| ((((0xffc000000000000 <<< 60) ||| 0xffc000000000000) <<< 60) ||| 0xffc000000000000)) <<< 300) ||| ((((((0xffc000000000000 <<< 60) ||| 0xffc000000000000) <<< 60) ||| 0xffc000000000000) <<< 120) ||| ((0xffc000000000000 <<< 60) ||| 0xffc000000000000))))]

def g102C : List ColumnInfo := [(2,0,100,0,4)]

def g102D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0

def g102L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g102D4)
  | _ => emptyPacking

def g102I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g102 : Forest := ⟨102, 4, fun i => (g102Y[i]?).getD (0,0), g102C, [[]], g102L, g102I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102P4n0 : block g102 4 0 1 = true := by decide +kernel

theorem g102B4 : block g102 4 0 1 = true := g102P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102T : checkedTables g102 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g102 0 0 0 = true)
  · exact (rfl : block g102 1 0 0 = true)
  · exact (rfl : block g102 2 0 0 = true)
  · exact (rfl : block g102 3 0 0 = true)
  · exact g102B4

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102G : graphValid g102 (boundsBefore K90) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low102 : Lower true (varsX 102) (graphGoal 102) 5 := lower_forest (g:=g102) (i:=0) (hints:=17827152) (before_sound K90 V90) g102G g102T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K102 := extendKnown K90 5 [(102,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V102 : Known true K102 := extend_ok (m:=102) V90 low102 (by decide +kernel)

def g106Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0xaeebbaeebbaeebb) <<< 60) ||| 0xaeebbaeebbaeebb) <<< 180) ||| ((((0xaeebbaeebbaeebb <<< 60) ||| 0xaeebbaeebbaeebb) <<< 60) ||| 0xaeebbaeebbaeebb)) <<< 360) ||| ((((((0xaeebbaeebbaeebb <<< 60) ||| 0xaeebbaeebbaeebb) <<< 60) ||| 0xaeebbaeebbaeebb) <<< 180) ||| ((((0xaeebbaeebbaeebb <<< 60) ||| 0xaeebbaeebbaeebb) <<< 60) ||| 0xaeebbaeebbaeebb))), ((((((((0xffc00 <<< 60) ||| 0xffc00) <<< 60) ||| 0xffc00) <<< 180) ||| ((((0xffc00 <<< 60) ||| 0xffc00) <<< 60) ||| 0xffc00)) <<< 300) ||| ((((((0xffc00 <<< 60) ||| 0xffc00) <<< 60) ||| 0xffc00) <<< 120) ||| ((0xffc00 <<< 60) ||| 0xffc00)))),
    (0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0xcb72dcb72dcb72d) <<< 60) ||| 0xcb72dcb72dcb72d) <<< 180) ||| ((((0xcb72dcb72dcb72d <<< 60) ||| 0xcb72dcb72dcb72d) <<< 60) ||| 0xcb72dcb72dcb72d)) <<< 360) ||| ((((((0xcb72dcb72dcb72d <<< 60) ||| 0xcb72dcb72dcb72d) <<< 60) ||| 0xcb72dcb72dcb72d) <<< 180) ||| ((((0xcb72dcb72dcb72d <<< 60) ||| 0xcb72dcb72dcb72d) <<< 60) ||| 0xcb72dcb72dcb72d))), ((((((((0xffc00003ff00000 <<< 60) ||| 0xffc00003ff00000) <<< 60) ||| 0xffc00003ff00000) <<< 180) ||| ((((0xffc00003ff00000 <<< 60) ||| 0xffc00003ff00000) <<< 60) ||| 0xffc00003ff00000)) <<< 300) ||| ((((((0xffc00003ff00000 <<< 60) ||| 0xffc00003ff00000) <<< 60) ||| 0xffc00003ff00000) <<< 120) ||| ((0xffc00003ff00000 <<< 60) ||| 0xffc00003ff00000)))),
    (0x0, 0x0),
    (((((((((0x6 <<< 60) ||| 0xf3bcef3bcef3bce) <<< 60) ||| 0xf3bcef3bcef3bce) <<< 180) ||| ((((0xf3bcef3bcef3bce <<< 60) ||| 0xf3bcef3bcef3bce) <<< 60) ||| 0xf3bcef3bcef3bce)) <<< 360) ||| ((((((0xf3bcef3bcef3bce <<< 60) ||| 0xf3bcef3bcef3bce) <<< 60) ||| 0xf3bcef3bcef3bce) <<< 180) ||| ((((0xf3bcef3bcef3bce <<< 60) ||| 0xf3bcef3bcef3bce) <<< 60) ||| 0xf3bcef3bcef3bce))), ((((((((0xffc0000000 <<< 60) ||| 0xffc0000000) <<< 60) ||| 0xffc0000000) <<< 180) ||| ((((0xffc0000000 <<< 60) ||| 0xffc0000000) <<< 60) ||| 0xffc0000000)) <<< 300) ||| ((((((0xffc0000000 <<< 60) ||| 0xffc0000000) <<< 60) ||| 0xffc0000000) <<< 120) ||| ((0xffc0000000 <<< 60) ||| 0xffc0000000)))),
    (((((((((0xfc3f0fc3f0fc3f0 <<< 60) ||| 0xfc3f0fc3f0fc3f0) <<< 60) ||| 0xfc3f0fc3f0fc3f0) <<< 180) ||| ((((0xfc3f0fc3f0fc3f0 <<< 60) ||| 0xfc3f0fc3f0fc3f0) <<< 60) ||| 0xfc3f0fc3f0fc3f0)) <<< 300) ||| ((((((0xfc3f0fc3f0fc3f0 <<< 60) ||| 0xfc3f0fc3f0fc3f0) <<< 60) ||| 0xfc3f0fc3f0fc3f0) <<< 120) ||| ((0xfc3f0fc3f0fc3f0 <<< 60) ||| 0xfc3f0fc3f0fc3f0))), ((((((((0xfffff0000000000 <<< 60) ||| 0xfffff0000000000) <<< 60) ||| 0xfffff0000000000) <<< 180) ||| ((((0xfffff0000000000 <<< 60) ||| 0xfffff0000000000) <<< 60) ||| 0xfffff0000000000)) <<< 300) ||| ((((((0xfffff0000000000 <<< 60) ||| 0xfffff0000000000) <<< 60) ||| 0xfffff0000000000) <<< 120) ||| ((0xfffff0000000000 <<< 60) ||| 0xfffff0000000000))))]

def g106C : List ColumnInfo := [(8,0,98,0,4)]

def g106D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0

def g106L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g106D4)
  | _ => emptyPacking

def g106I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g106 : Forest := ⟨106, 4, fun i => (g106Y[i]?).getD (0,0), g106C, [[]], g106L, g106I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P4n0 : block g106 4 0 1 = true := by decide +kernel

theorem g106B4 : block g106 4 0 1 = true := g106P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106T : checkedTables g106 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g106 0 0 0 = true)
  · exact (rfl : block g106 1 0 0 = true)
  · exact (rfl : block g106 2 0 0 = true)
  · exact (rfl : block g106 3 0 0 = true)
  · exact g106B4

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106G : graphValid g106 (boundsBefore K102) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low106 : Lower true (varsX 106) (graphGoal 106) 5 := lower_forest (g:=g106) (i:=0) (hints:=17829936) (before_sound K102 V102) g106G g106T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K106 := extendKnown K102 5 [(106,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V106 : Known true K106 := extend_ok (m:=106) V102 low106 (by decide +kernel)

def g108Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0xb5daed76bb5daed) <<< 60) ||| 0x76bb5daed76bb5d) <<< 180) ||| ((((0xaed76bb5daed76b <<< 60) ||| 0xb5daed76bb5daed) <<< 60) ||| 0x76bb5daed76bb5d)) <<< 360) ||| ((((((0xaed76bb5daed76b <<< 60) ||| 0xb5daed76bb5daed) <<< 60) ||| 0x76bb5daed76bb5d) <<< 180) ||| ((((0xaed76bb5daed76b <<< 60) ||| 0xb5daed76bb5daed) <<< 60) ||| 0x76bb5daed76bb5d))), ((((((((0x7 <<< 60) ||| 0xe00ff8000000007) <<< 60) ||| 0xfc01ff000000000) <<< 180) ||| ((((0xff803fe00000000 <<< 60) ||| 0x1ff007fc0000000) <<< 60) ||| 0x3fe00ff8000000)) <<< 360) ||| ((((((0x7fc01ff000000 <<< 60) ||| 0xff803fe00000) <<< 60) ||| 0x1ff007fc0000) <<< 180) ||| ((((0x3fe00ff8000 <<< 60) ||| 0x7fc01ff000) <<< 60) ||| 0xff803fe00)))),
    (((((((((0x2 <<< 60) ||| 0xd96cb65b2d96cb6) <<< 60) ||| 0x5b2d96cb65b2d96) <<< 180) ||| ((((0xcb65b2d96cb65b2 <<< 60) ||| 0xd96cb65b2d96cb6) <<< 60) ||| 0x5b2d96cb65b2d96)) <<< 360) ||| ((((((0xcb65b2d96cb65b2 <<< 60) ||| 0xd96cb65b2d96cb6) <<< 60) ||| 0x5b2d96cb65b2d96) <<< 180) ||| ((((0xcb65b2d96cb65b2 <<< 60) ||| 0xd96cb65b2d96cb6) <<< 60) ||| 0x5b2d96cb65b2d96))), ((((((((0x7 <<< 60) ||| 0xfff00003fe00007) <<< 60) ||| 0xfffe00007fc0000) <<< 180) ||| ((((0xffffc0000ff8000 <<< 60) ||| 0x1ffff80001ff000) <<< 60) ||| 0x3ffff00003fe00)) <<< 360) ||| ((((((0x7fffe00007fc0 <<< 60) ||| 0xffffc0000ff8) <<< 60) ||| 0x1ffff80001ff) <<< 180) ||| ((((0x3ffff00003f <<< 60) ||| 0xe00007fffe00007) <<< 60) ||| 0xfc0000ffffc0000)))),
    (0x0, 0x0),
    (((((((((0x4 <<< 60) ||| 0xfe7f3f9fcfe7f3f) <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 180) ||| ((((0xf3f9fcfe7f3f9fc <<< 60) ||| 0xfe7f3f9fcfe7f3f) <<< 60) ||| 0x9fcfe7f3f9fcfe7)) <<< 360) ||| ((((((0xf3f9fcfe7f3f9fc <<< 60) ||| 0xfe7f3f9fcfe7f3f) <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 180) ||| ((((0xf3f9fcfe7f3f9fc <<< 60) ||| 0xfe7f3f9fcfe7f3f) <<< 60) ||| 0x9fcfe7f3f9fcfe7))), ((((((((0xff8 <<< 60) ||| 0x1ff) <<< 60) ||| 0x3f) <<< 180) ||| ((((0xe00000000000007 <<< 60) ||| 0xfc0000000000000) <<< 60) ||| 0xff8000000000000)) <<< 300) ||| ((((((0x1ff000000000000 <<< 60) ||| 0x3fe00000000000) <<< 60) ||| 0x7fc0000000000) <<< 120) ||| ((0xff8000000000 <<< 60) ||| 0x1ff000000000)))),
    (((((((((0x7 <<< 60) ||| 0x1f8fc7e3f1f8fc7) <<< 60) ||| 0xe3f1f8fc7e3f1f8) <<< 180) ||| ((((0xfc7e3f1f8fc7e3f <<< 60) ||| 0x1f8fc7e3f1f8fc7) <<< 60) ||| 0xe3f1f8fc7e3f1f8)) <<< 360) ||| ((((((0xfc7e3f1f8fc7e3f <<< 60) ||| 0x1f8fc7e3f1f8fc7) <<< 60) ||| 0xe3f1f8fc7e3f1f8) <<< 180) ||| ((((0xfc7e3f1f8fc7e3f <<< 60) ||| 0x1f8fc7e3f1f8fc7) <<< 60) ||| 0xe3f1f8fc7e3f1f8))), ((((((((0x3ffff000 <<< 60) ||| 0x7fffe00) <<< 60) ||| 0xffffc0) <<< 180) ||| ((((0x1ffff8 <<< 60) ||| 0x3ffff) <<< 60) ||| 0x7fff)) <<< 300) ||| ((((((0xe00000000000fff <<< 60) ||| 0xfc00000000001ff) <<< 60) ||| 0xff800000000003f) <<< 120) ||| ((0xfff000000000007 <<< 60) ||| 0xfffe00000000000))))]

def g108C : List ColumnInfo := [(8,0,100,0,4)]

def g108D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0

def g108L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g108D4)
  | _ => emptyPacking

def g108I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g108 : Forest := ⟨108, 4, fun i => (g108Y[i]?).getD (0,0), g108C, [[]], g108L, g108I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108P4n0 : block g108 4 0 1 = true := by decide +kernel

theorem g108B4 : block g108 4 0 1 = true := g108P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108T : checkedTables g108 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g108 0 0 0 = true)
  · exact (rfl : block g108 1 0 0 = true)
  · exact (rfl : block g108 2 0 0 = true)
  · exact (rfl : block g108 3 0 0 = true)
  · exact g108B4

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108G : graphValid g108 (boundsBefore K106) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low108 : Lower true (varsX 108) (graphGoal 108) 5 := lower_forest (g:=g108) (i:=0) (hints:=35673344) (before_sound K106 V106) g108G g108T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K108 := extendKnown K106 5 [(108,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V108 : Known true K108 := extend_ok (m:=108) V106 low108 (by decide +kernel)

def g114Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x2 <<< 60) ||| 0xf57abd5eaf57abd) <<< 60) ||| 0x5eaf57abd5eaf57) <<< 180) ||| ((((0xabd5eaf57abd5ea <<< 60) ||| 0xf57abd5eaf57abd) <<< 60) ||| 0x5eaf57abd5eaf57)) <<< 360) ||| ((((((0xabd5eaf57abd5ea <<< 60) ||| 0xf57abd5eaf57abd) <<< 60) ||| 0x5eaf57abd5eaf57) <<< 180) ||| ((((0xabd5eaf57abd5ea <<< 60) ||| 0xf57abd5eaf57abd) <<< 60) ||| 0x5eaf57abd5eaf57))), ((((((((0x7 <<< 60) ||| 0xe00ff8000000007) <<< 60) ||| 0xfc01ff000000000) <<< 180) ||| ((((0xff803fe00000000 <<< 60) ||| 0x1ff007fc0000000) <<< 60) ||| 0x3fe00ff8000000)) <<< 360) ||| ((((((0x7fc01ff000000 <<< 60) ||| 0xff803fe00000) <<< 60) ||| 0x1ff007fc0000) <<< 180) ||| ((((0x3fe00ff8000 <<< 60) ||| 0x7fc01ff000) <<< 60) ||| 0xff803fe00)))),
    (0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0x59acd66b359acd6) <<< 60) ||| 0x6b359acd66b359a) <<< 180) ||| ((((0xcd66b359acd66b3 <<< 60) ||| 0x59acd66b359acd6) <<< 60) ||| 0x6b359acd66b359a)) <<< 360) ||| ((((((0xcd66b359acd66b3 <<< 60) ||| 0x59acd66b359acd6) <<< 60) ||| 0x6b359acd66b359a) <<< 180) ||| ((((0xcd66b359acd66b3 <<< 60) ||| 0x59acd66b359acd6) <<< 60) ||| 0x6b359acd66b359a))), ((((((((0x7 <<< 60) ||| 0xfff0000001ff007) <<< 60) ||| 0xfffe0000003fe00) <<< 180) ||| ((((0xffffc0000007fc0 <<< 60) ||| 0x1ffff8000000ff8) <<< 60) ||| 0x3ffff0000001ff)) <<< 360) ||| ((((((0x7fffe0000003f <<< 60) ||| 0xe00ffffc0000007) <<< 60) ||| 0xfc01ffff8000000) <<< 180) ||| ((((0xff803ffff000000 <<< 60) ||| 0x1ff007fffe00000) <<< 60) ||| 0x3fe00ffffc0000)))),
    (((((((((0x4 <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3) <<< 180) ||| ((((0xf1f8fc7e3f1f8fc <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3)) <<< 360) ||| ((((((0xf1f8fc7e3f1f8fc <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3) <<< 180) ||| ((((0xf1f8fc7e3f1f8fc <<< 60) ||| 0x7e3f1f8fc7e3f1f) <<< 60) ||| 0x8fc7e3f1f8fc7e3))), ((((((((0x1ffff8 <<< 60) ||| 0x3ffff) <<< 60) ||| 0x7fff) <<< 180) ||| ((((0xe00000000000fff <<< 60) ||| 0xfc00000000001ff) <<< 60) ||| 0xff800000000003f)) <<< 300) ||| ((((((0xfff000000000007 <<< 60) ||| 0xfffe00000000000) <<< 60) ||| 0xffffc0000000000) <<< 120) ||| ((0x1ffff8000000000 <<< 60) ||| 0x3ffff000000000)))),
    (((((((((0x7 <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc) <<< 180) ||| ((((0xfe7f3f9fcfe7f3f <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc)) <<< 360) ||| ((((((0xfe7f3f9fcfe7f3f <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc) <<< 180) ||| ((((0xfe7f3f9fcfe7f3f <<< 60) ||| 0x9fcfe7f3f9fcfe7) <<< 60) ||| 0xf3f9fcfe7f3f9fc))), ((((((((0x3fe00000 <<< 60) ||| 0x7fc0000) <<< 60) ||| 0xff8000) <<< 180) ||| ((((0x1ff000 <<< 60) ||| 0x3fe00) <<< 60) ||| 0x7fc0)) <<< 300) ||| ((((((0xff8 <<< 60) ||| 0x1ff) <<< 60) ||| 0x3f) <<< 120) ||| ((0xe00000000000007 <<< 60) ||| 0xfc0000000000000))))]

def g114C : List ColumnInfo := [(16,0,98,0,4)]

def g114D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0

def g114L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g114D4)
  | _ => emptyPacking

def g114I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g114 : Forest := ⟨114, 4, fun i => (g114Y[i]?).getD (0,0), g114C, [[]], g114L, g114I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114P4n0 : block g114 4 0 1 = true := by decide +kernel

theorem g114B4 : block g114 4 0 1 = true := g114P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114T : checkedTables g114 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g114 0 0 0 = true)
  · exact (rfl : block g114 1 0 0 = true)
  · exact (rfl : block g114 2 0 0 = true)
  · exact (rfl : block g114 3 0 0 = true)
  · exact g114B4

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114G : graphValid g114 (boundsBefore K108) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low114 : Lower true (varsX 114) (graphGoal 114) 5 := lower_forest (g:=g114) (i:=0) (hints:=18219088) (before_sound K108 V108) g114G g114T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K114 := extendKnown K108 5 [(114,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V114 : Known true K114 := extend_ok (m:=114) V108 low114 (by decide +kernel)

def g116Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0xabeafabeafabeaf) <<< 60) ||| 0xabeafabeafabeaf) <<< 180) ||| ((((0xabeafabeafabeaf <<< 60) ||| 0xabeafabeafabeaf) <<< 60) ||| 0xabeafabeafabeaf)) <<< 360) ||| ((((((0xabeafabeafabeaf <<< 60) ||| 0xabeafabeafabeaf) <<< 60) ||| 0xabeafabeafabeaf) <<< 180) ||| ((((0xabeafabeafabeaf <<< 60) ||| 0xabeafabeafabeaf) <<< 60) ||| 0xabeafabeafabeaf))), ((((((((0xffc00 <<< 60) ||| 0xffc00) <<< 60) ||| 0xffc00) <<< 180) ||| ((((0xffc00 <<< 60) ||| 0xffc00) <<< 60) ||| 0xffc00)) <<< 300) ||| ((((((0xffc00 <<< 60) ||| 0xffc00) <<< 60) ||| 0xffc00) <<< 120) ||| ((0xffc00 <<< 60) ||| 0xffc00)))),
    (0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0xcd735cd735cd735) <<< 60) ||| 0xcd735cd735cd735) <<< 180) ||| ((((0xcd735cd735cd735 <<< 60) ||| 0xcd735cd735cd735) <<< 60) ||| 0xcd735cd735cd735)) <<< 360) ||| ((((((0xcd735cd735cd735 <<< 60) ||| 0xcd735cd735cd735) <<< 60) ||| 0xcd735cd735cd735) <<< 180) ||| ((((0xcd735cd735cd735 <<< 60) ||| 0xcd735cd735cd735) <<< 60) ||| 0xcd735cd735cd735))), ((((((((0x3ff003ff00000 <<< 60) ||| 0x3ff003ff00000) <<< 60) ||| 0x3ff003ff00000) <<< 180) ||| ((((0x3ff003ff00000 <<< 60) ||| 0x3ff003ff00000) <<< 60) ||| 0x3ff003ff00000)) <<< 300) ||| ((((((0x3ff003ff00000 <<< 60) ||| 0x3ff003ff00000) <<< 60) ||| 0x3ff003ff00000) <<< 120) ||| ((0x3ff003ff00000 <<< 60) ||| 0x3ff003ff00000)))),
    (((((((((0x6 <<< 60) ||| 0xf1bc6f1bc6f1bc6) <<< 60) ||| 0xf1bc6f1bc6f1bc6) <<< 180) ||| ((((0xf1bc6f1bc6f1bc6 <<< 60) ||| 0xf1bc6f1bc6f1bc6) <<< 60) ||| 0xf1bc6f1bc6f1bc6)) <<< 360) ||| ((((((0xf1bc6f1bc6f1bc6 <<< 60) ||| 0xf1bc6f1bc6f1bc6) <<< 60) ||| 0xf1bc6f1bc6f1bc6) <<< 180) ||| ((((0xf1bc6f1bc6f1bc6 <<< 60) ||| 0xf1bc6f1bc6f1bc6) <<< 60) ||| 0xf1bc6f1bc6f1bc6))), ((((((((0x3ffffc0000000 <<< 60) ||| 0x3ffffc0000000) <<< 60) ||| 0x3ffffc0000000) <<< 180) ||| ((((0x3ffffc0000000 <<< 60) ||| 0x3ffffc0000000) <<< 60) ||| 0x3ffffc0000000)) <<< 300) ||| ((((((0x3ffffc0000000 <<< 60) ||| 0x3ffffc0000000) <<< 60) ||| 0x3ffffc0000000) <<< 120) ||| ((0x3ffffc0000000 <<< 60) ||| 0x3ffffc0000000)))),
    (((((((((0xfe3f8fe3f8fe3f8 <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 180) ||| ((((0xfe3f8fe3f8fe3f8 <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 60) ||| 0xfe3f8fe3f8fe3f8)) <<< 300) ||| ((((((0xfe3f8fe3f8fe3f8 <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 60) ||| 0xfe3f8fe3f8fe3f8) <<< 120) ||| ((0xfe3f8fe3f8fe3f8 <<< 60) ||| 0xfe3f8fe3f8fe3f8))), ((((((((0xffc000000000000 <<< 60) ||| 0xffc000000000000) <<< 60) ||| 0xffc000000000000) <<< 180) ||| ((((0xffc000000000000 <<< 60) ||| 0xffc000000000000) <<< 60) ||| 0xffc000000000000)) <<< 300) ||| ((((((0xffc000000000000 <<< 60) ||| 0xffc000000000000) <<< 60) ||| 0xffc000000000000) <<< 120) ||| ((0xffc000000000000 <<< 60) ||| 0xffc000000000000))))]

def g116C : List ColumnInfo := [(16,0,100,0,4)]

def g116D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0

def g116L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g116D4)
  | _ => emptyPacking

def g116I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g116 : Forest := ⟨116, 4, fun i => (g116Y[i]?).getD (0,0), g116C, [[]], g116L, g116I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g116P4n0 : block g116 4 0 1 = true := by decide +kernel

theorem g116B4 : block g116 4 0 1 = true := g116P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g116T : checkedTables g116 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g116 0 0 0 = true)
  · exact (rfl : block g116 1 0 0 = true)
  · exact (rfl : block g116 2 0 0 = true)
  · exact (rfl : block g116 3 0 0 = true)
  · exact g116B4

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g116G : graphValid g116 (boundsBefore K114) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low116 : Lower true (varsX 116) (graphGoal 116) 5 := lower_forest (g:=g116) (i:=0) (hints:=35783680) (before_sound K114 V114) g116G g116T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K116 := extendKnown K114 5 [(116,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V116 : Known true K116 := extend_ok (m:=116) V114 low116 (by decide +kernel)

def g120Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x2 <<< 60) ||| 0xbababababababab) <<< 60) ||| 0xabababababababa) <<< 180) ||| ((((0xbababababababab <<< 60) ||| 0xabababababababa) <<< 60) ||| 0xbababababababab)) <<< 360) ||| ((((((0xabababababababa <<< 60) ||| 0xbababababababab) <<< 60) ||| 0xabababababababa) <<< 180) ||| ((((0xbababababababab <<< 60) ||| 0xabababababababa) <<< 60) ||| 0xbababababababab))), ((((((((0xff00ff000000ff <<< 60) ||| 0xff00ff000000f) <<< 60) ||| 0xf00ff00ff000000) <<< 180) ||| ((((0xff00ff00ff00000 <<< 60) ||| 0xff00ff00ff0000) <<< 60) ||| 0xff00ff00ff000)) <<< 300) ||| ((((((0xff00ff00ff00 <<< 60) ||| 0xff00ff00ff0) <<< 60) ||| 0xff00ff00ff) <<< 120) ||| ((0xff00ff00f <<< 60) ||| 0xf000000ff00ff00)))),
    (((((((((0x4 <<< 60) ||| 0xececececececece) <<< 60) ||| 0xcececececececec) <<< 180) ||| ((((0xececececececece <<< 60) ||| 0xcececececececec) <<< 60) ||| 0xececececececece)) <<< 360) ||| ((((((0xcececececececec <<< 60) ||| 0xececececececece) <<< 60) ||| 0xcececececececec) <<< 180) ||| ((((0xececececececece <<< 60) ||| 0xcececececececec) <<< 60) ||| 0xececececececece))), ((((((((0x7 <<< 60) ||| 0xf00000000ff00ff) <<< 60) ||| 0xff00000000ff00f) <<< 180) ||| ((((0xfff00000000ff00 <<< 60) ||| 0xffff00000000ff0) <<< 60) ||| 0xffff00000000ff)) <<< 360) ||| ((((((0xffff00000000f <<< 60) ||| 0xf00ffff00000000) <<< 60) ||| 0xff00ffff0000000) <<< 180) ||| ((((0xff00ffff000000 <<< 60) ||| 0xff00ffff00000) <<< 60) ||| 0xff00ffff0000)))),
    (((((((((0x7 <<< 60) ||| 0x3f3f3f3f3f3f3f3) <<< 60) ||| 0xf3f3f3f3f3f3f3f) <<< 180) ||| ((((0x3f3f3f3f3f3f3f3 <<< 60) ||| 0xf3f3f3f3f3f3f3f) <<< 60) ||| 0x3f3f3f3f3f3f3f3)) <<< 360) ||| ((((((0xf3f3f3f3f3f3f3f <<< 60) ||| 0x3f3f3f3f3f3f3f3) <<< 60) ||| 0xf3f3f3f3f3f3f3f) <<< 180) ||| ((((0x3f3f3f3f3f3f3f3 <<< 60) ||| 0xf3f3f3f3f3f3f3f) <<< 60) ||| 0x3f3f3f3f3f3f3f3))), ((((((((0xffff00 <<< 60) ||| 0xffff0) <<< 60) ||| 0xffff) <<< 180) ||| ((((0xfff <<< 60) ||| 0xf000000000000ff) <<< 60) ||| 0xff000000000000f)) <<< 300) ||| ((((((0xfff000000000000 <<< 60) ||| 0xffff00000000000) <<< 60) ||| 0xffff0000000000) <<< 120) ||| ((0xffff000000000 <<< 60) ||| 0xffff00000000)))),
    (((((((((0x7 <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc)) <<< 360) ||| ((((((0xfcfcfcfcfcfcfcf <<< 60) ||| 0xcfcfcfcfcfcfcfc) <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 180) ||| ((((0xcfcfcfcfcfcfcfc <<< 60) ||| 0xfcfcfcfcfcfcfcf) <<< 60) ||| 0xcfcfcfcfcfcfcfc))), ((((((((0xffff000000 <<< 60) ||| 0xffff00000) <<< 60) ||| 0xffff0000) <<< 180) ||| ((((0xffff000 <<< 60) ||| 0xffff00) <<< 60) ||| 0xffff0)) <<< 300) ||| ((((((0xffff <<< 60) ||| 0xfff) <<< 60) ||| 0xf000000000000ff) <<< 120) ||| ((0xff000000000000f <<< 60) ||| 0xfff000000000000))))]

def g120C : List ColumnInfo := []

def g120D3 (j : Nat) : Nat := if j = 0 then 0xf else 0

def g120L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g120D3)
  | _ => emptyPacking

def g120I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g120 : Forest := ⟨120, 3, fun i => (g120Y[i]?).getD (0,0), g120C, [[]], g120L, g120I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120P3n0 : block g120 3 0 1 = true := by decide +kernel

theorem g120B3 : block g120 3 0 1 = true := g120P3n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120T : checkedTables g120 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g120 0 0 0 = true)
  · exact (rfl : block g120 1 0 0 = true)
  · exact (rfl : block g120 2 0 0 = true)
  · exact g120B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120G : graphValid g120 (boundsBefore K116) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low120 : Lower true (varsX 120) (graphGoal 120) 4 := lower_forest (g:=g120) (i:=0) (hints:=70668288) (before_sound K116 V116) g120G g120T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K120 := extendKnown K116 4 [(120,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V120 : Known true K120 := extend_ok (m:=120) V116 low120 (by decide +kernel)

def g62Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0x6dd5ab6ead5b756) <<< 60) ||| 0xadbab56dd5ab6ea) <<< 180) ||| ((((0xd5b756adbab56dd <<< 60) ||| 0x5ab6ead5b756adb) <<< 60) ||| 0xab56dd5ab6ead5b)) <<< 360) ||| ((((((0x756adbab56dd5ab <<< 60) ||| 0x6ead5b756adbab5) <<< 60) ||| 0x6dd5ab6ead5b756) <<< 180) ||| ((((0xadbab56dd5ab6ea <<< 60) ||| 0xd5b756adbab56dd) <<< 60) ||| 0x5ab6ead5b756adb))), ((((((((0x3ffffe00 <<< 60) ||| 0x3f) <<< 60) ||| 0xfffe00000fffff8) <<< 180) ||| ((((0x0 <<< 60) ||| 0x7ffffc0000) <<< 60) ||| 0x7fff)) <<< 300) ||| ((((((0xfc00001fffff000 <<< 60) ||| 0x0) <<< 60) ||| 0xfffff8000000) <<< 120) ||| ((0xfffff8 <<< 60) ||| 0x3ffffe00000)))),
    (((((((((0x1 <<< 60) ||| 0xb766cdbb366dd9b) <<< 60) ||| 0x36ecd9b766cdbb3) <<< 180) ||| ((((0x66dd9b36ecd9b76 <<< 60) ||| 0x6cdbb366dd9b36e) <<< 60) ||| 0xcd9b766cdbb366d)) <<< 360) ||| ((((((0xd9b36ecd9b766cd <<< 60) ||| 0xbb366dd9b36ecd9) <<< 60) ||| 0xb766cdbb366dd9b) <<< 180) ||| ((((0x36ecd9b766cdbb3 <<< 60) ||| 0x66dd9b36ecd9b76) <<< 60) ||| 0x6cdbb366dd9b36e))), ((((((((0xfffff800003f <<< 60) ||| 0xfffffffff000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1fffff000007fff)) <<< 300) ||| ((((((0xffffffe00000000 <<< 60) ||| 0x0) <<< 60) ||| 0x3f) <<< 120) ||| ((0xfffe00000ffffff <<< 60) ||| 0xffffc0000000000)))),
    (((((((((0x6 <<< 60) ||| 0x39f8f1cfc78e7e3) <<< 60) ||| 0xc73f1e39f8f1cfc) <<< 180) ||| ((((0x78e7e3c73f1e39f <<< 60) ||| 0x8f1cfc78e7e3c73) <<< 60) ||| 0xf1e39f8f1cfc78e)) <<< 360) ||| ((((((0x7e3c73f1e39f8f1 <<< 60) ||| 0xcfc78e7e3c73f1e) <<< 60) ||| 0x39f8f1cfc78e7e3) <<< 180) ||| ((((0xc73f1e39f8f1cfc <<< 60) ||| 0x78e7e3c73f1e39f) <<< 60) ||| 0x8f1cfc78e7e3c73))), ((((((((0x7ffffc0000000 <<< 60) ||| 0xffffffffffc0) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0xfffff8000000000) <<< 60) ||| 0x1ffffffffff8000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x1ff) <<< 60) ||| 0xfff00000000003f) <<< 120) ||| ((0xfffffffff000000 <<< 60) ||| 0x0)))),
    (((((((((0x3e7f01f3f80f9fc <<< 60) ||| 0x7cfe03e7f01f3f) <<< 60) ||| 0x80f9fc07cfe03e7) <<< 180) ||| ((((0xf01f3f80f9fc07c <<< 60) ||| 0xfe03e7f01f3f80f) <<< 60) ||| 0x9fc07cfe03e7f01)) <<< 300) ||| ((((((0xf3f80f9fc07cfe0 <<< 60) ||| 0x3e7f01f3f80f9fc) <<< 60) ||| 0x7cfe03e7f01f3f) <<< 120) ||| ((0x80f9fc07cfe03e7 <<< 60) ||| 0xf01f3f80f9fc07c))), ((((((((0x7ffffffffffff <<< 60) ||| 0xfff000000000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x3ffffe00000 <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xe00000000000000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x7ffffc00001ff) <<< 60) ||| 0xfffffffffffffc0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))),
    (((((((((0x7 <<< 60) ||| 0xc07ffe03fff01ff) <<< 60) ||| 0xf80fffc07ffe03f) <<< 180) ||| ((((0xff01fff80fffc07 <<< 60) ||| 0xffe03fff01fff80) <<< 60) ||| 0xfffc07ffe03fff0)) <<< 360) ||| ((((((0x1fff80fffc07ffe <<< 60) ||| 0x3fff01fff80fff) <<< 60) ||| 0xc07ffe03fff01ff) <<< 180) ||| ((((0xf80fffc07ffe03f <<< 60) ||| 0xff01fff80fffc07) <<< 60) ||| 0xffe03fff01fff80))), ((((((((0x7 <<< 60) ||| 0xff8000000000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x3ffffffffff) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x7fffffffffe00) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0)))),
    (0x0, 0x0)]

def g62C : List ColumnInfo := [(0,16,42,4,5), (2,0,60,0,4), (4,0,42,0,4), (4,16,42,0,4), (8,0,54,0,4), (16,0,46,0,5)]

def g62D4 (j : Nat) : Nat := if j = 0 then 0xc2f40a925b89504 else 0

def g62D5 (j : Nat) : Nat := if j = 0 then ((((0x500841500901 <<< 60) ||| 0x106c894280fe24f) <<< 60) ||| 0xd24fe04fd04fd02) else 0

def g62D6 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0

def g62L : Nat → Packing
  | 4 => (2, 2, 3, 0, 0, 3, 0, g62D4)
  | 5 => (5, 1, 3, 0, 0, 6, 0, g62D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g62D6)
  | _ => emptyPacking

def g62I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => some ((0x1 >>> (1 * (tag % 2))) &&& 1, 0)
  | 6, tag => some ((0x888c0 >>> (3 * (tag % 9))) &&& 7, 0)
  | _, _ => none

def g62 : Forest := ⟨62, 6, fun i => (g62Y[i]?).getD (0,0), g62C, [[]], g62L, g62I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P4n0 : block g62 4 0 2 = true := by decide +kernel

theorem g62B4 : block g62 4 0 2 = true := g62P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P5n0 : block g62 5 0 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P5n2 : block g62 5 2 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P5n4 : block g62 5 4 1 = true := by decide +kernel

theorem g62B5 : block g62 5 0 5 = true := (@block_merge g62 5 0 2 3 g62P5n0 (@block_merge g62 5 2 2 1 g62P5n2 g62P5n4))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P6n0 : block g62 6 0 1 = true := by decide +kernel

theorem g62B6 : block g62 6 0 1 = true := g62P6n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact (rfl : block g62 3 0 0 = true)
  · exact g62B4
  · exact g62B5
  · exact g62B6

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K120) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 7 := lower_forest (g:=g62) (i:=0) (hints:=1184816) (before_sound K120 V120) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K62 := extendKnown K120 7 [(62,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V120 low62 (by decide +kernel)

def g94Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0x6dd55b6eaadb755) <<< 60) ||| 0x6dbaab6dd55b6ea) <<< 180) ||| ((((0xadb7556dbaab6dd <<< 60) ||| 0x55b6eaadb7556db) <<< 60) ||| 0xaab6dd55b6eaadb)) <<< 360) ||| ((((((0x7556dbaab6dd55b <<< 60) ||| 0x6eaadb7556dbaab) <<< 60) ||| 0x6dd55b6eaadb755) <<< 180) ||| ((((0x6dbaab6dd55b6ea <<< 60) ||| 0xadb7556dbaab6dd) <<< 60) ||| 0x55b6eaadb7556db))), ((((((((0x3ffffe00 <<< 60) ||| 0x3f) <<< 60) ||| 0xfffe00000fffff8) <<< 180) ||| ((((0x0 <<< 60) ||| 0x7ffffc0000) <<< 60) ||| 0x7fff)) <<< 300) ||| ((((((0xfc00001fffff000 <<< 60) ||| 0x0) <<< 60) ||| 0xfffff8000000) <<< 120) ||| ((0xfffff8 <<< 60) ||| 0x3ffffe00000)))),
    (((((((((0x5 <<< 60) ||| 0xb7666dbb336dd99) <<< 60) ||| 0xb6eccdb7666dbb3) <<< 180) ||| ((((0x36dd99b6eccdb76 <<< 60) ||| 0x66dbb336dd99b6e) <<< 60) ||| 0xccdb7666dbb336d)) <<< 360) ||| ((((((0xd99b6eccdb7666d <<< 60) ||| 0xbb336dd99b6eccd) <<< 60) ||| 0xb7666dbb336dd99) <<< 180) ||| ((((0xb6eccdb7666dbb3 <<< 60) ||| 0x36dd99b6eccdb76) <<< 60) ||| 0x66dbb336dd99b6e))), ((((((((0xfffff800003f <<< 60) ||| 0xfffffffff000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x1fffff000007fff)) <<< 300) ||| ((((((0xffffffe00000000 <<< 60) ||| 0x0) <<< 60) ||| 0x3f) <<< 120) ||| ((0xfffe00000ffffff <<< 60) ||| 0xffffc0000000000)))),
    (((((((((0x6 <<< 60) ||| 0x39f871cfc38e7e1) <<< 60) ||| 0xc73f0e39f871cfc) <<< 180) ||| ((((0x38e7e1c73f0e39f <<< 60) ||| 0x871cfc38e7e1c73) <<< 60) ||| 0xf0e39f871cfc38e)) <<< 360) ||| ((((((0x7e1c73f0e39f871 <<< 60) ||| 0xcfc38e7e1c73f0e) <<< 60) ||| 0x39f871cfc38e7e1) <<< 180) ||| ((((0xc73f0e39f871cfc <<< 60) ||| 0x38e7e1c73f0e39f) <<< 60) ||| 0x871cfc38e7e1c73))), ((((((((0x7ffffc0000000 <<< 60) ||| 0xffffffffffc0) <<< 60) ||| 0x0) <<< 180) ||| ((((0x3ffffe00000 <<< 60) ||| 0xfffff8000000000) <<< 60) ||| 0x1ffffffffff8000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x7ffffc00001ff) <<< 60) ||| 0xfff00000000003f) <<< 120) ||| ((0xfffffffff000000 <<< 60) ||| 0x0)))),
    (((((((((0x3e7f81f3fc0f9fe <<< 60) ||| 0x7cff03e7f81f3f) <<< 60) ||| 0xc0f9fe07cff03e7) <<< 180) ||| ((((0xf81f3fc0f9fe07c <<< 60) ||| 0xff03e7f81f3fc0f) <<< 60) ||| 0x9fe07cff03e7f81)) <<< 300) ||| ((((((0xf3fc0f9fe07cff0 <<< 60) ||| 0x3e7f81f3fc0f9fe) <<< 60) ||| 0x7cff03e7f81f3f) <<< 120) ||| ((0xc0f9fe07cff03e7 <<< 60) ||| 0xf81f3fc0f9fe07c))), ((((((((0x7ffffffffffff <<< 60) ||| 0xfff000000000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xe00000000000000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x1ff) <<< 60) ||| 0xfffffffffffffc0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))),
    (0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0xc07ffe03fff01ff) <<< 60) ||| 0xf80fffc07ffe03f) <<< 180) ||| ((((0xff01fff80fffc07 <<< 60) ||| 0xffe03fff01fff80) <<< 60) ||| 0xfffc07ffe03fff0)) <<< 360) ||| ((((((0x1fff80fffc07ffe <<< 60) ||| 0x3fff01fff80fff) <<< 60) ||| 0xc07ffe03fff01ff) <<< 180) ||| ((((0xf80fffc07ffe03f <<< 60) ||| 0xff01fff80fffc07) <<< 60) ||| 0xffe03fff01fff80))), ((((((((0x7 <<< 60) ||| 0xff8000000000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x3ffffffffff) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x7fffffffffe00) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0))))]

def g94C : List ColumnInfo := [(0,8,84,2,5), (2,0,84,0,4), (2,8,84,0,4), (4,0,90,0,4), (8,0,86,0,5), (16,0,78,0,4)]

def g94D4 (j : Nat) : Nat := if j = 0 then 0xc2ec2a9a578d514 else 0

def g94D5 (j : Nat) : Nat := if j = 0 then ((((0x4008c1400941 <<< 60) ||| 0x306c894280fe34f) <<< 60) ||| 0xd34fe14fd14fd13) else 0

def g94D6 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0

def g94L : Nat → Packing
  | 4 => (2, 2, 3, 0, 0, 3, 0, g94D4)
  | 5 => (5, 1, 3, 0, 0, 6, 0, g94D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g94D6)
  | _ => emptyPacking

def g94I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => some ((0x10 >>> (1 * (tag % 5))) &&& 1, 0)
  | 6, tag => some ((0x1a220 >>> (3 * (tag % 6))) &&& 7, 0)
  | _, _ => none

def g94 : Forest := ⟨94, 6, fun i => (g94Y[i]?).getD (0,0), g94C, [[]], g94L, g94I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P4n0 : block g94 4 0 2 = true := by decide +kernel

theorem g94B4 : block g94 4 0 2 = true := g94P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5n0 : block g94 5 0 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5n2 : block g94 5 2 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5n4 : block g94 5 4 1 = true := by decide +kernel

theorem g94B5 : block g94 5 0 5 = true := (@block_merge g94 5 0 2 3 g94P5n0 (@block_merge g94 5 2 2 1 g94P5n2 g94P5n4))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P6n0 : block g94 6 0 1 = true := by decide +kernel

theorem g94B6 : block g94 6 0 1 = true := g94P6n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact g94B4
  · exact g94B5
  · exact g94B6

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K62) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 7 := lower_forest (g:=g94) (i:=0) (hints:=16913456) (before_sound K62 V62) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K94 := extendKnown K62 7 [(94,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V62 low94 (by decide +kernel)

def g110Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0x5b57aab6af556d5) <<< 60) ||| 0xeaadabd55b57aab) <<< 180) ||| ((((0x6af556d5eaadabd <<< 60) ||| 0x55b57aab6af556d) <<< 60) ||| 0x5eaadabd55b57aa)) <<< 360) ||| ((((((0xb6af556d5eaadab <<< 60) ||| 0xd55b57aab6af556) <<< 60) ||| 0xd5eaadabd55b57a) <<< 180) ||| ((((0xab6af556d5eaada <<< 60) ||| 0xbd55b57aab6af55) <<< 60) ||| 0x6d5eaadabd55b57))), ((((((((0x7 <<< 60) ||| 0xffff00000000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x3fffff8 <<< 60) ||| 0xfffffe0000) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x7fffff000001fff) <<< 60) ||| 0xffc000000000000) <<< 180) ||| ((((0x0 <<< 60) ||| 0xfffffe00) <<< 60) ||| 0x3fffff800000)))),
    (((((((((0x6 <<< 60) ||| 0x6d9accdb3599b66) <<< 60) ||| 0xb336cd666d9accd) <<< 180) ||| ((((0xb3599b66b336cd6 <<< 60) ||| 0x66d9accdb3599b6) <<< 60) ||| 0x6b336cd666d9acc)) <<< 360) ||| ((((((0xdb3599b66b336cd <<< 60) ||| 0x666d9accdb3599b) <<< 60) ||| 0x66b336cd666d9ac) <<< 180) ||| ((((0xcdb3599b66b336c <<< 60) ||| 0xd666d9accdb3599) <<< 60) ||| 0xb66b336cd666d9a))), ((((((((0xfff <<< 60) ||| 0xffe000003ffffff) <<< 60) ||| 0xfffff0000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x1fffffc00000)) <<< 300) ||| ((((((0x7ffffffffffe000 <<< 60) ||| 0x0) <<< 60) ||| 0x3ffff) <<< 120) ||| ((0xf800000ffffffff <<< 60) ||| 0xfffc00000000000)))),
    (((((((((0x71e3f0e3c7e1c78 <<< 60) ||| 0xfc38f1f871e3f0e) <<< 60) ||| 0x3c7e1c78fc38f1f) <<< 180) ||| ((((0x871e3f0e3c7e1c7 <<< 60) ||| 0x8fc38f1f871e3f0) <<< 60) ||| 0xe3c7e1c78fc38f1)) <<< 300) ||| ((((((0xf871e3f0e3c7e1c <<< 60) ||| 0x78fc38f1f871e3f) <<< 60) ||| 0xe3c7e1c78fc38f) <<< 120) ||| ((0x1f871e3f0e3c7e1 <<< 60) ||| 0xc78fc38f1f871e3))), ((((((((0x1fffff <<< 60) ||| 0xc00000000000fff) <<< 60) ||| 0xffffffffc000000) <<< 180) ||| ((((0x0 <<< 60) ||| 0x3fffff80000000) <<< 60) ||| 0x1fffffffffff)) <<< 300) ||| ((((((0x800000000000000 <<< 60) ||| 0x7fffff0) <<< 60) ||| 0x3ffff) <<< 120) ||| ((0xfffffff00000000 <<< 60) ||| 0x0)))),
    (0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0x81fcff03f9fe07f) <<< 60) ||| 0x3fc0fe7f81fcff0) <<< 180) ||| ((((0x3f9fe07f3fc0fe7 <<< 60) ||| 0xf81fcff03f9fe07) <<< 60) ||| 0xf3fc0fe7f81fcff)) <<< 360) ||| ((((((0x3f9fe07f3fc0fe <<< 60) ||| 0x7f81fcff03f9fe0) <<< 60) ||| 0x7f3fc0fe7f81fcf) <<< 180) ||| ((((0xf03f9fe07f3fc0f <<< 60) ||| 0xe7f81fcff03f9fe) <<< 60) ||| 0x7f3fc0fe7f81fc))), ((((((((0x7fffff000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0xff <<< 60) ||| 0xfffe00000000000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x1fffffc0000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))),
    (((((((((0x7 <<< 60) ||| 0xfe00fffc01fff80) <<< 60) ||| 0x3fff007ffe00fff) <<< 180) ||| ((((0xc01fff803fff007 <<< 60) ||| 0xffe00fffc01fff8) <<< 60) ||| 0x3fff007ffe00ff)) <<< 360) ||| ((((((0xfc01fff803fff00 <<< 60) ||| 0x7ffe00fffc01fff) <<< 60) ||| 0x803fff007ffe00f) <<< 180) ||| ((((0xffc01fff803fff0 <<< 60) ||| 0x7ffe00fffc01ff) <<< 60) ||| 0xf803fff007ffe00))), ((((((((0x1fffff <<< 60) ||| 0xffffff800000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x3fffffffffff00) <<< 60) ||| 0x0)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x7ffffff) <<< 60) ||| 0xffffe0000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))]

def g110C : List ColumnInfo := [(2,0,108,0,5), (4,0,106,0,5), (8,0,102,0,5), (64,0,46,0,5)]

def g110D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0

def g110L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g110D6)
  | _ => emptyPacking

def g110I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g110 : Forest := ⟨110, 6, fun i => (g110Y[i]?).getD (0,0), g110C, [[]], g110L, g110I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P6n0 : block g110 6 0 1 = true := by decide +kernel

theorem g110B6 : block g110 6 0 1 = true := g110P6n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact (rfl : block g110 4 0 0 = true)
  · exact (rfl : block g110 5 0 0 = true)
  · exact g110B6

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K94) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 7 := lower_forest (g:=g110) (i:=0) (hints:=17831216) (before_sound K94 V94) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K110 := extendKnown K94 7 [(110,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V94 low110 (by decide +kernel)

def g118Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0x55b6aaab6d5556d) <<< 60) ||| 0xaaaadb5555b6aaa) <<< 180) ||| ((((0xb6d5556daaaadb5 <<< 60) ||| 0x555b6aaab6d5556) <<< 60) ||| 0xdaaaadb5555b6aa)) <<< 360) ||| ((((((0xab6d5556daaaadb <<< 60) ||| 0x5555b6aaab6d555) <<< 60) ||| 0x6daaaadb5555b6a) <<< 180) ||| ((((0xaab6d5556daaaad <<< 60) ||| 0xb5555b6aaab6d55) <<< 60) ||| 0x56daaaadb5555b6))), ((((((((0x7 <<< 60) ||| 0xffff00000000000) <<< 60) ||| 0xfff) <<< 180) ||| ((((0xffe000003fffff8 <<< 60) ||| 0xfffffe0000) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x1fffffc00000 <<< 60) ||| 0x7fffff000001fff) <<< 60) ||| 0xffc000000000000) <<< 180) ||| ((((0x3ffff <<< 60) ||| 0xf800000fffffe00) <<< 60) ||| 0x3fffff800000)))),
    (((((((((0x6 <<< 60) ||| 0x66dbcccdb7999b6) <<< 60) ||| 0xf3336de666dbccc) <<< 180) ||| ((((0xdb7999b6f3336de <<< 60) ||| 0x666dbcccdb7999b) <<< 60) ||| 0x6f3336de666dbcc)) <<< 360) ||| ((((((0xcdb7999b6f3336d <<< 60) ||| 0xe666dbcccdb7999) <<< 60) ||| 0xb6f3336de666dbc) <<< 180) ||| ((((0xccdb7999b6f3336 <<< 60) ||| 0xde666dbcccdb799) <<< 60) ||| 0x9b6f3336de666db))), ((((((((0x3ffffff <<< 60) ||| 0xfffff0000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x7ffffffffffe000)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0xffffffff <<< 60) ||| 0xfffc00000000000)))),
    (0x0, 0x0),
    (((((((((0x78e3f0f1c7e1e38 <<< 60) ||| 0xfc3c71f878e3f0f) <<< 60) ||| 0x1c7e1e38fc3c71f) <<< 180) ||| ((((0x878e3f0f1c7e1e3 <<< 60) ||| 0x8fc3c71f878e3f0) <<< 60) ||| 0xf1c7e1e38fc3c71)) <<< 300) ||| ((((((0xf878e3f0f1c7e1e <<< 60) ||| 0x38fc3c71f878e3f) <<< 60) ||| 0xf1c7e1e38fc3c7) <<< 120) ||| ((0x1f878e3f0f1c7e1 <<< 60) ||| 0xe38fc3c71f878e3))), ((((((((0x3fffff800000fff <<< 60) ||| 0xffffffffc000000) <<< 60) ||| 0x0) <<< 120) ||| ((0x7fffff00 <<< 60) ||| 0x1fffffffffff)) <<< 300) ||| ((((((0x800000000000000 <<< 60) ||| 0xf) <<< 60) ||| 0xffffe000003ffff) <<< 120) ||| ((0xfffffff00000000 <<< 60) ||| 0x0)))),
    (((((((((0x7 <<< 60) ||| 0x80fcff01f9fe03f) <<< 60) ||| 0x3fc07e7f80fcff0) <<< 180) ||| ((((0x1f9fe03f3fc07e7 <<< 60) ||| 0xf80fcff01f9fe03) <<< 60) ||| 0xf3fc07e7f80fcff)) <<< 360) ||| ((((((0x1f9fe03f3fc07e <<< 60) ||| 0x7f80fcff01f9fe0) <<< 60) ||| 0x3f3fc07e7f80fcf) <<< 180) ||| ((((0xf01f9fe03f3fc07 <<< 60) ||| 0xe7f80fcff01f9fe) <<< 60) ||| 0x3f3fc07e7f80fc))), ((((((((0x3fffffffffff000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x7fffffff <<< 60) ||| 0xfffe00000000000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0xf) <<< 60) ||| 0xffffffffffc0000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))),
    (((((((((0x7 <<< 60) ||| 0xff00fffe01fffc0) <<< 60) ||| 0x3fff807fff00fff) <<< 180) ||| ((((0xe01fffc03fff807 <<< 60) ||| 0xfff00fffe01fffc) <<< 60) ||| 0x3fff807fff00ff)) <<< 360) ||| ((((((0xfe01fffc03fff80 <<< 60) ||| 0x7fff00fffe01fff) <<< 60) ||| 0xc03fff807fff00f) <<< 180) ||| ((((0xffe01fffc03fff8 <<< 60) ||| 0x7fff00fffe01ff) <<< 60) ||| 0xfc03fff807fff00))), ((((((((0x1fffff <<< 60) ||| 0xc00000000000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x3fffff80000000) <<< 60) ||| 0x0)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x7fffff0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))]

def g118C : List ColumnInfo := [(2,0,116,0,5), (4,0,114,0,5), (16,0,102,0,5), (32,0,86,0,5)]

def g118D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0

def g118L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g118D6)
  | _ => emptyPacking

def g118I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none

def g118 : Forest := ⟨118, 6, fun i => (g118Y[i]?).getD (0,0), g118C, [[]], g118L, g118I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6n0 : block g118 6 0 1 = true := by decide +kernel

theorem g118B6 : block g118 6 0 1 = true := g118P6n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g118 0 0 0 = true)
  · exact (rfl : block g118 1 0 0 = true)
  · exact (rfl : block g118 2 0 0 = true)
  · exact (rfl : block g118 3 0 0 = true)
  · exact (rfl : block g118 4 0 0 = true)
  · exact (rfl : block g118 5 0 0 = true)
  · exact g118B6

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K110) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := lower_forest (g:=g118) (i:=0) (hints:=17957968) (before_sound K110 V110) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K118 := extendKnown K110 7 [(118,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V110 low118 (by decide +kernel)

def g122Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0xaaaedeaabb7aaae) <<< 60) ||| 0xdeaabb7aaaedeaa) <<< 180) ||| ((((0xbb7aaaedeaabb7a <<< 60) ||| 0xaaedeaabb7aaaed) <<< 60) ||| 0xeaabb7aaaedeaab)) <<< 360) ||| ((((((0xb7aaaedeaabb7aa <<< 60) ||| 0xaedeaabb7aaaede) <<< 60) ||| 0xaabb7aaaedeaabb) <<< 180) ||| ((((0x7aaaedeaabb7aaa <<< 60) ||| 0xedeaabb7aaaedea) <<< 60) ||| 0xabb7aaaedeaabb7))), ((((((((0x3ff <<< 60) ||| 0xfff00000000000f) <<< 60) ||| 0xffffc0000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x3fffff00)) <<< 300) ||| ((((((0xfffffc <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x3fffff0000000 <<< 60) ||| 0xfffffc00000)))),
    (0x0, 0x0),
    (((((((((0x3 <<< 60) ||| 0xcccb6f332dbcccb) <<< 60) ||| 0x6f332dbcccb6f33) <<< 180) ||| ((((0x2dbcccb6f332dbc <<< 60) ||| 0xccb6f332dbcccb6) <<< 60) ||| 0xf332dbcccb6f332)) <<< 360) ||| ((((((0xdbcccb6f332dbcc <<< 60) ||| 0xcb6f332dbcccb6f) <<< 60) ||| 0x332dbcccb6f332d) <<< 180) ||| ((((0xbcccb6f332dbccc <<< 60) ||| 0xb6f332dbcccb6f3) <<< 60) ||| 0x32dbcccb6f332db))), ((((((((0xfffffc000000000 <<< 60) ||| 0xfffffc00) <<< 60) ||| 0x3fffff0) <<< 180) ||| ((((0xfffff <<< 60) ||| 0xc00000000000000) <<< 60) ||| 0xfffffc0000000)) <<< 300) ||| ((((((0x3fffff000000 <<< 60) ||| 0xfffffc0000) <<< 60) ||| 0xfff) <<< 120) ||| ((0xffc00000000003f <<< 60) ||| 0xffff00000000000)))),
    (((((((((0x2 <<< 60) ||| 0xf0f38bc3ce2f0f3) <<< 60) ||| 0x8bc3ce2f0f38bc3) <<< 180) ||| ((((0xce2f0f38bc3ce2f <<< 60) ||| 0xf38bc3ce2f0f38) <<< 60) ||| 0xbc3ce2f0f38bc3c)) <<< 360) ||| ((((((0xe2f0f38bc3ce2f0 <<< 60) ||| 0xf38bc3ce2f0f38b) <<< 60) ||| 0xc3ce2f0f38bc3ce) <<< 180) ||| ((((0x2f0f38bc3ce2f0f <<< 60) ||| 0x38bc3ce2f0f38bc) <<< 60) ||| 0x3ce2f0f38bc3ce2))), ((((((((0xffff <<< 60) ||| 0xfc00000ffffffff) <<< 60) ||| 0xffffffffc000000) <<< 180) ||| ((((0x0 <<< 60) ||| 0xfffffc000) <<< 60) ||| 0xfffffffffffff)) <<< 300) ||| ((((((0xfffc00000000000 <<< 60) ||| 0x0) <<< 60) ||| 0xfffffc00000fff) <<< 120) ||| ((0xfffffffffffffc0 <<< 60) ||| 0x0)))),
    (((((((((0x4 <<< 60) ||| 0xff03f3fc0fcff03) <<< 60) ||| 0xf3fc0fcff03f3fc) <<< 180) ||| ((((0xfcff03f3fc0fcf <<< 60) ||| 0xf03f3fc0fcff03f) <<< 60) ||| 0x3fc0fcff03f3fc0)) <<< 360) ||| ((((((0xfcff03f3fc0fcff <<< 60) ||| 0x3f3fc0fcff03f3) <<< 60) ||| 0xfc0fcff03f3fc0f) <<< 180) ||| ((((0xcff03f3fc0fcff0 <<< 60) ||| 0x3f3fc0fcff03f3f) <<< 60) ||| 0xc0fcff03f3fc0fc))), ((((((((0xffff <<< 60) ||| 0xfffffff00000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0xfffffffff) <<< 60) ||| 0xff0000000000000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0xfffffffffff000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))),
    (((((((((0xfffc03fff00fffc <<< 60) ||| 0x3fff00fffc03ff) <<< 60) ||| 0xf00fffc03fff00f) <<< 180) ||| ((((0xffc03fff00fffc0 <<< 60) ||| 0x3fff00fffc03fff) <<< 60) ||| 0xfffc03fff00ff)) <<< 300) ||| ((((((0xfc03fff00fffc03 <<< 60) ||| 0xfff00fffc03fff0) <<< 60) ||| 0xfffc03fff00fff) <<< 120) ||| ((0xc03fff00fffc03f <<< 60) ||| 0xff00fffc03fff00))), ((((((((0xfffffffffff0000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 180) ||| ((((0xfffff <<< 60) ||| 0xffffff000000000) <<< 60) ||| 0x0)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0xffffffffff) <<< 60) ||| 0xf00000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))]

def g122C : List ColumnInfo := [(0,16,42,64,5), (2,0,120,0,4), (8,0,114,0,5), (16,0,106,0,5), (32,0,90,0,4), (64,0,42,0,4), (64,16,42,0,4)]

def g122D4 (j : Nat) : Nat := if j = 0 then 0x5d85503 else 0

def g122D5 (j : Nat) : Nat := if j = 0 then 0x190808fd03 else 0

def g122D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0

def g122L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g122D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g122D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g122D6)
  | _ => emptyPacking

def g122I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => some ((0x0 >>> (1 * (tag % 1))) &&& 1, 0)
  | 6, tag => some ((0x0 >>> (1 * (tag % 1))) &&& 1, 0)
  | _, _ => none

def g122 : Forest := ⟨122, 6, fun i => (g122Y[i]?).getD (0,0), g122C, [[]], g122L, g122I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P4n0 : block g122 4 0 1 = true := by decide +kernel

theorem g122B4 : block g122 4 0 1 = true := g122P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P5n0 : block g122 5 0 1 = true := by decide +kernel

theorem g122B5 : block g122 5 0 1 = true := g122P5n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P6n0 : block g122 6 0 1 = true := by decide +kernel

theorem g122B6 : block g122 6 0 1 = true := g122P6n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122T : checkedTables g122 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g122 0 0 0 = true)
  · exact (rfl : block g122 1 0 0 = true)
  · exact (rfl : block g122 2 0 0 = true)
  · exact (rfl : block g122 3 0 0 = true)
  · exact g122B4
  · exact g122B5
  · exact g122B6

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122G : graphValid g122 (boundsBefore K118) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 7 := lower_forest (g:=g122) (i:=0) (hints:=18223152) (before_sound K118 V118) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K122 := extendKnown K118 7 [(122,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V118 low122 (by decide +kernel)

def g124Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (((((((((0x7 <<< 60) ||| 0xaaaedeaabb7aaae) <<< 60) ||| 0xdeaabb7aaaedeaa) <<< 180) ||| ((((0xbb7aaaedeaabb7a <<< 60) ||| 0xaaedeaabb7aaaed) <<< 60) ||| 0xeaabb7aaaedeaab)) <<< 360) ||| ((((((0xb7aaaedeaabb7aa <<< 60) ||| 0xaedeaabb7aaaede) <<< 60) ||| 0xaabb7aaaedeaabb) <<< 180) ||| ((((0x7aaaedeaabb7aaa <<< 60) ||| 0xedeaabb7aaaedea) <<< 60) ||| 0xabb7aaaedeaabb7))), ((((((((0xfffffc00000f <<< 60) ||| 0xffffc0000000000) <<< 60) ||| 0x0) <<< 120) ||| ((0xff <<< 60) ||| 0xfffc00000fffffc)) <<< 240) ||| ((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0xfffffc0 <<< 60) ||| 0xfffffc00000)))),
    (((((((((0x2 <<< 60) ||| 0xcccb6b332dacccb) <<< 60) ||| 0x6b332dacccb6b33) <<< 180) ||| ((((0x2dacccb6b332dac <<< 60) ||| 0xccb6b332dacccb6) <<< 60) ||| 0xb332dacccb6b332)) <<< 360) ||| ((((((0xdacccb6b332dacc <<< 60) ||| 0xcb6b332dacccb6b) <<< 60) ||| 0x332dacccb6b332d) <<< 180) ||| ((((0xacccb6b332daccc <<< 60) ||| 0xb6b332dacccb6b3) <<< 60) ||| 0x32dacccb6b332da))), ((((((((0xfffffc000000000 <<< 60) ||| 0xfffffc00) <<< 60) ||| 0xfffffffffff0) <<< 180) ||| ((((0xfffff <<< 60) ||| 0xc00000000000000) <<< 60) ||| 0xfffffc00000ff)) <<< 300) ||| ((((((0xfffffffff000000 <<< 60) ||| 0xfffffc0000) <<< 60) ||| 0xfff) <<< 120) ||| ((0xffc00000fffffff <<< 60) ||| 0xffff00000000000)))),
    (((((((((0x3 <<< 60) ||| 0xf0f38fc3ce3f0f3) <<< 60) ||| 0x8fc3ce3f0f38fc3) <<< 180) ||| ((((0xce3f0f38fc3ce3f <<< 60) ||| 0xf38fc3ce3f0f38) <<< 60) ||| 0xfc3ce3f0f38fc3c)) <<< 360) ||| ((((((0xe3f0f38fc3ce3f0 <<< 60) ||| 0xf38fc3ce3f0f38f) <<< 60) ||| 0xc3ce3f0f38fc3ce) <<< 180) ||| ((((0x3f0f38fc3ce3f0f <<< 60) ||| 0x38fc3ce3f0f38fc) <<< 60) ||| 0x3ce3f0f38fc3ce3))), ((((((((0xffff <<< 60) ||| 0xfc00000ffffffff) <<< 60) ||| 0xfff000000000000) <<< 180) ||| ((((0x0 <<< 60) ||| 0xfffffc000) <<< 60) ||| 0xfffffffffff00)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0xfffffc00000fff) <<< 120) ||| ((0xffffffff0000000 <<< 60) ||| 0x0)))),
    (((((((((0x4 <<< 60) ||| 0xff03f3fc0fcff03) <<< 60) ||| 0xf3fc0fcff03f3fc) <<< 180) ||| ((((0xfcff03f3fc0fcf <<< 60) ||| 0xf03f3fc0fcff03f) <<< 60) ||| 0x3fc0fcff03f3fc0)) <<< 360) ||| ((((((0xfcff03f3fc0fcff <<< 60) ||| 0x3f3fc0fcff03f3) <<< 60) ||| 0xfc0fcff03f3fc0f) <<< 180) ||| ((((0xcff03f3fc0fcff0 <<< 60) ||| 0x3f3fc0fcff03f3f) <<< 60) ||| 0xc0fcff03f3fc0fc))), ((((((((0xffff <<< 60) ||| 0xfffffff00000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0xfffffffff) <<< 60) ||| 0xff0000000000000)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0xfffffffffff000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))),
    (((((((((0xfffc03fff00fffc <<< 60) ||| 0x3fff00fffc03ff) <<< 60) ||| 0xf00fffc03fff00f) <<< 180) ||| ((((0xffc03fff00fffc0 <<< 60) ||| 0x3fff00fffc03fff) <<< 60) ||| 0xfffc03fff00ff)) <<< 300) ||| ((((((0xfc03fff00fffc03 <<< 60) ||| 0xfff00fffc03fff0) <<< 60) ||| 0xfffc03fff00fff) <<< 120) ||| ((0xc03fff00fffc03f <<< 60) ||| 0xff00fffc03fff00))), ((((((((0xfffffffffff0000 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 180) ||| ((((0xfffff <<< 60) ||| 0xffffff000000000) <<< 60) ||| 0x0)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0xffffffffff) <<< 60) ||| 0xf00000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0))))]

def g124C : List ColumnInfo := [(0,8,84,32,5), (4,0,120,0,4), (8,0,116,0,5), (16,0,108,0,5), (32,0,84,0,4), (32,8,84,0,4), (64,0,60,0,4)]

def g124D4 (j : Nat) : Nat := if j = 0 then 0x5b89504 else 0

def g124D5 (j : Nat) : Nat := if j = 0 then 0x190808fd04 else 0

def g124D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0

def g124L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g124D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g124D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g124D6)
  | _ => emptyPacking

def g124I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => some ((0x0 >>> (1 * (tag % 1))) &&& 1, 0)
  | 6, tag => some ((0x0 >>> (1 * (tag % 1))) &&& 1, 0)
  | _, _ => none

def g124 : Forest := ⟨124, 6, fun i => (g124Y[i]?).getD (0,0), g124C, [[]], g124L, g124I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P4n0 : block g124 4 0 1 = true := by decide +kernel

theorem g124B4 : block g124 4 0 1 = true := g124P4n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P5n0 : block g124 5 0 1 = true := by decide +kernel

theorem g124B5 : block g124 5 0 1 = true := g124P5n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P6n0 : block g124 6 0 1 = true := by decide +kernel

theorem g124B6 : block g124 6 0 1 = true := g124P6n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124T : checkedTables g124 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g124 0 0 0 = true)
  · exact (rfl : block g124 1 0 0 = true)
  · exact (rfl : block g124 2 0 0 = true)
  · exact (rfl : block g124 3 0 0 = true)
  · exact g124B4
  · exact g124B5
  · exact g124B6

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124G : graphValid g124 (boundsBefore K122) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low124 : Lower true (varsX 124) (graphGoal 124) 7 := lower_forest (g:=g124) (i:=0) (hints:=35804160) (before_sound K122 V122) g124G g124T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K124 := extendKnown K122 7 [(124,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V124 : Known true K124 := extend_ok (m:=124) V122 low124 (by decide +kernel)

def g126Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (((((((((0x5 <<< 60) ||| 0x555555b56adbaaa) <<< 60) ||| 0xaaab6ad5b755555) <<< 180) ||| ((((0x56d5ab6eaaaaaad <<< 60) ||| 0xab56dd555555b56) <<< 60) ||| 0xadbaaaaaab6ad5b)) <<< 360) ||| ((((((0x75555556d5ab6ea <<< 60) ||| 0xaaaaadab56dd555) <<< 60) ||| 0x555b56adbaaaaaa) <<< 180) ||| ((((0xb6ad5b75555556d <<< 60) ||| 0x5ab6eaaaaaadab5) <<< 60) ||| 0x6dd555555b56adb))), ((((((0xffffffffffff <<< 60) ||| 0xe00000000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0xffffff)) <<< 180) ||| ((((0xffffffe00000000 <<< 60) ||| 0x3ffffffffff) <<< 60) ||| 0xff8000000000000))),
    (((((((((0x6 <<< 60) ||| 0x666666d9b36eccc) <<< 60) ||| 0xcccdb366dd99999) <<< 180) ||| ((((0x9b66cdbb3333336 <<< 60) ||| 0xcd9b76666666d9b) <<< 60) ||| 0x36eccccccdb366d)) <<< 360) ||| ((((((0xd999999b66cdbb3 <<< 60) ||| 0x333336cd9b76666) <<< 60) ||| 0x666d9b36ecccccc) <<< 180) ||| ((((0xdb366dd999999b6 <<< 60) ||| 0x6cdbb3333336cd9) <<< 60) ||| 0xb76666666d9b36e))), ((((((0x3f <<< 60) ||| 0xfffffffffff8000) <<< 60) ||| 0xffffff) <<< 180) ||| ((((0xfffffffffffffff <<< 60) ||| 0xffffc0000000000) <<< 60) ||| 0x0))),
    (((((((((0x7 <<< 60) ||| 0x8787871e3c73f0f) <<< 60) ||| 0xf0e3c78e7e1e1e) <<< 180) ||| ((((0x1c78f1cfc3c3c38 <<< 60) ||| 0xf1e39f8787871e3) <<< 60) ||| 0xc73f0f0f0e3c78e)) <<< 360) ||| ((((((0x7e1e1e1c78f1cfc <<< 60) ||| 0x3c3c38f1e39f878) <<< 60) ||| 0x7871e3c73f0f0f0) <<< 180) ||| ((((0xe3c78e7e1e1e1c7 <<< 60) ||| 0x8f1cfc3c3c38f1e) <<< 60) ||| 0x39f8787871e3c73))), ((((((((0x7 <<< 60) ||| 0xffffffffffff000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x7fffffffff) <<< 60) ||| 0xfff000000000000)) <<< 360) ||| ((((((0x3f <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffff000000) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0)))),
    (((((((((0x7 <<< 60) ||| 0xf807f81fc07cff0) <<< 60) ||| 0xff03f80f9fe01f) <<< 180) ||| ((((0xe07f01f3fc03fc0 <<< 60) ||| 0xfe03e7f807f81fc) <<< 60) ||| 0x7cff00ff03f80f)) <<< 360) ||| ((((((0x9fe01fe07f01f3f <<< 60) ||| 0xc03fc0fe03e7f80) <<< 60) ||| 0x7f81fc07cff00ff) <<< 180) ||| ((((0x3f80f9fe01fe07 <<< 60) ||| 0xf01f3fc03fc0fe0) <<< 60) ||| 0x3e7f807f81fc07c))), ((((((((0x1fffff <<< 60) ||| 0xfffffffc0000000) <<< 60) ||| 0x7fffffffff) <<< 120) ||| ((0xfffffffffffffff <<< 60) ||| 0xfffffffffffffc0)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))),
    (((((((((0x7 <<< 60) ||| 0xfff8001fff80fff) <<< 60) ||| 0xf0003fff01fffe0) <<< 180) ||| ((((0x7ffe03fffc000 <<< 60) ||| 0xfffc07fff8001ff) <<< 60) ||| 0xf80ffff0003fff0)) <<< 360) ||| ((((((0x1fffe0007ffe03f <<< 60) ||| 0xffc000fffc07fff) <<< 60) ||| 0x8001fff80ffff00) <<< 180) ||| ((((0x3fff01fffe0007 <<< 60) ||| 0xffe03fffc000fff) <<< 60) ||| 0xc07fff8001fff80))), ((((((((0x1fffff <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffff8000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 300) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)))),
    (((((((((0x7 <<< 60) ||| 0xffffffe00000fff) <<< 60) ||| 0xffffc00001fffff) <<< 180) ||| ((((0xff800003fffffff <<< 60) ||| 0x7ffffffe00) <<< 60) ||| 0xfffffffc0000)) <<< 360) ||| ((((((0x1fffffff800003f <<< 60) ||| 0xffffff000007fff) <<< 60) ||| 0xfffe00000ffffff) <<< 180) ||| ((((0xfc00001fffffff8 <<< 60) ||| 0x3fffffff000) <<< 60) ||| 0x7ffffffe00000))), ((((((((0x7 <<< 60) ||| 0xfffffffffffffff) <<< 60) ||| 0xfffffffffe00000) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0))))]

def g126C : List ColumnInfo := [(0,8,84,34,6), (0,16,42,68,6), (2,0,124,0,7), (2,8,84,32,5), (4,0,122,0,7), (4,16,42,64,5), (6,0,120,0,4), (8,0,118,0,7), (10,0,116,0,5), (12,0,114,0,5), (16,0,110,0,7), (18,0,108,0,5), (20,0,106,0,5), (24,0,102,0,5), (26,0,100,0,4), (28,0,98,0,4), (32,0,94,0,7), (32,8,84,2,5), (34,0,84,0,4), (34,8,84,0,4), (36,0,90,0,4), (40,0,86,0,5), (42,0,84,0,4), (48,0,78,0,4), (64,0,62,0,7), (64,16,42,4,5), (66,0,60,0,4), (68,0,42,0,4), (68,16,42,0,4), (72,0,54,0,4), (80,0,46,0,5), (84,0,42,0,4)]

def g126D5 (j : Nat) : Nat := if j = 0 then ((((((((0x18040 <<< 60) ||| 0x80204e9109e) <<< 60) ||| 0x364e84d950c03c6) <<< 180) ||| ((((0x8214541534f2618 <<< 60) ||| 0x515254538d51515) <<< 60) ||| 0x81914d3a1751505)) <<< 360) ||| ((((((0x412b38e11589904 <<< 60) ||| 0xe3545455644078e) <<< 60) ||| 0x5150559101e3545) <<< 180) ||| ((((0x59514407cc51505 <<< 60) ||| 0x45101e394559504) <<< 60) ||| 0x407cc5151541101))) else 0

def g126D6 (j : Nat) : Nat := if j = 0 then ((((((((((((((0x38004140210e520 <<< 60) ||| 0x4000080b1020310) <<< 120) ||| ((0x23830c818e0d8cb <<< 60) ||| 0x5320a3a38601ec3)) <<< 180) ||| ((((0x800863830105008 <<< 60) ||| 0x426041003008e02) <<< 60) ||| 0x3b848418d8cb532)) <<< 420) ||| ((((((0x82744100001022 <<< 60) ||| 0x620c41898908b3b) <<< 120) ||| ((0x10a38702622a195 <<< 60) ||| 0x4f8bc947c583406)) <<< 180) ||| ((((0x8e0c9c0b885160d <<< 60) ||| 0x10c809c0b89860) <<< 60) ||| 0x321104003800438))) <<< 840) ||| ((((((((0x410f8e01060080 <<< 60) ||| 0x23a302622a18983) <<< 120) ||| ((0x4040e0d8c280842 <<< 60) ||| 0x260b0d01400982)) <<< 180) ||| ((((0x2f888818908b <<< 60) ||| 0x3b10800b0981062) <<< 60) ||| 0x620163820003026)) <<< 420) ||| ((((((0x24a02104058340c <<< 60) ||| 0x500d40bc680006) <<< 120) ||| ((0x3800414021 <<< 60) ||| 0xe0804380c10982)) <<< 180) ||| ((((0x3808e8d0c09f513 <<< 60) ||| 0xe201c160b016300) <<< 60) ||| 0x898214021038004)))) <<< 1620) ||| ((((((((((0x140e020020c0984 <<< 60) ||| 0x3008c09843808e1) <<< 120) ||| ((0x501062608e02382 <<< 60) ||| 0x10e0984382e2c2)) <<< 180) ||| ((((0x8262055ce0b0984 <<< 60) ||| 0xc38068993820626) <<< 60) ||| 0xc10802200b5538)) <<< 420) ||| ((((((0x504901cff0fe4fd <<< 60) ||| 0x8fbcfa0f94f78f3) <<< 120) ||| ((0xcee0ea4e68e3ce1 <<< 60) ||| 0xde4dd8dbcda0d6)) <<< 180) ||| ((((0x4d18cecce0cd4cb <<< 60) ||| 0x8c7cc20b44ab8a9) <<< 60) ||| 0xca60a54a28a1c9f))) <<< 780) ||| ((((((((0x9c498897c9608d <<< 60) ||| 0x482881c8007f47e) <<< 120) ||| ((0x87ac7607547186e <<< 60) ||| 0xc6d06c46b860c60)) <<< 180) ||| ((((0x5e45a859c59058 <<< 60) ||| 0x455852c5004d44b) <<< 60) ||| 0x849c3e03c43a837)) <<< 360) ||| ((((((0xc3503042d82bc29 <<< 60) ||| 0x27423821c2001d) <<< 60) ||| 0x41a80cc09006404) <<< 180) ||| ((((0x802c0013f5c2165 <<< 60) ||| 0x167eb8c0ca2e7d4) <<< 60) ||| 0x585925dda490b24))))) <<< 3240) ||| ((((((((((((0xb3f5d2164967eb8 <<< 60) ||| 0x42c92eed4685925) <<< 120) ||| ((0xbdae90b24b7b5c2 <<< 60) ||| 0x16497b70ba8a92f)) <<< 180) ||| ((((0x6d1751525edc2ca <<< 60) ||| 0x2a4b375d236457b) <<< 60) ||| 0xb0ba8a8acfd7191)) <<< 420) ||| ((((((0x905bf40ea320b3f <<< 60) ||| 0x5d216417bd03a8a) <<< 120) ||| ((0x82e7e1651505edc <<< 60) ||| 0x2e92a0bdb459254)) <<< 180) ||| ((((0x175ea2c0c9a6dd3 <<< 60) ||| 0x5819349faeb0326) <<< 60) ||| 0x93f5c6064d3cf03))) <<< 780) ||| ((((((((0xa8a9a79d0751534 <<< 60) ||| 0xe1a8a92a69c7515) <<< 120) ||| ((0x54d36eb2c0c9a7 <<< 60) ||| 0x9d4581934bbaeb0)) <<< 180) ||| ((((0x3269775c6064d2e <<< 60) ||| 0xf1ba2a924fd70d9) <<< 60) ||| 0x514bec2eb2a29bd)) <<< 360) ||| ((((((0x85d654527f03aca <<< 60) ||| 0x8a7b61751514e5a) <<< 60) ||| 0x8a92a29cd515154) <<< 180) ||| ((((0x539ea2a0a8a6bd4 <<< 60) ||| 0x581914dea2b0322) <<< 60) ||| 0x93f5d606453cf03)))) <<< 1620) ||| ((((((((((0xa688a79d064d114 <<< 60) ||| 0x9fc2eb2a09be81d) <<< 120) ||| ((0x65413dd03a8a825 <<< 60) ||| 0xde3745504e7a8a8)) <<< 180) ||| ((((0xaa097e85d054139 <<< 60) ||| 0xca2a0a826ed3589) <<< 60) ||| 0x904dda2b132093b)) <<< 420) ||| ((((((0x5d626412f713a08 <<< 60) ||| 0x89dde37455029fc) <<< 120) ||| ((0xcea2a033f5d3654 <<< 60) ||| 0x67f23aca80e7d4)) <<< 180) ||| ((((0x559501eea8a8aa0 <<< 60) ||| 0x37e91d05407bca2) <<< 60) ||| 0xa0a80f692541501))) <<< 780) ||| ((((((((0xdea2bb2203be417 <<< 60) ||| 0x644067ebaec880c) <<< 120) ||| ((0xff75591019faeab <<< 60) ||| 0x2203af515644077)) <<< 180) ||| ((((0xa8aac880ef90559 <<< 60) ||| 0x101beeea8a2037d) <<< 60) ||| 0x5d514407daa2a28)) <<< 360) ||| ((((((0x80ef76545101dea <<< 60) ||| 0xca8a203fc415144) <<< 60) ||| 0x7ca9a22880df97) <<< 180) ||| ((((0x541101f728a8220 <<< 60) ||| 0x3bed95044077cb2) <<< 60) ||| 0xa0880ff11541101)))))) else 0

def g126D7 (j : Nat) : Nat := if j = 0 then ((((((((((((((0x70c <<< 60) ||| 0x10481053962810d) <<< 120) ||| ((0x4283a5481010100 <<< 60) ||| 0x69c3664a2a48107)) <<< 240) ||| ((((0x304c822042d8274 <<< 60) ||| 0x80ace1c2234408) <<< 120) ||| ((0x8034d1324453a2 <<< 60) ||| 0x439d396080f151))) <<< 480) ||| ((((((0xc3a548131020300 <<< 60) ||| 0xf3e74e5860aa387) <<< 120) ||| ((0x4a931224300e326 <<< 60) ||| 0x99161aa387c90f)) <<< 240) ||| ((((0x14032c70559e262 <<< 60) ||| 0x239c3664c30211) <<< 120) ||| ((0x62044300b35609b <<< 60) ||| 0x20283848708101)))) <<< 960) ||| ((((((((0x69a26498104e0 <<< 60) ||| 0xc73e70d5820283a) <<< 120) ||| ((0x548121020200e36 <<< 60) ||| 0x68caa0c9020e68c)) <<< 240) ||| ((((0x986042102808093 <<< 60) ||| 0x464c1363c35270f) <<< 120) ||| ((0x901c2406b8a03a5 <<< 60) ||| 0x27c98873ee09d09))) <<< 480) ||| ((((((0x49f223c480a3ee0 <<< 60) ||| 0x9d02128527488d1) <<< 120) ||| ((0x2030c17274074a1 <<< 60) ||| 0x41f204468814100)) <<< 240) ||| ((((0x79c32e0890942b3 <<< 60) ||| 0xc5c98a09871c16a) <<< 120) ||| ((0x1293c5c98a09471 <<< 60) ||| 0xc1323425278b911))))) <<< 1860) ||| ((((((((((0xe28280d3865c172 <<< 60) ||| 0x74084a4e911a282) <<< 120) ||| ((0x501ee0b9627425 <<< 60) ||| 0xa4f91223450501)) <<< 240) ||| ((((0xc540800caaa0e00 <<< 60) ||| 0x438e0a5020283c5) <<< 120) ||| ((0x88101010069c36e <<< 60) ||| 0xc14541473e70db))) <<< 480) ||| ((((((0x829405078b10101 <<< 60) ||| 0x6b83050890881) <<< 120) ||| ((0x20a124e38305a84 <<< 60) ||| 0xa4e1e2c48504c3a)) <<< 240) ||| ((((0x71c18264684a4f1 <<< 60) ||| 0x6242828001e70db) <<< 120) ||| ((0x830528100a120a0 <<< 60) ||| 0x2ce1a284c20218c)))) <<< 900) ||| ((((((((0x16284e80a0f1022 <<< 60) ||| 0x3440808038a1222) <<< 120) ||| ((0x9c3220439c73e0a <<< 60) ||| 0x1120a85670b1312)) <<< 240) ||| ((((0x134d382c4c95014 <<< 60) ||| 0x1c243840401ae0c) <<< 120) ||| ((0x132444843840a0a <<< 60) ||| 0x2cf0a8e0443649))) <<< 420) ||| ((((((0x5470808634e0c13 <<< 60) ||| 0x25408030505017e) <<< 120) ||| ((0x286a4f921001c62 <<< 60) ||| 0x7021aa100033860)) <<< 180) ||| ((((0x9900c1010ee0c16 <<< 60) ||| 0xa03b54a4e1e2c48) <<< 60) ||| 0x504d3ae0c13a1aa))))) <<< 3780) ||| ((((((((((((0x5278b101c282800 <<< 60) ||| 0x1e7ce3820283868) <<< 120) ||| ((0xb10242040401c6c <<< 60) ||| 0xd3830a83051cf9c)) <<< 240) ||| ((((0x3669c10141c3458 <<< 60) ||| 0x90808038f9c36e0) <<< 120) ||| ((0xc2ace18284840a0 <<< 60) ||| 0xa038f9c34e0c6a4))) <<< 480) ||| ((((((0xe1a204060a0a138 <<< 60) ||| 0xfd826c080e542b3) <<< 120) ||| ((0xc7890e14038e582 <<< 60) ||| 0xe589b020ab3c70b)) <<< 240) ||| ((((0x121c2420602260b <<< 60) ||| 0x13602838688121c) <<< 120) ||| ((0x2040401c5093020 <<< 60) ||| 0x9c3031cc16284c9)))) <<< 960) ||| ((((((((0x30141c344870808 <<< 60) ||| 0x38b1426c082ace) <<< 120) ||| ((0x18284840a02038b <<< 60) ||| 0x1324c086a4e1a20)) <<< 240) ||| ((((0x406090c03a6852e <<< 60) ||| 0x19554a064411e98) <<< 120) ||| ((0xbd444a171081817 <<< 60) ||| 0x3f35f2cf2e77bba))) <<< 480) ||| ((((((0xc9ca2e1a6e735d1 <<< 60) ||| 0xa0acab62faff971) <<< 120) ||| ((0xeb275862ba9512a <<< 60) ||| 0x524f8a6b12a48e3)) <<< 240) ||| ((((0x4482180ff07c13b <<< 60) ||| 0x1bfcd5868a32d1) <<< 120) ||| ((0x81cba05b52cd158 <<< 60) ||| 0xca044932158fd07))))) <<< 1860) ||| ((((((((((0x1832415e09503ae <<< 60) ||| 0x16f09c03400d000) <<< 120) ||| ((0xff85945bf85945 <<< 60) ||| 0xff45945ff81945b)) <<< 240) ||| ((((0xf81945ff41945bf <<< 60) ||| 0x85925fb85925db5) <<< 120) ||| ((0x1525b78d915df51 <<< 60) ||| 0x515bf91905ff519))) <<< 480) ||| ((((((0x5bf85905ff4590 <<< 60) ||| 0x5df51505db49505) <<< 120) ||| ((0xf3c9734f349734f <<< 60) ||| 0x741734bf81934e7)) <<< 240) ||| ((((0x51534f3c9534f34 <<< 60) ||| 0x9534f741534f781) <<< 120) ||| ((0x934ff4d524ff455 <<< 60) ||| 0x24bfd9514ff5951)))) <<< 900) ||| ((((((((0x4bf59514ef51514 <<< 60) ||| 0xfbc9514fb49514f) <<< 120) ||| ((0xd45514ff41514bf <<< 60) ||| 0x81914ff41914e74)) <<< 240) ||| ((((0xd114bf59504ef51 <<< 60) ||| 0x504ff4d504ff455) <<< 120) ||| ((0x4fe41504bb8990 <<< 60) ||| 0x4ff41113ff45502))) <<< 420) ||| ((((((0xff51501fbc9501f <<< 60) ||| 0xb49501bfd9501ff) <<< 120) ||| ((0x59501bf59501fd4 <<< 60) ||| 0x5501fe41501f7cd)) <<< 180) ||| ((((0x101f74d101bfd91 <<< 60) ||| 0x1ff59101bf5910) <<< 60) ||| 0x1fd45101fe41101)))))) else 0

def g126D8 (j : Nat) : Nat := if j = 0 then ((((((((((((0x1961142a2a71e41 <<< 60) ||| 0x2208100e798c103) <<< 60) ||| 0x8a9c71641220810) <<< 120) ||| ((0xf6585b0a879222 <<< 60) ||| 0x1d65847042a2879)) <<< 300) ||| ((((((0x40e20810106584 <<< 60) ||| 0xd1c2a1e40e200b7) <<< 60) ||| 0xdc6d963042a2a71) <<< 120) ||| ((0xc51220810116996 <<< 60) ||| 0x3042a2a71e41030))) <<< 540) ||| ((((((((0x8100f7f84502a79 <<< 60) ||| 0x22219e185d140a9) <<< 60) ||| 0xc71641220810107) <<< 120) ||| ((0x19e1140a9c59220 <<< 60) ||| 0x4be185503ea2879)) <<< 240) ||| ((((0x40e208100fe185 <<< 60) ||| 0x1142a2a71c51220) <<< 120) ||| ((0x8100fe185934914 <<< 60) ||| 0x2a2a71e41030810)))) <<< 1140) ||| ((((((((((0x11e1847040d2871 <<< 60) ||| 0x64103882040419e) <<< 60) ||| 0x18c103ce30a9c71) <<< 120) ||| ((0x220810106786304 <<< 60) ||| 0xb2a71c59040c20)) <<< 300) ||| ((((((0x40438611c10a8a2 <<< 60) ||| 0x471440e2081010e) <<< 60) ||| 0x1847040ea8a2079) <<< 120) ||| ((0x408100fe18c10a <<< 60) ||| 0x8a9c71851030810))) <<< 540) ||| ((((((((0xfcf1862f157ca6 <<< 60) ||| 0x932234432798e11) <<< 60) ||| 0x922c44b07c8c612) <<< 120) ||| ((0x6180180007f517f <<< 60) ||| 0xa6bef25fe92fb49)) <<< 240) ||| ((((0x7fa2bfd05ef9a7f <<< 60) ||| 0x4d3ba69fd24fe8a) <<< 120) ||| ((0x7f413fa47fd13fe <<< 60) ||| 0x81ff44bfa05fd01))))) else 0

def g126D9 (j : Nat) : Nat := if j = 0 then 0x620a390433f else 0

def g126L : Nat → Packing
  | 5 => (11, 4, 5, 0, 0, 7, 0, g126D5)
  | 6 => (87, 3, 5, 0, 0, 12, 0, g126D6)
  | 7 => (62, 2, 5, 0, 0, 13, 0, g126D7)
  | 8 => (19, 1, 5, 0, 0, 11, 0, g126D8)
  | 9 => (1, 0, 5, 0, 0, 1, 0, g126D9)
  | _ => emptyPacking

def g126I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => some ((((0x306a800520 <<< 60) ||| 0x91004700) >>> (4 * (tag % 27))) &&& 15, 0)
  | 7, tag => some ((((((((((((((((0x1000040000 <<< 60) ||| 0x318000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x9be0000b000000)) <<< 180) ||| ((((0x0 <<< 60) ||| 0xc000000) <<< 60) ||| 0x0)) <<< 420) ||| ((((((0x0 <<< 60) ||| 0x60000046) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x24000000000000))) <<< 780) ||| ((((((((0xe5a0000000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x3a01e000000)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x780005c04d0 <<< 60) ||| 0x0) <<< 60) ||| 0x0) <<< 180) ||| ((((0x520000 <<< 60) ||| 0x0) <<< 60) ||| 0x0)))) <<< 1560) ||| ((((((((((0x10c0000000000 <<< 60) ||| 0x128000000000) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x150000 <<< 60) ||| 0xf400000000) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x1380 <<< 60) ||| 0x190) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0xc1) <<< 60) ||| 0x700000000000000))) <<< 780) ||| ((((((((0x0 <<< 60) ||| 0x0) <<< 120) ||| ((0x0 <<< 60) ||| 0x100000)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x1e0001) <<< 60) ||| 0x900000000000000)) <<< 360) ||| ((((((0x380002a0 <<< 60) ||| 0xa2000000002780) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0x110114000000) <<< 60) ||| 0x88))))) <<< 3120) ||| ((((((((((((0x4400000 <<< 60) ||| 0x160000a400) <<< 120) ||| ((0x0 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x310000000000000) <<< 60) ||| 0x90000000000000) <<< 180) ||| ((((0x800208000000000 <<< 60) ||| 0x0) <<< 60) ||| 0x4c0000000000))) <<< 780) ||| ((((((((0x160000000ac <<< 60) ||| 0x8000000000000) <<< 120) ||| ((0xa8000000000 <<< 60) ||| 0x7001a0000000)) <<< 180) ||| ((((0x11c0000 <<< 60) ||| 0x1b8067) <<< 60) ||| 0x2c04e0000000000)) <<< 360) ||| ((((((0x1f0000 <<< 60) ||| 0xa6000) <<< 60) ||| 0xac00007000000) <<< 180) ||| ((((0x0 <<< 60) ||| 0x0) <<< 60) ||| 0x0)))) <<< 1560) ||| ((((((((((0x1400a000000000 <<< 60) ||| 0x4a0000) <<< 120) ||| ((0x5000001240 <<< 60) ||| 0x0)) <<< 180) ||| ((((0x4000048000bc000 <<< 60) ||| 0x0) <<< 60) ||| 0x42000000000)) <<< 360) ||| ((((((0x3b0000000000 <<< 60) ||| 0x5500fc00e0000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x0 <<< 60) ||| 0xa0000000) <<< 60) ||| 0x350))) <<< 780) ||| ((((((((0xd8021000000000 <<< 60) ||| 0x28000000005a0) <<< 120) ||| ((0x6c <<< 60) ||| 0x0)) <<< 180) ||| ((((0x240001d00000010 <<< 60) ||| 0x0) <<< 60) ||| 0x0)) <<< 360) ||| ((((((0x0 <<< 60) ||| 0x6800000000000) <<< 60) ||| 0x0) <<< 180) ||| ((((0x230000980 <<< 60) ||| 0x0) <<< 60) ||| 0x0)))))) >>> (7 * (tag % 897))) &&& 127, 0)
  | 8, tag => some ((((((((((((((0xa00000000401a <<< 60) ||| 0xec0026c00e0000e) <<< 60) ||| 0x31000000000) <<< 120) ||| ((0x24000000 <<< 60) ||| 0x8c0000)) <<< 240) ||| ((((0x36000 <<< 60) ||| 0x2f5c0) <<< 120) ||| ((0xcc0000 <<< 60) ||| 0x60007403c0000))) <<< 540) ||| ((((((((0x0 <<< 60) ||| 0xd000000000000) <<< 60) ||| 0x440000000) <<< 120) ||| ((0x532 <<< 60) ||| 0x0)) <<< 240) ||| ((((0xa0002a005 <<< 60) ||| 0x0) <<< 120) ||| ((0x2e000000000 <<< 60) ||| 0xdc001c00003c)))) <<< 1080) ||| ((((((((((0x21000000000 <<< 60) ||| 0x329000000000) <<< 60) ||| 0x39000000034000) <<< 120) ||| ((0x25000000 <<< 60) ||| 0xb00000000000)) <<< 240) ||| ((((0x880000000 <<< 60) ||| 0x0) <<< 120) ||| ((0x3d <<< 60) ||| 0x0))) <<< 540) ||| ((((((((0x0 <<< 60) ||| 0x3a000000000000) <<< 60) ||| 0x9c00100000007cb) <<< 120) ||| ((0x19800580780007 <<< 60) ||| 0x2b0004c0480)) <<< 240) ||| ((((0x1b000000000035 <<< 60) ||| 0x542000b58200) <<< 120) ||| ((0x40000000240 <<< 60) ||| 0xc0000000))))) >>> (6 * (tag % 368))) &&& 63, 0)
  | 9, tag => some ((((((((0x30000002000000 <<< 60) ||| 0x280008004e78240) <<< 60) ||| 0x58000000e030000) <<< 120) ||| ((0x100001a000143 <<< 60) ||| 0x44800000220)) >>> (5 * (tag % 60))) &&& 31, 0)
  | _, _ => none

def g126 : Forest := ⟨126, 9, fun i => (g126Y[i]?).getD (0,0), g126C, [[]], g126L, g126I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n0 : block g126 5 0 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n2 : block g126 5 2 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n4 : block g126 5 4 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n6 : block g126 5 6 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n8 : block g126 5 8 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5n10 : block g126 5 10 1 = true := by decide +kernel

theorem g126B5 : block g126 5 0 11 = true := (@block_merge g126 5 0 6 5 (@block_merge g126 5 0 2 4 g126P5n0 (@block_merge g126 5 2 2 2 g126P5n2 g126P5n4)) (@block_merge g126 5 6 2 3 g126P5n6 (@block_merge g126 5 8 2 1 g126P5n8 g126P5n10)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n0 : block g126 6 0 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n2 : block g126 6 2 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n4 : block g126 6 4 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n6 : block g126 6 6 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n8 : block g126 6 8 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n10 : block g126 6 10 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n12 : block g126 6 12 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n14 : block g126 6 14 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n16 : block g126 6 16 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n18 : block g126 6 18 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n20 : block g126 6 20 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n22 : block g126 6 22 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n24 : block g126 6 24 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n26 : block g126 6 26 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n28 : block g126 6 28 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n30 : block g126 6 30 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n32 : block g126 6 32 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n34 : block g126 6 34 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n36 : block g126 6 36 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n38 : block g126 6 38 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n40 : block g126 6 40 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n42 : block g126 6 42 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n44 : block g126 6 44 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n46 : block g126 6 46 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n48 : block g126 6 48 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n50 : block g126 6 50 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n52 : block g126 6 52 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n54 : block g126 6 54 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n56 : block g126 6 56 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n58 : block g126 6 58 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n60 : block g126 6 60 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n62 : block g126 6 62 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n64 : block g126 6 64 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n66 : block g126 6 66 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n68 : block g126 6 68 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n70 : block g126 6 70 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n72 : block g126 6 72 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n74 : block g126 6 74 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n76 : block g126 6 76 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n78 : block g126 6 78 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n80 : block g126 6 80 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n82 : block g126 6 82 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n84 : block g126 6 84 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6n86 : block g126 6 86 1 = true := by decide +kernel

theorem g126B6 : block g126 6 0 87 = true := (@block_merge g126 6 0 44 43 (@block_merge g126 6 0 22 22 (@block_merge g126 6 0 10 12 (@block_merge g126 6 0 4 6 (@block_merge g126 6 0 2 2 g126P6n0 g126P6n2) (@block_merge g126 6 4 2 4 g126P6n4 (@block_merge g126 6 6 2 2 g126P6n6 g126P6n8))) (@block_merge g126 6 10 6 6 (@block_merge g126 6 10 2 4 g126P6n10 (@block_merge g126 6 12 2 2 g126P6n12 g126P6n14)) (@block_merge g126 6 16 2 4 g126P6n16 (@block_merge g126 6 18 2 2 g126P6n18 g126P6n20)))) (@block_merge g126 6 22 10 12 (@block_merge g126 6 22 4 6 (@block_merge g126 6 22 2 2 g126P6n22 g126P6n24) (@block_merge g126 6 26 2 4 g126P6n26 (@block_merge g126 6 28 2 2 g126P6n28 g126P6n30))) (@block_merge g126 6 32 6 6 (@block_merge g126 6 32 2 4 g126P6n32 (@block_merge g126 6 34 2 2 g126P6n34 g126P6n36)) (@block_merge g126 6 38 2 4 g126P6n38 (@block_merge g126 6 40 2 2 g126P6n40 g126P6n42))))) (@block_merge g126 6 44 22 21 (@block_merge g126 6 44 10 12 (@block_merge g126 6 44 4 6 (@block_merge g126 6 44 2 2 g126P6n44 g126P6n46) (@block_merge g126 6 48 2 4 g126P6n48 (@block_merge g126 6 50 2 2 g126P6n50 g126P6n52))) (@block_merge g126 6 54 6 6 (@block_merge g126 6 54 2 4 g126P6n54 (@block_merge g126 6 56 2 2 g126P6n56 g126P6n58)) (@block_merge g126 6 60 2 4 g126P6n60 (@block_merge g126 6 62 2 2 g126P6n62 g126P6n64)))) (@block_merge g126 6 66 10 11 (@block_merge g126 6 66 4 6 (@block_merge g126 6 66 2 2 g126P6n66 g126P6n68) (@block_merge g126 6 70 2 4 g126P6n70 (@block_merge g126 6 72 2 2 g126P6n72 g126P6n74))) (@block_merge g126 6 76 6 5 (@block_merge g126 6 76 2 4 g126P6n76 (@block_merge g126 6 78 2 2 g126P6n78 g126P6n80)) (@block_merge g126 6 82 2 3 g126P6n82 (@block_merge g126 6 84 2 1 g126P6n84 g126P6n86))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n0 : block g126 7 0 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n2 : block g126 7 2 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n4 : block g126 7 4 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n6 : block g126 7 6 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n8 : block g126 7 8 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n10 : block g126 7 10 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n12 : block g126 7 12 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n14 : block g126 7 14 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n16 : block g126 7 16 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n18 : block g126 7 18 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n20 : block g126 7 20 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n22 : block g126 7 22 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n24 : block g126 7 24 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n26 : block g126 7 26 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n28 : block g126 7 28 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n30 : block g126 7 30 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n32 : block g126 7 32 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n34 : block g126 7 34 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n36 : block g126 7 36 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n38 : block g126 7 38 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n40 : block g126 7 40 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n42 : block g126 7 42 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n44 : block g126 7 44 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n46 : block g126 7 46 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n48 : block g126 7 48 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n50 : block g126 7 50 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n52 : block g126 7 52 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n54 : block g126 7 54 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n56 : block g126 7 56 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n58 : block g126 7 58 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n60 : block g126 7 60 2 = true := by decide +kernel

theorem g126B7 : block g126 7 0 62 = true := (@block_merge g126 7 0 30 32 (@block_merge g126 7 0 14 16 (@block_merge g126 7 0 6 8 (@block_merge g126 7 0 2 4 g126P7n0 (@block_merge g126 7 2 2 2 g126P7n2 g126P7n4)) (@block_merge g126 7 6 4 4 (@block_merge g126 7 6 2 2 g126P7n6 g126P7n8) (@block_merge g126 7 10 2 2 g126P7n10 g126P7n12))) (@block_merge g126 7 14 8 8 (@block_merge g126 7 14 4 4 (@block_merge g126 7 14 2 2 g126P7n14 g126P7n16) (@block_merge g126 7 18 2 2 g126P7n18 g126P7n20)) (@block_merge g126 7 22 4 4 (@block_merge g126 7 22 2 2 g126P7n22 g126P7n24) (@block_merge g126 7 26 2 2 g126P7n26 g126P7n28)))) (@block_merge g126 7 30 16 16 (@block_merge g126 7 30 8 8 (@block_merge g126 7 30 4 4 (@block_merge g126 7 30 2 2 g126P7n30 g126P7n32) (@block_merge g126 7 34 2 2 g126P7n34 g126P7n36)) (@block_merge g126 7 38 4 4 (@block_merge g126 7 38 2 2 g126P7n38 g126P7n40) (@block_merge g126 7 42 2 2 g126P7n42 g126P7n44))) (@block_merge g126 7 46 8 8 (@block_merge g126 7 46 4 4 (@block_merge g126 7 46 2 2 g126P7n46 g126P7n48) (@block_merge g126 7 50 2 2 g126P7n50 g126P7n52)) (@block_merge g126 7 54 4 4 (@block_merge g126 7 54 2 2 g126P7n54 g126P7n56) (@block_merge g126 7 58 2 2 g126P7n58 g126P7n60)))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n0 : block g126 8 0 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n2 : block g126 8 2 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n4 : block g126 8 4 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n6 : block g126 8 6 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n8 : block g126 8 8 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n10 : block g126 8 10 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n12 : block g126 8 12 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n14 : block g126 8 14 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n16 : block g126 8 16 2 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n18 : block g126 8 18 1 = true := by decide +kernel

theorem g126B8 : block g126 8 0 19 = true := (@block_merge g126 8 0 10 9 (@block_merge g126 8 0 4 6 (@block_merge g126 8 0 2 2 g126P8n0 g126P8n2) (@block_merge g126 8 4 2 4 g126P8n4 (@block_merge g126 8 6 2 2 g126P8n6 g126P8n8))) (@block_merge g126 8 10 4 5 (@block_merge g126 8 10 2 2 g126P8n10 g126P8n12) (@block_merge g126 8 14 2 3 g126P8n14 (@block_merge g126 8 16 2 1 g126P8n16 g126P8n18))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P9n0 : block g126 9 0 1 = true := by decide +kernel

theorem g126B9 : block g126 9 0 1 = true := g126P9n0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact g126B5
  · exact g126B6
  · exact g126B7
  · exact g126B8
  · exact g126B9

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K124) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 10 := lower_forest (g:=g126) (i:=0) (hints:=17962032) (before_sound K124 V124) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end ForestCore
open ForestCore
def graph (x : Fin 6 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def coding : Fin 6 → Nat := ![1, 2, 3, 4, 5, 6]
def roots : List Sig := List.ofFn (fun i : Fin 6 => inputs.getD (coding i) zero)
def codedGraph : Sig := graphGoal 126

theorem wholeBound : Lower true roots codedGraph 10 := by
  have same : roots = varsX 126 := by decide +kernel
  rw [same];exact low126
def sampleInput (r : Row) (i : Fin 6) : Bool := bit r (inputs.getD (coding i) zero)

theorem sampledInput (r : Row) : List.ofFn (sampleInput r) = roots.map (bit r) := by
  rw [roots, List.map_ofFn]
  rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sampleCorrect : ∀ r : Row, bit r codedGraph = graph (sampleInput r) := by decide +kernel

def signedNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem binaryLower (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) :
    10 ≤ C.gates.countP (fun g => !signedNot g) := by
  have goalEq : (execute C.gates roots).getD C.output zero = codedGraph := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fit g hg).1), ← sampledInput]
    exact (comp (sampleInput r)).trans (sampleCorrect r).symm
  have out := get_rep (u := true) (execute C.gates roots) C.output
  rw [goalEq] at out
  unfold ForestCore.Repr at out
  have pg : bit 0 codedGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  have properGoal : proper codedGraph := by unfold proper; decide +kernel
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates roots fit (by simp) properGoal
    (out.resolve_right (fun h => h properGoal))
  change k ≤ C.gates.countP (fun g => !signedNot g) at hk
  rw [nrm_map (by decide +kernel : roots.all plainWord = true)] at sub
  have step := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have ready : supply true (roots.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, reach, hit, paid⟩ := contraction (observe_proper properGoal) step _ Reach.start ready
  have lower := wholeBound q bank reach hit
  omega

end Base
namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isNegGate (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem negGate_iff (g : Gate) : isNegGate g = true ↔ g.op = .not := by
  cases g with | mk o l => cases o <;> simp [isNegGate]

theorem countNeg_le (gs : List Gate)
    (u : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    gs.countP isNegGate ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have tail := ih (fun i j hi hj => Fin.ext (by
      have h := u i.succ j.succ hi hj
      exact Nat.succ.inj (congrArg Fin.val h)))
    by_cases neg : g.op = .not
    · have clear : gs.countP isNegGate = 0 := by
        apply List.countP_eq_zero.mpr
        intro k hk
        obtain ⟨i, rfl⟩ := List.get_of_mem hk
        have ne : (gs.get i).op ≠ .not := by
          intro h; have absurd := u 0 i.succ neg h
          have := congrArg Fin.val absurd
          simp at this
        cases h : isNegGate (gs.get i)
        · decide
        · exact (ne ((negGate_iff _).mp h)).elim
      simp [List.countP_cons,(negGate_iff g).mpr neg,clear]
    · simpa [List.countP_cons,negGate_iff,neg] using tail

theorem gateMonoOn (g : Gate) (h : g.op = .and ∨ g.op = .or)
    (a b : ℕ → Bool) (le : ∀ i ∈ g.inputs, a i ≤ b i) :
    g.op.eval (g.inputs.map a) ≤ g.op.eval (g.inputs.map b) := by
  rcases h with e | e
  · rw [e]; simp only [GateOp.eval,List.all_map,Function.comp_def]
    apply Bool.le_iff_imp.mpr
    intro ha
    simp_all only [List.all_eq_true,decide_eq_true_eq]
    intro i hi
    exact Bool.le_iff_imp.mp (le i hi) (ha i hi)
  · rw [e]; simp only [GateOp.eval,List.any_map,Function.comp_def]
    apply Bool.le_iff_imp.mpr
    intro ha
    simp_all only [List.any_eq_true,decide_eq_true_eq]
    obtain ⟨i,hi,ha⟩ := ha
    exact ⟨i,hi,Bool.le_iff_imp.mp (le i hi) ha⟩

theorem wiresAnti (gs : List Gate) (p : ℕ) (legal : ∀ g ∈ gs, Ok g)
    (no : ∀ g ∈ gs, g.op ≠ GateOp.not → p ∉ g.inputs)
    (unique : gs.countP isNegGate ≤ 1) :
    ∀ (A B : List Bool), A.length = B.length → p < A.length →
      A.getD p false = true → B.getD p false = false →
      (∀ i ≠ p, A.getD i false ≤ B.getD i false) →
      ((∃ g ∈ gs, g.op = GateOp.not) → ∀ i ≠ p, A.getD i false = B.getD i false) →
      ∀ i ≠ p, (wiresFrom gs A).getD i false ≤ (wiresFrom gs B).getD i false := by
  induction gs with
  | nil => intro A B _ _ _ _ le _; exact le
  | cons g gs ih =>
    intro A B lens plen ap bp le eq
    let newBit (W : List Bool) := g.op.eval (g.inputs.map fun i => W.getD i false)
    have child (h : ∃ k ∈ gs, k.op = GateOp.not) : g.op ≠ GateOp.not := by
      obtain ⟨k,hk,e⟩ := h
      have pos : 0 < gs.countP isNegGate := List.countP_pos_iff.mpr ⟨k,hk,(negGate_iff k).mpr e⟩
      intro bad
      simp only [List.countP_cons,(negGate_iff g).mpr bad,if_true] at unique
      omega
    have bit : newBit A ≤ newBit B := by
      by_cases neg : g.op = GateOp.not
      · have he := eq ⟨g,List.mem_cons_self,neg⟩
        unfold newBit
        rw [neg]
        cases hs : g.inputs with
        | nil => simp [GateOp.eval]
        | cons i ins =>
          change (!A.getD i false) ≤ !B.getD i false
          by_cases hn : i = p
          · rw [hn,ap,bp]; decide
          · rw [he i hn]
      · have hg := (legal g List.mem_cons_self).1
        have ops : g.op = .and ∨ g.op = .or := by
          rcases hg with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (neg h).elim
        exact gateMonoOn g ops _ _ (fun i hi => le i (fun e => no g List.mem_cons_self neg (e ▸ hi)))
    have ut : gs.countP isNegGate ≤ 1 := by
      rw [List.countP_cons] at unique
      split at unique <;> omega
    apply ih (fun k hk => legal k (List.mem_cons_of_mem _ hk))
      (fun k hk => no k (List.mem_cons_of_mem _ hk)) ut
      (A ++ [newBit A]) (B ++ [newBit B]) (by simp [lens]) (by simp;omega)
      (by rw [List.getD_append _ _ _ _ plen];exact ap)
      (by rw [List.getD_append _ _ _ _ (lens ▸ plen)];exact bp)
    · intro i nei
      by_cases h : i = A.length
      · rw [h,getD_snoc_eq,lens,getD_snoc_eq];exact bit
      · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)];exact le i nei
    · intro ex i nei
      have he := eq (by obtain ⟨k,hk,hn⟩ := ex;exact ⟨k,List.mem_cons_of_mem _ hk,hn⟩)
      by_cases h : i = A.length
      · rw [h,getD_snoc_eq,lens,getD_snoc_eq]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        exact he j (fun e => no g List.mem_cons_self (child ex) (e ▸ hj))
      · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)];exact he i nei

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isBinaryGate (g : Gate) : Bool := !isNegGate g
abbrev binaryCount (gs : List Gate) := gs.countP isBinaryGate

theorem binary_of_ne {g : Gate} (ne : g.op ≠ .not) : isBinaryGate g = true := by
  cases h : isNegGate g
  · simp [isBinaryGate,h]
  · exact (ne ((negGate_iff _).mp h)).elim

theorem simp_binary_le (g : Gate) (m : ℕ) (ins : List Stat) :
    binaryCount (simplify g.op m ins).1.toList ≤ (if isBinaryGate g then 1 else 0) := by
  by_cases neg : g.op = .not
  · rw [show isBinaryGate g = false by simp [isBinaryGate,(negGate_iff g).mpr neg]]
    rw [neg]
    cases ins with
    | nil => simp [binaryCount,simplify,simpNot]
    | cons s t => cases s <;> simp [binaryCount,simplify,simpNot,isBinaryGate,isNegGate]
  · have flag := binary_of_ne neg
    rw [flag]
    exact le_trans List.countP_le_length (toList_length_le _)

theorem bin_step (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    binaryCount (elimStep n acc g).2 ≤ binaryCount acc.2 + (if isBinaryGate g then 1 else 0) := by
  simp only [elimStep,binaryCount,List.countP_append]
  exact Nat.add_le_add_left (simp_binary_le _ _ _) _

theorem bin_all (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    binaryCount (elim n gs acc).2 ≤ binaryCount acc.2 + binaryCount gs := by
  induction gs generalizing acc with
  | nil => simp [elim,binaryCount]
  | cons g gs ih =>
    have a := ih (elimStep n acc g)
    have b := bin_step n acc g
    rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
    omega

theorem bin_save (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, g.op ≠ .not ∧ k ∈ g.inputs) →
    binaryCount (elim n gs acc).2 + 1 ≤ binaryCount acc.2 + binaryCount gs := by
  induction gs with
  | nil => intro acc _ _ _ h; simpa using h
  | cons g gs ih =>
    intro acc ok hk hc hex
    by_cases hit : g.op ≠ .not ∧ k ∈ g.inputs
    · obtain ⟨c,hc⟩ := hc
      have hg := ok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hg.1.1
        · simpa using hg.1.2
        · intro h; simpa using hg.2 h
        · exact ⟨c,List.mem_map.2 ⟨k,hit.2,hc⟩⟩
      have same : (elimStep n acc g).2 = acc.2 := by simp only [elimStep,hnone];simp
      have after := bin_all n gs (elimStep n acc g)
      rw [same] at after
      have flag := binary_of_ne hit.1
      rw [elim_cons];simp only [binaryCount,List.countP_cons,flag,if_true] at *
      omega
    · have rest : ∃ g ∈ gs, g.op ≠ .not ∧ k ∈ g.inputs := by
        obtain ⟨g',hmem,props⟩ := hex
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact (hit props).elim
        · exact ⟨_,hmem,props⟩
      have step := bin_step n acc g
      have after := ih (elimStep n acc g) (fun j hj => ok j (List.mem_cons_of_mem _ hj))
        (by simp [elimStep];omega)
        (by obtain ⟨c,hc⟩ := hc; refine ⟨c,?_⟩;simp only [elimStep];rw [getD_snoc_ne _ _ _ _ (by omega)];exact hc)
        rest
      rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
      omega

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem needsPositiveReader (n : ℕ) (C : Circuit) (legal : FanInTwo C)
    (unique : C.gates.countP isNegGate ≤ 1) (hout : C.output ≠ n)
    (y : Fin n → Bool)
    (up : C.eval (List.ofFn (Fin.snoc y true)) = true)
    (dn : C.eval (List.ofFn (Fin.snoc y false)) = false) :
    ∃ g ∈ C.gates, g.op ≠ .not ∧ n ∈ g.inputs := by
  by_contra no
  have bad : ∀ g ∈ C.gates, g.op ≠ .not → n ∉ g.inputs :=
    fun g hg a b => no ⟨g,hg,a,b⟩
  let W := List.ofFn y
  have len : W.length = n := by simp [W]
  have same (i : ℕ) (ne : i ≠ n) : (W ++ [true]).getD i false = (W ++ [false]).getD i false := by
    rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)]
  have h := wiresAnti C.gates n legal bad unique (W ++ [true]) (W ++ [false])
    (by simp) (by simp [len]) (getD_snoc_len _ _ _ _ len) (getD_snoc_len _ _ _ _ len)
    (fun i hi => le_of_eq (same i hi)) (fun _ => same) C.output hout
  rw [ofFn_snoc] at up dn
  change (wiresFrom C.gates (W ++ [true])).getD C.output false = true at up
  change (wiresFrom C.gates (W ++ [false])).getD C.output false = false at dn
  rw [up,dn] at h
  contradiction

theorem normBinary (gs : List Gate) : binaryCount (gs.map normGate) = binaryCount gs := by
  simp only [binaryCount,List.countP_map]
  have eq : isBinaryGate ∘ normGate = isBinaryGate := by
    funext g
    cases g with | mk op t => cases op <;> rfl
  rw [eq]

theorem saveBinaryLast (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (C : Circuit)
    (fit : FanInTwo C) (unique : C.gates.countP isNegGate ≤ 1)
    (comp : ∀ x, C.eval (List.ofFn x) = f x)
    (inc : ∃ y : Fin n → Bool, f (Fin.snoc y true) = true ∧ f (Fin.snoc y false) = false)
    (nonconstant : ∃ y z : Fin n → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc z false)) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ y, D.eval (List.ofFn y) = f (Fin.snoc y false)) ∧
      binaryCount D.gates + 1 ≤ binaryCount C.gates := by
  have hout : C.output ≠ n := by
    intro out
    have fixed (y : Fin n → Bool) : f (Fin.snoc y false) = false := by
      rw [← comp,ofFn_snoc]
      change (wiresFrom C.gates (List.ofFn y ++ [false])).getD C.output false = false
      rw [out,getD_wiresFrom _ _ _ (by simp)]
      exact getD_snoc_len _ _ _ _ (by simp)
    obtain ⟨y,z,ne⟩ := nonconstant
    exact ne ((fixed _).trans (fixed _).symm)
  obtain ⟨y,yup,ydn⟩ := inc
  obtain ⟨g,mem,op,read⟩ := needsPositiveReader n C fit unique hout y
    ((comp _).trans yup) ((comp _).trans ydn)
  set gs := C.gates.map normGate with hgs
  have hok : ∀ g ∈ gs, NOk g := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact normGate_nok u (fit u hu)
  have same : normGate g = g := by
    cases g with | mk o t => cases o <;> simp_all [normGate]
  have read' : ∃ t ∈ gs, t.op ≠ .not ∧ n ∈ t.inputs :=
    ⟨g,same ▸ List.mem_map_of_mem mem,op,read⟩
  set acc := elim n gs (initStats n false,[]) with ha
  have val (z : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn z)) (acc.1.getD C.output (Sum.inl false)) = f (Fin.snoc z false) := by
    have h := inv_elim n _ (by simp : (List.ofFn z).length = n) gs _ _ (fun k hk => (hok k hk).1) (inv_init n false z)
    rw [((h.2 C.output).2 : statVal _ _ = _), ← ofFn_snoc,hgs,wiresFrom_norm,← comp]
    rfl
  cases status : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y,z,ne⟩ := nonconstant
    exfalso;apply ne;rw [← val y,← val z,status];rfl
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elim_ok n gs _ (by simp),?_,?_⟩
    · intro z;have e := val z;rw [status] at e;exact e
    · have h := bin_save n n gs (initStats n false,[]) hok (by simp [initStats])
        ⟨false,getD_snoc_len _ _ _ _ (by simp)⟩ read'
      change binaryCount acc.2 + 1 ≤ binaryCount ([] : List Gate) + binaryCount gs at h
      have counts : binaryCount gs = binaryCount C.gates := normBinary _
      rw [counts] at h
      simpa only [binaryCount,List.countP_nil,Nat.zero_add] using h

theorem relabelBinary {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) :
    binaryCount (relabel n m π C).gates = binaryCount C.gates := by
  simp only [binaryCount,relabel,List.countP_map]
  rfl

theorem binary_lt_length (gs : List Gate) (ex : ∃ g ∈ gs, g.op = .not) :
    binaryCount gs < gs.length := by
  obtain ⟨g,hg,neg⟩ := ex
  by_contra! h
  have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
  simp [isBinaryGate,(negGate_iff g).mpr neg] at eq

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem relabelFan {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (fit : FanInTwo C) :
    FanInTwo (relabel n m π C) := by
  intro g hg
  obtain ⟨h, mem, rfl⟩ := List.mem_map.mp hg
  exact ⟨(fit h mem).1, by simpa [relGate] using (fit h mem).2⟩

theorem relabelHasNot {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (ex : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ g ∈ (relabel n m π C).gates, g.op = GateOp.not := by
  obtain ⟨g, hg, hop⟩ := ex
  exact ⟨relGate n m π g, List.mem_map.mpr ⟨g,hg,rfl⟩, hop⟩

theorem relabelUniqueNot {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      (C.gates.get j).op = GateOp.not → i = j) :
    let D := relabel n m π C
    ∀ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.not →
      (D.gates.get j).op = GateOp.not → i = j := by
  dsimp only
  intro i j hi hj
  let a : Fin C.gates.length := ⟨i.val, by simpa [relabel] using i.isLt⟩
  let b : Fin C.gates.length := ⟨j.val, by simpa [relabel] using j.isLt⟩
  have pick (k : Fin (C.gates.map (relGate n m π)).length) :
      ((C.gates.map (relGate n m π)).get k).op =
      (C.gates.get ⟨k.val, by simpa using k.isLt⟩).op := by
    change ((C.gates.map (relGate n m π))[k.val]).op =
      (C.gates[k.val]'(by simpa using k.isLt)).op
    rw [List.getElem_map]
    rfl
  have ha : (C.gates.get a).op = GateOp.not := (pick i).symm.trans hi
  have hb : (C.gates.get b).op = GateOp.not := (pick j).symm.trans hj
  apply Fin.ext
  exact congrArg (fun k : Fin C.gates.length => k.val) (unique a b ha hb)

theorem relabelEval {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) := by
  exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem liftBinaryLower (π : Fin 8 → Fin 8) (graph : (Fin 8 → Bool) → Bool)
    (base : (Fin 7 → Bool) → Bool) (b : ℕ)
    (inc : ∃ y : Fin 7 → Bool, graph ((Fin.snoc y true) ∘ π) = true ∧ graph ((Fin.snoc y false) ∘ π) = false)
    (nc : ∃ y z : Fin 7 → Bool, graph ((Fin.snoc y false) ∘ π) ≠ graph ((Fin.snoc z false) ∘ π))
    (table : ∀ y, graph ((Fin.snoc y false) ∘ π) = base y)
    (baseLower : ∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = base x) → b ≤ binaryCount D.gates)
    (C : Circuit) (fit : FanInTwo C)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (has : ∃ g ∈ C.gates, g.op = .not) (comp : ∀ x, C.eval (List.ofFn x) = graph x) :
    b + 2 ≤ C.gates.length := by
  let D := relabel 8 8 π C
  have cd (x : Fin 8 → Bool) : D.eval (List.ofFn x) = graph (x ∘ π) :=
    (relabelEval π C x).trans (comp _)
  have un := countNeg_le D.gates (relabelUniqueNot π C unique)
  obtain ⟨S,fitS,evS,saved⟩ := saveBinaryLast 7 (fun x => graph (x ∘ π)) D
    (relabelFan π C fit) un cd inc nc
  have l := baseLower S fitS (fun x => (evS x).trans (table x))
  have same : binaryCount D.gates = binaryCount C.gates := relabelBinary π C
  have lt := binary_lt_length _ has
  omega
end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem simplify_neg_sub (g : Gate) (m : ℕ) (ins : List Stat) :
    (simplify g.op m ins).1.toList.countP isNegGate ≤ (if isNegGate g then 1 else 0) := by
  cases g with
  | mk op inp =>
    cases op with
    | not => exact le_trans List.countP_le_length (toList_length_le _)
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simplify,simpAnd,isNegGate]
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simplify,simpOr,isNegGate]
    | _ => simp [simplify,isNegGate]

theorem elim_neg_sub (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).2.countP isNegGate ≤ acc.2.countP isNegGate + gs.countP isNegGate := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    have step : (elimStep n acc g).2.countP isNegGate ≤ acc.2.countP isNegGate + (if isNegGate g then 1 else 0) := by
      simp only [elimStep,List.countP_append]
      exact Nat.add_le_add_left (simplify_neg_sub _ _ _) _
    have tail := ih (elimStep n acc g)
    rw [elim_cons,List.countP_cons]
    omega

theorem normNeg (gs : List Gate) : (gs.map normGate).countP isNegGate = gs.countP isNegGate := by
  rw [List.countP_map]
  have e : isNegGate ∘ normGate = isNegGate := by
    funext g;cases g with | mk op t => cases op <;> rfl
  rw [e]
end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem saveBinaryWithBudget (n : ℕ) (bit : Bool) (f : (Fin (n + 1) → Bool) → Bool) (C : Circuit)
    (fit : FanInTwo C) (unique : C.gates.countP isNegGate ≤ 1)
    (comp : ∀ x, C.eval (List.ofFn x) = f x)
    (inc : ∃ y : Fin n → Bool, f (Fin.snoc y true) = true ∧ f (Fin.snoc y false) = false)
    (nonconstant : ∃ y z : Fin n → Bool, f (Fin.snoc y bit) ≠ f (Fin.snoc z bit)) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ y, D.eval (List.ofFn y) = f (Fin.snoc y bit)) ∧
      binaryCount D.gates + 1 ≤ binaryCount C.gates ∧ D.gates.countP isNegGate ≤ C.gates.countP isNegGate := by
  have hout : C.output ≠ n := by
    intro out
    have fixed (y : Fin n → Bool) : f (Fin.snoc y bit) = bit := by
      rw [← comp,ofFn_snoc]
      change (wiresFrom C.gates (List.ofFn y ++ [bit])).getD C.output false = bit
      rw [out,getD_wiresFrom _ _ _ (by simp)]
      exact getD_snoc_len _ _ _ _ (by simp)
    obtain ⟨y,z,ne⟩ := nonconstant
    exact ne ((fixed _).trans (fixed _).symm)
  obtain ⟨y,yup,ydn⟩ := inc
  obtain ⟨g,mem,op,read⟩ := needsPositiveReader n C fit unique hout y
    ((comp _).trans yup) ((comp _).trans ydn)
  set gs := C.gates.map normGate with hgs
  have hok : ∀ g ∈ gs, NOk g := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact normGate_nok u (fit u hu)
  have same : normGate g = g := by
    cases g with | mk o t => cases o <;> simp_all [normGate]
  have read' : ∃ t ∈ gs, t.op ≠ .not ∧ n ∈ t.inputs :=
    ⟨g,same ▸ List.mem_map_of_mem mem,op,read⟩
  set acc := elim n gs (initStats n bit,[]) with ha
  have val (z : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn z)) (acc.1.getD C.output (Sum.inl false)) = f (Fin.snoc z bit) := by
    have h := inv_elim n _ (by simp : (List.ofFn z).length = n) gs _ _ (fun k hk => (hok k hk).1) (inv_init n bit z)
    rw [((h.2 C.output).2 : statVal _ _ = _), ← ofFn_snoc,hgs,wiresFrom_norm,← comp]
    rfl
  cases status : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y,z,ne⟩ := nonconstant
    exfalso;apply ne;rw [← val y,← val z,status];rfl
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elim_ok n gs _ (by simp),?_,?_,?_⟩
    · intro z;have e := val z;rw [status] at e;exact e
    · have h := bin_save n n gs (initStats n bit,[]) hok (by simp [initStats])
        ⟨bit,getD_snoc_len _ _ _ _ (by simp)⟩ read'
      change binaryCount acc.2 + 1 ≤ binaryCount ([] : List Gate) + binaryCount gs at h
      have counts : binaryCount gs = binaryCount C.gates := normBinary _
      rw [counts] at h
      simpa only [binaryCount,List.countP_nil,Nat.zero_add] using h
    · have h := elim_neg_sub n gs (initStats n bit,[])
      change acc.2.countP isNegGate ≤ ([] : List Gate).countP isNegGate + gs.countP isNegGate at h
      have e : gs.countP isNegGate = C.gates.countP isNegGate := normNeg _
      rw [e] at h
      simpa only [List.countP_nil,Nat.zero_add] using h

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev SA := List Stat × List Gate
abbrev signal (w : List Bool) (i : Nat) := w.getD i false
abbrev statusAt (s : SA) (i : Nat) := s.1.getD i (Sum.inl false)
def nextBit (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map (signal w))
abbrev pushBit (w : List Bool) (g : Gate) := w ++ [nextBit w g]
def diffInput (a b : List Bool) (g : Gate) :=
  ∃ i ∈ g.inputs, signal a i ≠ signal b i
def tracks (a b : List Bool) (s : SA) (p : Nat → Stat → Prop) :=
  ∀ i, signal a i ≠ signal b i → p i (statusAt s i)
abbrev constantStat (v : Stat) := ∃ c : Bool, v = Sum.inl c

theorem pushLast (w : List Bool) (g : Gate) (i : Nat) (h : i = w.length) :
    signal (pushBit w g) i = nextBit w g := h ▸ getD_snoc_eq _ _ _

theorem pushOld (w : List Bool) (g : Gate) (i : Nat) (h : i ≠ w.length) :
    signal (pushBit w g) i = signal w i := getD_snoc_ne _ _ _ _ h

theorem differentReader {a b : List Bool} {g : Gate}
    (h : nextBit a g ≠ nextBit b g) : diffInput a b g := by
  by_contra hno
  apply h
  unfold nextBit
  congr 1
  apply List.map_congr_left
  intro i hi
  by_contra ne
  exact hno ⟨i,hi,ne⟩

theorem chargedStep {n : Nat} {s : SA} {g : Gate} (ok : NOk g) (binary : g.op ≠ .not)
    {i : Nat} (read : i ∈ g.inputs) (val : constantStat (statusAt s i)) :
    binaryCount (elimStep n s g).2 + 1 ≤ binaryCount s.2 + (if isBinaryGate g then 1 else 0) := by
  obtain ⟨c,hc⟩ := val
  have size := elimStep_none n s g ok i read c hc
  have same : (elimStep n s g).2 = s.2 := by
    let tail := (simplify g.op (n + s.2.length) (g.inputs.map (statusAt s))).1.toList
    change (s.2 ++ tail).length = s.2.length at size
    rw [List.length_append] at size
    have nil : tail = [] := List.length_eq_zero_iff.mp (by omega)
    change s.2 ++ tail = s.2
    rw [nil,List.append_nil]
  rw [same,binary_of_ne binary]
  simp

theorem preserveBefore {n : Nat} {a b w : List Bool} {s : SA} {g : Gate}
    (la : a.length = s.1.length) (lb : b.length = s.1.length) (lw : w.length = s.1.length)
    (prev : tracks a b s (fun i v => v = Sum.inl (signal w i)))
    (easy : g.op = .not ∨ ¬diffInput a b g) :
    tracks (pushBit a g) (pushBit b g) (elimStep n s g)
      (fun i v => v = Sum.inl (signal (pushBit w g) i)) := by
  intro i disagree
  by_cases last : i = s.1.length
  · subst i
    rw [show signal (pushBit a g) s.1.length = nextBit a g by rw [← la]; exact getD_snoc_eq _ _ _,
        show signal (pushBit b g) s.1.length = nextBit b g by rw [← lb]; exact getD_snoc_eq _ _ _] at disagree
    have rd := differentReader disagree
    have neg := easy.resolve_right (fun e => e rd)
    rw [show signal (pushBit w g) s.1.length = nextBit w g by rw [← lw]; exact getD_snoc_eq _ _ _]
    change (s.1 ++ [_]).getD s.1.length _ = _
    rw [getD_snoc_eq]
    cases he : g.inputs with
    | nil => simp [nextBit,he,neg,GateOp.eval] at disagree
    | cons j rest =>
      have delta : signal a j ≠ signal b j := by
        simpa [nextBit,neg,he,GateOp.eval] using disagree
      have eq := prev j delta
      change s.1.getD j (Sum.inl false) = Sum.inl (signal w j) at eq
      simp only [simplify,neg,he,List.map_cons,eq,simpNot,nextBit,GateOp.eval,List.headD_cons]
  · have hda := getD_snoc_ne a (nextBit a g) false i (by omega)
    have hdb := getD_snoc_ne b (nextBit b g) false i (by omega)
    have hdw := getD_snoc_ne w (nextBit w g) false i (by omega)
    have hstat : statusAt (elimStep n s g) i = statusAt s i := getD_snoc_ne _ _ _ _ last
    rw [hstat,pushOld w g i (by omega)]
    exact prev i (by simpa only [signal,pushBit,hda,hdb] using disagree)

theorem trackStep {n : Nat} {a b : List Bool} {s : SA} {g : Gate}
    (la : a.length = s.1.length) (lb : b.length = s.1.length)
    (prev : tracks a b s (fun _ v => constantStat v))
    (new : nextBit a g ≠ nextBit b g → constantStat (statusAt (elimStep n s g) s.1.length)) :
    tracks (pushBit a g) (pushBit b g) (elimStep n s g) (fun _ v => constantStat v) := by
  intro i diff
  by_cases eq : i = s.1.length
  · subst i
    exact new (by simpa only [pushLast a g _ la.symm,pushLast b g _ lb.symm] using diff)
  · have prevDiff : signal a i ≠ signal b i := by
      simpa only [pushOld a g i (by omega),pushOld b g i (by omega)] using diff
    have same : statusAt (elimStep n s g) i = statusAt s i := getD_snoc_ne _ _ _ _ eq
    rw [same];exact prev i prevDiff

theorem staysConstant {n : Nat} {a b : List Bool} {s : SA} {g : Gate}
    (prev : tracks a b s (fun _ v => constantStat v))
    (easy : g.op = .not ∨ ¬diffInput a b g) (diff : nextBit a g ≠ nextBit b g) :
    constantStat (statusAt (elimStep n s g) s.1.length) := by
  have neg := easy.resolve_right (fun e => e (differentReader diff))
  unfold constantStat statusAt
  simp only [elimStep]
  rw [getD_snoc_eq]
  cases h : g.inputs with
  | nil => simp [nextBit,neg,h] at diff
  | cons j rest =>
    have delta : signal a j ≠ signal b j := by simpa [nextBit,neg,h,GateOp.eval] using diff
    obtain ⟨c,hc⟩ := prev j delta
    change s.1.getD j (Sum.inl false) = Sum.inl c at hc
    exact ⟨!c,by simp only [simplify,neg,List.map_cons,hc,simpNot]⟩

theorem afterFirst (n : Nat) (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, NOk g) :
    ∀ a b s, a.length = s.1.length → b.length = s.1.length →
      tracks a b s (fun _ v => constantStat v) →
      signal (wiresFrom gs a) o ≠ signal (wiresFrom gs b) o →
      ¬constantStat (statusAt (elim n gs s) o) →
      binaryCount (elim n gs s).2 + 1 ≤ binaryCount s.2 + binaryCount gs := by
  induction gs with
  | nil =>
    intro a b s _ _ prev diff non
    exact (non (prev o diff)).elim
  | cons g gs ih =>
    intro a b s la lb prev diff non
    have ok := legal g List.mem_cons_self
    by_cases hit : g.op ≠ .not ∧ diffInput a b g
    · obtain ⟨op,i,read,delta⟩ := hit
      have first := chargedStep (n := n) ok op read (prev i delta)
      have tail := bin_all n gs (elimStep n s g)
      rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
      omega
    · have easy : g.op = .not ∨ ¬diffInput a b g := by tauto
      have still := trackStep la lb prev (staysConstant (n := n) prev easy)
      have tail := ih (fun k hk => legal k (List.mem_cons_of_mem _ hk)) (pushBit a g) (pushBit b g) (elimStep n s g)
        (by simp [pushBit,elimStep,la]) (by simp [pushBit,elimStep,lb]) still diff non
      have step := bin_step n s g
      rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
      omega

theorem pickBranch (v : Bool → Bool) (force : Bool) (diff : v false ≠ v true) :
    ∃ b, v b = force := by
  by_cases e : v false = force
  · exact ⟨false,e⟩
  · refine ⟨true,?_⟩
    cases h0 : v false <;> cases h1 : v true <;> cases force <;> simp_all

theorem beforeFirst (n : Nat) (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, NOk g) :
    ∀ (w : Bool → List Bool) (s : Bool → SA),
      (∀ a b, (w a).length = (s b).1.length) →
      (∀ b, tracks (w false) (w true) (s b) (fun i v => v = Sum.inl (signal (w b) i))) →
      signal (wiresFrom gs (w false)) o ≠ signal (wiresFrom gs (w true)) o →
      (∀ b, ¬constantStat (statusAt (elim n gs (s b)) o)) →
      ∃ b, binaryCount (elim n gs (s b)).2 + 2 ≤ binaryCount (s b).2 + binaryCount gs := by
  induction gs with
  | nil =>
    intro w s _ prev diff non
    exact (non false ⟨_,prev false o diff⟩).elim
  | cons g gs ih =>
    intro w s width prev diff non
    have ok := legal g List.mem_cons_self
    have tailOk (k) (hk : k ∈ gs) := legal k (List.mem_cons_of_mem _ hk)
    let w' := fun b => pushBit (w b) g
    let s' := fun b => elimStep n (s b) g
    have width' (a b : Bool) : (w' a).length = (s' b).1.length := by simp [w',s',pushBit,elimStep,width a b]
    by_cases hit : g.op ≠ .not ∧ diffInput (w false) (w true) g
    · obtain ⟨op,i,read,delta⟩ := hit
      obtain ⟨b,force⟩ := pickBranch (fun b => signal (w b) i) (fixBit g) delta
      have hc := prev b i delta
      have first := chargedStep (n := n) ok op read ⟨_,hc⟩
      have status := elimStep_const n (s b) g ok i read (hc.trans (congrArg Sum.inl force))
      have still : tracks (w' false) (w' true) (s' b) (fun _ v => constantStat v) :=
        trackStep (width false b) (width true b) (fun j d => ⟨_,prev b j d⟩) (fun _ => status)
      have tail := afterFirst n gs o tailOk (w' false) (w' true) (s' b)
        (width' false b) (width' true b) still diff (non b)
      refine ⟨b,?_⟩
      change binaryCount (elim n gs (s' b)).2 + 2 ≤ _
      change binaryCount (s' b).2 + 1 ≤ _ at first
      simp only [binaryCount,List.countP_cons] at *
      omega
    · have easy : g.op = .not ∨ ¬diffInput (w false) (w true) g := by tauto
      have next (b) := preserveBefore (n := n) (width false b) (width true b) (width b b) (prev b) easy
      obtain ⟨b,tail⟩ := ih tailOk w' s' width' next diff non
      have step := bin_step n (s b) g
      change binaryCount (s' b).2 ≤ _ at step
      refine ⟨b,?_⟩
      change binaryCount (elim n gs (s' b)).2 + 2 ≤ _
      simp only [binaryCount,List.countP_cons] at *
      omega

theorem saveTwoBinary (n : Nat) (f : (Fin (n+1) → Bool) → Bool) (C : Circuit)
    (fit : FanInTwo C) (comp : ∀ x, C.eval (List.ofFn x) = f x)
    (depends : ∃ y : Fin n → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y true))
    (nonconstant : ∀ b, ∃ y z : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc z b)) :
    ∃ (b : Bool) (D : Circuit), FanInTwo D ∧ (∀ y, D.eval (List.ofFn y) = f (Fin.snoc y b)) ∧
      binaryCount D.gates + 2 ≤ binaryCount C.gates ∧ D.gates.countP isNegGate ≤ C.gates.countP isNegGate := by
  obtain ⟨y,dep⟩ := depends
  let gs := C.gates.map normGate
  let w := fun b => List.ofFn y ++ [b]
  let s : Bool → SA := fun b => (initStats n b,[])
  let acc := fun b => elim n gs (s b)
  have ok (g) (mem : g ∈ gs) : NOk g := by
    obtain ⟨old,hm,rfl⟩ := List.mem_map.mp mem
    exact normGate_nok old (fit old hm)
  have val (b : Bool) (z : Fin n → Bool) :
      statVal (wiresFrom (acc b).2 (List.ofFn z)) (statusAt (acc b) C.output) = f (Fin.snoc z b) := by
    have inv := inv_elim n _ (by simp : (List.ofFn z).length = n) gs _ _ (fun k hk => (ok k hk).1) (inv_init n b z)
    rw [((inv.2 C.output).2 : statVal _ _ = _), ←ofFn_snoc, show gs = C.gates.map normGate by rfl,wiresFrom_norm,←comp]
    rfl
  have non (b : Bool) : ¬constantStat (statusAt (acc b) C.output) := by
    rintro ⟨c,hc⟩
    obtain ⟨u,v,ne⟩ := nonconstant b
    apply ne;rw [←val b u,←val b v,hc];rfl
  have ev (b : Bool) : signal (wiresFrom gs (w b)) C.output = f (Fin.snoc y b) := by
    change (wiresFrom (C.gates.map normGate) (List.ofFn y ++ [b])).getD C.output false = _
    rw [wiresFrom_norm,←ofFn_snoc,←comp];rfl
  have start (b : Bool) : tracks (w false) (w true) (s b) (fun i v => v = Sum.inl (signal (w b) i)) := by
    intro i diff
    by_cases last : i = n
    · subst i
      change (initStats n b).getD n _ = Sum.inl ((List.ofFn y ++ [b]).getD n false)
      rw [initStats_last,getD_snoc_len _ _ _ _ (by simp)]
    · exfalso;apply diff
      change (List.ofFn y ++ [false]).getD i _ = (List.ofFn y ++ [true]).getD i _
      rw [getD_snoc_ne _ _ _ _ (by simpa using last),getD_snoc_ne _ _ _ _ (by simpa using last)]
  obtain ⟨b,paid⟩ := beforeFirst n gs C.output ok w s (by simp [s,w,initStats]) start
    (by simpa only [ev] using dep) non
  cases h : statusAt (acc b) C.output with
  | inl c => exact (non b ⟨c,h⟩).elim
  | inr j =>
    refine ⟨b,⟨(acc b).2,j⟩,elim_ok n gs _ (by simp [s]),?_,?_,?_⟩
    · intro z;have e := val b z;rw [h] at e;exact e
    · change binaryCount (acc b).2 + 2 ≤ binaryCount ([] : List Gate) + binaryCount (C.gates.map normGate) at paid
      simpa only [normBinary,binaryCount,List.countP_nil,Nat.zero_add] using paid
    · have h := elim_neg_sub n gs (s b)
      change (acc b).2.countP isNegGate ≤ ([] : List Gate).countP isNegGate + (C.gates.map normGate).countP isNegGate at h
      simpa only [normNeg,List.countP_nil,Nat.zero_add] using h

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Within {n : Nat} (f : (Fin n → Bool) → Bool) (k : Nat) : Prop :=
  ∀ (C : Circuit), FanInTwo C → C.gates.countP isNegGate ≤ 1 →
    (∀ x, C.eval (List.ofFn x) = f x) → k ≤ binaryCount C.gates

theorem within_zero {n : Nat} (f : (Fin n → Bool) → Bool) : Within f 0 :=
  fun _ _ _ _ => Nat.zero_le _

theorem relabelNeg {n m : Nat} (pi : Fin n → Fin m) (C : Circuit) :
    (relabel n m pi C).gates.countP isNegGate = C.gates.countP isNegGate := by
  simp only [relabel,List.countP_map]
  rfl

theorem within_projection {n m k : Nat} {f : (Fin n → Bool) → Bool} {g : (Fin m → Bool) → Bool}
    (pi : Fin n → Fin m) (eq : ∀ y, f (y ∘ pi) = g y) (low : Within g k) : Within f k := by
  intro C fit num ev
  let D := relabel n m pi C
  have h := low D (relabelFan pi C fit) ((relabelNeg pi C).le.trans num)
    (fun y => (relabelEval pi C y).trans ((ev _).trans (eq y)))
  exact h.trans (relabelBinary pi C).le

theorem within_single {n k : Nat} {f : (Fin (n+1) → Bool) → Bool} {g : (Fin n → Bool) → Bool}
    (pi : Fin (n+1) → Fin (n+1)) (b : Bool) (eq : ∀ y, f (Fin.snoc y b ∘ pi) = g y)
    (inc : ∃ y, f (Fin.snoc y true ∘ pi) = true ∧ f (Fin.snoc y false ∘ pi) = false)
    (nc : ∃ y z, g y ≠ g z) (low : Within g k) : Within f (k+1) := by
  apply within_projection pi (fun _ => rfl)
  intro C fit num ev
  obtain ⟨u,v,ne⟩ := nc
  obtain ⟨D,leg,acts,paid,cnt⟩ := saveBinaryWithBudget n b (fun y => f (y ∘ pi)) C fit num ev inc
    ⟨u,v,by simpa only [eq] using ne⟩
  have h := low D leg (cnt.trans num) (fun y => (acts y).trans (eq y))
  omega

theorem within_two {n k : Nat} {f : (Fin (n+1) → Bool) → Bool} {gs : Bool → (Fin n → Bool) → Bool}
    (pi : Fin (n+1) → Fin (n+1)) (eq : ∀ b y, f (Fin.snoc y b ∘ pi) = gs b y)
    (depends : ∃ y, gs false y ≠ gs true y) (nc : ∀ b, ∃ y z, gs b y ≠ gs b z)
    (low : ∀ b, Within (gs b) k) : Within f (k+2) := by
  apply within_projection pi (fun _ => rfl)
  intro C fit num ev
  obtain ⟨u,ne⟩ := depends
  obtain ⟨b,D,leg,acts,paid,cnt⟩ := saveTwoBinary n (fun y => f (y ∘ pi)) C fit ev
    ⟨u,by simpa only [eq] using ne⟩ (fun s => by simpa only [eq] using nc s)
  have h := low b D leg (cnt.trans num) (fun y => (acts y).trans (eq b y))
  omega
end Transfer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def graph (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 6) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def mon : List Gate := [⟨.or, [1, 7]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [10, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [19, 14]⟩, ⟨.or, [20, 18]⟩]

theorem baseBound (D : Circuit) (fit : FanInTwo D)
    (ev : ∀ x, D.eval (List.ofFn x) = Base.graph x) : 10 ≤ Transfer.binaryCount D.gates := by
  have low := Base.binaryLower D fit ev
  change 10 ≤ D.gates.countP (fun g => !Base.signedNot g) at low
  have eq : (fun g => !Base.signedNot g) = Transfer.isBinaryGate := by
    funext g;cases g with | mk op l => cases op <;> rfl
  rw [eq] at low;exact low

def cofactor0 (x : Fin 6 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 4 && x 5)
theorem cofactor0_bound : Transfer.Within cofactor0 10 := by
  intro C fit num ev
  let pi : Fin 6 → Fin 6 := ![0, 1, 2, 3, 4, 5]
  have ht : ∀ y, cofactor0 (y ∘ pi) = Base.graph y := by decide +kernel
  have h := baseBound (Transfer.relabel 6 6 pi C) (Transfer.relabelFan pi C fit)
    (fun y => (Transfer.relabelEval pi C y).trans ((ev _).trans (ht y)))
  have same := Transfer.relabelBinary pi C
  omega

def cofactor1 (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
theorem cofactor1_bound : Transfer.Within cofactor1 11 := by
  apply Transfer.within_single (g := cofactor0) ![0, 1, 2, 3, 4, 6, 5] false (by decide +kernel)
    ⟨![true, false, false, false, false, false],by decide +kernel⟩ ⟨![false, false, false, false, false, false],![true, false, true, false, false, false],by decide +kernel⟩ cofactor0_bound

def cofactor2 (x : Fin 7 → Bool) : Bool := x 5 || (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6)
theorem cofactor2_bound : Transfer.Within cofactor2 11 := by
  apply Transfer.within_single (g := cofactor0) ![0, 1, 2, 3, 4, 6, 5] false (by decide +kernel)
    ⟨![false, false, false, false, false, false],by decide +kernel⟩ ⟨![false, false, false, false, false, false],![true, false, true, false, false, false],by decide +kernel⟩ cofactor0_bound

def cofactor3 (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
theorem cofactor3_bound : Transfer.Within cofactor3 13 := by
  let branches (b : Bool) : (Fin 7 → Bool) → Bool := if b then cofactor2 else cofactor1
  apply Transfer.within_two (gs := branches) ![0, 1, 7, 2, 3, 4, 5, 6] (by decide +kernel)
    ⟨![false, false, false, false, false, true, false],by decide +kernel⟩
  · intro bit;cases bit
    · exact ⟨![false, false, false, false, false, false, false],![true, false, true, false, false, false, false],by decide +kernel⟩
    · exact ⟨![false, false, false, false, false, false, false],![true, false, true, false, false, false, false],by decide +kernel⟩
  · intro bit;cases bit
    · exact cofactor1_bound
    · exact cofactor2_bound

theorem bound (C : Circuit) (fit : FanInTwo C)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (has : ∃ g ∈ C.gates, g.op = .not) (ev : ∀ x, C.eval (List.ofFn x) = graph x) :
    14 ≤ C.gates.length := by
  have table : ∀ x : Fin 8 → Bool, graph x = cofactor3 x := by decide +kernel
  have low := cofactor3_bound C fit (Transfer.countNeg_le C.gates unique) (fun x => (ev x).trans (table x))
  have lt := Transfer.binary_lt_length _ has
  omega

set_option maxRecDepth 8192 in
theorem spec : ∀ x : Fin 8 → Bool, graph x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
set_option maxRecDepth 8192 in
theorem witness : ∀ x : Fin 8 → Bool, (⟨mon,21⟩ : Circuit).eval (List.ofFn x) = graph x := by decide +kernel
theorem basis : ∀ g ∈ mon, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mon,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_32776

open PEqualNP.Outside.L_meta_32776 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_32776 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o fit uniq computes
  by_cases has : ∃ g ∈ gates, g.op = GateOp.not
  · have low := bound ⟨gates,o⟩ fit uniq has (fun x => (computes x).trans (spec x).symm)
    exact ⟨mon,21,basis,(show mon.length ≤ 14 by decide).trans low,fun x => (witness x).trans (spec x)⟩
  · refine ⟨gates,o,?_,le_rfl,computes⟩
    intro g hg
    obtain ⟨op,l⟩ := fit g hg
    exact ⟨op.imp_right (fun p => p.resolve_right (fun h => has ⟨g,hg,h⟩)),l⟩
